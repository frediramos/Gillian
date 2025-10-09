open Gillian
open Gillian.Gil_syntax
open Javert_utils
open Semantics_shared.MemoryUtils
module SFVL = Semantics_shared.SFVL
module GAsrt = Asrt
module SSubst = Gillian.Symbolic.Subst
module L = Logging
module SVal = Gillian.Symbolic.Values
module PFS = Gillian.Symbolic.Pure_context
module Type_env = Gillian.Symbolic.Type_env
module Recovery_tactic = Gillian.General.Recovery_tactic

module StringKey = struct
  type t = string [@@deriving yojson]

  let compare = String.compare
end

module LogLiftingObj : ObjectIntf = struct
  module SMap = Map.Make (StringKey)

  type ot = ot' list
  and ot' = Srec of (vt * vt) | Crec of vt SMap.t [@@deriving yojson]

  type t = ot [@@deriving yojson]

  let create () = []
  let clone o = o

  let to_list_aux' (o : ot') (tbl : (vt, vt) Hashtbl.t) :
      vts * vts * (vt, vt) Hashtbl.t =
    match o with
    | Srec (p, v) when Expr.equal v none -> (set_empty, set_single p, tbl)
    | Srec (p, v) ->
        Hashtbl.replace tbl p v;
        (set_single p, set_empty, tbl)
    | Crec cmap ->
        let s1, s2 =
          SMap.fold
            (fun p v (s1, s2) ->
              let p' = Expr.string p in
              if Expr.equal v none then (s1, Expr.Set.add p' s2)
              else (
                Hashtbl.replace tbl p' v;
                (Expr.Set.add p' s1, s2)))
            cmap (set_empty, set_empty)
        in
        (s1, s2, tbl)

  let rec to_list_aux (o : t) (tbl : (vt, vt) Hashtbl.t) :
      vts * vts * (vt, vt) Hashtbl.t =
    match o with
    | [] -> (set_empty, set_empty, tbl)
    | o1 :: o2 ->
        let fs_1, fs_1', tbl = to_list_aux' o1 tbl in
        let fs_2, fs_2', tbl = to_list_aux o2 tbl in
        ( set_summ fs_1 (set_diff fs_2 fs_1'),
          set_summ fs_1' (set_diff fs_2' fs_1),
          tbl )

  let to_list o : (vt * vt) list =
    let set1, _, tbl = to_list_aux o (Hashtbl.create 0) in
    Expr.Set.fold
      (fun p acc ->
        match Hashtbl.find_opt tbl p with
        | Some v -> (p, v) :: acc
        | None -> assert false)
      set1 []

  let to_sfvl o =
    let pairs = to_list o in
    list_to_sfvl pairs

  let get_fields o : vt list =
    let set1, _, _ = to_list_aux o (Hashtbl.create 0) in
    Expr.Set.to_list set1

  let set_aux (obj' : ot') prop v : ot' =
    match (prop, obj') with
    | Expr.Lit (String field), Crec map -> Crec (SMap.add field v map)
    | Expr.Lit (String field), _ -> Crec (SMap.singleton field v)
    | _ -> Srec (prop, v)

  let set (obj : ot) (field : vt) (value : vt) =
    match (obj, field) with
    | r1 :: r2, _ -> (
        let r = set_aux r1 field value in
        match r1 with
        | Crec _ -> (
            match r with
            | Crec map -> Crec map :: r2
            | _ -> r :: obj)
        | _ -> r :: obj)
    | [], Expr.Lit (String field) -> [ Crec (SMap.singleton field value) ]
    | [], _ -> [ Srec (field, value) ]

  let from_list (pairs : (vt * vt) list) : ot =
    List.fold_left (fun acc (p, v) -> set acc p v) [] pairs

  let from_sfvl sfvl =
    let lst = SFVL.to_list sfvl in
    from_list lst

  let rec get_vals' (obj : ot') (prop : vt) (pc : vt) (gamma : Type_env.t) :
      (vt * vt) list * vt =
    let open Expr.Infix in
    match (obj, prop) with
    | Crec map, Lit (String field) -> (
        match SMap.find_opt field map with
        | Some v -> ([ (v, Expr.true_) ], Expr.false_)
        | None -> ([], Expr.true_))
    | Crec map, _ ->
        SMap.fold
          (fun prop' v (acc, not_found) ->
            let prop' = Expr.string prop' in
            if is_sat [ prop' == prop; pc ] gamma then
              ((v, prop == prop') :: acc, not_found && not (prop == prop'))
            else (acc, not_found))
          map ([], Expr.true_)
    | Srec (prop', v), _ ->
        if is_sat [ prop' == prop; pc ] gamma then
          ([ (v, prop == prop') ], not (prop == prop'))
        else ([], Expr.true_)

  and get_vals (obj : t) (prop : vt) (pc : vt) (gamma : Type_env.t) :
      (vt * vt) list * vt =
    let open Expr.Infix in
    match obj with
    | [] -> ([], Expr.true_)
    | r :: obj' -> (
        let lst1, pi1 = get_vals' r prop pc gamma in
        match pi1 with
        | Lit (Bool false) -> (lst1, pi1)
        | _ ->
            if is_sat [ pc && pi1 ] gamma then
              let lst2, pi2 = get_vals obj' prop (pc && pi1) gamma in
              (lst1 @ lst2, pi1 && pi2)
            else (lst1, pi1))

  let get (obj : ot) (prop : vt) (pc : vt) (gamma : Type_env.t) : (vt * vt) list
      =
    let lst, not_found_pc_ = get_vals obj prop pc gamma in
    let lst' = branch_types lst in
    let lst'' =
      List.fold_left
        (fun acc (l, pc') ->
          let ite = mk_ite_v l in
          (ite, pc') :: acc)
        [] lst'
    in
    let ret =
      match not_found_pc_ with
      | Lit (Bool false) -> lst''
      | Lit (Bool true) -> (undef, not_found_pc_) :: lst''
      | _ ->
          if is_sat [ not_found_pc_; pc ] gamma then
            (undef, not_found_pc_) :: lst''
          else lst''
    in
    if ret = [] then failwith "ERROR: loglifting_get() should not return empty"
    else ret

  let delete (obj : ot) (prop : vt) : ot = set obj prop none

  let pp_map fmt v =
    let map_iter f m = SMap.iter (fun k d -> f (k, d)) m in
    Fmt.iter ~sep:Fmt.comma map_iter
      (fun fmt (key, data) -> Fmt.pf fmt {|%a: %a|} Fmt.string key SVal.pp data)
      fmt v

  let rec pp_t' fmt (t' : ot') =
    match t' with
    | Srec (prop, v) -> Fmt.pf fmt "Srec(%a -> %a)" SVal.pp prop SVal.pp v
    | Crec map -> Fmt.pf fmt "[%a]" pp_map map

  and pp_list fmt (l : ot' list) =
    let list_iter f l = List.iter (fun o' -> f o') l in
    Fmt.iter ~sep:Fmt.comma list_iter
      (fun fmt o' -> Fmt.pf fmt "%a" pp_t' o')
      fmt l

  let pp fmt (o : t) : unit = Fmt.pf fmt "@[<hov 2> { %a } @]" pp_list o
end

module M = struct
  module Heap = MakeHeap (LogLiftingObj)
  include Heap

  let execute_action
      ?matching:_
      (action : string)
      (heap : t)
      (pfs : PFS.t)
      (gamma : Type_env.t)
      (args : vt list) : action_ret =
    if action = JSILNames.getCell then
      match args with
      | [ loc; prop ] -> get_cell heap pfs gamma loc prop
      | _ -> raise (Failure "Internal Error. execute_action")
    else if action = JSILNames.setCell then
      match args with
      | [ loc; prop; v ] -> set_cell heap pfs gamma loc prop v
      | _ -> raise (Failure "Internal Error. execute_action. setCell")
    else if action = JSILNames.delCell then
      match args with
      | [ loc; prop ] -> remove_cell heap pfs gamma loc prop
      | _ -> raise (Failure "Internal Error. execute_action. delCell")
    else if action = JSILNames.alloc then
      match args with
      | [ Lit Empty; m_loc ] -> alloc heap pfs None (Some m_loc)
      | [ loc; m_loc ] -> alloc heap pfs (Some loc) (Some m_loc)
      | _ -> raise (Failure "Internal Error. execute_action. alloc")
    else if action = JSILNames.delObj then
      match args with
      | [ loc ] -> delete_object heap pfs gamma loc
      | _ -> raise (Failure "Internal Error. execute_action. delObj")
    else if action = JSILNames.getAllProps then
      match args with
      | [ loc ] -> get_full_domain heap pfs gamma loc
      | _ -> raise (Failure "Internal Error. execute_action. getAllProps")
    else if action = JSILNames.getMetadata then
      match args with
      | [ loc ] -> get_metadata heap pfs gamma loc
      | _ -> raise (Failure "Internal Error. execute_action. getMetadata")
    else if action = JSILNames.setMetadata then
      match args with
      | [ loc; loc_m ] -> set_metadata heap pfs gamma loc loc_m
      | _ -> raise (Failure "Internal Error. execute_action. setMetadata")
    else if action = JSILNames.delMetadata then
      match args with
      | [ _ ] -> Ok [ (heap, [], [], []) ]
      | _ -> raise (Failure "Internal Error. execute_action. delMetadata")
    else if action = JSILNames.getProps then
      match args with
      | [ loc; props ] -> get_partial_domain heap pfs gamma loc props
      | _ -> raise (Failure "Internal Error. execute_action. getProps")
    else if action = JSILNames.setProps then
      match args with
      | [ loc; props ] -> set_domain heap pfs gamma loc props
      | _ -> raise (Failure "Internal Error. execute_action")
    else if action = JSILNames.delProps then
      match args with
      | [ loc; _ ] -> remove_domain heap pfs gamma loc
      | _ -> raise (Failure "Internal Error. execute_action. remove_domain")
    else raise (Failure "Internal Error. execute_action")

  let ga_to_setter (a_id : string) : string =
    if a_id = JSILNames.aCell then JSILNames.setCell
    else if a_id = JSILNames.aMetadata then JSILNames.setMetadata
    else if a_id = JSILNames.aProps then JSILNames.setProps
    else raise (Failure "DEATH. ga_to_setter")

  let ga_to_getter (a_id : string) : string =
    if a_id = JSILNames.aCell then JSILNames.getCell
    else if a_id = JSILNames.aMetadata then JSILNames.getMetadata
    else if a_id = JSILNames.aProps then JSILNames.getProps
    else raise (Failure "DEATH. ga_to_setter")

  let ga_to_deleter (a_id : string) : string =
    if a_id = JSILNames.aCell then JSILNames.delCell
    else if a_id = JSILNames.aMetadata then JSILNames.delMetadata
    else if a_id = JSILNames.aProps then JSILNames.delProps
    else raise (Failure "DEATH. ga_to_setter")

  let is_overlapping_asrt (a : string) : bool =
    if a = JSILNames.aMetadata then true else false
end
