open Gillian
open Gillian.Gil_syntax
open Javert_utils
module GAsrt = Asrt
module SSubst = Gillian.Symbolic.Subst
module L = Logging
module SVal = Gillian.Symbolic.Values
module PFS = Gillian.Symbolic.Pure_context
module Type_env = Gillian.Symbolic.Type_env
module Recovery_tactic = Gillian.General.Recovery_tactic
open Gillian.Logic

module M = struct
  type init_data = unit
  type vt = SVal.t [@@deriving yojson, show]
  type ot' = Rec of (vt * vt) [@@deriving yojson]
  type ot = ot' list [@@deriving yojson]

  type t = {
    fvl : (string, ot) Hashtbl.t;
    cdom : (string, Expr.t option) Hashtbl.t;
    cmet : (string, Expr.t option) Hashtbl.t;
    sdom : (string, Expr.t option) Hashtbl.t;
    smet : (string, Expr.t option) Hashtbl.t;
  }
  [@@deriving yojson]

  let sure_is_nonempty _ = false

  type st = SSubst.t
  type i_fix_t = unit [@@deriving yojson, show]
  type err_t = vt list * i_fix_t list list * Expr.t [@@deriving yojson, show]

  type action_ret =
    ( (t * vt list * Expr.t list * (string * Type.t) list) list,
      err_t list )
    result

  type vts = Expr.Set.t

  (* Auxiliaries *)
  let is_c = Expr.is_concrete
  let has_loc (heap : t) (loc : string) : bool = Hashtbl.mem heap.fvl loc

  let remove (heap : t) (loc : string) : unit =
    Hashtbl.remove heap.fvl loc;
    Hashtbl.remove heap.cdom loc;
    Hashtbl.remove heap.cmet loc;
    Hashtbl.remove heap.sdom loc;
    Hashtbl.remove heap.smet loc

  let merge (a : 't option) (b : 't option) (f : 't -> 't -> 't) : 't option =
    match (a, b) with
    | a, None -> a
    | None, b -> b
    | Some a, Some b -> Some (f a b)

  let set_fvl (heap : t) (loc : string) (obj : ot option) : unit =
    let obj' =
      match obj with
      | None -> []
      | Some obj -> obj
    in
    Hashtbl.replace heap.fvl loc obj'

  let set_dom (heap : t) (loc : string) (dom : vt option) : unit =
    Hashtbl.remove heap.cdom loc;
    Hashtbl.remove heap.sdom loc;
    let add, rem =
      match dom with
      | Some x when not (is_c x) -> (heap.sdom, heap.cdom)
      | _ -> (heap.cdom, heap.sdom)
    in
    Hashtbl.replace add loc dom;
    Hashtbl.remove rem loc

  let set_met (heap : t) (loc : string) (met : vt option) : unit =
    Hashtbl.remove heap.cmet loc;
    Hashtbl.remove heap.smet loc;
    let add, rem =
      match met with
      | Some x when not (is_c x) -> (heap.smet, heap.cmet)
      | _ -> (heap.cmet, heap.smet)
    in
    Hashtbl.replace add loc met;
    Hashtbl.remove rem loc

  let get_fvl (heap : t) (loc : string) : ot option =
    Hashtbl.find_opt heap.fvl loc

  let get_dom (heap : t) (loc : string) : Expr.t option =
    let cdom = Option.value ~default:None (Hashtbl.find_opt heap.cdom loc) in
    let sdom = Option.value ~default:None (Hashtbl.find_opt heap.sdom loc) in
    merge cdom sdom (fun _ _ ->
        raise
          (Failure "Domain in both the concrete and symbolic part of the heap."))

  let get_met (heap : t) (loc : string) : Expr.t option =
    let cmet = Option.value ~default:None (Hashtbl.find_opt heap.cmet loc) in
    let smet = Option.value ~default:None (Hashtbl.find_opt heap.smet loc) in
    merge cmet smet (fun _ _ ->
        raise
          (Failure
             "MetaData in both the concrete and symbolic part of the heap."))

  let get_all (heap : t) (loc : string) =
    Option.map
      (fun sfvl -> ((sfvl, get_dom heap loc), get_met heap loc))
      (get_fvl heap loc)

  (* Logging *)
  let undef = Expr.lit Undefined
  let none = Expr.lit Nono
  let set_empty = Expr.Set.empty
  let set_summ a b = Expr.Set.union a b
  let set_diff a b = Expr.Set.diff a b
  let set_single a = Expr.Set.singleton a

  let ite (e : vt) (c1 : vt) (c2 : vt) : vt =
    let open Expr.Infix in
    (e && c1) || ((not e) && c2)

  let must_be cond pc gamma =
    not (FOSolver.check_satisfiability [ Expr.Infix.not cond; pc ] gamma)

  let rec mk_ite_v (lst : (vt * vt) list) : vt =
    let check_none v = if Expr.equal v none then undef else v in
    match lst with
    | [] -> undef
    | [ (v, cond) ] ->
        let v' = check_none v in
        ite cond v' undef
    | (v, cond) :: rest ->
        let v' = check_none v in
        ite cond v' (mk_ite_v rest)

  let to_list_aux' (o : ot') (tbl : (vt, vt) Hashtbl.t) :
      vts * vts * (vt, vt) Hashtbl.t =
    match o with
    | Rec (p, v) when Expr.equal v none -> (set_empty, set_single p, tbl)
    | Rec (p, v) ->
        Hashtbl.replace tbl p v;
        (set_single p, set_empty, tbl)

  let rec to_list_aux (o : ot) (tbl : (vt, vt) Hashtbl.t) :
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

  let to_obj (pairs : (vt * vt) list) : ot =
    List.fold_left (fun acc (p, v) -> Rec (p, v) :: acc) [] pairs

  let get_fields o : vt list =
    let set1, _, _ = to_list_aux o (Hashtbl.create 0) in
    Expr.Set.to_list set1

  let set (heap : t) (loc : string) (field : Expr.t) (value : Expr.t) : unit =
    let obj =
      match Hashtbl.find_opt heap.fvl loc with
      | None -> []
      | Some obj -> obj
    in
    let obj' = Rec (field, value) :: obj in
    set_fvl heap loc (Some obj')

  let rec get_vals' (obj : ot') (prop : vt) (pc : vt) (gamma : Type_env.t) :
      (vt * vt) list * vt =
    let open Expr.Infix in
    match obj with
    | Rec (prop', v) ->
        if FOSolver.check_satisfiability [ prop == prop'; pc ] gamma then
          ([ (v, prop == prop') ], not (prop == prop'))
        else ([], Expr.true_)

  and get_vals (obj : ot) (prop : vt) (pc : vt) (gamma : Type_env.t) :
      (vt * vt) list * vt =
    let open Expr.Infix in
    match obj with
    | [] -> ([], Expr.true_)
    | r :: obj' ->
        let lst1, pi1 = get_vals' r prop pc gamma in
        if Expr.equal pi1 Expr.false_ then (lst1, pi1)
        else if FOSolver.check_satisfiability [ pc; pi1 ] gamma then
          let lst2, pi2 = get_vals obj' prop (pc && pi1) gamma in
          (lst1 @ lst2, pi1 && pi2)
        else (lst1, pi1)

  let get (obj : ot) (prop : vt) (pc : vt) (gamma : Type_env.t) : (vt * vt) list
      =
    let lst, not_found_pc = get_vals obj prop pc gamma in
    if Expr.equal not_found_pc Expr.true_ then (undef, not_found_pc) :: lst
    else lst

  (* Default *)
  let pp_i_fix ft (_ : i_fix_t) : unit = Fmt.pf ft "@[<h>i_fix_t=unit@]"

  let get_failing_constraint (err : err_t) : Expr.t =
    let _, _, f = err in
    f

  let pp_err ft (err : err_t) : unit =
    let open Fmt in
    let vs, fixes, f = err in
    let pp_fixes ft fix = pf ft "[%a]" (list ~sep:comma pp_i_fix) fix in
    pf ft "@[<h><[%a], %a, %a>@]" (list ~sep:comma SVal.pp) vs Expr.pp f
      (list ~sep:semi pp_fixes) fixes

  let get_recovery_tactic (_ : t) (_ : err_t) =
    Recovery_tactic.{ try_fold = None; try_unfold = None }

  let assertions ?to_keep:_ (_ : t) : GAsrt.t =
    failwith "Implement assertions() in Logging Memory"

  let lvars (heap : t) : Containers.SS.t =
    let to_ss (pairs : (vt * vt) list) : SS.t =
      let gllv = Expr.lvars in
      List.fold_left
        (fun ac (e_field, e_val) ->
          SS.union ac (SS.union (gllv e_field) (gllv e_val)))
        SS.empty pairs
    in

    let lvars_fvl =
      Hashtbl.fold
        (fun _ fvl ac -> Var.Set.union (to_ss @@ to_list fvl) ac)
        heap.fvl Var.Set.empty
    in
    let lvars_dom =
      Hashtbl.fold
        (fun _ oe ac ->
          let voe = Option.fold ~some:Expr.lvars ~none:Var.Set.empty oe in
          Var.Set.union voe ac)
        heap.sdom Var.Set.empty
    in
    let lvars_met =
      Hashtbl.fold
        (fun _ oe ac ->
          let voe = Option.fold ~some:Expr.lvars ~none:Var.Set.empty oe in
          Var.Set.union voe ac)
        heap.smet Var.Set.empty
    in
    List.fold_left SS.union Var.Set.empty [ lvars_fvl; lvars_met; lvars_dom ]

  let alocs (heap : t) : Var.Set.t =
    let union = Var.Set.union in
    let to_ss (pairs : (vt * vt) list) : SS.t =
      List.fold_left
        (fun ac (e_field, e_val) ->
          SS.union ac (SS.union (Expr.alocs e_field) (Expr.alocs e_val)))
        SS.empty pairs
    in
    Var.Set.empty
    |> Hashtbl.fold
         (fun _ fvl ac -> Var.Set.union (to_ss @@ to_list fvl) ac)
         heap.fvl
    |> Hashtbl.fold
         (fun _ oe ac ->
           Option.fold ~some:(fun oe -> union (Expr.alocs oe) ac) ~none:ac oe)
         heap.sdom
    |> Hashtbl.fold
         (fun _ oe ac ->
           Option.fold ~some:(fun oe -> union (Expr.alocs oe) ac) ~none:ac oe)
         heap.smet

  let clean_up ?(keep = Expr.Set.empty) (heap : t) : Expr.Set.t * Expr.Set.t =
    Hashtbl.reset heap.fvl;
    Hashtbl.reset heap.cdom;
    Hashtbl.reset heap.sdom;
    Hashtbl.reset heap.cmet;
    Hashtbl.reset heap.smet;
    (Expr.Set.empty, keep)

  (* TODO *)
  let substitution_in_place ~pfs:_ ~gamma:_ (_ : st) (heap : t) =
    (* SHeap.substitution_in_place subst heap; *)
    [ (heap, Expr.Set.empty, []) ]

  let pp_ot fmt (o : ot) : unit =
    let pp_rec fmt (t' : ot') =
      match t' with
      | Rec (prop, v) -> Fmt.pf fmt "Rec(%a -> %a)" SVal.pp prop SVal.pp v
    in
    let pp_ot' fmt (l : ot' list) =
      Fmt.iter ~sep:Fmt.comma List.iter
        (fun fmt o' -> Fmt.pf fmt "%a" pp_rec o')
        fmt l
    in
    Fmt.pf fmt "@[<hov 2> { %a } @]" pp_ot' o

  let pp_ot' fmt (entry : (string, ot) Hashtbl.t) : unit =
    let tbl_iter f m = Hashtbl.iter (fun k d -> f (k, d)) m in
    Fmt.iter ~sep:Fmt.comma tbl_iter
      (fun ppf (key, data) -> Fmt.pf ppf {|%s -> %a|} key pp_ot data)
      fmt entry

  let pp' fmt (entry : (string, Expr.t option) Hashtbl.t) : unit =
    let tbl_iter f m = Hashtbl.iter (fun k d -> f (k, d)) m in
    Fmt.iter ~sep:Fmt.comma tbl_iter
      (fun ppf (key, data) ->
        match data with
        | Some e -> Fmt.pf ppf "%s -> %a" key SVal.pp e
        | None -> Fmt.pf ppf "%s -> <none>" key)
      fmt entry

  let pp fmt (heap : t) : unit =
    Fmt.record ~sep:Fmt.semi
      [
        Fmt.field "fvl" (fun h -> h.fvl) pp_ot';
        Fmt.field "cdom" (fun h -> h.cdom) pp';
        Fmt.field "cmet" (fun h -> h.cmet) pp';
        Fmt.field "sdom" (fun h -> h.sdom) pp';
        Fmt.field "smet" (fun h -> h.smet) pp';
      ]
      fmt heap

  (* TODO *)
  let pp_by_need locs fmt heap = SHeap.pp_by_need locs fmt heap

  (* TODO *)
  let get_print_info = SHeap.get_print_info

  let copy (heap : t) : t =
    {
      fvl = Hashtbl.copy heap.fvl;
      cdom = Hashtbl.copy heap.cdom;
      sdom = Hashtbl.copy heap.sdom;
      cmet = Hashtbl.copy heap.cmet;
      smet = Hashtbl.copy heap.smet;
    }

  let init () : t =
    let open Config in
    {
      fvl = Hashtbl.create big_tbl_size;
      cdom = Hashtbl.create big_tbl_size;
      sdom = Hashtbl.create big_tbl_size;
      cmet = Hashtbl.create big_tbl_size;
      smet = Hashtbl.create big_tbl_size;
    }

  let get_init_data _ = ()
  let clear (_ : t) = init () (* We don't maintain any context *)

  let get_loc_name pfs gamma =
    Gillian.Logic.FOSolver.resolve_loc_name ~pfs ~gamma

  let fresh_loc ?(loc : vt option) (pfs : PFS.t) (gamma : Type_env.t) :
      string * vt * Expr.t list =
    match loc with
    | Some loc -> (
        let loc_name = get_loc_name pfs gamma loc in
        match loc_name with
        | Some loc_name ->
            if Names.is_aloc_name loc_name then
              (loc_name, Expr.ALoc loc_name, [])
            else (loc_name, Expr.Lit (Loc loc_name), [])
        | None ->
            let al = ALoc.alloc () in
            (al, ALoc al, [ Expr.BinOp (ALoc al, Equal, loc) ]))
    | None ->
        let al = ALoc.alloc () in
        (al, ALoc al, [])

  let init_object
      (heap : t)
      (loc : string)
      ?is_empty:(ie = false)
      (mtdt : Expr.t option) : unit =
    if Hashtbl.mem heap.fvl loc then raise (Failure "Illegal init_object")
    else
      let dom : Expr.t option = if ie then None else Some (ESet []) in
      set_dom heap loc dom;
      set_met heap loc mtdt;
      Hashtbl.replace heap.fvl loc []

  let alloc
      (heap : t)
      (pfs : PFS.t)
      (loc : vt option)
      ?is_empty:(ie = false)
      (mv : vt option) : action_ret =
    let (loc_name : string), (loc : Expr.t) =
      match (loc : Expr.t option) with
      | None ->
          let loc_name = ALoc.alloc () in
          (loc_name, ALoc loc_name)
      | Some (Lit (Loc loc)) -> (loc, Lit (Loc loc))
      | Some (ALoc loc) -> (loc, ALoc loc)
      | Some (LVar v) ->
          let loc_name = ALoc.alloc () in
          PFS.extend pfs (BinOp (LVar v, Equal, ALoc loc_name));
          (loc_name, ALoc loc_name)
      | Some le ->
          raise
            (Failure
               (Printf.sprintf "Alloc with a non-loc loc argument: %s"
                  ((Fmt.to_to_string Expr.pp) le)))
    in
    init_object heap loc_name ~is_empty:ie mv;
    Ok [ (heap, [ loc ], [], []) ]

  let set_cell
      (heap : t)
      (pfs : PFS.t)
      (gamma : Type_env.t)
      (loc : vt)
      (prop : vt)
      (v : vt) : action_ret =
    let loc_name, _, new_pfs = fresh_loc ~loc pfs gamma in
    set heap loc_name prop v;
    Ok [ (heap, [], new_pfs, []) ]

  let get_cell
      (heap : t)
      (pfs : PFS.t)
      (gamma : Type_env.t)
      (loc : vt)
      (prop : vt) : action_ret =
    let loc_name = get_loc_name pfs gamma loc in

    let get_cell_from_loc loc_name =
      let obj = Hashtbl.find_opt heap.fvl loc_name in
      match obj with
      | None -> Error [ ([], [], Expr.false_) ]
      | Some o ->
          let pc = Expr.conjunct (PFS.to_list pfs) in
          let values = get o prop pc gamma in
          let expr = mk_ite_v values in
          Ok [ (heap, [ loc; prop; expr ], [], []) ]
    in

    let result =
      Option.fold ~some:get_cell_from_loc
        ~none:(Error [ ([], [], Expr.false_) ])
        loc_name
    in
    result

  let remove_cell
      (heap : t)
      (pfs : PFS.t)
      (gamma : Type_env.t)
      (loc : vt)
      (prop : vt) : action_ret =
    let f (loc_name : string) : unit =
      Option.fold
        ~some:(fun _ -> set heap loc_name prop none)
        ~none:()
        (Hashtbl.find_opt heap.fvl loc_name)
    in
    Option.fold ~some:f ~none:() (get_loc_name pfs gamma loc);
    Ok [ (heap, [], [], []) ]

  let set_domain
      (heap : t)
      (pfs : PFS.t)
      (gamma : Type_env.t)
      (loc : vt)
      (dom : vt) : action_ret =
    let loc_name, _, new_pfs = fresh_loc ~loc pfs gamma in

    (match Hashtbl.find_opt heap.fvl loc_name with
    | None ->
        set_fvl heap loc_name None;
        set_met heap loc_name None;
        set_dom heap loc_name (Some dom)
    | Some _ -> set_dom heap loc_name (Some dom));
    Ok [ (heap, [], new_pfs, []) ]

  let get_metadata (heap : t) (pfs : PFS.t) (gamma : Type_env.t) (loc : vt) :
      action_ret =
    let make_gm_error (loc_name : string) : err_t =
      let loc = Expr.loc_from_loc_name loc_name in
      ([ loc ], [], Expr.false_)
    in

    let f loc_name =
      let loc =
        if Names.is_aloc_name loc_name then Expr.ALoc loc_name
        else Expr.Lit (Loc loc_name)
      in
      match Hashtbl.find_opt heap.fvl loc_name with
      | None -> Error [ make_gm_error loc_name ]
      | Some _ ->
          let mtdt = get_met heap loc_name in
          Option.fold
            ~some:(fun mtdt -> Ok [ (heap, [ loc; mtdt ], [], []) ])
            ~none:(Error [ make_gm_error loc_name ])
            mtdt
    in
    let loc_name = get_loc_name pfs gamma loc in
    Option.fold ~some:f ~none:(Error [ ([ loc ], [], Expr.false_) ]) loc_name

  let set_metadata
      (heap : t)
      (pfs : PFS.t)
      (gamma : Type_env.t)
      (loc : vt)
      (mtdt : vt) : action_ret =
    let loc_name, _, new_pfs = fresh_loc ~loc pfs gamma in

    (match Hashtbl.find_opt heap.fvl loc_name with
    | None ->
        set_fvl heap loc_name None;
        set_met heap loc_name (Some mtdt);
        set_dom heap loc_name None
    | Some _ -> (
        match get_met heap loc_name with
        | None -> set_met heap loc_name (Some mtdt)
        | Some omet ->
            if omet <> Option.get (SVal.from_expr (Lit Null)) then
              PFS.extend pfs (BinOp (mtdt, Equal, omet))
            else set_met heap loc_name (Some mtdt)));
    Ok [ (heap, [], new_pfs, []) ]

  let delete_object (heap : t) (pfs : PFS.t) (gamma : Type_env.t) (loc : vt) :
      action_ret =
    let loc_name = get_loc_name pfs gamma loc in

    match loc_name with
    | Some loc_name ->
        if has_loc heap loc_name then (
          remove heap loc_name;
          Ok [ (heap, [], [], []) ])
        else raise (Failure "delete_obj. Unknown Location")
    | None -> raise (Failure "delete_obj. Unknown Location")

  let get_partial_domain
      (heap : t)
      (pfs : PFS.t)
      (gamma : Type_env.t)
      (loc : vt)
      (e_dom : vt) : action_ret =
    let loc_name = get_loc_name pfs gamma loc in

    let f loc_name =
      let loc = Expr.loc_from_loc_name loc_name in
      match get_all heap loc_name with
      | None -> raise (Failure "DEATH. get_partial_domain. illegal loc_name")
      | Some ((_, None), _) ->
          raise (Failure "DEATH. get_partial_domain. missing domain")
      | Some ((fv_list, Some dom), mtdt) -> (
          let pairs = to_list fv_list in
          L.verbose (fun fmt -> fmt "Domain: %a" Expr.pp dom);
          let none_fv_list, pos_fv_list =
            List.partition (fun (_, fv) -> fv = Expr.Lit Nono) pairs
          in
          (* Called from the entailment - compute all negative resource associated with
             the location whose name is loc_name *)
          let none_props, _ = List.split none_fv_list in
          L.verbose (fun fmt ->
              fmt "None-props in heap: %a"
                Fmt.(brackets (list ~sep:comma Expr.pp))
                none_props);
          let dom' = Expr.BinOp (dom, SetDiff, ESet none_props) in
          let dom'' =
            Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) dom'
          in

          (* Expected dom - dom *)
          let dom_diff = Expr.BinOp (e_dom, SetDiff, dom'') in
          let dom_diff' =
            Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) dom_diff
          in

          (* if dom_diff' != {} then we have to put the excess properties in the heap as nones *)
          match dom_diff' with
          | ESet props ->
              let new_fv_list =
                List.fold_left
                  (fun fv_list prop -> (prop, Expr.Lit Nono) :: fv_list)
                  pos_fv_list props
              in
              set_fvl heap loc_name (Some (to_obj new_fv_list));
              set_dom heap loc_name (Some e_dom);
              set_met heap loc_name mtdt;
              Ok [ (heap, [ loc; e_dom ], [], []) ]
          | _ -> raise (Failure "DEATH. get_partial_domain. dom_diff"))
    in
    let result =
      Option.fold ~some:f ~none:(Error [ ([ loc ], [], Expr.false_) ]) loc_name
    in
    result

  let get_full_domain (heap : t) (pfs : PFS.t) (gamma : Type_env.t) (loc : vt) :
      action_ret =
    let loc_name = get_loc_name pfs gamma loc in
    let f loc_name =
      let loc = Expr.loc_from_loc_name loc_name in
      match get_all heap loc_name with
      | None ->
          (* This should never happen *)
          raise (Failure "DEATH. get_full_domain. illegal loc_name")
      | Some ((_, None), _) ->
          (* This is not correct *)
          raise (Failure "DEATH. TODO. get_full_domain. missing domain")
      | Some ((fv_list, Some dom), _) ->
          let props = get_fields fv_list in
          let pairs = to_list fv_list in
          let a_set_equality : Expr.t = BinOp (dom, Equal, ESet props) in
          let solver_ret =
            FOSolver.check_entailment Containers.SS.empty pfs [ a_set_equality ]
              gamma
          in
          if solver_ret then
            let _, pos_fv_list =
              List.partition (fun (_, fv) -> fv = Expr.Lit Nono) pairs
            in
            let final =
              List.fold_left (fun acc (p, _) -> p :: acc) [] pos_fv_list
            in
            Ok [ (heap, [ loc; EList final ], [], []) ]
          else raise (Failure "DEATH. TODO. get_full_domain. incomplete domain")
    in

    let result =
      Option.fold ~some:f ~none:(Error [ ([ loc ], [], Expr.false_) ]) loc_name
    in
    result

  let remove_domain (heap : t) (pfs : PFS.t) (gamma : Type_env.t) (loc : vt) :
      action_ret =
    let f (loc_name : string) : unit =
      Option.fold
        ~some:(fun _ ->
          set_dom heap loc_name None;
          ())
        ~none:()
        (Hashtbl.find_opt heap.fvl loc_name)
    in
    Option.fold ~some:f ~none:() (get_loc_name pfs gamma loc);
    Ok [ (heap, [], [], []) ]

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

  let mem_constraints (_ : t) : Expr.t list = []

  let is_overlapping_asrt (a : string) : bool =
    if a = JSILNames.aMetadata then true else false

  let prop_abduce_none_in_js = [ "@call" ]
  let prop_abduce_both_in_js = [ "hasOwnProperty" ]
  let complete_fix_js (_ : i_fix_t) : Asrt.t list = []

  (* Fix completion: simple *)
  let complete_fix_jsil (_ : i_fix_t) : Asrt.t list = []

  (* An error can have multiple fixes *)
  let get_fixes (err : err_t) : Asrt.t list =
    let pp_fix ft res =
      let open Fmt in
      pf ft "@[<v 2>@[<h>[[ %a ]]@]@\n@]" Asrt.pp res
    in
    let _, fixes, _ = err in
    L.verbose (fun m ->
        m "@[<v 2>Memory: Fixes found:@\n%a@]"
          Fmt.(
            list ~sep:(any "@\n")
              (brackets (brackets (hbox (list ~sep:comma pp_i_fix)))))
          fixes);

    let complete =
      if !Js_config.js then complete_fix_js else complete_fix_jsil
    in

    let complete_ifixes (ifixes : i_fix_t list) : Asrt.t list =
      let completed_ifixes = List.map complete ifixes in
      let completed_ifixes = List_utils.list_product completed_ifixes in
      let completed_ifixes : Asrt.t list =
        List.map
          (fun fixes -> List.fold_right List.append fixes [])
          completed_ifixes
      in

      L.verbose (fun m ->
          m "@[<v 2>Memory: i-fixes completed: %d@\n%a"
            (List.length completed_ifixes)
            Fmt.(list ~sep:(any "@\n") pp_fix)
            completed_ifixes);

      completed_ifixes
    in

    (* Fixes hold lists of lists of i_fixes, *)
    List.concat_map complete_ifixes fixes

  let can_fix _ = true

  let sorted_locs_with_vals (heap : t) =
    let sorted_locs =
      Hashtbl.to_seq_keys heap.fvl |> List.of_seq |> List.sort compare
    in
    List.map (fun loc -> (loc, Option.get (get_all heap loc))) sorted_locs
end
