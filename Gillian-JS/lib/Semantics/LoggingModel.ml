open Javert_utils
open Gillian.Gil_syntax
open Gillian.Logic
module L = Logging
module SVal = Gillian.Symbolic.Values
module PFS = Gillian.Symbolic.Pure_context
module Type_env = Gillian.Symbolic.Type_env
module Mem = MemoryTypes

type vt = Mem.vt
type t = Mem.t
type err_t = Mem.err_t
type i_fix_t = Mem.i_fix_t
type action_ret = Mem.action_ret

let get_loc_name pfs gamma = Gillian.Logic.FOSolver.resolve_loc_name ~pfs ~gamma

let fresh_loc ?(loc : vt option) (pfs : PFS.t) (gamma : Type_env.t) :
    string * vt * Expr.t list =
  match loc with
  | Some loc -> (
      let loc_name = get_loc_name pfs gamma loc in
      match loc_name with
      | Some loc_name ->
          if Names.is_aloc_name loc_name then (loc_name, Expr.ALoc loc_name, [])
          else (loc_name, Expr.Lit (Loc loc_name), [])
      | None ->
          let al = ALoc.alloc () in
          (al, ALoc al, [ Expr.BinOp (ALoc al, Equal, loc) ]))
  | None ->
      let al = ALoc.alloc () in
      (al, ALoc al, [])

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
  SHeap.init_object heap loc_name ~is_empty:ie mv;
  Ok [ (heap, [ loc ], [], []) ]

let set_cell
    (heap : t)
    (pfs : PFS.t)
    (gamma : Type_env.t)
    (loc : vt)
    (prop : vt)
    (v : vt) : action_ret =
  let loc_name, _, new_pfs = fresh_loc ~loc pfs gamma in
  SHeap.set_fv_pair heap loc_name prop v;
  Ok [ (heap, [], new_pfs, []) ]

let get_cell
    (heap : t)
    (pfs : PFS.t)
    (gamma : Type_env.t)
    (loc : vt)
    (prop : vt) : action_ret =
  let loc_name = get_loc_name pfs gamma loc in

  L.tmi (fun m ->
      m "@[<h>GetCell: resolved location: %a -> %a@]" SVal.pp loc
        Fmt.(option ~none:(any "None") string)
        loc_name);

  let make_gc_error
      (loc_name : string)
      (prop : vt)
      (props : vt list)
      (dom : vt option) : err_t =
    let loc = Expr.loc_from_loc_name loc_name in
    (*  failing_constraint *)
    let ff =
      Expr.conjunct
        (List.map
           (fun prop' -> Expr.UnOp (Not, BinOp (prop, Equal, prop')))
           props)
    in

    let fixes_exist_props : i_fix_t list list =
      List.map
        (fun prop' -> [ Mem.FPure (Expr.BinOp (prop, Equal, prop')) ])
        props
    in
    let fix_new_property : i_fix_t list = [ FCell (loc, prop); FPure ff ] in

    match dom with
    | Some dom ->
        let ff' : Expr.t = BinOp (prop, SetMem, dom) in
        let ff'' : Expr.t = BinOp (ff, And, ff') in
        let fix_new_property' : i_fix_t list = FPure ff' :: fix_new_property in
        ([ loc ], fix_new_property' :: fixes_exist_props, ff'')
    | None -> ([ loc; prop ], fix_new_property :: fixes_exist_props, ff)
  in

  let get_cell_from_loc loc_name =
    Option.fold
      ~some:(fun ((fv_list, dom), mtdt) ->
        L.tmi (fun m -> m "fv_list: %a" SFVL.pp fv_list);
        L.tmi (fun m ->
            m "domain: %a" Fmt.(option ~none:(any "None") Expr.pp) dom);
        L.tmi (fun m ->
            m "metadata: %a" Fmt.(option ~none:(any "None") Expr.pp) mtdt);
        match SFVL.get prop fv_list with
        | Some ffv -> Ok [ (heap, [ loc; prop; ffv ], [], []) ]
        | None -> (
            match
              ( dom,
                SFVL.get_first
                  (fun name -> FOSolver.is_equal ~pfs ~gamma name prop)
                  fv_list )
            with
            | None, None ->
                Error
                  [
                    make_gc_error loc_name prop (SFVL.field_names fv_list) None;
                  ]
            | _, Some (ffn, ffv) -> Ok [ (heap, [ loc; ffn; ffv ], [], []) ]
            | Some dom, None ->
                let a_set_inclusion : Expr.t =
                  UnOp (Not, BinOp (prop, SetMem, dom))
                in
                if
                  FOSolver.check_entailment Containers.SS.empty pfs
                    [ a_set_inclusion ] gamma
                then (
                  let new_domain : Expr.t =
                    NOp (SetUnion, [ dom; ESet [ prop ] ])
                  in
                  let new_domain =
                    Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs)
                      new_domain
                  in
                  let fv_list' = SFVL.add prop (Lit Nono) fv_list in
                  SHeap.set heap loc_name fv_list' (Some new_domain) mtdt;
                  Ok [ (heap, [ loc; prop; Lit Nono ], [], []) ])
                else
                  let f_names : Expr.t list = SFVL.field_names fv_list in
                  let full_knowledge : Expr.t =
                    BinOp (dom, Equal, ESet f_names)
                  in
                  if
                    FOSolver.check_entailment Containers.SS.empty pfs
                      [ full_knowledge ] gamma
                  then (
                    L.verbose (fun m -> m "GET CELL will branch\n");
                    let rets : (t * vt list * Expr.t list * 'a) option list =
                      List.map
                        (fun (f_name, f_value) ->
                          let new_f : Expr.t = BinOp (f_name, Equal, prop) in
                          let sat =
                            FOSolver.check_satisfiability
                              ~time:"JS getCell branch: heap"
                              (new_f :: PFS.to_list pfs) gamma
                          in
                          match sat with
                          | false -> None
                          | true ->
                              (* Cases in which the prop exists *)
                              let heap' = SHeap.copy heap in
                              Some
                                (heap', [ loc; f_name; f_value ], [ new_f ], []))
                        (SFVL.to_list fv_list)
                    in

                    let rets =
                      List.map Option.get (List.filter Option.is_some rets)
                    in

                    (* I need the case in which the prop does not exist *)
                    let new_f : Expr.t =
                      UnOp (Not, BinOp (prop, SetMem, dom))
                    in
                    let sat =
                      FOSolver.check_satisfiability
                        ~time:"JS getCell branch: domain"
                        (new_f :: PFS.to_list pfs) gamma
                    in
                    let dom_ret =
                      match sat with
                      | false -> []
                      | true ->
                          [ (heap, [ loc; prop; Lit Nono ], [ new_f ], []) ]
                    in
                    Ok (rets @ dom_ret))
                  else
                    Error
                      [
                        make_gc_error loc_name prop (SFVL.field_names fv_list)
                          (Some dom);
                      ]))
      ~none:
        (Error
           [ ([], [ [ Mem.FLoc loc; Mem.FCell (loc, prop) ] ], Expr.false_) ])
      (SHeap.get heap loc_name)
  in

  let result =
    Option.fold ~some:get_cell_from_loc
      ~none:
        (Error
           [ ([], [ [ Mem.FLoc loc; Mem.FCell (loc, prop) ] ], Expr.false_) ])
      loc_name
  in
  result

let remove_cell
    (heap : t)
    (pfs : PFS.t)
    (gamma : Type_env.t)
    (loc : vt)
    (prop : vt) : action_ret =
  let heap = SHeap.copy heap in
  let f (loc_name : string) : unit =
    Option.fold
      ~some:(fun ((fv_list, dom), mtdt) ->
        SHeap.set heap loc_name (SFVL.remove prop fv_list) dom mtdt;
        ())
      ~none:() (SHeap.get heap loc_name)
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

  (match SHeap.get heap loc_name with
  | None -> SHeap.set heap loc_name SFVL.empty (Some dom) None
  | Some ((fv_list, _), mtdt) ->
      (* TODO: This probably needs to be a bit more sophisticated *)
      SHeap.set heap loc_name fv_list (Some dom) mtdt);
  Ok [ (heap, [], new_pfs, []) ]

let get_metadata (heap : t) (pfs : PFS.t) (gamma : Type_env.t) (loc : vt) :
    action_ret =
  let loc_name = get_loc_name pfs gamma loc in

  let make_gm_error (loc_name : string) : err_t =
    let loc = Expr.loc_from_loc_name loc_name in
    ([ loc ], [ [ FMetadata loc ] ], Expr.false_)
  in

  let f loc_name =
    let loc =
      if Names.is_aloc_name loc_name then Expr.ALoc loc_name
      else Expr.Lit (Loc loc_name)
    in
    match SHeap.get heap loc_name with
    | None -> Error [ make_gm_error loc_name ]
    | Some ((_, _), mtdt) ->
        Option.fold
          ~some:(fun mtdt -> Ok [ (heap, [ loc; mtdt ], [], []) ])
          ~none:(Error [ make_gm_error loc_name ])
          mtdt
  in

  Option.fold ~some:f
    ~none:
      (Error [ ([ loc ], [ [ Mem.FLoc loc; Mem.FMetadata loc ] ], Expr.false_) ])
    loc_name

let set_metadata
    (heap : t)
    (pfs : PFS.t)
    (gamma : Type_env.t)
    (loc : vt)
    (mtdt : vt) : action_ret =
  L.tmi (fun m -> m "Trying to set metadata.");
  let loc_name, _, new_pfs = fresh_loc ~loc pfs gamma in

  (match SHeap.get heap loc_name with
  | None -> SHeap.set heap loc_name SFVL.empty None (Some mtdt)
  | Some ((fv_list, dom), None) ->
      SHeap.set heap loc_name fv_list dom (Some mtdt)
  | Some ((fv_list, dom), Some omet) ->
      if omet <> Option.get (SVal.from_expr (Lit Null)) then
        PFS.extend pfs (BinOp (mtdt, Equal, omet))
      else SHeap.set heap loc_name fv_list dom (Some mtdt));
  L.tmi (fun m -> m "Done setting metadata.");
  Ok [ (heap, [], new_pfs, []) ]

let delete_object (heap : t) (pfs : PFS.t) (gamma : Type_env.t) (loc : vt) :
    action_ret =
  let loc_name = get_loc_name pfs gamma loc in

  match loc_name with
  | Some loc_name ->
      if SHeap.has_loc heap loc_name then (
        SHeap.remove heap loc_name;
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

  L.verbose (fun fmt -> fmt "Get partial domain");
  L.verbose (fun fmt -> fmt "Expected domain: %a" SVal.pp e_dom);

  let f loc_name =
    let loc = Expr.loc_from_loc_name loc_name in
    match SHeap.get heap loc_name with
    | None -> raise (Failure "DEATH. get_partial_domain. illegal loc_name")
    | Some ((_, None), _) ->
        raise (Failure "DEATH. get_partial_domain. missing domain")
    | Some ((fv_list, Some dom), mtdt) -> (
        L.verbose (fun fmt -> fmt "Domain: %a" Expr.pp dom);
        let none_fv_list, pos_fv_list =
          SFVL.partition (fun _ fv -> fv = Lit Nono) fv_list
        in
        (* Called from the entailment - compute all negative resource associated with
           the location whose name is loc_name *)
        let none_props = SFVL.field_names none_fv_list in
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
                (fun fv_list prop -> SFVL.add prop (Lit Nono) fv_list)
                pos_fv_list props
            in
            SHeap.set heap loc_name new_fv_list (Some e_dom) mtdt;
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
    match SHeap.get heap loc_name with
    | None ->
        (* This should never happen *)
        raise (Failure "DEATH. get_full_domain. illegal loc_name")
    | Some ((_, None), _) ->
        (* This is not correct *)
        raise (Failure "DEATH. TODO. get_full_domain. missing domain")
    | Some ((fv_list, Some dom), _) ->
        let props = SFVL.field_names fv_list in
        let a_set_equality : Expr.t = BinOp (dom, Equal, ESet props) in
        let solver_ret =
          FOSolver.check_entailment Containers.SS.empty pfs [ a_set_equality ]
            gamma
        in
        if solver_ret then
          let _, pos_fv_list =
            SFVL.partition (fun _ fv -> fv = Lit Nono) fv_list
          in
          Ok [ (heap, [ loc; EList (SFVL.field_names pos_fv_list) ], [], []) ]
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
      ~some:(fun ((fv_list, _), mtdt) ->
        SHeap.set heap loc_name fv_list None mtdt;
        ())
      ~none:() (SHeap.get heap loc_name)
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
