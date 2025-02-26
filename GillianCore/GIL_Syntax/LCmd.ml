(** {b GIL logic commands}. *)

module SS = Containers.SS

type t = TypeDef__.lcmd =
  | If of Expr.t * t list * t list  (** If-then-else     *)
  | Branch of Formula.t  (** branching on a FO formual *)
  | Macro of string * Expr.t list  (** Macro            *)
  | Assert of Formula.t  (** Assert           *)
  | Assume of Formula.t  (** Assume           *)
  | AssumeType of string * Type.t  (** Assume Type      *)
  | SpecVar of string list  (** Spec Var         *)
  | SL of SLCmd.t
  | IsSymbolic of string * Expr.t (* x := IsSymbolic(e) *)
  | IsSat of string * Formula.t (* x := IsSat(f) *)
  | NewSymVar of string * Expr.t (* x := NewSymVar(e) *)
  | NewSymVarName of string * string * Expr.t (* x := NewSymVarName(s,e) *)
  | NewSymVarArray of string * string * Expr.t * Expr.t (* x := NewSymVarArray(s,i,e) *)
  | Maximize of string * Expr.t (* x := Maximize(e) *)
  | Minimize of string * Expr.t (* x := Minimize(e) *)
  (*| Constraints of string (* c := Constraints() *)*)


  let rec map
    (f_l : (t -> t) option)
    (f_e : (Expr.t -> Expr.t) option)
    (f_p : (Formula.t -> Formula.t) option)
    (f_sl : (SLCmd.t -> SLCmd.t) option)
    (lcmd : t) : t =
  (* Functions to map over formulas, expressions, and sl-commands *)
  let f = map f_l f_e f_p f_sl in
  let map_e = Option.value ~default:(fun x -> x) f_e in
  let map_p = Option.value ~default:(fun x -> x) f_p in
  let map_sl = Option.value ~default:(fun x -> x) f_sl in

  (* Apply the given function to the logical command *)
  let mapped_lcmd = Option.fold ~some:(fun f -> f lcmd) ~none:lcmd f_l in

  (* Map over the elements of the command *)
  match mapped_lcmd with
  | Branch a -> Branch (map_p a)
  | If (e, l1, l2) -> If (map_e e, List.map f l1, List.map f l2)
  | Macro (s, l) -> Macro (s, List.map map_e l)
  | Assume a -> Assume (map_p a)
  | Assert a -> Assert (map_p a)
  | AssumeType _ -> mapped_lcmd
  | SpecVar _ -> mapped_lcmd
  | SL sl_cmd -> SL (map_sl sl_cmd)
  | IsSymbolic (x, e) -> IsSymbolic (x, map_e e)
  | IsSat (x, a) -> IsSat (x, map_p a)
  | NewSymVar (x, e) -> NewSymVar (x, map_e e)
  | NewSymVarName (x, s, e) -> NewSymVarName (x, s, map_e e)
  | NewSymVarArray (x, s, i, e) -> NewSymVarArray (x, s, i, map_e e)
  | Maximize (x, e) -> Maximize (x, map_e e)
  | Minimize (x, e) -> Minimize (x, map_e e)
  

let fold = List.fold_left SS.union SS.empty

let rec pvars (lcmd : t) : SS.t =
  let pvars_es es = fold (List.map Expr.pvars es) in
  let pvars_lcmds es = fold (List.map pvars es) in
  match lcmd with
  | If (e, lthen, lelse) ->
      SS.union (Expr.pvars e) (SS.union (pvars_lcmds lthen) (pvars_lcmds lelse))
  | Macro (_, es) -> pvars_es es
  | Branch pf | Assert pf | Assume pf -> Formula.pvars pf
  | AssumeType (x, _) ->
      if Names.is_pvar_name x then SS.singleton x else SS.empty
  | SpecVar _ -> SS.empty
  | SL slcmd -> SLCmd.pvars slcmd
  | IsSymbolic (x, e) -> SS.union (SS.singleton x) (Expr.pvars e)
  | IsSat (x, a) -> SS.union (SS.singleton x) (Formula.pvars a)
  | NewSymVar (x, e) -> SS.union (SS.singleton x) (Expr.pvars e)
  | NewSymVarName (x, s, e) -> SS.union (SS.singleton x) (SS.union (SS.singleton s) (Expr.pvars e))
  | NewSymVarArray (x, s, i, e) ->
     SS.union (SS.singleton x) (SS.union (SS.singleton s) (SS.union (Expr.pvars i) (Expr.pvars e)))
  | Maximize (x, e) -> SS.union (SS.singleton x) (Expr.pvars e)
  | Minimize (x, e) -> SS.union (SS.singleton x) (Expr.pvars e)


let rec lvars (lcmd : t) : SS.t =
  let lvars_es es = fold (List.map Expr.lvars es) in
  let lvars_lcmds es = fold (List.map lvars es) in
  match lcmd with
  | If (e, lthen, lelse) ->
      SS.union (Expr.lvars e) (SS.union (lvars_lcmds lthen) (lvars_lcmds lelse))
  | Macro (_, es) -> lvars_es es
  | Branch pf | Assert pf | Assume pf -> Formula.lvars pf
  | AssumeType (x, _) ->
      if Names.is_lvar_name x then SS.singleton x else SS.empty
  | SpecVar svars -> SS.of_list svars
  | SL slcmd -> SLCmd.lvars slcmd
  | IsSymbolic (_, e) -> Expr.lvars e 
  | IsSat (_, a) -> Formula.lvars a 
  | NewSymVar (_, e) -> Expr.lvars e 
  | NewSymVarName (_, _, e) -> Expr.lvars e 
  | NewSymVarArray (_, _, i, e) ->  SS.union (Expr.lvars i)  (Expr.lvars e) 
  | Maximize (_, e) -> Expr.lvars e 
  | Minimize (_, e) -> Expr.lvars e 

let rec locs (lcmd : t) : SS.t =
  let locs_es es = fold (List.map Expr.locs es) in
  let locs_lcmds es = fold (List.map locs es) in
  match lcmd with
  | If (e, lthen, lelse) ->
      SS.union (Expr.locs e) (SS.union (locs_lcmds lthen) (locs_lcmds lelse))
  | Macro (_, es) -> locs_es es
  | Branch pf | Assert pf | Assume pf -> Formula.locs pf
  | AssumeType _ -> SS.empty
  | SpecVar svars -> SS.of_list svars
  | SL slcmd -> SLCmd.locs slcmd
  | IsSymbolic (_, e) -> Expr.locs e
  | IsSat (_, a) -> Formula.locs a 
  | NewSymVar (_, e) -> Expr.locs e
  | NewSymVarName (_, _, e) -> Expr.locs e
  | NewSymVarArray (_, _, i, e) ->  SS.union (Expr.locs i)  (Expr.locs e) 
  | Maximize (_, e) -> Expr.locs e
  | Minimize (_, e) -> Expr.locs e

let rec pp fmt lcmd =
  let pp_list = Fmt.list ~sep:Fmt.semi pp in
  let pp_params = Fmt.list ~sep:Fmt.comma Expr.pp in
  match lcmd with
  | If (le, then_lcmds, else_lcmds) ->
      if List.length else_lcmds > 0 then
        Fmt.pf fmt "@[<hov 2>if (%a) then {@ %a@]@ @[<hov 2>} else {@ %a@]@ }"
          (Fmt.hbox Expr.pp) le pp_list then_lcmds pp_list else_lcmds
      else
        Fmt.pf fmt "if (@[<h>%a@]) @[<hov 2>then {@\n%a@]@\n}" Expr.pp le
          pp_list then_lcmds
  | Branch fo -> Fmt.pf fmt "branch (%a)" Formula.pp fo
  | Macro (name, lparams) -> Fmt.pf fmt "%s(@[%a@])" name pp_params lparams
  | Assert a -> Fmt.pf fmt "assert (@[%a@])" Formula.pp a
  | Assume a -> Fmt.pf fmt "assume (@[%a@])" Formula.pp a
  | AssumeType (x, t) -> Fmt.pf fmt "assume_type (%s, %s)" x (Type.str t)
  | SpecVar xs ->
      Fmt.pf fmt "spec_var (@[%a@])" (Fmt.list ~sep:Fmt.comma Fmt.string) xs
  | SL sl_cmd -> SLCmd.pp fmt sl_cmd
  | IsSymbolic (x, e) -> Fmt.pf fmt "%s := IsSymbolic (@[%a@])" x Expr.pp e
  | IsSat (x, a) -> Fmt.pf fmt "%s := IsSat (@[%a@])" x Formula.pp a
  | NewSymVar (x, e) -> Fmt.pf fmt "%s := NewSymVar (@[%a@])" x Expr.pp e
  | NewSymVarName (x, s, e) -> Fmt.pf fmt "%s := NewSymVarName (@[%s,%a@])" x s Expr.pp e
  | NewSymVarArray (x, s, i, e) -> Fmt.pf fmt "%s := NewSymVarArray (@[%s,%a,%a@])" x s Expr.pp i Expr.pp e
  | Maximize (x, e) -> Fmt.pf fmt "%s := Maximize (@[%a@])" x Expr.pp e
  | Minimize (x, e) -> Fmt.pf fmt "%s := Minimize (@[%a@])" x Expr.pp e