open Gillian
open Gillian.Gil_syntax
module GAsrt = Asrt
module SSubst = Gillian.Symbolic.Subst
module L = Logging
module SVal = Gillian.Symbolic.Values
module PFS = Gillian.Symbolic.Pure_context
module Type_env = Gillian.Symbolic.Type_env
module Recovery_tactic = Gillian.General.Recovery_tactic

type init_data = unit
type vt = SVal.t [@@deriving yojson, show]

(** Type of JSIL general states *)
type t = SHeap.t [@@deriving yojson]

(** Type of JSIL substitutions *)
type st = SSubst.t

(** Errors *)
type i_fix_t =
  | FLoc of vt
  | FCell of vt * vt
  | FMetadata of vt
  | FPure of Expr.t
[@@deriving yojson, show]

type err_t = vt list * i_fix_t list list * Expr.t [@@deriving yojson, show]

type action_ret =
  ((t * vt list * Expr.t list * (string * Type.t) list) list, err_t list) result
