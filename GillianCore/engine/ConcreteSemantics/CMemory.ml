module type S = sig
  (** Type of GIL values *)
  type vt = CVal.M.t

  (** Type of GIL substitutions *)
  type st = CVal.CSubst.t

  (** Errors *)
  type err_t

  (** Type of GIL general states *)
  type t

  type action_ret = ASucc of (t * vt list) | AFail of err_t list

  (** Initialisation *)
  val init : unit -> t

  (** Execute action *)
  val execute_action : string -> t -> vt list -> action_ret

  (** State Copy *)
  val copy : t -> t

  (** Printer *)
  val pp : Format.formatter -> t -> unit

  val pp_err : Format.formatter -> err_t -> unit
end
