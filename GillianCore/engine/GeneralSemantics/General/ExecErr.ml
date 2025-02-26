type ('value, 'state_err) t =
  | EProc of 'value  (** Incorrect procedure identifier *)
  | ESt of 'state_err  (** Memory Error *)
  | ECleanUp
  | EFailReached of { fail_code : string; fail_params : 'value list }
[@@deriving yojson]

let pp pp_val pp_state_err ft err =
  let open Fmt in
  match err with
  | EProc pid -> pf ft "@[<h>EProc(%a)@]" pp_val pid
  | ESt err -> (hbox pp_state_err) ft err
  | ECleanUp -> string ft "ECleanUp()"
  | EFailReached { fail_code; fail_params } ->
      pf ft "@[<h>EFailReached(%s, %a)@]" fail_code (list pp_val) fail_params
