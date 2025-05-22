(**************************************************************************************)
(** This module provides printf-style functions over the basic printing functions provided
    by Coq. *)
(**************************************************************************************)

(** [Log.printf] is a standard [printf] function, except it automatically adds a newline
    at the end. *)
let printf fmt = Format.ksprintf (fun res -> Feedback.msg_notice (Pp.str res)) fmt

(** Same as [Log.printf] except it generates an error instead. *)
let error ?(loc : Loc.t option) fmt =
  Format.ksprintf (fun res -> CErrors.user_err ?loc (Pp.str res)) fmt

(** Print an [EConstr.t] to a string. *)
let show_econstr env sigma t : string =
  Pp.string_of_ppcmds @@ Printer.pr_econstr_env env sigma t

(** Print the internal representation of a [Constr.t] to a string. *)
let debug_constr t : string = t |> Constr.debug_print |> Pp.string_of_ppcmds
