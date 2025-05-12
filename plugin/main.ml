open Prelude
open Ltac2_plugin

(** A testing signature.*)
let build_signature () : signature =
  { n_ctors = 2
  ; base_types = [| EConstr.to_constr Evd.empty @@ Lazy.force Consts.string |]
  ; ctor_names = [| "App"; "Lam" |]
  ; ctor_types = [| [ AT_term; AT_term ]; [ AT_base 0; AT_bind AT_term ] |]
  }

(*let term n = List.init n @@ fun _ -> AT_term in
let s =
  { n_ctors = 16
  ; base_types =
      [| EConstr.to_constr Evd.empty @@ Lazy.force Consts.nat
       ; EConstr.to_constr Evd.empty @@ Lazy.force Consts.string
      |]
  ; ctor_names =
      [| "csort"
       ; "cpi"
       ; "clam"
       ; "capp"
       ; "cunit"
       ; "ctt"
       ; "ctop"
       ; "cstar"
       ; "cbot"
       ; "cbot_elim"
       ; "pvec"
       ; "pvnil"
       ; "pvcons"
       ; "pvec_elim"
       ; "pvec_elimG"
       ; "pvec_elimP"
      |]
  ; ctor_types =
      [| [ AT_base 0; AT_base 1 ]
       ; [ AT_base 0; AT_term; AT_bind AT_term ]
       ; [ AT_base 0; AT_term; AT_bind AT_term ]
       ; term 2
       ; []
       ; []
       ; []
       ; []
       ; []
       ; AT_base 1 :: term 2
       ; term 4
       ; term 1
       ; term 3
       ; term 12
       ; term 12
       ; term 10
      |]
  }
in*)

(** We keep track of the generated operations using the [Libobject] API. The first step is
    to create a reference using [Summary.ref]. *)
let saved_ops : ops_all option ref = Summary.ref ~name:"autosubst_saved_ops_summary" None

(** We declare a [Libobject.obj], which gives us a function [update_saved_ops] to update
    the contents of [saved_ops]. Accessing the contents of [saved_ops] can be done by
    simply de-referencing: [!saved_ops].

    It is important that we call [Libobject.declare_object] at the toplevel. *)
let update_saved_ops : ops_all option -> Libobject.obj =
  Libobject.declare_object
    { (Libobject.default_object "autosubst_saved_ops_libobject") with
      cache_function = (fun v -> saved_ops := v)
    ; load_function = (fun _ v -> saved_ops := v)
    ; classify_function = (fun _ -> Keep)
    }

(** Given a signature, generate all relevant definitions and lemmas (i.e. add them to the
    global environment), and return the names of the generated operations. *)
let generate_operations (s : signature) : ops_all =
  let ops0 = Gen_ops_zero.generate s in
  let ops1 = Gen_ops_one.generate s ops0 in
  let re = Gen_ops_reify_eval.generate s ops0 ops1 in
  let congr = Gen_ops_congr.generate s ops0 in
  let bij = Gen_ops_bijection.generate s ops0 ops1 re congr in
  let pe = Gen_ops_push_eval.generate s ops0 ops1 re congr bij in
  { ops_ops0 = ops0
  ; ops_ops1 = ops1
  ; ops_re = re
  ; ops_congr = congr
  ; ops_bij = bij
  ; ops_pe = pe
  }

(** Main entry point for the plugin: generate level zero terms, operations, and lemmas. *)
let generate () =
  (* We use a testing signature (for the moment). *)
  let s = build_signature () in
  (* Generate the operations. *)
  let ops = generate_operations s in
  (* Save the operations. *)
  Lib.add_leaf @@ update_saved_ops (Some ops)

let reify_term_tac (t : EConstr.t) : (EConstr.t * EConstr.t) Proofview.tactic =
  let s = build_signature () in
  let ops =
    match !saved_ops with
    | None -> Log.error "reify_tac: must generate operations beforehand."
    | Some ops -> ops
  in
  monad_run_tactic @@ Reification.reify_term s ops t

let eval_term_tac (t : EConstr.t) : (EConstr.t * EConstr.t) Proofview.tactic =
  let s = build_signature () in
  let ops =
    match !saved_ops with
    | None -> Log.error "eval_tac: must generate operations beforehand."
    | Some ops -> ops
  in
  monad_run_tactic @@ Evaluation.eval_term s ops t

(** Register the reification and evaluation tactics using Ltac2's FFI. *)
let () =
  let open Tac2externals in
  let open Tac2ffi in
  let name s =
    Tac2expr.{ mltac_plugin = "autosubst-experiments.plugin"; mltac_tactic = s }
  in
  define (name "reify_term") (constr @-> tac (pair constr constr)) reify_term_tac;
  define (name "eval_term") (constr @-> tac (pair constr constr)) eval_term_tac
