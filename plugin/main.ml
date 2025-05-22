open Prelude
open Signature

(* Helper function to build a signature. *)
(*let mk_sig (base : EConstr.t list) (ctors : (string * arg_ty list) list) : signature =
  { sort = Names.Id.of_string_soft "term"
  ; n_ctors = List.length ctors
  ; base_types = Array.of_list @@ List.map (EConstr.to_constr Evd.empty) base
  ; ctor_names = Array.of_list @@ List.map Names.Id.of_string_soft @@ List.map fst ctors
  ; ctor_types = Array.of_list @@ List.map snd ctors
  }

(** A testing signature.*)
let build_signature () : signature =
  (*mk_sig
    [ mkglob' Constants.string ]
    [ ("App", [ AT_term; AT_term ]); ("Lam", [ AT_base 0; AT_bind AT_term ]) ]*)
  let level = AT_base 0 in
  let mode = AT_base 1 in
  mk_sig
    [ mkglob' (Constants.resolve "ghost_reflection.level")
    ; mkglob' (Constants.resolve "ghost_reflection.mode")
    ]
    [ ("Sort", [ mode; level ])
    ; ("Pi", [ level; level; mode; mode; AT_term; AT_bind AT_term ])
    ; ("lam", [ mode; AT_term; AT_bind AT_term ])
    ; ("app", [ AT_term; AT_term ])
    ; ("Erased", [ AT_term ])
    ; ("hide", [ AT_term ])
    ; ("reveal", [ AT_term; AT_term; AT_term ])
    ; ("Reveal", [ AT_term; AT_term ])
    ; ("toRev", [ AT_term; AT_term; AT_term ])
    ; ("fromRev", [ AT_term; AT_term; AT_term ])
    ; ("gheq", [ AT_term; AT_term; AT_term ])
    ; ("ghrefl", [ AT_term; AT_term ])
    ; ("ghcast", [ AT_term; AT_term; AT_term; AT_term; AT_term; AT_term ])
    ; ("tbool", [])
    ; ("ttrue", [])
    ; ("tfalse", [])
    ; ("tif", [ mode; AT_term; AT_term; AT_term; AT_term ])
    ; ("tnat", [])
    ; ("tzero", [])
    ; ("tsucc", [ AT_term ])
    ; ("tnat_elim", [ mode; AT_term; AT_term; AT_term; AT_term ])
    ; ("tvec", [ AT_term; AT_term ])
    ; ("tvnil", [ AT_term ])
    ; ("tvcons", [ AT_term; AT_term; AT_term ])
    ; ("tvec_elim", [ mode; AT_term; AT_term; AT_term; AT_term; AT_term; AT_term ])
    ; ("bot", [])
    ; ("bot_elim", [ mode; AT_term; AT_term ])
    ]*)

(**************************************************************************************)
(** *** Generating operations/lemmas. *)
(**************************************************************************************)

(** We keep track of the generated operations using the [Libobject] API. The first step is
    to create a reference using [Summary.ref]. *)
let saved_ops : (signature * ops_all) option ref =
  Summary.ref ~name:"autosubst_saved_ops_summary" None

(** We declare a [Libobject.obj], which gives us a function [update_saved_ops] to update
    the contents of [saved_ops]. Accessing the contents of [saved_ops] can be done by
    simply de-referencing: [!saved_ops].

    It is important that we call [Libobject.declare_object] at the toplevel. *)
let update_saved_ops : (signature * ops_all) option -> Libobject.obj =
  Libobject.declare_object
    { (Libobject.default_object "autosubst_saved_ops_libobject") with
      cache_function = (fun v -> saved_ops := v)
    ; load_function = (fun _ v -> saved_ops := v)
    ; classify_function = (fun _ -> Keep)
    }

(** Given a signature, generate all relevant definitions and lemmas (i.e. add them to the
    global environment), and return the names of the generated operations. *)
let generate_operations (sign : signature) : ops_all =
  let ops0 = Gen_ops_zero.generate sign in
  let ops1 = Gen_ops_one.generate sign ops0 in
  let re = Gen_ops_reify_eval.generate sign ops0 ops1 in
  let congr = Gen_ops_congr.generate sign ops0 in
  let bij = Gen_ops_bijection.generate sign ops0 ops1 re congr in
  let pe = Gen_ops_push_eval.generate sign ops0 ops1 re congr bij in
  { ops_ops0 = ops0
  ; ops_ops1 = ops1
  ; ops_re = re
  ; ops_congr = congr
  ; ops_bij = bij
  ; ops_pe = pe
  }

(** Main entry point for the plugin: generate level zero terms, operations, and lemmas. *)
let generate (sign : signature) =
  (* Generate the operations. *)
  let ops = generate_operations sign in
  (* Save the operations. *)
  Lib.add_leaf @@ update_saved_ops (Some (sign, ops))

(**************************************************************************************)
(** *** Expose Ltac2 reification and evaluation tactics. *)
(**************************************************************************************)

(** [define_ltac2 name body] declares an Ltac2 tactic named [name], with type
    [constr -> constr * constr], which is implemented by [body].

    You must write the following in a .v file before calling the tactic from Ltac2:
    [Ltac2 @external my_tac : constr -> constr * constr := "autosubst-experiments.plugin"
     "name"] *)
let define_ltac2 (name : string)
    (body : signature -> ops_all -> EConstr.t -> (EConstr.t * EConstr.t) m) : unit =
  let open Ltac2_plugin in
  let open Tac2externals in
  let open Tac2ffi in
  (* We must delay fetching the saved operations [!saved_ops] until the tactic is 
     actually called. *)
  let ocaml_tactic x =
    let sign, ops =
      match !saved_ops with
      | None -> Log.error "define_ltac2: must generate operations beforehand."
      | Some x -> x
    in
    monad_run_tactic @@ body sign ops x
  in
  define
    Tac2expr.{ mltac_plugin = "autosubst-experiments.plugin"; mltac_tactic = name }
    (constr @-> tac (pair constr constr))
    ocaml_tactic

let () =
  define_ltac2 "reify_term" Reification.reify_term;
  define_ltac2 "reify_subst" Reification.reify_subst;
  define_ltac2 "eval_term" Evaluation.eval_term;
  define_ltac2 "eval_subst" Evaluation.eval_subst
