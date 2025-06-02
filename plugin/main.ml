open Prelude
open Signature
module C = Constants

(**************************************************************************************)
(** *** Saving the names of generated constants and lemmas. *)
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

(**************************************************************************************)
(** *** Generating operations/lemmas. *)
(**************************************************************************************)

(** Build the inductive representing level zero terms. *)
let build_term (sign : signature) : Names.Ind.t m =
  (* Constructor names and types. We add an extra constructor for variables. *)
  let ctor_names = sign.var_ctor_name :: Array.to_list sign.ctor_names in
  let ctor_types =
    (fun ind -> ret @@ arrow (mkglob' C.nat) (EConstr.mkVar ind))
    :: Array.to_list
         (Array.map
            (fun ty ind -> ret @@ ctor_ty_constr sign ty (EConstr.mkVar ind))
            sign.ctor_types)
  in
  (* Declare the inductive. *)
  declare_ind sign.sort_name EConstr.mkSet ctor_names ctor_types

(** Given a signature, generate the term inductive and internalize all base types. *)
let generate_term (gen_sign : Constrexpr.constr_expr gen_signature) :
    signature * Names.Ind.t =
  monad_run
  @@
  let* sign = interp_signature_base_types gen_sign in
  let* term = build_term sign in
  ret (sign, term)

(** Given a signature, generate all relevant definitions and lemmas (i.e. add them to the
    global environment), and return the names of the generated operations. *)
let generate_operations (sign : signature) (term : Names.Ind.t) : ops_all =
  let ops0 = Gen_ops_zero.generate sign term in
  let ops1 = Gen_ops_one.generate sign ops0 in
  let re = Gen_ops_reify_eval.generate sign ops0 ops1 in
  let congr = Gen_ops_congr.generate sign ops0 ops1 re in
  let bij = Gen_ops_bijection.generate sign ops0 ops1 re congr in
  let pe = Gen_ops_push_eval.generate sign ops0 ops1 re congr bij in
  { ops_ops0 = ops0
  ; ops_ops1 = ops1
  ; ops_re = re
  ; ops_congr = congr
  ; ops_bij = bij
  ; ops_pe = pe
  }

(** Register hints in database [asimpl_unfold] used by tactic [aunfold]. See [RASimpl.v]
    for more details. *)
let register_aunfold_hints (sign : signature) (ops : ops_all) : unit =
  let force_const (gref : Names.GlobRef.t Lazy.t) : Names.Constant.t =
    match Lazy.force gref with
    | Names.GlobRef.ConstRef cname -> cname
    | _ -> Log.error "register_aunfold_hints: expected a reference to a constant"
  in
  let consts = [ force_const C.up_ren; ops.ops_ops0.up_subst ] in
  Hints.add_hints ~locality:Hints.Export [ "asimpl_unfold" ]
    (HintsUnfoldEntry (List.map (fun c -> Evaluable.EvalConstRef c) consts))

(** Main entry point for the plugin: generate the term inductive as well as level zero
    terms, operations, and lemmas. *)
let generate (gen_sign : Constrexpr.constr_expr gen_signature) : unit =
  (* Generate the term inductive. *)
  let sign, term = generate_term gen_sign in
  (* Generate the operations. *)
  let ops = generate_operations sign term in
  (* Register [aunfold] hints. *)
  register_aunfold_hints sign ops;
  (* Save the operations. *)
  Lib.add_leaf @@ update_saved_ops (Some (sign, ops))

(**************************************************************************************)
(** *** Expose Ltac2 simplification tactics. *)
(**************************************************************************************)

(** [define_ltac2 name body] declares an Ltac2 tactic named [name], with type
    [constr -> constr * constr], which is implemented by [body].

    You must write the following in a .v file before calling the tactic from Ltac2:
    [Ltac2 @external my_tac : constr -> constr * constr := "autosubst-experiments.plugin"
     "name"] *)
let define_ltac2 (name : string)
    (body : signature -> ops_all -> EConstr.t -> (EConstr.t * EConstr.t) Proofview.tactic)
    : unit =
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
    body sign ops x
  in
  define
    Tac2expr.{ mltac_plugin = "autosubst-experiments.plugin"; mltac_tactic = name }
    (constr @-> tac (pair constr constr))
    ocaml_tactic

let () =
  define_ltac2 "simpl_term_zero" Simplification.simpl_term_zero;
  define_ltac2 "simpl_subst_zero" Simplification.simpl_subst_zero
