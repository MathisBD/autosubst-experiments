include Metaprog

(**************************************************************************************)
(** *** OCaml representation of a signature. *)
(**************************************************************************************)

(** Argument type. Base types store the index of the type in the [base_types] array. *)
type arg_ty = AT_base of int | AT_term | AT_bind of arg_ty

(** An abstract signature:
    - [n_ctors] is the number of _non-variable_ constructors.
    - [ctor_names] contains the name of each constructor.
    - [ctor_sig] contains the argument types of each constructor.

    The length of [ctor_names] and [ctor_sig] should be equal to [n_ctors]. *)
type signature =
  { n_ctors : int
  ; base_types : Constr.t array
  ; ctor_names : string array
  ; ctor_types : arg_ty list array
  }

(** [arg_ty_constr sign ty ind] builds the [EConstr.t] corresponding to [ty]. We use [ind]
    as a placeholder for the inductive type of terms. *)
let rec arg_ty_constr (sign : signature) (ty : arg_ty) (ind : EConstr.t) : EConstr.t =
  match ty with
  | AT_base i -> EConstr.of_constr sign.base_types.(i)
  | AT_term -> ind
  | AT_bind ty -> arg_ty_constr sign ty ind

(** [ctor_ty_constr sign tys ind] build the type of a constructor as a [EConstr.t]. We use
    [ind] as a placeholder for the inductive type of terms. *)
let ctor_ty_constr (sign : signature) (tys : arg_ty list) (ind : EConstr.t) : EConstr.t =
  arrows (List.map (fun ty -> arg_ty_constr sign ty ind) tys) ind

(**************************************************************************************)
(** *** References to generated constants. *)
(**************************************************************************************)

(** Level zero terms, renaming functions, and substitution functions. *)
type ops_zero =
  { term : Names.Ind.t
  ; subst : Names.Constant.t
  ; sid : Names.Constant.t
  ; sshift : Names.Constant.t
  ; scons : Names.Constant.t
  ; rename : Names.Constant.t
  ; substitute : Names.Constant.t
  ; srcomp : Names.Constant.t
  ; rscomp : Names.Constant.t
  ; scomp : Names.Constant.t
  ; up_subst : Names.Constant.t
  }

(** Level one signature, and level one constants specialized to this signature. *)
type ops_one =
  { (* Signature. *)
    base : Names.Ind.t
  ; eval_base : Names.Constant.t
  ; ctor : Names.Ind.t
  ; ctor_type : Names.Constant.t
  ; sign : Names.Constant.t
  ; (* Expressions. *)
    expr : Names.Ind.t
  ; e_var : Names.Construct.t
  ; e_ctor : Names.Construct.t
  ; e_al_nil : Names.Construct.t
  ; e_al_cons : Names.Construct.t
  ; e_abase : Names.Construct.t
  ; e_aterm : Names.Construct.t
  ; e_abind : Names.Construct.t
  ; (* Substitutions. *)
    subst : Names.Constant.t
  }

(** Congruence lemmas. [congr_ctor] contains congruence lemmas for all non-variable
    constructors. *)
type ops_congr =
  { congr_ctors : Names.Constant.t array
  ; congr_rename : Names.Constant.t
  ; congr_substitute : Names.Constant.t
  ; congr_rscomp : Names.Constant.t
  ; congr_srcomp : Names.Constant.t
  ; congr_scomp : Names.Constant.t
  ; congr_scons : Names.Constant.t
  ; congr_up_subst : Names.Constant.t
  }

(** Reification functions (level zero -> level one) and evaluation functions (level one ->
    level zero). *)
type ops_reify_eval =
  { reify : Names.Constant.t
  ; sreify : Names.Constant.t
  ; eval_arg : Names.Constant.t
  ; eval_args : Names.Constant.t
  ; eval_kind : Names.Constant.t
  ; eval_ctor : Names.Constant.t
  ; eval : Names.Constant.t
  ; seval : Names.Constant.t
  }

(**************************************************************************************)
(** *** Utility functions. *)
(**************************************************************************************)

(** Helper function to declare a definition. *)
let def (name : string) ?(kind : Decls.definition_object_kind option)
    (mk_body : EConstr.t m) : Names.Constant.t =
  let kind = match kind with None -> Decls.Definition | Some k -> k in
  monad_run
    begin
      let* body = mk_body in
      (* Typecheck to resolve evars. *)
      let* _ = typecheck body in
      declare_def kind name body
    end

(** Helper function to prove a lemma using a tactic. *)
let lemma (name : string) (mk_stmt : EConstr.t m) (tac : unit Proofview.tactic) :
    Names.Constant.t =
  monad_run
    begin
      let* stmt = mk_stmt in
      (* Typecheck to resolve evars. *)
      let* _ = typecheck stmt in
      declare_theorem Decls.Lemma name stmt tac
    end
