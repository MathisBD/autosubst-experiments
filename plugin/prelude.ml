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

(** We gather the names of generated constants & lemmas in records. Once everything has
    been generated, we store the names using the [Libobject] API (see [main.ml]). *)

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

(** Level one signature. *)
type ops_one =
  { base : Names.Ind.t
  ; base_eqdec : Names.Constant.t
  ; eval_base : Names.Constant.t
  ; ctor : Names.Ind.t
  ; ctor_eqdec : Names.Constant.t
  ; ctor_type : Names.Constant.t
  ; sign : Names.Constant.t
  }

(** Helper function to build the kind of terms [Kt]. *)
let kt (ops1 : ops_one) : EConstr.t = app (mkglob' Constants.k_t) @@ mkind ops1.base

(** Helper function to build the type of level one terms [O.expr Kt]. *)
let term1 (ops1 : ops_one) : EConstr.t =
  apps (mkglob' Constants.O.expr) [| mkconst ops1.sign; kt ops1 |]

(** Helper function to build the type of level one substitutions [O.subst]. *)
let subst1 (ops1 : ops_one) : EConstr.t =
  app (mkglob' Constants.O.subst) (mkconst ops1.sign)

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

(** Proof of bijection between level zero and level one, and custom induction principle on
    level one terms. *)
type ops_bijection =
  { eval_reify_inv : Names.Constant.t
  ; seval_sreify_inv : Names.Constant.t
  ; term_ind : Names.Constant.t
  }

(** Lemmas which push [eval] inside terms. *)
type ops_push_eval =
  { eval_rename : Names.Constant.t
  ; eval_substitute : Names.Constant.t
  ; seval_rscomp : Names.Constant.t
  ; seval_srcomp : Names.Constant.t
  ; seval_scomp : Names.Constant.t
  ; seval_scons : Names.Constant.t
  ; seval_up_subst : Names.Constant.t
  }

(** All generated operations. *)
type ops_all =
  { ops_ops0 : ops_zero
  ; ops_ops1 : ops_one
  ; ops_re : ops_reify_eval
  ; ops_congr : ops_congr
  ; ops_bij : ops_bijection
  ; ops_pe : ops_push_eval
  }

(**************************************************************************************)
(** *** Utility functions. *)
(**************************************************************************************)

(** [is_const env sigma cname t] checks if [t] is a constant with name [cname]. *)
let is_const (env : Environ.env) (sigma : Evd.evar_map) (c : Names.Constant.t)
    (t : EConstr.t) : bool =
  match EConstr.kind sigma t with
  | Const (c', _) when Environ.QConstant.equal env c c' -> true
  | _ -> false

(** [is_ind env sigma iname t] checks if [t] is an inductive with name [iname]. *)
let is_ind (env : Environ.env) (sigma : Evd.evar_map) (i : Names.Ind.t) (t : EConstr.t) :
    bool =
  match EConstr.kind sigma t with
  | Ind (i', _) when Environ.QInd.equal env i i' -> true
  | _ -> false

(** [is_ctor env sigma cname t] checks if [t] is a constructor with name [cname]. *)
let is_ctor (env : Environ.env) (sigma : Evd.evar_map) (c : Names.Construct.t)
    (t : EConstr.t) : bool =
  match EConstr.kind sigma t with
  | Construct (c', _) when Environ.QConstruct.equal env c c' -> true
  | _ -> false

(** [is_glob env sigma gname t] checks if [t] is a global reference with name [gname]. *)
let is_glob (env : Environ.env) (sigma : Evd.evar_map) (g : Names.GlobRef.t)
    (t : EConstr.t) : bool =
  match (g, EConstr.kind sigma t) with
  | ConstRef c, Const (c', _) when Environ.QConstant.equal env c c' -> true
  | IndRef i, Constr.Ind (i', _) when Environ.QInd.equal env i i' -> true
  | ConstructRef c, Construct (c', _) when Environ.QConstruct.equal env c c' -> true
  | VarRef v, Var v' when Names.Id.equal v v' -> true
  | _ -> false

(** Helper function to declare a definition. *)
let def (name : string) ?(kind = Decls.Definition) (mk_body : EConstr.t m) :
    Names.Constant.t =
  monad_run
    begin
      let* body = mk_body in
      declare_def kind name body
    end

(** Helper function to prove a lemma using a tactic. *)
let lemma (name : string) (mk_stmt : EConstr.t m) (tac : unit Proofview.tactic) :
    Names.Constant.t =
  monad_run
    begin
      let* stmt = mk_stmt in
      declare_theorem Decls.Lemma name stmt tac
    end

(**************************************************************************************)
(** *** Pattern matching utilities. *)
(**************************************************************************************)

(** The reification and evaluation machinery needs to pattern match on terms. We develop
    small pattern matching utilities to deal with this. *)

(** A pattern ['vars patt] is a function which takes a term (an [EConstr.t]) and either:
    - succeeds and extracts a set of variables of type ['vars].
    - fails and returns [None]. *)
type 'vars patt = EConstr.t -> 'vars option m

(** A branch [('vars, 'res) branch] is a function which takes a set of extracted variables
    of type ['vars] and returns a result of type ['res]. *)
type ('vars, 'res) branch = 'vars -> 'res m

(** A case ['res case] is a pair of a pattern and a branch. *)
type _ case = Case : 'vars patt * ('vars, 'res) branch -> 'res case

(** [pattern_match t cases default] performs case analysis on [t]:
    - [cases] is a list of cases which are tried in order until a pattern succeeds.
    - [default] is a branch which has no pattern (it is passed [t]) and is tried only if
      all [cases] fail. *)
let pattern_match (t : EConstr.t) (cases : 'res case list)
    (default_branch : (EConstr.t, 'res) branch) : 'res m =
  let rec loop cases =
    match cases with
    | [] -> default_branch t
    | Case (p, b) :: cases -> begin
        let* vars_opt = p t in
        match vars_opt with Some vars -> b vars | None -> loop cases
      end
  in
  loop cases
