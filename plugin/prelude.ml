include Metaprog

(**************************************************************************************)
(** *** References to generated constants. *)
(**************************************************************************************)

(** We gather the names of generated constants & lemmas in records. Once everything has
    been generated, we store the names using the [Libobject] API (see [main.ml]). *)

(** Concrete terms, renaming functions, and substitution functions. *)
type ops_concrete =
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

(** Rocq signature. *)
type ops_sign =
  { base : Names.Ind.t
  ; base_eqdec : Names.Constant.t
  ; eval_base : Names.Constant.t
  ; fctor : Names.Ind.t
  ; fctor_eqdec : Names.Constant.t
  ; fctor_shape : Names.Constant.t
  ; fctor_size : Names.Constant.t
  ; ctor : Names.Ind.t
  ; ctor_eqdec : Names.Constant.t
  ; ctor_type : Names.Constant.t
  ; sign : Names.Constant.t
  }

(** Helper function to build the kind of terms [Kt]. *)
let kt (ops : ops_sign) : EConstr.t = app (mkglob' Constants.k_t) @@ mkind ops.base

(** Helper function to build the type of parameterized terms [P.expr Kt]. *)
let term1 (ops : ops_sign) : EConstr.t =
  apps (mkglob' Constants.P.expr) [| mkconst ops.sign; kt ops |]

(** Helper function to build the type of parameterized substitutions [P.subst]. *)
let subst1 (ops : ops_sign) : EConstr.t =
  app (mkglob' Constants.P.subst) (mkconst ops.sign)

(** Reification functions (concrete syntax -> parameterized syntax) and evaluation
    functions (parameterized syntax -> concrete syntax). *)
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
  ; congr_eval : Names.Constant.t
  ; congr_seval : Names.Constant.t
  }

(** Proof of bijection between concrete and parameterized syntax, and custom induction
    principle on parameterized terms. *)
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
  { ops_conc : ops_concrete
  ; ops_si : ops_sign
  ; ops_re : ops_reify_eval
  ; ops_congr : ops_congr
  ; ops_bij : ops_bijection
  ; ops_pe : ops_push_eval
  }

(**************************************************************************************)
(** *** Utility functions. *)
(**************************************************************************************)

(** [decompose_app2 sigma t] checks if [t] is an application [f x], and if so returns
    [Some (f, x)]. Note that [f] can itself be an application. *)
let decompose_app2 (sigma : Evd.evar_map) (t : EConstr.t) : (EConstr.t * EConstr.t) option
    =
  match EConstr.kind sigma t with
  | App (f, args) when Array.length args > 0 ->
      let n = Array.length args in
      Some (apps f (Array.sub args 0 (n - 1)), args.(n - 1))
  | _ -> None

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

(** [fresh_global_id base] computes a fresh identifier [id] from [base] such that [id] can
    be declared as a new global constants in the current module. *)
let fresh_global_id (base : Names.Id.t) : Names.Id.t m =
 fun env sigma ->
  let id =
    Namegen.next_ident_away_from base (fun id' -> Nametab.exists_cci @@ Lib.make_path id')
  in
  (sigma, id)

(** Helper function to declare a definition. If [refresh] is [true], it will pick a fresh
    name to avoid clashing with previously defined constants. *)
let def (name : string) ?(refresh = false) ?(kind = Decls.Definition)
    (mk_body : EConstr.t m) : Names.Constant.t =
  monad_run
    begin
      let* name =
        if refresh
        then fresh_global_id @@ Names.Id.of_string_soft name
        else ret @@ Names.Id.of_string_soft name
      in
      let* body = mk_body in
      declare_def kind name body
    end

(** Helper function to prove a lemma using a tactic. If [refresh] is [true], it will pick
    a fresh name to avoid clashing with previously defined constants. *)
let lemma (name : string) ?(refresh = false) (mk_stmt : EConstr.t m)
    (tac : unit Proofview.tactic) : Names.Constant.t =
  monad_run
    begin
      let* name =
        if refresh
        then fresh_global_id @@ Names.Id.of_string_soft name
        else ret @@ Names.Id.of_string_soft name
      in
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
