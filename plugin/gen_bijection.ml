(** This file generates the proof that [eval] and [reify] form a bijection between level
    zero terms and level one terms. To prove this we also need to generate a custom
    induction principle on level one terms. *)

open Prelude

(**************************************************************************************)
(** *** Build the lemmas. *)
(**************************************************************************************)

(** Build [forall t, eval (reify t) = t]. *)
let build_eval_reify (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  prod "t" (mkind ops0.term) @@ fun t ->
  let t' =
    apps (mkconst re.eval)
      [| app (Lazy.force Consts.k_t) @@ mkind ops1.base
       ; app (mkconst re.reify) @@ EConstr.mkVar t
      |]
  in
  ret @@ apps (Lazy.force Consts.eq) [| mkind ops0.term; t'; EConstr.mkVar t |]

(** Build [forall t, seval (sreify s) =₁ s]. *)
let build_seval_sreify (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  prod "s" (mkconst ops0.subst) @@ fun s ->
  let s' = app (mkconst re.seval) @@ app (mkconst re.sreify) @@ EConstr.mkVar s in
  ret
  @@ apps (Lazy.force Consts.point_eq)
       [| Lazy.force Consts.nat; mkind ops0.term; s'; EConstr.mkVar s |]

(** Build the induction hypothesis for the non-variable constructor number [idx] (starting
    at [0]). *)
let build_ind_hyp (s : signature) (ops1 : ops_one) (pred : Names.Id.t) (idx : int)
    (tys : arg_ty list) : EConstr.t m =
  let open EConstr in
  let term1 = app (mkind ops1.expr) @@ app (Lazy.force Consts.k_t) @@ mkind ops1.base in
  (* Re-build an argument. *)
  let rec build_arg (ty : arg_ty) (arg : Names.Id.t) : EConstr.t m =
    match ty with
    | AT_base b ->
        ret @@ apps (mkctor ops1.e_abase) [| mkctor (ops1.base, b + 1); mkVar arg |]
    | AT_term -> ret @@ apps (mkctor ops1.e_aterm) [| mkVar arg |]
    | AT_bind ty ->
        let* ev = fresh_evar None in
        let* arg' = build_arg ty arg in
        ret @@ apps (mkctor ops1.e_abind) [| ev; arg' |]
  in
  (* Re-build the list of arguments. *)
  let rec build_args (args : (arg_ty * Names.Id.t) list) : EConstr.t m =
    match args with
    | [] -> ret @@ mkctor ops1.e_al_nil
    | (ty, arg) :: args ->
        let* ev1 = fresh_evar None in
        let* ev2 = fresh_evar None in
        let* rarg = build_arg ty arg in
        let* rargs = build_args args in
        ret @@ apps (mkctor ops1.e_al_cons) [| ev1; ev2; rarg; rargs |]
  in
  (* Build the recursive hypothesis on argument [arg] with arg type [ty].
     Base types ([AT_base]) don't give rise to a hypothesis. *)
  let rec rec_hyp (arg : Names.Id.t) (ty : arg_ty) (k : EConstr.t m) : EConstr.t m =
    match ty with
    | AT_base _ -> k
    | AT_term ->
        let* k' = k in
        ret @@ arrow (app (mkVar pred) (mkVar arg)) k'
    | AT_bind ty -> rec_hyp arg ty k
  in
  (* Bind the arguments of the constructor, and the recursive hypothesis on
     each argument (if needed). *)
  let rec loop (tys : arg_ty list) (k : Names.Id.t list -> EConstr.t m) : EConstr.t m =
    match tys with
    | [] -> k []
    | ty :: tys ->
        prod "x" (arg_ty_constr s ty term1) @@ fun x ->
        rec_hyp x ty @@ loop tys @@ fun xs -> k (x :: xs)
  in
  loop tys @@ fun args ->
  (* Build the conclusion. *)
  let* args' = build_args @@ List.combine tys args in
  ret
  @@ app (mkVar pred)
  @@ apps (mkctor ops1.e_ctor) [| mkctor (ops1.ctor, idx + 1); args' |]

(** Build the custom induction principle on level one terms. *)
let build_ind (s : signature) (ops1 : ops_one) : EConstr.t m =
  let open EConstr in
  let term1 = app (mkind ops1.expr) @@ app (Lazy.force Consts.k_t) @@ mkind ops1.base in
  prod "P" (arrow term1 mkProp) @@ fun pred ->
  let* var_hyp =
    prod "i" (Lazy.force Consts.nat) @@ fun i ->
    ret @@ app (mkVar pred) @@ app (mkctor ops1.e_var) @@ mkVar i
  in
  let* ctor_hyps =
    List.monad_mapi (build_ind_hyp s ops1 pred) @@ Array.to_list s.ctor_types
  in
  let* concl = prod "t" term1 @@ fun t -> ret @@ app (mkVar pred) (mkVar t) in
  ret @@ arrows (var_hyp :: ctor_hyps) concl

(**************************************************************************************)
(** *** Prove the lemmas. *)
(**************************************************************************************)

(** Prove [forall t, eval (reify t) = t]. *)
let prove_eval_reify (congr : ops_congr) : unit Proofview.tactic =
  let open PVMonad in
  let* t = intro_fresh "t" in
  let* _ = Induction.induction false None (EConstr.mkVar t) None None in
  let* _ = Tactics.simpl_in_concl in
  dispatch @@ function
  (* Solve the variable constructor with [reflexivity]. *)
  | 0 -> Tactics.reflexivity
  (* Solve the non-variable constructors by applying the appropriate congruence lemma
     and finishing with [auto]. *)
  | i -> Tactics.apply (mkconst congr.congr_ctors.(i - 1)) >> auto ()

(** Prove [forall s, seval (sreify s) =₁ s]. *)
let prove_seval_sreify (re : ops_reify_eval) (eval_reify : Names.Constant.t) :
    unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_fresh "s" in
  let* _ = intro_fresh "i" in
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef re.seval) in
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef re.sreify) in
  Tactics.apply (mkconst eval_reify)

(** Prove the custom induction principle on level one terms. *)
let prove_ind (s : signature) (ops1 : ops_one) : unit Proofview.tactic =
  let open PVMonad in
  let* pred = intro_fresh "P" in
  let* var_hyp = intro_fresh "H" in
  let* ctor_hyps = repeat_n s.n_ctors (intro_fresh "H") in
  print_open_goals

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Generate the bijection proof and the custom induction principle. *)
let generate (s : signature) (ops0 : ops_zero) (ops1 : ops_one) (congr : ops_congr)
    (re : ops_reify_eval) : unit =
  let eval_reify =
    lemma "eval_reify_inv" (build_eval_reify ops0 ops1 re) @@ prove_eval_reify congr
  in
  let _seval_sreify =
    lemma "seval_sreify_inv" (build_seval_sreify ops0 ops1 re)
    @@ prove_seval_sreify re eval_reify
  in
  let _ind = lemma "term_ind'" (build_ind s ops1) @@ prove_ind s ops1 in
  ()
