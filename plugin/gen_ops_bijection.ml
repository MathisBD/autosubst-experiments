(** This file generates the proof that [eval] and [reify] form a bijection between level
    zero terms and level one terms. To prove this we also need to generate a custom
    induction principle on level one terms. *)

open Prelude

module Make (P : sig
  val sign : signature
  val ops0 : ops_zero
  val ops1 : ops_one
  val re : ops_reify_eval
  val congr : ops_congr
end) =
struct
  (**************************************************************************************)
  (** *** Build the lemmas. *)
  (**************************************************************************************)

  (** Build [forall t, eval (reify t) = t]. *)
  let build_eval_reify () : EConstr.t m =
    prod "t" (mkind P.ops0.term) @@ fun t ->
    let t' =
      apps (mkconst P.re.eval)
        [| app (Lazy.force Consts.k_t) @@ mkind P.ops1.base
         ; app (mkconst P.re.reify) @@ EConstr.mkVar t
        |]
    in
    ret @@ apps (Lazy.force Consts.eq) [| mkind P.ops0.term; t'; EConstr.mkVar t |]

  (** Build [forall t, seval (sreify s) =₁ s]. *)
  let build_seval_sreify () : EConstr.t m =
    prod "s" (mkconst P.ops0.subst) @@ fun s ->
    let s' = app (mkconst P.re.seval) @@ app (mkconst P.re.sreify) @@ EConstr.mkVar s in
    ret
    @@ apps (Lazy.force Consts.point_eq)
         [| Lazy.force Consts.nat; mkind P.ops0.term; s'; EConstr.mkVar s |]

  (** Build the induction hypothesis for the non-variable constructor number [idx]
      (starting at [0]). *)
  let build_ind_hyp (pred : Names.Id.t) (idx : int) (tys : arg_ty list) : EConstr.t m =
    let open EConstr in
    (* Re-build an argument. *)
    let rec build_arg (ty : arg_ty) (arg : Names.Id.t) : EConstr.t m =
      match ty with
      | AT_base b ->
          ret @@ apps (mkctor P.ops1.e_abase) [| mkctor (P.ops1.base, b + 1); mkVar arg |]
      | AT_term -> ret @@ apps (mkctor P.ops1.e_aterm) [| mkVar arg |]
      | AT_bind ty ->
          let* arg' = build_arg ty arg in
          apps_ev (mkctor P.ops1.e_abind) 1 [| arg' |]
    in
    (* Re-build the list of arguments. *)
    let rec build_args (args : (arg_ty * Names.Id.t) list) : EConstr.t m =
      match args with
      | [] -> ret @@ mkctor P.ops1.e_al_nil
      | (ty, arg) :: args ->
          let* rarg = build_arg ty arg in
          let* rargs = build_args args in
          apps_ev (mkctor P.ops1.e_al_cons) 2 [| rarg; rargs |]
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
          prod "x" (arg_ty_constr P.sign ty @@ term1 P.ops1) @@ fun x ->
          rec_hyp x ty @@ loop tys @@ fun xs -> k (x :: xs)
    in
    loop tys @@ fun args ->
    (* Build the conclusion. *)
    let* args' = build_args @@ List.combine tys args in
    ret
    @@ app (mkVar pred)
    @@ apps (mkctor P.ops1.e_ctor) [| mkctor (P.ops1.ctor, idx + 1); args' |]

  (** Build the custom induction principle on level one terms. *)
  let build_ind () : EConstr.t m =
    let open EConstr in
    prod "P" (arrow (term1 P.ops1) mkProp) @@ fun pred ->
    let* var_hyp =
      prod "i" (Lazy.force Consts.nat) @@ fun i ->
      ret @@ app (mkVar pred) @@ app (mkctor P.ops1.e_var) @@ mkVar i
    in
    let* ctor_hyps =
      List.monad_mapi (build_ind_hyp pred) @@ Array.to_list P.sign.ctor_types
    in
    let* concl = prod "t" (term1 P.ops1) @@ fun t -> ret @@ app (mkVar pred) (mkVar t) in
    ret @@ arrows (var_hyp :: ctor_hyps) concl

  (** Build [forall t, reify (eval t) = t]. *)
  (*let build_reify_eval (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  let term1 = app (mkind P.ops1.expr) @@ app (Lazy.force Consts.k_t) @@ mkind P.ops1.base in
  prod "t" term1 @@ fun t ->
  let t' =
    app (mkconst P.re.reify)
    @@ apps (mkconst P.re.eval)
         [| app (Lazy.force Consts.k_t) @@ mkind P.ops1.base; EConstr.mkVar t |]
  in
  ret @@ apps (Lazy.force Consts.eq) [| term1; t'; EConstr.mkVar t |]

(** Build [forall t, sreify (seval s) =₁ s]. *)
let build_sreify_seval (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  let term1 = app (mkind P.ops1.expr) @@ app (Lazy.force Consts.k_t) @@ mkind P.ops1.base in
  prod "s" (mkconst P.ops1.subst) @@ fun s ->
  let s' = app (mkconst P.re.sreify) @@ app (mkconst P.re.seval) @@ EConstr.mkVar s in
  ret
  @@ apps (Lazy.force Consts.point_eq)
       [| Lazy.force Consts.nat; term1; s'; EConstr.mkVar s |]*)

  (**************************************************************************************)
  (** *** Prove the lemmas. *)
  (**************************************************************************************)

  (** Prove [forall t, eval (reify t) = t]. *)
  let prove_eval_reify () : unit Proofview.tactic =
    let open PVMonad in
    let* t = intro_fresh "t" in
    let* _ = induction @@ EConstr.mkVar t in
    let* _ = Tactics.simpl_in_concl in
    dispatch @@ function
    (* Solve the variable constructor with [reflexivity]. *)
    | 0 -> Tactics.reflexivity
    (* Solve the non-variable constructors by applying the appropriate congruence lemma
     and finishing with [auto]. *)
    | i -> Tactics.apply (mkconst P.congr.congr_ctors.(i - 1)) >> auto ()

  (** Prove [forall s, seval (sreify s) =₁ s]. *)
  let prove_seval_sreify (eval_reify : Names.Constant.t) : unit Proofview.tactic =
    let open PVMonad in
    let* _ = intro_fresh "s" in
    let* _ = intro_fresh "i" in
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.re.seval) in
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.re.sreify) in
    Tactics.apply (mkconst eval_reify)

  (** Call the tactic [lia]. *)
  let lia () : unit Proofview.tactic =
    let open Ltac_plugin in
    let kname = mk_kername [ "Coq"; "micromega"; "Lia" ] "lia" in
    Tacinterp.eval_tactic (Tacenv.interp_ltac kname)

  (** Helper function for [prove_ind] which takes care of the [i]-th non-variable
      constructor (starting at [0]). *)
  let prove_ind_ctor (ctor_hyps : Names.Id.t list) (idx : int) : unit Proofview.tactic =
    let open EConstr in
    let open PVMonad in
    (* Invert an argument. *)
    let rec inv_arg (ty : arg_ty) (arg : Names.Id.t) : unit Proofview.tactic =
      let* _ = pattern (mkVar arg) in
      match ty with
      | AT_base _ ->
          let* _ = Tactics.apply (mkconst P.ops1.inv_Ka_base) in
          let* _ = intro_fresh "b" in
          ret ()
      | AT_term ->
          let* _ = Tactics.apply (mkconst P.ops1.inv_Ka_term) in
          let* _ = intro_fresh "t" in
          ret ()
      | AT_bind ty' ->
          let* _ = Tactics.apply (mkconst P.ops1.inv_Ka_bind) in
          let* arg' = intro_fresh "a" in
          inv_arg ty' arg'
    in
    (* Invert an argument list. *)
    let rec inv_args (tys : arg_ty list) (args : Names.Id.t) : unit Proofview.tactic =
      let* _ = pattern (mkVar args) in
      match tys with
      | [] -> Tactics.apply (mkconst P.ops1.inv_Kal_nil)
      | ty :: tys ->
          let* _ = Tactics.apply (mkconst P.ops1.inv_Kal_cons) in
          let* arg = intro_fresh "a" in
          let* args = intro_fresh "al" in
          inv_arg ty arg >> inv_args tys args
    in
    (* Invert everything (_before_ introducing [IH]). *)
    let* al = intro_fresh "al" in
    let* _ = inv_args P.sign.ctor_types.(idx) al in
    (* Apply the induction hypothesis and finish with [lia]. *)
    let* ind_hyp = intro_fresh "IH" in
    let* _ = Tactics.apply (mkVar @@ List.nth ctor_hyps idx) in
    let* _ = Tactics.apply (mkVar ind_hyp) in
    let* _ = Tactics.simpl_in_concl in
    lia ()

  (** Prove the custom induction principle on level one terms. *)
  let prove_ind () : unit Proofview.tactic =
    let open EConstr in
    let open PVMonad in
    (* Introduce the hypotheses. *)
    let* pred = intro_fresh "P" in
    let* var_hyp = intro_fresh "H" in
    let* ctor_hyps = repeat_n P.sign.n_ctors (intro_fresh "H") in
    (* Apply the well founded induction principle. *)
    let term1 =
      app (mkind P.ops1.expr) @@ app (Lazy.force Consts.k_t) @@ mkind P.ops1.base
    in
    let esize =
      app (mkconst P.ops1.esize) @@ app (Lazy.force Consts.k_t) @@ mkind P.ops1.base
    in
    let* _ =
      Tactics.apply
      @@ apps (Lazy.force Consts.measure_induction) [| term1; esize; mkVar pred |]
    in
    (* Invert [t]. *)
    let* t = intro_fresh "t" in
    let* _ = pattern (mkVar t) >> Tactics.apply (mkconst P.ops1.inv_Kt) in
    Proofview.tclDISPATCH
      [ (* Solve the [E_var] case. *)
        begin
          intro_n 2 >> Tactics.apply (mkVar var_hyp)
        end
      ; (* Start the [E_ctor] case. *)
        begin
          let* c = intro_fresh "c" in
          let* _ = destruct @@ mkVar c in
          dispatch @@ prove_ind_ctor ctor_hyps
        end
      ]
    >> print_open_goals ()
end

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Generate the bijection proof and the custom induction principle. *)
let generate (s : signature) (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval)
    (congr : ops_congr) : ops_bijection =
  let module M = Make (struct
    let sign = s
    let ops0 = ops0
    let ops1 = ops1
    let re = re
    let congr = congr
  end) in
  let eval_reify_inv =
    lemma "eval_reify_inv" (M.build_eval_reify ()) @@ M.prove_eval_reify ()
  in
  let seval_sreify_inv =
    lemma "seval_sreify_inv" (M.build_seval_sreify ())
    @@ M.prove_seval_sreify eval_reify_inv
  in
  let term_ind = lemma "term_ind'" (M.build_ind ()) @@ M.prove_ind () in
  { eval_reify_inv; seval_sreify_inv; term_ind }
