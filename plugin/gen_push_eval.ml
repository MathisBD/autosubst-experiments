(** This file generates lemmas which push [eval] inside level one terms. *)

open Prelude

(**************************************************************************************)
(** *** Build the lemmas. *)
(**************************************************************************************)

(** Build [forall r t, eval (O.rename r t) = rename r (eval t)]. *)
let build_eval_rename (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  let open EConstr in
  prod "r" (Lazy.force Consts.ren) @@ fun r ->
  prod "t" (term1 ops1) @@ fun t ->
  let lhs =
    apps (mkconst re.eval)
      [| kt ops1; apps (mkconst ops1.rename) [| kt ops1; mkVar r; mkVar t |] |]
  in
  let rhs =
    apps (mkconst ops0.rename)
      [| mkVar r; apps (mkconst re.eval) [| kt ops1; mkVar t |] |]
  in
  ret @@ apps (Lazy.force Consts.eq) [| mkind ops0.term; lhs; rhs |]

(** Build [forall r s, seval (O.rscomp r s) =₁ rscomp r (seval s)].*)
let build_seval_rscomp (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  let open EConstr in
  prod "r" (Lazy.force Consts.ren) @@ fun r ->
  prod "s" (mkconst ops1.subst) @@ fun s ->
  let lhs = app (mkconst re.seval) @@ apps (mkconst ops1.rscomp) [| mkVar r; mkVar s |] in
  let rhs = apps (mkconst ops0.rscomp) [| mkVar r; app (mkconst re.seval) @@ mkVar s |] in
  ret
  @@ apps (Lazy.force Consts.point_eq)
       [| Lazy.force Consts.nat; mkind ops0.term; lhs; rhs |]

(** Build [forall s r, seval (O.srcomp s r) =₁ srcomp (seval s) r].*)
let build_seval_srcomp (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  let open EConstr in
  prod "s" (mkconst ops1.subst) @@ fun s ->
  prod "r" (Lazy.force Consts.ren) @@ fun r ->
  let lhs = app (mkconst re.seval) @@ apps (mkconst ops1.srcomp) [| mkVar s; mkVar r |] in
  let rhs = apps (mkconst ops0.srcomp) [| app (mkconst re.seval) @@ mkVar s; mkVar r |] in
  ret
  @@ apps (Lazy.force Consts.point_eq)
       [| Lazy.force Consts.nat; mkind ops0.term; lhs; rhs |]

(** Build [forall t s, seval (O.scons t s) =₁ scons (eval t) (seval s)].*)
let build_seval_scons (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  let open EConstr in
  prod "t" (term1 ops1) @@ fun t ->
  prod "s" (mkconst ops1.subst) @@ fun s ->
  let lhs = app (mkconst re.seval) @@ apps (mkconst ops1.scons) [| mkVar t; mkVar s |] in
  let rhs =
    apps (mkconst ops0.scons)
      [| apps (mkconst re.eval) [| kt ops1; mkVar t |]
       ; app (mkconst re.seval) @@ mkVar s
      |]
  in
  ret
  @@ apps (Lazy.force Consts.point_eq)
       [| Lazy.force Consts.nat; mkind ops0.term; lhs; rhs |]

(** Build [forall s, seval (O.up_subst s) =₁ up_subst (seval s)].*)
let build_seval_up_subst (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  let open EConstr in
  prod "s" (mkconst ops1.subst) @@ fun s ->
  let lhs = app (mkconst re.seval) @@ app (mkconst ops1.up_subst) @@ mkVar s in
  let rhs = app (mkconst ops0.up_subst) @@ app (mkconst re.seval) @@ mkVar s in
  ret
  @@ apps (Lazy.force Consts.point_eq)
       [| Lazy.force Consts.nat; mkind ops0.term; lhs; rhs |]

(** Build [forall s t, eval (O.substitute s t) = substitute (seval s) (eval t)].*)
let build_eval_substitute (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  let open EConstr in
  prod "s" (mkconst ops1.subst) @@ fun s ->
  prod "t" (term1 ops1) @@ fun t ->
  let lhs =
    apps (mkconst re.eval)
      [| kt ops1; apps (mkconst ops1.substitute) [| mkVar s; mkVar t |] |]
  in
  let rhs =
    apps (mkconst ops0.substitute)
      [| app (mkconst re.seval) @@ mkVar s
       ; apps (mkconst re.eval) [| kt ops1; mkVar t |]
      |]
  in
  ret @@ apps (Lazy.force Consts.eq) [| mkind ops0.term; lhs; rhs |]

(** Build [forall s1 s2, seval (O.scomp s1 s2) =₁ scomp (seval s1) (seval s2)].*)
let build_seval_scomp (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    EConstr.t m =
  let open EConstr in
  prod "s1" (mkconst ops1.subst) @@ fun s1 ->
  prod "s2" (mkconst ops1.subst) @@ fun s2 ->
  let lhs =
    app (mkconst re.seval) @@ apps (mkconst ops1.scomp) [| mkVar s1; mkVar s2 |]
  in
  let rhs =
    apps (mkconst ops0.scomp)
      [| app (mkconst re.seval) @@ mkVar s1; app (mkconst re.seval) @@ mkVar s2 |]
  in
  ret
  @@ apps (Lazy.force Consts.point_eq) [| Lazy.force Consts.nat; term1 ops1; lhs; rhs |]

(**************************************************************************************)
(** *** Prove the lemmas. *)
(**************************************************************************************)

let intro_term_ind (s : signature) (idx : int) :
    (Names.Id.t list * Names.Id.t list) Proofview.tactic =
  let open PVMonad in
  let rec loop (tys : arg_ty list) =
    match tys with
    | [] -> ret ([], [])
    | AT_base _ :: tys ->
        let* a = intro_fresh "x" in
        let* args, hyps = loop tys in
        ret (a :: args, hyps)
    | AT_term :: tys ->
        let* a = intro_fresh "x" in
        let* h = intro_fresh "IH" in
        let* args, hyps = loop tys in
        ret (a :: args, h :: hyps)
    | AT_bind ty :: tys -> loop (ty :: tys)
  in
  loop s.ctor_types.(idx)

(** Prove [forall r t, eval (O.rename r t) = rename r (eval t)]. *)
let prove_eval_rename (s : signature) (congr : ops_congr) (bij : ops_bijection) :
    unit Proofview.tactic =
  let open PVMonad in
  let* r = intro_fresh "r" in
  let* t = intro_fresh "t" in
  let* _ = Generalize.revert [ r ] in
  (* Induction on [t]. *)
  let* _ = pattern (EConstr.mkVar t) in
  let* _ = Tactics.apply (mkconst bij.term_ind) in
  dispatch @@ function
  (* Variable constructor. *)
  | 0 -> intro_n 2 >> Tactics.reflexivity
  (* Non-variable constructors. *)
  | i ->
      (* Introduce constructor arguments and induction hypotheses. *)
      let* _ = intro_fresh "r" in
      let* _, _ = intro_term_ind s (i - 1) in
      (* Simplify. *)
      let* _ =
        Tacticals.tclREPEAT
          (Principles_proofs.simp_eqns [ "rename" ] >> Tactics.simpl_in_concl)
      in
      (* Apply the congruence principle and finish with [auto]. *)
      let* _ = Tactics.apply (mkconst congr.congr_ctors.(i - 1)) in
      auto ()

(** Prove [forall r s, seval (O.rscomp r s) =₁ rscomp r (seval s)].*)
let prove_seval_rscomp () : unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_n 3 in
  Tactics.reflexivity

(** Prove [forall s r, seval (O.srcomp s r) =₁ srcomp (seval s) r].*)
let prove_seval_srcomp (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval)
    (eval_rename : Names.Constant.t) : unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_fresh "s" in
  let* _ = intro_fresh "r" in
  let* _ = intro_fresh "i" in
  (* Unfold. *)
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef re.seval) in
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops0.srcomp) in
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops1.srcomp) in
  (* Apply [eval_rename]. *)
  Tactics.apply (mkconst eval_rename)

(** Prove [forall t s, seval (O.scons t s) =₁ scons (eval t) (seval s)].*)
let prove_seval_scons (ops0 : ops_zero) (ops1 : ops_one) (re : ops_reify_eval) :
    unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_fresh "t" in
  let* _ = intro_fresh "s" in
  let* i = intro_fresh "i" in
  (* Simply destruct [i]. *)
  let* _ = destruct @@ EConstr.mkVar i in
  Tactics.reflexivity

(** Prove [forall s, seval (O.up_subst s) =₁ up_subst (seval s)].*)
let prove_seval_up_subst (ops0 : ops_zero) (ops1 : ops_one) (congr : ops_congr)
    (re : ops_reify_eval) (seval_srcomp : Names.Constant.t)
    (seval_scons : Names.Constant.t) : unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_fresh "s" in
  (* Unfold. *)
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops0.up_subst) in
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops1.up_subst) in
  (* Rewrite with [seval_scons]. *)
  let* _ = rewrite LeftToRight (Names.GlobRef.ConstRef seval_scons) in
  let* _ = Tactics.simpl_in_concl in
  (* Apply [congr_scons]. *)
  let* _ = Tactics.apply (mkconst congr.congr_scons) in
  (* Finish with [seval_srcomp]. *)
  auto ~lemmas:[ mkconst seval_srcomp ] ()

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

let generate (s : signature) (ops0 : ops_zero) (ops1 : ops_one) (congr : ops_congr)
    (re : ops_reify_eval) (bij : ops_bijection) : unit =
  let eval_rename =
    lemma "eval_rename" (build_eval_rename ops0 ops1 re) @@ prove_eval_rename s congr bij
  in
  let _seval_rscomp =
    lemma "seval_rscomp" (build_seval_rscomp ops0 ops1 re) @@ prove_seval_rscomp ()
  in
  let seval_srcomp =
    lemma "seval_srcomp" (build_seval_srcomp ops0 ops1 re)
    @@ prove_seval_srcomp ops0 ops1 re eval_rename
  in
  let seval_scons =
    lemma "seval_scons" (build_seval_scons ops0 ops1 re) @@ prove_seval_scons ops0 ops1 re
  in
  let _seval_up_subst =
    lemma "seval_up_subst" (build_seval_up_subst ops0 ops1 re)
    @@ prove_seval_up_subst ops0 ops1 congr re seval_srcomp seval_scons
  in
  ()
