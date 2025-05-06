(** This file generates lemmas which push [eval] inside level one terms. *)

open Prelude

module Make (P : sig
  val sign : signature
  val ops0 : ops_zero
  val ops1 : ops_one
  val re : ops_reify_eval
  val congr : ops_congr
  val bij : ops_bijection
end) =
struct
  (**************************************************************************************)
  (** *** Build the lemmas. *)
  (**************************************************************************************)

  (** Build [forall r t, eval (O.rename r t) = rename r (eval t)]. *)
  let build_eval_rename () : EConstr.t m =
    let open EConstr in
    prod "r" (Lazy.force Consts.ren) @@ fun r ->
    prod "t" (term1 P.ops1) @@ fun t ->
    let lhs =
      apps (mkconst P.re.eval)
        [| kt P.ops1; apps (mkconst P.ops1.rename) [| kt P.ops1; mkVar r; mkVar t |] |]
    in
    let rhs =
      apps (mkconst P.ops0.rename)
        [| mkVar r; apps (mkconst P.re.eval) [| kt P.ops1; mkVar t |] |]
    in
    ret @@ apps (Lazy.force Consts.eq) [| mkind P.ops0.term; lhs; rhs |]

  (** Build [forall r s, seval (O.rscomp r s) =₁ rscomp r (seval s)].*)
  let build_seval_rscomp () : EConstr.t m =
    let open EConstr in
    prod "r" (Lazy.force Consts.ren) @@ fun r ->
    prod "s" (mkconst P.ops1.subst) @@ fun s ->
    let lhs =
      app (mkconst P.re.seval) @@ apps (mkconst P.ops1.rscomp) [| mkVar r; mkVar s |]
    in
    let rhs =
      apps (mkconst P.ops0.rscomp) [| mkVar r; app (mkconst P.re.seval) @@ mkVar s |]
    in
    ret
    @@ apps (Lazy.force Consts.point_eq)
         [| Lazy.force Consts.nat; mkind P.ops0.term; lhs; rhs |]

  (** Build [forall s r, seval (O.srcomp s r) =₁ srcomp (seval s) r].*)
  let build_seval_srcomp () : EConstr.t m =
    let open EConstr in
    prod "s" (mkconst P.ops1.subst) @@ fun s ->
    prod "r" (Lazy.force Consts.ren) @@ fun r ->
    let lhs =
      app (mkconst P.re.seval) @@ apps (mkconst P.ops1.srcomp) [| mkVar s; mkVar r |]
    in
    let rhs =
      apps (mkconst P.ops0.srcomp) [| app (mkconst P.re.seval) @@ mkVar s; mkVar r |]
    in
    ret
    @@ apps (Lazy.force Consts.point_eq)
         [| Lazy.force Consts.nat; mkind P.ops0.term; lhs; rhs |]

  (** Build [forall t s, seval (O.scons t s) =₁ scons (eval t) (seval s)].*)
  let build_seval_scons () : EConstr.t m =
    let open EConstr in
    prod "t" (term1 P.ops1) @@ fun t ->
    prod "s" (mkconst P.ops1.subst) @@ fun s ->
    let lhs =
      app (mkconst P.re.seval) @@ apps (mkconst P.ops1.scons) [| mkVar t; mkVar s |]
    in
    let rhs =
      apps (mkconst P.ops0.scons)
        [| apps (mkconst P.re.eval) [| kt P.ops1; mkVar t |]
         ; app (mkconst P.re.seval) @@ mkVar s
        |]
    in
    ret
    @@ apps (Lazy.force Consts.point_eq)
         [| Lazy.force Consts.nat; mkind P.ops0.term; lhs; rhs |]

  (** Build [forall s, seval (O.up_subst s) =₁ up_subst (seval s)].*)
  let build_seval_up_subst () : EConstr.t m =
    let open EConstr in
    prod "s" (mkconst P.ops1.subst) @@ fun s ->
    let lhs = app (mkconst P.re.seval) @@ app (mkconst P.ops1.up_subst) @@ mkVar s in
    let rhs = app (mkconst P.ops0.up_subst) @@ app (mkconst P.re.seval) @@ mkVar s in
    ret
    @@ apps (Lazy.force Consts.point_eq)
         [| Lazy.force Consts.nat; mkind P.ops0.term; lhs; rhs |]

  (** Build [forall s t, eval (O.substitute s t) = substitute (seval s) (eval t)].*)
  let build_eval_substitute () : EConstr.t m =
    let open EConstr in
    prod "s" (mkconst P.ops1.subst) @@ fun s ->
    prod "t" (term1 P.ops1) @@ fun t ->
    let lhs =
      apps (mkconst P.re.eval)
        [| kt P.ops1
         ; apps (mkconst P.ops1.substitute) [| kt P.ops1; mkVar s; mkVar t |]
        |]
    in
    let rhs =
      apps (mkconst P.ops0.substitute)
        [| app (mkconst P.re.seval) @@ mkVar s
         ; apps (mkconst P.re.eval) [| kt P.ops1; mkVar t |]
        |]
    in
    ret @@ apps (Lazy.force Consts.eq) [| mkind P.ops0.term; lhs; rhs |]

  (** Build [forall s1 s2, seval (O.scomp s1 s2) =₁ scomp (seval s1) (seval s2)].*)
  let build_seval_scomp () : EConstr.t m =
    let open EConstr in
    prod "s1" (mkconst P.ops1.subst) @@ fun s1 ->
    prod "s2" (mkconst P.ops1.subst) @@ fun s2 ->
    let lhs =
      app (mkconst P.re.seval) @@ apps (mkconst P.ops1.scomp) [| mkVar s1; mkVar s2 |]
    in
    let rhs =
      apps (mkconst P.ops0.scomp)
        [| app (mkconst P.re.seval) @@ mkVar s1; app (mkconst P.re.seval) @@ mkVar s2 |]
    in
    ret
    @@ apps (Lazy.force Consts.point_eq)
         [| Lazy.force Consts.nat; mkind P.ops0.term; lhs; rhs |]

  (**************************************************************************************)
  (** *** Prove the lemmas. *)
  (**************************************************************************************)

  (** Helper function to be used when applying the custom induction principle on level
      terms [bij.term_ind], which introduces the arguments and induction hypotheses for
      non-variable constructor [idx] (starting at [0]). It returns a list of pairs
      [(arg, hyp)], where [arg] is the name of the constructor argument, and [hyp] is the
      corresponding induction hypothesis (possibly [None], e.g. whenever [arg] has type
      [AT_bind _]). *)
  let intro_term_ind (idx : int) : (Names.Id.t * Names.Id.t option) list Proofview.tactic
      =
    let open PVMonad in
    let rec loop (tys : arg_ty list) =
      match tys with
      | [] -> ret []
      | AT_base _ :: tys ->
          let* a = intro_fresh "x" in
          let* res = loop tys in
          ret ((a, None) :: res)
      | AT_term :: tys ->
          let* a = intro_fresh "x" in
          let* h = intro_fresh "IH" in
          let* res = loop tys in
          ret ((a, Some h) :: res)
      | AT_bind ty :: tys -> loop (ty :: tys)
    in
    loop P.sign.ctor_types.(idx)

  (** Prove [forall r t, eval (O.rename r t) = rename r (eval t)]. *)
  let prove_eval_rename () : unit Proofview.tactic =
    let open PVMonad in
    let* r = intro_fresh "r" in
    let* t = intro_fresh "t" in
    let* _ = Generalize.revert [ r ] in
    (* Induction on [t]. *)
    let* _ = pattern (EConstr.mkVar t) in
    let* _ = Tactics.apply (mkconst P.bij.term_ind) in
    dispatch @@ function
    (* Variable constructor. *)
    | 0 -> intro_n 2 >> Tactics.reflexivity
    (* Non-variable constructors. *)
    | i ->
        (* Introduce constructor arguments and induction hypotheses. *)
        let* _ = intro_fresh "r" in
        let* _ = intro_term_ind (i - 1) in
        (* Simplify. *)
        let* _ =
          Tacticals.tclREPEAT
            (Principles_proofs.simp_eqns [ "rename" ] >> Tactics.simpl_in_concl)
        in
        (* Apply the congruence principle and finish with [auto]. *)
        let* _ = Tactics.apply (mkconst P.congr.congr_ctors.(i - 1)) in
        auto ()

  (** Prove [forall r s, seval (O.rscomp r s) =₁ rscomp r (seval s)].*)
  let prove_seval_rscomp () : unit Proofview.tactic =
    let open PVMonad in
    let* _ = intro_n 3 in
    Tactics.reflexivity

  (** Prove [forall s r, seval (O.srcomp s r) =₁ srcomp (seval s) r].*)
  let prove_seval_srcomp (eval_rename : Names.Constant.t) : unit Proofview.tactic =
    let open PVMonad in
    let* _ = intro_fresh "s" in
    let* _ = intro_fresh "r" in
    let* _ = intro_fresh "i" in
    (* Unfold. *)
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.re.seval) in
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.ops0.srcomp) in
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.ops1.srcomp) in
    (* Apply [eval_rename]. *)
    Tactics.apply (mkconst eval_rename)

  (** Prove [forall t s, seval (O.scons t s) =₁ scons (eval t) (seval s)].*)
  let prove_seval_scons () : unit Proofview.tactic =
    let open PVMonad in
    let* _ = intro_fresh "t" in
    let* _ = intro_fresh "s" in
    let* i = intro_fresh "i" in
    (* Simply destruct [i]. *)
    let* _ = destruct @@ EConstr.mkVar i in
    Tactics.reflexivity

  (** Prove [forall s, seval (O.up_subst s) =₁ up_subst (seval s)].*)
  let prove_seval_up_subst (seval_srcomp : Names.Constant.t)
      (seval_scons : Names.Constant.t) : unit Proofview.tactic =
    let open PVMonad in
    let* _ = intro_fresh "s" in
    (* Unfold. *)
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.ops0.up_subst) in
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.ops1.up_subst) in
    (* Rewrite with [seval_scons]. *)
    let* _ = rewrite LeftToRight (Names.GlobRef.ConstRef seval_scons) in
    let* _ = Tactics.simpl_in_concl in
    (* Apply [congr_scons]. *)
    let* _ = Tactics.apply (mkconst P.congr.congr_scons) in
    (* Finish with [seval_srcomp]. *)
    auto ~lemmas:[ mkconst seval_srcomp ] ()

  (** Helper function for [prove_eval_substitute] which takes care of a single argument of
      non-variable constructor [idx] (starting at [0]). *)
  let prove_eval_substitute_aux (ty : arg_ty) (arg : Names.Id.t) (hyp : Names.Id.t option)
      (seval_up_subst : Names.Constant.t) : unit Proofview.tactic =
    let open PVMonad in
    (* Rewrite with the induction hypothesis. *)
    let* _ =
      match hyp with
      | None -> ret ()
      | Some hyp -> rewrite LeftToRight @@ Names.GlobRef.VarRef hyp
    in
    (* For [AT_bind AT_term] we need to rewrite with [seval_up_subst]. *)
    let solve_at_bind : unit Proofview.tactic =
      let* _ = Tactics.apply (mkconst P.congr.congr_substitute) in
      let* _ = Proofview.tclDISPATCH [ ret (); Tactics.reflexivity ] in
      Tacticals.tclREPEAT
        (rewrite LeftToRight (Names.GlobRef.ConstRef seval_up_subst)
        >> Tactics.apply (mkconst P.congr.congr_up_subst))
    in
    (* Some argument types - such as [AT_base _], [AT_term], or [AT_bind (AT_base _)] -
     only require [reflexivity]. *)
    Tacticals.tclSOLVE [ Tactics.reflexivity; solve_at_bind >> Tactics.reflexivity ]

  (** Prove [forall s t, eval (O.substitute s t) = substitute (seval s) (eval t)].*)
  let prove_eval_substitute (seval_up_subst : Names.Constant.t) : unit Proofview.tactic =
    let open PVMonad in
    let* s = intro_fresh "s" in
    let* t = intro_fresh "t" in
    (* Induction on [t]. *)
    let* _ = Generalize.revert [ s ] in
    let* _ = pattern (EConstr.mkVar t) in
    let* _ = Tactics.apply (mkconst P.bij.term_ind) in
    dispatch @@ function
    (* Variable constructor. *)
    | 0 -> intro_n 2 >> Tactics.reflexivity
    (* Non-variable constructors. *)
    | i ->
        let* args = intro_term_ind (i - 1) in
        let* s = intro_fresh "s" in
        (* Simplify. *)
        let* _ =
          Tacticals.tclREPEAT
            (Principles_proofs.simp_eqns [ "substitute" ] >> Tactics.simpl_in_concl)
        in
        (* Apply the right congruence lemma. *)
        let* _ = Tactics.apply (mkconst P.congr.congr_ctors.(i - 1)) in
        (* Rewrite with the induction hypotheses. *)
        Proofview.tclDISPATCH
        @@ List.map2
             (fun ty (arg, hyp) -> prove_eval_substitute_aux ty arg hyp seval_up_subst)
             P.sign.ctor_types.(i - 1)
             args

  (** Prove [forall s1 s2, seval (O.scomp s1 s2) =₁ scomp (seval s1) (seval s2)].*)
  let prove_seval_scomp (eval_substitute : Names.Constant.t) : unit Proofview.tactic =
    let open PVMonad in
    let* s1 = intro_fresh "s1" in
    let* s2 = intro_fresh "s2" in
    let* i = intro_fresh "i" in
    (* Unfold. *)
    let* _ = Tactics.unfold_constr @@ Names.GlobRef.ConstRef P.ops0.scomp in
    let* _ = Tactics.unfold_constr @@ Names.GlobRef.ConstRef P.ops1.scomp in
    let* _ = Tactics.unfold_constr @@ Names.GlobRef.ConstRef P.re.seval in
    (* Rewrite with [eval_substitute]. *)
    let* _ = rewrite LeftToRight @@ Names.GlobRef.ConstRef eval_substitute in
    Tactics.reflexivity

  (**************************************************************************************)
  (** *** Put everything together. *)
  (**************************************************************************************)

  let generate () : unit =
    let eval_rename =
      lemma "eval_rename" (build_eval_rename ()) @@ prove_eval_rename ()
    in
    let _seval_rscomp =
      lemma "seval_rscomp" (build_seval_rscomp ()) @@ prove_seval_rscomp ()
    in
    let seval_srcomp =
      lemma "seval_srcomp" (build_seval_srcomp ()) @@ prove_seval_srcomp eval_rename
    in
    let seval_scons =
      lemma "seval_scons" (build_seval_scons ()) @@ prove_seval_scons ()
    in
    let seval_up_subst =
      lemma "seval_up_subst" (build_seval_up_subst ())
      @@ prove_seval_up_subst seval_srcomp seval_scons
    in
    let eval_substitute =
      lemma "eval_substitute" (build_eval_substitute ())
      @@ prove_eval_substitute seval_up_subst
    in
    let _seval_scomp =
      lemma "seval_scomp" (build_seval_scomp ()) @@ prove_seval_scomp eval_substitute
    in
    ()
end
