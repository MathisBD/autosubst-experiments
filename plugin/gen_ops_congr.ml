open Prelude
open Signature
module C = Constants

module Make (P : sig
  val sign : signature
  val ops0 : ops_zero
end) =
struct
  (**************************************************************************************)
  (** *** Build the congruence lemmas. *)
  (**************************************************************************************)

  (** Build the congruence lemma for the non-variable constructor [idx] (starting at [0]).
  *)
  let build_congr_ctor (idx : int) : EConstr.t m =
    let open EConstr in
    (* Helper function to bind the arguments of the constructor. *)
    let rec with_vars (tys : arg_ty list) (k : (Names.Id.t * Names.Id.t) list -> 'a m) :
        'a m =
      match tys with
      | [] -> k []
      | ty :: tys ->
          prod "l" (arg_ty_constr P.sign ty @@ mkind P.ops0.term) @@ fun t ->
          prod "r" (arg_ty_constr P.sign ty @@ mkind P.ops0.term) @@ fun t' ->
          with_vars tys @@ fun ts -> k ((t, t') :: ts)
    in
    (* Bind the arguments of the constructor. *)
    with_vars P.sign.ctor_types.(idx) @@ fun ts ->
    (* Build the hypotheses. *)
    let hyps =
      List.map2
        (fun (t, t') ty ->
          apps (mkglob' C.eq)
            [| arg_ty_constr P.sign ty @@ mkind P.ops0.term; mkVar t; mkVar t' |])
        ts P.sign.ctor_types.(idx)
    in
    (* Build the conclusion. *)
    let ctor = mkctor (P.ops0.term, idx + 2) in
    let left = apps ctor @@ Array.of_list @@ List.map mkVar @@ List.map fst ts in
    let right = apps ctor @@ Array.of_list @@ List.map mkVar @@ List.map snd ts in
    let concl = apps (mkglob' C.eq) [| mkind P.ops0.term; left; right |] in
    (* Assemble everything. *)
    ret @@ arrows hyps concl

  (** Build [forall r r' t t', r =₁ r' -> t = t' -> rename r t = rename r' t']. *)
  let build_congr_rename () : EConstr.t m =
    let open EConstr in
    prod "r" (mkglob' C.ren) @@ fun r ->
    prod "r'" (mkglob' C.ren) @@ fun r' ->
    prod "t" (mkind P.ops0.term) @@ fun t ->
    prod "t'" (mkind P.ops0.term) @@ fun t' ->
    let hyp_r =
      apps (mkglob' C.point_eq) [| mkglob' C.nat; mkglob' C.nat; mkVar r; mkVar r' |]
    in
    let hyp_t = apps (mkglob' C.eq) [| mkind P.ops0.term; mkVar t; mkVar t' |] in
    let concl =
      apps (mkglob' C.eq)
        [| mkind P.ops0.term
         ; apps (mkconst P.ops0.rename) [| mkVar r; mkVar t |]
         ; apps (mkconst P.ops0.rename) [| mkVar r'; mkVar t' |]
        |]
    in
    ret @@ arrows [ hyp_r; hyp_t ] concl

  (** Build [forall r r' s s', r =₁ r' -> s =₁ s' -> rscomp r s =₁ rscomp r' s']. *)
  let build_congr_rscomp () : EConstr.t m =
    let open EConstr in
    prod "r" (mkglob' C.ren) @@ fun r ->
    prod "r'" (mkglob' C.ren) @@ fun r' ->
    prod "s" (mkconst P.ops0.subst) @@ fun s ->
    prod "s'" (mkconst P.ops0.subst) @@ fun s' ->
    let hyp_r =
      apps (mkglob' C.point_eq) [| mkglob' C.nat; mkglob' C.nat; mkVar r; mkVar r' |]
    in
    let hyp_s =
      apps (mkglob' C.point_eq) [| mkglob' C.nat; mkind P.ops0.term; mkVar s; mkVar s' |]
    in
    let concl =
      apps (mkglob' C.point_eq)
        [| mkglob' C.nat
         ; mkind P.ops0.term
         ; apps (mkconst P.ops0.rscomp) [| mkVar r; mkVar s |]
         ; apps (mkconst P.ops0.rscomp) [| mkVar r'; mkVar s' |]
        |]
    in
    ret @@ arrows [ hyp_r; hyp_s ] concl

  (** Build [forall s s' r r', s =₁ s' -> r =₁ r' -> srcomp s r =₁ srcomp s' r']. *)
  let build_congr_srcomp () : EConstr.t m =
    let open EConstr in
    prod "s" (mkconst P.ops0.subst) @@ fun s ->
    prod "s'" (mkconst P.ops0.subst) @@ fun s' ->
    prod "r" (mkglob' C.ren) @@ fun r ->
    prod "r'" (mkglob' C.ren) @@ fun r' ->
    let hyp_s =
      apps (mkglob' C.point_eq) [| mkglob' C.nat; mkind P.ops0.term; mkVar s; mkVar s' |]
    in
    let hyp_r =
      apps (mkglob' C.point_eq) [| mkglob' C.nat; mkglob' C.nat; mkVar r; mkVar r' |]
    in
    let concl =
      apps (mkglob' C.point_eq)
        [| mkglob' C.nat
         ; mkind P.ops0.term
         ; apps (mkconst P.ops0.srcomp) [| mkVar s; mkVar r |]
         ; apps (mkconst P.ops0.srcomp) [| mkVar s'; mkVar r' |]
        |]
    in
    ret @@ arrows [ hyp_s; hyp_r ] concl

  (** Build [forall t t' s s', t = t' -> s =₁ s' -> scons t s =₁ scons t' s']. *)
  let build_congr_scons () : EConstr.t m =
    let open EConstr in
    prod "t" (mkind P.ops0.term) @@ fun t ->
    prod "t'" (mkind P.ops0.term) @@ fun t' ->
    prod "s" (mkconst P.ops0.subst) @@ fun s ->
    prod "s'" (mkconst P.ops0.subst) @@ fun s' ->
    let hyp_t = apps (mkglob' C.eq) [| mkind P.ops0.term; mkVar t; mkVar t' |] in
    let hyp_s =
      apps (mkglob' C.point_eq) [| mkglob' C.nat; mkind P.ops0.term; mkVar s; mkVar s' |]
    in
    let concl =
      apps (mkglob' C.point_eq)
        [| mkglob' C.nat
         ; mkind P.ops0.term
         ; apps (mkconst P.ops0.scons) [| mkVar t; mkVar s |]
         ; apps (mkconst P.ops0.scons) [| mkVar t'; mkVar s' |]
        |]
    in
    ret @@ arrows [ hyp_t; hyp_s ] concl

  (** Build [forall s s', s =₁ s' -> up_subst s =₁ up_subst s']. *)
  let build_congr_up_subst () : EConstr.t m =
    let open EConstr in
    prod "s" (mkconst P.ops0.subst) @@ fun s ->
    prod "s'" (mkconst P.ops0.subst) @@ fun s' ->
    let hyp =
      apps (mkglob' C.point_eq) [| mkglob' C.nat; mkind P.ops0.term; mkVar s; mkVar s' |]
    in
    let concl =
      apps (mkglob' C.point_eq)
        [| mkglob' C.nat
         ; mkind P.ops0.term
         ; app (mkconst P.ops0.up_subst) (mkVar s)
         ; app (mkconst P.ops0.up_subst) (mkVar s')
        |]
    in
    ret @@ arrow hyp concl

  (** Build [forall s s' t t', s =₁ s' -> t = t' -> substitute s t = substitute s' t']. *)
  let build_congr_substitute () : EConstr.t m =
    let open EConstr in
    prod "s" (mkconst P.ops0.subst) @@ fun s ->
    prod "s'" (mkconst P.ops0.subst) @@ fun s' ->
    prod "t" (mkind P.ops0.term) @@ fun t ->
    prod "t'" (mkind P.ops0.term) @@ fun t' ->
    let hyp_s =
      apps (mkglob' C.point_eq) [| mkglob' C.nat; mkind P.ops0.term; mkVar s; mkVar s' |]
    in
    let hyp_t = apps (mkglob' C.eq) [| mkind P.ops0.term; mkVar t; mkVar t' |] in
    let concl =
      apps (mkglob' C.eq)
        [| mkind P.ops0.term
         ; apps (mkconst P.ops0.substitute) [| mkVar s; mkVar t |]
         ; apps (mkconst P.ops0.substitute) [| mkVar s'; mkVar t' |]
        |]
    in
    ret @@ arrows [ hyp_s; hyp_t ] concl

  (** Build
      [forall s1 s1' s2 s2', s1 =₁ s1' -> s2 =₁ s2' -> scomp s1 s2 =₁ scomp s1' s2']. *)
  let build_congr_scomp () : EConstr.t m =
    let open EConstr in
    prod "s1" (mkconst P.ops0.subst) @@ fun s1 ->
    prod "s1'" (mkconst P.ops0.subst) @@ fun s1' ->
    prod "s2" (mkconst P.ops0.subst) @@ fun s2 ->
    prod "s2'" (mkconst P.ops0.subst) @@ fun s2' ->
    let hyp_s1 =
      apps (mkglob' C.point_eq)
        [| mkglob' C.nat; mkind P.ops0.term; mkVar s1; mkVar s1' |]
    in
    let hyp_s2 =
      apps (mkglob' C.point_eq)
        [| mkglob' C.nat; mkind P.ops0.term; mkVar s2; mkVar s2' |]
    in
    let concl =
      apps (mkglob' C.point_eq)
        [| mkglob' C.nat
         ; mkind P.ops0.term
         ; apps (mkconst P.ops0.scomp) [| mkVar s1; mkVar s2 |]
         ; apps (mkconst P.ops0.scomp) [| mkVar s1'; mkVar s2' |]
        |]
    in
    ret @@ arrows [ hyp_s1; hyp_s2 ] concl

  (**************************************************************************************)
  (** *** Prove the congruence lemmas. *)
  (**************************************************************************************)

  (** Prove the congruence lemma for the non-variable constructor [idx] (starting at [0]).
  *)
  let prove_congr_ctor (idx : int) : unit Proofview.tactic =
    let open PVMonad in
    let arg_tys = P.sign.ctor_types.(idx) in
    (* Introduce the constructor arguments. *)
    let* _ = intro_n (2 * List.length arg_tys) in
    (* Introduce each hypothesis and rewrite with it from left to right. *)
    let* _ = Tacticals.tclDO (List.length arg_tys) @@ intro_rewrite LeftToRight in
    (* Close with reflexivity. *)
    Tactics.reflexivity

  (** Prove [forall r r' t t', r =₁ r' -> t = t' -> rename r t = rename r' t']. *)
  let prove_congr_rename (congr_ctors : Names.Constant.t array) : unit Proofview.tactic =
    let open PVMonad in
    (* Introduce the variables. *)
    let* r = intro_fresh "r" in
    let* r' = intro_fresh "r'" in
    let* t = intro_fresh "t" in
    let* _ = intro_fresh "t'" in
    (* Rewrite with the second hypothesis. *)
    let* hyp_r = intro_fresh "H" in
    let* _ = intro_rewrite RightToLeft in
    (* Induction on [t]. *)
    let* _ = Generalize.revert [ r; r'; hyp_r ] in
    let* _ = induction @@ EConstr.mkVar t in
    (* Process each subgoal. *)
    dispatch @@ fun i ->
    let* r = intro_fresh "r" in
    let* r' = intro_fresh "r'" in
    let* hyp = intro_fresh "H" in
    let* _ = Tactics.simpl_in_concl in
    if i = 0
    then
      (* Variable constructor. *)
      auto ()
    else
      (* Other constructors. *)
      let* _ = Tactics.apply @@ mkconst congr_ctors.(i - 1) in
      auto ~lemmas:[ mkglob' C.congr_up_ren ] ()

  (** Prove [forall r r' s s', r =₁ r' -> s =₁ s' -> rscomp r s =₁ rscomp r' s']. *)
  let prove_congr_rscomp () : unit Proofview.tactic =
    let open PVMonad in
    let* _ = intro_n 4 in
    let* h1 = intro_fresh "H" in
    let* h2 = intro_fresh "H" in
    let* _ = intro_fresh "i" in
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.ops0.rscomp) in
    let* _ = rewrite LeftToRight (Names.GlobRef.VarRef h1) in
    let* _ = rewrite LeftToRight (Names.GlobRef.VarRef h2) in
    Tactics.reflexivity

  (** Prove [forall s s' r r', s =₁ s' -> r =₁ r' -> srcomp s r =₁ srcomp s' r']. *)
  let prove_congr_srcomp (congr_rename : Names.Constant.t) : unit Proofview.tactic =
    let open PVMonad in
    let* _ = intro_n 4 in
    let* h1 = intro_fresh "H" in
    let* h2 = intro_fresh "H" in
    let* _ = intro_fresh "i" in
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.ops0.srcomp) in
    let* _ = Tactics.apply (mkconst congr_rename) in
    auto ()

  (** Prove [forall t t' s s', t = t' -> s =₁ s' -> scons t s =₁ scons t' s']. *)
  let prove_congr_scons () : unit Proofview.tactic =
    let open PVMonad in
    let* _ = intro_n 4 in
    let* _ = intro_rewrite LeftToRight in
    let* h = intro_fresh "H" in
    (* Introduce [i] and immediately destruct it. *)
    let i_patt =
      Tactypes.IntroAction
        (Tactypes.IntroOrAndPattern (Tactypes.IntroOrPattern [ []; [] ]))
    in
    let* _ = Tactics.intro_patterns false [ CAst.make @@ i_patt ] in
    (* Unfold [scons] and finish with auto. *)
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.ops0.scons) in
    Proofview.tclDISPATCH [ Tactics.reflexivity; Tactics.apply (EConstr.mkVar h) ]

  (** Prove [forall s s', s =₁ s' -> up_subst s =₁ up_subst s']. *)
  let prove_congr_up_subst (congr_scons : Names.Constant.t)
      (congr_srcomp : Names.Constant.t) : unit Proofview.tactic =
    let open PVMonad in
    let* _ = intro_n 2 in
    let* h = intro_fresh "H" in
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.ops0.up_subst) in
    (* Apply [congr_scons]. *)
    let* _ = Tactics.apply (mkconst congr_scons) in
    let* _ = Proofview.tclDISPATCH [ Tactics.reflexivity; ret () ] in
    (* Apply [congr_srcomp]. *)
    let* _ = Tactics.apply (mkconst congr_srcomp) in
    Proofview.tclDISPATCH [ Tactics.assumption; Tactics.reflexivity ]

  (** Prove [forall s s' t t', s =₁ s' -> t = t' -> substitute s t =₁ substitute s' t'].
  *)
  let prove_congr_substitute (congr_up_subst : Names.Constant.t)
      (congr_ctors : Names.Constant.t array) : unit Proofview.tactic =
    let open PVMonad in
    (* Introduce the variables. *)
    let* s = intro_fresh "s" in
    let* s' = intro_fresh "s'" in
    let* t = intro_fresh "t" in
    let* _ = intro_fresh "t'" in
    (* Rewrite with the second hypothesis. *)
    let* hyp_s = intro_fresh "H" in
    let* _ = intro_rewrite RightToLeft in
    (* Induction on [t]. *)
    let* _ = Generalize.revert [ s; s'; hyp_s ] in
    let* _ = induction @@ EConstr.mkVar t in
    (* Process each subgoal. *)
    dispatch @@ fun i ->
    let* s = intro_fresh "s" in
    let* s' = intro_fresh "s'" in
    let* hyp_s = intro_fresh "H" in
    let* _ = Tactics.simpl_in_concl in
    if i = 0
    then
      (* Variable constructor. *)
      auto ()
    else
      (* Other constructors. *)
      let* _ = Tactics.apply @@ mkconst congr_ctors.(i - 1) in
      auto ~lemmas:[ mkconst congr_up_subst ] ()

  (** Prove
      [forall s1 s1' s2 s2', s1 =₁ s1' -> s2 =₁ s2' -> scomp s1 s2 =₁ scomp s1' s2']. *)
  let prove_congr_scomp (congr_substitute : Names.Constant.t) : unit Proofview.tactic =
    let open PVMonad in
    (* Introduce the variables. *)
    let* _ = intro_n 4 in
    let* h1 = intro_fresh "H" in
    let* h2 = intro_fresh "H" in
    let* i = intro_fresh "i" in
    (* Unfold [scomp]. *)
    let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef P.ops0.scomp) in
    (* Apply [congr_substitute]. *)
    let* _ = Tactics.apply (mkconst congr_substitute) in
    auto ()
end

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Generate all the congruence lemmas. *)
let generate (s : signature) (ops0 : ops_zero) : ops_congr =
  let module M = Make (struct
    let sign = s
    let ops0 = ops0
  end) in
  let congr_ctors =
    Array.init s.n_ctors @@ fun i ->
    let name = "congr_" ^ Names.Id.to_string s.ctor_names.(i) in
    lemma name (M.build_congr_ctor i) @@ M.prove_congr_ctor i
  in
  let congr_rename =
    lemma "congr_rename" (M.build_congr_rename ()) @@ M.prove_congr_rename congr_ctors
  in
  let congr_rscomp =
    lemma "congr_rscomp" (M.build_congr_rscomp ()) @@ M.prove_congr_rscomp ()
  in
  let congr_srcomp =
    lemma "congr_srcomp" (M.build_congr_srcomp ()) @@ M.prove_congr_srcomp congr_rename
  in
  let congr_scons =
    lemma "congr_scons" (M.build_congr_scons ()) @@ M.prove_congr_scons ()
  in
  let congr_up_subst =
    lemma "congr_up_subst" (M.build_congr_up_subst ())
    @@ M.prove_congr_up_subst congr_scons congr_srcomp
  in
  let congr_substitute =
    lemma "congr_substitute" (M.build_congr_substitute ())
    @@ M.prove_congr_substitute congr_up_subst congr_ctors
  in
  let congr_scomp =
    lemma "congr_scomp" (M.build_congr_scomp ()) @@ M.prove_congr_scomp congr_substitute
  in
  { congr_ctors
  ; congr_rename
  ; congr_substitute
  ; congr_rscomp
  ; congr_srcomp
  ; congr_scomp
  ; congr_scons
  ; congr_up_subst
  }
