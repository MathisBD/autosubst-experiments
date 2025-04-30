open Prelude

(**************************************************************************************)
(** *** Build the congruence lemmas. *)
(**************************************************************************************)

(** Build the congruence lemma for the non-variable constructor [idx] (starting at [0]).
*)
let build_congr_ctor (sign : signature) (ops : ops_zero) (idx : int) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ops.term in
  (* Helper function to bind the arguments of the constructor. *)
  let rec with_vars (tys : arg_ty list) (k : (Names.Id.t * Names.Id.t) list -> 'a m) :
      'a m =
    match tys with
    | [] -> k []
    | ty :: tys ->
        prod "l" (arg_ty_constr sign ty term) @@ fun t ->
        prod "r" (arg_ty_constr sign ty term) @@ fun t' ->
        with_vars tys @@ fun ts -> k ((t, t') :: ts)
  in
  (* Bind the arguments of the constructor. *)
  with_vars sign.ctor_types.(idx) @@ fun ts ->
  (* Build the hypotheses. *)
  let hyps =
    List.map2
      (fun (t, t') ty ->
        apps (Lazy.force Consts.eq) [| arg_ty_constr sign ty term; mkVar t; mkVar t' |])
      ts sign.ctor_types.(idx)
  in
  (* Build the conclusion. *)
  let* ctor = fresh_ctor (ops.term, idx + 2) in
  let left = apps ctor @@ Array.of_list @@ List.map mkVar @@ List.map fst ts in
  let right = apps ctor @@ Array.of_list @@ List.map mkVar @@ List.map snd ts in
  let concl = apps (Lazy.force Consts.eq) [| term; left; right |] in
  (* Assemble everything. *)
  ret @@ arrows hyps concl

(** Build [forall r r' t t', r =₁ r' -> t = t' -> rename r t = rename r' t']. *)
let build_congr_rename (sign : signature) (ops : ops_zero) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ops.term in
  prod "r" (Lazy.force Consts.ren) @@ fun r ->
  prod "r'" (Lazy.force Consts.ren) @@ fun r' ->
  prod "t" term @@ fun t ->
  prod "t'" term @@ fun t' ->
  let hyp_r =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat; Lazy.force Consts.nat; mkVar r; mkVar r' |]
  in
  let hyp_t = apps (Lazy.force Consts.eq) [| term; mkVar t; mkVar t' |] in
  let concl =
    apps (Lazy.force Consts.eq)
      [| term
       ; apps (mkconst ops.rename) [| mkVar r; mkVar t |]
       ; apps (mkconst ops.rename) [| mkVar r'; mkVar t' |]
      |]
  in
  ret @@ arrows [ hyp_r; hyp_t ] concl

(** Build [forall r r' s s', r =₁ r' -> s =₁ s' -> rscomp r s =₁ rscomp r' s']. *)
let build_congr_rscomp (sign : signature) (ops : ops_zero) : EConstr.t m =
  let open EConstr in
  prod "r" (Lazy.force Consts.ren) @@ fun r ->
  prod "r'" (Lazy.force Consts.ren) @@ fun r' ->
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  let hyp_r =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat; Lazy.force Consts.nat; mkVar r; mkVar r' |]
  in
  let hyp_s =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat; mkind ops.term; mkVar s; mkVar s' |]
  in
  let concl =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat
       ; mkind ops.term
       ; apps (mkconst ops.rscomp) [| mkVar r; mkVar s |]
       ; apps (mkconst ops.rscomp) [| mkVar r'; mkVar s' |]
      |]
  in
  ret @@ arrows [ hyp_r; hyp_s ] concl

(** Build [forall s s' r r', s =₁ s' -> r =₁ r' -> srcomp s r =₁ srcomp s' r']. *)
let build_congr_srcomp (sign : signature) (ops : ops_zero) : EConstr.t m =
  let open EConstr in
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  prod "r" (Lazy.force Consts.ren) @@ fun r ->
  prod "r'" (Lazy.force Consts.ren) @@ fun r' ->
  let hyp_s =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat; mkind ops.term; mkVar s; mkVar s' |]
  in
  let hyp_r =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat; Lazy.force Consts.nat; mkVar r; mkVar r' |]
  in
  let concl =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat
       ; mkind ops.term
       ; apps (mkconst ops.srcomp) [| mkVar s; mkVar r |]
       ; apps (mkconst ops.srcomp) [| mkVar s'; mkVar r' |]
      |]
  in
  ret @@ arrows [ hyp_s; hyp_r ] concl

(** Build [forall t t' s s', t = t' -> s =₁ s' -> scons t s =₁ scons t' s']. *)
let build_congr_scons (sign : signature) (ops : ops_zero) : EConstr.t m =
  let open EConstr in
  prod "t" (mkind ops.term) @@ fun t ->
  prod "t'" (mkind ops.term) @@ fun t' ->
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  let hyp_t = apps (Lazy.force Consts.eq) [| mkind ops.term; mkVar t; mkVar t' |] in
  let hyp_s =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat; mkind ops.term; mkVar s; mkVar s' |]
  in
  let concl =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat
       ; mkind ops.term
       ; apps (mkconst ops.scons) [| mkVar t; mkVar s |]
       ; apps (mkconst ops.scons) [| mkVar t'; mkVar s' |]
      |]
  in
  ret @@ arrows [ hyp_t; hyp_s ] concl

(** Build [forall s s', s =₁ s' -> up_subst s =₁ up_subst s']. *)
let build_congr_up_subst (sign : signature) (ops : ops_zero) : EConstr.t m =
  let open EConstr in
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  let hyp =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat; mkind ops.term; mkVar s; mkVar s' |]
  in
  let concl =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat
       ; mkind ops.term
       ; app (mkconst ops.up_subst) (mkVar s)
       ; app (mkconst ops.up_subst) (mkVar s')
      |]
  in
  ret @@ arrow hyp concl

(** Build [forall s s' t t', s =₁ s' -> t = t' -> substitute s t = substitute s' t']. *)
let build_congr_substitute (sign : signature) (ops : ops_zero) : EConstr.t m =
  let open EConstr in
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  prod "t" (mkind ops.term) @@ fun t ->
  prod "t'" (mkind ops.term) @@ fun t' ->
  let hyp_s =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat; mkind ops.term; mkVar s; mkVar s' |]
  in
  let hyp_t = apps (Lazy.force Consts.eq) [| mkind ops.term; mkVar t; mkVar t' |] in
  let concl =
    apps (Lazy.force Consts.eq)
      [| mkind ops.term
       ; apps (mkconst ops.substitute) [| mkVar s; mkVar t |]
       ; apps (mkconst ops.substitute) [| mkVar s'; mkVar t' |]
      |]
  in
  ret @@ arrows [ hyp_s; hyp_t ] concl

(** Build [forall s1 s1' s2 s2', s1 =₁ s1' -> s2 =₁ s2' -> scomp s1 s2 =₁ scomp s1' s2'].
*)
let build_congr_scomp (sign : signature) (ops : ops_zero) : EConstr.t m =
  let open EConstr in
  prod "s1" (mkconst ops.subst) @@ fun s1 ->
  prod "s1'" (mkconst ops.subst) @@ fun s1' ->
  prod "s2" (mkconst ops.subst) @@ fun s2 ->
  prod "s2'" (mkconst ops.subst) @@ fun s2' ->
  let hyp_s1 =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat; mkind ops.term; mkVar s1; mkVar s1' |]
  in
  let hyp_s2 =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat; mkind ops.term; mkVar s2; mkVar s2' |]
  in
  let concl =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat
       ; mkind ops.term
       ; apps (mkconst ops.scomp) [| mkVar s1; mkVar s2 |]
       ; apps (mkconst ops.scomp) [| mkVar s1'; mkVar s2' |]
      |]
  in
  ret @@ arrows [ hyp_s1; hyp_s2 ] concl

(**************************************************************************************)
(** *** Prove the congruence lemmas. *)
(**************************************************************************************)

(** Prove the congruence lemma for the non-variable constructor [idx] (starting at [0]).
*)
let prove_congr_ctor (sign : signature) (ops : ops_zero) (idx : int) :
    unit Proofview.tactic =
  let open PVMonad in
  let arg_tys = sign.ctor_types.(idx) in
  (* Introduce the constructor arguments. *)
  let* _ = intro_n (2 * List.length arg_tys) in
  (* Introduce each hypothesis and rewrite with it from left to right. *)
  let* _ = Tacticals.tclDO (List.length arg_tys) @@ intro_rewrite ~dir:true in
  (* Close with reflexivity. *)
  Tactics.reflexivity

(** Prove [forall r r' t t', r =₁ r' -> t = t' -> rename r t = rename r' t']. *)
let prove_congr_rename (sign : signature) (ops : ops_zero)
    (congr_ctors : Names.Constant.t array) : unit Proofview.tactic =
  let open PVMonad in
  (* Introduce the variables. *)
  let* r = intro_fresh "r" in
  let* r' = intro_fresh "r'" in
  let* t = intro_fresh "t" in
  let* _ = intro_fresh "t'" in
  (* Rewrite with the second hypothesis. *)
  let* hyp_r = intro_fresh "H" in
  let* _ = intro_rewrite ~dir:false in
  (* Induction on [t]. *)
  let* _ = Generalize.revert [ r; r'; hyp_r ] in
  let intro_patt =
    CAst.make @@ Tactypes.IntroOrPattern (List.init (1 + sign.n_ctors) @@ fun _ -> [])
  in
  let* _ = Induction.induction false None (EConstr.mkVar t) (Some intro_patt) None in
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
    auto ~lemmas:[ Lazy.force Consts.congr_up_ren ] ()

(** Prove [forall r r' s s', r =₁ r' -> s =₁ s' -> rscomp r s =₁ rscomp r' s']. *)
let prove_congr_rscomp (sign : signature) (ops : ops_zero) : unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_n 4 in
  let* h1 = intro_fresh "H" in
  let* h2 = intro_fresh "H" in
  let* _ = intro_fresh "i" in
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops.rscomp) in
  let* _ = rewrite ~dir:true (Names.GlobRef.VarRef h1) in
  let* _ = rewrite ~dir:true (Names.GlobRef.VarRef h2) in
  Tactics.reflexivity

(** Prove [forall s s' r r', s =₁ s' -> r =₁ r' -> srcomp s r =₁ srcomp s' r']. *)
let prove_congr_srcomp (sign : signature) (ops : ops_zero)
    (congr_rename : Names.Constant.t) : unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_n 4 in
  let* h1 = intro_fresh "H" in
  let* h2 = intro_fresh "H" in
  let* _ = intro_fresh "i" in
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops.srcomp) in
  let* _ = Tactics.apply (mkconst congr_rename) in
  auto ()

(** Prove [forall t t' s s', t = t' -> s =₁ s' -> scons t s =₁ scons t' s']. *)
let prove_congr_scons (sign : signature) (ops : ops_zero) : unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_n 4 in
  let* _ = intro_rewrite ~dir:true in
  let* h = intro_fresh "H" in
  (* Introduce [i] and immediately destruct it. *)
  let i_patt =
    Tactypes.IntroAction (Tactypes.IntroOrAndPattern (Tactypes.IntroOrPattern [ []; [] ]))
  in
  let* _ = Tactics.intro_patterns false [ CAst.make @@ i_patt ] in
  (* Unfold [scons] and finish with auto. *)
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops.scons) in
  Proofview.tclDISPATCH [ Tactics.reflexivity; Tactics.apply (EConstr.mkVar h) ]

(** Prove [forall s s', s =₁ s' -> up_subst s =₁ up_subst s']. *)
let prove_congr_up_subst (sign : signature) (ops : ops_zero)
    (congr_scons : Names.Constant.t) (congr_srcomp : Names.Constant.t) :
    unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_n 2 in
  let* h = intro_fresh "H" in
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops.up_subst) in
  (* Apply [congr_scons]. *)
  let* _ = Tactics.apply (mkconst congr_scons) in
  let* _ = Proofview.tclDISPATCH [ Tactics.reflexivity; ret () ] in
  (* Apply [congr_srcomp]. *)
  let* _ = Tactics.apply (mkconst congr_srcomp) in
  Proofview.tclDISPATCH [ Tactics.assumption; Tactics.reflexivity ]

(** Prove [forall s s' t t', s =₁ s' -> t = t' -> substitute s t =₁ substitute s' t']. *)
let prove_congr_substitute (sign : signature) (ops : ops_zero)
    (congr_up_subst : Names.Constant.t) (congr_ctors : Names.Constant.t array) :
    unit Proofview.tactic =
  let open PVMonad in
  (* Introduce the variables. *)
  let* s = intro_fresh "s" in
  let* s' = intro_fresh "s'" in
  let* t = intro_fresh "t" in
  let* _ = intro_fresh "t'" in
  (* Rewrite with the second hypothesis. *)
  let* hyp_s = intro_fresh "H" in
  let* _ = intro_rewrite ~dir:false in
  (* Induction on [t]. *)
  let* _ = Generalize.revert [ s; s'; hyp_s ] in
  let intro_patt =
    CAst.make @@ Tactypes.IntroOrPattern (List.init (1 + sign.n_ctors) @@ fun _ -> [])
  in
  let* _ = Induction.induction false None (EConstr.mkVar t) (Some intro_patt) None in
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

(** Prove [forall s1 s1' s2 s2', s1 =₁ s1' -> s2 =₁ s2' -> scomp s1 s2 =₁ scomp s1' s2'].
*)
let prove_congr_scomp (sign : signature) (ops : ops_zero)
    (congr_substitute : Names.Constant.t) : unit Proofview.tactic =
  let open PVMonad in
  (* Introduce the variables. *)
  let* _ = intro_n 4 in
  let* h1 = intro_fresh "H" in
  let* h2 = intro_fresh "H" in
  let* i = intro_fresh "i" in
  (* Unfold [scomp]. *)
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops.scomp) in
  (* Apply [congr_substitute]. *)
  let* _ = Tactics.apply (mkconst congr_substitute) in
  auto ()

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Generate all the congruence lemmas. *)
let generate (s : signature) (ops : ops_zero) : congr_lemmas =
  let congr_ctors =
    Array.init s.n_ctors @@ fun i ->
    let name = String.concat "_" [ "congr"; s.ctor_names.(i) ] in
    lemma name (build_congr_ctor s ops i) @@ prove_congr_ctor s ops i
  in
  let congr_rename =
    lemma "congr_rename" (build_congr_rename s ops)
    @@ prove_congr_rename s ops congr_ctors
  in
  let congr_rscomp =
    lemma "congr_rscomp" (build_congr_rscomp s ops) @@ prove_congr_rscomp s ops
  in
  let congr_srcomp =
    lemma "congr_srcomp" (build_congr_srcomp s ops)
    @@ prove_congr_srcomp s ops congr_rename
  in
  let congr_scons =
    lemma "congr_scons" (build_congr_scons s ops) @@ prove_congr_scons s ops
  in
  let congr_up_subst =
    lemma "congr_up_subst" (build_congr_up_subst s ops)
    @@ prove_congr_up_subst s ops congr_scons congr_srcomp
  in
  let congr_substitute =
    lemma "congr_substitute" (build_congr_substitute s ops)
    @@ prove_congr_substitute s ops congr_up_subst congr_ctors
  in
  let congr_scomp =
    lemma "congr_scomp" (build_congr_scomp s ops)
    @@ prove_congr_scomp s ops congr_substitute
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
