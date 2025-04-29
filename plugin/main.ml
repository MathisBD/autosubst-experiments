open Monad
open Locally_nameless
open Custom_tactics

(**************************************************************************************)
(** *** Rocq constants we need to access from OCaml. *)
(**************************************************************************************)

let eq : Names.Ind.t =
  (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Logic" ] "eq", 0)

let point_eq : Names.Constant.t =
  Names.Constant.make1 @@ mk_kername [ "Prototype"; "Prelude" ] "point_eq"

let nat : Names.Ind.t =
  (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Datatypes" ] "nat", 0)

let nat_zero : Names.Construct.t = (nat, 1)
let nat_succ : Names.Construct.t = (nat, 2)

let string : Names.Ind.t =
  (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Strings"; "String" ] "string", 0)

let ren : Names.Constant.t =
  Names.Constant.make1 @@ mk_kername [ "Prototype"; "Prelude" ] "ren"

let rshift : Names.Constant.t =
  Names.Constant.make1 @@ mk_kername [ "Prototype"; "Prelude" ] "rshift"

let up_ren : Names.Constant.t =
  Names.Constant.make1 @@ mk_kername [ "Prototype"; "Prelude" ] "up_ren"

let congr_up_ren : Names.Constant.t =
  Names.Constant.make1 @@ mk_kername [ "Prototype"; "Prelude" ] "congr_up_ren"

(**************************************************************************************)
(** *** OCaml representation of a signature. *)
(**************************************************************************************)

(** Argument type. *)
type arg_ty = AT_base of EConstr.types | AT_term | AT_bind of arg_ty

(** An abstract signature:
    - [n_ctors] is the number of _non-variable_ constructors.
    - [ctor_names] contains the name of each constructor.
    - [ctor_sig] contains the argument types of each constructor.

    The length of [ctor_names] and [ctor_sig] should be equal to [n_ctors]. *)
type signature =
  { n_ctors : int; ctor_names : string array; ctor_types : arg_ty list array }

(** [arg_ty_constr ty ind] builds the [EConstr.t] corresponding to [ty]. We use [ind] as a
    placeholder for the inductive type of terms. *)
let rec arg_ty_constr (ty : arg_ty) (ind : EConstr.t) : EConstr.t =
  match ty with AT_base b -> b | AT_term -> ind | AT_bind ty -> arg_ty_constr ty ind

(** [ctor_ty_constr tys ind] build the type of a constructor as a [EConstr.t]. We use
    [ind] as a placeholder for the inductive type of terms. *)
let ctor_ty_constr (tys : arg_ty list) (ind : EConstr.t) : EConstr.t =
  arrows (List.map (fun ty -> arg_ty_constr ty ind) tys) ind

(**************************************************************************************)
(** *** Build the term inductive and related operations (renaming, substitution, etc). *)
(**************************************************************************************)

let build_term (sign : signature) : Names.Ind.t m =
  (* Constructor names and types. We add an extra constructor for variables. *)
  let ctor_names = "Var" :: Array.to_list sign.ctor_names in
  let ctor_types =
    (fun ind -> ret @@ arrow (mkind nat) (EConstr.mkVar ind))
    :: Array.to_list
         (Array.map
            (fun ty ind -> ret @@ ctor_ty_constr ty (EConstr.mkVar ind))
            sign.ctor_types)
  in
  (* Declare the inductive. *)
  declare_ind "term" EConstr.mkSet ctor_names ctor_types

let rec rename_arg (rename : EConstr.t) (r : EConstr.t) (arg : EConstr.t) (ty : arg_ty) :
    EConstr.t =
  match ty with
  | AT_base _ -> arg
  | AT_term -> apps rename [| r; arg |]
  | AT_bind ty ->
      let r' = app (mkconst up_ren) r in
      rename_arg rename r' arg ty

let build_rename (sign : signature) (term : Names.Ind.t) : EConstr.t m =
  let open EConstr in
  (* Bind the input parameters. *)
  fix "rename" 1 (arrows [ mkconst ren; mkind term ] (mkind term)) @@ fun rename ->
  lambda "r" (mkconst ren) @@ fun r ->
  lambda "t" (mkind term) @@ fun t ->
  (* Build the case expression. *)
  case (mkVar t) @@ fun i args ->
  if i = 0
  then
    (* Variable branch. *)
    ret @@ app (mkctor (term, 1)) @@ app (mkVar r) (mkVar @@ List.hd args)
  else
    (* Other branches. *)
    let args' =
      List.map2
        (rename_arg (mkVar rename) (mkVar r))
        (List.map mkVar args)
        sign.ctor_types.(i - 1)
    in
    ret @@ apps (mkctor (term, i + 1)) @@ Array.of_list args'

let build_subst (term : Names.Ind.t) : EConstr.t m = ret @@ arrow (mkind nat) (mkind term)

let build_srcomp (ind : Names.Ind.t) (subst : Names.Constant.t)
    (rename : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "s" (mkconst subst) @@ fun s ->
  lambda "r" (mkconst ren) @@ fun r ->
  lambda "i" (mkind nat) @@ fun i ->
  ret @@ apps (mkconst rename) [| mkVar r; app (mkVar s) (mkVar i) |]

let build_rscomp (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "r" (mkconst ren) @@ fun r ->
  lambda "s" (mkconst subst) @@ fun s ->
  lambda "i" (mkind nat) @@ fun i -> ret @@ app (mkVar s) @@ app (mkVar r) (mkVar i)

let build_sid (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "i" (mkind nat) @@ fun i -> ret @@ app (mkctor (term, 1)) (mkVar i)

let build_sshift (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "i" (mkind nat) @@ fun i ->
  ret @@ app (mkctor (term, 1)) @@ app (mkctor nat_succ) (mkVar i)

let build_scons (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "t" (mkind term) @@ fun t ->
  lambda "s" (mkconst subst) @@ fun s ->
  lambda "i" (mkind nat) @@ fun i ->
  case (mkVar i) @@ fun idx args ->
  if idx = 0 then ret (mkVar t) else ret @@ app (mkVar s) (mkVar @@ List.hd args)

let build_up_subst (term : Names.Ind.t) (subst : Names.Constant.t)
    (scons : Names.Constant.t) (srcomp : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "s" (mkconst subst) @@ fun s ->
  ret
  @@ apps (mkconst scons)
       [| app (mkctor (term, 1)) (mkctor nat_zero)
        ; apps (mkconst srcomp) [| mkVar s; mkconst rshift |]
       |]

let rec substitute_arg (substitute : EConstr.t) (up_subst : EConstr.t) (s : EConstr.t)
    (arg : EConstr.t) (ty : arg_ty) : EConstr.t =
  match ty with
  | AT_base _ -> arg
  | AT_term -> apps substitute [| s; arg |]
  | AT_bind ty -> substitute_arg substitute up_subst (app up_subst s) arg ty

let build_substitute (s_ : signature) (term : Names.Ind.t) (subst : Names.Constant.t)
    (up_subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  fix "substitute" 1 (arrows [ mkconst subst; mkind term ] @@ mkind term)
  @@ fun substitute ->
  lambda "s" (mkconst subst) @@ fun s ->
  lambda "t" (mkind term) @@ fun t ->
  (* Build the case expression. *)
  case (mkVar t) @@ fun i args ->
  if i = 0
  then
    (* Variable branch. *)
    ret @@ app (mkVar s) (mkVar @@ List.hd args)
  else
    (* Other branches. *)
    let args' =
      List.map2
        (substitute_arg (mkVar substitute) (mkconst up_subst) (mkVar s))
        (List.map mkVar args)
        s_.ctor_types.(i - 1)
    in
    ret @@ apps (mkctor (term, i + 1)) @@ Array.of_list args'

let build_scomp (term : Names.Ind.t) (subst : Names.Constant.t)
    (substitute : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "s1" (mkconst subst) @@ fun s1 ->
  lambda "s2" (mkconst subst) @@ fun s2 ->
  lambda "i" (mkind nat) @@ fun i ->
  ret @@ apps (mkconst substitute) [| mkVar s2; app (mkVar s1) (mkVar i) |]

(** After having defined terms, renaming, and substitution, we gather all newly defined
    constants in this record. *)
type operations =
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

(**************************************************************************************)
(** *** Build congruence lemmas. *)
(**************************************************************************************)

(** Build the congruence lemma for the non-variable constructor [idx] (starting at [0]).
*)
let build_congr_ctor (sign : signature) (ops : operations) (idx : int) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ops.term in
  (* Helper function to bind the arguments of the constructor. *)
  let rec with_vars (tys : arg_ty list) (k : (Names.Id.t * Names.Id.t) list -> 'a m) :
      'a m =
    match tys with
    | [] -> k []
    | ty :: tys ->
        prod "l" (arg_ty_constr ty term) @@ fun t ->
        prod "r" (arg_ty_constr ty term) @@ fun t' ->
        with_vars tys @@ fun ts -> k ((t, t') :: ts)
  in
  (* Bind the arguments of the constructor. *)
  with_vars sign.ctor_types.(idx) @@ fun ts ->
  (* Build the hypotheses. *)
  let hyps =
    List.map2
      (fun (t, t') ty -> apps (mkind eq) [| arg_ty_constr ty term; mkVar t; mkVar t' |])
      ts sign.ctor_types.(idx)
  in
  (* Build the conclusion. *)
  let* ctor = fresh_ctor (ops.term, idx + 2) in
  let left = apps ctor @@ Array.of_list @@ List.map mkVar @@ List.map fst ts in
  let right = apps ctor @@ Array.of_list @@ List.map mkVar @@ List.map snd ts in
  let concl = apps (mkind eq) [| term; left; right |] in
  (* Assemble everything. *)
  ret @@ arrows hyps concl

(** Build [forall r r' t t', r =₁ r' -> t = t' -> rename r t = rename r' t']. *)
let build_congr_rename (sign : signature) (ops : operations) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ops.term in
  prod "r" (mkconst ren) @@ fun r ->
  prod "r'" (mkconst ren) @@ fun r' ->
  prod "t" term @@ fun t ->
  prod "t'" term @@ fun t' ->
  let hyp_r = apps (mkconst point_eq) [| mkind nat; mkind nat; mkVar r; mkVar r' |] in
  let hyp_t = apps (mkind eq) [| term; mkVar t; mkVar t' |] in
  let concl =
    apps (mkind eq)
      [| term
       ; apps (mkconst ops.rename) [| mkVar r; mkVar t |]
       ; apps (mkconst ops.rename) [| mkVar r'; mkVar t' |]
      |]
  in
  ret @@ arrows [ hyp_r; hyp_t ] concl

(** Build [forall r r' s s', r =₁ r' -> s =₁ s' -> rscomp r s =₁ rscomp r' s']. *)
let build_congr_rscomp (sign : signature) (ops : operations) : EConstr.t m =
  let open EConstr in
  prod "r" (mkconst ren) @@ fun r ->
  prod "r'" (mkconst ren) @@ fun r' ->
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  let hyp_r = apps (mkconst point_eq) [| mkind nat; mkind nat; mkVar r; mkVar r' |] in
  let hyp_s =
    apps (mkconst point_eq) [| mkind nat; mkind ops.term; mkVar s; mkVar s' |]
  in
  let concl =
    apps (mkconst point_eq)
      [| mkind nat
       ; mkind ops.term
       ; apps (mkconst ops.rscomp) [| mkVar r; mkVar s |]
       ; apps (mkconst ops.rscomp) [| mkVar r'; mkVar s' |]
      |]
  in
  ret @@ arrows [ hyp_r; hyp_s ] concl

(** Build [forall s s' r r', s =₁ s' -> r =₁ r' -> srcomp s r =₁ srcomp s' r']. *)
let build_congr_srcomp (sign : signature) (ops : operations) : EConstr.t m =
  let open EConstr in
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  prod "r" (mkconst ren) @@ fun r ->
  prod "r'" (mkconst ren) @@ fun r' ->
  let hyp_s =
    apps (mkconst point_eq) [| mkind nat; mkind ops.term; mkVar s; mkVar s' |]
  in
  let hyp_r = apps (mkconst point_eq) [| mkind nat; mkind nat; mkVar r; mkVar r' |] in
  let concl =
    apps (mkconst point_eq)
      [| mkind nat
       ; mkind ops.term
       ; apps (mkconst ops.srcomp) [| mkVar s; mkVar r |]
       ; apps (mkconst ops.srcomp) [| mkVar s'; mkVar r' |]
      |]
  in
  ret @@ arrows [ hyp_s; hyp_r ] concl

(** Build [forall t t' s s', t = t' -> s =₁ s' -> scons t s =₁ scons t' s']. *)
let build_congr_scons (sign : signature) (ops : operations) : EConstr.t m =
  let open EConstr in
  prod "t" (mkind ops.term) @@ fun t ->
  prod "t'" (mkind ops.term) @@ fun t' ->
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  let hyp_t = apps (mkind eq) [| mkind ops.term; mkVar t; mkVar t' |] in
  let hyp_s =
    apps (mkconst point_eq) [| mkind nat; mkind ops.term; mkVar s; mkVar s' |]
  in
  let concl =
    apps (mkconst point_eq)
      [| mkind nat
       ; mkind ops.term
       ; apps (mkconst ops.scons) [| mkVar t; mkVar s |]
       ; apps (mkconst ops.scons) [| mkVar t'; mkVar s' |]
      |]
  in
  ret @@ arrows [ hyp_t; hyp_s ] concl

(** Build [forall s s', s =₁ s' -> up_subst s =₁ up_subst s']. *)
let build_congr_up_subst (sign : signature) (ops : operations) : EConstr.t m =
  let open EConstr in
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  let hyp = apps (mkconst point_eq) [| mkind nat; mkind ops.term; mkVar s; mkVar s' |] in
  let concl =
    apps (mkconst point_eq)
      [| mkind nat
       ; mkind ops.term
       ; app (mkconst ops.up_subst) (mkVar s)
       ; app (mkconst ops.up_subst) (mkVar s')
      |]
  in
  ret @@ arrow hyp concl

(** Build [forall s s' t t', s =₁ s' -> t = t' -> substitute s t = substitute s' t']. *)
let build_congr_substitute (sign : signature) (ops : operations) : EConstr.t m =
  let open EConstr in
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  prod "t" (mkind ops.term) @@ fun t ->
  prod "t'" (mkind ops.term) @@ fun t' ->
  let hyp_s =
    apps (mkconst point_eq) [| mkind nat; mkind ops.term; mkVar s; mkVar s' |]
  in
  let hyp_t = apps (mkind eq) [| mkind ops.term; mkVar t; mkVar t' |] in
  let concl =
    apps (mkind eq)
      [| mkind ops.term
       ; apps (mkconst ops.substitute) [| mkVar s; mkVar t |]
       ; apps (mkconst ops.substitute) [| mkVar s'; mkVar t' |]
      |]
  in
  ret @@ arrows [ hyp_s; hyp_t ] concl

(** Build [forall s1 s1' s2 s2', s1 =₁ s1' -> s2 =₁ s2' -> scomp s1 s2 =₁ scomp s1' s2'].
*)
let build_congr_scomp (sign : signature) (ops : operations) : EConstr.t m =
  let open EConstr in
  prod "s1" (mkconst ops.subst) @@ fun s1 ->
  prod "s1'" (mkconst ops.subst) @@ fun s1' ->
  prod "s2" (mkconst ops.subst) @@ fun s2 ->
  prod "s2'" (mkconst ops.subst) @@ fun s2' ->
  let hyp_s1 =
    apps (mkconst point_eq) [| mkind nat; mkind ops.term; mkVar s1; mkVar s1' |]
  in
  let hyp_s2 =
    apps (mkconst point_eq) [| mkind nat; mkind ops.term; mkVar s2; mkVar s2' |]
  in
  let concl =
    apps (mkconst point_eq)
      [| mkind nat
       ; mkind ops.term
       ; apps (mkconst ops.scomp) [| mkVar s1; mkVar s2 |]
       ; apps (mkconst ops.scomp) [| mkVar s1'; mkVar s2' |]
      |]
  in
  ret @@ arrows [ hyp_s1; hyp_s2 ] concl

(**************************************************************************************)
(** *** Prove congruence lemmas. *)
(**************************************************************************************)

(** Prove the congruence lemma for the non-variable constructor [idx] (starting at [0]).
*)
let prove_congr_ctor (sign : signature) (ops : operations) (idx : int) :
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
let prove_congr_rename (sign : signature) (ops : operations)
    (congr_lemmas : Names.Constant.t list) : unit Proofview.tactic =
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
    let* _ =
      Tactics.apply @@ EConstr.UnsafeMonomorphic.mkConst @@ List.nth congr_lemmas (i - 1)
    in
    auto ~lemmas:[ mkconst congr_up_ren ] ()

(** Prove [forall r r' s s', r =₁ r' -> s =₁ s' -> rscomp r s =₁ rscomp r' s']. *)
let prove_congr_rscomp (sign : signature) (ops : operations) : unit Proofview.tactic =
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
let prove_congr_srcomp (sign : signature) (ops : operations)
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
let prove_congr_scons (sign : signature) (ops : operations) : unit Proofview.tactic =
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
let prove_congr_up_subst (sign : signature) (ops : operations)
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
let prove_congr_substitute (sign : signature) (ops : operations)
    (congr_up_subst : Names.Constant.t) (congr_lemmas : Names.Constant.t list) :
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
    let* _ =
      Tactics.apply @@ EConstr.UnsafeMonomorphic.mkConst @@ List.nth congr_lemmas (i - 1)
    in
    auto ~lemmas:[ mkconst congr_up_subst ] ()

(** Prove [forall s1 s1' s2 s2', s1 =₁ s1' -> s2 =₁ s2' -> scomp s1 s2 =₁ scomp s1' s2'].
*)
let prove_congr_scomp (sign : signature) (ops : operations)
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
(** *** Putting everything together. *)
(**************************************************************************************)

(** Helper function to declare a definition. *)
let def (name : string) ?(kind : Decls.definition_object_kind option)
    (mk_body : EConstr.t m) : Names.Constant.t =
  let kind = match kind with None -> Decls.Definition | Some k -> k in
  monad_run
    begin
      let* body = mk_body in
      let* _ = typecheck body in
      declare_def kind name body
    end

(** Helper function to prove a lemma using a tactic. *)
let lemma (name : string) (mk_stmt : EConstr.t m) (tac : unit Proofview.tactic) :
    Names.Constant.t =
  monad_run
    begin
      let* stmt = mk_stmt in
      let* _ = typecheck stmt in
      (*let* env = get_env in
      let* sigma = get_sigma in
      Log.printf "\nPROVING LEMMA:\n%s" (Log.show_econstr env sigma stmt);*)
      declare_theorem Decls.Lemma name stmt tac
    end

let main () =
  let s =
    { n_ctors = 2
    ; ctor_names = [| "App"; "Lam" |]
    ; ctor_types = [| [ AT_term; AT_term ]; [ AT_base (mkind string); AT_bind AT_term ] |]
    }
  in
  (* Define the term inductive. *)
  let term = monad_run @@ build_term s in
  (* Define renaming and substitution functions. *)
  let rename = def "rename" ~kind:Decls.Fixpoint @@ build_rename s term in
  let subst = def "subst" @@ build_subst term in
  let srcomp = def "srcomp" @@ build_srcomp term subst rename in
  let rscomp = def "rscomp" @@ build_rscomp term subst in
  let sid = def "sid" @@ build_sid term subst in
  let sshift = def "sshift" @@ build_sshift term subst in
  let scons = def "scons" @@ build_scons term subst in
  let up_subst = def "up_subst" @@ build_up_subst term subst scons srcomp in
  let substitute =
    def "substitute" ~kind:Decls.Fixpoint @@ build_substitute s term subst up_subst
  in
  let scomp = def "scomp" @@ build_scomp term subst substitute in
  let ops =
    { term
    ; rename
    ; subst
    ; srcomp
    ; rscomp
    ; sid
    ; sshift
    ; scons
    ; up_subst
    ; substitute
    ; scomp
    }
  in
  (* Prove congruence lemmas. *)
  let congr_ctors =
    List.init s.n_ctors @@ fun i ->
    let name = String.concat "_" [ "congr"; s.ctor_names.(i) ] in
    lemma name (build_congr_ctor s ops i) @@ prove_congr_ctor s ops i
  in
  let congr_rename =
    lemma "congr_rename" (build_congr_rename s ops)
    @@ prove_congr_rename s ops congr_ctors
  in
  let _congr_rscomp =
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
  let _congr_scomp =
    lemma "congr_scomp" (build_congr_scomp s ops)
    @@ prove_congr_scomp s ops congr_substitute
  in
  ()
