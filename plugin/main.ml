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
    - [ctor_names] contains the name of each constructor.
    - [ctor_sig] contains the argument types of each constructor. *)
type signature = { ctor_names : string array; ctor_types : arg_ty list array }

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

let build_term (s : signature) : Names.Ind.t m =
  (* Constructor names and types. We add an extra constructor for variables. *)
  let ctor_names = "Var" :: Array.to_list s.ctor_names in
  let ctor_types =
    (fun ind -> ret @@ arrow (mkind nat) (EConstr.mkVar ind))
    :: Array.to_list
         (Array.map
            (fun ty ind -> ret @@ ctor_ty_constr ty (EConstr.mkVar ind))
            s.ctor_types)
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

let build_rename (s : signature) (term : Names.Ind.t) : EConstr.t m =
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
        s.ctor_types.(i - 1)
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
(** *** Congruence lemmas. *)
(**************************************************************************************)

(** Build the congruence lemma for the non-variable constructor [idx] (starting at [0]).
*)
let build_congr_ctor (s : signature) (ops : operations) (idx : int) : EConstr.t m =
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
  with_vars s.ctor_types.(idx) @@ fun ts ->
  (* Build the hypotheses. *)
  let hyps =
    List.map2
      (fun (t, t') ty -> apps (mkind eq) [| arg_ty_constr ty term; mkVar t; mkVar t' |])
      ts s.ctor_types.(idx)
  in
  (* Build the conclusion. *)
  let* ctor = fresh_ctor (ops.term, idx + 2) in
  let left = apps ctor @@ Array.of_list @@ List.map mkVar @@ List.map fst ts in
  let right = apps ctor @@ Array.of_list @@ List.map mkVar @@ List.map snd ts in
  let concl = apps (mkind eq) [| term; left; right |] in
  (* Assemble everything. *)
  ret @@ arrows hyps concl

(** Prove the congruence lemma for the non-variable constructor [idx] (starting at [0]).
*)
let prove_congr_ctor (s : signature) (ops : operations) (idx : int) :
    unit Proofview.tactic =
  let open PVMonad in
  let arg_tys = s.ctor_types.(idx) in
  (* Introduce the constructor arguments. *)
  let* _ = intro_n (2 * List.length arg_tys) in
  (* Introduce each hypothesis and rewrite with it from left to right. *)
  let* _ = Tacticals.tclDO (List.length arg_tys) @@ intro_rewrite ~dir:true in
  (* Close with reflexivity. *)
  Tactics.reflexivity

(** Build [forall t t' r r', t = t' -> r =₁ r' -> rename r t = rename r' t']. *)
let build_congr_rename (s : signature) (ops : operations) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ops.term in
  prod "t" term @@ fun t ->
  prod "t'" term @@ fun t' ->
  prod "r" (mkconst ren) @@ fun r ->
  prod "r'" (mkconst ren) @@ fun r' ->
  let hyp_t = apps (mkind eq) [| term; mkVar t; mkVar t' |] in
  let hyp_r = apps (mkconst point_eq) [| mkind nat; mkind nat; mkVar r; mkVar r' |] in
  let concl =
    apps (mkind eq)
      [| term
       ; apps (mkconst ops.rename) [| mkVar r; mkVar t |]
       ; apps (mkconst ops.rename) [| mkVar r'; mkVar t' |]
      |]
  in
  ret @@ arrows [ hyp_t; hyp_r ] concl

(** Prove [forall t t' r r', t = t' -> r =₁ r' -> rename r t = rename r' t']. *)
let prove_congr_rename (s : signature) (ops : operations)
    (congr_lemmas : Names.Constant.t list) : unit Proofview.tactic =
  let open PVMonad in
  (* Introduce the variables. *)
  let* t = intro_fresh "t" in
  let* _ = intro_fresh "t'" in
  let* r = intro_fresh "r" in
  let* r' = intro_fresh "r'" in
  (* Rewrite with the first hypothesis. *)
  let* _ = intro_rewrite ~dir:false in
  let* _ = Generalize.revert [ r; r' ] in
  (* Induction on [t]. *)
  let intro_patt = CAst.make @@ Tactypes.IntroOrPattern [ []; []; [] ] in
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

(** Build [forall r r' s s', r =₁ r' -> s =₁ s' -> rscomp r s =₁ rscomp r' s']. *)
let build_congr_rscomp (s : signature) (ops : operations) : EConstr.t m =
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

(** Prove [forall r r' s s', r =₁ r' -> s =₁ s' -> rscomp r s =₁ rscomp r' s']. *)
let prove_congr_rscomp (s : signature) (ops : operations) : unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_n 4 in
  let* h1 = intro_fresh "H" in
  let* h2 = intro_fresh "H" in
  let* _ = intro_fresh "i" in
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops.rscomp) in
  let* _ = rewrite ~dir:true (Names.GlobRef.VarRef h1) in
  let* _ = rewrite ~dir:true (Names.GlobRef.VarRef h2) in
  Tactics.reflexivity

(** Build [forall s s' r r', s =₁ s' -> r =₁ r' -> srcomp s r =₁ srcomp s' r']. *)
let build_congr_srcomp (s : signature) (ops : operations) : EConstr.t m =
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

(** Prove [forall s s' r r', s =₁ s' -> r =₁ r' -> srcomp s r =₁ srcomp s' r']. *)
let prove_congr_srcomp (s : signature) (ops : operations)
    (congr_rename : Names.Constant.t) : unit Proofview.tactic =
  let open PVMonad in
  let* _ = intro_n 4 in
  let* h1 = intro_fresh "H" in
  let* h2 = intro_fresh "H" in
  let* _ = intro_fresh "i" in
  let* _ = Tactics.unfold_constr (Names.GlobRef.ConstRef ops.srcomp) in
  let* _ = Tactics.apply (mkconst congr_rename) in
  auto ()

(** Build [forall t t' s s', t = t' -> s =₁ s' -> scons t s =₁ scons t' s']. *)
let buildcongr_scons (s : signature) (ops : operations) : EConstr.t m =
  let open EConstr in
  prod "t" (mkind ops.term) @@ fun t ->
  prod "t'" (mkind ops.term) @@ fun t' ->
  prod "s" (mkconst ops.subst) @@ fun s ->
  prod "s'" (mkconst ops.subst) @@ fun s' ->
  let hyp_t = apps (mkind eq) [| mkind ops.term; mkVar t; mkVar t' |] in
  let hyp_s =
    apps (mkconst point_eq) [| mkind nat; mkconst ops.subst; mkVar s; mkVar s' |]
  in
  let concl =
    apps (mkconst point_eq)
      [| mkind nat
       ; mkconst ops.subst
       ; apps (mkconst ops.scons) [| mkVar t; mkVar s |]
       ; apps (mkconst ops.scons) [| mkVar t'; mkVar s' |]
      |]
  in
  ret @@ arrows [ hyp_t; hyp_s ] concl

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
      let* env = get_env in
      let* sigma = get_sigma in
      Log.printf "\nPROVING LEMMA:\n%s" (Log.show_econstr env sigma stmt);
      declare_theorem Decls.Lemma name stmt tac
    end

let main () =
  let s =
    { ctor_names = [| "App"; "Lam" |]
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
    List.init (Array.length s.ctor_types) @@ fun i ->
    let name = String.concat "_" [ "congr"; s.ctor_names.(i) ] in
    lemma name (stmt_congr_ctor s ops i) @@ tac_congr_ctor s ops i
  in
  let congr_rename =
    lemma "congr_rename" (stmt_congr_rename s ops) @@ tac_congr_rename s ops congr_ctors
  in
  let _congr_rscomp =
    lemma "congr_rscomp" (stmt_congr_rscomp s ops) @@ proof_congr_rscomp s ops
  in
  let _congr_rscomp =
    lemma "congr_srcomp" (stmt_congr_srcomp s ops)
    @@ proof_congr_srcomp s ops congr_rename
  in
  ()
