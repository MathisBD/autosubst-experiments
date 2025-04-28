open Monad
open Locally_nameless
open Custom_tactics

(**************************************************************************************)
(** *** Rocq constants we need to access from OCaml. *)
(**************************************************************************************)

let eq : EConstr.t =
  EConstr.UnsafeMonomorphic.mkInd
    (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Logic" ] "eq", 0)

let point_eq : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConst @@ Names.Constant.make1
  @@ mk_kername [ "Prototype"; "Prelude" ] "point_eq"

let nat : EConstr.t =
  EConstr.UnsafeMonomorphic.mkInd
    (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Datatypes" ] "nat", 0)

let nat_zero : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConstruct
    ((Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Datatypes" ] "nat", 0), 1)

let nat_succ : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConstruct
    ((Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Datatypes" ] "nat", 0), 2)

let string : EConstr.t =
  EConstr.UnsafeMonomorphic.mkInd
    (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Strings"; "String" ] "string", 0)

let ren : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConst @@ Names.Constant.make1
  @@ mk_kername [ "Prototype"; "Prelude" ] "ren"

let rshift : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConst @@ Names.Constant.make1
  @@ mk_kername [ "Prototype"; "Prelude" ] "rshift"

let up_ren : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConst @@ Names.Constant.make1
  @@ mk_kername [ "Prototype"; "Prelude" ] "up_ren"

let congr_up_ren : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConst @@ Names.Constant.make1
  @@ mk_kername [ "Prototype"; "Prelude" ] "congr_up_ren"

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
    (fun ind -> ret @@ arrow nat (EConstr.mkVar ind))
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
  | AT_bind ty -> rename_arg rename (app up_ren r) arg ty

let build_rename (s : signature) (ind : Names.Ind.t) : EConstr.t m =
  let open EConstr in
  (* Bind the input parameters. *)
  let* term = fresh_ind ind in
  fix "rename" 1 (arrows [ ren; term ] term) @@ fun rename ->
  lambda "r" ren @@ fun r ->
  lambda "t" term @@ fun t ->
  (* Build the case expression. *)
  case (mkVar t) @@ fun i args ->
  let* ctor = fresh_ctor (ind, i + 1) in
  if i = 0
  then
    (* Variable branch. *)
    ret @@ app ctor @@ app (mkVar r) (mkVar @@ List.hd args)
  else
    (* Other branches. *)
    let args' =
      List.map2
        (rename_arg (mkVar rename) (mkVar r))
        (List.map mkVar args)
        s.ctor_types.(i - 1)
    in
    ret @@ apps ctor @@ Array.of_list args'

let build_subst (ind : Names.Ind.t) : EConstr.t m =
  let* term = fresh_ind ind in
  ret (arrow nat term)

let build_srcomp (ind : Names.Ind.t) (subst : Names.Constant.t)
    (rename : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ind in
  let* subst = fresh_const subst in
  let* rename = fresh_const rename in
  lambda "s" subst @@ fun s ->
  lambda "r" ren @@ fun r ->
  lambda "i" nat @@ fun i -> ret @@ apps rename [| mkVar r; app (mkVar s) (mkVar i) |]

let build_rscomp (ind : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ind in
  let* subst = fresh_const subst in
  lambda "r" ren @@ fun r ->
  lambda "s" subst @@ fun s ->
  lambda "i" nat @@ fun i -> ret @@ app (mkVar s) @@ app (mkVar r) (mkVar i)

let build_sid (ind : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ind in
  let* subst = fresh_const subst in
  lambda "i" nat @@ fun i ->
  let* var_ctor = fresh_ctor (ind, 1) in
  ret @@ app var_ctor (mkVar i)

let build_sshift (ind : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ind in
  let* subst = fresh_const subst in
  lambda "i" nat @@ fun i ->
  let* var_ctor = fresh_ctor (ind, 1) in
  ret @@ app var_ctor @@ app nat_succ (mkVar i)

let build_scons (ind : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ind in
  let* subst = fresh_const subst in
  lambda "t" term @@ fun t ->
  lambda "s" subst @@ fun s ->
  lambda "i" nat @@ fun i ->
  case (mkVar i) @@ fun idx args ->
  if idx = 0 then ret (mkVar t) else ret @@ app (mkVar s) (mkVar @@ List.hd args)

let build_up_subst (ind : Names.Ind.t) (subst : Names.Constant.t)
    (scons : Names.Constant.t) (srcomp : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ind in
  let* subst = fresh_const subst in
  let* scons = fresh_const scons in
  let* srcomp = fresh_const srcomp in
  lambda "s" subst @@ fun s ->
  let* var_ctor = fresh_ctor (ind, 1) in
  ret @@ apps scons [| app var_ctor nat_zero; apps srcomp [| mkVar s; rshift |] |]

let rec substitute_arg (substitute : EConstr.t) (up_subst : EConstr.t) (s : EConstr.t)
    (arg : EConstr.t) (ty : arg_ty) : EConstr.t =
  match ty with
  | AT_base _ -> arg
  | AT_term -> apps substitute [| s; arg |]
  | AT_bind ty -> substitute_arg substitute up_subst (app up_subst s) arg ty

let build_substitute (s_ : signature) (ind : Names.Ind.t) (subst : Names.Constant.t)
    (up_subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ind in
  let* subst = fresh_const subst in
  let* up_subst = fresh_const up_subst in
  fix "substitute" 1 (arrows [ subst; term ] term) @@ fun substitute ->
  lambda "s" subst @@ fun s ->
  lambda "t" term @@ fun t ->
  (* Build the case expression. *)
  case (mkVar t) @@ fun i args ->
  let* ctor = fresh_ctor (ind, i + 1) in
  if i = 0
  then
    (* Variable branch. *)
    ret @@ app (mkVar s) (mkVar @@ List.hd args)
  else
    (* Other branches. *)
    let args' =
      List.map2
        (substitute_arg (mkVar substitute) up_subst (mkVar s))
        (List.map mkVar args)
        s_.ctor_types.(i - 1)
    in
    ret @@ apps ctor @@ Array.of_list args'

let build_scomp (ind : Names.Ind.t) (subst : Names.Constant.t)
    (substitute : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ind in
  let* subst = fresh_const subst in
  let* substitute = fresh_const substitute in
  lambda "s1" subst @@ fun s1 ->
  lambda "s2" subst @@ fun s2 ->
  lambda "i" nat @@ fun i ->
  ret @@ apps substitute [| mkVar s2; app (mkVar s1) (mkVar i) |]

(** After having defined terms, renaming, and substitution, we gather the names of all
    newly defined constants in this record. *)
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
(** *** Prove congruence lemmas. *)
(**************************************************************************************)

let stmt_congr_ctor (s : signature) (ops : operations) (idx : int) : EConstr.t m =
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
      (fun (t, t') ty -> apps eq [| arg_ty_constr ty term; mkVar t; mkVar t' |])
      ts s.ctor_types.(idx)
  in
  (* Build the conclusion. *)
  let* ctor = fresh_ctor (ops.term, idx + 2) in
  let left = apps ctor @@ Array.of_list @@ List.map mkVar @@ List.map fst ts in
  let right = apps ctor @@ Array.of_list @@ List.map mkVar @@ List.map snd ts in
  let concl = apps eq [| term; left; right |] in
  (* Assemble everything. *)
  ret @@ arrows hyps concl

let tac_congr_ctor (s : signature) (ops : operations) (idx : int) : unit Proofview.tactic
    =
  let open PVMonad in
  let arg_tys = s.ctor_types.(idx) in
  (* Introduce the constructor arguments with fresh names. *)
  let* _ =
    Tacticals.tclDO (2 * List.length arg_tys) @@ Proofview.tclIGNORE @@ intro_fresh "t"
  in
  (* Introduce each hypothesis and rewrite with it from left to right. *)
  let* _ = Tacticals.tclDO (List.length arg_tys) @@ intro_rewrite true in
  (* Close with reflexivity. *)
  Tactics.reflexivity

let stmt_congr_rename (s : signature) (ops : operations) : EConstr.t m =
  let open EConstr in
  let* term = fresh_ind ops.term in
  let* rename = fresh_const ops.rename in
  prod "t" term @@ fun t ->
  prod "t'" term @@ fun t' ->
  prod "r" ren @@ fun r ->
  prod "r'" ren @@ fun r' ->
  let hyp_t = apps eq [| term; mkVar t; mkVar t' |] in
  let hyp_r = apps point_eq [| nat; nat; mkVar r; mkVar r' |] in
  let concl =
    apps eq
      [| term; apps rename [| mkVar r; mkVar t |]; apps rename [| mkVar r'; mkVar t' |] |]
  in
  ret @@ arrows [ hyp_t; hyp_r ] concl

let tac_congr_rename (s : signature) (ops : operations)
    (congr_lemmas : Names.Constant.t list) : unit Proofview.tactic =
  let open PVMonad in
  (* Introduce the variables. *)
  let* t = intro_fresh "t" in
  let* _ = intro_fresh "t'" in
  let* r = intro_fresh "r" in
  let* r' = intro_fresh "r'" in
  (* Rewrite with the first hypothesis. *)
  let* _ = intro_rewrite false in
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
    auto ~lemmas:[ congr_up_ren ] ()

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
    ; ctor_types = [| [ AT_term; AT_term ]; [ AT_base string; AT_bind AT_term ] |]
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
  let _congr_rename =
    lemma "congr_rename" (stmt_congr_rename s ops) @@ tac_congr_rename s ops congr_ctors
  in
  ()
