open Monad
open Locally_nameless

(** Argument type. *)
type arg_ty = AT_base of EConstr.types | AT_term | AT_bind of arg_ty

(** An abstract signature:
    - [ctor_names] contains the name of each constructor.
    - [ctor_sig] contains the argument types of each constructor. *)
type signature = { ctor_names : string array; ctor_types : arg_ty list array }

(** Build the [EConstr.t] corresponding to an [arg_ty]. We use [ind] as a placeholder for
    the inductive type of terms. *)
let rec arg_ty_constr (ty : arg_ty) (ind : EConstr.t) : EConstr.t =
  match ty with AT_base b -> b | AT_term -> ind | AT_bind ty -> arg_ty_constr ty ind

(** Build the type of a constructor as a [EConstr.t]. We use [ind] as a placeholder for
    the inductive type of terms. *)
let ctor_ty_constr (tys : arg_ty list) (ind : EConstr.t) : EConstr.t =
  arrows (List.map (fun ty -> arg_ty_constr ty ind) tys) ind

(** Rocq inductive [nat]. *)
let nat : EConstr.t =
  EConstr.UnsafeMonomorphic.mkInd
    (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Datatypes" ] "nat", 0)

let nat_zero : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConstruct
    ((Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Datatypes" ] "nat", 0), 1)

let nat_succ : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConstruct
    ((Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Datatypes" ] "nat", 0), 2)

(** Rocq inductive [string]. *)
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

(** Helper function to declare definitions. *)
let def (name : string) ?(kind : Decls.definition_object_kind option)
    (mk_body : EConstr.t m) : Names.Constant.t =
  let kind = match kind with None -> Decls.Definition | Some k -> k in
  monad_run
    begin
      let* body = mk_body in
      let* _ = typecheck body in
      declare_def kind name body
    end

(** Helper function to prove lemmas. *)
let lemma (name : string) (mk_stmt : EConstr.t m) (tac : unit Proofview.tactic) :
    Names.Constant.t =
  monad_run
    (let* stmt = mk_stmt in
     declare_theorem Decls.Lemma name stmt tac)

let true_ : EConstr.t =
  EConstr.UnsafeMonomorphic.mkInd
    (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Logic" ] "True", 0)

let true_I : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConstruct
    ((Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Logic" ] "True", 0), 1)

let main () =
  let s =
    { ctor_names = [| "App"; "Lam" |]
    ; ctor_types = [| [ AT_term; AT_term ]; [ AT_base string; AT_bind AT_term ] |]
    }
  in
  let term = monad_run @@ build_term s in
  let rename = def "rename" ~kind:Decls.Fixpoint @@ build_rename s term in
  let subst = def "subst" @@ build_subst term in
  let srcomp = def "srcomp" @@ build_srcomp term subst rename in
  let _rscomp = def "rscomp" @@ build_rscomp term subst in
  let _sid = def "sid" @@ build_sid term subst in
  let _sshift = def "sshift" @@ build_sshift term subst in
  let scons = def "scons" @@ build_scons term subst in
  let up_subst = def "up_subst" @@ build_up_subst term subst scons srcomp in
  let substitute =
    def "substitute" ~kind:Decls.Fixpoint @@ build_substitute s term subst up_subst
  in
  let _ = lemma "test_lemma" (ret true_) @@ Tactics.exact_check true_I in
  let _scomp = def "scomp" @@ build_scomp term subst substitute in
  ()
