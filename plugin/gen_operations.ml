open Prelude

(**************************************************************************************)
(** *** Build the term inductive and related operations (renaming, substitution). *)
(**************************************************************************************)

let build_term (sign : signature) : Names.Ind.t m =
  (* Constructor names and types. We add an extra constructor for variables. *)
  let ctor_names = "Var" :: Array.to_list sign.ctor_names in
  let ctor_types =
    (fun ind -> ret @@ arrow (Lazy.force Consts.nat) (EConstr.mkVar ind))
    :: Array.to_list
         (Array.map
            (fun ty ind -> ret @@ ctor_ty_constr sign ty (EConstr.mkVar ind))
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
      let r' = app (Lazy.force Consts.up_ren) r in
      rename_arg rename r' arg ty

(** Build [rename : ren -> term -> term]. *)
let build_rename (sign : signature) (term : Names.Ind.t) : EConstr.t m =
  let open EConstr in
  (* Bind the input parameters. *)
  fix "rename" 1 (arrows [ Lazy.force Consts.ren; mkind term ] (mkind term))
  @@ fun rename ->
  lambda "r" (Lazy.force Consts.ren) @@ fun r ->
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

(** Build [subst : Type := nat -> term]. *)
let build_subst (term : Names.Ind.t) : EConstr.t m =
  ret @@ arrow (Lazy.force Consts.nat) (mkind term)

(** Build [srcomp : subst -> ren -> subst]. *)
let build_srcomp (ind : Names.Ind.t) (subst : Names.Constant.t)
    (rename : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "s" (mkconst subst) @@ fun s ->
  lambda "r" (Lazy.force Consts.ren) @@ fun r ->
  lambda "i" (Lazy.force Consts.nat) @@ fun i ->
  ret @@ apps (mkconst rename) [| mkVar r; app (mkVar s) (mkVar i) |]

(** Build [rscomp : ren -> subst -> subst]. *)
let build_rscomp (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "r" (Lazy.force Consts.ren) @@ fun r ->
  lambda "s" (mkconst subst) @@ fun s ->
  lambda "i" (Lazy.force Consts.nat) @@ fun i ->
  ret @@ app (mkVar s) @@ app (mkVar r) (mkVar i)

(** Build [sid : subst]. *)
let build_sid (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "i" (Lazy.force Consts.nat) @@ fun i -> ret @@ app (mkctor (term, 1)) (mkVar i)

(** Build [sshift : subst]. *)
let build_sshift (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "i" (Lazy.force Consts.nat) @@ fun i ->
  ret @@ app (mkctor (term, 1)) @@ app (Lazy.force Consts.succ) (mkVar i)

(** Build [scons : term -> subst -> subst]. *)
let build_scons (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "t" (mkind term) @@ fun t ->
  lambda "s" (mkconst subst) @@ fun s ->
  lambda "i" (Lazy.force Consts.nat) @@ fun i ->
  case (mkVar i) @@ fun idx args ->
  if idx = 0 then ret (mkVar t) else ret @@ app (mkVar s) (mkVar @@ List.hd args)

(** Build [up_subst : subst -> subst]. *)
let build_up_subst (term : Names.Ind.t) (subst : Names.Constant.t)
    (scons : Names.Constant.t) (srcomp : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "s" (mkconst subst) @@ fun s ->
  ret
  @@ apps (mkconst scons)
       [| app (mkctor (term, 1)) (Lazy.force Consts.zero)
        ; apps (mkconst srcomp) [| mkVar s; Lazy.force Consts.rshift |]
       |]

let rec substitute_arg (substitute : EConstr.t) (up_subst : EConstr.t) (s : EConstr.t)
    (arg : EConstr.t) (ty : arg_ty) : EConstr.t =
  match ty with
  | AT_base _ -> arg
  | AT_term -> apps substitute [| s; arg |]
  | AT_bind ty -> substitute_arg substitute up_subst (app up_subst s) arg ty

(** Build [substitute : susbt -> term -> term]. *)
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

(** Build [scomp : subst -> subst -> subst]. *)
let build_scomp (term : Names.Ind.t) (subst : Names.Constant.t)
    (substitute : Names.Constant.t) : EConstr.t m =
  let open EConstr in
  lambda "s1" (mkconst subst) @@ fun s1 ->
  lambda "s2" (mkconst subst) @@ fun s2 ->
  lambda "i" (Lazy.force Consts.nat) @@ fun i ->
  ret @@ apps (mkconst substitute) [| mkVar s2; app (mkVar s1) (mkVar i) |]

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Generate the term inductive, along with renaming and substitution functions. *)
let generate (s : signature) : ops_zero =
  let term = monad_run @@ build_term s in
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
  { term; rename; subst; srcomp; rscomp; sid; sshift; scons; up_subst; substitute; scomp }
