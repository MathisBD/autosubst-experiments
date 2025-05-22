open Prelude
open Signature
module C = Constants

module Make (P : sig
  val sign : signature
end) =
struct
  (**************************************************************************************)
  (** *** Build the term inductive and related operations (renaming, substitution). *)
  (**************************************************************************************)

  let build_term () : Names.Ind.t m =
    (* Constructor names and types. We add an extra constructor for variables. *)
    let ctor_names = "Var" :: Array.to_list P.sign.ctor_names in
    let ctor_types =
      (fun ind -> ret @@ arrow (mkglob' C.nat) (EConstr.mkVar ind))
      :: Array.to_list
           (Array.map
              (fun ty ind -> ret @@ ctor_ty_constr P.sign ty (EConstr.mkVar ind))
              P.sign.ctor_types)
    in
    (* Declare the inductive. *)
    declare_ind "term" EConstr.mkSet ctor_names ctor_types

  let rec rename_arg (rename : EConstr.t) (r : EConstr.t) (arg : EConstr.t) (ty : arg_ty)
      : EConstr.t =
    match ty with
    | AT_base _ -> arg
    | AT_term -> apps rename [| r; arg |]
    | AT_bind ty ->
        let r' = app (mkglob' C.up_ren) r in
        rename_arg rename r' arg ty

  (** Build [rename : ren -> term -> term]. *)
  let build_rename (term : Names.Ind.t) : EConstr.t m =
    let open EConstr in
    (* Bind the input parameters. *)
    fix "rename" 1 (arrows [ mkglob' C.ren; mkind term ] (mkind term)) @@ fun rename ->
    lambda "r" (mkglob' C.ren) @@ fun r ->
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
          P.sign.ctor_types.(i - 1)
      in
      ret @@ apps (mkctor (term, i + 1)) @@ Array.of_list args'

  (** Build [subst : Type := nat -> term]. *)
  let build_subst (term : Names.Ind.t) : EConstr.t m =
    ret @@ arrow (mkglob' C.nat) (mkind term)

  (** Build [srcomp : subst -> ren -> subst]. *)
  let build_srcomp (ind : Names.Ind.t) (subst : Names.Constant.t)
      (rename : Names.Constant.t) : EConstr.t m =
    let open EConstr in
    lambda "s" (mkconst subst) @@ fun s ->
    lambda "r" (mkglob' C.ren) @@ fun r ->
    lambda "i" (mkglob' C.nat) @@ fun i ->
    ret @@ apps (mkconst rename) [| mkVar r; app (mkVar s) (mkVar i) |]

  (** Build [rscomp : ren -> subst -> subst]. *)
  let build_rscomp (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
    let open EConstr in
    lambda "r" (mkglob' C.ren) @@ fun r ->
    lambda "s" (mkconst subst) @@ fun s ->
    lambda "i" (mkglob' C.nat) @@ fun i -> ret @@ app (mkVar s) @@ app (mkVar r) (mkVar i)

  (** Build [sid : subst]. *)
  let build_sid (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
    let open EConstr in
    lambda "i" (mkglob' C.nat) @@ fun i -> ret @@ app (mkctor (term, 1)) (mkVar i)

  (** Build [sshift : subst]. *)
  let build_sshift (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
    let open EConstr in
    lambda "i" (mkglob' C.nat) @@ fun i ->
    ret @@ app (mkctor (term, 1)) @@ app (mkglob' C.succ) (mkVar i)

  (** Build [scons : term -> subst -> subst]. *)
  let build_scons (term : Names.Ind.t) (subst : Names.Constant.t) : EConstr.t m =
    let open EConstr in
    lambda "t" (mkind term) @@ fun t ->
    lambda "s" (mkconst subst) @@ fun s ->
    lambda "i" (mkglob' C.nat) @@ fun i ->
    case (mkVar i) @@ fun idx args ->
    if idx = 0 then ret (mkVar t) else ret @@ app (mkVar s) (mkVar @@ List.hd args)

  (** Build [up_subst : subst -> subst]. *)
  let build_up_subst (term : Names.Ind.t) (subst : Names.Constant.t)
      (scons : Names.Constant.t) (srcomp : Names.Constant.t) : EConstr.t m =
    let open EConstr in
    lambda "s" (mkconst subst) @@ fun s ->
    ret
    @@ apps (mkconst scons)
         [| app (mkctor (term, 1)) (mkglob' C.zero)
          ; apps (mkconst srcomp) [| mkVar s; mkglob' C.rshift |]
         |]

  let rec substitute_arg (substitute : EConstr.t) (up_subst : EConstr.t) (s : EConstr.t)
      (arg : EConstr.t) (ty : arg_ty) : EConstr.t =
    match ty with
    | AT_base _ -> arg
    | AT_term -> apps substitute [| s; arg |]
    | AT_bind ty -> substitute_arg substitute up_subst (app up_subst s) arg ty

  (** Build [substitute : susbt -> term -> term]. *)
  let build_substitute (term : Names.Ind.t) (subst : Names.Constant.t)
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
          P.sign.ctor_types.(i - 1)
      in
      ret @@ apps (mkctor (term, i + 1)) @@ Array.of_list args'

  (** Build [scomp : subst -> subst -> subst]. *)
  let build_scomp (term : Names.Ind.t) (subst : Names.Constant.t)
      (substitute : Names.Constant.t) : EConstr.t m =
    let open EConstr in
    lambda "s1" (mkconst subst) @@ fun s1 ->
    lambda "s2" (mkconst subst) @@ fun s2 ->
    lambda "i" (mkglob' C.nat) @@ fun i ->
    ret @@ apps (mkconst substitute) [| mkVar s2; app (mkVar s1) (mkVar i) |]
end

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Generate the term inductive, along with renaming and substitution functions. *)
let generate (s : signature) : ops_zero =
  let module M = Make (struct
    let sign = s
  end) in
  let term = monad_run @@ M.build_term () in
  let rename = def "rename" ~kind:Decls.Fixpoint @@ M.build_rename term in
  let subst = def "subst" @@ M.build_subst term in
  let srcomp = def "srcomp" @@ M.build_srcomp term subst rename in
  let rscomp = def "rscomp" @@ M.build_rscomp term subst in
  let sid = def "sid" @@ M.build_sid term subst in
  let sshift = def "sshift" @@ M.build_sshift term subst in
  let scons = def "scons" @@ M.build_scons term subst in
  let up_subst = def "up_subst" @@ M.build_up_subst term subst scons srcomp in
  let substitute =
    def "substitute" ~kind:Decls.Fixpoint @@ M.build_substitute term subst up_subst
  in
  let scomp = def "scomp" @@ M.build_scomp term subst substitute in
  { term; rename; subst; srcomp; rscomp; sid; sshift; scons; up_subst; substitute; scomp }
