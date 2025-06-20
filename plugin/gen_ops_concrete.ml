open Prelude
open Signature
module C = Constants

let eval_cbn ?(whd = false) ?(red_flags = RedFlags.all) (t : EConstr.t) : EConstr.t m =
 fun env sigma ->
  if whd
  then (sigma, Cbn.whd_cbn red_flags env sigma t)
  else (sigma, Cbn.norm_cbn red_flags env sigma t)

module Make (P : sig
  val sign : signature
end) =
struct
  (**************************************************************************************)
  (** *** Build level zero operations (renaming, substitution). *)
  (**************************************************************************************)

  (** Given that [rename : ren -> term -> term], build a function [fn : ren -> ty -> ty]
      which maps renames arguments of type [ty]. *)
  let rec rename_func (rename : EConstr.t) (r : EConstr.t) (ty : arg_ty) : EConstr.t m =
    match ty with
    | AT_base _ ->
        let* ty = fresh_evar None in
        lambda "t" ty @@ fun t -> ret (EConstr.mkVar t)
    | AT_term -> ret @@ app rename r
    | AT_bind ty ->
        let r' = app (mkglob' C.up_ren) r in
        rename_func rename r' ty
    | AT_fctor (i, ty) ->
        let* fn = rename_func rename r ty in
        let map = app (mkglob' C.NF.map) (mkglob P.sign.functors.(i)) in
        apps_ev map 3 [| fn |]

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
      let* args' =
        List.monad_map2
          (fun arg ty ->
            let* fn = rename_func (mkVar rename) (mkVar r) ty in
            ret @@ app fn arg)
          (List.map mkVar args)
          P.sign.ctor_types.(i - 1)
      in
      let t' = apps (mkctor (term, i + 1)) @@ Array.of_list args' in
      (* Typecheck to solve evars and typeclass instances. *)
      let* _ = typecheck ~solve_tc:true t' (Some (mkind term)) in
      (* Use [cbn] to obtain a term that is nicer for the user and
         to make the guard checker happy. *)
      eval_cbn t'

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

  (** Given that [substitute : subst -> term -> term], build a function
      [fn : subst -> ty -> ty] which substitutes in arguments of type [ty]. *)
  let rec substitute_func (substitute : EConstr.t) (up_subst : EConstr.t) (s : EConstr.t)
      (ty : arg_ty) : EConstr.t m =
    match ty with
    | AT_base _ ->
        let* ty = fresh_evar None in
        lambda "t" ty @@ fun t -> ret (EConstr.mkVar t)
    | AT_term -> ret @@ apps substitute [| s |]
    | AT_bind ty -> substitute_func substitute up_subst (app up_subst s) ty
    | AT_fctor (i, ty) ->
        let* fn = substitute_func substitute up_subst s ty in
        let map = app (mkglob' C.NF.map) (mkglob P.sign.functors.(i)) in
        apps_ev map 3 [| fn |]

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
      let* args' =
        List.monad_map2
          (fun arg ty ->
            let* fn =
              substitute_func (mkVar substitute) (mkconst up_subst) (mkVar s) ty
            in
            ret @@ app fn arg)
          (List.map mkVar args)
          P.sign.ctor_types.(i - 1)
      in
      let t' = apps (mkctor (term, i + 1)) @@ Array.of_list args' in
      (* Typecheck to solve evars and typeclass instances. *)
      let* _ = typecheck ~solve_tc:true t' (Some (mkind term)) in
      (* Use [cbn] to obtain a term that is nicer for the user and
         to make the guard checker happy. *)
      eval_cbn t'

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

(** Generate the renaming and substitution functions. *)
let generate (sign : signature) (term : Names.Ind.t) : ops_concrete =
  let module M = Make (struct
    let sign = sign
  end) in
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
