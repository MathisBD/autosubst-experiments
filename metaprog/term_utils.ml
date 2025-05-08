open Monad

(**************************************************************************************)
(** *** Typing. *)
(**************************************************************************************)

let pretype (t : Constrexpr.constr_expr) : EConstr.t m =
 fun env sigma ->
  let t = Constrintern.intern_constr env sigma t in
  let t, ustate = Pretyping.understand env sigma t in
  (Evd.merge_universe_context sigma ustate, t)

let typecheck (t : EConstr.t) : EConstr.types m =
 fun env sigma -> Typing.type_of env sigma t

let retype (t : EConstr.t) : EConstr.types m =
 fun env sigma -> (sigma, Retyping.get_type_of env sigma t)

(**************************************************************************************)
(** *** Building constants/inductives/constructors. *)
(**************************************************************************************)

let mk_qualid (dir : string list) (label : string) : Libnames.qualid =
  let dir = Names.DirPath.make @@ List.rev_map Names.Id.of_string_soft dir in
  let label = Names.Id.of_string_soft label in
  Libnames.make_qualid dir label

let mk_kername (dir : string list) (label : string) : Names.KerName.t =
  let dir =
    Names.ModPath.MPfile (Names.DirPath.make @@ List.rev_map Names.Id.of_string_soft dir)
  in
  let label = Names.Label.make label in
  Names.KerName.make dir label

let mkconst (name : Names.Constant.t) : EConstr.t = EConstr.UnsafeMonomorphic.mkConst name
let mkind (name : Names.Ind.t) : EConstr.t = EConstr.UnsafeMonomorphic.mkInd name

let mkctor (name : Names.Construct.t) : EConstr.t =
  EConstr.UnsafeMonomorphic.mkConstruct name

let fresh_ind (ind : Names.Ind.t) : EConstr.t m =
 fun env sigma ->
  let sigma, (_, uinst) = Evd.fresh_inductive_instance env sigma ind in
  (sigma, EConstr.mkIndU (ind, EConstr.EInstance.make uinst))

let fresh_ctor (ctor : Names.Construct.t) : EConstr.t m =
 fun env sigma ->
  let sigma, (_, uinst) = Evd.fresh_constructor_instance env sigma ctor in
  (sigma, EConstr.mkConstructU (ctor, EConstr.EInstance.make uinst))

let fresh_const (const : Names.Constant.t) : EConstr.t m =
 fun env sigma ->
  let sigma, (_, uinst) = Evd.fresh_constant_instance env sigma const in
  (sigma, EConstr.mkConstU (const, EConstr.EInstance.make uinst))

(**************************************************************************************)
(** *** Manipulating contexts. *)
(**************************************************************************************)

let vass (name : string) (ty : EConstr.t) : EConstr.rel_declaration =
  Context.Rel.Declaration.LocalAssum
    ( { binder_name = Name (Names.Id.of_string_soft name)
      ; binder_relevance = EConstr.ERelevance.relevant
      }
    , ty )

let vdef (name : string) (def : EConstr.t) (ty : EConstr.t) : EConstr.rel_declaration =
  Context.Rel.Declaration.LocalDef
    ( { binder_name = Name (Names.Id.of_string_soft name)
      ; binder_relevance = EConstr.ERelevance.relevant
      }
    , def
    , ty )

let fresh_ident (id : Names.Id.t) : Names.Id.t m =
  let* env = get_env in
  let idset = Environ.ids_of_named_context_val (Environ.named_context_val env) in
  ret @@ Namegen.next_ident_away id idset

let with_local_decl (decl : EConstr.rel_declaration) (k : Names.Id.t -> 'a m) : 'a m =
  let* id =
    fresh_ident
      (match Context.Rel.Declaration.get_name decl with
      | Name n -> n
      | Anonymous -> Names.Id.of_string "x")
  in
  let* sigma = get_sigma in
  let named_decl =
    match decl with
    | LocalAssum (_, ty) ->
        Context.Named.Declaration.LocalAssum
          ( { binder_name = id; binder_relevance = Sorts.Relevant }
          , EConstr.to_constr ~abort_on_undefined_evars:false sigma ty )
    | LocalDef (_, def, ty) ->
        Context.Named.Declaration.LocalDef
          ( { binder_name = id; binder_relevance = Sorts.Relevant }
          , EConstr.to_constr ~abort_on_undefined_evars:false sigma def
          , EConstr.to_constr ~abort_on_undefined_evars:false sigma ty )
  in
  with_env' (Environ.push_named named_decl) @@ k id

let with_local_ctx (ctx : EConstr.rel_context) (k : Names.Id.t list -> 'a m) : 'a m =
  (* We process declarations from outermost to innermost. *)
  let rec loop decls ids =
    match decls with
    | [] -> k (List.rev ids)
    | d :: decls ->
        let d_subst = EConstr.Vars.substl_decl (List.map EConstr.mkVar ids) d in
        with_local_decl d_subst @@ fun id -> loop decls (id :: ids)
  in
  loop (List.rev ctx) []

(**************************************************************************************)
(** *** Building terms. *)
(**************************************************************************************)

let fresh_type : EConstr.t m =
 fun env sigma ->
  let level = UnivGen.fresh_level () in
  let sigma = Evd.add_global_univ sigma level in
  (sigma, EConstr.mkType @@ Univ.Universe.make level)

let fresh_evar (ty : EConstr.t option) : EConstr.t m =
 fun env sigma ->
  match ty with
  | Some ty -> Evarutil.new_evar env sigma ty
  | None ->
      let sigma, t = fresh_type env sigma in
      let sigma, ty = Evarutil.new_evar env sigma t in
      Evarutil.new_evar env sigma ty

let app f x = EConstr.mkApp (f, [| x |])
let apps f xs = EConstr.mkApp (f, xs)

let apps_ev (f : EConstr.t) (n : int) (args : EConstr.t array) : EConstr.t m =
  let rec mk_evars n evars : EConstr.t list m =
    if n <= 0
    then ret evars
    else
      let* ev = fresh_evar None in
      mk_evars (n - 1) (ev :: evars)
  in
  let* evars = mk_evars n [] in
  ret @@ apps f @@ Array.concat [ Array.of_list evars; args ]

let arrow t1 t2 = EConstr.mkArrowR t1 (EConstr.Vars.lift 1 t2)
let rec arrows ts t = match ts with [] -> t | t1 :: ts -> arrow t1 (arrows ts t)

let lambda name ty mk_body =
  with_local_decl (vass name ty) @@ fun id ->
  let* body = mk_body id in
  let* sigma = get_sigma in
  ret
  @@ EConstr.mkNamedLambda sigma
       { binder_name = id; binder_relevance = EConstr.ERelevance.relevant }
       ty body

let prod name ty mk_body =
  with_local_decl (vass name ty) @@ fun id ->
  let* body = mk_body id in
  let* sigma = get_sigma in
  ret
  @@ EConstr.mkNamedProd sigma
       { binder_name = id; binder_relevance = EConstr.ERelevance.relevant }
       ty body

let let_in name def ty mk_body =
  with_local_decl (vdef name def ty) @@ fun id ->
  let* body = mk_body id in
  let* sigma = get_sigma in
  ret
  @@ EConstr.mkNamedLetIn sigma
       { binder_name = id; binder_relevance = EConstr.ERelevance.relevant }
       def ty body

let fix (name : string) (rec_arg_idx : int) (ty : EConstr.t)
    (mk_body : Names.Id.t -> EConstr.t m) : EConstr.t m =
  with_local_decl (vass name ty) @@ fun id ->
  let* body = mk_body id in
  let* sigma = get_sigma in
  ret
  @@ EConstr.mkFix
       ( ([| rec_arg_idx |], 0)
       , ( [| { binder_name = Name id; binder_relevance = EConstr.ERelevance.relevant } |]
         , [| ty |]
         , [| EConstr.Vars.subst_var sigma id body |] ) )

(** [lambda_vars vars body] builds the lambda abstraction [fun vars => body]. *)
let rec lambda_vars (vars : Names.Id.t list) (body : EConstr.t) : EConstr.t m =
  match vars with
  | [] -> ret body
  | v :: vars ->
      let* body = lambda_vars vars body in
      let* env = get_env in
      let* sigma = get_sigma in
      let v_decl = Environ.lookup_named v env in
      ret
      @@ EConstr.mkNamedLambda sigma
           { binder_name = v; binder_relevance = EConstr.ERelevance.relevant }
           (EConstr.of_constr @@ Context.Named.Declaration.get_type v_decl)
           body

(** Smashes [ctx] (i.e. inlines all letins in [ctx]). *)
let lambda_ctx (ctx : EConstr.rel_context) (mk_body : Names.Id.t list -> EConstr.t m) :
    EConstr.t m =
  with_local_ctx (EConstr.Vars.smash_rel_context ctx) @@ fun vars ->
  let* body = mk_body vars in
  lambda_vars vars body

(** [split_list n xs] splits [xs] into its [n] first elements, and the rest. Does _not_
    crash if [xs] has less than [n] elements. *)
let split_list (n : int) (xs : 'a list) : 'a list * 'a list =
  let rec loop n acc xs =
    if n <= 0
    then (List.rev acc, xs)
    else match xs with [] -> (List.rev acc, []) | x :: xs -> loop (n - 1) (x :: acc) xs
  in
  loop n [] xs

(** [dest_ind ty] destructs [ty] into an inductive applied to a (possibly empty) list of
    parameters and a (possibly empty) list of indices. *)
let dest_ind (ty : EConstr.t) :
    (Names.Ind.t * EConstr.EInstance.t * EConstr.t list * EConstr.t list) m =
 fun env sigma ->
  (* Weak-head reduce [ty] before decomposing it. 
     Maybe we don't need all reduction rules here, perhaps a subset is still enough 
     (and would be more efficient). *)
  let ind, args = Reductionops.whd_all_stack env sigma ty in
  let ind, uinst = EConstr.destInd sigma ind in
  let params, indices = split_list (Inductiveops.inductive_nparams env ind) args in
  (sigma, (ind, uinst, params, indices))

let case (scrutinee : EConstr.t)
    ?(return : (Names.Id.t list -> Names.Id.t -> EConstr.t m) option)
    (branches : int -> Names.Id.t list -> EConstr.t m) : EConstr.t m =
  (* Get the inductive we are matching over. *)
  let* ty = retype scrutinee in
  let* ind, uinst, params, indices = dest_ind ty in
  let ind_fam = Inductiveops.make_ind_family ((ind, uinst), params) in
  (* Get the return type. *)
  let* return =
    let* env = get_env in
    let indices_ctx = Inductiveops.get_arity env ind_fam in
    let* ind' = fresh_ind ind in
    lambda_ctx indices_ctx @@ fun indices ->
    let x_ty = apps ind' @@ Array.of_list @@ params @ List.map EConstr.mkVar indices in
    lambda "x" x_ty @@ fun x ->
    match return with Some return -> return indices x | None -> fresh_evar None
  in
  (* Build the branches. *)
  let* env = get_env in
  let ctor_summaries = Inductiveops.get_constructors env ind_fam in
  let* branch_list =
    List.monad_mapi
      begin
        fun i ctor -> lambda_ctx ctor.Inductiveops.cs_args @@ branches i
      end
    @@ Array.to_list ctor_summaries
  in
  (* Assemble everything. *)
  let* env = get_env in
  let* sigma = get_sigma in
  ret
  @@ Inductiveops.simple_make_case_or_project env sigma
       (Inductiveops.make_case_info env ind Constr.RegularStyle)
       (return, EConstr.ERelevance.relevant)
       Constr.NoInvert scrutinee (Array.of_list branch_list)

(**************************************************************************************)
(** *** Declaring definitions/indutives. *)
(**************************************************************************************)

let declare_def (kind : Decls.definition_object_kind) (name : string)
    ?(ty : EConstr.t option) (body : EConstr.t) : Names.Constant.t m =
  (* Typecheck to resolve evars. *)
  let* _ = typecheck body in
  let* _ = match ty with None -> ret () | Some ty -> monad_ignore @@ typecheck ty in
  (* Constant info. *)
  let info =
    Declare.Info.make ~kind:(Decls.IsDefinition kind)
      ~scope:(Locality.Global Locality.ImportDefaultBehavior) ()
  in
  (* Declare the constant. *)
  let* sigma = get_sigma in
  let ref =
    Declare.declare_definition ~info
      ~cinfo:(Declare.CInfo.make ~name:(Names.Id.of_string_soft name) ~typ:ty ())
      ~opaque:false ~body sigma
  in
  (* Check the returned global reference is indeed a constant name. *)
  match ref with
  | Names.GlobRef.ConstRef cname -> ret cname
  | _ -> failwith "declare_def: expected a [ConstRef]."

(* I had issues with the API in [Declare.Proof]: universe constraints introduced by [tac]
   where not handled properly. Instead I now use the API from [Proof]: this allows 
   me to get a hold on the final proof term, which I can manually typecheck to gather 
   universe constraints and solve any remaining evars using typing information. *)
let declare_theorem (kind : Decls.theorem_kind) (name : string) (stmt : EConstr.t)
    (tac : unit Proofview.tactic) : Names.Constant.t m =
  (* Typecheck to solve evars. *)
  let* _ = typecheck stmt in
  (* Build the proof. *)
  let* env = get_env in
  let* sigma = get_sigma in
  let proof =
    Proof.start
      ~name:(Names.Id.of_string_soft "term_ind'")
      ~poly:false sigma
      [ (env, stmt) ]
  in
  let proof, _, _ = Proof.run_tactic env tac proof in
  let body = List.hd @@ Proof.partial_proof proof in
  (* Typecheck to solve evars and get universe constraints. *)
  let* _ = typecheck body in
  (* Constant info. *)
  let info =
    Declare.Info.make ~kind:(Decls.IsProof kind)
      ~scope:(Locality.Global Locality.ImportDefaultBehavior) ()
  in
  let cinfo =
    Declare.CInfo.make ~name:(Names.Id.of_string_soft name) ~typ:(Some stmt) ()
  in
  (* Declare the lemma. *)
  let* sigma = get_sigma in
  let ref = Declare.declare_definition ~info ~cinfo ~opaque:true ~body sigma in
  (* Get the name of the declared lemma. *)
  match ref with
  | Names.GlobRef.ConstRef cname -> ret cname
  | _ -> failwith "declare_theorem: expected a [ConstRef]."

let declare_ind (name : string) (arity : EConstr.t) (ctor_names : string list)
    (ctor_types : (Names.Id.t -> EConstr.t m) list) : Names.Ind.t m =
  let open Entries in
  (* Typecheck to solve evars. *)
  let* _ = typecheck arity in
  (* Build the constructor types. *)
  let build_ctor_type (mk_ty : Names.Id.t -> EConstr.t m) : Constr.t m =
    with_local_decl (vass name arity) @@ fun ind ->
    let* ty = mk_ty ind in
    let* _ = typecheck ty in
    let* sigma = get_sigma in
    ret @@ EConstr.to_constr sigma @@ EConstr.Vars.subst_var sigma ind ty
  in
  let* ctor_types = List.monad_map build_ctor_type ctor_types in
  (* Declare the inductive. *)
  let ind =
    { mind_entry_typename = Names.Id.of_string_soft name
    ; mind_entry_arity = EConstr.to_constr Evd.empty arity
    ; mind_entry_consnames = List.map Names.Id.of_string_soft ctor_names
    ; mind_entry_lc = ctor_types
    }
  in
  let mind =
    { mind_entry_record = None
    ; mind_entry_finite = Declarations.Finite
    ; mind_entry_params = Context.Rel.empty
    ; mind_entry_inds = [ ind ]
    ; mind_entry_universes = Monomorphic_ind_entry
    ; mind_entry_variance = None
    ; mind_entry_private = None
    }
  in
  let mind_name =
    DeclareInd.declare_mutual_inductive_with_eliminations mind
      (Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders)
      []
  in
  ret (mind_name, 0)
