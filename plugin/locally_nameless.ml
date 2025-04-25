open Monad

let mk_kername (dir : string list) (label : string) : Names.KerName.t =
  let dir =
    Names.ModPath.MPfile (Names.DirPath.make @@ List.rev_map Names.Id.of_string_soft dir)
  in
  let label = Names.Label.make label in
  Names.KerName.make dir label

let fresh_ident : string -> Names.Id.t =
  let used_names = ref Names.Id.Set.empty in
  fun basename ->
    let name = Namegen.next_ident_away (Names.Id.of_string_soft basename) !used_names in
    used_names := Names.Id.Set.add name !used_names;
    name

let with_local_decl (basename : string) ?(def : EConstr.t option) (ty : EConstr.t)
    (k : Names.Id.t -> 'a m) : 'a m =
  let id = fresh_ident basename in
  let* sigma = get_sigma in
  let decl =
    match def with
    | None ->
        Context.Named.Declaration.LocalAssum
          ( { binder_name = id; binder_relevance = Sorts.Relevant }
          , EConstr.to_constr sigma ty )
    | Some def ->
        Context.Named.Declaration.LocalDef
          ( { binder_name = id; binder_relevance = Sorts.Relevant }
          , EConstr.to_constr sigma def
          , EConstr.to_constr sigma ty )
  in
  with_env' (Environ.push_named decl) @@ k id

let app f x = EConstr.mkApp (f, [| x |])
let apps f xs = EConstr.mkApp (f, xs)
let arrow t1 t2 = EConstr.mkArrowR t1 (EConstr.Vars.lift 1 t2)
let rec arrows ts t = match ts with [] -> t | t1 :: ts -> arrow t1 (arrows ts t)

(*let rec with_local_decls (basenames : string list) (tys : EConstr.t list)
    (k : Environ.env -> Evd.evar_map -> Names.Id.t list -> Evd.evar_map * 'a) :
    Evd.evar_map * 'a =
  match (basenames, tys) with
  | [], [] -> k env sigma []
  | b :: basenames, t :: tys ->
      with_local_decls env sigma basenames tys (fun env sigma ids ->
          with_local_decl env sigma b t @@ fun env sigma id -> k env sigma (id :: ids))
  | _ -> failwith "with_local_decl: lengths differ"*)

let lambda name ty mk_body =
  with_local_decl name ty @@ fun id ->
  let* body = mk_body id in
  let* sigma = get_sigma in
  ret
  @@ EConstr.mkNamedLambda sigma
       { binder_name = id; binder_relevance = EConstr.ERelevance.relevant }
       ty body

let prod name ty mk_body =
  with_local_decl name ty @@ fun id ->
  let* body = mk_body id in
  let* sigma = get_sigma in
  ret
  @@ EConstr.mkNamedProd sigma
       { binder_name = id; binder_relevance = EConstr.ERelevance.relevant }
       ty body

let let_in name def ty mk_body =
  with_local_decl name ~def ty @@ fun id ->
  let* body = mk_body id in
  let* sigma = get_sigma in
  ret
  @@ EConstr.mkNamedLetIn sigma
       { binder_name = id; binder_relevance = EConstr.ERelevance.relevant }
       def ty body

let fix name rec_arg_idx ty mk_body =
  with_local_decl name ty @@ fun id ->
  let* body = mk_body id in
  let* sigma = get_sigma in
  ret
  @@ EConstr.mkFix
       ( ([| rec_arg_idx |], 0)
       , ( [| { binder_name = Name id; binder_relevance = EConstr.ERelevance.relevant } |]
         , [| ty |]
         , [| EConstr.Vars.subst_var sigma id body |] ) )

let declare_ind (name : string) (arity : EConstr.t) (ctor_names : string list)
    (ctor_types : (Names.Id.t -> EConstr.t m) list) : Names.Ind.t =
  let open Entries in
  (* Build the constructor types. *)
  let build_ctor_type (mk_ty : Names.Id.t -> EConstr.t m) : Constr.t =
    monad_run @@ with_local_decl name arity
    @@ fun ind ->
    let* ty = mk_ty ind in
    let* sigma = get_sigma in
    ret @@ EConstr.to_constr sigma @@ EConstr.Vars.subst_var sigma ind ty
  in
  (* Declare the inductive. *)
  let ind =
    { mind_entry_typename = Names.Id.of_string_soft name
    ; mind_entry_arity = EConstr.to_constr Evd.empty arity
    ; mind_entry_consnames = List.map Names.Id.of_string_soft ctor_names
    ; mind_entry_lc = List.map build_ctor_type ctor_types
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
  (mind_name, 0)

(** Generalizes [namedLambda] to multiple variables in a [EConstr.rel_context].

    The body receives the variables in the same order they are stored in the context, i.e.
    the most recent (= inner-most) variable first. *)
(*let namedLambdaContext env sigma (ctx : EConstr.rel_context)
    (body : Environ.env -> Evd.evar_map -> Names.Id.t list -> Evd.evar_map * EConstr.t) :
    Evd.evar_map * EConstr.t =
  let open EConstr in
  let open Context in
  let open Rel in
  (* Get the names and types of the variables in the context. *)
  let names =
    ctx
    |> List.map @@ fun decl ->
       match Declaration.get_name decl with
       | Name n -> Names.Id.to_string n
       | Anonymous -> "x"
  in
  let tys = List.map Declaration.get_type ctx in
  with_fresh_vars env sigma names tys @@ fun env sigma ids ->
  (* Build the body. *)
  let sigma, body = body env sigma ids in
  (* Add lambda abstractions. *)
  ( sigma
  , List.fold_left
      (fun body decl ->
        mkLambda
          ( { binder_name = Declaration.get_name decl
            ; binder_relevance = Declaration.get_relevance decl
            }
          , Declaration.get_type decl
          , Vars.subst_vars sigma ids body ))
      body ctx )*)
