open Prelude

module Make (P : sig
  val sign : signature
  val ops0 : ops_zero
  val ops1 : ops_one
end) =
struct
  (**************************************************************************************)
  (** *** Build the reification functions. *)
  (**************************************************************************************)

  (** Build [reify : term -> O.expr Kt]. *)
  let build_reify () : EConstr.t m =
    let open EConstr in
    (* Build the fixpoint. *)
    fix "reify" 0 (arrow (mkind P.ops0.term) (term1 P.ops1)) @@ fun reify ->
    lambda "t" (mkind P.ops0.term) @@ fun t ->
    case (EConstr.mkVar t) @@ fun i args ->
    (* Reify an argument. *)
    let rec reify_arg (ty : arg_ty) (arg : Names.Id.t) : EConstr.t m =
      match ty with
      | AT_base b ->
          ret @@ apps (mkctor P.ops1.e_abase) [| mkctor (P.ops1.base, b + 1); mkVar arg |]
      | AT_term ->
          ret @@ apps (mkctor P.ops1.e_aterm) [| app (EConstr.mkVar reify) (mkVar arg) |]
      | AT_bind ty ->
          let* ev = fresh_evar None in
          let* rarg = reify_arg ty arg in
          ret @@ apps (mkctor P.ops1.e_abind) [| ev; rarg |]
    in
    (* Reify a list of arguments. *)
    let rec reify_args (args : (arg_ty * Names.Id.t) list) : EConstr.t m =
      match args with
      | [] -> ret @@ mkctor P.ops1.e_al_nil
      | (ty, arg) :: args ->
          let* ev1 = fresh_evar None in
          let* ev2 = fresh_evar None in
          let* rarg = reify_arg ty arg in
          let* rargs = reify_args args in
          ret @@ apps (mkctor P.ops1.e_al_cons) [| ev1; ev2; rarg; rargs |]
    in
    if i = 0
    then (* Variable constructor. *)
      ret @@ app (mkctor P.ops1.e_var) (EConstr.mkVar @@ List.hd args)
    else (* Non-variable constructors. *)
      let* rargs = reify_args @@ List.combine P.sign.ctor_types.(i - 1) args in
      ret @@ apps (mkctor P.ops1.e_ctor) [| mkctor (P.ops1.ctor, i); rargs |]

  (** Build [sreify : susbt -> O.subst]. *)
  let build_sreify (reify : Names.Constant.t) : EConstr.t m =
    lambda "s" (mkconst P.ops0.subst) @@ fun s ->
    lambda "i" (Lazy.force Consts.nat) @@ fun i ->
    ret @@ app (mkconst reify) @@ app (EConstr.mkVar s) (EConstr.mkVar i)

  (**************************************************************************************)
  (** *** Build the evaluation functions. *)
  (**************************************************************************************)

  (** Build [eval_arg : arg_ty -> Type]. *)
  let build_eval_arg () : EConstr.t m =
    let open EConstr in
    let* t = fresh_type in
    let at = app (Lazy.force Consts.arg_ty) @@ mkind P.ops1.base in
    fix "eval_arg" 0 (arrow at t) @@ fun eval_arg ->
    lambda "ty" at @@ fun ty ->
    case (mkVar ty) ~return:(fun _ _ -> ret t) @@ fun i args ->
    match i with
    | 0 -> ret @@ app (mkconst P.ops1.eval_base) @@ mkVar @@ List.hd args
    | 1 -> ret @@ mkind P.ops0.term
    | _ -> ret @@ app (mkVar eval_arg) @@ mkVar @@ List.hd args

  (** Build [eval_args : arg_ty list -> Type]. *)
  let build_eval_args (eval_arg : Names.Constant.t) : EConstr.t m =
    let open EConstr in
    let* t = fresh_type in
    let at_list =
      app (Lazy.force Consts.list) @@ app (Lazy.force Consts.arg_ty) @@ mkind P.ops1.base
    in
    fix "eval_args" 0 (arrow at_list t) @@ fun eval_args ->
    lambda "tys" at_list @@ fun tys ->
    case (mkVar tys) ~return:(fun _ _ -> ret t) @@ fun i args ->
    match i with
    | 0 -> ret @@ Lazy.force Consts.unit
    | _ ->
        let ty = List.hd args in
        let tys = List.hd @@ List.tl args in
        ret
        @@ apps (Lazy.force Consts.prod)
             [| app (mkconst eval_arg) @@ mkVar ty; app (mkVar eval_args) @@ mkVar tys |]

  (** Build [eval_kind : kind -> Type]. *)
  let build_eval_kind (eval_arg : Names.Constant.t) (eval_args : Names.Constant.t) :
      EConstr.t m =
    let open EConstr in
    let kind = app (Lazy.force Consts.kind) @@ mkind P.ops1.base in
    lambda "k" kind @@ fun k ->
    case (mkVar k) ~return:(fun _ _ -> fresh_type) @@ fun i args ->
    match i with
    | 0 -> ret @@ mkind P.ops0.term
    | 1 -> ret @@ app (mkconst eval_arg) @@ mkVar @@ List.hd args
    | _ -> ret @@ app (mkconst eval_args) @@ mkVar @@ List.hd args

  (** Build [eval_ctor : ctor -> eval_args (ctor_type c) -> term]. *)
  let build_eval_ctor (eval_args : Names.Constant.t) : EConstr.t m =
    let open EConstr in
    lambda "c" (mkind P.ops1.ctor) @@ fun c ->
    (* We need to do dependent pattern matching (i.e. specify the case return clause by hand). *)
    let return _ c =
      ret
      @@ arrow (app (mkconst eval_args) @@ app (mkconst P.ops1.ctor_type) @@ mkVar c)
      @@ mkind P.ops0.term
    in
    case (mkVar c) ~return @@ fun i _ ->
    (* The arguments are bundled as [(a1, (a2, (a3, ...)))]. 
     We have to repeatedly pattern match to extract all individual arguments. *)
    let rec on_args (n : int) (acc : EConstr.t) (args : Names.Id.t) : EConstr.t m =
      match n with
      | 0 -> ret acc
      | _ -> (
          case (mkVar args) @@ fun _ bundle ->
          match bundle with
          | [ a; args ] -> on_args (n - 1) (app acc @@ mkVar a) args
          | _ -> Log.error "build_eval_ctor")
    in
    lambda "args"
      (app (mkconst eval_args)
      @@ app (mkconst P.ops1.ctor_type)
      @@ mkctor (P.ops1.ctor, i + 1))
    @@ on_args (List.length P.sign.ctor_types.(i)) (mkctor (P.ops0.term, i + 2))

  (** Build [eval : forall k : kind, O.expr k -> eval_kind k]. *)
  let build_eval (eval_kind : Names.Constant.t) (eval_ctor : Names.Constant.t) :
      EConstr.t m =
    let open EConstr in
    let* eval_ty =
      prod "k" (app (Lazy.force Consts.kind) @@ mkind P.ops1.base) @@ fun k ->
      ret
      @@ arrow (app (mkind P.ops1.expr) @@ mkVar k)
      @@ app (mkconst eval_kind)
      @@ mkVar k
    in
    fix "eval" 1 eval_ty @@ fun eval ->
    lambda "k" (app (Lazy.force Consts.kind) @@ mkind P.ops1.base) @@ fun k ->
    lambda "t" (app (mkind P.ops1.expr) @@ mkVar k) @@ fun t ->
    let return indices _ = ret @@ app (mkconst eval_kind) @@ mkVar @@ List.hd indices in
    case (mkVar t) ~return @@ fun i args ->
    match (i, args) with
    | 0, [ idx ] -> ret @@ app (mkctor (P.ops0.term, 1)) @@ mkVar idx
    | 1, [ c; al ] ->
        let* kal = fresh_evar None in
        ret
        @@ apps (mkconst eval_ctor) [| mkVar c; apps (mkVar eval) [| kal; mkVar al |] |]
    | 2, [] -> ret @@ Lazy.force Consts.tt
    | 3, [ ty; tys; a; al ] ->
        let* t1 = fresh_evar None in
        let* t2 = fresh_evar None in
        let* ka = fresh_evar None in
        let* kal = fresh_evar None in
        ret
        @@ apps (Lazy.force Consts.pair)
             [| t1
              ; t2
              ; apps (mkVar eval) [| ka; mkVar a |]
              ; apps (mkVar eval) [| kal; mkVar al |]
             |]
    | 4, [ b; x ] -> ret @@ mkVar x
    | 5, [ t ] ->
        let* kt = fresh_evar None in
        ret @@ apps (mkVar eval) [| kt; mkVar t |]
    | 6, [ ty; a ] ->
        let* ka = fresh_evar None in
        ret @@ apps (mkVar eval) [| ka; mkVar a |]
    | _ -> Log.error "build_eval: %i" i

  (** Build [seval : O.subst -> subst]. *)
  let build_seval (eval : Names.Constant.t) : EConstr.t m =
    lambda "s" (mkconst P.ops1.subst) @@ fun s ->
    lambda "i" (Lazy.force Consts.nat) @@ fun i ->
    let si = app (EConstr.mkVar s) (EConstr.mkVar i) in
    ret @@ apps (mkconst eval) [| app (Lazy.force Consts.k_t) @@ mkind P.ops1.base; si |]
end

(**************************************************************************************)
(** *** Put everything together. *)
(**************************************************************************************)

(** Generate the reification and evaluation functions. *)
let generate (s : signature) (ops0 : ops_zero) (ops1 : ops_one) : ops_reify_eval =
  let module M = Make (struct
    let sign = s
    let ops0 = ops0
    let ops1 = ops1
  end) in
  let reify = def "reify" ~kind:Decls.Fixpoint @@ M.build_reify () in
  let sreify = def "sreify" @@ M.build_sreify reify in
  let eval_arg = def "eval_arg" ~kind:Decls.Fixpoint @@ M.build_eval_arg () in
  let eval_args = def "eval_args" ~kind:Decls.Fixpoint @@ M.build_eval_args eval_arg in
  let eval_kind = def "eval_kind" @@ M.build_eval_kind eval_arg eval_args in
  let eval_ctor = def "eval_ctor" @@ M.build_eval_ctor eval_args in
  let eval = def "eval" @@ M.build_eval eval_kind eval_ctor in
  let seval = def "seval" @@ M.build_seval eval in
  { reify; sreify; eval_arg; eval_args; eval_kind; eval_ctor; eval; seval }
