(** This file reifies level zero terms/substitutions into level one terms/substitutions.
*)

open Prelude

module Make (P : sig
  val sign : signature
  val ops0 : ops_zero
  val ops1 : ops_one
  val re : ops_reify_eval
  val congr : ops_congr
  val bij : ops_bijection
  val pe : ops_push_eval
end) =
struct
  (**************************************************************************************)
  (** *** Patterns. *)
  (**************************************************************************************)

  (** Pattern which matches [O.E_Var ?i]. *)
  let var_patt : EConstr.t patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | App (f, [| i |]) when is_ctor sigma P.ops1.e_var f -> (sigma, Some i)
    | _ -> (sigma, None)

  (** Pattern which matches a single argument of type [ty]. *)
  let rec arg_patt (ty : arg_ty) : EConstr.t patt =
   fun a env sigma ->
    match (ty, EConstr.kind sigma a) with
    | AT_base _, App (f, [| _; x |]) when is_ctor sigma P.ops1.e_abase f -> (sigma, Some x)
    | AT_term, App (f, [| t |]) when is_ctor sigma P.ops1.e_aterm f -> (sigma, Some t)
    | AT_bind ty, App (f, [| _; a |]) when is_ctor sigma P.ops1.e_abind f ->
        arg_patt ty a env sigma
    | _ -> (sigma, None)

  (** Pattern which matches an argument list of type [tys]. *)
  let rec args_patt (tys : arg_ty list) : EConstr.t list patt =
   fun al env sigma ->
    match (tys, EConstr.kind sigma al) with
    | [], _ when is_ctor sigma P.ops1.e_al_nil al -> (sigma, Some [])
    | ty :: tys, App (f, [| _; _; a; al |]) when is_ctor sigma P.ops1.e_al_cons f -> begin
        match arg_patt ty a env sigma with
        | sigma, None -> (sigma, None)
        | sigma, Some a -> begin
            match args_patt tys al env sigma with
            | sigma, None -> (sigma, None)
            | sigma, Some al -> (sigma, Some (a :: al))
          end
      end
    | _ -> (sigma, None)

  (** Pattern which matches [O.E_ctor ?c ?al]. *)
  let ctor_patt : (int * EConstr.t list) patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | App (f, [| c; al |]) when is_ctor sigma P.ops1.e_ctor f -> begin
        match EConstr.kind sigma c with
        | Construct ((ctor, i), _) when Names.Ind.UserOrd.equal ctor P.ops1.ctor -> begin
            let tys = P.sign.ctor_types.(i - 1) in
            match args_patt tys al env sigma with
            | sigma, None -> (sigma, None)
            | sigma, Some al -> (sigma, Some (i - 1, al))
          end
        | _ -> (sigma, None)
      end
    | _ -> (sigma, None)

  (** Pattern which matches [O.rename ?r ?t]. *)
  let rename_patt : (EConstr.t * EConstr.t) patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | App (f, [| r; t |]) when is_const sigma P.ops1.rename f -> (sigma, Some (r, t))
    | _ -> (sigma, None)

  (** Pattern which matches [O.substitute ?s ?t]. *)
  let substitute_patt : (EConstr.t * EConstr.t) patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | App (f, [| _; s; t |]) when is_const sigma P.ops1.substitute f ->
        (sigma, Some (s, t))
    | _ -> (sigma, None)

  (** Pattern which matches [reify ?t]. *)
  let reify_patt : EConstr.t patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | App (f, [| t |]) when is_const sigma P.re.reify f -> (sigma, Some t)
    | _ -> (sigma, None)

  (** Pattern which matches [O.sid]. *)
  let sid_patt : unit patt =
   fun s env sigma ->
    if is_const sigma P.ops1.sid s then (sigma, Some ()) else (sigma, None)

  (** Pattern which matches [O.sshift]. *)
  let sshift_patt : unit patt =
   fun s env sigma ->
    if is_const sigma P.ops1.sshift s then (sigma, Some ()) else (sigma, None)

  (** Pattern which matches [O.scons ?t ?s]. *)
  let scons_patt : (EConstr.t * EConstr.t) patt =
   fun s env sigma ->
    match EConstr.kind sigma s with
    | App (f, [| t; s |]) when is_const sigma P.ops1.scons f -> (sigma, Some (t, s))
    | _ -> (sigma, None)

  (** Pattern which matches [O.scomp ?s1 ?s2]. *)
  let scomp_patt : (EConstr.t * EConstr.t) patt =
   fun s env sigma ->
    match EConstr.kind sigma s with
    | App (f, [| s1; s2 |]) when is_const sigma P.ops1.scomp f -> (sigma, Some (s1, s2))
    | _ -> (sigma, None)

  (** Pattern which matches [O.sreify ?s]. *)
  let sreify_patt : EConstr.t patt =
   fun s env sigma ->
    match EConstr.kind sigma s with
    | App (f, [| s |]) when is_const sigma P.re.sreify f -> (sigma, Some s)
    | _ -> (sigma, None)

  (**************************************************************************************)
  (** *** Reify terms and substitutions. *)
  (**************************************************************************************)

  let rec eval_term (t' : EConstr.t) : (EConstr.t * EConstr.t) m =
    (* Branch for [O.E_Var ?i]. *)
    let var_branch i =
      let t = app (mkctor (P.ops0.term, 1)) i in
      let* p = apps_ev (Lazy.force Consts.eq_refl) 1 [| t |] in
      ret (t, p)
    in
    (* Branch for [O.E_ctor ?c ?al]. *)
    let ctor_branch (i, al) =
      let rec eval_arg ty a : (EConstr.t * EConstr.t) m =
        match ty with
        | AT_base _ ->
            let* p = apps_ev (Lazy.force Consts.eq_refl) 1 [| a |] in
            ret (a, p)
        | AT_term -> eval_term a
        | AT_bind ty -> eval_arg ty a
      in
      let* eargs = List.monad_map2 eval_arg P.sign.ctor_types.(i) al in
      let args, p_args = List.split eargs in
      let t = apps (mkctor (P.ops0.term, 2 + i)) @@ Array.of_list args in
      let n_args = List.length al in
      let* p =
        apps_ev (mkconst P.congr.congr_ctors.(i)) (2 * n_args) @@ Array.of_list p_args
      in
      ret (t, p)
    in
    (* Branch for [O.rename ?r ?t1']. *)
    let rename_branch (r, t1') =
      let* p_r = apps_ev (Lazy.force Consts.reflexivity) 3 [| r |] in
      let* t1, p_t1 = eval_term t1' in
      let t = apps (mkconst P.ops0.rename) [| r; t1 |] in
      let p1 = apps (mkconst P.pe.eval_rename) [| r; t1' |] in
      let* p2 = apps_ev (mkconst P.congr.congr_rename) 4 [| p_r; p_t1 |] in
      let* p = apps_ev (Lazy.force Consts.transitivity) 6 [| p1; p2 |] in
      ret (t, p)
    in
    (* Branch for [O.substitute ?s' ?t1']. *)
    let substitute_branch (s', t1') =
      let* s, p_s = eval_subst s' in
      let* t1, p_t1 = eval_term t1' in
      let t = apps (mkconst P.ops0.substitute) [| s; t1 |] in
      let p1 = apps (mkconst P.pe.eval_substitute) [| s'; t1' |] in
      let* p2 = apps_ev (mkconst P.congr.congr_substitute) 4 [| p_s; p_t1 |] in
      let* p = apps_ev (Lazy.force Consts.transitivity) 6 [| p1; p2 |] in
      ret (t, p)
    in
    (* Branch for [reify ?t]. *)
    let reify_branch t = ret (t, app (mkconst P.bij.eval_reify_inv) t) in
    (* Default branch. *)
    let default_branch t' =
      let t = apps (mkconst P.re.eval) [| kt P.ops1; t' |] in
      let* p = apps_ev (Lazy.force Consts.eq_refl) 1 [| t |] in
      ret (t, p)
    in
    (* Actual pattern matching. *)
    pattern_match t'
      [ Case (var_patt, var_branch)
      ; Case (ctor_patt, ctor_branch)
      ; Case (rename_patt, rename_branch)
      ; Case (substitute_patt, substitute_branch)
      ; Case (reify_patt, reify_branch)
      ]
      default_branch

  and eval_subst (s' : EConstr.t) : (EConstr.t * EConstr.t) m =
    (* Match [O.sid]. *)
    let sid_branch () =
      let s = mkconst P.ops0.sid in
      let* p = apps_ev (Lazy.force Consts.reflexivity) 3 [| s |] in
      ret (s, p)
    in
    (* Match [O.sshift]. *)
    let sshift_branch () =
      let s = mkconst P.ops0.sshift in
      let* p = apps_ev (Lazy.force Consts.reflexivity) 3 [| s |] in
      ret (s, p)
    in
    (* Match [O.scons ?t' ?s1']. *)
    let scons_branch (t', s1') =
      let* t, p_t = eval_term t' in
      let* s1, p_s1 = eval_subst s1' in
      let s = apps (mkconst P.ops0.scons) [| t; s1 |] in
      let p1 = apps (mkconst P.pe.seval_scons) [| t'; s1' |] in
      let* p2 = apps_ev (mkconst P.congr.congr_scons) 4 [| p_t; p_s1 |] in
      let* p = apps_ev (Lazy.force Consts.transitivity) 6 [| p1; p2 |] in
      ret (s, p)
    in
    (* Match [O.scomp ?s1' ?s2']. *)
    let scomp_branch (s1', s2') =
      let* s1, p_s1 = eval_subst s1' in
      let* s2, p_s2 = eval_subst s2' in
      let s = apps (mkconst P.ops0.scomp) [| s1; s2 |] in
      let p1 = apps (mkconst P.pe.seval_scomp) [| s1'; s2' |] in
      let* p2 = apps_ev (mkconst P.congr.congr_scomp) 4 [| p_s1; p_s2 |] in
      let* p = apps_ev (Lazy.force Consts.transitivity) 6 [| p1; p2 |] in
      ret (s, p)
    in
    (* Match [sreify ?s]. *)
    let sreify_branch s = ret (s, app (mkconst P.bij.seval_sreify_inv) s) in
    (* Default branch. *)
    let default_branch s' =
      let s = app (mkconst P.re.seval) s' in
      let* p = apps_ev (Lazy.force Consts.reflexivity) 3 [| s |] in
      ret (s, p)
    in
    (* Actual pattern matching. *)
    pattern_match s'
      [ Case (sid_patt, sid_branch)
      ; Case (sshift_patt, sshift_branch)
      ; Case (scons_patt, scons_branch)
      ; Case (scomp_patt, scomp_branch)
      ; Case (sreify_patt, sreify_branch)
      ]
      default_branch
end

(**************************************************************************************)
(** *** Putting it all together. *)
(**************************************************************************************)

(** [eval_term sign ops t'] evaluates the level zero one [t'] into a pair [(t, p)]:
    - [t] is a level zero term.
    - [p] is a proof of [eval t' = t]. *)
let eval_term (sign : signature) (ops : ops_all) (t' : EConstr.t) :
    (EConstr.t * EConstr.t) m =
  let module M = Make (struct
    let sign = sign
    let ops0 = ops.ops_ops0
    let ops1 = ops.ops_ops1
    let congr = ops.ops_congr
    let re = ops.ops_re
    let bij = ops.ops_bij
    let pe = ops.ops_pe
  end) in
  let* t, p = M.eval_term t' in
  (* Typecheck to resolve evars. *)
  let* _ = typecheck t None in
  let p_ty =
    apps (Lazy.force Consts.eq)
      [| mkind ops.ops_ops0.term
       ; apps (mkconst ops.ops_re.eval) [| kt ops.ops_ops1; t' |]
       ; t
      |]
  in
  let* _ = typecheck p (Some p_ty) in
  ret (t, p)
