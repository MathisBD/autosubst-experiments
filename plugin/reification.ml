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

  (** Pattern which matches [Var ?i], where [Var] is the variable constructor for terms.
  *)
  let var_patt : EConstr.t patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | App (f, [| i |]) when is_ctor sigma (P.ops0.term, 1) f -> (sigma, Some i)
    | _ -> (sigma, None)

  (** Pattern which matches [C_i ?args], where [C_i] is the [i-th] non-variable
      constructor for terms ([i] starts at [0]). *)
  let ctor_patt : (int * EConstr.t array) patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | App (ind, args) -> begin
        match EConstr.kind sigma ind with
        | Construct ((ind, i), _) when Names.Ind.UserOrd.equal P.ops0.term ind && 2 <= i
          ->
            (sigma, Some (i - 2, args))
        | _ -> (sigma, None)
      end
    | _ -> (sigma, None)

  (** Pattern which matches [rename ?r ?t]. *)
  let rename_patt : (EConstr.t * EConstr.t) patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | App (f, [| r; t |]) when is_const sigma P.ops0.rename f -> (sigma, Some (r, t))
    | _ -> (sigma, None)

  (** Pattern which matches [substitute ?s ?t]. *)
  let substitute_patt : (EConstr.t * EConstr.t) patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | App (f, [| s; t |]) when is_const sigma P.ops0.substitute f -> (sigma, Some (s, t))
    | _ -> (sigma, None)

  (** Pattern which matches [sid]. *)
  let sid_patt : unit patt =
   fun s env sigma ->
    if is_const sigma P.ops0.sid s then (sigma, Some ()) else (sigma, None)

  (** Pattern which matches [sshift]. *)
  let sshift_patt : unit patt =
   fun s env sigma ->
    if is_const sigma P.ops0.sshift s then (sigma, Some ()) else (sigma, None)

  (** Pattern which matches [scons ?t ?s]. *)
  let scons_patt : (EConstr.t * EConstr.t) patt =
   fun s env sigma ->
    match EConstr.kind sigma s with
    | App (f, [| t; s |]) when is_const sigma P.ops0.scons f -> (sigma, Some (t, s))
    | _ -> (sigma, None)

  (** Pattern which matches [scomp ?s1 ?s2]. *)
  let scomp_patt : (EConstr.t * EConstr.t) patt =
   fun s env sigma ->
    match EConstr.kind sigma s with
    | App (f, [| s1; s2 |]) when is_const sigma P.ops0.scomp f -> (sigma, Some (s1, s2))
    | _ -> (sigma, None)

  (**************************************************************************************)
  (** *** Reify terms and substitutions. *)
  (**************************************************************************************)

  let rec mk_args (al : EConstr.t list) : EConstr.t m =
    match al with
    | [] -> ret @@ mkctor P.ops1.e_al_nil
    | a :: al ->
        let* al' = mk_args al in
        apps_ev (mkctor P.ops1.e_al_cons) 2 [| a; al' |]

  let rec reify_term (t : EConstr.t) : (EConstr.t * EConstr.t) m =
    (* Branch for [Var ?i]. *)
    let var_branch i =
      let t' = app (mkctor P.ops1.e_var) i in
      let* p = apps_ev (Lazy.force Consts.eq_refl) 1 [| t |] in
      ret (t', p)
    in
    (* Branch for [C_i ?args]. *)
    let ctor_branch (i, args) : (EConstr.t * EConstr.t) m =
      let args = Array.to_list args in
      (* Reify a single argument. *)
      let rec reify_arg ty arg =
        match ty with
        (* For [AT_base] we produce the proof [eq_refl]. *)
        | AT_base b_idx ->
            let arg' =
              apps (mkctor P.ops1.e_abase) [| mkctor (P.ops1.base, b_idx + 1); arg |]
            in
            let p =
              apps (Lazy.force Consts.eq_refl)
                [| EConstr.of_constr P.sign.base_types.(b_idx); arg |]
            in
            ret (arg', p)
        (* For [AT_term] we reuse the proof given by [reify_term]. *)
        | AT_term ->
            let* arg', p = reify_term arg in
            ret (app (mkctor P.ops1.e_aterm) arg', p)
        (* For [AT_bind] we reuse the proof given by [reify_arg]. *)
        | AT_bind ty ->
            let* arg', p = reify_arg ty arg in
            let* arg' = apps_ev (mkctor P.ops1.e_abind) 1 [| arg' |] in
            ret (arg', p)
      in
      let* rargs = List.monad_map2 reify_arg P.sign.ctor_types.(i) args in
      let args', p_args = List.split rargs in
      let* al' = mk_args args' in
      let t' = apps (mkctor P.ops1.e_ctor) [| mkctor (P.ops1.ctor, i + 1); al' |] in
      let n_args = List.length P.sign.ctor_types.(i) in
      (* No need to use a lemma of the form [eval_ctor]: [eval] computes on constructors. *)
      let* p =
        apps_ev (mkconst P.congr.congr_ctors.(i)) (2 * n_args) @@ Array.of_list p_args
      in
      ret (t', p)
    in
    (* Branch for [rename ?r ?t1]. *)
    let rename_branch (r, t1) =
      let* p_r = apps_ev (Lazy.force Consts.reflexivity) 3 [| r |] in
      let* t1', p_t1 = reify_term t1 in
      let t' = apps (mkconst P.ops1.rename) [| kt P.ops1; r; t1' |] in
      let p1 = apps (mkconst P.pe.eval_rename) [| r; t1' |] in
      let* p2 = apps_ev (mkconst P.congr.congr_rename) 4 [| p_r; p_t1 |] in
      let* p = apps_ev (Lazy.force Consts.transitivity) 6 [| p1; p2 |] in
      ret (t', p)
    in
    (* Branch for [substitute ?s ?t1]. *)
    let substitute_branch (s, t1) =
      let* s', p_s = reify_subst s in
      let* t1', p_t1 = reify_term t1 in
      let t' = apps (mkconst P.ops1.substitute) [| kt P.ops1; s'; t1' |] in
      let p1 = apps (mkconst P.pe.eval_substitute) [| s'; t1' |] in
      let* p2 = apps_ev (mkconst P.congr.congr_substitute) 4 [| p_s; p_t1 |] in
      let* p = apps_ev (Lazy.force Consts.transitivity) 6 [| p1; p2 |] in
      ret (t', p)
    in
    (* Default branch. *)
    let default_branch t =
      let t' = app (mkconst P.re.reify) t in
      let p = app (mkconst P.bij.eval_reify_inv) t in
      ret (t', p)
    in
    (* Actual pattern matching. *)
    pattern_match t
      [ Case (var_patt, var_branch)
      ; Case (ctor_patt, ctor_branch)
      ; Case (rename_patt, rename_branch)
      ; Case (substitute_patt, substitute_branch)
      ]
      default_branch

  and reify_subst (s : EConstr.t) : (EConstr.t * EConstr.t) m =
    (* Match [sid]. *)
    let sid_branch () =
      let s' = mkconst P.ops1.sid in
      let* p = apps_ev (Lazy.force Consts.reflexivity) 3 [| s |] in
      ret (s', p)
    in
    (* Match [sshift]. *)
    let sshift_branch () =
      let s' = mkconst P.ops1.sshift in
      let* p = apps_ev (Lazy.force Consts.reflexivity) 3 [| s |] in
      ret (s', p)
    in
    (* Match [scons ?t ?s1]. *)
    let scons_branch (t, s1) =
      let* t', p_t = reify_term t in
      let* s1', p_s1 = reify_subst s1 in
      let s' = apps (mkconst P.ops1.scons) [| t'; s1' |] in
      let p1 = apps (mkconst P.pe.seval_scons) [| t'; s1' |] in
      let* p2 = apps_ev (mkconst P.congr.congr_scons) 4 [| p_t; p_s1 |] in
      let* p = apps_ev (Lazy.force Consts.transitivity) 6 [| p1; p2 |] in
      ret (s', p)
    in
    (* Match [scomp ?s1 ?s2]. *)
    let scomp_branch (s1, s2) =
      let* s1', p_s1 = reify_subst s1 in
      let* s2', p_s2 = reify_subst s2 in
      let s' = apps (mkconst P.ops1.scomp) [| s1'; s2' |] in
      let p1 = apps (mkconst P.pe.seval_scomp) [| s1'; s2' |] in
      let* p2 = apps_ev (mkconst P.congr.congr_scomp) 4 [| p_s1; p_s2 |] in
      let* p = apps_ev (Lazy.force Consts.transitivity) 6 [| p1; p2 |] in
      ret (s', p)
    in
    (* Default branch. *)
    let default_branch s =
      let s' = app (mkconst P.re.sreify) s in
      let p = app (mkconst P.bij.seval_sreify_inv) s in
      ret (s', p)
    in
    (* Actual pattern matching. *)
    pattern_match s
      [ Case (sid_patt, sid_branch)
      ; Case (sshift_patt, sshift_branch)
      ; Case (scons_patt, scons_branch)
      ; Case (scomp_patt, scomp_branch)
      ]
      default_branch
end

(**************************************************************************************)
(** *** Putting it all together. *)
(**************************************************************************************)

(** [reify_term sign ops t] reifies the level zero term [t] into a pair [(t', p)]:
    - [t'] is a level one term.
    - [p] is a proof of [eval t' = t]. *)
let reify_term (sign : signature) (ops : ops_all) (t : EConstr.t) :
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
  (* Reify. *)
  let* t', p = M.reify_term t in
  (* Typecheck to resolve evars. *)
  let* _ = typecheck t' None in
  let p_ty =
    apps (Lazy.force Consts.eq)
      [| mkind ops.ops_ops0.term
       ; apps (mkconst ops.ops_re.eval) [| kt ops.ops_ops1; t' |]
       ; t
      |]
  in
  let* _ = typecheck p (Some p_ty) in
  ret (t', p)

(** [reify_subst sign ops s] reifies the level zero substitution [s] into a pair
    [(s', p)]:
    - [s'] is a level one substitution.
    - [p] is a proof of [seval s' = s]. *)
let reify_subst (sign : signature) (ops : ops_all) (s : EConstr.t) :
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
  let* s', p = M.reify_subst s in
  (* Typecheck to resolve evars. *)
  let* _ = typecheck s' None in
  let p_ty =
    apps (Lazy.force Consts.point_eq)
      [| Lazy.force Consts.nat
       ; mkind ops.ops_ops0.term
       ; app (mkconst ops.ops_re.seval) s'
       ; s
      |]
  in
  let* _ = typecheck p (Some p_ty) in
  ret (s', p)
