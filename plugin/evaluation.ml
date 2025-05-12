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

  (** Pattern which matches [O.E_ctor ?c ?al]. *)
  let ctor_patt : (EConstr.t * EConstr.t) patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | App (f, [| c; al |]) when is_ctor sigma P.ops1.e_ctor f -> (sigma, Some (c, al))
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
    | App (f, [| s; t |]) when is_const sigma P.ops1.substitute f -> (sigma, Some (s, t))
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
    (* Branch for [C_i ?args]. *)
    (*let ctor_branch (i, args) : (EConstr.t * EConstr.t) m =
      let args = Array.to_list args in
      (* Reify a single argument. *)
      let rec reify_arg (ty, arg) =
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
            let* arg', p = reify_arg (ty, arg) in
            let* arg' = apps_ev (mkctor P.ops1.e_abind) 1 [| arg' |] in
            ret (arg', p)
      in
      let* rargs = List.monad_map reify_arg @@ List.combine P.sign.ctor_types.(i) args in
      let args', p_args = List.split rargs in
      let* al' = mk_args args' in
      let t' = apps (mkctor P.ops1.e_ctor) [| mkctor (P.ops1.ctor, i + 1); al' |] in
      let n_args = List.length P.sign.ctor_types.(i) in
      (* No need to use a lemma of the form [eval_ctor]: [eval] computes on constructors. *)
      let* p =
        apps_ev (mkconst P.congr.congr_ctors.(i)) (2 * n_args) @@ Array.of_list p_args
      in
      ret (t', p)
    in*)
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
    (* Branch for [substitute ?s ?t1]. *)
    (*let substitute_branch (s, t1) =
      let* s', p_s = reify_subst s in
      let* t1', p_t1 = reify_term t1 in
      let t' = apps (mkconst P.ops1.substitute) [| kt P.ops1; s'; t1' |] in
      let p1 = apps (mkconst P.pe.eval_substitute) [| s'; t1' |] in
      let* p2 = apps_ev (mkconst P.congr.congr_substitute) 4 [| p_s; p_t1 |] in
      let* p = apps_ev (Lazy.force Consts.transitivity) 6 [| p1; p2 |] in
      ret (t', p)
    in*)
    (* Default branch. *)
    let default_branch t' =
      let t = apps (mkconst P.re.eval) [| kt P.ops1; t' |] in
      let p = app (mkconst P.bij.eval_reify_inv) t in
      ret (t, p)
    in
    (* Actual pattern matching. *)
    pattern_match t'
      [ Case (var_patt, var_branch); Case (rename_patt, rename_branch) ]
      default_branch

  (*and eval_subst (s : EConstr.t) : (EConstr.t * EConstr.t) m =
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
      default_branch*)
end

(**************************************************************************************)
(** *** Putting it all together. *)
(**************************************************************************************)

(** [eval_term sign ops t'] evaluates the level zero one [t'] into a pair [(t, p)]:
    - [t] is a level zero term.
    - [p] is a proof of [eval t' = t]. *)
let eval_term (sign : signature) (ops : ops_all) (t' : EConstr.t) :
    (EConstr.t * EConstr.t) m =
  let* env = get_env in
  let* sigma = get_sigma in
  Log.printf "%s" (Log.show_econstr env sigma t');
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
