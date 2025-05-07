(** This file reifies level zero terms/substitutions into level one terms/substitutions.
*)

open Prelude

let is_const (sigma : Evd.evar_map) (c : Names.Constant.t) (t : EConstr.t) : bool =
  match EConstr.kind sigma t with
  | Constr.Const (c', _) when Names.Constant.UserOrd.equal c c' -> true
  | _ -> false

let is_ind (sigma : Evd.evar_map) (i : Names.Ind.t) (t : EConstr.t) : bool =
  match EConstr.kind sigma t with
  | Constr.Ind (i', _) when Names.Ind.UserOrd.equal i i' -> true
  | _ -> false

let is_ctor (sigma : Evd.evar_map) (c : Names.Construct.t) (t : EConstr.t) : bool =
  match EConstr.kind sigma t with
  | Constr.Construct (c', _) when Names.Construct.UserOrd.equal c c' -> true
  | _ -> false

module MakeInternal (P : sig
  val sign : signature
  val ops0 : ops_zero
  val ops1 : ops_one
  val re : ops_reify_eval
  val congr : ops_congr
  val bij : ops_bijection
  val pe : ops_push_eval
end) =
struct
  let dest_var (sigma : Evd.evar_map) (t : EConstr.t) : EConstr.t option =
    match EConstr.kind sigma t with
    | Constr.App (f, [| i |]) when is_ctor sigma (P.ops0.term, 1) f -> Some i
    | _ -> None

  let dest_ctor (sigma : Evd.evar_map) (t : EConstr.t) : (int * EConstr.t array) option =
    match EConstr.kind sigma t with
    | Constr.App (ind, args) -> begin
        match EConstr.kind sigma ind with
        | Constr.Construct ((ind, i), _)
          when Names.Ind.UserOrd.equal P.ops0.term ind && 2 <= i ->
            Some (i - 2, args)
        | _ -> None
      end
    | _ -> None

  let dest_substitute (sigma : Evd.evar_map) (t : EConstr.t) :
      (EConstr.t * EConstr.t) option =
    match EConstr.kind sigma t with
    | Constr.App (f, [| s; t |]) when is_const sigma P.ops0.substitute f -> Some (s, t)
    | _ -> None

  (** [reify_term sigma t] reifies the level zero term [t] into a pair [(t', p)], such
      that [t'] is a level one term and [p] is a proof of [eval t' = t]. *)
  let rec reify_term (t : EConstr.t) : (EConstr.t * EConstr.t) m =
    let* sigma = get_sigma in
    match dest_var sigma t with
    | Some i ->
        let t' = app (mkctor P.ops1.e_var) i in
        let p = apps (Lazy.force Consts.eq_refl) [| mkind P.ops0.term; t |] in
        ret (t', p)
    | None -> (
        match dest_substitute sigma t with
        | Some (s, u) ->
            let* s', p1 = reify_subst s in
            let* u', p2 = reify_term u in
            let t' = apps (mkconst P.ops1.substitute) [| kt P.ops1; s'; u' |] in
            let* ev0 = fresh_evar None in
            let* ev1 = fresh_evar None in
            let* ev2 = fresh_evar None in
            let* ev3 = fresh_evar None in
            let* ev4 = fresh_evar None in
            let* ev5 = fresh_evar None in
            let* ev6 = fresh_evar None in
            let* ev7 = fresh_evar None in
            let p =
              apps
                (Lazy.force Consts.transitivity)
                [| mkind P.ops0.term
                 ; app (Lazy.force Consts.eq) @@ mkind P.ops0.term
                 ; ev4
                 ; ev5
                 ; ev6
                 ; ev7
                 ; apps (mkconst P.pe.eval_substitute) [| s'; u' |]
                 ; apps
                     (mkconst P.congr.congr_substitute)
                     [| ev0; ev1; ev2; ev3; p1; p2 |]
                |]
            in
            ret (t', p)
        | None ->
            let t' = app (mkconst P.re.reify) t in
            let p = app (mkconst P.bij.eval_reify_inv) t in
            ret (t', p))

  and reify_subst (s : EConstr.t) : (EConstr.t * EConstr.t) m =
    let s' = app (mkconst P.re.sreify) s in
    let p = app (mkconst P.bij.seval_sreify_inv) s in
    ret (s', p)
end

let reify_term (s : signature) (ops : ops_all) (t : EConstr.t) : (EConstr.t * EConstr.t) m
    =
  let module R = MakeInternal (struct
    let sign = s
    let ops0 = ops.ops_ops0
    let ops1 = ops.ops_ops1
    let congr = ops.ops_congr
    let re = ops.ops_re
    let bij = ops.ops_bij
    let pe = ops.ops_pe
  end) in
  R.reify_term t
