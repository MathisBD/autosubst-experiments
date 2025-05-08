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

(**************************************************************************************)
(** *** Pattern matching utilities. *)
(**************************************************************************************)

(** A pattern ['vars patt] is a function which takes a term (an [EConstr.t]) and either:
    - succeeds and extracts a set of variables of type ['vars].
    - fails and returns [None]. *)
type 'vars patt = EConstr.t -> 'vars option m

(** A branch [('vars, 'res) branch] is a function which takes a set of extracted variables
    of type ['vars] and returns a result of type ['res]. *)
type ('vars, 'res) branch = 'vars -> 'res m

(** A case ['res case] is a pair of a pattern and a branch. *)
type _ case = Case : 'vars patt * ('vars, 'res) branch -> 'res case

(** [pattern_match t cases default] performs case analysis on [t]:
    - [cases] is a list of cases which are tried in order until a pattern succeeds.
    - [default] is a branch which has no pattern (it is passed [t]) and is tried only if
      all [cases] fail. *)
let pattern_match (t : EConstr.t) (cases : 'res case list)
    (default_branch : (EConstr.t, 'res) branch) : 'res m =
  let rec loop cases =
    match cases with
    | [] -> default_branch t
    | Case (p, b) :: cases -> begin
        let* vars_opt = p t in
        match vars_opt with Some vars -> b vars | None -> loop cases
      end
  in
  loop cases

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
    | Constr.App (f, [| i |]) when is_ctor sigma (P.ops0.term, 1) f -> (sigma, Some i)
    | _ -> (sigma, None)

  (** Pattern which matches [C_i ?args], where [C_i] is the [i-th] non-variable
      constructor for terms ([i] starts at [0]). *)
  let ctor_patt : (int * EConstr.t array) patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | Constr.App (ind, args) -> begin
        match EConstr.kind sigma ind with
        | Constr.Construct ((ind, i), _)
          when Names.Ind.UserOrd.equal P.ops0.term ind && 2 <= i ->
            (sigma, Some (i - 2, args))
        | _ -> (sigma, None)
      end
    | _ -> (sigma, None)

  (** Pattern which matches [substitute ?s ?t]. *)
  let substitute_patt : (EConstr.t * EConstr.t) patt =
   fun t env sigma ->
    match EConstr.kind sigma t with
    | Constr.App (f, [| s; t |]) when is_const sigma P.ops0.substitute f ->
        (sigma, Some (s, t))
    | _ -> (sigma, None)

  (**************************************************************************************)
  (** *** Reify terms and substitutions. *)
  (**************************************************************************************)

  let rec reify_term (t : EConstr.t) : (EConstr.t * EConstr.t) m =
    (* Branch for [Var ?i]. *)
    let var_branch i =
      let t' = app (mkctor P.ops1.e_var) i in
      let* p = apps_ev (Lazy.force Consts.eq_refl) 1 [| t |] in
      ret (t', p)
    in
    (* Branch for [substitute ?s ?u]. *)
    let substitute_branch (s, u) =
      let* s', p1 = reify_subst s in
      let* u', p2 = reify_term u in
      let t' = apps (mkconst P.ops1.substitute) [| kt P.ops1; s'; u' |] in
      let trans =
        apps
          (Lazy.force Consts.transitivity)
          [| mkind P.ops0.term; app (Lazy.force Consts.eq) @@ mkind P.ops0.term |]
      in
      let lhs = apps (mkconst P.pe.eval_substitute) [| s'; u' |] in
      let* rhs = apps_ev (mkconst P.congr.congr_substitute) 4 [| p1; p2 |] in
      let* p = apps_ev trans 4 [| lhs; rhs |] in
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
      [ Case (var_patt, var_branch); Case (substitute_patt, substitute_branch) ]
      default_branch

  and reify_subst (s : EConstr.t) : (EConstr.t * EConstr.t) m =
    let s' = app (mkconst P.re.sreify) s in
    let p = app (mkconst P.bij.seval_sreify_inv) s in
    ret (s', p)
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
  M.reify_term t

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
  M.reify_subst s
