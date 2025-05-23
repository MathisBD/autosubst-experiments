open Prelude
open Signature
module C = Constants

(** Call tactic [simpl_term_one] defined in Ltac2. *)
let simpl_term_one (sign : EConstr.t) (t1 : EConstr.t) :
    (EConstr.t * EConstr.t) Proofview.tactic =
  let open PVMonad in
  let open Ltac2_plugin in
  let open Tac2ffi in
  let kname = mk_kername [ "Prototype"; "RASimpl" ] "simpl_term_one" in
  let tac = Tac2interp.eval_global kname in
  let* res = Tac2val.apply_val tac [ of_constr sign; of_constr t1 ] in
  ret @@ to_pair to_constr to_constr res

let simpl_term_zero (sign : signature) (ops : ops_all) (t0 : EConstr.t) :
    (EConstr.t * EConstr.t) Proofview.tactic =
  let open PVMonad in
  (* Reify Level 0 -> Level 1. *)
  let* t1, p1 = monad_run_tactic @@ Reification.reify_term sign ops t0 in
  (* Simplify on level 1. *)
  let* t1', p2 = simpl_term_one (mkconst ops.ops_ops1.sign) t1 in
  (* Eval Level 1 -> Level 0. *)
  let* t0', p3 = monad_run_tactic @@ Evaluation.eval_term sign ops t1' in
  (* [eq0 : t0 = t0']. *)
  let* eq0 =
    monad_run_tactic
    @@
    let open Metaprog in
    let* x = apps_ev (mkglob' C.eq_sym) 3 [| p1 |] in
    let* y =
      apps_ev (mkglob' C.eq_trans) 4
        [| apps (mkconst ops.ops_congr.congr_eval) [| t1; t1'; p2 |]; p3 |]
    in
    let* z = apps_ev (mkglob' C.eq_trans) 4 [| x; y |] in
    (* Typecheck to resolve evars. *)
    let* _ = typecheck z None in
    ret z
  in
  ret (t0', eq0)

(** Call tactic [simpl_subst_one] defined in Ltac2. *)
let simpl_subst_one (sign : EConstr.t) (s1 : EConstr.t) :
    (EConstr.t * EConstr.t) Proofview.tactic =
  let open PVMonad in
  let open Ltac2_plugin in
  let open Tac2ffi in
  let kname = mk_kername [ "Prototype"; "RASimpl" ] "simpl_subst_one" in
  let tac = Tac2interp.eval_global kname in
  let* res = Tac2val.apply_val tac [ of_constr sign; of_constr s1 ] in
  ret @@ to_pair to_constr to_constr res

let simpl_subst_zero (sign : signature) (ops : ops_all) (s0 : EConstr.t) :
    (EConstr.t * EConstr.t) Proofview.tactic =
  let open PVMonad in
  (* Reify Level 0 -> Level 1. *)
  let* s1, p1 = monad_run_tactic @@ Reification.reify_subst sign ops s0 in
  (* Simplify on level 1. *)
  let* s1', p2 = simpl_subst_one (mkconst ops.ops_ops1.sign) s1 in
  (* Eval Level 1 -> Level 0. *)
  let* s0', p3 = monad_run_tactic @@ Evaluation.eval_subst sign ops s1' in
  (* [eq0 : s0 =1 s0']. *)
  let* eq0 =
    monad_run_tactic
    @@
    let open Metaprog in
    let* x = apps_ev (mkglob' C.peq_sym) 4 [| p1 |] in
    let* y =
      apps_ev (mkglob' C.peq_trans) 5
        [| apps (mkconst ops.ops_congr.congr_seval) [| s1; s1'; p2 |]; p3 |]
    in
    let* z = apps_ev (mkglob' C.peq_trans) 5 [| x; y |] in
    (* Typecheck to resolve evars. *)
    let* _ = typecheck z None in
    ret z
  in
  ret (s0', eq0)
