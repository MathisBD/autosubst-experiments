From Sulfur Require Import Prelude Sig Constants.
From Sulfur Require ParamSyntax ExplicitSyntax Simplification Cleanup.
From Ltac2 Require Import RedFlags Printf.
From Ltac2 Require Ltac2.

Module P := ParamSyntax.
Module E := ExplicitSyntax.
Module Simp := Simplification.
Module Clean := Cleanup.

(*********************************************************************************)
(** *** Simplifying level one terms/substitutions. *)
(*********************************************************************************)

(** Reduction flags to unfold all (level 2 -> level 1) evaluation 
    functions (LevelTwo.v). *)
Ltac2 red_flags_eval () : RedFlags.t :=
  red_flags:(beta iota delta   
    [E.eeval E.seval E.eeval_functional E.seval_functional
     E.reval E.qeval E.reval_functional E.qeval_functional
     E.assign_qnat E.assign_ren E.assign_term E.assign_subst
     E.list_nth
     ]).
   
(** Simplify a level one term. Returns [(t1', eq)] where [eq : t1 = t1'].  *)
Ltac2 simpl_term_one (sig : constr) (t1 : constr) : constr * constr :=
  printf "t1: %t" t1;
  (* Reify Level 1 -> Level 2. *)
  let env := E.empty_env () in
  let (env, t2) := E.reify_expr sig env t1 in
  let env := E.build_env sig env in
  printf "t2: %t" t2;
  (* Simplify on Level 2. *)
  let t2' := Std.eval_cbn RedFlags.all constr:(Simp.esimp $t2) in
  printf "t2': %t" t2';
  let t2'' := Std.eval_cbn RedFlags.all constr:(Clean.eclean $t2') in
  printf "t2'': %t" t2'';
  (* Eval Level 2 -> Level 1. *)
  let t1' := Std.eval_cbn (red_flags_eval ()) constr:(E.eeval $env $t2'') in
  printf "t1': %t" t1';
  (* [eq1 : t1 = t1']. *)
  let eq1 := constr:(eq_trans
    (Simp.ered_sound $env _ _ (Simp.esimp_red $t2))
    (Clean.ered_sound $env _ _ (Clean.eclean_red $t2'))) 
  in
  (t1', eq1).
  
  (*(t1', eq1).*)

(** Simplify a level one substitution. Returns [(s1', eq)] where [eq : s1 =₁ s1'].*)
Ltac2 simpl_subst_one (sig : constr) (s1 : constr) : constr * constr :=
  printf "s1: %t" s1;
  (* Reify Level 1 -> Level 2. *)
  let env := E.empty_env () in
  let (env, s2) := E.reify_subst sig env s1 in
  let env := E.build_env sig env in
  printf "s2: %t" s2;
  (* Simplify on Level 2. *)
  let s2' := Std.eval_cbn RedFlags.all constr:(Simp.ssimp $s2) in
  printf "s2': %t" s2';
  let s2'' := Std.eval_cbn RedFlags.all constr:(Clean.sclean $s2') in
  printf "s2'': %t" s2'';
  (* Eval Level 2 -> Level 1. *)
  let s1' := Std.eval_cbv (red_flags_eval ()) constr:(E.seval $env $s2'') in
  printf "s1': %t" s1';
  (* [eq1 : s1 =₁ s1']. *)
  let eq1 := constr:(eq1_trans
    (Simp.sred_sound $env _ _ (Simp.ssimp_red $s2))
    (Clean.sred_sound $env _ _ (Clean.sclean_red $s2'))) 
  in
  (s1', eq1).

(*********************************************************************************)
(** *** Load the plugin. *)
(*********************************************************************************)

Declare ML Module "rocq-sulfur.plugin".

(*Ltac2 @external simpl_term_zero : constr -> constr * constr := "rocq-sulfur.plugin" "simpl_term_zero".
Ltac2 @external simpl_subst_zero : constr -> constr * constr := "rocq-sulfur.plugin" "simpl_subst_zero".*)

(*********************************************************************************)
(** *** Boilerplate for [rasimpl]. *)
(*********************************************************************************)

(** [Simplification x y] expresses the fact that [x] simplifies into [y].
    Typically [x] is a ground term and [y] is an evar, and a proof of 
    [Simplification x y] instantiates [y] with a simplified version of [x]. *)

(*Class NatSimplification (x y : nat) :=
  MkNatSimplification { nat_simplification : x = y }.

Class RenSimplification (x y : nat -> nat) :=
  MkRenSimplification { ren_simplification : x =₁ y }.

Class TermSimplification {T} (x y : T) := 
  MkTermSimplification { term_simplification : x = y }.

Class SubstSimplification {T} (x y : nat -> T) :=
  MkSubstSimplification { subst_simplification : x =₁ y }.

(** Helper function for [solve_simplification] which might leave unsolved 
    typeclass instances as shelved goals. *)
Ltac2 solve_simplification_aux () :=
  lazy_match! Control.goal () with 
  | TermSimplification ?t0 _ => 
    let (t0', eq0) := simpl_term_zero t0 in
    exact (MkTermSimplification _ $t0 $t0' $eq0)
  (*| RenSimplification ?r1 _ =>
    let (r1', eq1) := simpl_ren_one r1 in
    exact (MkRenSimplification _ $r1 $r1' $eq1)*)
  | SubstSimplification ?s0 _ =>
    let (s0', eq0) := simpl_subst_zero s0 in
    exact (MkSubstSimplification _ $s0 $s0' $eq0)
  end.

(** Solve a goal of the form [TermSimplification ?t _] or [SubstSimplification ?s _]. *)
Ltac solve_simplification := 
  ltac2:(solve_simplification_aux ()).

(*********************************************************************************)
(** *** [rasimpl]. *)
(*********************************************************************************)

(** Unfold constants related to terms and substitutions, typically before [rasimpl]. *)
Ltac aunfold := autounfold with asimpl_unfold.
  
(** Topdown version of [rasimpl]. *)
Ltac rasimpl_topdown := 
  (rewrite_strat (topdown (hints asimpl_topdown))) ; [| solve_simplification ..].

(** Outermost version of [rasimpl]. *)
Ltac rasimpl_outermost := 
  (rewrite_strat (outermost (hints asimpl_outermost))) ; [| solve_simplification ..].

(** Simplify in the goal. *)
Ltac rasimpl := 
  repeat aunfold ;
  repeat rasimpl_topdown ;
  repeat rasimpl_outermost.

(*********************************************************************************)
(** *** [rasimpl in H]. *)
(*********************************************************************************)

(** Unfold constants related to terms and substitutions, typically before [rasimpl in H]. *)
Tactic Notation "aunfold" "in" hyp(H) := autounfold with asimpl_unfold in H.
  
(** Topdown version of [rasimpl in H]. *)
Tactic Notation "rasimpl_topdown" "in" hyp(H) := 
  (rewrite_strat (topdown (hints asimpl_topdown)) in H) ; [| solve_simplification ..].

(** Outermost version of [rasimpl in H]. *)
Tactic Notation "rasimpl_outermost" "in" hyp(H) := 
  (rewrite_strat (outermost (hints asimpl_outermost)) in H) ; [| solve_simplification ..].

(** Simplify in a hypothesis [H]. *)
Tactic Notation "rasimpl" "in" hyp(H) := 
  repeat aunfold in H ;
  repeat rasimpl_topdown in H ;
  repeat rasimpl_outermost in H.*)

(** Tests. *)

Module G.
Sulfur Generate 
{{
  option : Functor
  list : Functor

  term : Type
  
  app : term -> (list (bind term in term)) -> term
  lam : (bind term in term) -> term
}}.

(*About ListNF.encode.
Print encoding.

Fixpoint vec_of_list' {A B} (f : A -> B) (xs : list A) : vec B (List.length xs) :=
  match xs with 
  | [] => vnil 
  | x :: xs => vcons (f x) (vec_of_list' f xs)
  end.

Definition list_encode {A B} (f : A -> B) (x : list A) : encoding ListNF.Shape ListNF.size B :=
  {| shape := List.length x ; elems := vec_of_list' f x |}.*)
  
Fixpoint reify (t : term) : @P.expr sign Kt :=
  match t with 
  | Var i => P.E_var i 
  | app t ts => 
    let t' := P.E_aterm (reify t) in 

    let ts' := @P.E_afunctor sign _ F1 
      (encode_shape list ts) 
      (encode_elems list (fun t => P.E_abind (P.E_aterm (reify t))) ts) 
    in
    
    @P.E_ctor sign Capp (P.E_al_cons t' (P.E_al_cons ts' P.E_al_nil))
  | lam t => @P.E_ctor sign Clam (P.E_al_cons (P.E_abind (P.E_aterm (reify t))) P.E_al_nil)
  end.
End G.

