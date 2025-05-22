From Coq Require Import Lia String.
From Ltac2 Require Import RedFlags Printf.
From Prototype Require Export Prelude.
From Prototype Require Import RASimpl.
From GhostTT Require Import BasicAST. 

Module O := LevelOne.
Module T := LevelTwo.
Module Clean := LevelTwoClean.

(*********************************************************************************)
(** *** Generate all operations and lemmas. *)
(*********************************************************************************)

Autosubst Generate 
{{
  term : Type
  
  Sort : {{mode}} -> {{level}} -> term
  
  Pi : {{level}} -> {{level}} -> {{mode}} -> {{mode}} -> term -> (bind term in term) -> term
  lam : {{mode}} -> term -> (bind term in term) -> term
  app : term -> term -> term
  
  Erased : term -> term
  hide : term -> term
  reveal : term -> term -> term -> term
  Reveal : term -> term -> term
  toRev : term -> term -> term -> term
  fromRev : term -> term -> term -> term
  
  gheq : term -> term -> term -> term
  ghrefl : term -> term -> term
  ghcast : term -> term -> term -> term -> term -> term -> term
  
  tbool : term
  ttrue : term
  tfalse : term
  tif : {{mode}} -> term -> term -> term -> term -> term
  
  tnat : term
  tzero : term
  tsucc : term -> term
  tnat_elim : {{mode}} -> term -> term -> term -> term -> term
  
  tvec : term -> term -> term
  tvnil : term -> term
  tvcons : term -> term -> term -> term
  tvec_elim : {{mode}} -> term -> term -> term -> term -> term -> term -> term
  
  bot : term
  bot_elim : {{mode}} -> term -> term -> term
}}.

(*********************************************************************************)
(** *** Glue code (eventually should be generic). *)
(*********************************************************************************)

(** Simplify a level zero term. *)
Ltac2 simpl_term_zero (t0 : constr) : constr * constr :=
  (* Reify Level 0 -> Level 1. *)
  let (t1, p1) := reify_term t0 in 
  (* Simplify on level 1. *)
  let (t1', p2) := simpl_term_one constr:(sig) t1 in
  (* Eval Level 1 -> Level 0. *)
  let (t0', p3) := eval_term t1' in
  (* [eq0 : t0 = t0']. *)
  let eq0 := constr:(transitivity
    (symmetry $p1) 
    (transitivity (f_equal (eval Sig.Kt) $p2) $p3)) 
  in
  (t0', eq0).
  
Lemma congr_seval {s1 s2} : 
  s1 =₁ s2 -> seval s1 =₁ seval s2.
Proof. intros H i. unfold seval. now rewrite H. Qed. 

(** Simplify a level zero substitution. *)
Ltac2 simpl_subst_zero (s0 : constr) : constr * constr :=
  (* Reify Level 0 -> Level 1. *)
  let (s1, p1) := reify_subst s0 in 
  (* Simplify on level 1. *)
  let (s1', p2) := simpl_subst_one constr:(sig) s1 in
  (* Eval Level 1 -> Level 0. *)
  let (s0', p3) := eval_subst s1' in
  (* [eq0 : s0 =₁ s0']. *)
  let eq0 := constr:(transitivity
    (symmetry $p1) 
    (transitivity (congr_seval $p2) $p3)) 
  in
  (s0', eq0).

(** Solve a goal of the form [TermSimplification ?t _] or [SubstSimplification ?s _]. *)
Ltac2 solve_simplification () :=
  lazy_match! Control.goal () with 
  | TermSimplification ?t0 _ => 
    let (t0', eq0) := simpl_term_zero t0 in
    exact (MkTermSimplification _ $t0 $t0' $eq0)
  | SubstSimplification ?s0 _ =>
    let (s0', eq0) := simpl_subst_zero s0 in
    exact (MkSubstSimplification _ $s0 $s0' $eq0)
  end.

Ltac rasimpl_topdown := 
  (rewrite_strat (topdown (hints asimpl_topdown))) ; [| ltac2:(solve_simplification ()) ..].

Ltac rasimpl_outermost := 
  (rewrite_strat (outermost (hints asimpl_outermost))) ; [| ltac2:(solve_simplification ()) ..].

(** Main simplification tactic. *)
Ltac rasimpl := 
  repeat rasimpl_topdown ;
  repeat rasimpl_outermost.

(** Trigger [rasimpl] on [rename _ _]. *)
Lemma autosubst_simpl_term_rename (r : ren) (t res : term) :
  TermSimplification (rename r t) res -> rename r t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_rename : asimpl_topdown.

(** Trigger [rasimpl] on [substitute _ _]. *)
Lemma autosubst_simpl_term_substitute (s : subst) (t res : term) :
  TermSimplification (substitute s t) res -> substitute s t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_substitute : asimpl_topdown.

Axiom r : ren.
Axiom s : subst.
Axiom t : term.
Axiom i : nat.
Axiom f : term -> term.
Lemma test : substitute sid (f (substitute sid t)) = Var 0.
Proof. rasimpl.
Admitted.