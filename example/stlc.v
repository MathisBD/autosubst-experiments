From Prototype Require Export All.

(*********************************************************************************)
(** *** Generate the term inductive and lemmas. *)
(*********************************************************************************)

Inductive type :=
| tbase : type 
| tarrow : type -> type.

Autosubst Generate 
{{
  term : Type
  lam : {{ type }} -> (bind term in term) -> term 
  app : term -> term -> term
}}.

Print term.
Print rename.
Print substitute.

(*********************************************************************************)
(** *** Triggers. *)
(*********************************************************************************)

(** At the moment you need to specify when [rasimpl] should trrigger  
    (hopefully we can improve this in the future). 
    
    This amounts to adding rewrite hints 
    in databases [asimpl_topdown] or [asimpl_outermost] depending on the rewrite strategy
    you want. The rewrite lemmas should have hypotheses of the form [TermSimplification _ _]
    or [SubstSimplification _ _]. *)

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

(** An example. *)
Axiom t : term.
Lemma test (H : rename (rcons 0 rshift) t = t) : substitute (up_subst Var) t = t.
Proof. rasimpl in H. rasimpl.
Admitted.