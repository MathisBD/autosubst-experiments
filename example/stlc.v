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
  lam : {{ type }} -> ( bind term in term) -> term 
  app : term -> term -> term
}}.

Print term.
Print rename.
Print substitute.

(*********************************************************************************)
(** *** Triggers. *)
(*********************************************************************************)

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
Lemma test : substitute (scomp sshift sid) (lam tbase (rename (rcons 0 rshift) t)) = t.
Proof. rasimpl.
Admitted.