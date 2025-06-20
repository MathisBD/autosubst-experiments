From Sulfur Require Export All.
From GhostTT Require Import BasicAST. 

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

Axiom r : ren.
Axiom t : term.
Axiom s : subst.
Lemma test (Htest : substitute (up_subst Var) t = t) : substitute sid t = t.
Proof. rasimpl in Htest. rasimpl.
Admitted.

