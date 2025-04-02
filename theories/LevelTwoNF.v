From Prototype Require Import Prelude Sig LevelTwo.

(** This file defines normal forms of level two expressions [nf],
    as well as a function [normalize] which computes normal forms. *)

Module Make (S : Sig).
Module T := LevelTwo.Make (S).
Import T.

(*********************************************************************************)
(** *** Normal forms. *)
(*********************************************************************************)

(** A term/substitution is in normal form if and only if:
    - metavariables always appear to the left of a substitution or composition.
    - no other term appears to the left of a substitution or composition. *)
Inductive nf : forall {k s}, expr k s -> Prop :=
| nf_tvar (i : nat) : 
    nf (E_var i)
| nf_tctor c (al : args _) : 
    nf al -> nf (E_ctor c al) 
| nf_al_nil : 
    nf E_al_nil
| nf_al_cons {ty tys} (a : arg ty) (al : args tys) :
    nf a -> nf al -> nf (E_al_cons a al)
| nf_abase b x :
    nf (E_abase b x) 
| nf_aterm (t : term) :
    nf t -> nf (E_aterm t)
| nf_abind {ty} (a : arg ty) :
    nf a -> nf (E_abind a)
| nf_sshift {k} : 
    nf (↑k)
| nf_scons (t : term) (s : subst) : 
    nf t -> nf s -> nf (t .: s)
| nf_subst_t {k} (xt : mvar k S1) (s : subst) : 
    nf s -> nf (E_mvar xt [: s ])
| nf_subst_s i (xs : mvar K_s S2) (s : subst) :
    nf s -> nf (E_var i [: E_mvar xs >> s])
| nf_scomp k (xs : mvar K_s S2) (s : subst) :
    nf s -> nf (↑k >> E_mvar xs >> s).
Hint Constructors nf : core.

(** Technical detail: we need to describe a class of renaming expressions,
    which are a subset of explicit renamings which don't contain metavariables. *)
Inductive rexp : subst -> Prop :=
| rexp_shift k : rexp (↑k)
| rexp_cons i r : rexp r -> rexp (E_var i .: r).
Hint Constructors rexp : core.

(** Renaming expressions are in fact a subclass of normal forms. *)
Lemma rexp_impl_nf r : rexp r -> nf r.
Proof. intros H. induction H ; auto. Qed.

(*********************************************************************************)
(** *** Inversion tactic. *)
(*********************************************************************************)

(** Rocq's inversion tactic doesn't work well on hypotheses of the form [nf _].
    We thus prove a number of inversion lemmas by hand, and provide a custom
    tactic [inv_nf] which recursively inverts all [nf _] hypotheses. *)

Lemma inv_nf_ctor c (al : args _) : 
  nf (E_ctor c al) -> nf al.
Proof. intros H. inv H. repeat apply Eqdep.EqdepTheory.inj_pair2 in H1. now subst. Qed.

Lemma inv_nf_al_cons {ty tys} (a : arg ty) (al : args tys) :
  nf (E_al_cons a al) -> nf a /\ nf al.
Proof. intros H. inv H. repeat apply Eqdep.EqdepTheory.inj_pair2 in H2, H3. now subst. Qed.

Lemma inv_nf_aterm (t : term) :
  nf (E_aterm t) -> nf t.
Proof. intros H. inv H. assumption. Qed.

Lemma inv_nf_abind {ty} (a : arg ty) :
  nf (E_abind a) -> nf a.
Proof. intros H. inv H. apply Eqdep.EqdepTheory.inj_pair2 in H1. now subst. Qed.

(** This inversion lemma is a bit complex, because there are two cases
    and the second case is only possible when [t] is _not_ a substitution.
    We can usually use one of the simpler lemmas below. *)
Lemma inv_nf_subst {k} (t : expr k S1) (s : subst) :
  nf (t[: s ]) -> 
    (exists xt, t = E_mvar xt /\ nf s) \/ 
    (match k as k0 return expr k0 S1 -> Prop with 
     | K_t => fun t => exists l xs s', t = E_var l /\ s = E_mvar xs >> s' /\ nf s'
     | _ => fun _ => False
     end) t.
Proof.
intros H. inv H.
- left. apply Eqdep.EqdepTheory.inj_pair2 in H0. subst. eauto.
- right. apply Eqdep.EqdepTheory.inj_pair2 in H4. subst. eexists. eauto.
Qed.

Lemma inv_nf_scons (t : term) (s : subst) :
  nf (t .: s) -> nf t /\ nf s.
Proof. intros H. inv H. auto. Qed.

Lemma inv_nf_scomp (s1 s2 : subst) :
  nf (s1 >> s2) -> exists l xs, s1 = ↑l >> E_mvar xs /\ nf s2.
Proof. intros H. inv H. eauto. Qed.

Lemma inv_rexp_cons (i : nat) (r : subst) :
  rexp (E_var i .: r) -> rexp r.
Proof. intros H. inv H. assumption. Qed.

Lemma inv_nf_subst_var i s : 
  nf (E_var i [: s ]) -> 
    exists (xs : mvar K_s S2) (s' : subst), s = E_mvar xs >> s' /\ nf s'.
Proof. 
intros H. apply inv_nf_subst in H.
destruct H as [(xt & H3 & H4) | H2] ; [inv H3 |].
destruct H2 as (l & xs & s' & H1 & H2 & H3).
subst. eauto.
Qed.

Lemma inv_nf_subst_mvar {k} (xt : mvar k S1) s : 
  nf (E_mvar xt [: s ]) -> nf s.
Proof. 
intros H. apply inv_nf_subst in H.
destruct H as [(xt' & H3 & H4) | H2] ; [assumption|].
dependent destruction k ; try easy.
destruct H2 as (l & xs & s' & H1 & H2 & H3). inv H1.
Qed.

Lemma inv_nf_subst_ctor c al s : 
  nf (E_ctor c al [: s ]) -> False.
Proof. 
intros H. apply inv_nf_subst in H.
destruct H as [(xt & H3 & H4) | H2] ; [inv H3 |].
destruct H2 as (l & xs & s' & H1 & H2 & H3). inv H1.
Qed.

Lemma inv_nf_subst_al_nil s : 
  nf (E_al_nil [: s ]) -> False.
Proof. 
intros H. apply inv_nf_subst in H.
destruct H as [(xt & H3 & H4) | H2] ; [inv H3 | auto].
Qed.

Lemma inv_nf_subst_al_cons {ty tys} (a : arg ty) (al : args tys) (s : subst) : 
  nf (E_al_cons a al [: s ]) -> False.
Proof. 
intros H. apply inv_nf_subst in H.
destruct H as [(xt & H3 & H4) | H2] ; [inv H3 | auto].
Qed.

Lemma inv_nf_subst_abase b x s : 
  nf (E_abase b x [: s ]) -> False.
Proof. 
intros H. apply inv_nf_subst in H.
destruct H as [(xt & H3 & H4) | H2] ; [inv H3 | auto].
Qed.

Lemma inv_nf_subst_aterm t s : 
  nf (E_aterm t [: s ]) -> False.
Proof. 
intros H. apply inv_nf_subst in H.
destruct H as [(xt & H3 & H4) | H2] ; [inv H3 | auto].
Qed.

Lemma inv_nf_subst_abind {ty} (a : arg ty) s : 
  nf (E_abind a [: s ]) -> False.
Proof. 
intros H. apply inv_nf_subst in H.
destruct H as [(xt & H3 & H4) | H2] ; [inv H3 | auto].
Qed.

Lemma inv_nf_subst_subst {k} (t : expr k S1) s1 s2 : 
  nf (t [: s1 ] [: s2 ]) -> False.
Proof. 
intros H. apply inv_nf_subst in H.
destruct H as [(xt & H3 & H4) | H2].
- inv H3.
- dependent destruction k ; auto. destruct H2 as (l & xs & s' & H1 & H2 & H3).
  inv H1.
Qed.

(** Invert a single [nf _] hypothesis. We can extend this to handle more
    cases as needed. *)
Ltac inv_nf_once :=
  match goal with 
  | [ H : nf (E_ctor _ _) |- _ ] => apply inv_nf_ctor in H
  | [ H : nf E_al_nil |- _ ] => clear H
  | [ H : nf (E_al_cons _ _) |- _ ] => 
    let H1 := fresh "H" in 
    let H2 := fresh "H" in 
    apply inv_nf_al_cons in H ;
    destruct H as [H1 H2]
  | [ H : nf (E_abase _ _) |- _ ] => clear H
  | [ H : nf (E_aterm _) |- _ ] => apply inv_nf_aterm in H
  | [ H : nf (E_abind _) |- _ ] => apply inv_nf_abind in H
  | [ H : nf (↑_) |- _ ] => clear H
  | [ H : nf (_ .: _) |- _ ] => apply inv_nf_scons in H
  | [ H : nf (_ >> _) |- _ ] => 
    apply inv_nf_scomp in H ;
    let l := fresh "l" in 
    let xs := fresh "xs" in 
    let H1 := fresh "H" in 
    let H2 := fresh "H" in 
    destruct H as (l & xs & H1 & H2)
  | [ H : nf (E_var _ [: _ ]) |- _ ] =>
    apply inv_nf_subst_var in H ; 
    let xs := fresh "xs" in 
    let s := fresh "s" in 
    let H1 := fresh "H" in 
    let H2 := fresh "H" in 
    destruct H as (xs & s & H1 & H2)
  | [ H : nf (_ [: _ ]) |- _ ] =>
    first [ now apply inv_nf_subst_ctor in H 
          | now apply inv_nf_subst_al_nil in H 
          | now apply inv_nf_subst_al_cons in H 
          | now apply inv_nf_subst_abase in H 
          | now apply inv_nf_subst_aterm in H 
          | now apply inv_nf_subst_abind in H
          | now apply inv_nf_subst_subst in H
          | apply inv_nf_subst_mvar in H
          | apply inv_nf_subst in H ]
  end.

(** Recursively invert all hypotheses of the form [nf _]. *)
Ltac inv_nf := repeat inv_nf_once.

(*********************************************************************************)
(** *** Normalization. *)
(*********************************************************************************)

(** Head of a normal form substitution. *)
Equations head (s : subst) : term :=
head (↑ k) := E_var k ;
head (t .: _) := t ;
head (↑k >> E_mvar xs >> s) := E_var k [: E_mvar xs >> s ] ;
head s := E_var 0 [: s ].

Lemma head_sound s : head s =σ E_var 0 [: s ].
Proof. 
funelim (head s) ; simp head in * ; auto.
- rewrite aeq_sshift_var. now rewrite <-plus_n_O.
- rewrite <-(aeq_subst_subst (E_var 0)), <-aeq_subst_subst.
  apply e_subst_proper ; [|reflexivity].
  rewrite <-aeq_subst_subst, aeq_sshift_var, <-plus_n_O.
  reflexivity.    
Qed.

Lemma head_rexp s : rexp s -> exists i, head s = E_var i.
Proof. intros H. dependent elimination H ; simp head ; eauto. Qed.

Lemma head_nf s : nf s -> nf (head s).
Proof. intros H. dependent elimination H ; simp head ; auto. Qed.

(** Tail of a normal form substitution. *)
Equations tail (s : subst) : subst :=
tail (↑k) := ↑(S k) ;
tail (_ .: s) := s ;
tail (↑k >> E_mvar xs >> s) := ↑(S k) >> E_mvar xs >> s ;
tail s := ↑1 >> s.  

Lemma tail_sound s : tail s =σ ↑1 >> s.
Proof. 
funelim (tail s) ; simp tail in * ; auto.
- now rewrite aeq_sshift_succ_l.
- repeat rewrite aeq_assoc. rewrite aeq_sshift_succ_l. reflexivity.
Qed.

Lemma tail_rexp s : rexp s -> rexp (tail s).
Proof. intros H. dependent elimination H ; simp tail ; auto. Qed.

Lemma tail_nf s : nf s -> nf (tail s).
Proof. intros H. dependent elimination H ; simp tail ; auto. Qed.

(** Drop the first [k] elements of a substitution. *)
Equations drop (k : nat) (s : subst) : subst :=
drop 0 s := s ;
drop (S k) s := tail (drop k s).

Lemma drop_sound k s : drop k s =σ ↑k >> s.
Proof. 
funelim (drop k s) ; auto. rewrite tail_sound, H. 
now rewrite aeq_assoc, aeq_sshift_succ_l.
Qed.

Lemma drop_rexp k s : rexp s -> rexp (drop k s).
Proof. intros H. funelim (drop k s) ; auto. apply tail_rexp. auto. Qed.
    
Lemma drop_nf k s : nf s -> nf (drop k s).
Proof. intros H. funelim (drop k s) ; auto. apply tail_nf. auto. Qed.

(** Apply a normal form substitution to a variable. *)
Definition vsubst (i : nat) (s : subst) : term :=
  head (drop i s).
  
Lemma vsubst_sound i s : vsubst i s =σ E_var i [: s ].
Proof. 
unfold vsubst. rewrite head_sound, drop_sound.
rewrite <-aeq_subst_subst, aeq_sshift_var, <-plus_n_O. reflexivity.
Qed.

Lemma vsubst_nf i s : nf s -> nf (vsubst i s).
Proof. intros H. unfold vsubst. now apply head_nf, drop_nf. Qed.

Lemma vsubst_rexp i s : rexp s -> exists i', vsubst i s = E_var i'.
Proof. intros H. unfold vsubst. apply head_rexp. now apply drop_rexp. Qed.

(** Composition of renaming expressions. *)
Equations rcomp (r1 r2 : subst) : subst :=
rcomp (↑k) r := drop k r  ;
rcomp (E_var i .: r1) r2 := vsubst i r2 .: rcomp r1 r2  ;
rcomp r1 r2 := r1 >> r2.

Lemma rcomp_sound r1 r2 : rcomp r1 r2 =σ r1 >> r2.
Proof. funelim (rcomp r1 r2) ; simp drop ; auto.
- now rewrite drop_sound.
- now rewrite H, vsubst_sound, aeq_distrib.
Qed.  

Lemma rcomp_rexp r1 r2 : rexp r1 -> rexp r2 -> rexp (rcomp r1 r2).
Proof. 
intros H1 H2. funelim (rcomp r1 r2) ; simp rcomp ; try (inv H1).
- now apply drop_rexp.
- destruct (vsubst_rexp i r2 H2) as [i' ->]. constructor.
  apply inv_rexp_cons in H1. now apply H.
Qed.

(** Lift a renaming expression through a binder. *)
Definition up_rexp (r : subst) : subst :=
  E_var 0 .: rcomp r (↑1).
  
Lemma up_rexp_sound r : up_rexp r =σ up_subst r.
Proof. unfold up_rexp. simp up_subst. now rewrite rcomp_sound. Qed.

Lemma up_rexp_rexp r : rexp r -> rexp (up_rexp r).
Proof. intros H. unfold up_rexp. constructor. now apply rcomp_rexp. Qed. 

(** Apply a renaming expression to a normal form term. *)
Equations rsubst {k} (t : expr k S1) (r : subst) : expr k S1 :=
rsubst (E_var i) r := vsubst i r ;
rsubst (E_ctor c al) r := E_ctor c (rsubst al r) ;
rsubst E_al_nil r := E_al_nil ;
rsubst (E_al_cons a al) r := E_al_cons (rsubst a r) (rsubst al r) ;
rsubst (E_abase b x) r := E_abase b x ;
rsubst (E_aterm t) r := E_aterm (rsubst t r) ;
rsubst (E_abind a) r := E_abind (rsubst a (up_rexp r)) ; 
rsubst (E_mvar xt [: s ]) r := E_mvar xt [: sr_comp s r ] ;
rsubst (E_var i [: E_mvar xs >> s]) r := E_var i [: E_mvar xs >> sr_comp s r ] ;
rsubst t r := t [: r ]
(** Compose a normal form substitution with a renaming expression. *)
with sr_comp (s r : subst) : subst :=
sr_comp (↑k) r := drop k r ;
sr_comp (t .: s) r := rsubst t r .: sr_comp s r ;
sr_comp (↑k >> E_mvar xs >> s) r := ↑k >> E_mvar xs >> sr_comp s r ;
sr_comp s r := s >> r.

Lemma rsubst_sr_comp_sound : 
  (forall k t r, @rsubst k t r =σ t [: r ]) *
  (forall s r, sr_comp s r =σ s >> r).
Proof.
apply rsubst_elim with 
  (P := fun _ t r res => res =σ t [: r ])
  (P0 := fun s r res => res =σ s >> r).
all: auto.
- intros i r. now rewrite vsubst_sound.
- intros c al r ->. now rewrite aeq_subst_ctor.
- intros ty tys a al r -> ->. now rewrite aeq_subst_al_cons.
- intros t r ->. now rewrite aeq_subst_aterm.
- intros ty a r ->. rewrite up_rexp_sound. now rewrite aeq_subst_abind.
- intros i xs s r ->. now rewrite aeq_subst_subst, aeq_assoc.
- intros k xt s r ->. now rewrite aeq_subst_subst.
- intros k r. now rewrite drop_sound.
- intros t s r -> ->. now rewrite aeq_distrib.
- intros k xs s r ->. now rewrite aeq_assoc.
Qed.   

Lemma rsubst_sr_comp_nf : 
  (forall k t r, nf t -> rexp r -> nf (@rsubst k t r)) *
  (forall s r, nf s -> rexp r -> nf (sr_comp s r)).
Proof. 
apply rsubst_elim with 
  (P := fun _ t r res => nf t -> rexp r -> nf res)
  (P0 := fun s r res => nf s -> rexp r -> nf res).
all: try (intros ; inv_nf ; solve [ easy | intuition ]).
- intros i r H1 H2. now apply vsubst_nf, rexp_impl_nf.
- intros ty a r H1 H2 H3. inv_nf. constructor.
  apply H1 ; auto. now apply up_rexp_rexp.
- intros i xs s r H1 H2 H3. inv_nf. constructor. apply H1 ; auto. now inv H.
- intros k r H1 H2. now apply drop_nf, rexp_impl_nf.
Qed.      

(** Lift a normal form substitution through a binder. *)
Definition up_nf (s : subst) : subst := 
  E_var 0 .: sr_comp s (↑1).

Lemma up_nf_sound s : up_nf s =σ up_subst s.
Proof. unfold up_nf. simp up_subst. now destruct rsubst_sr_comp_sound as [_ ->]. Qed.

Lemma up_nf_nf s : nf s -> nf (up_nf s).
Proof. 
intros H. unfold up_nf. constructor ; auto. 
destruct rsubst_sr_comp_nf as [_ H1]. auto. 
Qed. 

(** Apply a normal form substitution to a normal form term. *)
Equations ssubst {k} (t : expr k S1) (r : subst) : expr k S1 :=
ssubst (E_var i) s := vsubst i s ;
ssubst (E_ctor c al) s := E_ctor c (ssubst al s) ;
ssubst E_al_nil _ := E_al_nil ;
ssubst (E_al_cons a al) s := E_al_cons (ssubst a s) (ssubst al s) ;
ssubst (E_abase b x) _ := E_abase b x ;
ssubst (E_aterm t) s := E_aterm (ssubst t s) ;
ssubst (E_abind a) s := E_abind (ssubst a (up_nf s)) ; 
ssubst (E_mvar xt [: s1 ]) s2 := E_mvar xt [: scomp s1 s2 ] ;
ssubst (E_var i [: E_mvar xs >> s1]) s2 := E_var i [: E_mvar xs >> scomp s1 s2 ] ;
ssubst t s := t [: s ]
(** Compose two normal form substitutions. *)
with scomp (s r : subst) : subst :=
scomp (↑k) s := drop k s ;
scomp (t .: s1) s2 := ssubst t s2 .: scomp s1 s2 ;
scomp (↑k >> E_mvar xs >> s1) s2 := ↑k >> E_mvar xs >> scomp s1 s2 ;
scomp s1 s2 := s1 >> s2.

Lemma ssubst_scomp_sound :
  (forall k (t : expr k S1) (s : subst), ssubst t s =σ t[: s ]) *
  (forall (s1 s2 : subst), scomp s1 s2 =σ s1 >> s2).
Proof. 
apply ssubst_elim with 
  (P := fun _ t s res => res =σ t[: s ]) 
  (P0 := fun s1 s2 res => res =σ s1 >> s2).
all: try reflexivity.
- intros i s. now rewrite vsubst_sound.
- intros c args s ->. now rewrite aeq_subst_ctor.
- intros s. now rewrite aeq_subst_al_nil.
- intros ty tys a args s -> ->. now rewrite aeq_subst_al_cons.
- intros b x s. now rewrite aeq_subst_abase.
- intros t s ->. now rewrite aeq_subst_aterm.
- intros ty a s ->. now rewrite aeq_subst_abind, up_nf_sound. 
- intros i xs s1 s2 ->. now rewrite aeq_subst_subst, aeq_assoc.
- intros k xt s1 s2 ->. now rewrite aeq_subst_subst.
- intros k s. now rewrite drop_sound.
- intros t s1 s2 -> ->. now rewrite aeq_distrib.
- intros k xs s1 s2 ->. now rewrite aeq_assoc.
Qed.

Lemma ssubst_scomp_nf :
  (forall k (t : expr k S1) (s : subst), nf t -> nf s -> nf (ssubst t s)) *
  (forall (s1 s2 : subst), nf s1 -> nf s2 -> nf (scomp s1 s2)).
Proof. 
apply ssubst_elim with 
  (P := fun _ t s res => nf t -> nf s -> nf res) 
  (P0 := fun s1 s2 res => nf s1 -> nf s2 -> nf res).
all: try (intros ; inv_nf ; solve [ easy | intuition ]).
- intros i s H1 H2. now apply vsubst_nf.
- intros ty a s H1 H2 H3. constructor. inv_nf. apply H1 ; auto. now apply up_nf_nf.
- intros i xs s1 s2 H1 H2 H3. constructor. inv_nf. apply H1 ; auto. now inv H.
- intros k s H1 H2. now apply drop_nf.
Qed.  

(** Normalize a metavariable. *)
Equations normalize_mvar {k s} (x : mvar k s) : expr k s :=
@normalize_mvar K_s S2 xs := ↑0 >> E_mvar xs >> sid ;
@normalize_mvar _ S1 xt := E_mvar xt [: sid ] ;
@normalize_mvar _ _ x := E_mvar x. 

Lemma normalize_mvar_sound {k s} (x : mvar k s) : 
  normalize_mvar x =σ E_mvar x.
Proof. funelim (normalize_mvar x) ; auto. now rewrite aeq_sid_l, aeq_sid_r. Qed.

(** Reduce an expression to normal form. *)
Equations normalize {k s} (e : expr k s) : expr k s :=
normalize (E_var i) := E_var i ;
normalize (E_ctor c al) := E_ctor c (normalize al) ;
normalize E_al_nil := E_al_nil ;
normalize (E_al_cons a al) := E_al_cons (normalize a) (normalize al) ;
normalize (E_abase b x) := E_abase b x ;
normalize (E_aterm t) := E_aterm (normalize t) ;
normalize (E_abind a) := E_abind (normalize a) ;
normalize (t [: s ]) := ssubst (normalize t) (normalize s) ;
normalize (↑k) := ↑k ;
normalize (t .: s) := normalize t .: normalize s ;
normalize (s1 >> s2) := scomp (normalize s1) (normalize s2) ;
normalize (E_mvar x) := normalize_mvar x.

Lemma normalize_sound {k s} (e : expr k s) : normalize e =σ e.
Proof.
funelim (normalize e) ; try (now auto).
- destruct ssubst_scomp_sound as [-> _]. now rewrite H, H0.
- destruct ssubst_scomp_sound as [_ ->]. now rewrite H, H0.
- now rewrite normalize_mvar_sound.
Qed.

Lemma normalize_nf {k s} (e : expr k s) : nf (normalize e).
Proof.
funelim (normalize e) ; try (now auto).
- destruct ssubst_scomp_nf as [H1 _] ; apply H1 ; auto.
- destruct ssubst_scomp_nf as [_ H1] ; apply H1 ; auto.
- admit.
Admitted.

End Make.