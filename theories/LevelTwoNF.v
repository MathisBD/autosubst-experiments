From Prototype Require Import Prelude Sig LevelTwo.

(** This file defines normal forms of level two expressions [nf],
    as well as a function [reduce] which computes normal forms. *)

Module Make (S : Sig).
Module T := LevelTwo.Make (S).
Import T.

#[local] Notation "↑ k" := (T_sshift k) (at level 0).
#[local] Notation "t .: s" := (T_scons t s) (at level 60, right associativity).
#[local] Notation "s1 >> s2" := (T_scomp s1 s2) (at level 50, left associativity).
#[local] Notation "t '[:' s ']'" := (T_subst t s) (at level 15, s at level 0, no associativity).

(*********************************************************************************)
(** *** Normal forms. *)
(*********************************************************************************)

(** A term/substitution is in normal form if and only if:
    - metavariables always appear to the left of a substitution or composition.
    - no other term appears to the left of a substitution or composition. *)
Inductive nf : forall {k s}, term k s -> Prop :=
| nf_tvar {n} (i : fin n) : 
    nf (T_var i)
| nf_tctor {n} c (args : term _ (S1 n)) : 
    nf args -> nf (T_ctor c args) 
| nf_al_nil {n} : 
    nf (@T_al_nil n)
| nf_al_cons {n ty tys} (a : term (K_a ty) (S1 n)) (args : term (K_al tys) (S1 n)) :
    nf a -> nf args -> nf (T_al_cons a args)
| nf_abase {n} b x :
    nf (@T_abase n b x) 
| nf_aterm {n} (t : term K_t (S1 n)) :
    nf t -> nf (T_aterm t)
| nf_abind {n ty} (a : term (K_a ty) (S1 (S n))) :
    nf a -> nf (T_abind a)
| nf_sshift {n k} : 
    nf (@T_sshift n k)
| nf_scons {n m} (t : term K_t (S1 m)) (s : term K_s (S2 n m)) : 
    nf t -> nf s -> nf (t .: s)
| nf_subst_t {n m k} (xt : mvar k (S1 n)) (s : term K_s (S2 n m)) : 
    nf s -> nf (T_mvar xt [: s ])
| nf_subst_s {n m o k} (xs : mvar K_s (S2 (k + S n) m)) (s : term K_s (S2 m o)) :
    nf s -> nf (T_var fin_zero [: ↑k >> T_mvar xs ][: s])
| nf_scomp {n m o k} (xs : mvar K_s (S2 (k + n) m)) (s : term K_s (S2 m o)) :
    nf s -> nf (↑k >> T_mvar xs >> s).
Hint Constructors nf : core.

(** Technical detail: we need a type of renaming expression. *)
Inductive rexp : forall {n m}, term K_s (S2 n m) -> Prop :=
| rexp_shift {n k} : 
    rexp (@T_sshift n k)
| rexp_cons {n m} (i : fin m) (r : term K_s (S2 n m)) :
    rexp r -> rexp (T_var i .: r).
Hint Constructors rexp : core.

(*********************************************************************************)
(** *** Inversion lemmas. *)
(*********************************************************************************)

Lemma inv_nf_tctor {n} c (args : term (K_al _) (S1 n)) : 
  nf (T_ctor c args) -> nf args.
Proof. intros H. inv H. repeat apply Eqdep.EqdepTheory.inj_pair2 in H2. now subst. Qed.

Lemma inv_nf_al_cons {ty tys n} (a : term (K_a ty) (S1 n)) (args : term (K_al tys) (S1 n)) :
  nf (T_al_cons a args) -> nf a /\ nf args.
Proof. intros H. inv H. repeat apply Eqdep.EqdepTheory.inj_pair2 in H3, H5. now subst. Qed.

Lemma inv_nf_aterm {n} (t : term K_t (S1 n)) :
  nf (T_aterm t) -> nf t.
Proof. intros H. inv H. repeat apply Eqdep.EqdepTheory.inj_pair2 in H1. now subst. Qed.

Lemma inv_nf_abind {n ty} (a : term (K_a ty) (S1 (S n))) :
  nf (T_abind a) -> nf a.
Proof. intros H. inv H. repeat apply Eqdep.EqdepTheory.inj_pair2 in H2. now subst. Qed.

Lemma inv_nf_subst_t {n m k} (t : term k (S1 n)) (s : term K_s (S2 n m)) :
  nf (t[: s ]) -> 
    (exists xt, t = T_mvar xt /\ nf s) \/ 
    (match k as k0 return forall n, term k0 (S1 n) -> Prop with 
     | K_t => fun n t =>
       exists l (xs : mvar K_s (S2 (l + S n) n)), 
         t = @T_var (S n) (@fin_zero n) [: @T_sshift (S n) l >> T_mvar xs ] /\ nf s
     | _ => fun _ _ => False
     end) n t.
Proof.
intros H. inv H.
- left. repeat apply Eqdep.EqdepTheory.inj_pair2 in H4, H5. subst. eauto.
- right. repeat apply Eqdep.EqdepTheory.inj_pair2 in H6, H7. subst.
  exists k0. exists xs0. split ; auto. 
Admitted.

Lemma inv_nf_scons {n m} (t : term K_t (S1 m)) (s : term K_s (S2 n m)) :
  nf (t .: s) -> nf t /\ nf s.
Proof. 
intros H. inv H. 
repeat apply Eqdep.EqdepTheory.inj_pair2 in H2.  
repeat apply Eqdep.EqdepTheory.inj_pair2 in H3. now subst.
Qed.

Lemma inv_nf_scomp {n m o} (s1 : term K_s (S2 n m)) (s2 : term K_s (S2 m o)) :
  nf (s1 >> s2) -> exists l xs, s1 = ↑l >> T_mvar xs /\ nf s2.
Proof. intros H. inv H. repeat apply Eqdep.EqdepTheory.inj_pair2 in H4, H5. subst. eauto. Qed.

Lemma inv_rexp_cons {n m} (i : fin m) (r : term K_s (S2 n m)) :
  rexp (T_var i .: r) -> rexp r.
Proof. intros H. inv H. repeat apply Eqdep.EqdepTheory.inj_pair2 in H4. now subst. Qed.

(*********************************************************************************)
(** *** Operations on normal forms. *)
(*********************************************************************************)

(** Head of a normal form substitution. *)
Equations head {n m} (s : term K_s (S2 (S n) m)) : term K_t (S1 m) :=
head (↑ k) := T_var (fin_weaken k fin_zero) ;
head (t .: _) := t ;
head (↑k >> T_mvar xs >> s) := T_var fin_zero [: ↑k >> T_mvar xs ] [: s ] ;
head s := T_var fin_zero [: s ].

Lemma head_sound {n m} (s : term K_s (S2 (S n) m)) :
  head s =σ T_var fin_zero [: s ].
Proof. funelim (head s) ; simp head in * ; auto. Qed.

Lemma head_nf {n m} (s : term K_s (S2 (S n) m)) :
  nf s -> nf (head s).
Proof. intros H. dependent elimination H ; simp head ; auto. Qed.

(** Tail of a normal form substitution. *)
Equations tail {n m} (s : term K_s (S2 (S n) m)) : term K_s (S2 n m) :=
tail (↑k) := sshift_succ k ;
tail (_ .: s) := s ;
tail (↑k >> T_mvar xs >> s) := sshift_succ k >> T_mvar xs >> s ;
tail s := ↑1 >> s.

Lemma tail_sound {n m} (s : term K_s (S2 (S n) m)) :
  tail s =σ ↑1 >> s.
Proof. 
funelim (tail s) ; simp tail in * ; auto.
- now rewrite aeq_sshift_succ_l.
- repeat rewrite aeq_assoc. now rewrite aeq_sshift_succ_l.
Qed.

Lemma sshift_succ_nf {n} k : nf (@sshift_succ n k).
Proof.
funelim (sshift_succ k) ; simp sshift_succ in * ; auto.
- apply (@nf_sshift n 1).
-   

Lemma tail_nf {n m} (s : term K_s (S2 (S n) m)) :
  nf s -> nf (tail_nf s).
Proof. 
intros H. dependent elimination H ; simp tail_nf ; auto.

 Admitted.

(** Apply a normal form substitution to a variable. *)
Equations subst_var_nf {n m} (i : fin n) (s : term K_s (S2 n m)) : term K_t (S1 m) :=
subst_var_nf fin_zero s := head_nf s ;
subst_var_nf (fin_succ i) s := subst_var_nf i (tail_nf s).

Lemma subst_var_nf_sound {n m} (i : fin n) (s : term K_s (S2 n m)) :
  subst_var_nf i s =σ T_var i [: s ].
Proof. 
funelim (subst_var_nf i s).
- now rewrite head_nf_sound.
- rewrite H. rewrite tail_nf_sound. rewrite <-aeq_subst_subst, aeq_sshift_var.
  reflexivity.
Qed.

Lemma subst_var_nf_preserve {n m} (i : fin n) (s : term K_s (S2 n m)) :
  nf s -> nf (subst_var_nf i s).
Proof. 
intros H. funelim (subst_var_nf i s) ; simp subst_var_nf.
- now apply head_nf_preserve.
- apply H. now apply tail_nf_preserve.
Qed.

Axiom todo : forall {A}, A.

(** Composition of renaming expressions. *)
Equations comp_rexp {n m o} (r1 : term K_s (S2 n m)) (r2 : term K_s (S2 m o)) : term K_s (S2 n o) :=
comp_rexp (@T_sshift n 0) (@T_scons ?(n) o (@T_var ?(o) i2) r2) := todo ;
comp_rexp r1 r2 := r1 >> r2.

(*
↑k [>>] ↑1 := ↑(S k)
(t .: s) [>>] ↑1 := t [ ↑1 ] .: s [>>] ↑1
(n^ζ >> s) [>>] ↑1 := n^ζ >> (s [>>] ↑1)

i[↑1] := fin_succ i


*)

Inductive nf_ren : 

(** Apply a normal form substitution to a normal form term. *)
Equations subst_nf {k n m} (t : term k (S1 n)) (s : term K_s (S2 n m)) : term k (S1 m) by struct t :=
subst_nf (T_var i) s := subst_var_nf i s ;
subst_nf (T_ctor c args) s := T_ctor c (subst_nf args s) ;
subst_nf T_al_nil _ := T_al_nil ;
subst_nf (T_al_cons a args) s := T_al_cons (subst_nf a s) (subst_nf args s) ;
subst_nf (T_abase b x) s := T_abase b x ;
subst_nf (T_aterm t) s := T_aterm (subst_nf t s) ;
subst_nf (T_abind a) s := T_abind (subst_nf a (T_var fin_zero .: s >> ↑1 (*scomp_nf s (↑1)*) )) ;
subst_nf (T_subst t s1) s2 := T_subst t (scomp_nf s1 s2) ;
subst_nf (T_mvar xt) s := T_subst (T_mvar xt) s
(** Compose normal form substitutions. *)
with scomp_nf {n m o} (s1 : term K_s (S2 n m)) (s2 : term K_s (S2 m o)) : term K_s (S2 n o) by struct s1 :=
scomp_nf (↑k) s := (↑k) >> s ;
scomp_nf (t1 .: s1) s2 := subst_nf t1 s2 .: scomp_nf s1 s2 ;
scomp_nf (s1 >> s1') s2 := s1 >> (scomp_nf s1' s2) ;
scomp_nf (T_mvar xs) s := (T_mvar xs) >> s.

Lemma subst_scomp_nf_sound :
  (forall k n m (t : term k (S1 n)) (s : term K_s (S2 n m)), subst_nf t s =σ t[: s ]) *
  (forall n m o (s1 : term K_s (S2 n m)) (s2 : term K_s (S2 m o)), scomp_nf s1 s2 =σ s1 >> s2).
Proof. 
apply subst_nf_elim with 
  (P := fun _ _ _ t s res => res =σ t[: s ]) 
  (P0 := fun _ _ _ s1 s2 res => res =σ s1 >> s2).
- intros n m i s. now rewrite subst_var_nf_sound.
- intros n m c args s ->. now rewrite aeq_subst_ctor.
- intros n m s. now rewrite aeq_subst_al_nil.
- intros ty tys n m a args s -> ->. now rewrite aeq_subst_al_cons.
- intros b n m x s. now rewrite aeq_subst_abase.
- intros n m t s ->. now rewrite aeq_subst_aterm.
- intros ty n m a s ->. now rewrite aeq_subst_abind. 
- intros k n m o t s1 s2 ->. now rewrite aeq_subst_subst.
- reflexivity.
- reflexivity.
- intros n m o t1 s1 s2 -> ->. now rewrite aeq_distrib.
- intros n m o p s1 s2 s3 ->. now rewrite aeq_assoc.
- reflexivity.
Qed.

Lemma subst_nf_sound {k n m} (t : term k (S1 n)) (s : term K_s (S2 n m)) :
  subst_nf t s =σ t[: s ].
Proof. apply subst_scomp_nf_sound. Qed.

Lemma scomp_nf_sound {n m o} (s1 : term K_s (S2 n m)) (s2 : term K_s (S2 m o)) :
  scomp_nf s1 s2 =σ s1 >> s2.
Proof. apply subst_scomp_nf_sound. Qed.
  

Lemma simpl_subst_nf {k n m} (t : term k (S1 n)) (s : term K_s (S2 n m)) :
  nf t -> nf s -> nf (simpl_subst t s).
Proof.
apply simpl_subst_elim with (P0 := fun _ _ _ s1 s2 res => nf s1 -> nf s2 -> nf res) ;
clear k n m t s.
- intros n m i s H1 H2. now apply apply_subst_nf.
- intros n m c args s H1 H2 H3. apply nf_tctor. apply H1 ; [|exact H3].
  now apply inv_nf_tctor.
- intros n m s H1 H2. apply nf_al_nil.
- intros ty tys n m a args s H1 H2 H3 H4. apply inv_nf_al_cons in H3. apply nf_al_cons.
  + now apply H1.
  + now apply H2.
- intros b n m x s H1 H2. apply nf_abase.
- intros n m t s H1 H2 H3. apply inv_nf_aterm in H2. apply nf_aterm. now apply H1.
- intros ty n m a s H1 H2 H3. apply inv_nf_abind in H2. apply nf_abind. apply H1.
  + exact H2.
  + admit.
- intros k n m o t s1 s2 H1 H2 H3. 
  inv H2.
apply nf_subst_. 

Definition reduce {k s} (t : term k s) : term k s.
dependent induction t.
- exact (T_var f).
- exact (T_ctor c IHt).
- exact (T_al_nil).
- exact (T_al_cons IHt1 IHt2).
- exact (T_abase b d).
- exact (T_aterm IHt).
- exact (T_abind IHt).
- exact (simpl_subst t1 t2).
- exact (T_sshift k).
- exact (T_scons IHt1 IHt2).
- exact (T_scomp IHt1 IHt2).
Defined.  

Lemma up_subst_sid n : up_subst (@sid n) =σ sid.
Proof. 
cbv [up_subst sid]. simpl. setoid_rewrite <-(aeq_sshift_succ 0).
setoid_rewrite aeq_sshift_scons. reflexivity.
Qed.

Lemma subst_sid k n (t : term k (S1 n)) : t[: sid] =σ t.
Proof.
dependent induction t generalizing n ; try (now auto).
- unfold sid. rewrite (aeq_sshift_var f 0). reflexivity.
- rewrite aeq_subst_ctor. rewrite IHt ; auto.
- rewrite aeq_subst_al_cons. rewrite IHt1, IHt2 ; auto.
- rewrite aeq_subst_aterm. rewrite IHt ; auto.
- rewrite aeq_subst_abind. rewrite up_subst_sid. rewrite IHt ; auto.
- setoid_rewrite aeq_subst_subst. rewrite aeq_sid_r. reflexivity.
Qed. 

(** Main property: [reduce t] is axiomatically equal to [t]. *)
Lemma reduce_sound {k s} (t : term k s) : reduce t =σ t.
Proof.
dependent induction t ; simpl ; try auto.
- now rewrite simpl_subst_sound.
- rewrite IHt1, IHt2. reflexivity.
- rewrite IHt1, IHt2. reflexivity. 
Qed.

(*(** This lemma is a simple consequence of the soundness of [simpl]. 
    We could also prove it directly by induction, e.g. if we need it to prove 
    the soundness of [simpl]. *)
#[global] Instance simpl_proper k s : Proper (axiom_eq ==> axiom_eq) (@simpl k s).
Proof. intros ???. rewrite simpl_sound, simpl_sound. assumption. Qed.*)

End Make.