From Prototype Require Import Prelude Sig LevelTwo.
From Prototype Require LevelOne.
Module O := LevelOne.


(** The output of simplification (LevelTwoSimp.v) is good for comparing
    terms/equations for equality, but not very nice to work with. 
    This file implements cleanup functions which do trivial transformations 
    such as turning [Q_rapply R_shift i] into [Q_succ i]. Cleanup is
    typically applied after simplification.

    Cleanup functions can be applied to all terms (irreducible or not),
    and do not produce irreducible terms.
    
    For each cleanup function we prove a soundness lemma. *)

Section WithSignature.
Context {sig : signature}.
#[local] Existing Instance sig.

(** Add some power to [auto] and variants (such as [triv]). *)
#[local] Hint Extern 5 => intros ? : core.

(*********************************************************************************)
(** *** [mk_qsucc] *)
(*********************************************************************************)

(** [mk_qsucc n i] builds the quoted natural [Q_succ (Q_succ ... (Q_succ i))],
    where [Q_succ] appears [S n] times. *)
Equations mk_qsucc (n : nat) (i : qnat) : qnat :=
mk_qsucc 0 i := Q_succ i ;
mk_qsucc (S n) i := Q_succ (mk_qsucc n i).

Lemma eval_mk_qsucc e n i :
  qeval e (mk_qsucc n i) = S n + qeval e i.
Proof.
funelim (mk_qsucc n i) ; simp mk_qsucc qeval ; triv.
rewrite H. lia. 
Qed.
#[local] Hint Rewrite eval_mk_qsucc : qeval.

(*********************************************************************************)
(** *** [dest_rshift] *)
(*********************************************************************************)

(** We write our own version of [Nat.add] because we need to unfold it in 
    [RASimpl.v], and we need to avoid unfolding occurences of [add] introduced
    by the user. *)
Equations nat_add (n : nat) (m : nat) : nat :=
nat_add 0 n := n ;
nat_add (S n) m := nat_add n (S m).

Lemma nat_add_spec n m : nat_add n m = n + m.
Proof. funelim (nat_add n m) ; triv. rewrite H. lia. Qed. 

(** [dest_rshift r] checks if [r] is of the form [rshift >> rshift >> rshift >> ...]
    (with at least one shift): 
    - if so it returns [Some n] where [S n] is the number of shifts.
    - otherwise it returns [None]. *)
Equations dest_rshift (r : ren) : option nat :=
dest_rshift R_shift := Some 0 ;
dest_rshift (R_comp r1 r2) with dest_rshift r1, dest_rshift r2 := {
  | Some n1, Some n2 => Some (S (nat_add n1 n2))
  | _, _ => None 
  } ;
dest_rshift _ := None.

Lemma dest_rshift_sound e r n : 
  dest_rshift r = Some n -> reval e r =₁ add (S n).
Proof.
funelim (dest_rshift r) ; simp dest_rshift in * ; triv.
- intros H. depelim H. reflexivity.
- intros H. depelim H. simp qeval. apply (Hind e n2) in Heq. rewrite Heq. 
  apply (Hind0 e n1) in Heq0. rewrite Heq0. cbv [P.rcomp]. intros i. 
  rewrite nat_add_spec. lia.
Qed.

(*********************************************************************************)
(** *** [dest_ren] *)
(*********************************************************************************)

Equations dest_var {k} (t : expr k) : option qnat :=
dest_var (E_tvar i) := Some i ;
dest_var _ := None.

(* In the [S_cons] case, we match on [dest_var t]. This is because
   matching [t] with [E_tvar i] directly causes Equations to use 
   [apply_noConfusion], which is annoying to unfold completely with [cbv]. *)
Equations dest_ren (s : subst) : option ren :=
dest_ren S_id := Some R_id ;
dest_ren S_shift := Some R_shift ;
dest_ren (S_cons t s) with dest_var t, dest_ren s := {
  | Some i, Some r => Some (R_cons i r) 
  | _, _ => None 
  } ;
dest_ren (S_comp s1 s2) with dest_ren s1, dest_ren s2 := {
  | Some r1, Some r2 => Some (R_comp r1 r2)
  | _, _ => None
  } ;
dest_ren (S_ren r) := Some r ;
dest_ren _ := None.

Lemma dest_ren_sound e s r : 
  dest_ren s = Some r -> seval e s =₁ seval e (S_ren r).
Proof.
funelim (dest_ren s) ; triv.
all: intros H ; depelim H ; simp eeval qeval in * ; try reflexivity.
- depelim t ; triv. simp dest_var in Heq0. depelim Heq0. rewrite (Hind e r Heq).
  simp eeval. intros [|] ; reflexivity.
- rewrite (Hind e r2 Heq), (Hind0 e r1 Heq0). reflexivity.
Qed.

(*********************************************************************************)
(** *** Rewriting system. *)
(*********************************************************************************)

#[local] Reserved Notation "i =q=> i'" (at level 70, no associativity). 
#[local] Reserved Notation "r =r=> r'" (at level 70, no associativity). 
#[local] Reserved Notation "e =e=> e'" (at level 70, no associativity). 
#[local] Reserved Notation "s =s=> s'" (at level 70, no associativity). 

Unset Elimination Schemes.

Inductive qred : qnat -> qnat -> Prop :=
(* Preorder. *)
| qred_refl : reflexive qnat qred
| qred_trans : transitive qnat qred 
(* Congruence. *)
| qred_congr_succ : Proper (qred ==> qred) Q_succ
| qred_congr_rapply : Proper (rred ==> qred ==> qred) Q_rapply 
(* Cleanup rules. *)
| qred_rapply_shift r i n : dest_rshift r = Some n -> Q_rapply r i =q=> mk_qsucc n i

with rred : ren -> ren -> Prop :=
(* Preorder. *)
| rred_refl : reflexive ren rred
| rred_trans : transitive ren rred
(* Congruence. *)
| rred_congr_cons : Proper (qred ==> rred ==> rred) R_cons
| rred_congr_comp : Proper (rred ==> rred ==> rred) R_comp

where "i =q=> i'" := (qred i i')
  and "r =r=> r'" := (rred r r').

Inductive ered : forall {k}, expr k -> expr k -> Prop :=
(* Preorder. *)
| ered_refl {k} : reflexive (expr k) ered
| ered_trans {k} : transitive (expr k) ered
(* Congruence. *)
| ered_congr_tvar : Proper (qred ==> ered) E_tvar
| ered_congr_tctor c : Proper (ered ==> ered) (E_tctor c)
| ered_congr_al_cons {ty tys} : Proper (ered ==> ered ==> ered) (@E_al_cons _ ty tys)
| ered_congr_aterm : Proper (ered ==> ered) E_aterm
| ered_congr_abind {ty} : Proper (ered ==> ered) (@E_abind _ ty)
| ered_congr_ren {k} : Proper (rred ==> ered ==> ered) (@E_ren _ k)
| ered_congr_subst {k} : Proper (sred ==> ered ==> ered) (@E_subst _ k)
(* Cleanup rules. *)
| ered_ren_var r i : E_ren r (E_tvar i) =e=> E_tvar (Q_rapply r i)
| ered_subst_ren {k} s r (t : expr k) : dest_ren s = Some r -> E_subst s t =e=> E_ren r t

with sred : subst -> subst -> Prop :=
(* Preorder. *)
| sred_refl : reflexive subst sred
| sred_trans : transitive subst sred
(* Congruence. *)
| sred_congr_cons : Proper (ered ==> sred ==> sred) S_cons
| sred_congr_comp : Proper (sred ==> sred ==> sred) S_comp
| sred_congr_ren : Proper (rred ==> sred) S_ren

where "t =e=> t'" := (ered t t')
  and "s =s=> s'" := (sred s s').

Set Elimination Schemes.

Derive Signature for qred rred ered sred.

#[local] Hint Constructors qred rred ered sred : core.

Scheme qred_ind := Minimality for qred Sort Prop 
  with rred_ind := Minimality for rred Sort Prop.
Combined Scheme qred_rred_ind from qred_ind, rred_ind.

Scheme ered_ind := Minimality for ered Sort Prop 
  with sred_ind := Minimality for sred Sort Prop.
Combined Scheme ered_sred_ind from ered_ind, sred_ind.

(*********************************************************************************)
(** *** Setoid rewrite support. *)
(*********************************************************************************)

#[export] Instance qred_preorder : PreOrder qred.
Proof. constructor ; triv. Qed.
#[export] Instance rred_preorder : PreOrder rred.
Proof. constructor ; triv. Qed.
#[export] Instance ered_preorder k : PreOrder (@ered k).
Proof. constructor ; [apply ered_refl | apply ered_trans]. Qed.
#[export] Instance sred_preorder : PreOrder sred.
Proof. constructor ; triv. Qed.

#[export] Existing Instance qred_congr_succ.
#[export] Existing Instance qred_congr_rapply.
#[export] Existing Instance rred_congr_cons.
#[export] Existing Instance rred_congr_comp.
#[export] Existing Instance ered_congr_tvar.
#[export] Existing Instance ered_congr_tctor.
#[export] Existing Instance ered_congr_al_cons.
#[export] Existing Instance ered_congr_aterm.
#[export] Existing Instance ered_congr_abind.
#[export] Existing Instance ered_congr_ren.
#[export] Existing Instance ered_congr_subst.
#[export] Existing Instance sred_congr_cons.
#[export] Existing Instance sred_congr_comp.
#[export] Existing Instance sred_congr_ren.

(*********************************************************************************)
(** *** Soundness of the rewriting system. *)
(*********************************************************************************)

Lemma qred_rred_sound e : 
  (forall i i', i =q=> i' -> qeval e i = qeval e i') /\
  (forall r r', r =r=> r' -> reval e r =₁ reval e r').
Proof.
apply qred_rred_ind ; intros ; simp qeval ; triv.
- now rewrite H0, H2.
- now rewrite H0, H2.
- now rewrite (dest_rshift_sound _ _ _ H).
- now rewrite H0.
- now rewrite H0, H2.
- now rewrite H0, H2.
Qed.    

Lemma qred_sound e i i' : i =q=> i' -> qeval e i = qeval e i'.
Proof. now apply qred_rred_sound. Qed.

Lemma rred_sound e r r' : r =r=> r' -> reval e r =₁ reval e r'.
Proof. now apply qred_rred_sound. Qed.

Lemma ered_sred_sound e : 
  (forall {k} (t t' : expr k), t =e=> t' -> eeval e t = eeval e t') /\
  (forall s s', s =s=> s' -> seval e s =₁ seval e s').
Proof.
apply ered_sred_ind ; intros ; simp eeval ; triv.
all: try solve [ now rewrite H0, H2 ].
- eapply qred_sound in H. now rewrite H.
- eapply rred_sound in H. now rewrite H1, H.
- eapply dest_ren_sound in H. rewrite H. simp eeval.
  now rewrite O.ren_is_subst.
- eapply rred_sound in H. now rewrite H.
Qed.

Lemma ered_sound {k} e (t t' : expr k) : t =e=> t' -> eeval e t = eeval e t'.
Proof. now apply ered_sred_sound. Qed.

Lemma sred_sound e s s' : s =s=> s' -> seval e s =₁ seval e s'.
Proof. now apply ered_sred_sound. Qed.

(*********************************************************************************)
(** *** Irreducible & reducible forms. *)
(*********************************************************************************)

(** The "true" definition of irreducible forms, i.e. terms in which we can't 
    reduce. This definition is obviously correct but is hard to work with. *)
Definition qirred i := forall i', i =q=> i' -> i = i'.
Definition rirred r := forall r', r =r=> r' -> r = r'.
Definition eirred {k} (t : expr k) := forall t', t =e=> t' -> t = t'.
Definition sirred s := forall s', s =s=> s' -> s = s'.

Unset Elimination Schemes.

(** A definition of reducible forms, i.e. terms in which we can reduce,
    which is easy to work with but is not obviously correct.
    We prove below that this notion agrees with [qirred], [rirred], etc. *)
Inductive qreducible : qnat -> Prop :=
(* Congruence. *)
| qreducible_congr_succ i : qreducible i -> qreducible (Q_succ i)
| qreducible_congr_rapply_1 r i : rreducible r -> qreducible (Q_rapply r i)
| qreducible_congr_rapply_2 r i : qreducible i -> qreducible (Q_rapply r i)
(* Cleanup rules. *)
| qreducible_rapply_shift r i n : dest_rshift r = Some n -> qreducible (Q_rapply r i)

with rreducible : ren -> Prop :=
(* Congruence. *)
| rreducible_congr_cons_1 i r : qreducible i -> rreducible (R_cons i r)
| rreducible_congr_cons_2 i r : rreducible r -> rreducible (R_cons i r)
| rreducible_congr_comp_1 r1 r2 : rreducible r1 -> rreducible (R_comp r1 r2)
| rreducible_congr_comp_2 r1 r2 : rreducible r2 -> rreducible (R_comp r1 r2).

Inductive ereducible : forall {k}, expr k -> Prop :=
(* Congruence. *)
| ereducible_congr_tvar i : qreducible i -> ereducible (E_tvar i)
| ereducible_congr_tctor c al : ereducible al -> ereducible (E_tctor c al)
| ereducible_congr_al_cons_1 {ty tys} (a : expr (Ka ty)) (al : expr (Kal tys)) : 
    ereducible a -> ereducible (E_al_cons a al)
| ereducible_congr_al_cons_2 {ty tys} (a : expr (Ka ty)) (al : expr (Kal tys)) : 
    ereducible al -> ereducible (E_al_cons a al)
| ereducible_congr_aterm t : ereducible t -> ereducible (E_aterm t)
| ereducible_congr_abind {ty} (a : expr (Ka ty)) : ereducible a -> ereducible (E_abind a)
| ereducible_congr_ren_1 {k} r (t : expr k) : rreducible r -> ereducible (E_ren r t)
| ereducible_congr_ren_2 {k} r (t : expr k) : ereducible t -> ereducible (E_ren r t)
| ereducible_congr_subst_1 {k} s (t : expr k) : sreducible s -> ereducible (E_subst s t)
| ereducible_congr_subst_2 {k} s (t : expr k) : ereducible t -> ereducible (E_subst s t)
(* Cleanup rules. *)
| ereducible_ren_var r i : ereducible (E_ren r (E_tvar i))
| ereducible_subst_ren {k} s r (t : expr k) : dest_ren s = Some r -> ereducible (E_subst s t)

with sreducible : subst -> Prop :=
(* Congruence. *)
| sreducible_congr_cons_1 t s : ereducible t -> sreducible (S_cons t s)
| sreducible_congr_cons_2 t s : sreducible s -> sreducible (S_cons t s)
| sreducible_congr_comp_1 s1 s2 : sreducible s1 -> sreducible (S_comp s1 s2)
| sreducible_congr_comp_2 s1 s2 : sreducible s2 -> sreducible (S_comp s1 s2)
| sreducible_congr_ren r : rreducible r -> sreducible (S_ren r).

Set Elimination Schemes.

Scheme qreducible_ind := Minimality for qreducible Sort Prop 
  with rreducible_ind := Minimality for rreducible Sort Prop.
Combined Scheme qreducible_rreducible_ind from qreducible_ind, rreducible_ind.

Scheme ereducible_ind := Minimality for ereducible Sort Prop 
  with sreducible_ind := Minimality for sreducible Sort Prop.
Combined Scheme ereducible_sreducible_ind from ereducible_ind, sreducible_ind.

Derive Signature for qreducible rreducible ereducible sreducible.

#[local] Hint Constructors qreducible rreducible ereducible sreducible : core.

(*********************************************************************************)
(** *** Equivalence between the two notions of irreducible forms. *)
(*********************************************************************************)

Lemma qr_red_impl_reducible : 
  (forall i i', i =q=> i' -> i = i' \/ qreducible i) /\ 
  (forall r r', r =r=> r' -> r = r' \/ rreducible r).
Proof.
apply qred_rred_ind ; intros ; triv.
all: try solve [ destruct H0, H2 ; triv ].
destruct H0 ; triv.
Qed.

Lemma qr_reducible_impl_red : 
  (forall i, qreducible i -> exists i', i =q=> i' /\ i <> i') /\
  (forall r, rreducible r -> exists r', r =r=> r' /\ r <> r').
Proof.
apply qreducible_rreducible_ind ; intros.
all: try solve [ destruct H0 as (i' & H1 & H2) ; eexists ; split ; 
  [now rewrite H1 | intros H3 ; now depelim H3] ].
exists (mk_qsucc n i). split ; triv. destruct n ; triv.
Qed.

Lemma es_red_impl_reducible : 
  (forall {k} (t t' : expr k), t =e=> t' -> t = t' \/ ereducible t) /\ 
  (forall s s', s =s=> s' -> s = s' \/ sreducible s).
Proof.
apply ered_sred_ind ; intros ; triv.
all: try solve [ destruct H0 ; triv | destruct H0, H2 ; triv ].
- apply qr_red_impl_reducible in H. destruct H ; triv.
- apply qr_red_impl_reducible in H. destruct H, H1 ; triv.
- apply qr_red_impl_reducible in H. destruct H ; triv.   
Qed.

Lemma es_reducible_impl_red : 
  (forall {k} (t : expr k), ereducible t -> exists t', t =e=> t' /\ t <> t') /\
  (forall s, sreducible s -> exists s', s =s=> s' /\ s <> s').
Proof.
apply ereducible_sreducible_ind ; intros.
all: try solve [ destruct H0 as (i' & H1 & H2) ; eexists ; split ; 
  [now rewrite H1 | intros H3 ; now depelim H3] ].
all: try solve [ apply qr_reducible_impl_red in H ; destruct H as (i' & H1 & H2) ;
  eexists ; split ; [now rewrite H1 | intros H3 ; now depelim H3] ].
- destruct H0 as (i' & H1 & H2). eexists.
  split ; [now rewrite H1 | intros H3]. admit.
- exists (E_tvar (Q_rapply r i)). triv.
- exists (E_ren r t). split ; auto using ered_subst_ren. intros H1. depelim H1.
Admitted.

Lemma qirred_qreducible i : qirred i <-> ~qreducible i.
Proof.
split.
- intros H H'. apply qr_reducible_impl_red in H'. destruct H' as (i' & H1 & H2). triv.
- intros H i' Hi. apply qr_red_impl_reducible in Hi. destruct Hi ; triv.
Qed.

Lemma rirred_rreducible r : rirred r <-> ~rreducible r.
Proof.
split.
- intros H H'. apply qr_reducible_impl_red in H'. destruct H' as (r' & H1 & H2). triv.
- intros H r' Hr. apply qr_red_impl_reducible in Hr. destruct Hr ; triv.
Qed.

Lemma eirred_ereducible {k} (t : expr k) : eirred t <-> ~ereducible t.
Proof.
split.
- intros H H'. apply es_reducible_impl_red in H'. destruct H' as (t' & H1 & H2). triv.
- intros H t' Ht. apply es_red_impl_reducible in Ht. destruct Ht ; triv.
Qed.

Lemma sirred_sreducible s : sirred s <-> ~sreducible s.
Proof.
split.
- intros H H'. apply es_reducible_impl_red in H'. destruct H' as (s' & H1 & H2). triv.
- intros H s' Hs. apply es_red_impl_reducible in Hs. destruct Hs ; triv.
Qed.

(*********************************************************************************)
(** *** Characterization of irreducible forms. *)
(*********************************************************************************)

Lemma qirred_succ i : qirred (Q_succ i) <-> qirred i.
Proof.
repeat rewrite qirred_qreducible.
split ; intros H H1 ; apply H ; clear H ; triv. now depelim H1.
Qed.

Lemma qirred_rapply r i :
  qirred (Q_rapply r i) <-> rirred r /\ qirred i /\ dest_rshift r = None.
Proof.
repeat rewrite rirred_rreducible ; repeat rewrite qirred_qreducible. split ; intros H.
- split3 ; triv. destruct (dest_rshift r) eqn:E ; triv.
- intros H'. depelim H' ; triv. rewrite H0 in H ; triv.
Qed.

Lemma rirred_cons i r : 
  rirred (R_cons i r) <-> qirred i /\ rirred r.
Proof.
repeat rewrite rirred_rreducible ; repeat rewrite qirred_qreducible. 
split ; intros H.
- split ; triv.
- intros H'. depelim H' ; triv.
Qed.

Lemma rirred_comp r1 r2 : 
  rirred (R_comp r1 r2) <-> rirred r1 /\ rirred r2.
Proof.
repeat rewrite rirred_rreducible. split ; intros H.
- split ; triv.
- intros H'. depelim H' ; triv.
Qed.  

(*********************************************************************************)
(** *** [clean_rapply]. *)
(*********************************************************************************)

(** Cleanup [Q_rapply r i]. *)
Equations clean_rapply : ren -> qnat -> qnat :=
clean_rapply r i with dest_rshift r := { 
  | Some n => mk_qsucc n i 
  | None => Q_rapply r i
  }. 

Lemma clean_rapply_red r i : 
  Q_rapply r i =q=> clean_rapply r i.
Proof. funelim (clean_rapply r i) ; triv. Qed.
#[local] Hint Rewrite <-clean_rapply_red : red.

Lemma clean_rapply_irred r i :
  rirred r -> qirred i -> qirred (clean_rapply r i).
Proof.
intros H1 H2. funelim (clean_rapply r i).
- induction n in |- * ; simp mk_qsucc ; now rewrite qirred_succ.
- rewrite qirred_rapply. triv.
Qed.

(*********************************************************************************)
(** *** [qclean] and [rclean]. *)
(*********************************************************************************)

Equations qclean : qnat -> qnat :=
qclean Q_zero := Q_zero ;
qclean (Q_succ i) := Q_succ (qclean i) ;
qclean (Q_rapply r i) := clean_rapply (rclean r) (qclean i) ;
qclean (Q_mvar m) := Q_mvar m

with rclean : ren -> ren :=
rclean R_id := R_id ;
rclean R_shift := R_shift ;
rclean (R_cons i r) := R_cons (qclean i) (rclean r) ;
rclean (R_comp r1 r2) := R_comp (rclean r1) (rclean r2) ;
rclean (R_mvar m) := R_mvar m.

Lemma qrclean_red : 
  (forall i, i =q=> qclean i) * (forall r, r =r=> rclean r).
Proof.
apply qclean_elim with 
  (P := fun i res => i =q=> res)
  (P0 := fun r res => r =r=> res).
all: intros ; simp red ; triv.
- now rewrite <-H, <-H0.
- now rewrite <-H, <-H0.
- now rewrite <-H, <-H0.
Qed.

Lemma qclean_red i : i =q=> qclean i.
Proof. now apply qrclean_red. Qed.
#[local] Hint Rewrite <-qclean_red : red.

Lemma rclean_red r : r =r=> rclean r.
Proof. now apply qrclean_red. Qed.
#[local] Hint Rewrite <-rclean_red : red.

(*********************************************************************************)
(** *** [clean_rename] *)
(*********************************************************************************)

(** Cleanup [E_ren r t]. *)
Equations clean_rename {k} : ren -> expr k -> expr k :=
clean_rename r (E_tvar i) := E_tvar (clean_rapply r i) ;
clean_rename r t := E_ren r t.

Lemma clean_rename_red {k} r (t : expr k) :
  E_ren r t =e=> clean_rename r t.
Proof. funelim (clean_rename r t) ; simp red ; triv. Qed.
#[local] Hint Rewrite <-@clean_rename_red : red.

(*********************************************************************************)
(** *** [clean_substitute] *)
(*********************************************************************************)

(** Cleanup [E_subst s t]. *)
Equations clean_substitute {k} : subst -> expr k -> expr k :=
clean_substitute s t with dest_ren s := {
  | Some r => clean_rename r t 
  | None => E_subst s t
  }.

Lemma clean_substitute_red {k} s (t : expr k) : 
  E_subst s t =e=> clean_substitute s t.
Proof. funelim (clean_substitute s t) ; simp red ; triv. Qed.
#[local] Hint Rewrite <-@clean_substitute_red : red.

(*********************************************************************************)
(** *** [eclean] and [sclean] *)
(*********************************************************************************)
  
Equations eclean {k} : expr k -> expr k :=
eclean (E_tvar i) := E_tvar (qclean i) ;
eclean (E_tctor c al) := E_tctor c (eclean al) ;
eclean E_al_nil := E_al_nil ;
eclean (E_al_cons a al) := E_al_cons (eclean a) (eclean al) ;
eclean (E_abase b x) := E_abase b x ;
eclean (E_aterm t) := E_aterm (eclean t) ;
eclean (E_abind a) := E_abind (eclean a) ;
eclean (E_ren r t) := clean_rename (rclean r) (eclean t) ;
eclean (E_subst s t) := clean_substitute (sclean s) (eclean t) ;
eclean (E_mvar m) := E_mvar m

with sclean : subst -> subst :=
sclean S_id := S_id ;
sclean S_shift := S_shift ;
sclean (S_cons t s) := S_cons (eclean t) (sclean s) ;
sclean (S_comp s1 s2) := S_comp (sclean s1) (sclean s2) ;
sclean (S_ren r) := S_ren (rclean r) ;
sclean (S_mvar m) := S_mvar m.

Lemma eclean_subst_red : 
  (forall k (t : expr k), t =e=> eclean t) *
  (forall s, s =s=> sclean s).
Proof.
apply eclean_elim with 
  (P := fun k t res => t =e=> res) 
  (P0 := fun s res => s =s=> res).
all: intros ; simp red ; triv.
all: solve [ now rewrite <-H | now rewrite <-H, <-H0 ].
Qed. 

Lemma eclean_red {k} (t : expr k) : t =e=> eclean t.
Proof. now apply eclean_subst_red. Qed.
#[local] Hint Rewrite @eclean_red : red.

Lemma sclean_red s : s =s=> sclean s.
Proof. now apply eclean_subst_red. Qed.
#[local] Hint Rewrite sclean_red : red.

End WithSignature.

