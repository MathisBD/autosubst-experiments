From Prototype Require Import Prelude Sig LevelOne LevelTwo.

(** The output of simplification (LevelTwoSimp.v) is good for comparing
    terms/equations for equality, but not very nice to work with. 
    This file implements cleanup functions which do trivial transformations 
    such as turning [Q_rapply R_shift i] into [Q_succ i]. Cleanup is
    typically applied after simplification.

    Cleanup functions can be applied to all terms (irreducible or not),
    and do not produce irreducible terms.
    
    For each cleanup function we prove a soundness lemma. *)

Module Make (S : Sig).
Include LevelTwo.Make (S).

#[local] Hint Extern 5 => constructor : core.
#[local] Hint Extern 5 => subst : core.

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
#[export] Hint Rewrite eval_mk_qsucc : qeval.

(*********************************************************************************)
(** *** [dest_rshift] *)
(*********************************************************************************)

(** [dest_rshift r] checks if [r] is of the form [rshift >> rshift >> rshift >> ...]
    (with at least one shift): 
    - if so it returns [Some n] where [S n] is the number of shifts.
    - otherwise it returns [None]. *)
Equations dest_rshift (r : ren) : option nat :=
dest_rshift R_shift := Some 0 ;
dest_rshift (R_comp r1 r2) with dest_rshift r1, dest_rshift r2 := {
  | Some n1, Some n2 => Some (S (n1 + n2))
  | _, _ => None 
  } ;
dest_rshift _ := None.

Lemma dest_rshift_sound e r n : 
  dest_rshift r = Some n -> reval e r =₁ add (S n).
Proof.
funelim (dest_rshift r) ; simp dest_rshift in * ; triv.
- intros H. depelim H. reflexivity.
- intros H. depelim H. simp qeval. apply (Hind e n2) in Heq. rewrite Heq. 
  apply (Hind0 e n1) in Heq0. rewrite Heq0. cbv [P.rcomp]. intros i. lia.
Qed.

(*********************************************************************************)
(** *** Rewriting system. *)
(*********************************************************************************)

Reserved Notation "i =q=> i'" (at level 70, no associativity). 
Reserved Notation "r =r=> r'" (at level 70, no associativity). 
Reserved Notation "e =e=> e'" (at level 70, no associativity). 
Reserved Notation "s =s=> s'" (at level 70, no associativity). 

Unset Elimination Schemes.
Inductive qred : qnat -> qnat -> Prop :=
(* Reflexivity. *)
| qred_refl i : i =q=> i
(* Transitivity. *)
| qred_trans i i' i'' : i =q=> i' -> i' =q=> i'' -> i =q=> i'' 
(* Congruence. *)
| qred_congr_succ i i' : i =q=> i' -> Q_succ i =q=> Q_succ i'
| qred_congr_rapply r r' i i' : r =r=> r' -> i =q=> i' -> Q_rapply r i =q=> Q_rapply r' i'
(* Cleanup. *)
| qred_rapply_shift r i n : dest_rshift r = Some n -> Q_rapply r i =q=> mk_qsucc n i

with rred : ren -> ren -> Prop :=
(* Reflexivity. *)
| rred_refl r : r =r=> r
(* Transitivity. *)
| rred_trans r r' r'' : r =r=> r' -> r' =r=> r'' -> r =r=> r'' 
(* Congruence. *)
| rred_congr_cons i i' r r' : i =q=> i' -> r =r=> r' -> R_cons i r =r=> R_cons i' r'
| rred_congr_comp r1 r1' r2 r2' : r1 =r=> r1' -> r2 =r=> r2' -> R_comp r1 r2 =r=> R_comp r1' r2'

where "i =q=> i'" := (qred i i')
  and "r =r=> r'" := (rred r r').
Set Elimination Schemes.

(** Generate (non-dependent) induction schemes for [qred] and [rred]. *)
Scheme qred_ind := Minimality for qred Sort Prop 
  with rred_ind := Minimality for rred Sort Prop.
Combined Scheme qred_rred_ind from qred_ind, rred_ind.

Derive Signature for qred rred.

(*********************************************************************************)
(** *** Setoid rewrite support. *)
(*********************************************************************************)

#[export] Instance qred_preorder : PreOrder qred.
Proof.
constructor.
- intros ?. apply qred_refl.
- intros ?????. eauto using qred_trans.
Qed.

#[export] Instance qred_proper_succ : Proper (qred ==> qred) Q_succ.
Proof. intros ???. now apply qred_congr_succ. Qed.
    
#[export] Instance qred_proper_rapply : Proper (rred ==> qred ==> qred) Q_rapply.
Proof. intros ??????. now apply qred_congr_rapply. Qed.

#[export] Instance rred_preorder : PreOrder rred.
Proof.
constructor.
- intros ?. apply rred_refl.
- intros ?????. eauto using rred_trans.
Qed.

#[export] Instance rred_proper_cons : Proper (qred ==> rred ==> rred) R_cons.
Proof. intros ??????. now apply rred_congr_cons. Qed.

#[export] Instance rred_proper_comp : Proper (rred ==> rred ==> rred) R_comp.
Proof. intros ??????. now apply rred_congr_comp. Qed.

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

(*********************************************************************************)
(** *** Irreducible forms. *)
(*********************************************************************************)

Definition qirred i := forall i', i =q=> i' -> i = i'.
Definition rirred r := forall r', r =r=> r' -> r = r'.

Unset Elimination Schemes.
Inductive qreducible : qnat -> Prop :=
| qreducible_congr_succ i : qreducible i -> qreducible (Q_succ i)
| qreducible_congr_rapply_1 r i : rreducible r -> qreducible (Q_rapply r i)
| qreducible_congr_rapply_2 r i : qreducible i -> qreducible (Q_rapply r i)
| qreducible_rapply_shift r i n : dest_rshift r = Some n -> qreducible (Q_rapply r i)

with rreducible : ren -> Prop :=
| rreducible_congr_cons_1 i r : qreducible i -> rreducible (R_cons i r)
| rreducible_congr_cons_2 i r : rreducible r -> rreducible (R_cons i r)
| rreducible_congr_comp_1 r1 r2 : rreducible r1 -> rreducible (R_comp r1 r2)
| rreducible_congr_comp_2 r1 r2 : rreducible r2 -> rreducible (R_comp r1 r2).
Set Elimination Schemes.

Hint Constructors qreducible rreducible : core.

Scheme qreducible_ind := Minimality for qreducible Sort Prop 
  with rreducible_ind := Minimality for rreducible Sort Prop.
Combined Scheme qreducible_rreducible_ind from qreducible_ind,rreducible_ind.

Derive Signature for qreducible rreducible.

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
exists (mk_qsucc n i). split ; triv. destruct n ; simp mk_qsucc ; triv.
Qed.

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

Lemma qirred_succ i : qirred (Q_succ i) <-> qirred i.
Proof.
repeat rewrite qirred_qreducible.
split ; intros H H1 ; apply H ; clear H ; triv. now depelim H1.
Qed.

Lemma qirred_rapply r i :
  qirred (Q_rapply r i) <-> rirred r /\ qirred i /\ dest_rshift r = None.
Proof.
repeat rewrite rirred_rreducible ; repeat rewrite qirred_qreducible. split ; intros H.
- split3 ; triv.  admit.
- intros H'. depelim H' ; triv. rewrite H0 in H ; triv.


(*********************************************************************************)
(** *** [qclean] and [rclean]. *)
(*********************************************************************************)

(** Handle the [Q_rapply r i] case of [qclean]. *)
Equations qclean_rapply : ren -> qnat -> qnat :=
qclean_rapply r i with dest_rshift r := { 
  | Some n => mk_qsucc n i 
  | None => Q_rapply r i
  }. 

Lemma qclean_rapply_red r i : 
  Q_rapply r i =q=> qclean_rapply r i.
Proof. funelim (qclean_rapply r i) ; triv. now apply qred_rapply_shift. Qed.
#[global] Hint Rewrite <-qclean_rapply_red : red.

Equations qclean : qnat -> qnat :=
qclean Q_zero := Q_zero ;
qclean (Q_succ i) := Q_succ (qclean i) ;
qclean (Q_rapply r i) := qclean_rapply (rclean r) (qclean i) ;
qclean (Q_mvar m) := Q_mvar m

with rclean : ren -> ren :=
rclean R_id := R_id ;
rclean R_shift := R_shift ;
rclean (R_cons i r) := R_cons (qclean i) (rclean r) ;
rclean (R_comp r1 r2) := R_comp (rclean r1) (rclean r2) ;
rclean (R_mvar m) := R_mvar m.

Lemma qclean_rclean_sound : 
  (forall i, i =q=> qclean i) * (forall r, r =r=> rclean r).
Proof.
apply qclean_elim with 
  (P := fun i res => i =q=> res)
  (P0 := fun r res => r =r=> res).
all: intros ; simp red ; triv.
- now rewrite <-H.
- now rewrite <-H, <-H0.
- now rewrite <-H, <-H0.
- now rewrite <-H, <-H0.  
Qed.

Lemma qclean_sound i : i =q=> qclean i.
Proof. now apply qclean_rclean_sound. Qed.
#[export] Hint Rewrite <-qclean_sound : red.

Lemma rclean_sound r : r =r=> rclean r.
Proof. now apply qclean_rclean_sound. Qed.
#[export] Hint Rewrite <-rclean_sound : red.

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
(** *** [eclean] and [sclean]. *)
(*********************************************************************************)

(** Handle the [E_ren r t] case of [eclean]. *)
Equations eclean_ren {k} : ren -> expr k -> expr k :=
eclean_ren r (E_tvar i) := E_tvar (qclean_rapply r i) ;
eclean_ren r t := E_ren r t.

Lemma eclean_ren_sound {k} e r (t : expr k) :
  eeval e (eclean_ren r t) = eeval e (E_ren r t).
Proof. funelim (eclean_ren r t) ; triv. now simp eeval qeval. Qed.
#[export] Hint Rewrite @eclean_ren_sound : eeval.

(** Handle the [E_subst s e] case of [eclean]. *)
Equations eclean_subst {k} : subst -> expr k -> expr k :=
eclean_subst s e with dest_ren s := {
  | Some r => eclean_ren r e 
  | None => E_subst s e
  }.

Lemma eclean_subst_sound {k} e s (t : expr k) :
  eeval e (eclean_subst s t) = eeval e (E_subst s t).
Proof.
funelim (eclean_subst s t) ; simp eeval ; triv.
rewrite (dest_ren_sound _ _ _ Heq). simp eeval. now rewrite O.ren_is_subst.
Qed.
#[export] Hint Rewrite @eclean_subst_sound : eeval. 
  
Equations eclean {k} : expr k -> expr k :=
eclean (E_tvar i) := E_tvar (qclean i) ;
eclean (E_tctor c al) := E_tctor c (eclean al) ;
eclean E_al_nil := E_al_nil ;
eclean (E_al_cons a al) := E_al_cons (eclean a) (eclean al) ;
eclean (E_abase b x) := E_abase b x ;
eclean (E_aterm t) := E_aterm (eclean t) ;
eclean (E_abind a) := E_abind (eclean a) ;
eclean (E_ren r t) := eclean_ren (rclean r) (eclean t) ;
eclean (E_subst s t) := eclean_subst (sclean s) (eclean t) ;
eclean (E_mvar m) := E_mvar m

with sclean : subst -> subst :=
sclean S_id := S_id ;
sclean S_shift := S_shift ;
sclean (S_cons t s) := S_cons (eclean t) (sclean s) ;
sclean (S_comp s1 s2) := S_comp (sclean s1) (sclean s2) ;
sclean (S_ren r) := S_ren (rclean r) ;
sclean (S_mvar m) := S_mvar m.

Lemma eclean_sclean_sound e : 
  (forall k (t : expr k), eeval e (eclean t) = eeval e t) *
  (forall s, seval e (sclean s) =₁ seval e s).
Proof.
apply eclean_elim with 
  (P := fun k t res => eeval e res = eeval e t) 
  (P0 := fun s res => seval e res =₁ seval e s).
all: intros ; simp eeval qeval reval ; triv.
all: solve [now rewrite H | now rewrite H, H0 ].
Qed. 

Lemma eclean_sound {k} e (t : expr k) : eeval e (eclean t) = eeval e t.
Proof. now apply eclean_sclean_sound. Qed.
#[export] Hint Rewrite @eclean_sound : eeval.

Lemma sclean_sound e s : seval e (sclean s) =₁ seval e s.
Proof. now apply eclean_sclean_sound. Qed.
#[export] Hint Rewrite sclean_sound : seval.

End Make.

