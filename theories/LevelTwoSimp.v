From Prototype Require Import Prelude Sig.
From Prototype Require LevelOne LevelTwo.
Module P := Prelude.
Module O := LevelOne.
Module T := LevelTwo.
Import T.

(** This file defines _irreducible_ forms for level two 
    expressions/substitutions, i.e. expressions in which we can't
    simplify anymore.
    
    We first define _reducible_ forms (in which we can reduce),
    and define irreducible as the negation of reducible.
    
    We then prove numerous lemmas that characterize irreducible forms. *)

Section WithSignature.
Context {sig : signature}.

(*********************************************************************************)
(** *** Discriminators. *)
(*********************************************************************************)

(** Reducible/irreducible forms need to distinguish terms based 
    on their head constructor(s). We provide discriminator functions 
    which handle this. *)

Definition is_qsucc x := 
  match x with Q_succ _ => true | _ => false end.  
Definition is_qrapply x := 
  match x with Q_rapply _ _ => true | _ => false end.
Definition is_qmvar x :=
  match x with Q_mvar _ => true | _ => false end.
  
Definition is_rcons r := 
  match r with R_cons _ _ => true | _ => false end.
Definition is_rcomp r := 
  match r with R_comp _ _ => true | _ => false end.
Definition is_rmvar r := 
  match r with R_mvar _ => true | _ => false end. 

Definition is_rid_l r := 
  match r with R_comp R_id _ => true | _ => false end.
Definition is_rshift_l r := 
  match r with R_comp R_shift _ => true | _ => false end.
Definition is_rcons_l r := 
  match r with R_comp (R_cons _ _) _ => true | _ => false end. 
Definition is_rcomp_l r := 
  match r with R_comp (R_comp _ _) _ => true | _ => false end.
Definition is_rmvar_l r := 
  match r with R_comp (R_mvar _) _ => true | _ => false end.

Definition is_tvar {k} (t : expr k) :=
  match t with E_tvar _ => true | _ => false end.
Definition is_tvar_zero {k} (t : expr k) :=
  match t with E_tvar Q_zero => true | _ => false end.
Definition is_tmvar {k} (e : expr k) :=
  match e with E_mvar _ => True | _ => False end.

Definition is_scons s :=
  match s with S_cons _ _ => true | _ => false end.
Definition is_scomp s :=
  match s with S_comp _ _ => true | _ => false end.
Definition is_smvar s :=
  match s with S_mvar _ => true | _ => false end.
Definition is_sren s := 
  match s with S_ren _ => true | _ => false end.

Definition is_sshift_l s :=
  match s with S_comp S_shift _ => true | _ => false end.
Definition is_scons_l s :=
  match s with S_comp (S_cons _ _) _ => true | _ => false end.
Definition is_scomp_l s :=
  match s with S_comp (S_comp _ _) _ => true | _ => false end.
Definition is_smvar_l s :=
  match s with S_comp (S_mvar _) _ => true | _ => false end.
Definition is_sren_l s := 
  match s with S_comp (S_ren _) _ => true | _ => false end.



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
(* Simplification rules. *)
| qred_succ i : Q_succ i =q=> Q_rapply R_shift i
| qred_rapply_rid i : Q_rapply R_id i =q=> i
| qred_rapply_rapply r1 r2 i : 
    Q_rapply r2 (Q_rapply r1 i) =q=> Q_rapply (R_comp r1 r2) i
| qred_rapply_cons_zero i r : Q_rapply (R_cons i r) Q_zero =q=> i

with rred : ren -> ren -> Prop :=
(* Preorder. *)
| rred_refl : reflexive ren rred
| rred_trans : transitive ren rred
(* Congruence. *)
| rred_congr_cons : Proper (qred ==> rred ==> rred) R_cons
| rred_congr_comp : Proper (rred ==> rred ==> rred) R_comp
(* Simplification rules.*)
| rred_id_l r : R_comp R_id r =r=> r 
| rred_id_r r : R_comp r R_id =r=> r
| rred_comp_l r1 r2 r3 : R_comp (R_comp r1 r2) r3 =r=> R_comp r1 (R_comp r2 r3)
| rred_cos_l i r1 r2 : R_comp (R_cons i r1) r2 =r=> R_cons (Q_rapply r2 i) (R_comp r1 r2)
| rred_shift_cons i r : R_comp R_shift (R_cons i r) =r=> r
| rred_zero_shift : R_cons Q_zero R_shift =r=> R_id

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
(* Simplification rules. *)
| ered_rapply r i : E_tvar (Q_rapply r i) =e=> E_ren r (E_tvar i)
| ered_ren {k} r (t : expr k) : E_ren r t =e=> E_subst (S_ren r) t
| ered_subst_ctor s c al : E_subst s (E_tctor c al) =e=> E_tctor c (E_subst s al)
| ered_subst_al_nil s : E_subst s E_al_nil =e=> E_al_nil
| ered_subst_al_cons {ty tys} s (a : expr (Ka ty)) (al : expr (Kal tys)) : 
    E_subst s (E_al_cons a al) =e=> E_al_cons (E_subst s a) (E_subst s al)
| ered_subst_abase s b x : E_subst s (E_abase b x) =e=> E_abase b x
| ered_subst_aterm s t : E_subst s (E_aterm t) =e=> E_aterm (E_subst s t)
| ered_subst_abind {ty} s (a : expr (Ka ty)) : 
    E_subst s (E_abind a) =e=> E_abind (E_subst (S_cons (E_tvar Q_zero) (S_comp s S_shift)) a)
| ered_subst_subst {k} s1 s2 (t : expr k) : 
    E_subst s2 (E_subst s1 t) =e=> E_subst (S_comp s1 s2) t
| ered_subst_id {k} (t : expr k) : E_subst S_id t =e=> t
| ered_subst_cons_zero t s : E_subst (S_cons t s) (E_tvar Q_zero) =e=> t

with sred : subst -> subst -> Prop :=
(* Preorder. *)
| sred_refl : reflexive subst sred
| sred_trans : transitive subst sred
(* Congruence. *)
| sred_congr_cons : Proper (ered ==> sred ==> sred) S_cons
| sred_congr_comp : Proper (sred ==> sred ==> sred) S_comp
| sred_congr_ren : Proper (rred ==> sred) S_ren
(* Simplification rules. *)
| sred_id_l s : S_comp S_id s =s=> s
| sred_id_r s : S_comp s S_id =s=> s
| sred_comp_l s1 s2 s3 : S_comp (S_comp s1 s2) s3 =s=> S_comp s1 (S_comp s2 s3)
| sred_cons_l t s1 s2 : S_comp (S_cons t s1) s2 =s=> S_cons (E_subst s2 t) (S_comp s1 s2) 
| sred_shift_cons i s : S_comp S_shift (S_cons i s) =s=> s
| sred_zero_shift : S_cons (E_tvar Q_zero) S_shift =s=> S_id
| sred_sren_id : S_ren R_id =s=> S_id
| sred_sren_shift : S_ren R_shift =s=> S_shift
| sred_sren_cons i r : S_ren (R_cons i r) =s=> S_cons (E_tvar i) (S_ren r)
| sred_sren_comp r1 r2 : S_ren (R_comp r1 r2) =s=> S_comp (S_ren r1) (S_ren r2)

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
all: try solve [ now rewrite H0, H2 ].
- now rewrite O.rcomp_rcons_distrib.
- intros [|] ; reflexivity.
Qed.    

Lemma qred_sound e i i' : i =q=> i' -> qeval e i = qeval e i'.
Proof. now apply qred_rred_sound. Qed.

Lemma rred_sound e r r' : r =r=> r' -> reval e r =₁ reval e r'.
Proof. now apply qred_rred_sound. Qed.

Lemma ered_sred_sound e : 
  (forall {k} (t t' : expr k), t =e=> t' -> eeval e t = eeval e t') /\
  (forall s s', s =s=> s' -> seval e s =₁ seval e s').
Proof.
apply ered_sred_ind ; intros ; simp eeval qeval ; triv.
all: try solve [ now rewrite H0, H2 ]. 
- eapply qred_sound in H. now rewrite H.
- eapply rred_sound in H. now rewrite H1, H.
- now rewrite O.ren_is_subst.
- simp substitute. rewrite O.up_subst_alt. reflexivity.
- now rewrite O.subst_subst.
- now rewrite O.subst_sid.
- eapply rred_sound in H. now rewrite H.
- now rewrite O.scomp_sid_r.
- now rewrite O.scomp_assoc.
- now rewrite O.scomp_scons_distrib.
- now rewrite O.sid_scons.
- intros [|] ; reflexivity.      
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
(* Simplification rules. *)
| qreducible_rapply_id i : qreducible (Q_rapply R_id i)
| qreducible_rapply_rapply r1 r2 i : qreducible (Q_rapply r1 (Q_rapply r2 i))
| qreducible_rapply_rcons_zero r : is_rcons r -> qreducible (Q_rapply r Q_zero)
| qreducible_succ i : qreducible (Q_succ i)

with rreducible : ren -> Prop :=
(* Congruence. *)
| rreducible_congr_cons_1 i r : qreducible i -> rreducible (R_cons i r)
| rreducible_congr_cons_2 i r : rreducible r -> rreducible (R_cons i r)
| rreducible_congr_comp_1 r1 r2 : rreducible r1 -> rreducible (R_comp r1 r2)
| rreducible_congr_comp_2 r1 r2 : rreducible r2 -> rreducible (R_comp r1 r2)
(* Simplification rules. *)
| rreducible_id_l r : rreducible (R_comp R_id r)
| rreducible_id_r r : rreducible (R_comp r R_id)
| rreducible_comp_l r1 r2 r3 : rreducible (R_comp (R_comp r1 r2) r3)
| rreducible_cons_l i r1 r2 : rreducible (R_comp (R_cons i r1) r2)
| rreducible_shift_cons r : is_rcons r -> rreducible (R_comp R_shift r)
| rreducible_zero_shift : rreducible (R_cons Q_zero R_shift).

(** Expressions in which we can push substitutions. *)
Definition is_push {k} (e : expr k) : Prop :=
  match e with E_mvar _ | E_tvar _ | E_ren _ _ => False | _ => True end.

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
(* Simplification rules. *)
| ereducible_rapply r i : ereducible (E_tvar (Q_rapply r i))
| ereducible_ren {k} r (e : expr k) : ereducible (E_ren r e)
| ereducible_subst {k} s (e : expr k) : is_push e -> ereducible (E_subst s e)
| ereducible_subst_id {k} (e : expr k) : ereducible (E_subst S_id e)
| ereducible_subst_cons_zero s : is_scons s -> ereducible (E_subst s (E_tvar Q_zero))

with sreducible : subst -> Prop :=
(* Congruence. *)
| sreducible_congr_cons_1 t s : ereducible t -> sreducible (S_cons t s)
| sreducible_congr_cons_2 t s : sreducible s -> sreducible (S_cons t s)
| sreducible_congr_comp_1 s1 s2 : sreducible s1 -> sreducible (S_comp s1 s2)
| sreducible_congr_comp_2 s1 s2 : sreducible s2 -> sreducible (S_comp s1 s2)
| sreducible_congr_ren r : rreducible r -> sreducible (S_ren r)
(* Simplification rules. *)
| sreducible_id_l s : sreducible (S_comp S_id s)
| sreducible_id_r s : sreducible (S_comp s S_id)
| sreducible_comp_l s1 s2 s3: sreducible (S_comp (S_comp s1 s2) s3)
| sreducible_cons_l t s1 s2 : sreducible (S_comp (S_cons t s1) s2)
| sreducible_shift_cons s : is_scons s -> sreducible (S_comp S_shift s)
| sreducible_cons_zero_shift : sreducible (S_cons (E_tvar Q_zero) S_shift)
| sreducible_sren r : ~is_rmvar r -> sreducible (S_ren r).

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
all: solve [ destruct H0, H2 ; triv ].
Qed.

Lemma qr_reducible_impl_red : 
  (forall i, qreducible i -> exists i', i =q=> i' /\ i <> i') /\
  (forall r, rreducible r -> exists r', r =r=> r' /\ r <> r').
Proof.
apply qreducible_rreducible_ind ; intros.
all: try solve [ destruct H0 as (i' & H1 & H2) ; eexists ; split ; 
  [now rewrite H1 | intros H3 ; now depelim H3] ].
- exists i. split ; triv. intros H. admit.
  (*remember R_id as r. clear Heqr. 
  induction i in r, H |- * ; triv. depelim H. symmetry in H. triv.*)
- exists (Q_rapply (R_comp r2 r1) i). split ; triv. intros H ; depelim H.
  admit.
- destruct r ; triv. exists q. split ; triv. intros H1. admit.
- exists (Q_rapply R_shift i). split ; triv.
- exists r. split ; triv. intros H. admit.
- exists r. split ; triv. intros H. admit.
- exists (R_comp r1 (R_comp r2 r3)). split ; triv. intros H. depelim H. admit.
- exists (R_cons (Q_rapply r2 i) (R_comp r1 r2)). split ; triv.
- destruct r ; triv. exists r. split ; triv. intros H1. admit.
- exists R_id. split ; triv.
Admitted.

Lemma es_red_impl_reducible : 
  (forall {k} (t t' : expr k), t =e=> t' -> t = t' \/ ereducible t) /\ 
  (forall s s', s =s=> s' -> s = s' \/ sreducible s).
Proof.
apply ered_sred_ind ; intros ; triv.
all: try solve [ destruct H0 ; triv | destruct H0, H2 ; triv ].
all: try solve [ right ; apply ereducible_subst ; triv ]. 
all: try solve [ right ; apply sreducible_sren ; triv ]. 
- apply qr_red_impl_reducible in H. destruct H ; triv.
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
- destruct H0 as (i' & H1 & H2). eexists. split ; [now rewrite H1 | intros H3]. admit.
- exists (E_ren r (E_tvar i)). triv.
- exists (E_subst (S_ren r) e). triv.
- destruct e ; auto. 
  + exists (E_tctor c (E_subst s e)). triv.
  + exists E_al_nil. triv.
  + exists (E_al_cons (E_subst s e1) (E_subst s e2)). triv.
  + exists (E_abase b e). triv.
  + exists (E_aterm (E_subst s e)). triv.
  + eexists (E_abind (E_subst _ e)). triv.
  + exists (E_subst (S_comp s0 s) e). split ; triv. intros H1. depelim H1. admit. 
- exists e. split ; triv. admit.
- destruct s ; triv. exists e. split ; triv. admit.  
- exists s. split ; triv. admit.
- exists s. split ; triv. admit.
- exists (S_comp s1 (S_comp s2 s3)). split ; triv. admit.
- exists (S_cons (E_subst s2 t) (S_comp s1 s2)). split ; triv.
- destruct s ; triv. exists s. split ; triv. admit.
- exists S_id. triv.
- destruct r ; auto.
  + exists S_id. triv.
  + exists S_shift. triv.
  + eexists (S_cons _ _). triv.
  + eexists (S_comp _ _). triv.     
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

Ltac change_irred :=
  (repeat rewrite qirred_qreducible) ;
  (repeat rewrite rirred_rreducible) ;
  (repeat rewrite eirred_ereducible) ;
  (repeat rewrite sirred_sreducible).

(*********************************************************************************)
(** *** Characterization of irreducible forms. *)
(*********************************************************************************)

Lemma qirred_zero : qirred Q_zero.
Proof. change_irred. intros H. depelim H. Qed.

Lemma qirred_succ i : ~qirred (Q_succ i).
Proof. change_irred. intros H. apply H. now constructor. Qed.
    
Lemma qirred_rapply r i : 
  qirred (Q_rapply r i) <-> 
    rirred r /\ qirred i /\ r <> R_id /\ ~is_qrapply i /\
    ~(is_rcons r /\ i = Q_zero).
Proof. 
change_irred. split ; intros H. 
- split5 ; intros H' ; apply H ; triv.
  + destruct i ; triv.
  + destruct r ; triv. destruct H' as (_ & ->). triv.
- intros H' ; depelim H' ; triv.
  + destruct H as (_ & _ & _ & H & _). triv.
  + destruct r ; triv. destruct H as (_ & _ & _ & _ & H). triv.
Qed.

Lemma qirred_mvar m : qirred (Q_mvar m).
Proof. change_irred. intros H. depelim H. Qed.

Lemma rirred_cons i r : 
  rirred (R_cons i r) <-> 
    qirred i /\ rirred r /\ ~(i = Q_zero /\ r = R_shift).
Proof.
change_irred. split.
- intros H. split3 ; intros H' ; apply H ; triv.
  destruct H' ; subst. now constructor. 
- intros (H1 & H2 & H3) H. depelim H.
  + destruct H ; triv. apply H3 ; triv.
Qed.

Lemma rirred_mvar_l m r : 
  rirred (R_comp (R_mvar m) r) <-> rirred r /\ r <> R_id.
Proof.
split.
- intros H. split.
  + intros H'. apply H ; clear H. apply RR_congr_comp. now right.
  + intros H' ; subst. apply H. now constructor. 
- intros (H & H') H''. depelim H'' ; triv. now destruct H0.
Qed.      

Lemma rirred_shift_l r : 
  rirred (R_comp R_shift r) <-> 
    rirred r /\ r <> R_id /\ ~is_rcons r.
Proof.
split.
- intros H. split3 ; triv. intros H' ; apply H ; triv.
- intros (H1 & H2 & H3) H. depelim H ; triv. destruct H ; triv.
Qed.

Lemma rirred_comp r1 r2 : 
  rirred (R_comp r1 r2) <->
    rirred r1 /\ rirred r2 /\ ~is_rcomp r1 /\ ~is_rcons r1 /\ 
    r1 <> R_id /\ r2 <> R_id /\ ~(r1 = R_shift /\ is_rcons r2).
Proof.
split ; intros H.
- split7 ; intros H' ; apply H ; triv.
  + destruct r1 ; triv.
  + destruct r1 ; triv.
  + destruct H' as [-> H']. destruct r2 ; triv.
- intros H' ; depelim H' ; triv.
  + destruct H0 ; triv.
  + destruct H as (_ & _ & H & _) ; triv.
  + destruct H as (_ & _ & _ & H & _) ; triv.
  + destruct r2 ; triv. destruct H as (_ & _ & _ & _ & _ & _ & H). triv.
Qed. 

(*********************************************************************************)
(** *** Irreducible forms for substitutions & expressions. *)
(*********************************************************************************)

(** Reducible expression. *)
Inductive ered : forall {k}, expr k -> Prop :=

(** Congruence. *)
| ER_congr_tvar i : qred i -> ered (E_tvar i)
| ER_congr_tctor c al : ered al -> ered (E_tctor c al)
| ER_congr_al_cons {ty} {tys} (a : arg ty) (al : args tys) : ered a \/ ered al -> ered (E_al_cons a al)
| ER_congr_aterm t : ered t -> ered (E_aterm t)
| ER_congr_abind {ty} (a : arg ty) : ered a -> ered (E_abind a) 
| ER_congr_ren {k} r (e : expr k) : rred r \/ ered e -> ered (E_ren r e)
| ER_congr_subst {k} s (e : expr k) : sred s \/ ered e -> ered (E_subst s e)

(** Reduce [E_tvar (r i)] into [(E_tvar i)[S_ren r]]. *)
| ER_extract_rapply r i : ered (E_tvar (Q_rapply r i))
(** Reduce [rename r e] into [substitute (S_ren r) e]. *)
| ER_extract_ren {k} r (e : expr k) : ered (E_ren r e)
(** Push substitutions inside expressions. *)
| ER_push_subst {k} s (e : expr k) : is_push e -> ered (E_subst s e)
(** Reduce [e[sid]] into [e]. *)
| ER_subst_sid {k} (e : expr k) : ered (E_subst S_id e)
(** Reduce [0[t . s]] into [t]. *)
| ER_scons_zero s : is_scons s -> ered (E_subst s (E_tvar Q_zero))

(** Reducible substitutions. *)
with sred : subst -> Prop :=

(** Congruence. *)
| SR_cons t s : ered t \/ sred s -> sred (S_cons t s)
| SR_comp s1 s2 : sred s1 \/ sred s2 -> sred (S_comp s1 s2)
| SR_ren r : rred r -> sred (S_ren r)

(** Reduce [sid >> s] into [s]. *)
| SR_sid_l s : sred (S_comp S_id s)
(** Reduce [s >> sid] into [s]. *)
| SR_sid_r s : sred (S_comp s S_id)
(** Reduce [(s1 >> s2) >> s3] into [s1 >> (s2 >> s3)]. *)
| SR_comp_l s1 s2 s3: sred (S_comp (S_comp s1 s2) s3)
(** Push [S_ren] into renamings. *)
| SR_ren_distrib r : ~is_rmvar r -> sred (S_ren r)
(** Composition distributes over [S_cons]. *)
| SR_cons_l t s1 s2 : sred (S_comp (S_cons t s1) s2)
(** Reduce [shift >> (t . s)] into [s]. *)
| SR_shift_cons s : is_scons s -> sred (S_comp S_shift s)
(** Reduce [0 . shift] into [sid]. *)
| SR_zero_shift : sred (S_cons (E_tvar Q_zero) S_shift)
(** Reduce [s 0 . (shift >> s)] into [s]. *)
(*| SR_zero_shift_l s : sred (S_cons (E_subst s (E_tvar Q_zero)) (S_comp S_shift s))*).

Derive Signature for ered sred.

Hint Constructors ered : core.
Hint Constructors sred : core.

(** Irreducible expressions/substitutions. *)
Definition eirred {k} (e : expr k) := ~ered e.
Definition sirred s := ~sred s.

(*********************************************************************************)
(** *** Characterization of irreducible forms for expressions & substitutions. *)
(*********************************************************************************)

Lemma eirred_tvar i : 
  eirred (E_tvar i) <-> ~is_qrapply i /\ ~is_qsucc i.
Proof. 
split ; intros H.
- split ; intros H' ; apply H ; destruct i ; triv.
- intros H'. destruct H. destruct i ; triv.
  + depelim H'. depelim H1.
  + depelim H'. depelim H1.
Qed.

Lemma eirred_tvar_zero : eirred (E_tvar Q_zero).
Proof. intros H. depelim H. depelim H. Qed.

Lemma eirred_mvar m : eirred (E_mvar m).
Proof. intros H. depelim H. Qed.

Lemma eirred_tctor c al : eirred (E_tctor c al) <-> eirred al.
Proof. split ; intros H H' ; apply H ; triv. now depelim H'. Qed.

Lemma eirred_al_nil : eirred E_al_nil.
Proof. intros H ; depelim H. Qed.

Lemma eirred_al_cons {ty tys} (a : arg ty) (al : args tys) :
  eirred (E_al_cons a al) <-> eirred a /\ eirred al.
Proof.
split ; intros H.
- split ; intros H' ; apply H ; triv.
- intros H' ; depelim H' ; triv. destruct H0 ; triv.
Qed.

Lemma eirred_abase b x : eirred (E_abase b x).
Proof. triv. Qed.

Lemma eirred_aterm t : eirred (E_aterm t) <-> eirred t.
Proof. split ; intros H H' ; apply H ; triv. now depelim H'. Qed.

Lemma eirred_abind {ty} (a : arg ty) : 
  eirred (E_abind a) <-> eirred a.
Proof. split ; intros H H' ; apply H ; triv. now depelim H'. Qed.

Lemma eirred_ren {k} (e : expr k) r : ~eirred (E_ren r e).
Proof. intros H ; apply H. triv. Qed.

Lemma eirred_subst {k} (e : expr k) s :
  eirred (E_subst s e) <->
    eirred e /\ sirred s /\ ~is_push e /\
    ~(is_tvar_zero e /\ is_scons s) /\ s <> S_id.
Proof.
split ; intros H.
- split5 ; intros H' ; apply H ; triv.
  destruct e ; triv. destruct q ; triv. destruct s ; triv.
- intros H' ; depelim H' ; triv.
  + destruct H0 ; triv.
  + destruct s ; triv.
    destruct H as (_ & _ & _ & H & _). triv.
Qed.     

Lemma sirred_mvar m : sirred (S_mvar m).
Proof. intros H. depelim H. Qed.

Lemma sirred_cons t s : 
  sirred (S_cons t s) <-> 
    eirred t /\ sirred s /\ ~(t = E_tvar Q_zero /\ s = S_shift).
Proof.
split ; intros H.
- split3 ; intros H' ; apply H ; clear H.
  + constructor ; now left.
  + constructor ; now right.
  + destruct H' ; subst. now constructor. 
- intros H'. depelim H'. destruct H0 ; triv. destruct H as (_ & _ & H). triv.
Qed.   

Lemma sirred_ren r : sirred (S_ren r) <-> is_rmvar r.
Proof.
split ; intros H.
- destruct r ; triv. all: exfalso ; apply H ; now constructor.
- intros H' ; depelim H' ; triv. destruct r ; triv.
Qed.

Lemma sirred_comp s1 s2 : 
  sirred (S_comp s1 s2) <->
    sirred s1 /\ sirred s2 /\ ~is_scomp s1 /\ ~is_scons s1 /\ 
    s1 <> S_id /\ s2 <> S_id /\ ~(s1 = S_shift /\ is_scons s2).
Proof.
split ; intros H.
- split7 ; intros H' ; apply H ; triv.
  + destruct s1 ; triv.
  + destruct s1 ; triv.
  + destruct H' as [-> H']. destruct s2 ; triv.
- intros H' ; depelim H' ; triv.
  + destruct H0 ; triv.
  + destruct H as (_ & _ & H & _) ; triv.
  + destruct H as (_ & _ & _ & H & _) ; triv.
  + destruct s2 ; triv. destruct H as (_ & _ & _ & _ & _ & _ & H). triv.
Qed. 

End Make.
