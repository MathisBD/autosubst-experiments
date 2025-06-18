From Prototype Require Import Prelude Sig ExplicitSyntax.

(** This file defines a simplification algorithm on explicit syntax. 
    
    We first define simplification as a rewriting system ([qred], [rred], 
    [ered], [sred]) which is proved sound with respect to evaluation
    (lemmas [ered_sound], [sred_sound], etc).
    
    We then implement simplification functions ([qsimp], [rsimp], [esimp], 
    [ssimp]). We prove that the simplification functions indeed implement
    the rewriting system (lemmas [esimp_red], [ssimp_red], etc) and that 
    they compute irreducible forms (lemmas [esimp_irreducible], 
    [ssimp_irreducible], etc). *)

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
  match t with E_var _ => true | _ => false end.
Definition is_tvar_zero {k} (t : expr k) :=
  match t with E_var Q_zero => true | _ => false end.
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
| rred_special r : R_cons (Q_rapply r Q_zero) (R_comp R_shift r) =r=> r

where "i =q=> i'" := (qred i i')
  and "r =r=> r'" := (rred r r').

Inductive ered : forall {k}, expr k -> expr k -> Prop :=
(* Preorder. *)
| ered_refl {k} : reflexive (expr k) ered
| ered_trans {k} : transitive (expr k) ered
(* Congruence. *)
| ered_congr_tvar : Proper (qred ==> ered) E_var
| ered_congr_tctor c : Proper (ered ==> ered) (E_ctor c)
| ered_congr_al_cons {ty tys} : Proper (ered ==> ered ==> ered) (@E_al_cons _ ty tys)
| ered_congr_aterm : Proper (ered ==> ered) E_aterm
| ered_congr_abind {ty} : Proper (ered ==> ered) (@E_abind _ ty)
| ered_congr_afunctor {ty} f sh : Proper (vec_eq ered ==> ered) (@E_afunctor _ ty f sh)
| ered_congr_sapply : Proper (sred ==> qred ==> ered) E_sapply
| ered_congr_ren {k} : Proper (rred ==> ered ==> ered) (@E_ren _ k)
| ered_congr_subst {k} : Proper (sred ==> ered ==> ered) (@E_subst _ k)
(* Extract renamings/substitutions into [E_subst]. *)
| ered_rapply r i : E_var (Q_rapply r i) =e=> E_ren r (E_var i)
| ered_ren {k} r (t : expr k) : E_ren r t =e=> E_subst (S_ren r) t
| ered_sapply s i : E_sapply s i =e=> E_subst s (E_var i)
(* Simplification rules. *)
| ered_subst_ctor s c al : E_subst s (E_ctor c al) =e=> E_ctor c (E_subst s al)
| ered_subst_al_nil s : E_subst s E_al_nil =e=> E_al_nil
| ered_subst_al_cons {ty tys} s (a : expr (Ka ty)) (al : expr (Kal tys)) : 
    E_subst s (E_al_cons a al) =e=> E_al_cons (E_subst s a) (E_subst s al)
| ered_subst_abase s b x : E_subst s (E_abase b x) =e=> E_abase b x
| ered_subst_afunctor {ty} s f sh (al : vec (expr (Ka ty)) _) : 
    E_subst s (E_afunctor f sh al) =e=> E_afunctor f sh (vec_map (E_subst s) al) 
| ered_subst_aterm s t : E_subst s (E_aterm t) =e=> E_aterm (E_subst s t)
| ered_subst_abind {ty} s (a : expr (Ka ty)) : 
    E_subst s (E_abind a) =e=> E_abind (E_subst (S_cons (E_var Q_zero) (S_comp s S_shift)) a)
| ered_subst_subst {k} s1 s2 (t : expr k) : 
    E_subst s2 (E_subst s1 t) =e=> E_subst (S_comp s1 s2) t
| ered_subst_id {k} (t : expr k) : E_subst S_id t =e=> t
| ered_subst_cons_zero t s : E_subst (S_cons t s) (E_var Q_zero) =e=> t

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
| sred_zero_shift : S_cons (E_var Q_zero) S_shift =s=> S_id
| sred_sren_id : S_ren R_id =s=> S_id
| sred_sren_shift : S_ren R_shift =s=> S_shift
| sred_sren_cons i r : S_ren (R_cons i r) =s=> S_cons (E_var i) (S_ren r)
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
Proof. constructor ; eauto. Qed.
#[export] Instance rred_preorder : PreOrder rred.
Proof. constructor ; eauto. Qed.
#[export] Instance ered_preorder k : PreOrder (@ered k).
Proof. constructor ; [apply ered_refl | apply ered_trans]. Qed.
#[export] Instance sred_preorder : PreOrder sred.
Proof. constructor ; eauto. Qed.

#[export] Existing Instance qred_congr_succ.
#[export] Existing Instance qred_congr_rapply.
#[export] Existing Instance rred_congr_cons.
#[export] Existing Instance rred_congr_comp.
#[export] Existing Instance ered_congr_tvar.
#[export] Existing Instance ered_congr_tctor.
#[export] Existing Instance ered_congr_al_cons.
#[export] Existing Instance ered_congr_aterm.
#[export] Existing Instance ered_congr_abind.
#[export] Existing Instance ered_congr_afunctor.
#[export] Existing Instance ered_congr_sapply.
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
apply qred_rred_ind ; intros ; simp qeval ; eauto ; try easy.
all: try solve [ now rewrite H0, H2 ].
- now rewrite P.rcomp_rcons_distrib.
- intros [|] ; reflexivity.
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
apply ered_sred_ind ; intros ; simp eeval qeval ; eauto ; try easy.
all: try solve [ now rewrite H0 | now rewrite H0, H2 ]. 
- eapply qred_sound in H. now rewrite H.
- f_equal. apply vec_ext. intros i. simp vec_nth.
- eapply qred_sound in H1. now rewrite H0, H1. 
- eapply rred_sound in H. now rewrite H1, H.
- now rewrite P.ren_is_subst.
- simp substitute. f_equal. apply vec_ext. intros i. simp vec_nth. 
- simp substitute. rewrite P.up_subst_alt. reflexivity.
- now rewrite P.subst_subst.
- now rewrite P.subst_sid.
- eapply rred_sound in H. now rewrite H.
- now rewrite P.scomp_sid_r.
- now rewrite P.scomp_assoc.
- now rewrite P.scomp_scons_distrib.
- now rewrite P.sid_scons.
- intros [|] ; reflexivity.      
Qed.

Lemma ered_sound {k} e (t t' : expr k) : t =e=> t' -> eeval e t = eeval e t'.
Proof. now apply ered_sred_sound. Qed.

Lemma sred_sound e s s' : s =s=> s' -> seval e s =₁ seval e s'.
Proof. now apply ered_sred_sound. Qed.

(*********************************************************************************)
(** *** Irreducible & reducible forms. *)
(*********************************************************************************)

(** The "true" definition of irreducible forms (terms in which we can't 
    reduce). This definition is obviously correct but is hard to work with. *)
Definition qirreducible i := forall i', i =q=> i' -> i = i'.
Definition rirreducible r := forall r', r =r=> r' -> r = r'.
Definition eirreducible {k} (t : expr k) := forall t', t =e=> t' -> t = t'.
Definition sirreducible s := forall s', s =s=> s' -> s = s'.

(** A special type of renamings in which we can apply the "special" 
    reduction [rred_special] (for lack of a better name). *)
Inductive rspecial : ren -> Prop :=
| rspecial_intro r : rspecial (R_cons (Q_rapply r Q_zero) (R_comp R_shift r)).
Derive Signature for rspecial.
  
(** Expressions in which we can push substitutions. *)
Definition is_push {k} (e : expr k) : bool :=
  match e with E_mvar _ | E_var _ | E_ren _ _ | E_sapply _ _ => false | _ => true end.

Unset Elimination Schemes.

(** A definition of reducible forms (terms in which we can reduce)
    which is easy to work with but is not obviously correct.
    We prove below that this notion agrees with [qirreducible], [rirreducible], etc. *)
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
| rreducible_zero_shift : rreducible (R_cons Q_zero R_shift)
| rreducible_special r : rspecial r -> rreducible r.

Inductive ereducible : forall {k}, expr k -> Prop :=
(* Congruence. *)
| ereducible_congr_tvar i : qreducible i -> ereducible (E_var i)
| ereducible_congr_tctor c al : ereducible al -> ereducible (E_ctor c al)
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
| ereducible_rapply r i : ereducible (E_var (Q_rapply r i))
| ereducible_ren {k} r (e : expr k) : ereducible (E_ren r e)
| ereducible_sapply s i : ereducible (E_sapply s i)
| ereducible_subst {k} s (e : expr k) : is_push e -> ereducible (E_subst s e)
| ereducible_subst_id {k} (e : expr k) : ereducible (E_subst S_id e)
| ereducible_subst_cons_zero s : is_scons s -> ereducible (E_subst s (E_var Q_zero))

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
| sreducible_cons_zero_shift : sreducible (S_cons (E_var Q_zero) S_shift)
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

(** [inv_subterm H] checks if [H] is an equality between 
    expressions/substitutions/etc where one side is a subterm of the other,
    and if so it solves the goal. *)
Ltac inv_subterm H :=
  lazymatch type of H with 
  | @eq qnat _ _ => apply (f_equal qsize) in H ; simp qsize in H ; lia
  | @eq ren _ _ => apply (f_equal rsize) in H ; simp qsize in H ; lia
  | @eq (expr _) _ _ => apply (f_equal esize) in H ; simp esize in H ; lia
  | @eq subst _ _ => apply (f_equal ssize) in H ; simp esize in H ; lia
  end. 

Lemma qr_red_impl_reducible : 
  (forall i i', i =q=> i' -> i = i' \/ qreducible i) /\ 
  (forall r r', r =r=> r' -> r = r' \/ rreducible r).
Proof.
apply qred_rred_ind ; intros ; auto.
all: try solve [ destruct H0, H2 ; subst ; auto ].
right. now constructor.
Qed.

Lemma qr_reducible_impl_red : 
  (forall i, qreducible i -> exists i', i =q=> i' /\ i <> i') /\
  (forall r, rreducible r -> exists r', r =r=> r' /\ r <> r').
Proof.
apply qreducible_rreducible_ind ; intros ; auto.
all: try solve [ destruct H0 as (i' & H1 & H2) ; eexists ; split ; 
  [now rewrite H1 | intros H3 ; now depelim H3] ].
- exists i. split ; auto. intros H ; inv_subterm H.
- exists (Q_rapply (R_comp r2 r1) i). split ; auto. intros H ; depelim H.
  inv_subterm H.
- destruct r ; try easy. exists q. split ; auto. intros H1. inv_subterm H1.
- exists (Q_rapply R_shift i). split ; easy.
- exists r. split ; auto. intros H. inv_subterm H.
- exists r. split ; auto. intros H. inv_subterm H.
- exists (R_comp r1 (R_comp r2 r3)). split ; auto. intros H. depelim H. inv_subterm H.
- exists (R_cons (Q_rapply r2 i) (R_comp r1 r2)). split ; easy.
- destruct r ; try easy. exists r. split ; auto. intros H1. inv_subterm H1.
- exists R_id. split ; easy.
- destruct H. exists r. split ; auto. intros H. inv_subterm H. 
Qed.

Lemma es_red_impl_reducible : 
  (forall {k} (t t' : expr k), t =e=> t' -> t = t' \/ ereducible t) /\ 
  (forall s s', s =s=> s' -> s = s' \/ sreducible s).
Proof.
apply ered_sred_ind ; intros ; auto.
all: try solve [ destruct H0 ; subst ; auto | destruct H0, H2 ; subst ; auto ].
- apply qr_red_impl_reducible in H. destruct H ; subst ; auto.
- admit.
- apply qr_red_impl_reducible in H. destruct H ; subst ; auto.
- right ; eapply sreducible_sren ; simp dest_ren ; subst ; easy. 
- right ; eapply sreducible_sren ; simp dest_ren ; subst ; easy.
- right ; eapply sreducible_sren ; simp dest_ren ; subst ; easy. 
- right ; eapply sreducible_sren ; simp dest_ren ; subst ; easy.  
Admitted.

Lemma es_reducible_impl_red : 
  (forall {k} (t : expr k), ereducible t -> exists t', t =e=> t' /\ t <> t') /\
  (forall s, sreducible s -> exists s', s =s=> s' /\ s <> s').
Proof.
apply ereducible_sreducible_ind ; intros.
all: try solve [ destruct H0 as (i' & H1 & H2) ; eexists ; split ; 
  [now rewrite H1 | intros H3 ; now depelim H3] ].
all: try solve [ apply qr_reducible_impl_red in H ; destruct H as (i' & H1 & H2) ;
  eexists ; split ; [now rewrite H1 | intros H3 ; now depelim H3] ].
- destruct H0 as (i' & H1 & H2). eexists. split ; [now rewrite H1 | intros H3].
  inversion H3. unshelve eapply inj_right_pair in H4.
  + apply Sig.ctor_EqDec.
  + auto.
- now exists (E_ren r (E_var i)).
- now eexists.
- now eexists.
- destruct e ; try solve [ eexists ; easy ]. Unshelve. all: try easy.
  + exists (E_afunctor f sh) 
  exists (E_subst (S_comp s0 s) e). split ; auto. intros H1. depelim H1. 
  inv_subterm H0. 
- exists e. split ; auto. intros H. inv_subterm H.
- destruct s ; auto. exists e. split ; auto. intros H1. inv_subterm H1.
- exists s. split ; auto. intros H. inv_subterm H. 
- exists s. split ; auto. intros H. inv_subterm H. 
- exists (S_comp s1 (S_comp s2 s3)). split ; auto. intros H. 
  depelim H. inv_subterm H.
- exists (S_cons (E_subst s2 t) (S_comp s1 s2)). split ; auto.
- destruct s ; auto. exists s. split ; auto. intros H1. inv_subterm H1.
- exists S_id. auto.
- destruct r ; eexists ; auto.
Qed.   

Lemma qirreducible_qreducible i : qirreducible i <-> ~qreducible i.
Proof.
split.
- intros H H'. apply qr_reducible_impl_red in H'. destruct H' as (i' & H1 & H2). auto.
- intros H i' Hi. apply qr_red_impl_reducible in Hi. destruct Hi ; auto.
Qed.

Lemma rirreducible_rreducible r : rirreducible r <-> ~rreducible r.
Proof.
split.
- intros H H'. apply qr_reducible_impl_red in H'. destruct H' as (r' & H1 & H2). auto.
- intros H r' Hr. apply qr_red_impl_reducible in Hr. destruct Hr ; auto.
Qed.

Lemma eirreducible_ereducible {k} (t : expr k) : eirreducible t <-> ~ereducible t.
Proof.
split.
- intros H H'. apply es_reducible_impl_red in H'. destruct H' as (t' & H1 & H2). auto.
- intros H t' Ht. apply es_red_impl_reducible in Ht. destruct Ht ; auto.
Qed.

Lemma sirreducible_sreducible s : sirreducible s <-> ~sreducible s.
Proof.
split.
- intros H H'. apply es_reducible_impl_red in H'. destruct H' as (s' & H1 & H2). auto.
- intros H s' Hs. apply es_red_impl_reducible in Hs. destruct Hs ; auto.
Qed.

Ltac change_irred :=
  (repeat rewrite qirreducible_qreducible in *) ;
  (repeat rewrite rirreducible_rreducible in *) ;
  (repeat rewrite eirreducible_ereducible in *) ;
  (repeat rewrite sirreducible_sreducible in *).

(*********************************************************************************)
(** *** Characterization of irreducible forms. *)
(*********************************************************************************)

Lemma qirreducible_zero : qirreducible Q_zero.
Proof. change_irred. auto. Qed.
#[local] Hint Resolve qirreducible_zero : core.

Lemma qirreducible_succ i : ~qirreducible (Q_succ i).
Proof. change_irred. intros H. apply H. now constructor. Qed.
#[local] Hint Resolve qirreducible_succ : core.
  
Lemma qirreducible_rapply r i : 
  qirreducible (Q_rapply r i) <-> 
    rirreducible r /\ qirreducible i /\ r <> R_id /\ ~is_qrapply i /\
    ~(is_rcons r /\ i = Q_zero).
Proof. 
change_irred. split ; intros H. 
- split5 ; intros H' ; apply H ; auto.
  + destruct i ; auto.
  + destruct r ; auto. destruct H' as (_ & ->). auto.
- intros H' ; depelim H' ; auto.
  + destruct H as (_ & _ & _ & H & _). auto.
  + destruct r ; auto. destruct H as (_ & _ & _ & _ & H). auto.
Qed.

Lemma qirreducible_mvar m : qirreducible (Q_mvar m).
Proof. change_irred. intros H. depelim H. Qed.
#[local] Hint Resolve qirreducible_mvar : core.

Lemma rirreducible_id : rirreducible R_id.
Proof. change_irred. intros H. depelim H. depelim H. Qed.
#[local] Hint Resolve rirreducible_id : core.

Lemma rirreducible_shift : rirreducible R_shift.
Proof. change_irred. intros H. depelim H. depelim H. Qed.
#[local] Hint Resolve rirreducible_shift : core.

Lemma rirreducible_cons i r : 
  rirreducible (R_cons i r) <-> 
    qirreducible i /\ rirreducible r /\ 
    ~(i = Q_zero /\ r = R_shift) /\ ~rspecial (R_cons i r).
Proof.
change_irred. split.
- intros H. split4 ; intros H' ; apply H ; auto.
  destruct H' ; subst. now constructor.
- intros (H1 & H2 & H3 & H4) H. depelim H ; auto. 
Qed.

Lemma rirreducible_comp r1 r2 : 
  rirreducible (R_comp r1 r2) <->
    rirreducible r1 /\ rirreducible r2 /\ ~is_rcomp r1 /\ ~is_rcons r1 /\ 
    r1 <> R_id /\ r2 <> R_id /\ ~(r1 = R_shift /\ is_rcons r2).
Proof.
change_irred. split ; intros H.
- split7 ; intros H' ; apply H ; auto.
  + destruct r1 ; auto.
  + destruct r1 ; auto.
  + destruct H' as [-> H']. destruct r2 ; auto.
- intros H' ; depelim H' ; auto.
  + destruct H as (_ & _ & H & _) ; auto.
  + destruct H as (_ & _ & _ & H & _) ; auto.
  + destruct r2 ; auto. destruct H as (_ & _ & _ & _ & _ & _ & H). auto.
Qed. 

Lemma rirreducible_mvar m : rirreducible (R_mvar m).
Proof. change_irred. intros H. depelim H. depelim H. Qed.
#[local] Hint Resolve rirreducible_mvar : core.

Lemma eirreduciblE_var i : 
  eirreducible (E_var i) <-> ~is_qrapply i /\ ~is_qsucc i.
Proof. 
change_irred. split ; intros H.
- split ; intros H' ; apply H ; destruct i ; auto.
- intros H'. destruct H. destruct i ; auto.
  + depelim H' ; auto.
  + depelim H' ; auto.
Qed.

Lemma eirreduciblE_var_zero : eirreducible (E_var Q_zero).
Proof. change_irred. intros H. depelim H ; auto. Qed.
#[local] Hint Resolve eirreduciblE_var_zero : core.

Lemma eirreduciblE_ctor c al : eirreducible (E_ctor c al) <-> eirreducible al.
Proof. change_irred. split ; intros H H' ; apply H ; auto. now depelim H'. Qed.

Lemma eirreducible_al_nil : eirreducible E_al_nil.
Proof. change_irred. intros H ; depelim H. Qed.
#[local] Hint Resolve eirreducible_al_nil : core.

Lemma eirreducible_al_cons {ty tys} (a : expr (Ka ty)) (al : expr (Kal tys)) :
  eirreducible (E_al_cons a al) <-> eirreducible a /\ eirreducible al.
Proof.
change_irred. split ; intros H.
- split ; intros H' ; apply H ; auto.
- intros H' ; depelim H' ; auto.
Qed.

Lemma eirreducible_abase b x : eirreducible (E_abase b x).
Proof. change_irred. auto. Qed.
#[local] Hint Resolve eirreducible_abase : core.

Lemma eirreducible_aterm t : eirreducible (E_aterm t) <-> eirreducible t.
Proof. change_irred. split ; intros H H' ; apply H ; auto. now depelim H'. Qed.

Lemma eirreducible_abind {ty} (a : expr (Ka ty)) : 
  eirreducible (E_abind a) <-> eirreducible a.
Proof. change_irred. split ; intros H H' ; apply H ; auto. now depelim H'. Qed.

Lemma eirreducible_sapply s i : ~eirreducible (E_sapply s i).
Proof. change_irred. auto. Qed.

Lemma eirreducible_ren {k} (e : expr k) r : ~eirreducible (E_ren r e).
Proof. change_irred. auto. Qed.
    
Lemma eirreducible_subst {k} (e : expr k) s :
  eirreducible (E_subst s e) <->
    eirreducible e /\ sirreducible s /\ ~is_push e /\
    ~(is_tvar_zero e /\ is_scons s) /\ s <> S_id.
Proof.
change_irred. split ; intros H.
- split5 ; auto. destruct e ; auto. destruct q ; auto. destruct s ; auto.
- intros H' ; depelim H' ; auto.
  destruct s ; auto. destruct H as (_ & _ & _ & H & _). auto.
Qed.     

Lemma eirreducible_mvar m : eirreducible (E_mvar m).
Proof. change_irred. auto. Qed.
#[local] Hint Resolve eirreducible_mvar : core.

Lemma sirreducible_id : sirreducible S_id.
Proof. change_irred. auto. Qed.
#[local] Hint Resolve sirreducible_id : core.

Lemma sirreducible_shift : sirreducible S_shift.
Proof. change_irred. auto. Qed.
#[local] Hint Resolve sirreducible_shift : core.

Lemma sirreducible_cons t s : 
  sirreducible (S_cons t s) <-> 
    eirreducible t /\ sirreducible s /\ ~(t = E_var Q_zero /\ s = S_shift).
Proof.
change_irred. split ; intros H.
- split3 ; intros H' ; apply H ; auto.
  destruct H' ; subst. now constructor. 
- intros H'. depelim H' ; auto. destruct H as (_ & _ & H). auto.
Qed.   

Lemma sirreducible_comp s1 s2 : 
  sirreducible (S_comp s1 s2) <->
    sirreducible s1 /\ sirreducible s2 /\ ~is_scomp s1 /\ ~is_scons s1 /\ 
    s1 <> S_id /\ s2 <> S_id /\ ~(s1 = S_shift /\ is_scons s2).
Proof.
change_irred. split ; intros H.
- split7 ; intros H' ; apply H ; auto.
  + destruct s1 ; auto.
  + destruct s1 ; auto.
  + destruct H' as [-> H']. destruct s2 ; auto.
- intros H' ; depelim H' ; auto.
  + destruct H as (_ & _ & H & _) ; auto.
  + destruct H as (_ & _ & _ & H & _) ; auto.
  + destruct s2 ; auto. destruct H as (_ & _ & _ & _ & _ & _ & H). auto.
Qed. 

Lemma sirreducible_ren r : sirreducible (S_ren r) <-> is_rmvar r.
Proof.
change_irred. split ; intros H.
- destruct r ; auto. all: exfalso ; apply H ; now constructor.
- intros H' ; depelim H' ; auto. destruct r ; auto. depelim H0. depelim H0.
Qed.

Lemma sirreducible_mvar m : sirreducible (S_mvar m).
Proof. change_irred. intros H. depelim H. Qed.
#[local] Hint Resolve sirreducible_mvar : core.

(*********************************************************************************)
(** *** [dest_rspecial]. *)
(*********************************************************************************)

(** [dest_rspecial i r] tests if we can apply the "special" reduction 
    [rred_special] in [R_cons i r], and if so returns the result [r']
    of the one-step reduction [R_cons i r =r=> r']. *)
Equations dest_rspecial : qnat -> ren -> option ren :=
dest_rspecial (Q_rapply r1 Q_zero) (R_comp R_shift r2) :=
  if eq_ren r1 r2 then Some r1 else None ;
dest_rspecial _ _ := None.

Lemma dest_rspecial_spec i r : 
  (exists r', dest_rspecial i r = Some r') <-> rspecial (R_cons i r).
Proof.
split ; intros H.
- destruct H. destruct i ; auto. destruct i ; auto. destruct r ; auto. destruct r1 ; auto.
  simp dest_rspecial in H. destruct (eq_ren_spec r0 r2) ; auto. subst.
  depelim H. constructor.
- depelim H. exists r0. simp dest_rspecial. destruct (eq_ren_spec r0 r0) ; auto.
Qed.

Lemma dest_rspecial_red i r r' : 
  dest_rspecial i r = Some r' -> R_cons i r =r=> r'.
Proof.
intros H. assert (H1 : rspecial (R_cons i r)). 
{ rewrite <-dest_rspecial_spec. eauto. }
depelim H1. simp dest_rspecial in H. destruct (eq_ren_spec r0 r0) ; auto.
depelim H. auto.
Qed.

Lemma dest_rspecial_irreducible i r r' : 
  qirreducible i -> rirreducible r -> dest_rspecial i r = Some r' ->
  rirreducible r'.
Proof. 
intros H1 H2 H3. assert (H4 : rspecial (R_cons i r)).
{ rewrite <-dest_rspecial_spec. eauto. }
depelim H4. simp dest_rspecial in H3. destruct (eq_ren_spec r0 r0) ; auto.
depelim H3. now rewrite rirreducible_comp in H2.
Qed.

(*********************************************************************************)
(** *** [rcons] *)
(*********************************************************************************)

(** Simplify [R_cons i r]. *)
Equations rcons : qnat -> ren -> ren :=
rcons Q_zero R_shift := R_id ;
rcons a b with dest_rspecial a b := {
  | Some r => r 
  | None => R_cons a b
  }.
  
Lemma rcons_red i r : R_cons i r =r=> rcons i r.
Proof. 
funelim (rcons i r) ; auto. remember (Q_rapply r0 q0) as a. clear Heqa.
rewrite dest_rspecial_red ; [|eassumption]. auto.
Qed.
#[local] Hint Rewrite <-rcons_red : red.

Lemma rcons_irreducible i r :
  qirreducible i -> rirreducible r -> rirreducible (rcons i r).
Proof.
intros H1 H2. funelim (rcons i r) ; auto.
all: try solve [ rewrite rirreducible_cons ; auto ].
- apply dest_rspecial_irreducible in Heq ; auto.
- remember (Q_rapply r0 q0) as a. clear Heqa. rewrite rirreducible_cons.
  split4 ; auto.
  + intros (-> & ->). auto.
  + rewrite <-dest_rspecial_spec. intros (? & H3). rewrite H3 in Heq. auto.
Qed. 

(*********************************************************************************)
(** *** [rapply_aux] *)
(*********************************************************************************)

(** Helper function for [rapply] which takes care of the cases:
   - [r] is the identity.
   - [r] is [R_cons _ _] and [i] is [Q_zero]. *)
Equations rapply_aux (r : ren) (i : qnat) : qnat :=
rapply_aux R_id i := i ;
rapply_aux (R_cons k r) Q_zero := k ;
rapply_aux r i := Q_rapply r i.

Lemma rapply_aux_red r i : Q_rapply r i =q=> rapply_aux r i.
Proof. funelim (rapply_aux r i) ; auto. Qed.
#[local] Hint Rewrite <-rapply_aux_red : red.

Lemma rapply_aux_irreducible r i : 
  rirreducible r -> qirreducible i -> 
  (r <> R_id -> ~(is_rcons r /\ i = Q_zero) -> qirreducible (Q_rapply r i)) -> 
  qirreducible (rapply_aux r i).
Proof.
intros H1 H2 H3. funelim (rapply_aux r i) ; auto.
all: try solve [ apply H3 ; auto ].
rewrite rirreducible_cons in H1 ; auto.
Qed.   

(*********************************************************************************)
(** *** [rcomp_aux] *)
(*********************************************************************************)

(** Helper function for [rcomp] which takes care of the cases:
    - [r2] is the identity.
    - [r1] is [R_shift] and [r2] is [R_cons _ _]. *)
Equations rcomp_aux (r1 r2 : ren) : ren :=
rcomp_aux r R_id := r ;
rcomp_aux R_shift (R_cons _ r) := r ;
rcomp_aux r1 r2 := R_comp r1 r2.

Lemma rcomp_aux_red r1 r2 : R_comp r1 r2 =r=> rcomp_aux r1 r2.
Proof. funelim (rcomp_aux r1 r2) ; auto. Qed.
#[local] Hint Rewrite <-rcomp_aux_red : red.

Lemma rcomp_aux_irreducible r1 r2 : 
  rirreducible r1 -> rirreducible r2 -> 
  (r2 <> R_id -> ~(r1 = R_shift /\ is_rcons r2) -> rirreducible (R_comp r1 r2)) -> 
  rirreducible (rcomp_aux r1 r2).
Proof.
intros H1 H2 H3. funelim (rcomp_aux r1 r2) ; auto.
all: try solve [ apply H3 ; now auto ].
now rewrite rirreducible_cons in H2.
Qed.

(*********************************************************************************)
(** *** [rapply] and [rcomp] *)
(*********************************************************************************)

(** Simplify [Q_rapply r i]. *)
Equations rapply (r : ren) (i : qnat) : qnat by struct i := 
rapply r (Q_rapply r' i) := rapply_aux (rcomp r' r) i ;
rapply r i := rapply_aux r i

(** Simplify [R_comp r1 r2]. *)
with rcomp (r1 r2 : ren) : ren by struct r1 :=
rcomp R_id r := r ;
rcomp (R_cons i r1) r2 := rcons (rapply r2 i) (rcomp r1 r2) ;
rcomp (R_comp r1 r2) r3 := rcomp r1 (rcomp r2 r3) ;
rcomp r1 r2 := rcomp_aux r1 r2.

Lemma rapply_rcomp_red :
  (forall r i, Q_rapply r i =q=> rapply r i) *
  (forall r1 r2, R_comp r1 r2 =r=> rcomp r1 r2).
Proof.
apply rapply_elim with 
  (P := fun r i res => Q_rapply r i =q=> res)
  (P0 := fun r1 r2 res => R_comp r1 r2 =r=> res).
all: intros ; simp red ; auto.
- rewrite <-H. auto.
- rewrite <-H, <-H0. auto. 
- rewrite <-H0, <-H. auto. 
Qed.

Lemma rapply_red r i : Q_rapply r i =q=> rapply r i.
Proof. now apply rapply_rcomp_red. Qed.
#[local] Hint Rewrite <-rapply_red : red.

Lemma rcomp_red r1 r2 : R_comp r1 r2 =r=> rcomp r1 r2.
Proof. now apply rapply_rcomp_red. Qed.
#[local] Hint Rewrite <-rcomp_red : red.

Lemma rapply_rcomp_irreducible :
  (forall r i, rirreducible r -> qirreducible i -> qirreducible (rapply r i)) *
  (forall r1 r2, rirreducible r1 -> rirreducible r2 -> rirreducible (rcomp r1 r2)).
Proof.
apply rapply_elim with 
  (P := fun r i res => rirreducible r -> qirreducible i -> qirreducible res)
  (P0 := fun r1 r2 res => rirreducible r1 -> rirreducible r2 -> rirreducible res).
all: intros ; auto.
- apply rapply_aux_irreducible ; auto. intros H1 H2. rewrite qirreducible_rapply ; auto.
- now apply qirreducible_succ in H0.
- rewrite qirreducible_rapply in H1. apply rapply_aux_irreducible ; auto. 
  + now apply H.
  + intros H2 H3. rewrite qirreducible_rapply. split5 ; auto. now apply H.
- apply rapply_aux_irreducible ; auto. intros H1 H2. rewrite qirreducible_rapply.
  split5 ; auto.
- apply rcomp_aux_irreducible ; auto. intros H1 H2. rewrite rirreducible_comp.
  split3 ; auto.
- rewrite rirreducible_cons in *. apply rcons_irreducible.
  + now apply H.
  + now apply H0.
- rewrite rirreducible_comp in H1. apply H0 ; auto. apply H ; auto.
- apply rcomp_aux_irreducible ; auto. intros H1 H2. rewrite rirreducible_comp. auto.
Qed. 

(*********************************************************************************)
(** *** [qsimp] and [rsimp] *)
(*********************************************************************************)

(** Simplify a quoted natural. *)
Equations qsimp : qnat -> qnat :=
qsimp Q_zero := Q_zero ;
qsimp (Q_succ i) := rapply R_shift (qsimp i) ;
qsimp (Q_rapply r i) := rapply (rsimp r) (qsimp i) ;
qsimp (Q_mvar m) := Q_mvar m 

(** Simplify a renaming. *)
with rsimp : ren -> ren :=
rsimp R_id := R_id ;
rsimp R_shift := R_shift ;
rsimp (R_cons i r) := rcons (qsimp i) (rsimp r) ;
rsimp (R_comp r1 r2) := rcomp (rsimp r1) (rsimp r2) ;
rsimp (R_mvar m) := R_mvar m.

Lemma qsimp_rsimp_red :
  (forall i, i =q=> qsimp i) * (forall r, r =r=> rsimp r).
Proof. 
apply qsimp_elim with 
  (P := fun i res => i =q=> res)
  (P0 := fun r res => r =r=> res).
all: intros ; simp red ; auto.
- now rewrite <-H, <-H0.
- now rewrite <-H, <-H0.
- now rewrite <-H, <-H0. 
Qed.    

Lemma qsimp_red i : i =q=> qsimp i.
Proof. now apply qsimp_rsimp_red. Qed.
#[local] Hint Rewrite <-qsimp_red : red.

Lemma rsimp_red r : r =r=> rsimp r.
Proof. now apply qsimp_rsimp_red. Qed.
#[local] Hint Rewrite <-rsimp_red : red.

Lemma qsimp_rsimp_irreducible : 
  (forall i, qirreducible (qsimp i)) * (forall r, rirreducible (rsimp r)).
Proof.
apply qsimp_elim with 
  (P := fun _ res => qirreducible res) 
  (P0 := fun _ res => rirreducible res).
all: intros ; try solve [ auto | change_irred ; auto ].
- now apply rapply_rcomp_irreducible.
- now apply rapply_rcomp_irreducible.
- now apply rcons_irreducible.
- now apply rapply_rcomp_irreducible.
Qed.

Lemma qsimp_irreducible i : qirreducible (qsimp i).
Proof. now apply qsimp_rsimp_irreducible. Qed.

Lemma rsimp_irreducible r : rirreducible (rsimp r).
Proof. now apply qsimp_rsimp_irreducible. Qed.

(*********************************************************************************)
(** *** Cons expressions. *)
(*********************************************************************************)

(** A shift expression is a substitution of the form 
    [sshift >> (sshift >> (sshift >> ...))]. *)
Inductive sexpr : subst -> Prop :=
| sexpr_id : sexpr S_id
| sexpr_shift : sexpr S_shift 
| sexpr_extend s : sexpr s -> sexpr (S_comp S_shift s).
#[local] Hint Constructors sexpr : core.

(** A nat expression is a term of the form [Q_zero] or 
    [E_subst si (E_var Q_zero)] where [si] is a shift expression. *)
Inductive nexpr : expr Kt -> Prop :=
| nexpr_zero : nexpr (E_var Q_zero) 
| nexpr_subst s : sexpr s -> nexpr (E_subst s (E_var Q_zero)).
#[local] Hint Constructors nexpr : core.

(** A cons expression is a substitution of the form 
    [t0 . t1 . t2 . ... . s] where:
    - [s] is a shift expression.
    - each [ti] is a nat expression. *)
Inductive cexpr : subst -> Prop :=
| cexpr_base s : sexpr s -> cexpr s
| cexpr_extend t s : nexpr t -> cexpr s -> cexpr (S_cons t s).
#[local] Hint Constructors cexpr : core.

Derive Signature for sexpr nexpr cexpr.

(*********************************************************************************)
(** *** [scons] *)
(*********************************************************************************)

(** Simplify [S_cons t s]. *)
Equations scons (t : expr Kt) (s : subst) : subst :=
scons (E_var Q_zero) S_shift := S_id ;
scons t s := S_cons t s. 

Lemma scons_red t s : S_cons t s =s=> scons t s. 
Proof. funelim (scons t s) ; auto. Qed.
#[local] Hint Rewrite <-scons_red : red.

Lemma scons_cexpr t s : 
  nexpr t -> cexpr s -> cexpr (scons t s).
Proof. intros H1 H2. funelim (scons t s) ; auto. Qed.

Lemma scons_irreducible t s :
  eirreducible t -> sirreducible s -> sirreducible (scons t s).
Proof.
intros H1 H2. 
funelim (scons t s) ; try solve [ auto | rewrite sirreducible_cons ; auto ].
Qed. 

(*********************************************************************************)
(** *** [ctail] *)
(*********************************************************************************)

(** Tail of a cons expression, i.e. simplify [S_comp S_shift s]. *)
Equations ctail : subst -> subst :=
ctail S_id := S_shift ;
ctail (S_cons _ t) := t ;
ctail s := S_comp S_shift s.

Lemma ctail_red s : S_comp S_shift s =s=> ctail s.
Proof. funelim (ctail s) ; auto. Qed.
#[local] Hint Rewrite <-ctail_red : red.

Lemma ctail_cexpr s : cexpr s -> cexpr (ctail s). 
Proof.
intros H. depelim H.
- depelim H ; simp ctail ; auto.  
- simp ctail.
Qed.

Lemma ctail_irreducible s : 
  cexpr s -> sirreducible s -> sirreducible (ctail s).
Proof.
intros H1 H2. depelim H1.
- depelim H ; simp ctail ; auto.
  + rewrite sirreducible_comp. split7 ; auto.
  + rewrite sirreducible_comp. split7 ; auto.
- simp ctail. rewrite sirreducible_cons in H2. auto.
Qed.

(*********************************************************************************)
(** *** [capply_zero] *)
(*********************************************************************************)

(** Apply a cons expression to [Q_zero]. *)
Equations capply_zero : subst -> expr Kt :=
capply_zero (S_cons t _) := t ;
capply_zero S_id := E_var Q_zero ;
capply_zero s := E_subst s (E_var Q_zero).

Lemma capply_zero_red s : E_subst s (E_var Q_zero) =e=> capply_zero s.
Proof. funelim (capply_zero s) ; auto. Qed.
#[local] Hint Rewrite <-capply_zero_red : red.

Lemma capply_zero_nexpr s : cexpr s -> nexpr (capply_zero s).
Proof.
intros H. depelim H.
- depelim H ; simp capply_zero ; auto.
- simp capply_zero.
Qed.  

Lemma capply_zero_irreducible s : 
  cexpr s -> sirreducible s -> eirreducible (capply_zero s).
Proof.
intros H1 H2. depelim H1.
- depelim H ; simp capply_zero.
  + rewrite eirreduciblE_var. auto.
  + rewrite eirreducible_subst. split5 ; auto.
  + rewrite eirreducible_subst. split5 ; auto.
- simp capply_zero. rewrite sirreducible_cons in H2. auto.
Qed.

(*********************************************************************************)
(** *** [ccomp] *)
(*********************************************************************************)

(** Compose two cons expressions. *)
Equations ccomp (s1 s2 : subst) : subst :=
ccomp S_id s := s ;
ccomp S_shift s := ctail s ;
ccomp (S_comp S_shift s1) s2 := ctail (ccomp s1 s2) ;
ccomp (S_cons t s1) s2 with t := {
  | E_var Q_zero => scons (capply_zero s2) (ccomp s1 s2)
  | E_subst s (E_var Q_zero) => scons (capply_zero (ccomp s s2)) (ccomp s1 s2)
  | _ => S_comp (S_cons t s1) s2 
  } ;
ccomp x y := S_comp x y.

Lemma ccomp_red s1 s2 : S_comp s1 s2 =s=> ccomp s1 s2.
Proof. 
funelim (ccomp s1 s2) ; simp red ; auto.
- rewrite <-H. auto.
- rewrite <-H. auto.
- rewrite <-H, <-H0. rewrite sred_cons_l, ered_subst_subst. reflexivity.
Qed.  
#[local] Hint Rewrite <-ccomp_red : red.   

Lemma ccomp_cexpr_helper s1 s2 : sexpr s1 -> cexpr s2 -> cexpr (ccomp s1 s2).
Proof. intros H1 H2. induction H1 ; simp ccomp ; now apply ctail_cexpr. Qed.

Lemma ccomp_cexpr s1 s2 : cexpr s1 -> cexpr s2 -> cexpr (ccomp s1 s2).
Proof. 
intros H1 H2. induction H1.
- now apply ccomp_cexpr_helper.
- depelim H ; simp ccomp.
  + apply scons_cexpr ; auto. now apply capply_zero_nexpr.
  + apply scons_cexpr ; auto. apply capply_zero_nexpr. 
    now apply ccomp_cexpr_helper.
Qed.

Lemma ccomp_irreducible_helper s1 s2 : 
  sexpr s1 -> cexpr s2 -> sirreducible s1 -> sirreducible s2 -> sirreducible (ccomp s1 s2).
Proof. 
intros H1 H2 H3 H4. induction H1 ; simp ccomp.
- apply ctail_irreducible ; auto.
- apply ctail_irreducible.
  + now apply ccomp_cexpr_helper.
  + apply IHsexpr. rewrite sirreducible_comp in H3. auto.  
Qed.

Lemma ccomp_irreducible s1 s2 : 
  cexpr s1 -> cexpr s2 -> sirreducible s1 -> sirreducible s2 -> sirreducible (ccomp s1 s2).
Proof. 
intros H1 H2 H3 H4. revert s2 H2 H4. induction H1 ; intros s2 H2 H4.
- now apply ccomp_irreducible_helper.   
- destruct H ; simp ccomp.
  + rewrite sirreducible_cons in H3. apply scons_irreducible ; auto.
    * apply capply_zero_irreducible ; auto. 
    * apply IHcexpr ; auto.
  + rewrite sirreducible_cons in H3. destruct H3 as (H3 & H5 & H6).
    rewrite eirreducible_subst in H3. apply scons_irreducible.
    * apply capply_zero_irreducible.
      --apply ccomp_cexpr ; auto.
      --apply ccomp_irreducible_helper ; auto.
    * apply IHcexpr ; auto.
Qed.

(*********************************************************************************)
(** *** [cup] *)
(*********************************************************************************)

(** Lift a [cexpr] through a binder. *)
Definition cup (s : subst) : subst := 
  scons (E_var Q_zero) (ccomp s S_shift).

Lemma cup_red s : S_cons (E_var Q_zero) (S_comp s S_shift) =s=> cup s.
Proof. unfold cup. now simp red. Qed.
#[local] Hint Rewrite <-cup_red : red.

Lemma cup_cexpr s : cexpr s -> cexpr (cup s).
Proof.
intros H. unfold cup. apply scons_cexpr ; auto. apply ccomp_cexpr ; auto.
Qed.

Lemma cup_irreducible s : 
  cexpr s -> sirreducible s -> sirreducible (cup s).
Proof.
intros H1 H2. unfold cup. apply scons_irreducible ; auto.
apply ccomp_irreducible ; auto.
Qed.

(*********************************************************************************)
(** *** [csubstitute_aux] *)
(*********************************************************************************)

(** Helper function for [csubstitute] (and also [substitute]) 
    which takes care of the cases:
    - [s] is the identity.
    - [e] is [E_var Q_zero] and [s] is [S_cons _ _]. *)
Equations csubstitute_aux {k} : subst -> expr k -> expr k :=
csubstitute_aux S_id t := t ;
csubstitute_aux (S_cons t _) (E_var Q_zero) := t ;
csubstitute_aux s t := E_subst s t.

Lemma csubstitute_aux_red {k} s (t : expr k) : 
  E_subst s t =e=> csubstitute_aux s t.
Proof. funelim (csubstitute_aux s t) ; auto. Qed.
#[local] Hint Rewrite <-@csubstitute_aux_red : red.

Lemma csubstitute_aux_irreducible {k} s (t : expr k) : 
  sirreducible s -> eirreducible t -> 
  (s <> S_id -> ~(is_scons s /\ is_tvar_zero t) -> eirreducible (E_subst s t)) ->
  eirreducible (csubstitute_aux s t).
Proof.
intros H1 H2 H3. funelim (csubstitute_aux s t) ; auto.
all: try solve [ apply H3 ; auto ].
rewrite sirreducible_cons in H1. auto.
Qed.

(*********************************************************************************)
(** *** [sccomp_aux] *)
(*********************************************************************************)

(** Helper function for [sccomp] (and also [scomp]) which takes care 
    of the cases:
    - [s1] is [S_shift] and [s2] is [S_cons _ _].
    - [s2] is [S_id]. *)
Equations sccomp_aux : subst -> subst -> subst :=
sccomp_aux S_shift (S_cons _ s) := s ;
sccomp_aux s S_id := s ;
sccomp_aux s1 s2 := S_comp s1 s2.

Lemma sccomp_aux_red s1 s2 : S_comp s1 s2 =s=> sccomp_aux s1 s2.
Proof. funelim (sccomp_aux s1 s2) ; auto. Qed.
#[local] Hint Rewrite <-sccomp_aux_red : red.

Lemma sccomp_aux_irreducible s1 s2 : 
  sirreducible s1 -> sirreducible s2 ->
  (s2 <> S_id -> ~(s1 = S_shift /\ is_scons s2) -> sirreducible (S_comp s1 s2)) ->
  sirreducible (sccomp_aux s1 s2).
Proof.
intros H1 H2 H3. funelim (sccomp_aux s1 s2) ; auto.
all: try solve [apply H3 ; auto ].
rewrite sirreducible_cons in H2. auto.
Qed.

(*********************************************************************************)
(** *** [csubstitute] and [sccomp] *)
(*********************************************************************************)

(** Substitute with a [cexpr]. *)
Equations csubstitute {k} (s : subst) (e : expr k) : expr k by struct e :=
csubstitute s (E_var i) := csubstitute_aux s (E_var i) ;
csubstitute s (E_ctor c al) := E_ctor c (csubstitute s al) ;
csubstitute s E_al_nil := E_al_nil ;
csubstitute s (E_al_cons a al) := E_al_cons (csubstitute s a) (csubstitute s al) ;
csubstitute s (E_abase b x) := E_abase b x ;
csubstitute s (E_aterm t) := E_aterm (csubstitute s t) ;
csubstitute s (E_abind a) := E_abind (csubstitute (cup s) a) ;
csubstitute s2 (E_subst s1 e) := csubstitute_aux (sccomp s1 s2) e ;
csubstitute s e := csubstitute_aux s e 

(** Compose a substitution with a [cexpr]. *)
with sccomp (s1 s2 : subst) : subst by struct s1 :=
sccomp S_id s := s ;
sccomp S_shift s := ctail s ;
sccomp (S_comp s1 s2) s3 := sccomp_aux s1 (sccomp s2 s3) ;
sccomp (S_cons t s1) s2 := scons (csubstitute s2 t) (sccomp s1 s2) ;
sccomp s1 s2 := sccomp_aux s1 s2.

Lemma csubstitute_sccomp_red : 
  (forall {k} s (t : expr k), E_subst s t =e=> csubstitute s t) *
  (forall s1 s2, S_comp s1 s2 =s=> sccomp s1 s2).
Proof.
apply csubstitute_elim with 
  (P := fun _ s t res => E_subst s t =e=> res)
  (P0 := fun s1 s2 res => S_comp s1 s2 =s=> res).
all: intros ; simp red ; auto.
all: try solve [ now rewrite <-H ].
- now rewrite <-H, <-H0.
- rewrite <-H. simp red. auto.
- rewrite <-H, <-H0. auto.
Qed.    

Lemma csubstitute_red {k} s (t : expr k) : E_subst s t =e=> csubstitute s t.
Proof. now apply csubstitute_sccomp_red. Qed.
#[local] Hint Rewrite <-@csubstitute_red : red.

Lemma sccomp_red s1 s2 : S_comp s1 s2 =s=> sccomp s1 s2.
Proof. now apply csubstitute_sccomp_red. Qed.
#[local] Hint Rewrite <-sccomp_red : red.

Lemma csubstitute_sccomp_irreducible : 
  (forall {k} s (t : expr k),
    cexpr s -> sirreducible s -> eirreducible t -> eirreducible (csubstitute s t)) *
  (forall s1 s2, 
    cexpr s2 -> sirreducible s1 -> sirreducible s2 -> sirreducible (sccomp s1 s2)).
Proof.
apply csubstitute_elim with 
  (P := fun _ s t res =>   
    cexpr s -> sirreducible s -> eirreducible t -> eirreducible res)
  (P0 := fun s1 s2 res =>
    cexpr s2 -> sirreducible s1 -> sirreducible s2 -> sirreducible res).
all: intros ; auto.
- apply csubstitute_aux_irreducible ; auto. intros H2 H3. rewrite eirreducible_subst.
  split5 ; auto. intros (H4 & H5) ; auto.
- rewrite eirreduciblE_ctor in *. apply H ; auto.
- apply csubstitute_aux_irreducible ; auto. intros H2 H3. rewrite eirreducible_subst.
  split5 ; auto.
- rewrite eirreducible_al_cons in *. split ; [apply H | apply H0] ; auto.
- rewrite eirreducible_aterm in *. apply H ; auto.
- rewrite eirreducible_abind in *. apply H ; auto.
  * apply cup_cexpr ; auto.
  * apply cup_irreducible ; auto.  
- apply csubstitute_aux_irreducible ; auto. intros H2 H3. rewrite eirreducible_subst.
  split5 ; auto.
- now apply eirreducible_ren in H1.
- rewrite eirreducible_subst in H2. apply csubstitute_aux_irreducible ; auto.
  + now apply H.
  + intros H3 H4. rewrite eirreducible_subst. split5 ; auto.
    * now apply H.
    * intros (? & ?) ; auto.
- simp csubstitute. apply ctail_irreducible ; auto.
- rewrite sirreducible_cons in H2. simp csubstitute. apply scons_irreducible.
  + now apply H.  
  + now apply H0.
- simp csubstitute. rewrite sirreducible_comp in H1.
  apply sccomp_aux_irreducible ; auto.
  + apply H ; auto. 
  + intros H3 H4. rewrite sirreducible_comp. split7 ; auto. apply H ; auto.
- rewrite sirreducible_ren in H0. destruct r ; auto. simp csubstitute.
  apply sccomp_aux_irreducible ; auto.
  + now rewrite sirreducible_ren.
  + intros H2 H3. rewrite sirreducible_comp. split7 ; auto.
    now rewrite sirreducible_ren.
- simp csubstitute. apply sccomp_aux_irreducible ; auto.
  intros H2 H3. rewrite sirreducible_comp. split7 ; auto.
Qed.

(*********************************************************************************)
(** *** [sup] *)
(*********************************************************************************)

(** Lift a substitution through a binder. *)
Definition sup (s : subst) : subst :=
  scons (E_var Q_zero) (sccomp s S_shift).

Lemma sup_red s : S_cons (E_var Q_zero) (S_comp s S_shift) =s=> sup s.
Proof. unfold sup. simp red. auto. Qed.
#[local] Hint Rewrite <-sup_red : red.

Lemma sup_irreducible s : 
  sirreducible s -> sirreducible (sup s).
Proof.
intros H. unfold sup. apply scons_irreducible ; auto.
apply csubstitute_sccomp_irreducible ; auto.
Qed.

(*********************************************************************************)
(** *** [substitute] and [scomp] *)
(*********************************************************************************)

(** We reuse [csubstitute_aux] to define [substitute] 
    and [sccomp_aux] to define [scomp]. *)

(** Substitute in an expression. *)
Equations substitute {k} (s : subst) (e : expr k) : expr k by struct e :=
substitute s (E_var i) := csubstitute_aux s (E_var i) ;
substitute s (E_ctor c al) := E_ctor c (substitute s al) ;
substitute s E_al_nil := E_al_nil ;
substitute s (E_al_cons a al) := E_al_cons (substitute s a) (substitute s al) ;
substitute s (E_abase b x) := E_abase b x ;
substitute s (E_aterm t) := E_aterm (substitute s t) ;
substitute s (E_abind a) := E_abind (substitute (sup s) a) ;
substitute s2 (E_subst s1 e) := csubstitute_aux (scomp s1 s2) e ;
substitute s e := csubstitute_aux s e 

(** Compose two substitutions. *)
with scomp (s1 s2 : subst) : subst by struct s1 :=
scomp S_id s := s ;
scomp S_shift s := sccomp_aux S_shift s ;
scomp (S_comp s1 s2) s3 := sccomp_aux s1 (scomp s2 s3) ;
scomp (S_cons t s1) s2 := scons (substitute s2 t) (scomp s1 s2) ;
scomp s1 s2 := sccomp_aux s1 s2.

Lemma substitute_scomp_red : 
  (forall {k} s (t : expr k), E_subst s t =e=> substitute s t) *
  (forall s1 s2, S_comp s1 s2 =s=> scomp s1 s2).
Proof.
apply substitute_elim with 
  (P := fun _ s t res => E_subst s t =e=> res)
  (P0 := fun s1 s2 res => S_comp s1 s2 =s=> res).
all: intros ; simp red ; auto.
all: try solve [ now rewrite <-H ].
- now rewrite <-H, <-H0.
- rewrite <-H. simp red. auto.
- rewrite <-H, <-H0. auto.
Qed.    

Lemma substitute_red {k} s (t : expr k) : E_subst s t =e=> substitute s t.
Proof. now apply substitute_scomp_red. Qed.
#[local] Hint Rewrite <-@substitute_red : red.

Lemma scomp_red s1 s2 : S_comp s1 s2 =s=> scomp s1 s2.
Proof. now apply substitute_scomp_red. Qed.
#[local] Hint Rewrite <-scomp_red : red.

Lemma substitute_scomp_irreducible : 
  (forall {k} s (t : expr k), sirreducible s -> eirreducible t -> eirreducible (substitute s t)) *
  (forall s1 s2, sirreducible s1 -> sirreducible s2 -> sirreducible (scomp s1 s2)).
Proof.
apply substitute_elim with 
  (P := fun _ s t res => sirreducible s -> eirreducible t -> eirreducible res)
  (P0 := fun s1 s2 res => sirreducible s1 -> sirreducible s2 -> sirreducible res).
all: intros ; simp substitute ; auto.
- apply csubstitute_aux_irreducible ; auto. intros H2 H3. rewrite eirreducible_subst.
  split5 ; auto. intros (H4 & H5) ; auto.
- rewrite eirreduciblE_ctor in *. apply H ; auto.
- apply csubstitute_aux_irreducible ; auto. intros H2 H3. rewrite eirreducible_subst.
  split5 ; auto.
- rewrite eirreducible_al_cons in *. split ; [apply H | apply H0] ; auto.
- rewrite eirreducible_aterm in *. apply H ; auto.
- rewrite eirreducible_abind in *. apply H ; auto.
  apply sup_irreducible ; auto.  
- apply csubstitute_aux_irreducible ; auto. intros H2 H3. rewrite eirreducible_subst.
  split5 ; auto.
- now apply eirreducible_ren in H0.
- rewrite eirreducible_subst in H1. apply csubstitute_aux_irreducible ; auto.
  + now apply H.
  + intros H3 H4. rewrite eirreducible_subst. split5 ; auto.
    * now apply H.
    * intros (? & ?) ; auto.
- apply sccomp_aux_irreducible ; auto.
  intros H1 H2. rewrite sirreducible_comp. split7 ; auto.
- rewrite sirreducible_cons in H1. apply scons_irreducible.
  + now apply H.  
  + now apply H0.
- rewrite sirreducible_comp in H0.
  apply sccomp_aux_irreducible ; auto.
  + apply H ; auto. 
  + intros H3 H4. rewrite sirreducible_comp. split7 ; auto. apply H ; auto.
- rewrite sirreducible_ren in H. destruct r ; auto.
  apply sccomp_aux_irreducible ; auto.
  + now rewrite sirreducible_ren.
  + intros H2 H3. rewrite sirreducible_comp. split7 ; auto.
    now rewrite sirreducible_ren.
- apply sccomp_aux_irreducible ; auto.
  intros H2 H3. rewrite sirreducible_comp. split7 ; auto.
Qed.

(*********************************************************************************)
(** *** [tvar] and [sren] *)
(*********************************************************************************)

(** Simplify [E_var i]. We take care of extracting [Q_rapply] into [E_subst]. *)
Equations tvar : qnat -> expr Kt :=
tvar (Q_rapply r i) := E_subst (sren r) (E_var i) ; 
tvar i := E_var i

(** Simplify [S_ren r]. We rely crucially on the fact that [r] must already 
    be irreducible, so we can use [S_cons] and [S_comp] instead of 
    [scons] and [scomp]. This is important to be able to prove inversion 
    lemmas such as [is_scons (S_ren r) -> is_rcons r]. *)
with sren (r : ren) : subst :=
sren R_id := S_id ;
sren R_shift := S_shift ;
sren (R_cons i r) := S_cons (tvar i) (sren r) ;
sren (R_comp r1 r2) := S_comp (sren r1) (sren r2) ;
sren (R_mvar r) := S_ren (R_mvar r).

Lemma tvar_sren_red : 
  (forall i, E_var i =e=> tvar i) * (forall r, S_ren r =s=> sren r).
Proof.
apply tvar_elim with 
  (P := fun i res => E_var i =e=> res) 
  (P0 := fun r res => S_ren r =s=> res).
all: intros ; simp red ; auto.
- rewrite <-H. rewrite ered_rapply. auto.
- rewrite <-H, <-H0. auto.
- rewrite <-H, <-H0. auto.
Qed.

Lemma tvar_red i : E_var i =e=> tvar i.
Proof. now apply tvar_sren_red. Qed.
#[local] Hint Rewrite <-tvar_red : red.

Lemma sren_red r : S_ren r =s=> sren r.
Proof. now apply tvar_sren_red. Qed.
#[local] Hint Rewrite <-sren_red : red.

Lemma tvar_sren_irreducible : 
  (forall i, qirreducible i -> eirreducible (tvar i)) *
  (forall r, rirreducible r -> sirreducible (sren r)).
Proof.
apply tvar_elim with 
  (P := fun i res => qirreducible i -> eirreducible res)
  (P0 := fun r res => rirreducible r -> sirreducible res).
all: intros ; auto.
- now apply qirreducible_succ in H.
- rewrite qirreducible_rapply in H0. rewrite eirreducible_subst. split5 ; auto.
  + rewrite eirreduciblE_var. destruct i ; auto. destruct H0 as (_ & H0 & _). 
    now apply qirreducible_succ in H0.
  + now apply H.
  + intros (? & ?) ; auto. destruct i ; auto. destruct r ; auto. now apply H0.
  + now destruct r.
- rewrite eirreduciblE_var. auto.
- rewrite rirreducible_cons in H1. rewrite sirreducible_cons. split3 ; auto.
  + now apply H.
  + now apply H0.
  + intros (? & ?). destruct i ; auto. destruct r ; auto.
    destruct H1 as (_ & _ & H1 & _). now apply H1.
- rewrite rirreducible_comp in H1. rewrite sirreducible_comp. split7 ; auto.
  + now apply H.
  + now apply H0.
  + destruct r1 ; auto. 
  + destruct r1 ; auto.
  + destruct r1 ; auto.
  + destruct r2 ; auto.
  + destruct r1, r2 ; auto. exfalso. now apply H1.
- now rewrite sirreducible_ren.
Qed. 

(*********************************************************************************)
(** *** [esimp] and [ssimp] *)
(*********************************************************************************)

(** Simplify an expression. *)
Equations esimp {k} (t : expr k) : expr k :=
esimp (E_var i) := tvar (qsimp i) ;
esimp (E_ctor c al) := E_ctor c (esimp al) ;
esimp E_al_nil := E_al_nil ;
esimp (E_al_cons a al) := E_al_cons (esimp a) (esimp al) ;
esimp (E_abase b x) := E_abase b x ;
esimp (E_aterm t) := E_aterm (esimp t) ;
esimp (E_abind a) := E_abind (esimp a) ;
esimp (E_sapply s i) := substitute (ssimp s) (tvar (qsimp i)) ;
esimp (E_ren r t) := substitute (sren (rsimp r)) (esimp t) ;
esimp (E_subst s t) := substitute (ssimp s) (esimp t) ;
esimp (E_mvar m) := E_mvar m 

(** Simplify a substitution. *)
with ssimp (s : subst) : subst :=
ssimp S_id := S_id ;
ssimp S_shift := S_shift ;
ssimp (S_cons t s) := scons (esimp t) (ssimp s) ;
ssimp (S_comp s1 s2) := scomp (ssimp s1) (ssimp s2) ;
ssimp (S_ren r) := sren (rsimp r) ;
ssimp (S_mvar m) := S_mvar m.

Lemma esimp_ssimp_red :
  (forall {k} (t : expr k), t =e=> esimp t) *
  (forall s, s =s=> ssimp s).
Proof.
apply esimp_elim with 
  (P := fun _ t res => t =e=> res)
  (P0 := fun s res => s =s=> res).
all: intros ; simp red ; auto.
all: solve [ now rewrite <-H | now rewrite <-H, <-H0 ]. 
Qed.

Lemma esimp_red {k} (t : expr k) : t =e=> esimp t.
Proof. now apply esimp_ssimp_red. Qed.
#[local] Hint Rewrite <-@esimp_red : red.

Lemma ssimp_red s : s =s=> ssimp s.
Proof. now apply esimp_ssimp_red. Qed.
#[local] Hint Rewrite <-ssimp_red : red.

Lemma esimp_ssimp_irreducible :
  (forall {k} (t : expr k), eirreducible (esimp t)) *
  (forall s, sirreducible (ssimp s)).
Proof.
apply esimp_elim with 
  (P := fun _ _ res => eirreducible res) 
  (P0 := fun _ res => sirreducible res).
all: intros ; auto.
- apply tvar_sren_irreducible. apply qsimp_irreducible. 
- now rewrite eirreduciblE_ctor.
- now rewrite eirreducible_al_cons.
- now rewrite eirreducible_aterm.
- now rewrite eirreducible_abind.
- apply substitute_scomp_irreducible ; auto.
  apply tvar_sren_irreducible. now apply qsimp_irreducible.
- apply substitute_scomp_irreducible ; auto.
  apply tvar_sren_irreducible. now apply rsimp_irreducible.
- apply substitute_scomp_irreducible ; auto.
- now apply scons_irreducible.
- apply substitute_scomp_irreducible ; auto. 
- apply tvar_sren_irreducible. now apply rsimp_irreducible.
Qed.

Lemma esimp_irreducible {k} (t : expr k) : eirreducible (esimp t).
Proof. now apply esimp_ssimp_irreducible. Qed.

Lemma ssimp_irreducible s : sirreducible (ssimp s).
Proof. now apply esimp_ssimp_irreducible. Qed.

End WithSignature.