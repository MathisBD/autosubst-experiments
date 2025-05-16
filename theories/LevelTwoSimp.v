From Prototype Require Import Prelude Sig.
From Prototype Require LevelOne LevelTwo.
Module P := Prelude.
Module O := LevelOne.
Module T := LevelTwo.
Import T.

(** This file defines a simplification algorithm for level two 
    terms/substitutions. 
    
    We first define simplification as a rewriting system ([qred], [rred], 
    [ered], [sred]), which is proved sound with respect to evaluation
    (lemmas [ered_sound], [sred_sound], etc).
    
    We then implement simplification functions ([qsimp], [rsimp], [esimp], 
    [ssimp]). We prove that the simplification functions indeed implement
    the rewriting system (lemmas [qsimp_red], [rsimp_red], etc), and that 
    they compute irreducible forms (lemmas [qsimp_irreducible], 
    [rsimp_irreducible], etc). *)

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
(* Extract [Q_rapply] into [E_ren]. *)
| ered_rapply r i : E_tvar (Q_rapply r i) =e=> E_ren r (E_tvar i)
(* Simplify renamings. *)
| ered_ren_ctor r c al : E_ren r (E_tctor c al) =e=> E_tctor c (E_ren r al)
| ered_ren_al_nil r : E_ren r E_al_nil =e=> E_al_nil
| ered_ren_al_cons {ty tys} r (a : expr (Ka ty)) (al : expr (Kal tys)) : 
    E_ren r (E_al_cons a al) =e=> E_al_cons (E_ren r a) (E_ren r al)
| ered_ren_abase r b x : E_ren r (E_abase b x) =e=> E_abase b x
| ered_ren_aterm r t : E_ren r (E_aterm t) =e=> E_aterm (E_ren r t)
| ered_ren_abind {ty} r (a : expr (Ka ty)) : 
    E_ren r (E_abind a) =e=> E_abind (E_ren (R_cons Q_zero (R_comp r R_shift)) a)
| ered_ren_ren {k} r1 r2 (t : expr k) : 
    E_ren r2 (E_ren r1 t) =e=> E_ren (R_comp r1 r2) t
| ered_ren_subst {k} r s (t : expr k) : 
    E_ren r (E_subst s t) =e=> E_subst (S_comp s (S_ren r)) t
| ered_ren_id {k} (t : expr k) : E_ren R_id t =e=> t
| ered_ren_cons_zero i r : E_ren (R_cons i r) (E_tvar Q_zero) =e=> E_tvar i
(* Simplify substitutions. *)
| ered_subst_ctor s c al : E_subst s (E_tctor c al) =e=> E_tctor c (E_subst s al)
| ered_subst_al_nil s : E_subst s E_al_nil =e=> E_al_nil
| ered_subst_al_cons {ty tys} s (a : expr (Ka ty)) (al : expr (Kal tys)) : 
    E_subst s (E_al_cons a al) =e=> E_al_cons (E_subst s a) (E_subst s al)
| ered_subst_abase s b x : E_subst s (E_abase b x) =e=> E_abase b x
| ered_subst_aterm s t : E_subst s (E_aterm t) =e=> E_aterm (E_subst s t)
| ered_subst_abind {ty} s (a : expr (Ka ty)) : 
    E_subst s (E_abind a) =e=> E_abind (E_subst (S_cons (E_tvar Q_zero) (S_comp s (S_ren R_shift))) a)
| ered_subst_ren {k} s r (t : expr k) : 
    E_subst s (E_ren r t) =e=> E_subst (S_comp (S_ren r) s) t
| ered_subst_subst {k} s1 s2 (t : expr k) : 
    E_subst s2 (E_subst s1 t) =e=> E_subst (S_comp s1 s2) t
| ered_subst_id {k} (t : expr k) : E_subst S_id t =e=> t
| ered_subst_cons_zero t s : E_subst (S_cons t s) (E_tvar Q_zero) =e=> t
| ered_subst_sren {k} r (t : expr k) : E_subst (S_ren r) t =e=> E_ren r t

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
- now rewrite O.ren_ren.
- rewrite O.ren_subst. apply O.substitute_proper ; triv.
  intros i. cbv [O.srcomp O.scomp]. now rewrite O.ren_is_subst.
- now rewrite O.ren_rid. 
- simp substitute. rewrite O.up_subst_alt. reflexivity.
- rewrite O.subst_ren. apply O.substitute_proper ; triv.
- now rewrite O.subst_subst.
- now rewrite O.subst_sid.
- now rewrite O.ren_is_subst.   
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

(** The "true" definition of irreducible forms (terms in which we can't 
    reduce). This definition is obviously correct but is hard to work with. *)
Definition qirreducible i := forall i', i =q=> i' -> i = i'.
Definition rirreducible r := forall r', r =r=> r' -> r = r'.
Definition eirreducible {k} (t : expr k) := forall t', t =e=> t' -> t = t'.
Definition sirreducible s := forall s', s =s=> s' -> s = s'.

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
| rreducible_zero_shift : rreducible (R_cons Q_zero R_shift).

(** Expressions in which we can push substitutions. *)
Definition is_push {k} (e : expr k) : bool :=
  match e with E_mvar _ | E_tvar _ => false | _ => true end.

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
| ereducible_ren {k} r (e : expr k) : is_push e -> ereducible (E_ren r e)
| ereducible_ren_id {k} (e : expr k) : ereducible (E_ren R_id e)
| ereducible_ren_cons_zero r : is_rcons r -> ereducible (E_ren r (E_tvar Q_zero))
| ereducible_subst {k} s (e : expr k) : is_push e -> ereducible (E_subst s e)
| ereducible_subst_id {k} (e : expr k) : ereducible (E_subst S_id e)
| ereducible_subst_cons_zero s : is_scons s -> ereducible (E_subst s (E_tvar Q_zero))
| ereducible_subst_sren {k} s (e : expr k) : is_sren s -> ereducible (E_subst s e)

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
- exists i. split ; triv. intros H ; inv_subterm H.
- exists (Q_rapply (R_comp r2 r1) i). split ; triv. intros H ; depelim H.
  inv_subterm H.
- destruct r ; triv. exists q. split ; triv. intros H1. inv_subterm H1.
- exists (Q_rapply R_shift i). split ; triv.
- exists r. split ; triv. intros H. inv_subterm H.
- exists r. split ; triv. intros H. inv_subterm H.
- exists (R_comp r1 (R_comp r2 r3)). split ; triv. intros H. depelim H. inv_subterm H.
- exists (R_cons (Q_rapply r2 i) (R_comp r1 r2)). split ; triv.
- destruct r ; triv. exists r. split ; triv. intros H1. inv_subterm H1.
- exists R_id. split ; triv.
Qed.

Lemma es_red_impl_reducible : 
  (forall {k} (t t' : expr k), t =e=> t' -> t = t' \/ ereducible t) /\ 
  (forall s s', s =s=> s' -> s = s' \/ sreducible s).
Proof.
apply ered_sred_ind ; intros ; triv.
all: try solve [ destruct H0 ; triv | destruct H0, H2 ; triv ].
all: try solve [ right ; apply ereducible_subst ; triv ]. 
all: try solve [ right ; apply sreducible_sren ; triv ]. 
- apply qr_red_impl_reducible in H. destruct H ; triv.
- apply qr_red_impl_reducible in H. destruct H ; triv. subst.
  destruct H1 ; triv.
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
- destruct e ; try solve [ eexists ; triv ]. Unshelve. all: triv.
  exists (E_ren (R_comp r0 r) e). split ; triv. intros H1. depelim H1. inv_subterm H0.
- exists e. split ; triv. intros H. inv_subterm H. 
- destruct r ; triv. exists (E_tvar q). split ; triv.
- destruct e ; try solve [ eexists ; triv ]. Unshelve. all: triv.
  + exists (E_subst (S_comp (S_ren r) s) e). split ; triv. intros H1. depelim H1.
    inv_subterm H0.
  + exists (E_subst (S_comp s0 s) e). split ; triv. intros H1. depelim H1. 
    inv_subterm H0. 
- exists e. split ; triv. intros H. inv_subterm H.
- destruct s ; triv. exists e. split ; triv. intros H1. inv_subterm H1.
- destruct s ; triv. exists (E_ren r e). split ; triv.
- exists s. split ; triv. intros H. inv_subterm H. 
- exists s. split ; triv. intros H. inv_subterm H. 
- exists (S_comp s1 (S_comp s2 s3)). split ; triv. intros H. 
  depelim H. inv_subterm H.
- exists (S_cons (E_subst s2 t) (S_comp s1 s2)). split ; triv.
- destruct s ; triv. exists s. split ; triv. intros H1. inv_subterm H1.
- exists S_id. triv.
- destruct r ; eexists ; triv.
Admitted.

Lemma qirreducible_qreducible i : qirreducible i <-> ~qreducible i.
Proof.
split.
- intros H H'. apply qr_reducible_impl_red in H'. destruct H' as (i' & H1 & H2). triv.
- intros H i' Hi. apply qr_red_impl_reducible in Hi. destruct Hi ; triv.
Qed.

Lemma rirreducible_rreducible r : rirreducible r <-> ~rreducible r.
Proof.
split.
- intros H H'. apply qr_reducible_impl_red in H'. destruct H' as (r' & H1 & H2). triv.
- intros H r' Hr. apply qr_red_impl_reducible in Hr. destruct Hr ; triv.
Qed.

Lemma eirreducible_ereducible {k} (t : expr k) : eirreducible t <-> ~ereducible t.
Proof.
split.
- intros H H'. apply es_reducible_impl_red in H'. destruct H' as (t' & H1 & H2). triv.
- intros H t' Ht. apply es_red_impl_reducible in Ht. destruct Ht ; triv.
Qed.

Lemma sirreducible_sreducible s : sirreducible s <-> ~sreducible s.
Proof.
split.
- intros H H'. apply es_reducible_impl_red in H'. destruct H' as (s' & H1 & H2). triv.
- intros H s' Hs. apply es_red_impl_reducible in Hs. destruct Hs ; triv.
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
Proof. change_irred. triv. Qed.
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
- split5 ; intros H' ; apply H ; triv.
  + destruct i ; triv.
  + destruct r ; triv. destruct H' as (_ & ->). triv.
- intros H' ; depelim H' ; triv.
  + destruct H as (_ & _ & _ & H & _). triv.
  + destruct r ; triv. destruct H as (_ & _ & _ & _ & H). triv.
Qed.

Lemma qirreducible_mvar m : qirreducible (Q_mvar m).
Proof. change_irred. intros H. depelim H. Qed.
#[local] Hint Resolve qirreducible_mvar : core.

Lemma rirreducible_id : rirreducible R_id.
Proof. change_irred. triv. Qed.
#[local] Hint Resolve rirreducible_id : core.

Lemma rirreducible_shift : rirreducible R_shift.
Proof. change_irred. triv. Qed.
#[local] Hint Resolve rirreducible_shift : core.

Lemma rirreducible_cons i r : 
  rirreducible (R_cons i r) <-> 
    qirreducible i /\ rirreducible r /\ ~(i = Q_zero /\ r = R_shift).
Proof.
change_irred. split.
- intros H. split3 ; intros H' ; apply H ; triv.
  destruct H' ; subst. now constructor. 
- intros (H1 & H2 & H3) H. depelim H ; triv.
Qed.

Lemma rirreducible_comp r1 r2 : 
  rirreducible (R_comp r1 r2) <->
    rirreducible r1 /\ rirreducible r2 /\ ~is_rcomp r1 /\ ~is_rcons r1 /\ 
    r1 <> R_id /\ r2 <> R_id /\ ~(r1 = R_shift /\ is_rcons r2).
Proof.
change_irred. split ; intros H.
- split7 ; intros H' ; apply H ; triv.
  + destruct r1 ; triv.
  + destruct r1 ; triv.
  + destruct H' as [-> H']. destruct r2 ; triv.
- intros H' ; depelim H' ; triv.
  + destruct H as (_ & _ & H & _) ; triv.
  + destruct H as (_ & _ & _ & H & _) ; triv.
  + destruct r2 ; triv. destruct H as (_ & _ & _ & _ & _ & _ & H). triv.
Qed. 

Lemma rirreducible_mvar m : rirreducible (R_mvar m).
Proof. change_irred. intros H. depelim H. Qed.
#[local] Hint Resolve rirreducible_mvar : core.

Lemma eirreducible_tvar i : 
  eirreducible (E_tvar i) <-> ~is_qrapply i /\ ~is_qsucc i.
Proof. 
change_irred. split ; intros H.
- split ; intros H' ; apply H ; destruct i ; triv.
- intros H'. destruct H. destruct i ; triv.
  + depelim H' ; triv.
  + depelim H' ; triv.
Qed.

Lemma eirreducible_tvar_zero : eirreducible (E_tvar Q_zero).
Proof. change_irred. intros H. depelim H ; triv. Qed.
#[local] Hint Resolve eirreducible_tvar_zero : core.

Lemma eirreducible_tctor c al : eirreducible (E_tctor c al) <-> eirreducible al.
Proof. change_irred. split ; intros H H' ; apply H ; triv. now depelim H'. Qed.

Lemma eirreducible_al_nil : eirreducible E_al_nil.
Proof. change_irred. intros H ; depelim H. Qed.
#[local] Hint Resolve eirreducible_al_nil : core.

Lemma eirreducible_al_cons {ty tys} (a : expr (Ka ty)) (al : expr (Kal tys)) :
  eirreducible (E_al_cons a al) <-> eirreducible a /\ eirreducible al.
Proof.
change_irred. split ; intros H.
- split ; intros H' ; apply H ; triv.
- intros H' ; depelim H' ; triv.
Qed.

Lemma eirreducible_abase b x : eirreducible (E_abase b x).
Proof. change_irred. triv. Qed.
#[local] Hint Resolve eirreducible_abase : core.

Lemma eirreducible_aterm t : eirreducible (E_aterm t) <-> eirreducible t.
Proof. change_irred. split ; intros H H' ; apply H ; triv. now depelim H'. Qed.

Lemma eirreducible_abind {ty} (a : expr (Ka ty)) : 
  eirreducible (E_abind a) <-> eirreducible a.
Proof. change_irred. split ; intros H H' ; apply H ; triv. now depelim H'. Qed.

Lemma eirreducible_ren {k} (e : expr k) r :
  eirreducible (E_ren r e) <-> 
    rirreducible r /\ eirreducible e /\ ~is_push e /\
    ~(is_rcons r /\ is_tvar_zero e) /\ r <> R_id.
Proof. 
change_irred. split ; intros H.
- split5 ; intros H' ; apply H ; triv.
  destruct e ; triv. destruct q ; triv. destruct r ; triv.
- intros H' ; depelim H' ; triv.
  destruct r ; triv. destruct H as (_ & _ & _ & H & _). triv.
Qed.

Lemma eirreducible_subst {k} (e : expr k) s :
  eirreducible (E_subst s e) <->
    eirreducible e /\ sirreducible s /\ ~is_push e /\
    ~(is_tvar_zero e /\ is_scons s) /\ s <> S_id /\ ~is_sren s.
Proof.
change_irred. split ; intros H.
- split6 ; intros H' ; apply H ; triv.
  destruct e ; triv. destruct q ; triv. destruct s ; triv.
- intros H' ; depelim H' ; triv.
  destruct s ; triv. destruct H as (_ & _ & _ & H & _). triv.
Qed.     

Lemma eirreducible_mvar m : eirreducible (E_mvar m).
Proof. change_irred. triv. Qed.
#[local] Hint Resolve eirreducible_mvar : core.

Lemma sirreducible_id : sirreducible S_id.
Proof. change_irred. triv. Qed.
#[local] Hint Resolve sirreducible_id : core.

Lemma sirreducible_shift : sirreducible S_shift.
Proof. change_irred. triv. Qed.
#[local] Hint Resolve sirreducible_shift : core.

Lemma sirreducible_cons t s : 
  sirreducible (S_cons t s) <-> 
    eirreducible t /\ sirreducible s /\ ~(t = E_tvar Q_zero /\ s = S_shift).
Proof.
change_irred. split ; intros H.
- split3 ; intros H' ; apply H ; triv.
  destruct H' ; subst. now constructor. 
- intros H'. depelim H' ; triv. destruct H as (_ & _ & H). triv.
Qed.   

Lemma sirreducible_comp s1 s2 : 
  sirreducible (S_comp s1 s2) <->
    sirreducible s1 /\ sirreducible s2 /\ ~is_scomp s1 /\ ~is_scons s1 /\ 
    s1 <> S_id /\ s2 <> S_id /\ ~(s1 = S_shift /\ is_scons s2).
Proof.
change_irred. split ; intros H.
- split7 ; intros H' ; apply H ; triv.
  + destruct s1 ; triv.
  + destruct s1 ; triv.
  + destruct H' as [-> H']. destruct s2 ; triv.
- intros H' ; depelim H' ; triv.
  + destruct H as (_ & _ & H & _) ; triv.
  + destruct H as (_ & _ & _ & H & _) ; triv.
  + destruct s2 ; triv. destruct H as (_ & _ & _ & _ & _ & _ & H). triv.
Qed. 

Lemma sirreducible_ren r : sirreducible (S_ren r) <-> is_rmvar r.
Proof.
change_irred. split ; intros H.
- destruct r ; triv. all: exfalso ; apply H ; now constructor.
- intros H' ; depelim H' ; triv. destruct r ; triv.
Qed.

Lemma sirreducible_mvar m : sirreducible (S_mvar m).
Proof. change_irred. intros H. depelim H. Qed.
#[local] Hint Resolve sirreducible_mvar : core.

(*********************************************************************************)
(** *** [rapply_aux] *)
(*********************************************************************************)

(** Helper function for [rapply] which takes care of trivial cases. *)
Equations rapply_aux (r : ren) (i : qnat) : qnat :=
rapply_aux R_id i := i ;
rapply_aux (R_cons k r) Q_zero := k ;
rapply_aux r i := Q_rapply r i.

Lemma rapply_aux_red r i : Q_rapply r i =q=> rapply_aux r i.
Proof. funelim (rapply_aux r i) ; triv. Qed.
#[local] Hint Rewrite <-rapply_aux_red : red.

Lemma rapply_aux_irreducible r i : 
  rirreducible r -> qirreducible i -> 
  (r <> R_id -> ~(is_rcons r /\ i = Q_zero) -> qirreducible (Q_rapply r i)) -> 
  qirreducible (rapply_aux r i).
Proof.
intros H1 H2 H3. funelim (rapply_aux r i) ; triv.
all: try solve [ apply H3 ; triv ].
rewrite rirreducible_cons in H1 ; triv.
Qed.   

(*********************************************************************************)
(** *** [rcomp_aux] *)
(*********************************************************************************)

(** Helper function for [rcomp] which takes care of trivial cases. *)
Equations rcomp_aux (r1 r2 : ren) : ren :=
rcomp_aux r R_id := r ;
rcomp_aux R_shift (R_cons _ r) := r ;
rcomp_aux r1 r2 := R_comp r1 r2.

Lemma rcomp_aux_red r1 r2 : R_comp r1 r2 =r=> rcomp_aux r1 r2.
Proof. funelim (rcomp_aux r1 r2) ; triv. Qed.
#[local] Hint Rewrite <-rcomp_aux_red : red.

Lemma rcomp_aux_irreducible r1 r2 : 
  rirreducible r1 -> rirreducible r2 -> 
  (r2 <> R_id -> ~(r1 = R_shift /\ is_rcons r2) -> rirreducible (R_comp r1 r2)) -> 
  rirreducible (rcomp_aux r1 r2).
Proof.
intros H1 H2 H3. funelim (rcomp_aux r1 r2) ; triv.
all: try solve [ apply H3 ; now triv ].
now rewrite rirreducible_cons in H2.
Qed.

(*********************************************************************************)
(** *** [rcons] *)
(*********************************************************************************)

Equations rcons : qnat -> ren -> ren :=
rcons Q_zero R_shift := R_id ;
rcons i r := R_cons i r.

Lemma rcons_red i r : R_cons i r =r=> rcons i r.
Proof. funelim (rcons i r) ; triv. Qed.
#[local] Hint Rewrite <-rcons_red : red.

Lemma rcons_irreducible i r :
  qirreducible i -> rirreducible r -> rirreducible (rcons i r).
Proof.
intros H1 H2. funelim (rcons i r) ; triv.
all: solve [ rewrite rirreducible_cons ; triv ].
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
all: intros ; simp red ; triv.
- rewrite <-H. triv.
- rewrite <-H, <-H0. triv. 
- rewrite <-H0, <-H. triv. 
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
all: intros ; triv.
- apply rapply_aux_irreducible ; triv. intros H1 H2. rewrite qirreducible_rapply ; triv.
- now apply qirreducible_succ in H0.
- rewrite qirreducible_rapply in H1. apply rapply_aux_irreducible ; triv. 
  + now apply H.
  + intros H2 H3. rewrite qirreducible_rapply. split5 ; triv. now apply H.
- apply rapply_aux_irreducible ; triv. intros H1 H2. rewrite qirreducible_rapply.
  split5 ; triv.
- apply rcomp_aux_irreducible ; triv. intros H1 H2. rewrite rirreducible_comp.
  split3 ; triv.
- rewrite rirreducible_cons in *. apply rcons_irreducible.
  + now apply H.
  + now apply H0.
- rewrite rirreducible_comp in H1. apply H0 ; triv. apply H ; triv.
- apply rcomp_aux_irreducible ; triv. intros H1 H2. rewrite rirreducible_comp. triv.
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
rsimp (R_cons i r) := rcons (qsimp i) (rsimp r) ;
rsimp (R_comp r1 r2) := rcomp (rsimp r1) (rsimp r2) ;
rsimp r := r.

Lemma qsimp_rsimp_red :
  (forall i, i =q=> qsimp i) * (forall r, r =r=> rsimp r).
Proof. 
apply qsimp_elim with 
  (P := fun i res => i =q=> res)
  (P0 := fun r res => r =r=> res).
all: intros ; simp red ; triv.
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
all: intros ; try solve [ change_irred ; triv ].
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
(** *** [scons] *)
(*********************************************************************************)

(** Simplify [S_cons t s].
    We use a traditional pattern match instead of a [with] clause because 
    we want to avoid using [NoConfusion] in the generated code. *)
Equations scons (t : expr Kt) (s : subst) : subst :=
scons t S_shift := match t with E_tvar Q_zero => S_id | _ => S_cons t S_shift end ;
scons t s := S_cons t s. 

Lemma scons_red t s : S_cons t s =s=> scons t s. 
Proof.
funelim (scons t s) ; triv. depelim t ; triv. depelim q ; triv.
Qed.
#[local] Hint Rewrite <-scons_red : red.

Lemma scons_irreducible t s :
  eirreducible t -> sirreducible s -> sirreducible (scons t s).
Proof.
intros H1 H2. 
funelim (scons t s) ; try solve [ rewrite sirreducible_cons ; triv ].
depelim t ; try solve [ rewrite sirreducible_cons ; triv ].
depelim q ; try solve [ rewrite sirreducible_cons ; triv ]. triv.
Qed. 

(*********************************************************************************)
(** *** [tnat] *)
(*********************************************************************************)

(** Simplify [E_tvar i]. We take care of extracting [Q_rapply] into [E_ren]. *)
Equations tnat : qnat -> expr Kt :=
tnat (Q_rapply r i) := E_ren r (E_tvar i) ; 
tnat i := E_tvar i.

Lemma tnat_red i : E_tvar i =e=> tnat i.
Proof. funelim (tnat i) ; triv. Qed.
#[local] Hint Rewrite <-tnat_red : red.

Lemma tnat_irreducible i : qirreducible i -> eirreducible (tnat i).
Proof.
intros H. funelim (tnat i) ; triv.
- now apply qirreducible_succ in H.
- rewrite qirreducible_rapply in H. rewrite eirreducible_ren. split5 ; triv.
  + rewrite eirreducible_tvar. split ; triv. destruct i ; triv. 
    destruct H as (_ & H & _). now apply qirreducible_succ in H.
  + intros (H1 & H2). destruct i ; triv. destruct r ; triv.
    destruct H as (_ & _ & _ & _ & H). triv.
- rewrite eirreducible_tvar. triv.
Qed.

(*********************************************************************************)
(** *** [sren] *)
(*********************************************************************************)

(** Simplify [S_ren r]. *)
Equations sren (r : ren) : subst :=
sren R_id := S_id ;
sren R_shift := S_shift ;
sren (R_cons i r) := S_cons (tnat i) (sren r) ;
sren (R_comp r1 r2) := S_comp (sren r1) (sren r2) ;
sren (R_mvar r) := S_ren (R_mvar r).

Lemma sren_red r : S_ren r =s=> sren r.
Proof. 
funelim (sren r) ; simp red ; triv.
- rewrite <-H. triv.
- rewrite <-H, <-H0. triv.
Qed.  
#[local] Hint Rewrite <-sren_red : red.

Lemma sren_irreducible r :
  rirreducible r -> sirreducible (sren r).
Proof.
intros H. funelim (sren r) ; triv.
- rewrite rirreducible_cons in H0. rewrite sirreducible_cons. split3.
  + now apply tnat_irreducible.
  + now apply H.
  + intros (H2 & H3). destruct H0 as (_ & _ & H0) ; apply H0. split.
    * destruct i ; triv.
    * destruct r ; triv.  
- rewrite rirreducible_comp in H1. feed H ; triv. feed H0 ; triv.
  rewrite sirreducible_comp. split7 ; triv.
  + destruct r1 ; triv.
  + destruct r1 ; triv.
  + destruct r1 ; triv.
  + destruct r2 ; triv.
  + destruct r1 ; triv. destruct r2 ; triv.
    destruct H1 as (_ & _ & _ & _ & _ & _ & H1). triv.     
- rewrite sirreducible_ren. triv.
Qed.

(*********************************************************************************)
(** *** [scomp_aux] *)
(*********************************************************************************)

(** Helper function for [rscomp], [srcomp], and [scomp]
    which takes care of trivial cases. *)
Equations scomp_aux : subst -> subst -> subst :=
scomp_aux s S_id := s ;
scomp_aux S_shift (S_cons t s) := s ;
scomp_aux s1 s2 := S_comp s1 s2.

Lemma scomp_aux_red s1 s2 : S_comp s1 s2 =s=> scomp_aux s1 s2. 
Proof. funelim (scomp_aux s1 s2) ; triv. Qed.
#[local] Hint Rewrite <-scomp_aux_red : red.

Lemma scomp_aux_irreducible s1 s2 :
  sirreducible s1 -> sirreducible s2 -> 
  (s2 <> S_id -> ~(s1 = S_shift /\ is_scons s2) -> sirreducible (S_comp s1 s2)) ->
  sirreducible (scomp_aux s1 s2).
Proof.
intros H1 H2 H3. funelim (scomp_aux s1 s2) ; triv.
all: try solve [ apply H3 ; triv ]. 
now rewrite sirreducible_cons in H2.
Qed.

(*********************************************************************************)
(** *** [sapply_aux] *)
(*********************************************************************************)

(** Helper function for [sapply] which takes care of trivial cases. *)
Equations sapply_aux : subst -> qnat -> expr Kt :=
sapply_aux S_id i := E_tvar i ;
sapply_aux (S_cons t _) Q_zero := t ;
sapply_aux (S_ren r) i with i := {
  | Q_rapply r' i' => E_ren (rcomp r' r) (E_tvar i')
  | i' => E_ren r (E_tvar i')
  } ;
sapply_aux s i := E_subst s (E_tvar i).

Lemma sapply_aux_red s i : E_subst s (E_tvar i) =e=> sapply_aux s i. 
Proof. 
funelim (sapply_aux s i) ; simp red ; triv.
rewrite ered_subst_sren, ered_rapply. triv.
Qed.
#[local] Hint Rewrite <-sapply_aux_red : red.

Lemma sapply_aux_irreducible s i :
  sirreducible s -> qirreducible i -> ~is_qrapply i ->
  (s <> S_id -> ~(is_scons s /\ i = Q_zero) -> ~is_sren s -> eirreducible (E_subst s (E_tvar i))) ->
  eirreducible (sapply_aux s i).
Proof.
intros H1 H2 H3 H4. funelim (sapply_aux s i).
all: try solve [ apply H4 ; triv ].
- rewrite eirreducible_tvar. destruct i ; triv. now apply qirreducible_succ in H2.  
- now rewrite sirreducible_cons in H1.
- rewrite sirreducible_ren in H1. destruct r ; triv. rewrite eirreducible_ren. triv.
- now apply qirreducible_succ in H2.
- exfalso. triv.
- rewrite sirreducible_ren in H1. destruct r ; triv. rewrite eirreducible_ren. 
  split5 ; triv. rewrite eirreducible_tvar. triv.
Qed.

(*********************************************************************************)
(** *** [sapply] and [rscomp] *)
(*********************************************************************************)

(** Simplify [E_subst s (E_tvar i)]. *)
Equations sapply (s : subst) (i : qnat) : expr Kt by struct i :=
sapply s (Q_rapply r i) := sapply_aux (rscomp r s) i ;
sapply s i := sapply_aux s i

(** Simplify [S_comp (S_ren r) s]. *)
with rscomp (r : ren) (s : subst) : subst by struct r :=
rscomp R_id s := s ;
rscomp R_shift s := scomp_aux S_shift s ;
rscomp (R_cons i r) s := scons (sapply s i) (rscomp r s) ;
rscomp (R_comp r1 r2) s := rscomp r1 (rscomp r2 s) ;
rscomp (R_mvar m) s := scomp_aux (S_ren (R_mvar m)) s.

Lemma sapply_rscomp_red :
  (forall s i, E_subst s (E_tvar i) =e=> sapply s i) *
  (forall r s, S_comp (S_ren r) s =s=> rscomp r s).
Proof.
apply sapply_elim with 
  (P := fun s i res => E_subst s (E_tvar i) =e=> res)
  (P0 := fun r s res => S_comp (S_ren r) s =s=> res).
all: intros ; simp red ; triv.
- rewrite <-H. rewrite ered_rapply. triv.
- rewrite sred_sren_id. triv.
- rewrite sred_sren_shift. triv.
- rewrite <-H, <-H0. rewrite sred_sren_cons. triv.
- rewrite <-H0, <-H. rewrite sred_sren_comp. triv.  
Qed. 

Lemma sapply_red s i : E_subst s (E_tvar i) =e=> sapply s i.
Proof. now apply sapply_rscomp_red. Qed.
#[local] Hint Rewrite <-sapply_red : red.

Lemma rscomp_red r s : S_comp (S_ren r) s =s=> rscomp r s.
Proof. now apply sapply_rscomp_red. Qed.
#[local] Hint Rewrite <-rscomp_red : red.

Lemma sapply_rscomp_irreducible :
  (forall s i, sirreducible s -> qirreducible i -> eirreducible (sapply s i)) *
  (forall r s, rirreducible r -> sirreducible s -> sirreducible (rscomp r s)).
Proof.
apply sapply_elim with 
  (P := fun s i res => sirreducible s -> qirreducible i -> eirreducible res)
  (P0 := fun r s res => rirreducible r -> sirreducible s -> sirreducible res).
all: intros ; triv.
- apply sapply_aux_irreducible ; triv. intros H1 H2. rewrite eirreducible_subst.
  split5 ; triv. intros [? ?] ; triv.
- now apply qirreducible_succ in H0.
- rewrite qirreducible_rapply in H1. apply sapply_aux_irreducible ; triv. 
  + now apply H.
  + intros H2 H3. rewrite eirreducible_subst. split5 ; triv.
    * rewrite eirreducible_tvar. destruct i ; triv. destruct H1 as (_ & H1 & _).
      now apply qirreducible_succ in H1.
    * now apply H.
    * intros [? ?] ; destruct i ; triv.
- apply sapply_aux_irreducible ; triv.   intros H1 H2. rewrite eirreducible_subst.
  split5 ; triv. rewrite eirreducible_tvar ; triv. 
- apply scomp_aux_irreducible ; triv. intros H1. rewrite sirreducible_comp. triv. 
- rewrite rirreducible_cons in H1. apply scons_irreducible. 
  + apply H ; triv.
  + apply H0 ; triv.
- rewrite rirreducible_comp in H1. apply H0 ; triv. apply H ; triv.
- apply scomp_aux_irreducible ; triv.
  + rewrite sirreducible_ren ; triv.
  + intros H1 H2. rewrite sirreducible_comp. split7 ; triv.
    rewrite sirreducible_ren. triv.
Qed.

(*********************************************************************************)
(** *** [rename_aux] *)
(*********************************************************************************)

Equations rename_aux {k} (r : ren) (e : expr k) : expr k :=
rename_aux R_id t := t ;
rename_aux (R_cons i _) (E_tvar Q_zero) := tnat i ;
rename_aux r t := E_ren r t.

Lemma rename_aux_red {k} r (t : expr k) : 
  E_ren r t =e=> rename_aux r t.
Proof. funelim (rename_aux r t) ; simp red ; triv. Qed.
#[local] Hint Rewrite <-@rename_aux_red : red.

Lemma rename_aux_irreducible {k} r (t : expr k) :
  rirreducible r -> eirreducible t -> 
  (r <> R_id -> ~(is_rcons r /\ is_tvar_zero t) -> eirreducible (E_ren r t)) ->
  eirreducible (rename_aux r t).
Proof.
intros H1 H2 H3. funelim (rename_aux r t) ; triv.
all: try solve [ apply H3 ; triv ].
rewrite rirreducible_cons in H1. now apply tnat_irreducible.
Qed.

(*********************************************************************************)
(** *** [substitute_aux] *)
(*********************************************************************************)

(** Helper function for [rename] and [substitute] which takes care of trivial cases. *)
Equations substitute_aux {k} (s : subst) (t : expr k) : expr k :=
substitute_aux S_id t := t ;
substitute_aux (S_cons t _) (E_tvar Q_zero) := t ;
substitute_aux (S_ren r) t := E_ren r t ;
substitute_aux s t := E_subst s t.

Lemma substitute_aux_red {k} s (t : expr k) :
  E_subst s t =e=> substitute_aux s t.
Proof. funelim (substitute_aux s t) ; triv. Qed.
#[local] Hint Rewrite <-@substitute_aux_red : red.

Lemma substitute_aux_irreducible {k} s (t : expr k) :
  eirreducible t -> sirreducible s -> 
  match s with S_ren r => eirreducible (E_ren r t) | _ => True end ->
  (s <> S_id -> ~(is_tvar_zero t /\ is_scons s) -> ~is_sren s -> eirreducible (E_subst s t)) ->
  eirreducible (substitute_aux s t).
Proof.
intros H1 H2 H3 H4. funelim (substitute_aux s t) ; triv.
all: try solve [ apply H4 ; triv ].
now rewrite sirreducible_cons in H2.
Qed.

(*********************************************************************************)
(** *** [rename] and [srcomp] *)
(*********************************************************************************)

Definition rup (r : ren) : ren := rcons Q_zero (rcomp r R_shift).

(** Simplify [E_ren r t]. *)
Equations rename {k} (r : ren) (t : expr k) : expr k by struct t :=
rename r (E_tctor c al) := E_tctor c (rename r al) ;
rename r E_al_nil := E_al_nil ;
rename r (E_al_cons a al) := E_al_cons (rename r a) (rename r al) ;
rename _ (E_abase b x) := E_abase b x ;
rename r (E_aterm t) := E_aterm (rename r t) ;
rename r (E_abind a) := E_abind (rename (rup r) a) ;
rename r2 (E_ren r1 t) := rename_aux (rcomp r1 r2) t ;
rename r (E_subst s t) := substitute_aux (srcomp s r) t ;
rename r e := rename_aux r e 

(** Simplify [S_comp s (S_ren r)]. *)
with srcomp (s : subst) (r : ren) : subst by struct s :=
srcomp S_id r := sren r ;
srcomp (S_cons t s) r := scons (rename r t) (srcomp s r) ;
srcomp (S_comp s1 s2) r := scomp_aux s1 (srcomp s2 r) ;
srcomp s r := scomp_aux s (sren r). 

Lemma rename_srcomp_red : 
  (forall {k} r (t : expr k), E_ren r t =e=> rename r t) *
  (forall s r, S_comp s (S_ren r) =s=> srcomp s r).
Proof.
apply rename_elim with 
  (P := fun {k} r (t : expr k) res => E_ren r t =e=> res)
  (P0 := fun s r res => S_comp s (S_ren r) =s=> res).
all: intros.
all: try solve [ triv | simp red ; triv | simp red ; now rewrite <-H ].
- now rewrite <-H, <-H0.
- rewrite <-H. unfold rup. simp red. triv.
- simp red. rewrite <-H, <-H0. rewrite sred_cons_l. now rewrite ered_subst_sren.
Qed.

Lemma rename_red {k} r (t : expr k) :
  E_ren r t =e=> rename r t. 
Proof. now apply rename_srcomp_red. Qed.
#[local] Hint Rewrite <-@rename_red : red.

Lemma srcomp_red s r :
  S_comp s (S_ren r) =s=> srcomp s r.
Proof. now apply rename_srcomp_red. Qed.
#[local] Hint Rewrite <-srcomp_red : red.

Lemma rename_srcomp_irreducible :
  (forall {k} r (t : expr k), rirreducible r -> eirreducible t -> eirreducible (rename r t)) *
  (forall s r, sirreducible s -> rirreducible r -> sirreducible (srcomp s r)).
Proof.
apply rename_elim with 
  (P := fun {k} r (t : expr k) res => rirreducible r -> eirreducible t -> eirreducible res)
  (P0 := fun s r res => sirreducible s -> rirreducible r -> sirreducible res).
all: intros ; triv.
- rewrite eirreducible_tvar in H0. apply rename_aux_irreducible ; triv.
  + now rewrite eirreducible_tvar.
  + intros H1 H2. rewrite eirreducible_ren. split5 ; triv.
    rewrite eirreducible_tvar. triv.
- rewrite eirreducible_tctor in *. now apply H.
- apply rename_aux_irreducible ; triv.
  intros H1 H2. rewrite eirreducible_ren. split5 ; triv.
- rewrite eirreducible_al_cons in *. split ; [apply H | apply H0] ; triv.
- rewrite eirreducible_aterm in *. now apply H.
- rewrite eirreducible_abind in *. apply H ; triv. unfold rup. 
  apply rcons_irreducible ; triv. apply rapply_rcomp_irreducible ; triv.
- rewrite eirreducible_ren in H0. apply rename_aux_irreducible ; triv.
  + now apply rapply_rcomp_irreducible.
  + intros H1 H2. rewrite eirreducible_ren. split5 ; triv.
    now apply rapply_rcomp_irreducible.  
- rewrite eirreducible_subst in H1. feed2 H ; triv.
  apply substitute_aux_irreducible ; triv.
  + destruct (srcomp s r) ; triv. rewrite sirreducible_ren in H. destruct r0 ; triv.
    rewrite eirreducible_ren. triv.
  + intros H4 H5 H6. rewrite eirreducible_subst. triv.
- now apply sren_irreducible.
- apply scomp_aux_irreducible ; triv. 
  + now apply sren_irreducible.
  + intros H1 H2. rewrite sirreducible_comp. split7 ; triv.
    now apply sren_irreducible.
- rewrite sirreducible_cons in H1. apply scons_irreducible.
  + now apply H.
  + now apply H0.
- rewrite sirreducible_comp in H0. apply scomp_aux_irreducible ; triv.
  + now apply H.
  + intros H2 H3. rewrite sirreducible_comp. split7 ; triv.
    now apply H.
- rewrite sirreducible_ren in H. destruct r0 ; triv. apply scomp_aux_irreducible.
  + now rewrite sirreducible_ren.
  + now apply sren_irreducible.
  + intros H1 H2. rewrite sirreducible_comp. split7 ; triv. 
    * now rewrite sirreducible_ren.
    * now apply sren_irreducible.
- apply scomp_aux_irreducible ; triv.
  + now apply sren_irreducible.
  + intros H1 H2. rewrite sirreducible_comp. split7 ; triv.
    now apply sren_irreducible.
Qed. 

(*********************************************************************************)
(** *** [substitute] and [scomp] *)
(*********************************************************************************)

(** Lift a substitution through a binder. *)
Definition sup (s : subst) : subst := scons (E_tvar Q_zero) (srcomp s R_shift).

(** Apply an irreducible substitution to an irreducible expression. *)
Equations substitute {k} (s : subst) (t : expr k) : expr k by struct t :=
substitute s (E_tvar i) := sapply s i ;
substitute s (E_tctor c al) := E_tctor c (substitute s al) ;
substitute _ E_al_nil := E_al_nil ;
substitute s (E_al_cons a al) := E_al_cons (substitute s a) (substitute s al) ;
substitute _ (E_abase b x) := E_abase b x ;
substitute s (E_aterm t) := E_aterm (substitute s t) ;
substitute s (E_abind a) := E_abind (substitute (sup s) a) ;
substitute s (E_ren r e) := substitute_aux (rscomp r s) e ;
substitute s2 (E_subst s1 e) := substitute_aux (scomp s1 s2) e ;
substitute s e := substitute_aux s e 

(** Compose two irreducible substitutions. *)
with scomp (s1 s2 : subst) : subst by struct s1 :=
scomp S_id s := s ;
scomp (S_cons t s1) s2 := scons (substitute s2 t) (scomp s1 s2) ;
scomp (S_comp s1 s2) s3 := scomp_aux s1 (scomp s2 s3) ;
scomp s1 s2 := scomp_aux s1 s2. 

Lemma substitute_scomp_red : 
  (forall {k} s (t : expr k), E_subst s t =e=> substitute s t) *
  (forall s1 s2, S_comp s1 s2 =s=> scomp s1 s2).
Proof.
apply substitute_elim with
  (P := fun {k} s (t : expr k) res => E_subst s t =e=> res)
  (P0 := fun s1 s2 res => S_comp s1 s2 =s=> res).
all: intros ; simp red ; triv.
- now rewrite <-H.
- now rewrite <-H, <-H0.
- now rewrite <-H.
- rewrite <-H. unfold sup. rewrite ered_subst_abind. now simp red.
- now rewrite <-H.
- now rewrite <-H, <-H0.
- now rewrite <-H.
Qed.

Lemma substitute_red {k} s (t : expr k) :
  E_subst s t =e=> substitute s t.
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
  (P := fun {k} s (t : expr k) res => sirreducible s -> eirreducible t -> eirreducible res)
  (P0 := fun s1 s2 res => sirreducible s1 -> sirreducible s2 -> sirreducible res).
all: intros ; triv.
- apply sapply_rscomp_irreducible ; triv. rewrite eirreducible_tvar in H0.  
  destruct H0. destruct i ; triv. all: exfalso ; triv.
- rewrite eirreducible_tctor in *. now apply H.
- apply substitute_aux_irreducible ; triv.
  + destruct s ; triv. rewrite eirreducible_ren. rewrite sirreducible_ren in H.
    destruct r ; triv.
  + intros H1 H2 H3. rewrite eirreducible_subst. triv. 
- rewrite eirreducible_al_cons in *. feed2 H ; triv. feed2 H0 ; triv.
- rewrite eirreducible_aterm in *. now apply H.
- rewrite eirreducible_abind in *. apply H ; triv. unfold sup.
  apply scons_irreducible ; triv. apply rename_srcomp_irreducible ; triv.
- rewrite eirreducible_ren in H0.
  assert (H1 : sirreducible (rscomp r s)). { apply sapply_rscomp_irreducible ; triv. }
  apply substitute_aux_irreducible ; triv.
  + destruct (rscomp r s) ; triv. rewrite eirreducible_ren in *. rewrite sirreducible_ren in H1.
    destruct r0 ; triv.
  + intros H2 H3 H4. rewrite eirreducible_subst. split6 ; triv.  
- rewrite eirreducible_subst in H1. feed2 H ; triv. apply substitute_aux_irreducible ; triv.
  + destruct (scomp s1 s2) ; triv. rewrite sirreducible_ren in H. rewrite eirreducible_ren.
    destruct r ; triv.
  + intros H4 H5 H6. rewrite eirreducible_subst. triv.
- apply scomp_aux_irreducible ; triv. intros H1 H2. rewrite sirreducible_comp. triv.
- rewrite sirreducible_cons in *. feed2 H ; triv. feed2 H0 ; triv. 
  apply scons_irreducible ; triv.
- rewrite sirreducible_comp in H0. feed2 H ; triv. apply scomp_aux_irreducible ; triv.
  intros H4 H5. rewrite sirreducible_comp. triv.
- rewrite sirreducible_ren in H. destruct r ; triv. apply scomp_aux_irreducible ; triv.
  + rewrite sirreducible_ren. triv.
  + intros H1 H2. rewrite sirreducible_comp. split7 ; triv.
    rewrite sirreducible_ren ; triv.
- apply scomp_aux_irreducible ; triv. intros H1 H2. rewrite sirreducible_comp. triv.
Qed.

(*********************************************************************************)
(** *** [esimp] and [ssimp] *)
(*********************************************************************************)

(** Simplify an expression. *)
Equations esimp {k} (t : expr k) : expr k :=
esimp (E_tvar i) := tnat (qsimp i) ;
esimp (E_tctor c al) := E_tctor c (esimp al) ;
esimp E_al_nil := E_al_nil ;
esimp (E_al_cons a al) := E_al_cons (esimp a) (esimp al) ;
esimp (E_abase b x) := E_abase b x ;
esimp (E_aterm t) := E_aterm (esimp t) ;
esimp (E_abind a) := E_abind (esimp a) ;
esimp (E_ren r t) := rename (rsimp r) (esimp t) ;
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
all: intros ; simp red ; triv.
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
all: intros ; triv.
- apply tnat_irreducible. apply qsimp_irreducible. 
- now rewrite eirreducible_tctor.
- now rewrite eirreducible_al_cons.
- now rewrite eirreducible_aterm.
- now rewrite eirreducible_abind.
- apply rename_srcomp_irreducible ; triv. now apply rsimp_irreducible.
- apply substitute_scomp_irreducible ; triv.
- now apply scons_irreducible.
- apply substitute_scomp_irreducible ; triv.
- apply sren_irreducible. now apply rsimp_irreducible.
Qed.

Lemma esimp_irreducible {k} (t : expr k) : eirreducible (esimp t).
Proof. now apply esimp_ssimp_irreducible. Qed.

Lemma ssimp_irreducible s : sirreducible (ssimp s).
Proof. now apply esimp_ssimp_irreducible. Qed.

End WithSignature.
