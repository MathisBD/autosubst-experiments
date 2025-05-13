From Prototype Require Import Prelude Sig LevelOne LevelTwo.

(** This file defines _irreducible_ forms for level two 
    expressions/substitutions, i.e. expressions in which we can't
    simplify anymore.
    
    We first define _reducible_ forms (in which we can reduce),
    and define irreducible as the negation of reducible.
    
    We then prove numerous lemmas that characterize irreducible forms. *)

Module Make (S : Sig).
Include LevelTwo.Make (S).

(** Add some power to [auto] and variants. *)
#[local] Hint Extern 6 => exfalso : core.
#[local] Hint Extern 6 => subst : core.

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
(** *** Irreducible forms for renamings & naturals. *)
(*********************************************************************************)

(** Reducible quoted naturals. *)
Inductive qred : qnat -> Prop :=

(** Congruence. *)
| QR_congr_succ i : qred i -> qred (Q_succ i)
| QR_congr_rapply r i : rred r \/ qred i -> qred (Q_rapply r i)
(** Reduce [i[r1][r2]] into [i[r1 >> r2]]. *)
| QR_ren_ren r1 r2 i : qred (Q_rapply r1 (Q_rapply r2 i))
(** Reduce [i[rid]] into [i]. *)
| QR_ren_id i : qred (Q_rapply R_id i)
(** Reduce [0[i . r]] into [i]. *)
| QR_rcons_zero r : is_rcons r -> qred (Q_rapply r Q_zero)
(** Reduce [S i] into [i[R_shift]]. *)
| QR_succ_shift i : qred (Q_succ i)

(** Reducible renamings. *)
with rred : ren -> Prop :=

(** Congruence. *)
| RR_congr_cons i r : qred i \/ rred r -> rred (R_cons i r)
| RR_congr_comp r1 r2 : rred r1 \/ rred r2 -> rred (R_comp r1 r2)
(** Reduce [rid >> r] into [r]. *)
| RR_rid_l r : rred (R_comp R_id r)
(** Reduce [r >> rid] into [r]. *)
| RR_rid_r r : rred (R_comp r R_id)
(** Reduce [(r1 >> r2) >> r3] into [r1 >> (r2 >> r3)]. *)
| RR_comp_l r1 r2 r3 : rred (R_comp (R_comp r1 r2) r3)
(** Reduce [(i . r1) >> r2] into [i[r2] . (r1 >> r2)]. *)
| RR_cons_l i r1 r2 : rred (R_comp (R_cons i r1) r2)
(** Reduce [shift >> (i . r)] into [r]. *)
| RR_shift_cons r : is_rcons r -> rred (R_comp R_shift r)
(** Reduce [0 . shift] into [rid]. *)
| RR_zero_shift : rred (R_cons Q_zero R_shift)
(** Reduce [0[r] . (shift >> r)] into [r]. *)
(*| RR_shift_cons_l r : rred (R_cons (Q_rapply r Q_zero) (R_comp R_shift r))*).

Derive Signature for qred rred.

Hint Constructors qred : core.
Hint Constructors rred : core.

(** Irreducible quoted natural/renaming. *)
Definition qirred x := ~ qred x.
Definition rirred r := ~ rred r.
  
(*********************************************************************************)
(** *** Characterization of irreducible forms for renamings & naturals. *)
(*********************************************************************************)

Lemma qirred_zero : qirred Q_zero.
Proof. intros H. depelim H. Qed.

Lemma qirred_succ i : ~qirred (Q_succ i).
Proof. intros H. apply H. now constructor. Qed.
    
Lemma qirred_rapply r i : 
  qirred (Q_rapply r i) <-> 
    rirred r /\ qirred i /\ r <> R_id /\ ~is_qrapply i /\
    ~(is_rcons r /\ i = Q_zero).
Proof. 
split ; intros H. 
- split5 ; intros H' ; apply H ; triv.
  + destruct i ; triv.
  + destruct r ; triv. destruct H' as (_ & ->). triv.
- intros H' ; depelim H' ; triv.
  + destruct H0 ; triv.
  + destruct H as (_ & _ & _ & H & _). triv.
  + destruct r ; triv. destruct H as (_ & _ & _ & _ & H). triv.
Qed.

Lemma qirred_mvar m : qirred (Q_mvar m).
Proof. intros H. depelim H. Qed.

Lemma rirred_cons i r : 
  rirred (R_cons i r) <-> 
    qirred i /\ rirred r /\ ~(i = Q_zero /\ r = R_shift).
Proof.
split.
- intros H. split3 ; intros H' ; apply H ; triv.
  destruct H' ; subst. now constructor. 
- intros (H1 & H2 & H3) H. depelim H. destruct H ; triv. apply H3 ; triv.
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

(** Expressions in which we can push substitutions. *)
Definition is_push {k} (e : expr k) : Prop :=
  match e with E_mvar _ | E_tvar _ => False | _ => True end.

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

(** Reduce [E_tvar i[r]] into [substitute (S_ren r) (E_tvar i)]. *)
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
