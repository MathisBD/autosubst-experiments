From Prototype Require Import Prelude Sig LevelOne LevelTwo LevelTwoIrred.

(** This file implements simplification functions on level two 
    expressions/substitutions. 
    
    For each simplification function we prove a soundness lemma
    and an irreducibility lemma. *)

Module Make (S : Sig).
Module T := LevelTwoIrred.Make (S).
Export T.

(*********************************************************************************)
(** *** [rapply_aux] *)
(*********************************************************************************)

(** Helper function for [rapply] which takes care of trivial cases. *)
Equations rapply_aux (r : ren) (i : qnat) : qnat :=
rapply_aux R_id i := i ;
rapply_aux (R_cons k r) Q_zero := k ;
rapply_aux r i := Q_rapply r i.

Lemma rapply_aux_sound e r i : 
  qeval e (rapply_aux r i) = reval e r (qeval e i).
Proof. funelim (rapply_aux r i) ; simp qeval ; triv. Qed.
#[global] Hint Rewrite rapply_aux_sound : qeval.

Lemma rapply_aux_irred r i : 
  rirred r -> qirred i -> 
  (r <> R_id -> ~(is_rcons r /\ i = Q_zero) -> qirred (Q_rapply r i)) -> 
  qirred (rapply_aux r i).
Proof.
intros H1 H2 H3. funelim (rapply_aux r i) ; triv.
all: try solve [ apply H3 ; triv ].
rewrite rirred_cons in H1 ; triv.
Qed.   

(*********************************************************************************)
(** *** [rcomp_aux] *)
(*********************************************************************************)

(** Helper function for [rcomp] which takes care of trivial cases. *)
Equations rcomp_aux (r1 r2 : ren) : ren :=
rcomp_aux r R_id := r ;
rcomp_aux R_shift (R_cons _ r) := r ;
rcomp_aux r1 r2 := R_comp r1 r2.

Lemma rcomp_aux_sound e r1 r2 :
  reval e (rcomp_aux r1 r2) =₁ rcomp (reval e r1) (reval e r2).
Proof. funelim (rcomp_aux r1 r2) ; simp qeval ; triv. Qed.
#[global] Hint Rewrite rcomp_aux_sound : qeval reval.

Lemma rcomp_aux_irred r1 r2 : 
  rirred r1 -> rirred r2 -> 
  (r2 <> R_id -> ~(r1 = R_shift /\ is_rcons r2) -> rirred (R_comp r1 r2)) -> 
  rirred (rcomp_aux r1 r2).
Proof.
intros H1 H2 H3. funelim (rcomp_aux r1 r2) ; triv.
all: try solve [ apply H3 ; now triv ].
now rewrite rirred_cons in H2.
Qed.

(*********************************************************************************)
(** *** [rapply] and [rcomp] *)
(*********************************************************************************)

(** Apply an irreducible renaming to an irreducible quoted natural. *)
Equations rapply (r : ren) (i : qnat) : qnat by struct i := 
rapply r (Q_rapply r' i) := rapply_aux (rcomp r' r) i ;
rapply r i := rapply_aux r i

(** Compose two irreducible renamings. *)
with rcomp (r1 r2 : ren) : ren by struct r1 :=
rcomp R_id r := r ;
rcomp (R_cons i r1) r2 := R_cons (rapply r2 i) (rcomp r1 r2) ;
rcomp (R_comp r1 r2) r3 := rcomp r1 (rcomp r2 r3) ;
rcomp r1 r2 := rcomp_aux r1 r2.

Lemma rapply_rcomp_sound e :
  (forall r i, qeval e (rapply r i) = reval e r (qeval e i)) * 
  (forall r1 r2, reval e (rcomp r1 r2) =₁ P.rcomp (reval e r1) (reval e r2)).
Proof.
apply rapply_elim with 
  (P := fun r i res => qeval e res = reval e r (qeval e i))
  (P0 := fun r1 r2 res => reval e res =₁ P.rcomp (reval e r1) (reval e r2)).
all: intros ; simp qeval reval ; triv.
- rewrite H, H0. now rewrite O.rcomp_rcons_distrib.
- rewrite H0, H. now rewrite O.rcomp_assoc.
Qed.

Lemma rapply_sound e r i : 
  qeval e (rapply r i) = reval e r (qeval e i).
Proof. now apply rapply_rcomp_sound. Qed.
#[global] Hint Rewrite rapply_sound : qeval reval.

Lemma rcomp_sound e r1 r2 :
  reval e (rcomp r1 r2) =₁ P.rcomp (reval e r1) (reval e r2).
Proof. now apply rapply_rcomp_sound. Qed.
#[global] Hint Rewrite rcomp_sound : qeval reval.

Lemma rapply_rcomp_irred :
  (forall r i, rirred r -> qirred i -> qirred (rapply r i)) *
  (forall r1 r2, rirred r1 -> rirred r2 -> rirred (rcomp r1 r2)).
Proof.
apply rapply_elim with 
  (P := fun r i res => rirred r -> qirred i -> qirred res)
  (P0 := fun r1 r2 res => rirred r1 -> rirred r2 -> rirred res).
all: intros ; triv.
- apply rapply_aux_irred ; triv. intros H1 H2. rewrite qirred_rapply.
  split5 ; triv.
- rewrite qirred_rapply in H1. apply rapply_aux_irred ; triv. 
  + now apply H.
  + intros H2 H3. rewrite qirred_rapply. split5 ; triv. now apply H.
- apply rapply_aux_irred ; triv. intros H1 H2. rewrite qirred_rapply.
  split5 ; triv.
- apply rcomp_aux_irred ; triv. intros H1 H2. rewrite rirred_shift_l.
  split4 ; triv. destruct r2 ; triv. destruct r2_1 ; triv.
- rewrite rirred_cons in *. split.
  + now apply H.
  + now apply H0.
- assert (H3 : rirred r1 /\ rirred r2).
  { split ; intros H' ; apply H1 ; triv. }
  apply H0 ; triv. apply H ; triv.
- apply rcomp_aux_irred ; triv. intros H1 H2. rewrite rirred_mvar_l.
  split ; triv.
Qed. 

(*********************************************************************************)
(** *** [qsimp] and [rsimp] *)
(*********************************************************************************)

(** Simplify a quoted natural. *)
Equations qsimp : qnat -> qnat :=
qsimp Q_zero := Q_zero ;
qsimp (Q_rapply r i) := rapply (rsimp r) (qsimp i) ;
qsimp (Q_mvar m) := Q_mvar m 

(** Simplify a renaming. *)
with rsimp : ren -> ren :=
rsimp (R_cons i r) := R_cons (qsimp i) (rsimp r) ;
rsimp (R_comp r1 r2) := rcomp (rsimp r1) (rsimp r2) ;
rsimp r := r.

Lemma qsimp_rsimp_sound e :
  (forall i, qeval e (qsimp i) = qeval e i) *
  (forall r, reval e (rsimp r) =₁ reval e r).
Proof. 
apply qsimp_elim with 
  (P := fun i res => qeval e res = qeval e i)
  (P0 := fun r res => reval e res =₁ reval e r).
all: intros ; simp qeval reval ; triv.
- now rewrite H, H0.
- now rewrite H, H0.
- now rewrite H, H0. 
Qed.    

Lemma qsimp_sound e i : qeval e (qsimp i) = qeval e i.
Proof. now apply qsimp_rsimp_sound. Qed.
#[global] Hint Rewrite qsimp_sound : qeval.

Lemma rsimp_sound e r : reval e (rsimp r) =₁ reval e r.
Proof. now apply qsimp_rsimp_sound. Qed.
#[global] Hint Rewrite rsimp_sound : qeval reval.

Lemma qsimp_rsimp_irred : 
  (forall i, qirred (qsimp i)) * (forall r, rirred (rsimp r)).
Proof.
apply qsimp_elim with (P := fun _ res => qirred res) (P0 := fun _ res => rirred res).
all: intros ; triv.
- now apply rapply_rcomp_irred.
- now rewrite rirred_cons.
- now apply rapply_rcomp_irred.
Qed.

Lemma qsimp_irred i : qirred (qsimp i).
Proof. now apply qsimp_rsimp_irred. Qed.

Lemma rsimp_irred r : rirred (rsimp r).
Proof. now apply qsimp_rsimp_irred. Qed.

(*********************************************************************************)
(** *** [sapply_aux] *)
(*********************************************************************************)

(** Helper function for [sapply] which takes care of trivial cases. *)
Equations sapply_aux : subst -> qnat -> term :=
sapply_aux S_id i := E_tvar i ;
sapply_aux (S_cons t _) Q_zero := t ;
sapply_aux (S_ren r) i := E_tvar (rapply r i) ;
sapply_aux s i := E_subst (E_tvar i) s.

Lemma sapply_aux_sound e s i : 
  eeval e (sapply_aux s i) = seval e s (qeval e i).
Proof. funelim (sapply_aux s i) ; simp qeval eeval ; triv. Qed.
#[global] Hint Rewrite sapply_aux_sound : eeval seval.

Lemma sapply_aux_irred s i :
  sirred s -> qirred i ->
  (s <> S_id -> ~is_sren s -> ~(is_scons s /\ i = Q_zero) -> eirred (E_subst (E_tvar i) s)) ->
  eirred (sapply_aux s i).
Proof.
intros H1 H2 H3. funelim (sapply_aux s i).
all: try solve [ apply H3 ; triv ].
- now rewrite eirred_tvar.
- now apply sirred_cons in H1.
- rewrite eirred_tvar. apply rapply_rcomp_irred ; triv. 
  rewrite sirred_ren in H1. destruct r ; triv.
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

Lemma scomp_aux_sound e s1 s2 : 
  seval e (scomp_aux s1 s2) =₁ O.scomp (seval e s1) (seval e s2).
Proof.
funelim (scomp_aux s1 s2) ; simp seval eeval ; triv.
now rewrite O.scomp_sid_r.
Qed.
#[global] Hint Rewrite scomp_aux_sound : seval eeval.

Lemma scomp_aux_irred s1 s2 :
  sirred s1 -> sirred s2 -> 
  (s2 <> S_id -> ~(s1 = S_shift /\ is_scons s2) -> sirred (S_comp s1 s2)) ->
  sirred (scomp_aux s1 s2).
Proof.
intros H1 H2 H3. funelim (scomp_aux s1 s2) ; triv.
all: try solve [ apply H3 ; triv ]. 
now rewrite sirred_cons in H2.
Qed.

(*********************************************************************************)
(** *** [sapply] and [rscomp] *)
(*********************************************************************************)

(** Apply an irreducible substitution to an irreducible natural. *)
Equations sapply (s : subst) (i : qnat) : term by struct i :=
sapply s (Q_rapply r i) := sapply_aux (rscomp r s) i ;
sapply s i := sapply_aux s i

(** Compose an irreducible renaming with an irreducible substitution. *)
with rscomp (r : ren) (s : subst) : subst by struct r :=
rscomp R_id s := s ;
rscomp R_shift s := scomp_aux S_shift s ;
rscomp (R_cons i r) s := S_cons (sapply s i) (rscomp r s) ;
rscomp (R_comp r1 r2) s := rscomp r1 (rscomp r2 s) ;
rscomp (R_mvar m) s := scomp_aux (S_ren (R_mvar m)) s.

Lemma sapply_rscomp_sound e :
  (forall s i, eeval e (sapply s i) = seval e s (qeval e i)) *
  (forall r s, seval e (rscomp r s) =₁ O.rscomp (reval e r) (seval e s)).
Proof.
apply sapply_elim with 
  (P := fun s i res => eeval e res = seval e s (qeval e i))
  (P0 := fun r s res => seval e res =₁ O.rscomp (reval e r) (seval e s)).
all: intros ; simp eeval ; triv.
- rewrite H, H0. intros [|i'] ; reflexivity.
- rewrite H0, H. reflexivity.
Qed. 

Lemma sapply_sound e s i:
  eeval e (sapply s i) = seval e s (qeval e i).
Proof. now apply sapply_rscomp_sound. Qed.
#[global] Hint Rewrite sapply_sound : eeval seval.

Lemma rscomp_sound e r s :
  seval e (rscomp r s) =₁ O.rscomp (reval e r) (seval e s).
Proof. now apply sapply_rscomp_sound. Qed.
#[global] Hint Rewrite rscomp_sound : eeval seval.

Lemma sapply_rscomp_irred :
  (forall s i, sirred s -> qirred i -> eirred (sapply s i)) *
  (forall r s, rirred r -> sirred s -> sirred (rscomp r s)).
Proof.
apply sapply_elim with 
  (P := fun s i res => sirred s -> qirred i -> eirred res)
  (P0 := fun r s res => rirred r -> sirred s -> sirred res).
all: intros ; triv.
- apply sapply_aux_irred ; triv. intros H1 H2 H3. rewrite eirred_subst_var.
  split6 ; triv. intros [? ?] ; triv.
- rewrite qirred_rapply in H1. apply sapply_aux_irred ; triv. 
  + now apply H.
  + intros H2 H3 H4. rewrite eirred_subst_var. split6 ; triv.
    * now apply H.
    * intros [? ?] ; triv.
- apply sapply_aux_irred ; triv. intros H1 H2 H3. rewrite eirred_subst_var.
  split6 ; triv. 
- apply scomp_aux_irred ; triv. intros H1. rewrite sirred_shift_l.
  split3 ; triv. 
- rewrite sirred_cons. rewrite rirred_cons in H1. split.
  + apply H ; triv.
  + apply H0 ; triv.
- assert (H3 : rirred r1 /\ rirred r2).
  { split ; intros H' ; apply H1 ; triv. }
  apply H0 ; triv. apply H ; triv.
- apply scomp_aux_irred ; triv.
  + rewrite sirred_ren ; triv.
  + intros H1 H2. rewrite sirred_ren_l. split3 ; triv.
Qed.

(*********************************************************************************)
(** *** [sren] *)
(*********************************************************************************)

(** Turn an irreducible renaming into an irreducible substitution. *)
Equations sren (r : ren) : subst :=
sren R_id := S_id ;
sren R_shift := S_shift ;
sren (R_cons i r) := S_cons (E_tvar i) (sren r) ;
sren (R_comp r1 r2) := S_comp (sren r1) (sren r2) ;
sren (R_mvar r) := S_ren (R_mvar r).

Lemma sren_sound e r : 
  seval e (sren r) =₁ O.rscomp (reval e r) O.E_var.
Proof.
funelim (sren r) ; simp eeval qeval ; triv.
+ rewrite H. intros [|] ; reflexivity.
+ rewrite H0, H. reflexivity.
Qed.  
#[global] Hint Rewrite sren_sound : seval eeval.

Lemma sren_irred r : rirred r -> sirred (sren r).
Proof.
intros H. funelim (sren r) ; triv.
- rewrite sirred_cons, eirred_tvar. rewrite rirred_cons in H0.
  split ; triv. now apply H.
- rewrite rirred_comp in H1. feed H ; triv. feed H0 ; triv.
  rewrite sirred_comp. split7 ; triv.
  + funelim (sren r1) ; try discriminate. triv.
  + funelim (sren r1) ; try discriminate. triv.
  + funelim (sren r1) ; try discriminate. triv.
  + funelim (sren r2) ; try discriminate. triv.
  + funelim (sren r1) ; triv. funelim (sren r2) ; triv.
    destruct H2 as (_ & _ & _ & _ & _ & _ & H2). triv.     
- rewrite sirred_ren. triv.
Qed.

(*********************************************************************************)
(** *** [rup] *)
(*********************************************************************************)

(** Lift a renaming through a binder. *)
Equations rup (r : ren) : ren :=
rup r := R_cons Q_zero (rcomp r R_shift).

Lemma rup_sound e r : 
  reval e (rup r) =₁ up_ren (reval e r).
Proof. simp rup qeval. reflexivity. Qed.
#[global] Hint Rewrite rup_sound : reval qeval.

Lemma rup_irred r : rirred r -> rirred (rup r).
Proof. 
intros H. simp rup. rewrite rirred_cons. split ; triv.
apply rapply_rcomp_irred ; triv.
Qed.

(*********************************************************************************)
(** *** [rename_aux] *)
(*********************************************************************************)

(** Helper function for [rename] which takes care of trivial cases. *)
Equations rename_aux {k} (t : expr k) (r : ren) : expr k :=
rename_aux t R_id := t ;
rename_aux t r := E_ren t r.

Lemma rename_aux_sound e {k} (t : expr k) r :
  eeval e (rename_aux t r) = O.rename (eeval e t) (reval e r).
Proof.
funelim (rename_aux t r) ; simp reval ; triv. now rewrite O.ren_rid.
Qed.
#[global] Hint Rewrite rename_aux_sound : eeval seval.

Lemma rename_aux_irred {k} (t : expr k) r :
  eirred t -> rirred r -> (r <> R_id -> eirred (E_ren t r)) ->
  eirred (rename_aux t r).
Proof.
intros H1 H2 H3. funelim (rename_aux t r) ; triv.
all: solve [ apply H3 ; triv ].
Qed.

(*********************************************************************************)
(** *** [substitute_aux] *)
(*********************************************************************************)

(** Helper function for [rename] which takes care of trivial cases. *)
Equations substitute_aux {k} (t : expr k) (s : subst) : expr k :=
substitute_aux t S_id := t ;
substitute_aux (E_tvar i) (S_ren r) := E_tvar (rapply r i) ;
substitute_aux t (S_ren r) := E_ren t r ;
substitute_aux (E_tvar Q_zero) (S_cons t _) := t ;
substitute_aux t s := E_subst t s.

Lemma substitute_aux_sound e {k} (t : expr k) s :
  eeval e (substitute_aux t s) = O.substitute (eeval e t) (seval e s).
Proof.
funelim (substitute_aux t s) ; simp seval eeval qeval ; triv.
all: try solve [ now rewrite O.ren_is_subst ].
now rewrite O.subst_sid.
Qed.
#[global] Hint Rewrite substitute_aux_sound : eeval seval.

Lemma substitute_aux_irred {k} (t : expr k) s :
  eirred t -> sirred s -> 
  (match s with S_ren r => ~is_tvar t -> eirred (E_ren t r) | _ => True end) ->
  (s <> S_id -> ~is_sren s -> ~(is_tvar_zero t /\ is_scons s) -> eirred (E_subst t s)) ->
  eirred (substitute_aux t s).
Proof.
intros H1 H2 H3 H4. funelim (substitute_aux t s) ; triv.
all: try solve [ apply H3 ; triv ].
all: try solve [ apply H4 ; triv ].
- now rewrite sirred_cons in H2.
- rewrite eirred_tvar in *. rewrite sirred_ren in H2. 
  destruct r ; try discriminate. apply rapply_rcomp_irred ; triv.
Qed.

(*********************************************************************************)
(** *** [rename] and [srcomp] *)
(*********************************************************************************)

(** Apply an irreducible renaming to an irreducible expression. *)
Equations rename {k} (t : expr k) (r : ren) : expr k by struct t :=
rename (E_tvar i) r := E_tvar (rapply r i) ;
rename (E_tctor c al) r := E_tctor c (rename al r) ;
rename E_al_nil _ := E_al_nil ;
rename (E_al_cons a al) r := E_al_cons (rename a r) (rename al r) ;
rename (E_abase b x) _ := E_abase b x ;
rename (E_aterm t) r := E_aterm (rename t r) ;
rename (E_abind a) r := E_abind (rename a (rup r)) ;
rename (E_ren e r1) r2 := rename_aux e (rcomp r1 r2) ;
rename (E_subst e s) r := substitute_aux e (srcomp s r) ;
rename e r := rename_aux e r 

(** Compose an irreducible substitution with an irreducible renaming. *)
with srcomp (s : subst) (r : ren) : subst by struct s :=
srcomp S_id r := sren r ;
srcomp (S_cons t s) r := S_cons (rename t r) (srcomp s r) ;
srcomp (S_comp s1 s2) r := scomp_aux s1 (srcomp s2 r) ;
srcomp s r := scomp_aux s (sren r). 

Lemma rename_srcomp_sound e : 
  (forall {k} (t : expr k) r, eeval e (rename t r) = O.rename (eeval e t) (reval e r)) *
  (forall s r, seval e (srcomp s r) =₁ O.srcomp (seval e s) (reval e r)).
Proof.
apply rename_elim with 
  (P := fun {k} (t : expr k) r res => eeval e res = O.rename (eeval e t) (reval e r))
  (P0 := fun s r res => seval e res =₁ O.srcomp (seval e s) (reval e r)).
all: intros ; simp eeval seval qeval reval ; triv.
- now rewrite H.
- now rewrite H, H0.
- now rewrite H.
- rewrite H. now rewrite rup_sound.
- now rewrite O.ren_ren.
- now rewrite O.ren_subst, H.
- rewrite H, H0. intros [|] ; reflexivity.
- rewrite H. intros i. cbv [O.scomp O.srcomp]. now rewrite O.ren_subst.
- intros i. cbv [O.scomp O.srcomp]. now rewrite O.ren_is_subst.
Qed.

Lemma rename_sound {k} e (t : expr k) r :
  eeval e (rename t r) = O.rename (eeval e t) (reval e r).
Proof. now apply rename_srcomp_sound. Qed.
#[global] Hint Rewrite @rename_sound : eeval seval.

Lemma srcomp_sound e s r :
  seval e (srcomp s r) =₁ O.srcomp (seval e s) (reval e r).
Proof. now apply rename_srcomp_sound. Qed.
#[global] Hint Rewrite srcomp_sound : eeval seval.

Lemma rename_srcomp_irred :
  (forall {k} (t : expr k) r, eirred t -> rirred r -> eirred (rename t r)) *
  (forall s r, sirred s -> rirred r -> sirred (srcomp s r)).
Proof.
apply rename_elim with 
  (P := fun {k} (t : expr k) r res => eirred t -> rirred r -> eirred res)
  (P0 := fun s r res => sirred s -> rirred r -> sirred res).
all: intros ; triv.
- rewrite eirred_tvar in *. apply rapply_rcomp_irred ; triv.
- rewrite eirred_tctor in *. now apply H.
- apply rename_aux_irred ; triv. intros H1. intros H' ; inv H' ; triv.
  destruct H4 ; triv.
- rewrite eirred_al_cons in *. split ; [apply H | apply H0] ; triv.
- rewrite eirred_aterm in *. now apply H.
- rewrite eirred_abind in *. apply H ; triv. now apply rup_irred.
- rewrite eirred_ren in H. apply rename_aux_irred ; triv.
  + destruct e ; triv.
  + apply rapply_rcomp_irred ; triv.
  + intros H2. rewrite eirred_ren. split3 ; triv.
    apply rapply_rcomp_irred ; triv.
- rewrite eirred_subst in H0. feed2 H ; triv. 
  apply substitute_aux_irred ; triv.
  + destruct (srcomp s r) ; triv. intros H4. rewrite sirred_ren in H. 
    destruct r0 ; try discriminate. rewrite eirred_ren. split3 ; triv.
    destruct H0 as (_ & _ & H0 & _). destruct e ; triv.
    all: exfalso ; apply H0 ; triv.
  + intros H4 H5 H6. rewrite eirred_subst. split7 ; triv.
- now apply sren_irred.
- apply scomp_aux_irred ; triv. 
  + now apply sren_irred.
  + intros H1 H2. rewrite sirred_shift_l. split3 ; triv.
    now apply sren_irred.
- rewrite sirred_cons in *. split ; [apply H | apply H0] ; triv.
- rewrite sirred_comp in H0. feed2 H ; triv. apply scomp_aux_irred ; triv.
  intros H4 H5. rewrite sirred_comp. split7 ; triv.
- rewrite sirred_ren in H. destruct r0 ; triv. apply scomp_aux_irred.
  + now rewrite sirred_ren.
  + now apply sren_irred.
  + intros H1 H2. rewrite sirred_ren_l. split3 ; triv. now apply sren_irred.
- apply scomp_aux_irred ; triv.
  + now apply sren_irred.
  + intros H1 H2. rewrite sirred_mvar_l. split ; triv.
    now apply sren_irred.   
Qed.

(*********************************************************************************)
(** *** [sup] *)
(*********************************************************************************)

(** Lift a substitution through a binder. *)
Equations sup (s : subst) : subst :=
sup s := S_cons (E_tvar Q_zero) (srcomp s R_shift).

Lemma sup_sound e s : seval e (sup s) =₁ O.up_subst (seval e s).
Proof. simp sup seval eeval. reflexivity. Qed.
#[global] Hint Rewrite sup_sound : seval eeval.

Lemma sup_irred s : sirred s -> sirred (sup s).
Proof. 
intros H. simp sup. rewrite sirred_cons. split.
- rewrite eirred_tvar. triv.
- apply rename_srcomp_irred ; triv.
Qed.  

(*********************************************************************************)
(** *** [substitute] and [scomp] *)
(*********************************************************************************)

(** Apply an irreducible substitution to an irreducible expression. *)
Equations substitute {k} (t : expr k) (s : subst) : expr k by struct t :=
substitute (E_tvar i) s := sapply s i ;
substitute (E_tctor c al) s := E_tctor c (substitute al s) ;
substitute E_al_nil _ := E_al_nil ;
substitute (E_al_cons a al) s := E_al_cons (substitute a s) (substitute al s) ;
substitute (E_abase b x) _ := E_abase b x ;
substitute (E_aterm t) s := E_aterm (substitute t s) ;
substitute (E_abind a) s := E_abind (substitute a (sup s)) ;
substitute (E_ren e r) s := substitute_aux e (rscomp r s) ;
substitute (E_subst e s1) s2 := substitute_aux e (scomp s1 s2) ;
substitute e s := substitute_aux e s 

(** Compose two irreducible substitutions. *)
with scomp (s1 s2 : subst) : subst by struct s1 :=
scomp S_id s := s ;
scomp (S_cons t s1) s2 := S_cons (substitute t s2) (scomp s1 s2) ;
scomp (S_comp s1 s2) s3 := scomp_aux s1 (scomp s2 s3) ;
scomp s1 s2 := scomp_aux s1 s2. 

Lemma substitute_scomp_sound e : 
  (forall {k} (t : expr k) s, eeval e (substitute t s) = O.substitute (eeval e t) (seval e s)) *
  (forall s1 s2, seval e (scomp s1 s2) =₁ O.scomp (seval e s1) (seval e s2)).
Proof.
apply substitute_elim with
  (P := fun {k} (t : expr k) s res => eeval e res = O.substitute (eeval e t) (seval e s))
  (P0 := fun s1 s2 res => seval e res =₁ O.scomp (seval e s1) (seval e s2)).
all: intros ; simp eeval seval ; triv.
- now rewrite H.
- now rewrite H, H0.
- now rewrite H.
- now rewrite H, sup_sound.
- now rewrite O.subst_ren.
- now rewrite H, O.subst_subst.
- rewrite H, H0. now rewrite O.scomp_scons_distrib.
- rewrite H. now rewrite O.scomp_assoc.
Qed.

Lemma substitute_sound e {k} (t : expr k) s :
  eeval e (substitute t s) = O.substitute (eeval e t) (seval e s).
Proof. now apply substitute_scomp_sound. Qed.
#[global] Hint Rewrite substitute_sound : eeval seval.

Lemma scomp_sound e s1 s2 :
  seval e (scomp s1 s2) =₁ O.scomp (seval e s1) (seval e s2).
Proof. now apply substitute_scomp_sound. Qed.
#[global] Hint Rewrite scomp_sound : eeval seval.

Lemma substitute_scomp_irred : 
  (forall {k} (t : expr k) s, eirred t -> sirred s -> eirred (substitute t s)) *
  (forall s1 s2, sirred s1 -> sirred s2 -> sirred (scomp s1 s2)).
Proof.
apply substitute_elim with   
  (P := fun {k} (t : expr k) s res => eirred t -> sirred s -> eirred res)
  (P0 := fun s1 s2 res => sirred s1 -> sirred s2 -> sirred res).
all: intros ; triv.
- rewrite eirred_tvar in H. now apply sapply_rscomp_irred.
- rewrite eirred_tctor in *. now apply H.
- apply substitute_aux_irred ; triv.
  + destruct s ; triv. intros _. rewrite eirred_ren. 
    rewrite sirred_ren in H0. destruct r ; try discriminate. 
    split3 ; triv.
  + intros H1 H2 H3. rewrite eirred_subst. split7 ; triv. 
- rewrite eirred_al_cons in *. feed2 H ; triv. feed2 H0 ; triv.
- rewrite eirred_aterm in *. now apply H.
- rewrite eirred_abind in *. apply H ; triv. apply sup_irred ; triv.
- rewrite eirred_ren in H. destruct e ; triv. apply substitute_aux_irred ; triv. 
  + apply sapply_rscomp_irred ; triv.
  + assert (H1 : sirred (rscomp r s)) by now apply sapply_rscomp_irred.
    destruct (rscomp r s) ; triv. intros _. rewrite sirred_ren in H1. 
    destruct r0 ; try discriminate. rewrite eirred_ren. split3 ; triv.
  + intros H1 H2 H3. rewrite eirred_subst. split7 ; triv.
    apply sapply_rscomp_irred ; triv. 
- rewrite eirred_subst in H0. feed2 H ; triv. apply substitute_aux_irred ; triv.
  + destruct (scomp s1 s2) ; triv. intros H4. rewrite eirred_ren.
    destruct H0 as (H5 & H6 & H7 & H8 & H9 & H10 & H11). 
    rewrite sirred_ren in H. destruct r ; triv. destruct e ; triv.
    all: solve [ exfalso ; apply H7 ; triv ].
  + intros H4 H5 H6. rewrite eirred_subst. split7 ; triv.
- apply scomp_aux_irred ; triv. intros H1 H2. rewrite sirred_shift_l. split3 ; triv.
- rewrite sirred_cons in *. feed2 H ; triv. feed2 H0 ; triv.
- rewrite sirred_comp in H0. feed2 H ; triv. apply scomp_aux_irred ; triv.
  intros H4 H5. rewrite sirred_comp. split7 ; triv.
- rewrite sirred_ren in H. destruct r ; triv. apply scomp_aux_irred ; triv.
  + rewrite sirred_ren. triv.
  + intros H1 H2. rewrite sirred_ren_l. split3 ; triv.
- apply scomp_aux_irred ; triv. intros H1 H2. rewrite sirred_mvar_l. split ; triv.
Qed.

(*********************************************************************************)
(** *** [esimp] and [ssimp] *)
(*********************************************************************************)

(** Simplify an expression. *)
Equations esimp {k} (t : expr k) : expr k :=
esimp (E_tvar i) := E_tvar (qsimp i) ;
esimp (E_tctor c al) := E_tctor c (esimp al) ;
esimp E_al_nil := E_al_nil ;
esimp (E_al_cons a al) := E_al_cons (esimp a) (esimp al) ;
esimp (E_abase b x) := E_abase b x ;
esimp (E_aterm t) := E_aterm (esimp t) ;
esimp (E_abind a) := E_abind (esimp a) ;
esimp (E_ren t r) := rename (esimp t) (rsimp r) ;
esimp (E_subst t s) := substitute (esimp t) (ssimp s) ;
esimp (E_mvar m) := E_mvar m 

(** Simplify a substitution. *)
with ssimp (s : subst) : subst :=
ssimp S_id := S_id ;
ssimp S_shift := S_shift ;
ssimp (S_cons t s) := S_cons (esimp t) (ssimp s) ;
ssimp (S_comp s1 s2) := scomp (ssimp s1) (ssimp s2) ;
ssimp (S_ren r) := sren (rsimp r) ;
ssimp (S_mvar m) := S_mvar m.

Lemma esimp_ssimp_sound e :
  (forall {k} (t : expr k), eeval e (esimp t) = eeval e t) *
  (forall s, seval e (ssimp s) =₁ seval e s).
Proof.
apply esimp_elim with 
  (P := fun _ t res => eeval e res = eeval e t)
  (P0 := fun s res => seval e res =₁ seval e s).
all: intros ; simp eeval seval qeval ; triv.
all: try solve [ now rewrite H ]. 
all: try solve [ now rewrite H, H0 ]. 
Qed.

Lemma esimp_sound e {k} (t : expr k) : 
  eeval e (esimp t) = eeval e t.
Proof. now apply esimp_ssimp_sound. Qed.
#[global] Hint Rewrite esimp_sound : eeval seval.

Lemma ssimp_sound e s : seval e (ssimp s) =₁ seval e s.
Proof. now apply esimp_ssimp_sound. Qed.
#[global] Hint Rewrite ssimp_sound : eeval seval.

Lemma esimp_ssimp_irred :
  (forall {k} (t : expr k), eirred (esimp t)) *
  (forall s, sirred (ssimp s)).
Proof.
apply esimp_elim with (P := fun _ _ res => eirred res) (P0 := fun _ res => sirred res).
all: intros ; triv.
- rewrite eirred_tvar. now apply qsimp_irred.
- now rewrite eirred_tctor.
- now rewrite eirred_al_cons.
- now rewrite eirred_aterm.
- now rewrite eirred_abind.
- apply rename_srcomp_irred ; triv. now apply rsimp_irred.
- apply substitute_scomp_irred ; triv.
- now rewrite sirred_cons.
- apply substitute_scomp_irred ; triv.
- apply sren_irred. now apply rsimp_irred.
Qed.

Lemma esimp_irred {k} (t : expr k) : eirred (esimp t).
Proof. now apply esimp_ssimp_irred. Qed.

Lemma ssimp_irred s : sirred (ssimp s).
Proof. now apply esimp_ssimp_irred. Qed.

End Make.