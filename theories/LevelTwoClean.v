From Prototype Require Import Prelude Sig LevelOne LevelTwo.

(** The output of simplification (LevelTwoSimp.v) is good for comparing
    terms/equations for equality, but not very nice to work with. 
    
    This file implements cleanup functions, which are meant to be run on irreducible terms,
    and which do trivial transformations such as turning [Q_rapply R_shift i]
    into [Q_succ i]. We do not require that cleanup functions produce irreducible
    terms/substitutions. 

    For each cleanup function we prove a soundness lemma. *)

Module Make (S : Sig).
Include LevelTwo.Make (S).

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
  apply (Hind0 e n1) in Heq0. rewrite Heq0. cbv [rcomp]. intros i. lia.
Qed.

(*********************************************************************************)
(** *** [qclean] and [rclean]. *)
(*********************************************************************************)

(** Handle the [Q_rapply r i] case of [qclean]. *)
Equations qclean_rapply : ren -> qnat -> qnat :=
qclean_rapply r i with dest_rshift r := { 
  | Some n => mk_qsucc n i 
  | None => Q_rapply r i
  }. 

Lemma qclean_rapply_sound e r i :
  qeval e (qclean_rapply r i) = qeval e (Q_rapply r i).
Proof. 
funelim (qclean_rapply r i ) ; triv. simp qeval. rewrite (dest_rshift_sound _ _ _ Heq).
now rewrite eval_mk_qsucc.
Qed.

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

Lemma qclean_rclean_sound e : 
  (forall i, qeval e (qclean i) = qeval e i) *
  (forall r, reval e (rclean r) =₁ reval e r).
Proof.
apply qclean_elim with 
  (P := fun i res => qeval e res = qeval e i)
  (P0 := fun r res => reval e res =₁ reval e r).
all: intros ; simp qeval in * ; triv.
- rewrite qclean_rapply_sound. simp qeval. now rewrite H, H0.
- now rewrite H, H0.
- now rewrite H, H0.
Qed.

(*********************************************************************************)
(** *** [dest_ren] *)
(*********************************************************************************)

Equations dest_ren (s : subst) : option ren :=
dest_ren S_id := Some R_id ;
dest_ren S_shift := Some R_shift ;
dest_ren (S_cons (E_tvar i) s) with dest_ren s := {
  | Some r => Some (R_cons i r) 
  | None => None 
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
- rewrite (Hind e r Heq). simp eeval. intros [|] ; reflexivity.
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
Proof.
funelim (eclean_ren r t) ; triv. simp eeval. rewrite qclean_rapply_sound. 
simp qeval. reflexivity.
Qed.

(** Handle the [E_subst s e] case of [eclean]. *)
Equations eclean_subst {k} : subst -> expr k -> expr k :=
eclean_subst s e with dest_ren s := {
  | Some r => eclean_ren r e 
  | None => E_subst s e
  }.

Lemma eclean_subst_sound {k} e s (t : expr k) :
  eeval e (eclean_subst s t) = eeval e (E_subst s t).
Proof.
funelim (eclean_subst s t) ; triv. rewrite eclean_ren_sound ; simp eeval.
rewrite (dest_ren_sound _ _ _ Heq). simp eeval. now rewrite O.ren_is_subst.
Qed. 
  
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
Admitted.

End Make.

