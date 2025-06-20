From Sulfur Require Import Prelude Sig ExplicitSyntax.

(** The output of simplification (Simplification.v) is good for comparing
    terms/substitutions for equality, but not very nice to work with for the user. 
    This file implements cleanup functions which do trivial transformations 
    such as turning [Q_rapply R_shift i] into [Q_succ i], and are 
    typically applied after simplification. 
    Cleanup functions can be applied to all terms (not only the output 
    of [Simplification.v].
    
    We formulate the correctness of cleanup as a rewriting system 
    ([qred], [rred], [ered], [sred]), which is proved correct with 
    respect to evaluation (lemmas [ered_sound], [sred_sound], etc).
    Contrary to simplification, we don't prove that we obtain
    irreducible forms (for the cleanup rewriting system) because it is
    too much effort, although we might do the proofs in the future.
*)

Section WithSignature.
Context {sig : signature}.

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
funelim (mk_qsucc n i) ; simp mk_qsucc qeval ; auto.
rewrite H. lia. 
Qed.
#[local] Hint Rewrite eval_mk_qsucc : qeval.

(*********************************************************************************)
(** *** [dest_rshift] *)
(*********************************************************************************)

(** [dest_rshift r] checks if [r] is of the form [rshift >> rshift >> rshift >> ...]
    (with at least one shift, and up to associativity): 
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
funelim (dest_rshift r) ; simp dest_rshift in * ; try easy.
- intros H. depelim H. reflexivity.
- intros H. depelim H. simp qeval. apply (Hind e n2) in Heq. rewrite Heq. 
  apply (Hind0 e n1) in Heq0. rewrite Heq0. cbv [Prelude.rcomp]. intros i. lia.
Qed.

(*********************************************************************************)
(** *** [dest_ren] *)
(*********************************************************************************)

Equations dest_ren (s : subst) : option ren :=
dest_ren S_id := Some R_id ;
dest_ren S_shift := Some R_shift ;
dest_ren (S_cons (E_var i) s) with dest_ren s := {
  | Some r => Some (R_cons i r) 
  | _ => None 
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
funelim (dest_ren s).
all: intros H ; depelim H ; simp eeval qeval in * ; try reflexivity.
- rewrite (Hind e r Heq). simp eeval. intros [|] ; reflexivity.
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
| ered_congr_tvar : Proper (qred ==> ered) E_var
| ered_congr_tctor c : Proper (ered ==> ered) (E_ctor c)
| ered_congr_al_cons {ty tys} : Proper (ered ==> ered ==> ered) (@E_al_cons _ ty tys)
| ered_congr_aterm : Proper (ered ==> ered) E_aterm
| ered_congr_abind {ty} : Proper (ered ==> ered) (@E_abind _ ty)
| ered_congr_afunctor {ty} f sh : Proper (vec_eq ered ==> ered) (@E_afunctor _ ty f sh)
| ered_congr_sapply : Proper (sred ==> qred ==> ered) E_sapply
| ered_congr_ren {k} : Proper (rred ==> ered ==> ered) (@E_ren _ k)
| ered_congr_subst {k} : Proper (sred ==> ered ==> ered) (@E_subst _ k)
(* Cleanup rules. *)
| ered_ren_var r i : E_ren r (E_var i) =e=> E_var (Q_rapply r i)
| ered_subst_ren {k} s r (t : expr k) : dest_ren s = Some r -> E_subst s t =e=> E_ren r t
| ered_subst_var s i : E_subst s (E_var i) =e=> E_sapply s i
| ered_sapply_ren s r i : dest_ren s = Some r -> E_sapply s i =e=> E_ren r (E_var i)

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
apply qred_rred_ind ; intros ; simp qeval ; auto.
- now rewrite H0, H2.
- now rewrite H0, H2.
- now rewrite (dest_rshift_sound _ _ _ H).
- reflexivity.
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
apply ered_sred_ind ; intros ; simp eeval ; auto.
all: try solve [ now rewrite H0 | now rewrite H0, H2 ].
- eapply qred_sound in H. now rewrite H.
- f_equal. apply vec_ext. intros i. simp vec_nth.
- eapply qred_sound in H1. now rewrite H0, H1.
- eapply rred_sound in H. now rewrite H1, H.
- eapply dest_ren_sound in H. rewrite H. simp eeval.
  now rewrite P.ren_is_subst.
- eapply dest_ren_sound in H. rewrite H. simp eeval. simp rename. reflexivity.
- reflexivity.
- eapply rred_sound in H. now rewrite H.
Qed.

Lemma ered_sound {k} e (t t' : expr k) : t =e=> t' -> eeval e t = eeval e t'.
Proof. now apply ered_sred_sound. Qed.

Lemma sred_sound e s s' : s =s=> s' -> seval e s =₁ seval e s'.
Proof. now apply ered_sred_sound. Qed.

(*********************************************************************************)
(** *** [rapply]. *)
(*********************************************************************************)

(** Cleanup [Q_rapply r i]. *)
Equations rapply : ren -> qnat -> qnat :=
rapply r i with dest_rshift r := { 
  | Some n => mk_qsucc n i 
  | None => Q_rapply r i
  }. 

Lemma rapply_red r i : Q_rapply r i =q=> rapply r i.
Proof. funelim (rapply r i) ; auto. Qed.
#[local] Hint Rewrite <-rapply_red : red.

(*********************************************************************************)
(** *** [qclean] and [rclean]. *)
(*********************************************************************************)

Equations qclean : qnat -> qnat :=
qclean Q_zero := Q_zero ;
qclean (Q_succ i) := Q_succ (qclean i) ;
qclean (Q_rapply r i) := rapply (rclean r) (qclean i) ;
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
all: intros ; simp red ; auto.
all: solve [ now rewrite <-H, <-H0 ].
Qed.

Lemma qclean_red i : i =q=> qclean i.
Proof. now apply qrclean_red. Qed.
#[local] Hint Rewrite <-qclean_red : red.

Lemma rclean_red r : r =r=> rclean r.
Proof. now apply qrclean_red. Qed.
#[local] Hint Rewrite <-rclean_red : red.

(*********************************************************************************)
(** *** [sapply]. *)
(*********************************************************************************)

(** Cleanup [E_sapply s i]. *)
Equations sapply : subst -> qnat -> expr Kt :=
sapply s i with dest_ren s := { 
  | Some r => E_var (rapply r i)
  | None => E_sapply s i
  }. 

Lemma sapply_red s i : E_sapply s i =e=> sapply s i.
Proof. 
funelim (sapply s i) ; simp red.
- rewrite <-ered_ren_var. auto.
- reflexivity.  
Qed.
#[local] Hint Rewrite <-sapply_red : red.

(*********************************************************************************)
(** *** [rename] *)
(*********************************************************************************)

(** Cleanup [E_ren r t]. *)
Equations rename {k} : ren -> expr k -> expr k :=
rename r (E_var i) := E_var (rapply r i) ;
rename r t := E_ren r t.

Lemma rename_red {k} r (t : expr k) : E_ren r t =e=> rename r t.
Proof. funelim (rename r t) ; simp red ; easy. Qed.
#[local] Hint Rewrite <-@rename_red : red.

(*********************************************************************************)
(** *** [substitute] *)
(*********************************************************************************)

(** Cleanup [E_subst s t]. *)
Equations substitute {k} : subst -> expr k -> expr k :=
substitute s (E_var i) := sapply s i ;
substitute s t with dest_ren s := {
  | Some r => rename r t 
  | None => E_subst s t
  }.

Lemma substitute_red {k} s (t : expr k) : E_subst s t =e=> substitute s t.
Proof. funelim (substitute s t) ; simp red ; auto ; try easy. Qed.
#[local] Hint Rewrite <-@substitute_red : red.

(*********************************************************************************)
(** *** [eclean] and [sclean] *)
(*********************************************************************************)
  
Equations eclean {k} : expr k -> expr k :=
eclean (E_var i) := E_var (qclean i) ;
eclean (E_ctor c al) := E_ctor c (eclean al) ;
eclean E_al_nil := E_al_nil ;
eclean (E_al_cons a al) := E_al_cons (eclean a) (eclean al) ;
eclean (E_abase b x) := E_abase b x ;
eclean (E_aterm t) := E_aterm (eclean t) ;
eclean (E_abind a) := E_abind (eclean a) ;
eclean (E_afunctor f sh al) := E_afunctor f sh (vec_map eclean al) ;
eclean (E_sapply s i) := sapply (sclean s) (qclean i) ;
eclean (E_ren r t) := rename (rclean r) (eclean t) ;
eclean (E_subst s t) := substitute (sclean s) (eclean t) ;
eclean (E_mvar m) := E_mvar m

with sclean : subst -> subst :=
sclean S_id := S_id ;
sclean S_shift := S_shift ;
sclean (S_cons t s) := S_cons (eclean t) (sclean s) ;
sclean (S_comp s1 s2) := S_comp (sclean s1) (sclean s2) ;
sclean (S_ren r) := S_ren (rclean r) ;
sclean (S_mvar m) := S_mvar m.

Lemma eclean_sclean_red : 
  (forall k (t : expr k), t =e=> eclean t) /\ (forall s, s =s=> sclean s).
Proof.
apply expr_subst_ind.
all: intros ; simp eclean red ; auto ; try easy.
all: try solve [ now rewrite <-H | now rewrite <-H, <-H0 ].
f_equiv. intros i. simp vec_nth. 
Qed. 

Lemma eclean_red {k} (t : expr k) : t =e=> eclean t.
Proof. now apply eclean_sclean_red. Qed.
#[local] Hint Rewrite @eclean_red : red.

Lemma sclean_red s : s =s=> sclean s.
Proof. now apply eclean_sclean_red. Qed.
#[local] Hint Rewrite sclean_red : red.

End WithSignature.

