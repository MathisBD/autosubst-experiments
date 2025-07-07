From Coq Require Import List.


Inductive ty :=
| base 
| arr (A B : ty).


Inductive tm :=
| var (idx : nat)
| app (t u : tm)
| lam (T : ty) (t : tm).

Definition rup (r : nat -> nat) : nat -> nat :=
fun idx =>
  match idx with 
  | 0 => 0
  | S idx => S (r idx)
  end.
  
Fixpoint ren (r : nat -> nat) (t : tm) : tm :=
match t with 
| var idx => var (r idx)
| app t u => app (ren r t) (ren r u)
| lam T t => lam T (ren (rup r) t)
end.

Definition sup (s : nat -> tm) : nat -> tm :=
fun idx =>
  match idx with 
  | 0 => var 0
  | S idx => ren S (s idx)
  end.
  
Fixpoint subst (s : nat -> tm) (t : tm) : tm :=
match t with 
| var idx => s idx
| app t u => app (subst s t) (subst s u)
| lam T t => lam T (subst (sup s) t)
end.

(** Typing judgement. *)
Inductive typing : list ty -> tm -> ty -> Prop :=

| typing_var Γ idx T : 
    List.nth_error Γ idx = Some T ->
    typing Γ (var idx) T

| typing_app Γ t u A B : 
    typing Γ t (arr A B) ->
    typing Γ u A ->
    typing Γ (app t u) B

| typing_lam Γ t A B :
    typing (A :: Γ) t B ->
    typing Γ (lam A t) (arr A B).

Definition spoint (t : tm) (idx : nat) : tm :=
  match idx with 
  | 0 => t 
  | S idx => var idx
  end.

(** One-step beta-reduction. *)
Inductive red1 : tm -> tm -> Prop :=

| red1_beta t u T : 
    red1 (app (lam T t) u) (subst (spoint u) t)
    
| red1_app_l t t' u :
    red1 t t' ->
    red1 (app t u) (app t' u)

| red1_app_r t u u' :
    red1 u u' ->
    red1 (app t u) (app t u')
    
| red1_lam T t t' :
    red1 t t' ->
    red1 (lam T t) (lam T t').

Lemma typing_ren Γ Γ' t r T : 
  typing Γ t T ->
  (forall i, nth_error Γ i = nth_error Γ' (r i)) ->
  typing Γ' (ren r t) T.
Proof.
intros Ht Hr. induction t in Γ, Γ', r, T, Ht, Hr |- *.
all: inversion Ht ; subst ; clear Ht ; cbn in *.
- constructor. rewrite <-Hr. assumption.
- econstructor.
  + eapply IHt1 ; eassumption.
  + eapply IHt2 ; eassumption.
- econstructor. eapply IHt.
  + eassumption.
  + intros [|i] ; cbn.
    * reflexivity.
    * apply Hr.
Qed.

Lemma typing_subst Γ Γ' t s T :
  typing Γ t T ->
  (forall i A, nth_error Γ i = Some A -> typing Γ' (s i) A) ->
  typing Γ' (subst s t) T.
Proof.
intros Ht Hs. induction Ht in Γ', s, Hs |- *.
- apply Hs. assumption.
- cbn. econstructor ; eauto.
- cbn. constructor. apply IHHt. intros [|i] T H ; cbn in *.
  + constructor. cbn. assumption.
  + eapply typing_ren ; eauto. 
Qed.

Lemma preservation :
  forall Γ t t' T,
    typing Γ t T -> 
    red1 t t' ->
    typing Γ t' T.
Proof.
intros Γ t t' T Hty Hred. induction Hred in Γ, T, Hty |- *.
all: inversion Hty ; subst ; clear Hty.
- inversion H2 ; subst ; clear H2. eapply typing_subst.
  + eassumption.
  + intros [|i] B H ; cbn in *.
    * inversion H ; subst ; assumption.
    * now constructor.
- econstructor.
  + apply IHHred. eassumption.
  + assumption.
- econstructor.
  + eassumption.
  + apply IHHred. assumption.
- econstructor. apply IHHred. assumption. 
Qed.         