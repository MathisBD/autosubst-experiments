From Prototype Require Export All.

(*********************************************************************************)
(** *** Generate all operations and lemmas. *)
(*********************************************************************************)

Module SystemF.

Autosubst Generate 
{{
  expr(var) : Type

  (* Types. *)
  arr : expr -> expr -> expr 
  all : (bind expr in expr) -> expr 

  (* Terms. *)
  app : expr -> expr -> expr 
  tapp : expr -> expr -> expr 
  vt : expr -> expr 

  (* Values. *)
  lam : expr -> (bind expr in expr) -> expr 
  tlam : (bind expr in expr) -> expr
}}.

End SystemF.
Import SystemF.

Derive NoConfusion NoConfusionHom for expr.

Notation ty := expr (only parsing).
Notation tm := expr (only parsing).
Notation vl := expr (only parsing).

Inductive sort := Sty | Stm | Svl. 
Derive NoConfusion for sort.

Tactic Notation "rapply" constr(t) :=
  let tac2 := ltac2:(t |- 
  eapply_eq_gen 
    (fun ty => constr:(@eq $ty))
    (fun () => () (*try (solve [ reflexivity | ltac1:(rasimpl) ; reflexivity ])*))
    (Option.get (Ltac1.to_constr t)))  
  in
  tac2 t ;
  shelve_unifiable.

(*********************************************************************************)
(** *** Triggers for [rasimpl]. *)
(*********************************************************************************)

(** Trigger [rasimpl] on [rename _ _]. *)
Lemma rasimpl_trigger_rename (r : ren) (t res : expr) :
  TermSimplification (rename r t) res -> rename r t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> rasimpl_trigger_rename : asimpl_topdown.

(** Trigger [rasimpl] on [substitute _ _]. *)
Lemma rasimpl_trigger_substitute (s : subst) (t res : expr) :
  TermSimplification (substitute s t) res -> substitute s t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> rasimpl_trigger_substitute : asimpl_topdown.

(*Axiom P : expr -> Prop.
Axiom t : expr.
Lemma test (H : forall t r, P (rename r t)) : P (var 0).
Proof. rapply H. rasimpl. Unshelve. 2: exact t. rasimpl. *)

(*********************************************************************************)
(** *** Scoping for terms. *)
(*********************************************************************************)

Definition scope := list sort.

(** Scoping as a proposition. *)
Inductive scoping : scope -> expr -> sort -> Prop :=

| scoping_var Γ i s :
    nth_error Γ i = Some s -> scoping Γ (var i) s

| scoping_arr Γ t1 t2 : 
    scoping Γ t1 Sty -> scoping Γ t2 Sty -> scoping Γ (arr t1 t2) Sty

| scoping_all Γ t : 
    scoping (Sty :: Γ) t Sty -> scoping Γ (all t) Sty

| scoping_app Γ t1 t2 :
    scoping Γ t1 Stm -> scoping Γ t2 Stm -> scoping Γ (app t1 t2) Stm

| scoping_tapp Γ t1 t2 : 
    scoping Γ t1 Stm -> scoping Γ t2 Sty -> scoping Γ (tapp t1 t2) Stm

| scoping_vt Γ t : 
    scoping Γ t Svl -> scoping Γ (vt t) Stm

| scoping_lam Γ t1 t2 : 
    scoping Γ t1 Sty -> scoping (Svl :: Γ) t2 Stm -> scoping Γ (lam t1 t2) Svl

| scoping_tlam Γ t :
    scoping (Sty :: Γ) t Stm -> scoping Γ (tlam t) Svl.

Derive Signature for scoping.

(** Trigger [rasimpl] on [scoping]. *)
Lemma rasimpl_trigger_scoping Γ t1 t2 m :
  TermSimplification t1 t2 ->
    scoping Γ t1 m <-> scoping Γ t2 m.
Proof. intros H. now rewrite (@term_simplification _ t1 t2 H). Qed.
#[export] Hint Rewrite -> rasimpl_trigger_scoping : asimpl_outermost.

(** Read the sort of a (well-scoped) expression. *)
Definition read_sort (Γ : scope) (t : expr) : sort :=
  match t with 
  | var i => 
    (* We use a dummy sort in case [i] is not in scope. *)
    nth i Γ Sty
  | arr _ _ | all _ => Sty 
  | app _ _ | tapp _ _ | vt _ => Stm
  | lam _ _ | tlam _ => Svl
  end.

(** Relation between the two notions of scoping. *)
Lemma read_sort_spec Γ t s : 
  scoping Γ t s -> read_sort Γ t = s.
Proof. intros H. destruct H ; cbn ; try reflexivity. now apply nth_error_nth. Qed.

(** Consequence: scoping is functional. *)
Lemma scoping_functional Γ t s1 s2 :
  scoping Γ t s1 ->
  scoping Γ t s2 ->
  s1 = s2.
Proof.
intros H1 H2. transitivity (read_sort Γ t).
- symmetry. now apply read_sort_spec.
- now apply read_sort_spec.
Qed. 

(*********************************************************************************)
(** *** Scoping for renamings. *)
(*********************************************************************************)

(** [rscoping Γ r Δ] states that [r] takes inputs in [Δ] and has outputs in [Γ]. *)
Definition rscoping (Γ : scope) (r : ren) (Δ : scope) : Prop :=
  forall i mi,
    nth_error Δ i = Some mi ->
    nth_error Γ (r i) = Some mi.

#[export] Instance rscoping_proper : 
  Proper (eq ==> point_eq ==> eq ==> iff) rscoping.
Proof.
intros ? Γ -> r1 r2 Hr ? t ->. split.
- intros H i mi Hi. rewrite <-Hr. now apply H.
- intros H i mi Hi. rewrite Hr. now apply H.
Qed.

(** Trigger [rasimpl] on [rscoping]. *)
Lemma rasimpl_trigger_rscoping Γ r1 r2 Δ :
  RenSimplification r1 r2 ->
    rscoping Γ r1 Δ <-> rscoping Γ r2 Δ.
Proof. intros H. now rewrite ren_simplification. Qed.
#[export] Hint Rewrite -> rasimpl_trigger_rscoping : asimpl_outermost.

Lemma rscoping_rid Γ :
  rscoping Γ rid Γ.
Proof. intros i mi H. assumption. Qed.
#[export] Hint Resolve rscoping_rid : scoping.

Lemma rscoping_rshift Γ m :
  rscoping (m :: Γ) rshift Γ.
Proof. intros i mi H. now cbn. Qed.
#[export] Hint Resolve rscoping_rshift : scoping.

Lemma rscoping_rcons Γ Δ i mi r : 
  nth_error Γ i = Some mi -> rscoping Γ r Δ -> rscoping Γ (rcons i r) (mi :: Δ).
Proof.
intros Hi Hr x mx Hx. destruct x ; cbn in *.
- depelim Hx. assumption.
- apply Hr. assumption.
Qed.  
#[export] Hint Resolve rscoping_rcons : scoping.

Lemma rscoping_rcomp Γ Δ Ε r1 r2 :
  rscoping Δ r1 Ε -> rscoping Γ r2 Δ -> rscoping Γ (rcomp r1 r2) Ε.
Proof. intros H1 H2 i mi Hi. apply H2. apply H1. assumption. Qed.
#[export] Hint Resolve rscoping_rcomp : scoping.

Lemma rscoping_up_ren Γ Δ r m :
  rscoping Γ r Δ -> rscoping (m :: Γ) (up_ren r) (m :: Δ).
Proof. unfold up_ren. auto with scoping. Qed.
#[export] Hint Resolve rscoping_up_ren : scoping.

(** Renaming preserves the scope. *)
Lemma scoping_rename Γ Δ r t st :
  rscoping Γ r Δ ->
  scoping Δ t st ->
  scoping Γ (rename r t) st.
Proof.
intros Hr Ht. induction Ht in Γ, r, Hr |- *.
all: solve [ rasimpl ; constructor ; auto with scoping ].
Qed.
#[export] Hint Resolve scoping_rename : scoping.

(*********************************************************************************)
(** *** Scoping for substitutions. *)
(*********************************************************************************)

(** [sscoping Γ s Δ] states that [s] takes inputs in [Δ] and has outputs in [Γ]. *)
Inductive sscoping (Γ : scope) : subst -> scope -> Prop :=
| sscoping_nil s : sscoping Γ s []
| sscoping_cons Δ s m :
    sscoping Γ (scomp sshift s) Δ ->
    scoping Γ (s 0) m ->
    sscoping Γ s (m :: Δ).

#[export] Instance sscoping_proper : 
  Proper (eq ==> point_eq ==> eq ==> iff) sscoping.
Proof.
intros ? Γ -> s1 s2 Hs ? t ->. split ; intros H.
- induction H in s2, Hs |- * ; constructor.
  + apply IHsscoping. now apply congr_scomp.
  + now rewrite <-Hs.    
- induction H in s1, Hs |- * ; constructor.
  + apply IHsscoping. now apply congr_scomp.
  + now rewrite Hs.    
Qed.

(** Trigger [rasimpl] on [sscoping]. *)
Lemma rasimpl_trigger_sscoping Γ s1 s2 Δ :
  SubstSimplification s1 s2 ->
    sscoping Γ s1 Δ <-> sscoping Γ s2 Δ.
Proof. intros H. now rewrite subst_simplification. Qed.
#[export] Hint Rewrite -> rasimpl_trigger_sscoping : asimpl_outermost.

Lemma sscoping_sshift_r Γ Δ s m :
  sscoping Γ s Δ -> sscoping (m :: Γ) (scomp s sshift) Δ.
Proof.
intros H. induction H.
- constructor.
- constructor.
  + assumption.
  + eapply_eq scoping_rename. (*eapply_eq scoping_rename. Unshelve. 5: exact rshift.
    * 

    
  assert (scomp s sshift 0 = rename rshift (s 0)) as -> by now rasimpl. 
    eapply scoping_rename ; eauto with scoping.
Qed.*)
Admitted.
#[export] Hint Resolve sscoping_sshift_r : scoping.

(** Substituting preserves the scope. *)
Lemma scoping_substitute Γ Δ s t m :
  sscoping Γ s Δ ->
  scoping Δ t m ->
  scoping Γ (substitute s t) m.
Proof.
intros Hs Ht.
induction Ht in Γ, s, Hs |- *.
all: rasimpl.
all: try solve [ econstructor ; eauto ].
- induction Hs in i, H |- *.
  + now destruct i.
  + destruct i ; cbn in *.
    * depelim H. assumption.
    * apply IHHs. assumption.   
- constructor.
  apply IHHt. constructor.
  + rasimpl. now apply sscoping_sshift_r. 
  + rasimpl. constructor. reflexivity.
- constructor.
  + eauto.
  + apply IHHt2. constructor.
    * rasimpl. now apply sscoping_sshift_r. 
    * rasimpl. constructor. reflexivity.
- constructor. apply IHHt. constructor.
  + rasimpl. now apply sscoping_sshift_r.
  + rasimpl. constructor. reflexivity.   
Qed.
#[export] Hint Resolve scoping_substitute : scoping.

Lemma sscoping_sid Γ :
  sscoping Γ sid Γ.
Proof.
induction Γ.
- constructor.
- constructor. 
  + rasimpl. apply sscoping_sshift_r with (m := a) in IHΓ. rasimpl in IHΓ. assumption.
  + rasimpl. constructor. reflexivity.
Qed.      
#[export] Hint Resolve sscoping_sid : scoping.

Lemma sscoping_up_subst Γ Δ m s :
  sscoping Γ s Δ ->
  sscoping (m :: Γ) (up_subst s) (m :: Δ).
Proof.
intros H. constructor.
- rasimpl. eauto with scoping.
- rasimpl. now constructor.
Qed.
#[export] Hint Resolve sscoping_up_subst : scoping.

Lemma sscoping_sextend Γ t m : 
  scoping Γ t m ->
  sscoping Γ (scons t sid) (m :: Γ).
Proof.
intros H. constructor.
- rasimpl. apply sscoping_sid.
- rasimpl. assumption.
Qed.  
#[export] Hint Resolve sscoping_sextend : scoping.

Lemma scoping_strengthening Γ m t mt : 
  scoping (m :: Γ) (rename rshift t) mt ->
  scoping Γ t mt.
Proof. Admitted.
(** Looks annoying to prove... *)

(*********************************************************************************)
(** *** Notations. *)
(*********************************************************************************)

Declare Scope asubst_scope.
Delimit Scope asubst_scope with asub.

Notation "s [ sigma ]" := (substitute sigma s) 
  (at level 7, left associativity, format "s [ sigma ]") : asubst_scope.
Notation "s '..'" := (scons s sid) 
  (at level 1, format "s ..") : asubst_scope.

Open Scope asubst_scope.

(*********************************************************************************)
(** *** Call by value reduction. *)
(*********************************************************************************)

Inductive eval : tm -> vl -> Prop :=
| eval_app (A : ty) (s t u : tm) (v1 v2 : vl) :
    eval s (lam A u) -> eval t v1 -> eval u[v1..] v2 ->
    eval (app s t) v2
| eval_tapp (A : ty) (s u : tm) (v : vl) :
    eval s (tlam u) -> eval u[A..] v ->
    eval (tapp s A) v
| eval_val (v : vl) :
    eval (vt v) v.
Hint Resolve eval_val : core.

(** Evaluation preserves scoping. *)
Lemma eval_scoping Γ t v : 
  eval t v ->
  scoping Γ t Stm ->
  scoping Γ v Svl.
Proof.
intros He Hs. induction He in Γ, Hs |- .
- apply IHHe3. depelim Hs. specialize (IHHe1 Γ Hs1). specialize (IHHe2 Γ Hs2).
  depelim IHHe1. eapply scoping_substitute ; [|eassumption]. eauto with scoping.
- apply IHHe2. depelim Hs. specialize (IHHe1 _ Hs1).
   eapply scoping_substitute.
   + eapply sscoping_sextend. eassumption.
   + depelim IHHe1. assumption.
- depelim Hs. assumption.
Qed. 

(*********************************************************************************)
(** *** Typing Contexts. *)
(*********************************************************************************)

(** [liftn n t] lifts free variables of [t] by [n]. *)
Fixpoint liftn (n : nat) (t : expr) : expr :=
  match n with 
  | 0 => t
  | S n => rename rshift (liftn n t)
  end. 

(** A context declaration. *)
Inductive ctx_decl :=
  | TyDecl (* Declare a new type. *)
  | VlDecl (ty : expr) (* Declare a new value with given type. *).

Derive NoConfusion for ctx_decl.

(** A typing context. *)
Definition ctx := list ctx_decl.

(** The empty context. *)
Notation "'∙'" := (@nil ctx_decl).

(** Extend a context with a type declaration. *)
Notation "C ,, *" := (@cons ctx_decl TyDecl C) 
  (at level 20).

(** Extend a context with a type declaration. *)
Notation "C ,, ty" := (@cons ctx_decl (VlDecl ty) C) 
  (at level 20, ty at next level).

(** Concatenate contexts. *)
Notation "Γ ,,, Δ" := (@app ctx_decl Δ Γ) 
  (at level 25, Δ at next level, left associativity).

(** The sort of a bound variable which is described by a context declaration. *)
Definition sort_of_ctx_decl (d : ctx_decl) : sort :=
  match d with 
  | TyDecl => Sty 
  | VlDecl _ => Svl
  end.

(** The scope associated to a context. *)
Definition scope_of_ctx (c : ctx) : scope :=
  map sort_of_ctx_decl c.

Notation "⌜ C ⌝" := (scope_of_ctx C) (format "⌜ C ⌝").

(** Well-formedness of typing contexts. *)
Inductive wf_ctx : ctx -> Prop :=
| wf_ctx_empty : wf_ctx ∙
| wf_ctx_ty C : wf_ctx C -> wf_ctx (C ,, *)
| wf_ctx_vl C A : wf_ctx C -> scoping ⌜C⌝ A Sty -> wf_ctx (C ,, A).

(** Well-formed contexts contain only well-scoped types. *)
Lemma wf_ctx_lookup C i A :
  wf_ctx C ->
  nth_error C i = Some (VlDecl A) ->
  scoping ⌜C⌝ (liftn (S i) A) Sty.
Proof.
intros Hc H. induction Hc in i, A, H |- .
- rewrite nth_error_nil in H. depelim H.
- destruct i ; cbn in H.
  + depelim H.
  + specialize (IHHc _ _ H). eapply scoping_rename ; [|eassumption].
    apply rscoping_rshift.
- destruct i ; cbn in H.
  + depelim H. eapply scoping_rename ; [|eassumption]. apply rscoping_rshift.
  + specialize (IHHc _ _ H). eapply scoping_rename ; [|eassumption].
    apply rscoping_rshift.
Qed.

(*********************************************************************************)
(** *** Typing judgement. *)
(*********************************************************************************)

Unset Elimination Schemes.

(** Typing for terms. *)
Inductive typing_tm : ctx -> tm -> ty -> Prop :=

| typing_app C (A B : ty) (t1 t2 : tm) :
    typing_tm C t1 (arr A B) ->
    typing_tm C t2 A ->
    typing_tm C (app t1 t2) B

| typing_tapp C (A B : ty) (t : tm) :
    scoping ⌜C⌝ B Sty ->
    typing_tm C t (all A) ->
    typing_tm C (tapp t B) A[B..]

| typing_vt C (A : ty) (v : vl) :
    typing_vl C v A ->
    typing_tm C (vt v) A

(** Typing for values. *)
with typing_vl : ctx -> vl -> ty -> Prop :=

| typing_var C (A : ty) (i : nat) :
    nth_error C i = Some (VlDecl A) -> 
    typing_vl C (var i) (liftn (S i) A)
 
| typing_lam C (A B : ty) (t : tm) :
    scoping ⌜C⌝ A Sty ->
    typing_tm (C ,, A) t (rename rshift B) ->
    typing_vl C (lam A t) (arr A B)

| typing_tlam C (A : ty) (t : tm) :
    typing_tm (C ,, *) t A ->
    typing_vl C (tlam t) (all A).

Set Elimination Schemes.

Scheme typing_tm_ind := Minimality for typing_tm Sort Prop 
  with typing_vl_ind := Minimality for typing_vl Sort Prop.
Combined Scheme typing_tm_vl_ind from typing_tm_ind, typing_vl_ind.

Derive Signature for typing_tm typing_vl.

(** In a typing judgement [typing C t A], both [T] and [A] are well scoped
    (under the hypothesis that [C] itself is well scoped). *)
Lemma typing_scoping_aux :
  (forall C t A, typing_tm C t A -> wf_ctx C -> scoping ⌜C⌝ t Stm /\ scoping ⌜C⌝ A Sty) /\
  (forall C v A, typing_vl C v A -> wf_ctx C -> scoping ⌜C⌝ v Svl /\ scoping ⌜C⌝ A Sty).
Proof.
apply typing_tm_vl_ind ; intros.
- destruct (H2 H3). destruct (H0 H3). depelim H7. split ; [constructor|] ; assumption.
- destruct (H1 H2). split ; [constructor|] ; try assumption.
  depelim H4. eapply scoping_substitute ; [|eassumption]. apply sscoping_sextend. 
  assumption.
- destruct (H0 H1). split ; [constructor|] ; assumption.
- split.
  + constructor. unfold scope_of_ctx. erewrite map_nth_error by eassumption. reflexivity.
  + now apply wf_ctx_lookup.
- feed H1. { constructor ; assumption. } destruct H1. split.
  + constructor ; assumption.
  + constructor ; try assumption. apply scoping_strengthening in H4. assumption.
- feed H0. { constructor. assumption. } destruct H0. split.
  + constructor. assumption.
  + constructor. assumption.
Qed.

(*********************************************************************************)
(** *** Preservation. *)
(*********************************************************************************)

Definition rtyping (C1 : ctx) (r : ren) (C2 : ctx) : Prop :=
  forall i di,
    nth_error C2 i = Some di ->
    nth_error C1 (r i) = Some di.

Lemma rtyping_rid C :
  rtyping C rid C.
Proof. intros i di Hi. assumption. Qed.

Lemma rtyping_rshift C d :
  rtyping (d :: C) rshift C.
Proof. intros i di Hi. cbn. assumption. Qed.

Lemma rtyping_rcons C1 i di r C2 :
  nth_error C1 i = Some di ->
  rtyping C1 r C2 ->
  rtyping C1 (rcons i r) (di :: C2).
Proof.
intros H1 H2 j dj Hj. destruct j ; cbn in *.
- depelim Hj. assumption.
- apply H2. assumption.
Qed.

Lemma rtyping_up_ren C1 r d C2 : 
  rtyping C1 r C2 ->
  rtyping (d :: C1) (up_ren r) (d :: C2).
Proof.
intros H i di Hi. destruct i ; cbn in *.
- now depelim Hi.
- apply H. assumption.
Qed.

(** Typing is stable under renaming. *)
Lemma typing_rcons : 
  (forall C t A, typing_tm C t A -> forall C' r, rtyping C' r C -> typing_tm C' (rename r t) (rename r A)) /\
  (forall C v A, typing_vl C v A -> forall C' r, rtyping C' r C -> typing_vl C' (rename r v) (rename r A)).
Proof.
apply typing_tm_vl_ind ; intros.
- specialize (H0 _ _ H3). specialize (H2 _ _ H3). rasimpl. eapply typing_app ; eassumption.
- specialize (H1 _ _ H2). rasimpl. eapply typing_tapp.

(*

typing_

*)

(** Typing is stable under _value_ substitution. *)
Lemma typing_substitute_vl C t v A B : 
  typing_tm (C ,, A) t (rename rshift B) -> 
  typing_vl C v A ->
  typing_tm C t[v..] B.
Proof.


Admitted.

(** Typing is stable under _type_ substitution. *)
Lemma typing_substitute_ty C t T B : 
  typing_tm (C ,, *) t B -> 
  scoping ⌜C⌝ T Sty ->
  typing_tm C t[T..] B[T..].
Proof.
intros H1. revert T. induction H1 using typing_tm_ind with (P0 := _).
all: intros.
- rasimpl. eapply typing_app.
  + now apply IHtyping_tm1.
  + now apply IHtyping_tm2.  
- assert ((tapp s B)[T..] = tapp s[T..] B[T..]) as -> by now rasimpl.
  rasimpl.
  apply typing_tapp.



(** Preservation a.k.a. subject reduction. *)
Lemma preservation C t v A :
  eval t v -> 
  typing_tm C t A -> 
  typing_vl C v A.
Proof.
intros H Ht. induction H in C, A, Ht |- .
- apply IHeval3. depelim Ht. specialize (IHeval1 _ _ Ht1). specialize (IHeval2 _ _ Ht2).
  depelim IHeval1. eapply typing_substitute_vl ; eassumption.
- apply IHeval2. depelim Ht. specialize (IHeval1 _ _ Ht). depelim IHeval1.
  eapply typing_substitute_ty ; eassumption.
- now depelim Ht.
Qed. 

(*********************************************************************************)
(** *** Semantic typing. *)
(*********************************************************************************)

(** [L P s] means that [s] reduces to a value which satisfies [P]. *)
Definition L (P : vl -> Prop) (s : tm) : Prop :=
  exists2 v, eval s v & P v.

Definition fcons {A} (x : A) (f : nat -> A) : nat -> A :=
  fun n =>
    match n with 
    | 0 => x
    | S n => f n 
    end.

Fixpoint V (A : ty) (rho : nat -> vl -> Prop) (v : vl) {struct A} : Prop :=
  match A with
  | var X => rho X v
  | arr A B =>
    match v with
    | lam C t => forall u, V A rho u -> L (V B rho) t[u..]
    | _ => False
    end
  | all A =>
    match v with
    | tlam t => forall i (B : ty), L (V A (fcons i rho)) t[B..]
    | _ => False
    end
  | _ => False
  end.

Notation E A rho := (L (V A rho)).

Lemma V_ren (A : ty) (rho : nat -> vl -> Prop) (xi : -> ) :
  V A.[ren xi] rho = V A (xi >>> rho).








Lemma V_weak (A : ty) d rho :
V A.[ren (+1)] (d .: rho) = V A rho.

Lemma V_subst (A : ty) rho sigma :
V A.[sigma] rho = V A (fun x => V (sigma x) rho).









Lemma E_subst1 (A B : ty) rho :
E A.[B .: var_ty] rho = E A (V B rho .: rho).



Definition VG (Gamma : ctx) (rho : index -> vl -> Prop) (sigma : index -> vl) :=
forall x, x < size Gamma -> V Gamma`_x rho (sigma x).

Theorem soundness (Gamma : ctx) :
(forall (s : tm) (A : ty), tm_ty Gamma s A ->
  forall sigma tau rho, VG Gamma rho tau -> E A rho s.[sigma,tau]) /\
(forall (v : vl) (A : ty), vl_ty Gamma v A ->
  forall sigma tau rho, VG Gamma rho tau -> V A rho v.[sigma,tau]).

