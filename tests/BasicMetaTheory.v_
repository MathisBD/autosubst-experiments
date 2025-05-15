(** Basic meta-theory before building the model **)

From Coq Require Import Utf8 List.
From GhostTT Require Import Util GAST BasicAST SubstNotations ContextDecl CastRemoval
  TermMode Scoping Typing.
From Coq Require Import Setoid Morphisms Relation_Definitions.
From Equations Require Import Equations.

Import ListNotations.

Set Default Goal Selector "!".

(** Substitution preserves modes **)

Definition rscoping (Γ : scope) (ρ : ren) (Δ : scope) : Prop :=
  ∀ x m,
    nth_error Δ x = Some m →
    nth_error Γ (ρ x) = Some m.

Inductive sscoping (Γ : scope) (σ : subst) : scope → Prop :=
| scope_nil : sscoping Γ σ []
| scope_cons :
    ∀ Δ m,
      sscoping Γ (↑ >> σ) Δ →
      scoping Γ (σ 0) m →
      sscoping Γ σ (m :: Δ).

Lemma rscoping_S :
  ∀ Γ m,
    rscoping (m :: Γ) S Γ.
Proof.
  intros Γ m. intros x mx e.
  cbn. assumption.
Qed.

Lemma rscoping_shift :
  ∀ Γ Δ ρ mx,
    rscoping Γ ρ Δ →
    rscoping (mx :: Γ) (0 .:ᵣ ρ >>ᵣ S) (mx :: Δ).
Proof.
  intros ? ? ? mx h' y my e.
  destruct y.
  - simpl in *. assumption.
  - simpl in *. apply h'. assumption.
Qed.

Lemma scoping_ren :
  ∀ Γ Δ ρ t m,
    rscoping Γ ρ Δ →
    scoping Δ t m →
    scoping Γ (rename ρ t) m.
Proof.
  intros Γ Δ ρ t m hρ ht.
  pose proof rscoping_shift as lem.
  induction ht in Γ, ρ, hρ, lem |- *.
  all: solve [ rasimpl ; econstructor ; eauto ].
Qed.

Lemma sscoping_weak :
  ∀ Γ Δ σ m,
    sscoping Γ σ Δ →
    sscoping (m :: Γ) (srcomp σ rshift) Δ.
Proof.
  intros Γ Δ σ m h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + eapply scoping_ren. 2: eassumption. apply rscoping_S.
Qed.

Lemma scoping_subst :
  ∀ Γ Δ σ t m,
    sscoping Γ σ Δ →
    scoping Δ t m →
    scoping Γ (t <[ σ ]) m.
Proof.
  intros Γ Δ σ t m hσ ht.
  induction ht in Γ, σ, hσ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ].
  - rename H into hx, Γ0 into Δ. induction hσ in x, hx |- *. 1: destruct x ; discriminate.
    destruct x.
    + simpl in *. inversion hx. subst. assumption.
    + apply IHhσ. simpl in hx. assumption.
  - rasimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * rasimpl. apply sscoping_weak. assumption.
      * rasimpl. constructor. reflexivity.
  - rasimpl. constructor.
    + eauto.
    + apply IHht2. constructor.
      * rasimpl. apply sscoping_weak. assumption.
      * rasimpl. constructor. reflexivity.
Qed.

Lemma sscoping_shift :
  ∀ Γ Δ mx σ,
    sscoping Γ σ Δ →
    sscoping (mx :: Γ) (var 0 .: σ >> ren1 S) (mx :: Δ).
Proof.
  intros Γ Δ mx σ h.
  constructor.
  - rasimpl. apply sscoping_weak. assumption.
  - rasimpl. constructor. reflexivity.
Qed.

#[export] Instance rscoping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) rscoping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n m en. rewrite <- e. apply h. assumption.
Qed.

Lemma autosubst_simpl_rscoping :
  ∀ Γ Δ r s,
    RenSimplification r s →
    rscoping Γ r Δ ↔ rscoping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply rscoping_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_rscoping : rasimpl_outermost.

#[export] Instance sscoping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) sscoping.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ih ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_sscoping :
  ∀ Γ Δ r s,
    SubstSimplification r s →
    sscoping Γ r Δ ↔ sscoping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply sscoping_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_sscoping : rasimpl_outermost.

Lemma sscoping_ids :
  ∀ Γ,
    sscoping Γ ids Γ.
Proof.
  intros Γ. induction Γ as [| m Γ ih].
  - constructor.
  - constructor.
    + eapply sscoping_weak with (m := m) in ih. rasimpl in ih. assumption.
    + constructor. reflexivity.
Qed.

Lemma sscoping_one :
  ∀ Γ u mx,
    scoping Γ u mx →
    sscoping Γ u.. (mx :: Γ).
Proof.
  intros Γ u mx h.
  constructor.
  - rasimpl. apply sscoping_ids.
  - rasimpl. assumption.
Qed.

(** Cast removal preserves modes **)

Lemma scoping_castrm :
  ∀ Γ t m,
    scoping Γ t m →
    scoping Γ (castrm t) m.
Proof.
  intros Γ t m h.
  induction h.
  all: try solve [ simpl ; econstructor ; eauto ].
  cbn. assumption.
Qed.

Lemma md_castrm :
  ∀ Γ t,
    md Γ t = md Γ (castrm t).
Proof.
  intros Γ t.
  induction t in Γ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  cbn. rewrite <- IHt3. destruct md. all: reflexivity.
Qed.

(** Cast removal commutes with renamings **)

Lemma castrm_ren :
  ∀ t ρ,
    ε| ρ ⋅ t | = ρ ⋅ ε| t |.
Proof.
  intros t ρ.
  induction t in ρ |- *.
  all: try reflexivity.
  all: solve [ simpl ; rasimpl ; repeat core.unfold_funcomp ; f_equal ; auto ].
Qed.

(** Cast removal commutes with substitution **)

Lemma castrm_subst :
  ∀ t σ,
    ε| t <[ σ ] | = ε| t | <[ σ >> castrm ].
Proof.
  intros t σ.
  assert (∀ σ t,
    t <[ (var 0 .: σ >> ren1 ↑) >> castrm] =
    t <[ var 0 .: σ >> (castrm >> ren1 ↑) ]
  ).
  { intros θ u.
    apply ext_term. intros n.
    destruct n.
    - rasimpl. repeat core.unfold_funcomp. simpl. reflexivity.
    - rasimpl. repeat core.unfold_funcomp. simpl.
      apply castrm_ren.
  }
  induction t in σ |- *. all: try reflexivity.
  all: try solve [ rasimpl ; repeat core.unfold_funcomp ; simpl ; f_equal ; auto ].
  - rasimpl. repeat core.unfold_funcomp. simpl. f_equal. 1: auto.
    rasimpl. repeat core.unfold_funcomp. rewrite IHt2.
    auto.
  - rasimpl. repeat core.unfold_funcomp. simpl. f_equal. 1: auto.
    rasimpl. repeat core.unfold_funcomp. rewrite IHt2.
    auto.
Qed.

(** Inversion for scoping **)

Lemma scope_app_inv :
  ∀ Γ u v m,
    scoping Γ (app u v) m →
    ∃ mx,
      scoping Γ u m ∧
      scoping Γ v mx.
Proof.
  intros Γ u v m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_lam_inv :
  ∀ Γ mx A t m,
    scoping Γ (lam mx A t) m →
    scoping Γ A mKind ∧
    scoping (mx :: Γ) t m.
Proof.
  intros Γ mx A t m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_reveal_inv :
  ∀ Γ t P p m,
    scoping Γ (reveal t P p) m →
    In m [ mProp ; mGhost ] ∧
    scoping Γ t mGhost ∧
    scoping Γ P mKind ∧
    scoping Γ p m.
Proof.
  intros Γ t P p m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_Reveal_inv :
  ∀ Γ t p m,
    scoping Γ (Reveal t p) m →
    scoping Γ t mGhost ∧
    scoping Γ p mKind ∧
    m = mKind.
Proof.
  intros Γ t p m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_toRev_inv :
  ∀ Γ t p u m,
    scoping Γ (toRev t p u) m →
    scoping Γ t mType ∧
    scoping Γ p mKind ∧
    scoping Γ u mProp ∧
    m = mProp.
Proof.
  intros Γ t p u m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_fromRev_inv :
  ∀ Γ t p u m,
    scoping Γ (fromRev t p u) m →
    scoping Γ t mType ∧
    scoping Γ p mKind ∧
    scoping Γ u mProp ∧
    m = mProp.
Proof.
  intros Γ t p u m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_sort_inv :
  ∀ Γ ms i m,
    scoping Γ (Sort ms i) m →
    m = mKind.
Proof.
  intros Γ ms i m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_pi_inv :
  ∀ Γ i j mx m A B m',
    scoping Γ (Pi i j m mx A B) m' →
    scoping Γ A mKind ∧
    scoping (mx :: Γ) B mKind ∧
    m' = mKind.
Proof.
  intros Γ i j mx m A B m' h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_erased_inv :
  ∀ Γ A m,
    scoping Γ (Erased A) m →
    scoping Γ A mKind ∧
    m = mKind.
Proof.
  intros Γ A m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_hide_inv :
  ∀ Γ t m,
    scoping Γ (hide t) m →
    scoping Γ t mType ∧
    m = mGhost.
Proof.
  intros Γ t m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_gheq_inv :
  ∀ Γ A u v m,
    scoping Γ (gheq A u v) m →
    scoping Γ A mKind ∧
    scoping Γ u mGhost ∧
    scoping Γ v mGhost ∧
    m = mKind.
Proof.
  intros Γ A u v m h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_if_inv :
  ∀ Γ m b P t f m',
    scoping Γ (tif m b P t f) m' →
    scoping Γ b mType ∧
    scoping Γ P mKind ∧
    scoping Γ t m ∧
    scoping Γ f m ∧
    m' = m.
Proof.
  intros Γ m b P t f m' h.
  inversion h. subst.
  intuition eauto.
Qed.

Lemma scope_bot_elim_inv :
  ∀ Γ m A p m',
    scoping Γ (bot_elim m A p) m' →
    scoping Γ A mKind ∧
    scoping Γ p mProp ∧
    m' = m.
Proof.
  intros Γ m A p m' h.
  inversion h. subst.
  intuition eauto.
Qed.

Ltac scoping_fun :=
  match goal with
  | h : scoping ?Γ ?t ?m, h' : scoping ?Γ ?t ?m' |- _ =>
    assert (m = m') ; [
      eapply scoping_functional ; eassumption
    | first [ subst m' ; clear h' | subst m ; clear h ]
    ]
  end.

(** Scoping of top **)

Lemma scope_top :
  ∀ Γ,
    scoping Γ top mKind.
Proof.
  intros Γ. constructor. all: constructor.
Qed.

(** Conversion entails mode equality **)

Definition rscoping_comp (Γ : scope) ρ (Δ : scope) :=
  ∀ x,
    nth_error Δ x = None →
    nth_error Γ (ρ x) = None.

Definition sscoping_comp (Γ : scope) σ (Δ : scope) :=
  ∀ n,
    nth_error Δ n = None →
    ∃ m,
      σ n = var m ∧
      nth_error Γ m = None.

Lemma sscoping_comp_shift :
  ∀ Γ Δ σ mx,
    sscoping_comp Γ σ Δ →
    sscoping_comp (mx :: Γ) (up_term σ) (mx :: Δ).
Proof.
  intros Γ Δ σ mx h. intros n e.
  destruct n.
  - cbn in e. discriminate.
  - cbn in e. cbn.
    eapply h in e as e'. destruct e' as [m [e1 e2]].
    unfold core.funcomp. exists (S m). intuition eauto.
    rewrite e1. rasimpl. reflexivity.
Qed.

Lemma rscoping_comp_S :
  ∀ Γ m,
    rscoping_comp (m :: Γ) S Γ.
Proof.
  intros Γ m. intros n e. cbn. assumption.
Qed.

Lemma nth_nth_error :
  ∀ A (l : list A) (d : A) n,
    nth n l d = match nth_error l n with Some x => x | None => d end.
Proof.
  intros A l d n.
  induction l in n |- *.
  - cbn. destruct n. all: reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. apply IHl.
Qed.

Lemma rscoping_comp_upren :
  ∀ Γ Δ m ρ,
    rscoping_comp Γ ρ Δ →
    rscoping_comp (m :: Γ) (up_ren ρ) (m :: Δ).
Proof.
  intros Γ Δ m ρ h. intros x e.
  destruct x.
  - cbn in *. assumption.
  - cbn in *. apply h. assumption.
Qed.

Lemma md_ren :
  ∀ Γ Δ ρ t,
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    md Γ (ρ ⋅ t) = md Δ t.
Proof.
  intros Γ Δ ρ t hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  - cbn. rewrite 2!nth_nth_error.
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e. rewrite e. reflexivity.
    + eapply hcρ in e. rewrite e. reflexivity.
  - cbn. eapply IHt2.
    + eapply rscoping_shift. assumption.
    + eapply rscoping_comp_upren. assumption.
  - cbn. erewrite IHt3. 2,3: eauto.
    reflexivity.
Qed.

Lemma md_subst :
  ∀ Γ Δ σ t,
    sscoping Γ σ Δ →
    sscoping_comp Γ σ Δ →
    md Γ (t <[ σ ]) = md Δ t.
Proof.
  intros Γ Δ σ t hσ hcσ.
  induction t in Γ, Δ, σ, hσ, hcσ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  - cbn. rewrite nth_nth_error.
    destruct (nth_error Δ n) eqn:e.
    + clear hcσ. induction hσ as [| σ Δ mx hσ ih hm] in n, m, e |- *.
      1: destruct n ; discriminate.
      destruct n.
      * cbn in *. noconf e.
        erewrite scoping_md. 2: eassumption. reflexivity.
      * cbn in e. eapply ih. assumption.
    + eapply hcσ in e. destruct e as [m [e1 e2]].
      rewrite e1. cbn. rewrite nth_nth_error. rewrite e2. reflexivity.
  - cbn. eapply IHt2.
    + eapply sscoping_shift. assumption.
    + eapply sscoping_comp_shift. assumption.
  - cbn. erewrite IHt3. 2,3: eauto.
    reflexivity.
Qed.

Lemma sscoping_comp_one :
  ∀ Γ u mx,
    sscoping_comp Γ u.. (mx :: Γ).
Proof.
  intros Γ u mx. intros n e.
  destruct n.
  - cbn in e. discriminate.
  - cbn in e. cbn. eexists. intuition eauto.
Qed.

Lemma conv_md :
  ∀ Γ u v,
    Γ ⊢ u ≡ v →
    mdc Γ u = mdc Γ v.
Proof.
  intros Γ u v h.
  induction h.
  all: try solve [ cbn ; reflexivity ].
  all: try solve [ cbn ; eauto ].
  - cbn. erewrite md_subst.
    2: eapply sscoping_one ; eassumption.
    2: eapply sscoping_comp_one.
    reflexivity.
  - cbn. erewrite scoping_md. 2: eassumption.
    cbn in H2. destruct H2 as [| []]. 3: contradiction.
    all: subst. all: reflexivity.
  - cbn. erewrite scoping_md. 2: eassumption.
    reflexivity.
  - cbn. erewrite scoping_md. 2: eassumption.
    reflexivity.
  - cbn. erewrite scoping_md. 2: eassumption.
    reflexivity.
  - cbn. erewrite scoping_md. 2: eassumption.
    reflexivity.
  - cbn. erewrite scoping_md. 2: eassumption.
    reflexivity.
  - cbn. erewrite scoping_md. 2: eassumption.
    reflexivity.
  - cbn. rewrite IHh3. reflexivity.
  - etransitivity. all: eassumption.
  - erewrite 2!scoping_md. 2,3: eassumption.
    reflexivity.
Qed.

(** Renaming preserves typing **)

Definition rtyping (Γ : context) (ρ : nat → nat) (Δ : context) : Prop :=
  ∀ x m A,
    nth_error Δ x = Some (m, A) →
    ∃ B,
      nth_error Γ (ρ x) = Some (m, B) ∧
      (plus (S x) >> ρ) ⋅ A = (plus (S (ρ x))) ⋅ B.

#[export] Instance rtyping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) rtyping.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  intros n m A en. rewrite <- e.
  eapply h in en as [B [en eB]].
  eexists. split. 1: eassumption.
  rasimpl. rasimpl in eB. rewrite <- eB.
  apply extRen_term. intro x. cbn. core.unfold_funcomp.
  rewrite <- e. reflexivity.
Qed.

Lemma autosubst_simpl_rtyping :
  ∀ Γ Δ r s,
    RenSimplification r s →
    rtyping Γ r Δ ↔ rtyping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply rtyping_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_rtyping : rasimpl_outermost.

Lemma rtyping_scoping :
  ∀ Γ Δ ρ,
    rtyping Γ ρ Δ →
    rscoping (sc Γ) ρ (sc Δ).
Proof.
  intros Γ Δ ρ h.
  intros n m e. unfold sc in e. rewrite nth_error_map in e.
  destruct (nth_error Δ n) as [[]|] eqn:en. 2: discriminate.
  simpl in e. inversion e. subst. clear e.
  eapply h in en. destruct en as [B [en eB]].
  unfold sc. rewrite nth_error_map.
  rewrite en. reflexivity.
Qed.

Lemma rtyping_shift :
  ∀ Γ Δ mx A ρ,
    rtyping Γ ρ Δ →
    rtyping (Γ ,, (mx, ρ ⋅ A)) (0 .: ρ >> S) (Δ,, (mx, A)).
Proof.
  intros Γ Δ mx A ρ hρ.
  intros y my B hy.
  destruct y.
  - cbn in *. inversion hy. eexists.
    split. 1: reflexivity.
    rasimpl. reflexivity.
  - cbn in *. eapply hρ in hy. destruct hy as [C [en eC]].
    eexists. split. 1: eassumption.
    rasimpl.
    apply (f_equal (λ t, S ⋅ t)) in eC. rasimpl in eC.
    assumption.
Qed.

Lemma rtyping_S :
  ∀ Γ m A,
    rtyping (Γ ,, (m, A)) S Γ.
Proof.
  intros Γ m A. intros x mx B e.
  simpl. rasimpl.
  eexists. split. 1: eassumption.
  rasimpl. reflexivity.
Qed.

Lemma rscoping_sscoping :
  ∀ Γ Δ ρ,
    rscoping Γ ρ Δ →
    sscoping Γ (ρ >> var) Δ.
Proof.
  intros Γ Δ ρ h.
  induction Δ as [| m Δ ih] in ρ, h |- *.
  - constructor.
  - constructor.
    + apply ih. rasimpl.
      intros x mx e.
      apply h. cbn. assumption.
    + constructor. apply h. reflexivity.
Qed.

Lemma meta_conv :
  ∀ Γ t A B,
    Γ ⊢ t : A →
    A = B →
    Γ ⊢ t : B.
Proof.
  intros Γ t A B h ->. assumption.
Qed.

Lemma meta_conv_trans_l :
  ∀ Γ u v w,
    u = v →
    Γ ⊢ v ≡ w →
    Γ ⊢ u ≡ w.
Proof.
  intros Γ ??? <- h. assumption.
Qed.

Lemma meta_conv_trans_r :
  ∀ Γ u v w,
    Γ ⊢ u ≡ v →
    v = w →
    Γ ⊢ u ≡ w.
Proof.
  intros Γ u v ? h <-. assumption.
Qed.

Lemma meta_conv_refl :
  ∀ Γ u v,
    u = v →
    Γ ⊢ u ≡ v.
Proof.
  intros Γ u ? <-. gconv.
Qed.

Ltac scoping_ren_finish :=
  eapply scoping_ren ; [| eassumption] ;
  try apply rscoping_shift ;
  apply rtyping_scoping ; assumption.

Lemma conv_ren :
  ∀ Γ Δ ρ u v,
    rtyping Γ ρ Δ →
    Δ ⊢ u ≡ v →
    Γ ⊢ ρ ⋅ u ≡ ρ ⋅ v.
Proof.
  intros Γ Δ ρ u v hρ h.
  induction h in Γ, ρ, hρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ; scoping_ren_finish ].
  - rasimpl. eapply meta_conv_trans_r. 1: econstructor.
    all: try scoping_ren_finish.
    rasimpl. reflexivity.
  - rasimpl. eapply conv_trans. 1: econstructor.
    all: try scoping_ren_finish. 1: auto.
    cbn. gconv.
    + rasimpl. gconv.
    + rasimpl. gconv.
  - constructor. all: auto.
    eapply IHh2. apply rtyping_shift. assumption.
  - rasimpl. constructor. 1: auto.
    eapply IHh2. apply rtyping_shift. assumption.
Qed.

Lemma typing_ren :
  ∀ Γ Δ ρ t A,
    rtyping Γ ρ Δ →
    Δ ⊢ t : A →
    Γ ⊢ ρ ⋅ t : ρ ⋅ A.
Proof.
  intros Γ Δ ρ t A hρ ht.
  induction ht in Γ, ρ, hρ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ; scoping_ren_finish ].
  - rasimpl. eapply hρ in H as [B [? eB]].
    rasimpl in eB. rewrite eB.
    econstructor. eassumption.
  - rasimpl. econstructor. all: eauto. all: try scoping_ren_finish.
    eapply IHht2. eapply rtyping_shift. assumption.
  - rasimpl. econstructor. all: eauto. all: try scoping_ren_finish.
    + eapply IHht2. eapply rtyping_shift. assumption.
    + eapply IHht3. eapply rtyping_shift. assumption.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht4.
    eapply meta_conv. 1: econstructor. all: eauto. all: try scoping_ren_finish.
    1:{ eapply IHht4. eapply rtyping_shift. assumption. }
    rasimpl. reflexivity.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht2. rasimpl in IHht3.
    econstructor. all: eauto. all: try scoping_ren_finish.
    eapply meta_conv. 1: apply IHht3. 1: auto.
    f_equal. f_equal. rasimpl. reflexivity.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht2. rasimpl in IHht3. rasimpl in IHht4.
    econstructor. all: eauto. all: scoping_ren_finish.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht2. rasimpl in IHht3. rasimpl in IHht4.
    econstructor. all: eauto. all: try scoping_ren_finish.
    eapply meta_conv. 1: apply IHht4. 1: auto.
    f_equal. rasimpl. reflexivity.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht2. rasimpl in IHht3. rasimpl in IHht4.
    rasimpl in IHht5. rasimpl in IHht6.
    econstructor. 8: eauto. all: eauto. all: try scoping_ren_finish.
    + eapply meta_conv. 1: eauto.
      f_equal. cbn. f_equal. f_equal. rasimpl. reflexivity.
    + eapply meta_conv. 1: eauto.
      f_equal. cbn. f_equal. rasimpl. reflexivity.
  - rasimpl. rasimpl in IHht2.
    econstructor. all: eauto. all: try scoping_ren_finish.
    rewrite 2!castrm_ren.
    eapply conv_ren. all: eassumption.
Qed.

(** Substitution preserves typing **)

Inductive styping (Γ : context) (σ : nat → term) : context → Prop :=
| type_nil : styping Γ σ []
| type_cons :
    ∀ Δ m A,
      styping Γ (↑ >> σ) Δ →
      cscoping Γ (σ 0) m →
      Γ ⊢ σ var_zero : A <[ S >> σ ] →
      styping Γ σ (Δ,, (m, A)).

#[export] Instance styping_morphism :
  Proper (eq ==> pointwise_relation _ eq ==> eq ==> iff) styping.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| ? ? ? ? ? ih ] in σ', e |- *.
  - constructor.
  - constructor.
    + apply ih. intros n. apply e.
    + rewrite <- e. assumption.
    + rewrite <- e. eapply meta_conv. 1: eassumption.
      rasimpl. apply ext_term.
      intro. apply e.
Qed.

Lemma autosubst_simpl_styping :
  ∀ Γ Δ r s,
    SubstSimplification r s →
    styping Γ r Δ ↔ styping Γ s Δ.
Proof.
  intros Γ Δ r s H.
  apply styping_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_styping : rasimpl_outermost.

Lemma styping_scoping :
  ∀ Γ Δ σ,
    styping Γ σ Δ →
    sscoping (sc Γ) σ (sc Δ).
Proof.
  intros Γ Δ σ h. induction h.
  - constructor.
  - cbn. constructor. all: assumption.
Qed.

Lemma styping_weak :
  ∀ Γ Δ σ mx A,
    styping Γ σ Δ →
    styping (Γ,, (mx, A)) (σ >> ren_term ↑) Δ.
Proof.
  intros Γ Δ σ mx A h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + eapply scoping_ren. 2: eassumption.
      apply rscoping_S.
    + rasimpl. eapply meta_conv.
      * eapply typing_ren. 2: eassumption.
        intros n ? ? e. rasimpl. cbn.
        eexists. split. 1: eassumption.
        reflexivity.
      * rasimpl. reflexivity.
Qed.

Lemma styping_shift :
  ∀ Γ Δ mx A σ,
    styping Γ σ Δ →
    styping (Γ ,, (mx, A <[ σ ])) (var 0 .: σ >> ren1 S) (Δ,, (mx, A)).
Proof.
  intros Γ Δ mx A σ h.
  constructor.
  - rasimpl. apply styping_weak. assumption.
  - rasimpl. constructor. reflexivity.
  - rasimpl. eapply meta_conv.
    + econstructor. cbn. reflexivity.
    + rasimpl. reflexivity.
Qed.

Lemma styping_ids :
  ∀ Γ,
    styping Γ ids Γ.
Proof.
  intros Γ. induction Γ as [| [m A] Γ ih].
  - constructor.
  - constructor.
    + eapply styping_weak with (mx := m) (A := A) in ih.
      rasimpl in ih. assumption.
    + constructor. reflexivity.
    + eapply meta_conv. 1: econstructor.
      * cbn. reflexivity.
      * rasimpl. substify. reflexivity.
Qed.

Lemma styping_one :
  ∀ Γ mx A u,
    cscoping Γ u mx →
    Γ ⊢ u : A →
    styping Γ u.. (Γ ,, (mx, A)).
Proof.
  intros Γ mx A u h hm.
  constructor. all: rasimpl. all: auto.
  apply styping_ids.
Qed.

Ltac scoping_subst_finish :=
  eapply scoping_subst ; [| eassumption] ;
  try apply sscoping_shift ;
  apply styping_scoping ; assumption.

Ltac conv_subst_finish :=
  eapply scoping_subst ; [| eassumption] ;
  try apply sscoping_shift ;
  assumption.

Lemma conv_subst :
  ∀ Γ Δ σ u v,
    sscoping (sc Γ) σ (sc Δ) →
    Δ ⊢ u ≡ v →
    Γ ⊢ u <[ σ ] ≡ v <[ σ ].
Proof.
  intros Γ Δ σ u v hσ h.
  induction h in Γ, σ, hσ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ; conv_subst_finish ].
  - rasimpl. eapply meta_conv_trans_r. 1: econstructor.
    all: try conv_subst_finish.
    rasimpl. apply ext_term.
    intros [].
    + rasimpl. reflexivity.
    + rasimpl. reflexivity.
  - cbn. rasimpl. eapply conv_trans.
    1:{ econstructor. all: try conv_subst_finish. assumption. }
    gconv.
    + rasimpl. gconv.
    + apply meta_conv_refl. f_equal. rasimpl.
      eapply ext_term. intro x.
      rasimpl. cbn. rasimpl. reflexivity.
  - rasimpl. constructor. all: auto.
    eapply IHh2. cbn. apply sscoping_shift. assumption.
  - rasimpl. constructor. 1: auto.
    eapply IHh2. cbn. apply sscoping_shift. assumption.
Qed.

Lemma sscoping_castrm :
  ∀ Γ σ Δ,
    sscoping Γ σ Δ →
    sscoping Γ (σ >> castrm) Δ.
Proof.
  intros Γ σ Δ h.
  induction h.
  - constructor.
  - constructor.
    + assumption.
    + rasimpl. eapply scoping_castrm. assumption.
Qed.

Lemma typing_subst :
  ∀ Γ Δ σ t A,
    styping Γ σ Δ →
    Δ ⊢ t : A →
    Γ ⊢ t <[ σ ] : A <[ σ ].
Proof.
  intros Γ Δ σ t A hσ ht.
  induction ht in Γ, σ, hσ |- *.
  all: try solve [ rasimpl ; econstructor ; eauto ; scoping_subst_finish ].
  - rasimpl.
    induction hσ in x, H |- *. 1: destruct x ; discriminate.
    destruct x.
    + cbn in H. inversion H. subst. assumption.
    + apply IHhσ. assumption.
  - rasimpl. econstructor. all: eauto. all: try scoping_subst_finish.
    eapply IHht2. eapply styping_shift. assumption.
  - rasimpl. econstructor. all: eauto. all: try scoping_subst_finish.
    + eapply IHht2. eapply styping_shift. assumption.
    + eapply IHht3. eapply styping_shift. assumption.
  - rasimpl. rasimpl in IHht1.
    eapply meta_conv. 1: econstructor.
    all: eauto. all: try scoping_subst_finish.
    1:{ eapply IHht4. eapply styping_shift. assumption. }
    rasimpl. apply ext_term. intros [].
    + rasimpl. reflexivity.
    + rasimpl. reflexivity.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht2. rasimpl in IHht3.
    econstructor. all: eauto. all: try scoping_subst_finish.
    eapply meta_conv. 1: apply IHht3. 1: auto.
    f_equal. f_equal. rasimpl. reflexivity.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht2. rasimpl in IHht3. rasimpl in IHht4.
    econstructor. all: eauto. all: scoping_subst_finish.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht2. rasimpl in IHht3. rasimpl in IHht4.
    econstructor. all: eauto. all: try scoping_subst_finish.
    eapply meta_conv. 1: apply IHht4. 1: auto.
    f_equal. rasimpl. reflexivity.
  - rasimpl. rasimpl in IHht1. rasimpl in IHht2. rasimpl in IHht3. rasimpl in IHht4.
    rasimpl in IHht5. rasimpl in IHht6.
    econstructor. 8: eauto. all: eauto. all: try scoping_subst_finish.
    + eapply meta_conv. 1: eauto.
      f_equal. cbn. f_equal. f_equal. rasimpl. reflexivity.
    + eapply meta_conv. 1: eauto.
      f_equal. cbn. f_equal. rasimpl. reflexivity.
  - rasimpl. rasimpl in IHht2.
    econstructor. all: eauto. all: try scoping_subst_finish.
    rewrite 2!castrm_subst.
    eapply conv_subst. 2: eassumption.
    apply sscoping_castrm. eapply styping_scoping. assumption.
Qed.

(** Inversion of typing **)

Set Equations With UIP.
Derive NoConfusion EqDec for mode.
Derive NoConfusion NoConfusionHom EqDec for term.
Derive Signature for typing.

Require Import Equations.Prop.DepElim.

Ltac destruct_exists h :=
  match type of h with
  | ∃ _, _ => destruct h as [? h] ; destruct_exists h
  | _ => idtac
  end.

Notation "Γ ⊢ u ε≡ v" :=
  (Γ ⊢ ε|u| ≡ ε|v|)
  (at level 80, u, v at next level, format "Γ  ⊢  u  ε≡  v").

Lemma type_var_inv :
  ∀ Γ x A,
    Γ ⊢ var x : A →
    ∃ m B,
      nth_error Γ x = Some (m, B) ∧
      Γ ⊢ (plus (S x)) ⋅ B ε≡ A.
Proof.
  intros Γ x A h.
  dependent induction h.
  - eexists _, _. split. 1: eassumption.
    constructor.
  - destruct_exists IHh1. intuition subst.
    eexists _, _. split. 1: eassumption.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_sort_inv :
  ∀ Γ m i A,
    Γ ⊢ Sort m i : A →
    Γ ⊢ Sort mKind (usup m i) ε≡ A.
Proof.
  intros ???? h.
  dependent induction h.
  - constructor.
  - eapply conv_trans. all: eauto.
Qed.

Lemma type_pi_inv :
  ∀ Γ i j mx m A B C,
    Γ ⊢ Pi i j m mx A B : C →
    cscoping Γ A mKind ∧
    cscoping (Γ ,, (mx, A)) B mKind ∧
    Γ ⊢ A : Sort mx i ∧
    Γ ,, (mx, A) ⊢ B : Sort m j ∧
    Γ ⊢ Sort m (umax mx m i j) ε≡ C.
Proof.
  intros ???????? h.
  dependent induction h.
  - intuition eauto. constructor.
  - intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_lam_inv :
  ∀ Γ mx A t C,
    Γ ⊢ lam mx A t : C →
    ∃ i j m B,
      cscoping Γ A mKind ∧
      cscoping (Γ ,, (mx, A)) B mKind ∧
      cscoping (Γ ,, (mx, A)) t m ∧
      Γ ⊢ A : Sort mx i ∧
      Γ ,, (mx, A) ⊢ B : Sort m j ∧
      Γ ,, (mx, A) ⊢ t : B ∧
      Γ ⊢ Pi i j m mx A B ε≡ C.
Proof.
  intros Γ mx A t C h.
  dependent induction h.
  - eexists _,_,_,_. intuition eauto.
    apply conv_refl.
  - destruct_exists IHh1. eexists _,_,_,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_app_inv :
  ∀ Γ t u C,
    Γ ⊢ app t u : C →
    ∃ mx m i j A B,
      cscoping (Γ ,, (mx, A)) B mKind ∧
      cscoping Γ t m ∧
      cscoping Γ u mx ∧
      cscoping Γ A mKind ∧
      Γ ⊢ t : Pi i j m mx A B ∧
      Γ ⊢ u : A ∧
      Γ ⊢ A : Sort mx i ∧
      Γ ,, (mx, A) ⊢ B : Sort m j ∧
      Γ ⊢ B <[ u .. ] ε≡ C.
Proof.
  intros Γ t u C h.
  dependent induction h.
  - eexists _,_,_,_,_,_. intuition eauto.
    apply conv_refl.
  - destruct_exists IHh1. eexists _,_,_,_,_,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_erased_inv :
  ∀ Γ A C,
    Γ ⊢ Erased A : C →
    ∃ i,
      cscoping Γ A mKind ∧
      Γ ⊢ A : Sort mType i ∧
      Γ ⊢ Sort mGhost i ε≡ C.
Proof.
  intros Γ A C h.
  dependent induction h.
  - eexists. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_hide_inv :
  ∀ Γ t C,
    Γ ⊢ hide t : C →
    ∃ i A,
      cscoping Γ A mKind ∧
      cscoping Γ t mType ∧
      Γ ⊢ A : Sort mType i ∧
      Γ ⊢ t : A ∧
      Γ ⊢ Erased A ε≡ C.
Proof.
  intros Γ t C h.
  dependent induction h.
  - eexists _,_. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists _,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_reveal_inv :
  ∀ Γ t P p C,
    Γ ⊢ reveal t P p : C →
    ∃ i j m A,
      cscoping Γ p m ∧
      cscoping Γ t mGhost ∧
      cscoping Γ P mKind ∧
      cscoping Γ A mKind ∧
      In m [ mProp ; mGhost ] ∧
      Γ ⊢ t : Erased A ∧
      Γ ⊢ P : Erased A ⇒[ i | usup m j / mGhost | mKind ] Sort m j ∧
      Γ ⊢ p : Pi i j m mType A (app (S ⋅ P) (hide (var 0))) ∧
      Γ ⊢ app P t ε≡ C.
Proof.
  intros Γ t P p C h.
  dependent induction h.
  - eexists _,_,_,_. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists _,_,_,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_Reveal_inv :
  ∀ Γ t p C,
    Γ ⊢ Reveal t p : C →
    ∃ i A,
      cscoping Γ t mGhost ∧
      cscoping Γ p mKind ∧
      Γ ⊢ t : Erased A ∧
      Γ ⊢ p : A ⇒[ i | 0 / mType | mKind ] Sort mProp 0 ∧
      Γ ⊢ A : Sort mType i ∧
      cscoping Γ A mKind ∧
      Γ ⊢ Sort mProp 0 ε≡ C.
Proof.
  intros Γ t p C h.
  dependent induction h.
  - eexists _,_. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists _,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_toRev_inv :
  ∀ Γ t p u C,
    Γ ⊢ toRev t p u : C →
    ∃ i A,
      cscoping Γ t mType ∧
      cscoping Γ p mKind ∧
      cscoping Γ u mProp ∧
      Γ ⊢ t : A ∧
      Γ ⊢ p : A ⇒[ i | 0 / mType | mKind ] Sort mProp 0 ∧
      Γ ⊢ u : app p t ∧
      Γ ⊢ Reveal (hide t) p ε≡ C.
Proof.
  intros Γ t p u C h.
  dependent induction h.
  - eexists _,_. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists _,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_fromRev_inv :
  ∀ Γ t p u C,
    Γ ⊢ fromRev t p u : C →
    ∃ i A,
      cscoping Γ t mType ∧
      cscoping Γ p mKind ∧
      cscoping Γ u mProp ∧
      Γ ⊢ t : A ∧
      Γ ⊢ p : A ⇒[ i | 0 / mType | mKind ] Sort mProp 0 ∧
      Γ ⊢ u : Reveal (hide t) p ∧
      Γ ⊢ app p t ε≡ C.
Proof.
  intros Γ t p u C h.
  dependent induction h.
  - eexists _,_. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists _,_. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_gheq_inv :
  ∀ Γ A u v C,
    Γ ⊢ gheq A u v : C →
    ∃ i,
      cscoping Γ A mKind ∧
      cscoping Γ u mGhost ∧
      cscoping Γ v mGhost ∧
      Γ ⊢ A : Sort mGhost i ∧
      Γ ⊢ u : A ∧
      Γ ⊢ v : A ∧
      Γ ⊢ Sort mProp 0 ε≡ C.
Proof.
  intros Γ A u v C h.
  dependent induction h.
  - eexists. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_ghrefl_inv :
  ∀ Γ A u C,
    Γ ⊢ ghrefl A u : C →
    ∃ i,
      cscoping Γ A mKind ∧
      cscoping Γ u mGhost ∧
      Γ ⊢ A : Sort mGhost i ∧
      Γ ⊢ u : A ∧
      Γ ⊢ gheq A u u ε≡ C.
Proof.
  intros Γ A u C h.
  dependent induction h.
  - eexists. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_ghcast_inv :
  ∀ Γ A u v e P t C,
    Γ ⊢ ghcast A u v e P t : C →
    ∃ i m,
      cscoping Γ A mKind ∧
      cscoping Γ P mKind ∧
      cscoping Γ u mGhost ∧
      cscoping Γ v mGhost ∧
      cscoping Γ t m ∧
      cscoping Γ e mProp ∧
      m ≠ mKind ∧
      Γ ⊢ A : Sort mGhost i ∧
      Γ ⊢ u : A ∧
      Γ ⊢ v : A ∧
      Γ ⊢ e : gheq A u v ∧
      Γ ⊢ P : A ⇒[ i | usup m i / mGhost | mKind ] Sort m i ∧
      Γ ⊢ t : app P u ∧
      Γ ⊢ app P v ε≡ C.
Proof.
  intros Γ A u v e P t C h.
  dependent induction h.
  - eexists _,_. intuition idtac. all: eauto.
    apply conv_refl.
  - destruct_exists IHh1. eexists _,_.
    intuition idtac. all: eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_bool_inv :
  ∀ Γ C,
    Γ ⊢ tbool : C →
    Γ ⊢ Sort mType 0 ε≡ C.
Proof.
  intros Γ C h.
  dependent induction h.
  - apply conv_refl.
  - eapply conv_trans. all: eauto.
Qed.

Lemma type_true_inv :
  ∀ Γ C,
    Γ ⊢ ttrue : C →
    Γ ⊢ tbool ε≡ C.
Proof.
  intros Γ C h.
  dependent induction h.
  - apply conv_refl.
  - eapply conv_trans. all: eauto.
Qed.

Lemma type_false_inv :
  ∀ Γ C,
    Γ ⊢ tfalse : C →
    Γ ⊢ tbool ε≡ C.
Proof.
  intros Γ C h.
  dependent induction h.
  - apply conv_refl.
  - eapply conv_trans. all: eauto.
Qed.

Lemma type_if_inv :
  ∀ Γ m b P t f C,
    Γ ⊢ tif m b P t f : C →
    ∃ i,
      cscoping Γ b mType ∧
      cscoping Γ P mKind ∧
      cscoping Γ t m ∧
      cscoping Γ f m ∧
      Γ ⊢ b : tbool ∧
      Γ ⊢ P : tbool ⇒[ 0 | usup m i / mType | mKind ] Sort m i ∧
      Γ ⊢ t : app P ttrue ∧
      Γ ⊢ f : app P tfalse ∧
      Γ ⊢ app P b ε≡ C.
Proof.
  intros Γ m b P t f C h.
  dependent induction h.
  - eexists. intuition idtac. 1: eauto.
    apply conv_refl.
  - destruct_exists IHh1. eexists _.
    intuition idtac. 1: eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_nat_inv :
  ∀ Γ C,
    Γ ⊢ tnat : C →
    Γ ⊢ Sort mType 0 ε≡ C.
Proof.
  intros Γ C h.
  dependent induction h.
  - apply conv_refl.
  - eapply conv_trans. all: eauto.
Qed.

Lemma type_zero_inv :
  ∀ Γ C,
    Γ ⊢ tzero : C →
    Γ ⊢ tnat ε≡ C.
Proof.
  intros Γ C h.
  dependent induction h.
  - apply conv_refl.
  - eapply conv_trans. all: eauto.
Qed.

Lemma type_succ_inv :
  ∀ Γ n C,
    Γ ⊢ tsucc n : C →
    cscoping Γ n mType ∧
    Γ ⊢ n : tnat ∧
    Γ ⊢ tnat ε≡ C.
Proof.
  intros Γ n C h.
  dependent induction h.
  - intuition idtac. apply conv_refl.
  - intuition auto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_nat_elim_inv :
  ∀ Γ m n P z s C,
    Γ ⊢ tnat_elim m n P z s : C →
    ∃ i,
      m ≠ mKind ∧
      cscoping Γ n mType ∧
      cscoping Γ P mKind ∧
      cscoping Γ z m ∧
      cscoping Γ s m ∧
      Γ ⊢ n : tnat ∧
      Γ ⊢ P : tnat ⇒[ 0 | usup m i / mType | mKind ] Sort m i ∧
      Γ ⊢ z : app P tzero ∧
      Γ ⊢ s : Pi 0 i m mType tnat (app (S ⋅ P) (var 0) ⇒[ i | i / m | m ] app (S ⋅ P) (tsucc (var 0))) ∧
      Γ ⊢ app P n ε≡ C.
Proof.
  intros Γ m n P z s C h.
  dependent induction h.
  - eexists. intuition idtac. 1,2: eauto.
    apply conv_refl.
  - destruct_exists IHh1. eexists _.
    intuition idtac. 1,2: eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_vec_inv :
  ∀ Γ A n C,
    Γ ⊢ tvec A n : C →
    ∃ i,
      cscoping Γ A mKind ∧
      cscoping Γ n mGhost ∧
      Γ ⊢ A : Sort mType i ∧
      Γ ⊢ n : Erased tnat ∧
      Γ ⊢ Sort mType i ε≡ C.
Proof.
  intros Γ A n C h.
  dependent induction h.
  - eexists. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists.
    intuition eauto. eapply conv_trans. all: eauto.
Qed.

Lemma type_vnil_inv :
  ∀ Γ A C,
    Γ ⊢ tvnil A : C →
    ∃ i,
      cscoping Γ A mKind ∧
      Γ ⊢ A : Sort mType i ∧
      Γ ⊢ tvec A (hide tzero) ε≡ C.
Proof.
  intros Γ A C h.
  dependent induction h.
  - eexists. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists.
    intuition eauto. eapply conv_trans. all: eauto.
Qed.

Lemma type_vcons_inv :
  ∀ Γ a n v C,
    Γ ⊢ tvcons a n v : C →
    ∃ i A,
      cscoping Γ a mType ∧
      cscoping Γ n mGhost ∧
      cscoping Γ v mType ∧
      Γ ⊢ a : A ∧
      Γ ⊢ n : Erased tnat ∧
      Γ ⊢ v : tvec A n ∧
      Γ ⊢ A : Sort mType i ∧
      cscoping Γ A mKind ∧
      Γ ⊢ tvec A (gS n) ε≡ C.
Proof.
  intros Γ a n v C h.
  dependent induction h.
  - eexists _,_. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists _,_.
    intuition eauto. eapply conv_trans. all: eauto.
Qed.

Lemma type_vec_elim_inv :
  ∀ Γ m A n v P z s C,
    Γ ⊢ tvec_elim m A n v P z s : C →
    ∃ i j,
      m ≠ mKind ∧
      cscoping Γ v mType ∧
      cscoping Γ P mKind ∧
      cscoping Γ z m ∧
      cscoping Γ s m ∧
      Γ ⊢ v : tvec A n ∧
      Γ ⊢ P : Pi 0 (umax mType mKind i (usup m j)) mKind mGhost (Erased tnat) (
        tvec (S ⋅ A) (var 0) ⇒[ i | usup m j / mType | mKind ] Sort m j
      ) ∧
      Γ ⊢ z : app (app P (hide tzero)) (tvnil A) ∧
      Γ ⊢ s : Pi i (umax mGhost m 0 (umax mType m i (umax m m j j))) m mType A (
        Pi 0 (umax mType m i (umax m m j j)) m mGhost (Erased tnat) (
          Pi i (umax m m j j) m mType (tvec (S ⋅ S ⋅ A) (var 0)) (
            app (app (S ⋅ S ⋅ S ⋅ P) (var 1)) (var 0) ⇒[ j | j / m | m ]
            app (app (S ⋅ S ⋅ S ⋅ P) (gS (var 1))) (tvcons (var 2) (var 1) (var 0))
          )
        )
      ) ∧
      cscoping Γ n mGhost ∧
      cscoping Γ A mKind ∧
      Γ ⊢ A : Sort mType i ∧
      Γ ⊢ n : Erased tnat ∧
      Γ ⊢ app (app P n) v ε≡ C.
Proof.
  intros Γ m A n v P z s C h.
  dependent induction h.
  - eexists _,_. intuition eauto.
    apply conv_refl.
  - destruct_exists IHh1. eexists _,_.
    intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Lemma type_bot_inv :
  ∀ Γ C,
    Γ ⊢ bot : C →
    Γ ⊢ Sort mProp 0 ε≡ C.
Proof.
  intros Γ C h.
  dependent induction h.
  - apply conv_refl.
  - eapply conv_trans. all: eauto.
Qed.

Lemma type_bot_elim_inv :
  ∀ Γ m A p C,
    Γ ⊢ bot_elim m A p : C →
    ∃ i,
      cscoping Γ A mKind ∧
      cscoping Γ p mProp ∧
      Γ ⊢ A : Sort m i ∧
      Γ ⊢ p : bot ∧
      Γ ⊢ A ε≡ C.
Proof.
  intros Γ m A p C h.
  dependent induction h.
  - eexists. intuition eauto. apply conv_refl.
  - destruct_exists IHh1. eexists. intuition eauto.
    eapply conv_trans. all: eauto.
Qed.

Ltac ttinv h h' :=
  lazymatch type of h with
  | _ ⊢ ?t : _ =>
    lazymatch t with
    | var _ => eapply type_var_inv in h as h'
    | Sort _ _ => eapply type_sort_inv in h as h'
    | Pi _ _ _ _ _ _ => eapply type_pi_inv in h as h'
    | lam _ _ _ => eapply type_lam_inv in h as h'
    | app _ _ => eapply type_app_inv in h as h'
    | Erased _ => eapply type_erased_inv in h as h'
    | hide _ => eapply type_hide_inv in h as h'
    | reveal _ _ _ => eapply type_reveal_inv in h as h'
    | Reveal _ _ => eapply type_Reveal_inv in h as h'
    | toRev _ _ _ => eapply type_toRev_inv in h as h'
    | fromRev _ _ _ => eapply type_fromRev_inv in h as h'
    | gheq _ _ _ => eapply type_gheq_inv in h as h'
    | ghrefl _ _ => eapply type_ghrefl_inv in h as h'
    | ghcast _ _ _ _ _ _ => eapply type_ghcast_inv in h as h'
    | tbool => eapply type_bool_inv in h as h'
    | ttrue => eapply type_true_inv in h as h'
    | tfalse => eapply type_false_inv in h as h'
    | tif _ _ _ _ _ => eapply type_if_inv in h as h'
    | tnat => eapply type_nat_inv in h as h'
    | tzero => eapply type_zero_inv in h as h'
    | tsucc _ => eapply type_succ_inv in h as h'
    | tnat_elim _ _ _ _ _ => eapply type_nat_elim_inv in h as h'
    | tvec _ _ => eapply type_vec_inv in h as h'
    | tvnil _ => eapply type_vnil_inv in h as h'
    | tvcons _ _ _ => eapply type_vcons_inv in h as h'
    | tvec_elim _ _ _ _ _ _ _ => eapply type_vec_elim_inv in h as h'
    | bot => eapply type_bot_inv in h as h'
    | bot_elim _ _ _ => eapply type_bot_elim_inv in h as h'
    end
  end.

(** Validity (or presupposition) **)

Lemma validity :
  ∀ Γ t A,
    wf Γ →
    Γ ⊢ t : A →
    cscoping Γ t (mdc Γ t) ∧
    (∃ i, Γ ⊢ A : Sort (mdc Γ t) i).
Proof.
  intros Γ t A hΓ h.
  induction h in hΓ |- *.
  all: try solve [
    split ; [
      cbn ; econstructor ; eauto
    | eexists ; econstructor ; eauto
    ]
  ].
  - split.
    + constructor. unfold sc. rewrite nth_error_map.
      rewrite H. cbn.
      change mType with (fst (mType, A)).
      rewrite map_nth. erewrite nth_error_nth. 2: eassumption.
      reflexivity.
    + induction hΓ as [| Γ my j B hΓ ih hB] in x, H |- *. 1: destruct x ; discriminate.
      destruct x.
      * cbn in *. inversion H. subst.
        exists j. rasimpl.
        eapply meta_conv. 1: eapply typing_ren.
        -- apply rtyping_S.
        -- eassumption.
        -- reflexivity.
      * cbn in H. eapply ih in H as [i h].
        eapply typing_ren in h. 2: eapply rtyping_S with (m := my) (A := B).
        rasimpl in h.
        exists i. assumption.
  - split.
    + cbn. constructor. 1,2: auto.
      apply IHh3. econstructor. all: eauto.
    + eexists. cbn. eapply meta_conv. 1: econstructor. all: auto.
      erewrite scoping_md. 2: eassumption.
      reflexivity.
  - split.
    + cbn. econstructor. 2: eauto.
      eapply scoping_md in H0 as e. subst.
      assumption.
    + forward IHh1 by auto. destruct IHh1 as [hst [l hP]].
      ttinv hP hP'.
      eexists. eapply meta_conv. 1: eapply typing_subst. 2: intuition eauto.
      * eapply styping_one. all: auto.
      * cbn. erewrite scoping_md. 1: reflexivity.
        assumption.
  - split.
    + cbn. erewrite scoping_md. 2: eassumption.
      cbn in H3. destruct H3 as [<- | [<- |]].
      * constructor. all: auto with datatypes.
      * constructor. all: auto with datatypes.
      * contradiction.
    + eexists. eapply meta_conv. 1: econstructor. 4: shelve. all: eauto.
      * rasimpl. constructor.
      * pose proof IHh2 as hP.
        forward hP by auto. destruct hP as [hsP [l hP]].
        eapply type_pi_inv in hP. intuition assumption.
      * pose proof IHh2 as hP.
        forward hP by auto. destruct hP as [hsP [l hP]].
        eapply type_pi_inv in hP. intuition assumption.
      * cbn - [mdc]. f_equal.
        cbn. erewrite scoping_md. 2: eassumption.
        destruct H3 as [<- | [<- |]]. 3: contradiction.
        all: reflexivity.
      Unshelve. constructor. assumption.
  - split.
    + cbn. econstructor. all: assumption.
    + forward IHh2 by auto. destruct IHh2 as [hp [j hT]].
      ttinv hT h'.
      cbn. eexists. econstructor.
      * constructor. assumption.
      * assumption.
      * econstructor. 3,4: intuition eauto. all: intuition auto.
      * eassumption.
      * intuition eauto.
      * intuition eauto.
  - split.
    + cbn. econstructor. all: assumption.
    + forward IHh2 by auto. destruct IHh2 as [hp [j hT]].
      ttinv hT h'.
      cbn. eexists. eapply meta_conv. 1: econstructor. 5-9: intuition eauto.
      all: intuition eauto.
  - split.
    + cbn. econstructor. all: eauto.
      * erewrite scoping_md. 2: eassumption. assumption.
      * erewrite scoping_md. 2: eassumption. assumption.
    + eexists. eapply meta_conv. 1: econstructor. 4: shelve.
      all: try eassumption.
      * cbn. constructor.
      * cbn. econstructor.
      * cbn - [mdc]. f_equal.
        cbn. erewrite scoping_md. 2: eassumption. reflexivity.
      Unshelve. assumption.
  - split.
    + cbn. econstructor. all: eauto.
    + eexists. cbn. eapply meta_conv.
      * econstructor. 5: eassumption. all: try eassumption.
        all: cbn. all: constructor.
      * reflexivity.
  - split.
    + cbn. constructor. all: eauto.
    + eexists. cbn. eapply meta_conv.
      * econstructor. 5: eassumption. all: try eassumption.
        all: cbn. all: constructor.
      * reflexivity.
  - split.
    + cbn. constructor. auto.
    + cbn. eexists. econstructor. all: gtype.
  - split.
    + cbn. gscope.
    + cbn. eexists. gtype.
      1:{ cbn. auto. }
      1: reflexivity.
      unfold gS. eapply type_conv.
      4:{
        econstructor. 6: eauto. all: gtype.
        1,3,4: reflexivity.
        1: cbn ; auto.
        1:{
          eapply meta_conv.
          - econstructor.
            5:{
              cbn. econstructor. 6: gtype. all: gtype.
            }
            all: gtype.
            1,2: reflexivity.
            eapply meta_conv.
            + gtype. reflexivity.
            + reflexivity.
          - reflexivity.
        }
        cbn. eapply type_conv.
        4:{
          econstructor.
          4:{
            gtype. 1: reflexivity.
            eapply meta_conv.
            - gtype. reflexivity.
            - reflexivity.
          }
          all: gtype.
          reflexivity.
        }
        4:{
          apply conv_sym. gconv. reflexivity.
        }
        1-3: gscope. 1,2: reflexivity.
        eapply meta_conv.
        - econstructor.
          6:{
            econstructor.
            4:{ gtype. reflexivity. }
            all: cbn. all: gtype.
            reflexivity.
          }
          all: cbn.
          3:{ econstructor. gscope. reflexivity. }
          4:{
            econstructor. 6: gtype. all: gtype.
          }
          all: gtype.
        - reflexivity.
      }
      4:{ cbn. gconv. eapply scoping_castrm. assumption. }
      all: gtype.
      * lazy. auto.
      * reflexivity.
  - split.
    + cbn. gscope.
    + eexists. eapply meta_conv.
      * econstructor. 6: eauto.
        5:{
          eapply meta_conv.
          - econstructor. 5: eauto. all: gtype. all: try reflexivity.
            1-3: eapply scoping_ren ; cbn ; eauto using rscoping_S.
            + eapply meta_conv.
              * eapply typing_ren. 1: apply rtyping_S.
                eauto.
              * reflexivity.
            + eapply meta_conv.
              * gtype. reflexivity.
              * reflexivity.
          - cbn. f_equal. rasimpl. reflexivity.
        }
        all: gtype.
      * reflexivity.
  - split.
    + cbn. constructor. all: auto.
    + eexists. cbn. eassumption.
  - split.
    + erewrite scoping_md. 2: eassumption. assumption.
    + eexists. erewrite scoping_md. 2: eassumption. eassumption.
Qed.