Require Import core fintype.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive term (n_term : nat) : Type :=
  | var_term : fin n_term -> term n_term
  | app : term n_term -> term n_term -> term n_term
  | lam : term (S n_term) -> term n_term.

Lemma congr_app {m_term : nat} {s0 : term m_term} {s1 : term m_term}
  {t0 : term m_term} {t1 : term m_term} (H0 : s0 = t0) (H1 : s1 = t1) :
  app m_term s0 s1 = app m_term t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app m_term x s1) H0))
         (ap (fun x => app m_term t0 x) H1)).
Qed.

Lemma congr_lam {m_term : nat} {s0 : term (S m_term)} {t0 : term (S m_term)}
  (H0 : s0 = t0) : lam m_term s0 = lam m_term t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => lam m_term x) H0)).
Qed.

Lemma upRen_term_term {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_term_term (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_term {m_term : nat} {n_term : nat}
(xi_term : fin m_term -> fin n_term) (s : term m_term) {struct s} :
term n_term :=
  match s with
  | var_term _ s0 => var_term n_term (xi_term s0)
  | app _ s0 s1 => app n_term (ren_term xi_term s0) (ren_term xi_term s1)
  | lam _ s0 => lam n_term (ren_term (upRen_term_term xi_term) s0)
  end.

Lemma up_term_term {m : nat} {n_term : nat} (sigma : fin m -> term n_term) :
  fin (S m) -> term (S n_term).
Proof.
exact (scons (var_term (S n_term) var_zero) (funcomp (ren_term shift) sigma)).
Defined.

Lemma up_list_term_term (p : nat) {m : nat} {n_term : nat}
  (sigma : fin m -> term n_term) : fin (plus p m) -> term (plus p n_term).
Proof.
exact (scons_p p (funcomp (var_term (plus p n_term)) (zero_p p))
         (funcomp (ren_term (shift_p p)) sigma)).
Defined.

Fixpoint subst_term {m_term : nat} {n_term : nat}
(sigma_term : fin m_term -> term n_term) (s : term m_term) {struct s} :
term n_term :=
  match s with
  | var_term _ s0 => sigma_term s0
  | app _ s0 s1 =>
      app n_term (subst_term sigma_term s0) (subst_term sigma_term s1)
  | lam _ s0 => lam n_term (subst_term (up_term_term sigma_term) s0)
  end.

Lemma upId_term_term {m_term : nat} (sigma : fin m_term -> term m_term)
  (Eq : forall x, sigma x = var_term m_term x) :
  forall x, up_term_term sigma x = var_term (S m_term) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_term shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_term_term {p : nat} {m_term : nat}
  (sigma : fin m_term -> term m_term)
  (Eq : forall x, sigma x = var_term m_term x) :
  forall x, up_list_term_term p sigma x = var_term (plus p m_term) x.
Proof.
exact (fun n =>
       scons_p_eta (var_term (plus p m_term))
         (fun n => ap (ren_term (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_term {m_term : nat} (sigma_term : fin m_term -> term m_term)
(Eq_term : forall x, sigma_term x = var_term m_term x) (s : term m_term)
{struct s} : subst_term sigma_term s = s :=
  match s with
  | var_term _ s0 => Eq_term s0
  | app _ s0 s1 =>
      congr_app (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | lam _ s0 =>
      congr_lam
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s0)
  end.

Lemma upExtRen_term_term {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_term_term xi x = upRen_term_term zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_term_term {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_term_term p xi x = upRen_list_term_term p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_term {m_term : nat} {n_term : nat}
(xi_term : fin m_term -> fin n_term) (zeta_term : fin m_term -> fin n_term)
(Eq_term : forall x, xi_term x = zeta_term x) (s : term m_term) {struct s} :
ren_term xi_term s = ren_term zeta_term s :=
  match s with
  | var_term _ s0 => ap (var_term n_term) (Eq_term s0)
  | app _ s0 s1 =>
      congr_app (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | lam _ s0 =>
      congr_lam
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s0)
  end.

Lemma upExt_term_term {m : nat} {n_term : nat} (sigma : fin m -> term n_term)
  (tau : fin m -> term n_term) (Eq : forall x, sigma x = tau x) :
  forall x, up_term_term sigma x = up_term_term tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_term shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_term_term {p : nat} {m : nat} {n_term : nat}
  (sigma : fin m -> term n_term) (tau : fin m -> term n_term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_term_term p sigma x = up_list_term_term p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_term (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_term {m_term : nat} {n_term : nat}
(sigma_term : fin m_term -> term n_term)
(tau_term : fin m_term -> term n_term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : term m_term) {struct s}
   : subst_term sigma_term s = subst_term tau_term s :=
  match s with
  | var_term _ s0 => Eq_term s0
  | app _ s0 s1 =>
      congr_app (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | lam _ s0 =>
      congr_lam
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s0)
  end.

Lemma up_ren_ren_term_term {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_term zeta) (upRen_term_term xi) x =
  upRen_term_term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_term_term {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_term_term p zeta) (upRen_list_term_term p xi) x =
  upRen_list_term_term p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_term {k_term : nat} {l_term : nat} {m_term : nat}
(xi_term : fin m_term -> fin k_term) (zeta_term : fin k_term -> fin l_term)
(rho_term : fin m_term -> fin l_term)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x)
(s : term m_term) {struct s} :
ren_term zeta_term (ren_term xi_term s) = ren_term rho_term s :=
  match s with
  | var_term _ s0 => ap (var_term l_term) (Eq_term s0)
  | app _ s0 s1 =>
      congr_app (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | lam _ s0 =>
      congr_lam
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s0)
  end.

Lemma up_ren_subst_term_term {k : nat} {l : nat} {m_term : nat}
  (xi : fin k -> fin l) (tau : fin l -> term m_term)
  (theta : fin k -> term m_term) (Eq : forall x, funcomp tau xi x = theta x)
  :
  forall x,
  funcomp (up_term_term tau) (upRen_term_term xi) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_term shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_term_term {p : nat} {k : nat} {l : nat}
  {m_term : nat} (xi : fin k -> fin l) (tau : fin l -> term m_term)
  (theta : fin k -> term m_term) (Eq : forall x, funcomp tau xi x = theta x)
  :
  forall x,
  funcomp (up_list_term_term p tau) (upRen_list_term_term p xi) x =
  up_list_term_term p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_term (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_term {k_term : nat} {l_term : nat} {m_term : nat}
(xi_term : fin m_term -> fin k_term) (tau_term : fin k_term -> term l_term)
(theta_term : fin m_term -> term l_term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x)
(s : term m_term) {struct s} :
subst_term tau_term (ren_term xi_term s) = subst_term theta_term s :=
  match s with
  | var_term _ s0 => Eq_term s0
  | app _ s0 s1 =>
      congr_app (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | lam _ s0 =>
      congr_lam
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s0)
  end.

Lemma up_subst_ren_term_term {k : nat} {l_term : nat} {m_term : nat}
  (sigma : fin k -> term l_term) (zeta_term : fin l_term -> fin m_term)
  (theta : fin k -> term m_term)
  (Eq : forall x, funcomp (ren_term zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_term shift (upRen_term_term zeta_term)
                (funcomp shift zeta_term) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_term zeta_term shift (funcomp shift zeta_term)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_term shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_term_term {p : nat} {k : nat} {l_term : nat}
  {m_term : nat} (sigma : fin k -> term l_term)
  (zeta_term : fin l_term -> fin m_term) (theta : fin k -> term m_term)
  (Eq : forall x, funcomp (ren_term zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_list_term_term p zeta_term))
    (up_list_term_term p sigma) x = up_list_term_term p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var_term (plus p m_term)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_term (shift_p p)
                  (upRen_list_term_term p zeta_term)
                  (funcomp (shift_p p) zeta_term)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_term zeta_term (shift_p p)
                        (funcomp (shift_p p) zeta_term) (fun x => eq_refl)
                        (sigma n))) (ap (ren_term (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_term {k_term : nat} {l_term : nat} {m_term : nat}
(sigma_term : fin m_term -> term k_term)
(zeta_term : fin k_term -> fin l_term)
(theta_term : fin m_term -> term l_term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : term m_term) {struct s} :
ren_term zeta_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var_term _ s0 => Eq_term s0
  | app _ s0 s1 =>
      congr_app
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | lam _ s0 =>
      congr_lam
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s0)
  end.

Lemma up_subst_subst_term_term {k : nat} {l_term : nat} {m_term : nat}
  (sigma : fin k -> term l_term) (tau_term : fin l_term -> term m_term)
  (theta : fin k -> term m_term)
  (Eq : forall x, funcomp (subst_term tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_term shift (up_term_term tau_term)
                (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_term tau_term shift
                      (funcomp (ren_term shift) tau_term) (fun x => eq_refl)
                      (sigma fin_n))) (ap (ren_term shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_term_term {p : nat} {k : nat} {l_term : nat}
  {m_term : nat} (sigma : fin k -> term l_term)
  (tau_term : fin l_term -> term m_term) (theta : fin k -> term m_term)
  (Eq : forall x, funcomp (subst_term tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_list_term_term p tau_term))
    (up_list_term_term p sigma) x = up_list_term_term p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_term (plus p l_term)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_term (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_term (shift_p p) (up_list_term_term p tau_term)
                  (funcomp (up_list_term_term p tau_term) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_term tau_term (shift_p p) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_term (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_term {k_term : nat} {l_term : nat} {m_term : nat}
(sigma_term : fin m_term -> term k_term)
(tau_term : fin k_term -> term l_term)
(theta_term : fin m_term -> term l_term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : term m_term) {struct s} :
subst_term tau_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var_term _ s0 => Eq_term s0
  | app _ s0 s1 =>
      congr_app
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | lam _ s0 =>
      congr_lam
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s0)
  end.

Lemma renRen_term {k_term : nat} {l_term : nat} {m_term : nat}
  (xi_term : fin m_term -> fin k_term) (zeta_term : fin k_term -> fin l_term)
  (s : term m_term) :
  ren_term zeta_term (ren_term xi_term s) =
  ren_term (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_term_pointwise {k_term : nat} {l_term : nat} {m_term : nat}
  (xi_term : fin m_term -> fin k_term) (zeta_term : fin k_term -> fin l_term)
  :
  pointwise_relation _ eq (funcomp (ren_term zeta_term) (ren_term xi_term))
    (ren_term (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term {k_term : nat} {l_term : nat} {m_term : nat}
  (xi_term : fin m_term -> fin k_term) (tau_term : fin k_term -> term l_term)
  (s : term m_term) :
  subst_term tau_term (ren_term xi_term s) =
  subst_term (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term_pointwise {k_term : nat} {l_term : nat} {m_term : nat}
  (xi_term : fin m_term -> fin k_term) (tau_term : fin k_term -> term l_term)
  :
  pointwise_relation _ eq (funcomp (subst_term tau_term) (ren_term xi_term))
    (subst_term (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term {k_term : nat} {l_term : nat} {m_term : nat}
  (sigma_term : fin m_term -> term k_term)
  (zeta_term : fin k_term -> fin l_term) (s : term m_term) :
  ren_term zeta_term (subst_term sigma_term s) =
  subst_term (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term_pointwise {k_term : nat} {l_term : nat} {m_term : nat}
  (sigma_term : fin m_term -> term k_term)
  (zeta_term : fin k_term -> fin l_term) :
  pointwise_relation _ eq
    (funcomp (ren_term zeta_term) (subst_term sigma_term))
    (subst_term (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s => compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term {k_term : nat} {l_term : nat} {m_term : nat}
  (sigma_term : fin m_term -> term k_term)
  (tau_term : fin k_term -> term l_term) (s : term m_term) :
  subst_term tau_term (subst_term sigma_term s) =
  subst_term (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term_pointwise {k_term : nat} {l_term : nat} {m_term : nat}
  (sigma_term : fin m_term -> term k_term)
  (tau_term : fin k_term -> term l_term) :
  pointwise_relation _ eq
    (funcomp (subst_term tau_term) (subst_term sigma_term))
    (subst_term (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_term_term {m : nat} {n_term : nat}
  (xi : fin m -> fin n_term) (sigma : fin m -> term n_term)
  (Eq : forall x, funcomp (var_term n_term) xi x = sigma x) :
  forall x,
  funcomp (var_term (S n_term)) (upRen_term_term xi) x = up_term_term sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_term shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_term_term {p : nat} {m : nat} {n_term : nat}
  (xi : fin m -> fin n_term) (sigma : fin m -> term n_term)
  (Eq : forall x, funcomp (var_term n_term) xi x = sigma x) :
  forall x,
  funcomp (var_term (plus p n_term)) (upRen_list_term_term p xi) x =
  up_list_term_term p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var_term (plus p n_term)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_term (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_term {m_term : nat} {n_term : nat}
(xi_term : fin m_term -> fin n_term) (sigma_term : fin m_term -> term n_term)
(Eq_term : forall x, funcomp (var_term n_term) xi_term x = sigma_term x)
(s : term m_term) {struct s} : ren_term xi_term s = subst_term sigma_term s
:=
  match s with
  | var_term _ s0 => Eq_term s0
  | app _ s0 s1 =>
      congr_app (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | lam _ s0 =>
      congr_lam
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s0)
  end.

Lemma rinstInst'_term {m_term : nat} {n_term : nat}
  (xi_term : fin m_term -> fin n_term) (s : term m_term) :
  ren_term xi_term s = subst_term (funcomp (var_term n_term) xi_term) s.
Proof.
exact (rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_term_pointwise {m_term : nat} {n_term : nat}
  (xi_term : fin m_term -> fin n_term) :
  pointwise_relation _ eq (ren_term xi_term)
    (subst_term (funcomp (var_term n_term) xi_term)).
Proof.
exact (fun s => rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_term {m_term : nat} (s : term m_term) :
  subst_term (var_term m_term) s = s.
Proof.
exact (idSubst_term (var_term m_term) (fun n => eq_refl) s).
Qed.

Lemma instId'_term_pointwise {m_term : nat} :
  pointwise_relation _ eq (subst_term (var_term m_term)) id.
Proof.
exact (fun s => idSubst_term (var_term m_term) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_term {m_term : nat} (s : term m_term) : ren_term id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma rinstId'_term_pointwise {m_term : nat} :
  pointwise_relation _ eq (@ren_term m_term m_term id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma varL'_term {m_term : nat} {n_term : nat}
  (sigma_term : fin m_term -> term n_term) (x : fin m_term) :
  subst_term sigma_term (var_term m_term x) = sigma_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_term_pointwise {m_term : nat} {n_term : nat}
  (sigma_term : fin m_term -> term n_term) :
  pointwise_relation _ eq (funcomp (subst_term sigma_term) (var_term m_term))
    sigma_term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_term {m_term : nat} {n_term : nat}
  (xi_term : fin m_term -> fin n_term) (x : fin m_term) :
  ren_term xi_term (var_term m_term x) = var_term n_term (xi_term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_term_pointwise {m_term : nat} {n_term : nat}
  (xi_term : fin m_term -> fin n_term) :
  pointwise_relation _ eq (funcomp (ren_term xi_term) (var_term m_term))
    (funcomp (var_term n_term) xi_term).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_term X Y :=
    up_term : X -> Y.

#[global]
Instance Subst_term  {m_term n_term : nat}: (Subst1 _ _ _) :=
 (@subst_term m_term n_term).

#[global]
Instance Up_term_term  {m n_term : nat}: (Up_term _ _) :=
 (@up_term_term m n_term).

#[global]
Instance Ren_term  {m_term n_term : nat}: (Ren1 _ _ _) :=
 (@ren_term m_term n_term).

#[global]
Instance VarInstance_term  {n_term : nat}: (Var _ _) := (@var_term n_term).

Notation "[ sigma_term ]" := (subst_term sigma_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_term ]" := (subst_term sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__term" := up_term (only printing)  : subst_scope.

Notation "↑__term" := up_term_term (only printing)  : subst_scope.

Notation "⟨ xi_term ⟩" := (ren_term xi_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_term ⟩" := (ren_term xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_term ( at level 1, only printing)  : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
( at level 5, format "x __term", only printing)  : subst_scope.

Notation "x '__term'" := (var_term x) ( at level 5, format "x __term")  :
subst_scope.

#[global]
Instance subst_term_morphism  {m_term : nat} {n_term : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_term m_term n_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_term f_term s = subst_term g_term t')
         (ext_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_term_morphism2  {m_term : nat} {n_term : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_term m_term n_term)).
Proof.
exact (fun f_term g_term Eq_term s => ext_term f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_term_morphism  {m_term : nat} {n_term : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_term m_term n_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_term f_term s = ren_term g_term t')
         (extRen_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_term_morphism2  {m_term : nat} {n_term : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_term m_term n_term)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_term f_term g_term Eq_term s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                      Up_term_term, Up_term, up_term, Subst_term, Subst1,
                      subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_term, Var, ids,
                                            Ren_term, Ren1, ren1,
                                            Up_term_term, Up_term, up_term,
                                            Subst_term, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress
                    unfold up_list_term_term, up_term_term,
                     upRen_list_term_term, upRen_term_term, up_ren
                 | progress cbn[subst_term ren_term]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1
                  in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_term_pointwise;
                  try setoid_rewrite rinstInst'_term.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_term_pointwise;
                  try setoid_rewrite_left rinstInst'_term.

End Core.

Module Extra.

Import
Core.

Arguments var_term {n_term}.

Arguments lam {n_term}.

Arguments app {n_term}.

#[global] Hint Opaque subst_term: rewrite.

#[global] Hint Opaque ren_term: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

