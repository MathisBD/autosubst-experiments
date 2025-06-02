From Prototype Require Export All.

(*********************************************************************************)
(** *** Generate all operations and lemmas. *)
(*********************************************************************************)

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

Derive NoConfusion NoConfusionHom for expr.

Inductive sort := Sty | Stm | Svl. 
Derive NoConfusion for sort.

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

(*********************************************************************************)
(** *** Scoping for terms. *)
(*********************************************************************************)

Definition scope := list sort.

(** Scoping as a proposition. *)
Inductive scoping : scope -> expr -> sort -> Type :=

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

Derive Signature NoConfusion NoConfusionHom for scoping.

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
Lemma rscoping_rename Γ Δ r t st :
  rscoping Γ r Δ ->
  scoping Δ t st ->
  scoping Γ (rename r t) st.
Proof.
intros Hr Ht. induction Ht in Γ, r, Hr |- *.
all: solve [ rasimpl ; constructor ; auto with scoping ].
Qed.

(*********************************************************************************)
(** *** Scoping for substitutions. *)
(*********************************************************************************)

(** [sscoping Γ s Δ] states that [s] takes inputs in [Δ] and has outputs in [Γ]. *)
Inductive sscoping (Γ : scope) (s : subst) : scope -> Prop :=
| sscoping_nil : sscoping Γ s []
| sscoping_cons Δ m :
    sscoping Γ (scomp sshift s) Δ ->
    scoping Γ (s 0) m ->
    sscoping Γ s (m :: Δ).

Lemma sscoping_weak Γ Δ s m :
  sscoping Γ s Δ -> sscoping (m :: Γ) (srcomp s rshift) Δ.
Proof.
intros H. induction H.
- constructor.
- constructor.
  + assumption.
  + eapply rscoping_rename. 2: eassumption. apply rscoping_rshift.
Qed.
#[export] Hint Resolve sscoping_weak : scoping.

(** Substituting preserves the scope. *)
Lemma sscoping_substitute Γ Δ s t m :
  sscoping Γ s Δ ->
  scoping Δ t m ->
  scoping Γ (substitute s t) m.
Proof.
intros Hs Ht.
induction Ht in Γ, s, Hs |- *.
all: try solve [ rasimpl ; econstructor ; eauto ].
- rasimpl_topdown.

rename H into hx, Γ0 into Δ. induction hσ in x, hx |- *. 1: destruct x ; discriminate.
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


(*Inductive ty_view : scoping -> expr -> Type :=
| ty_view_var i : ty_view (scoping_var Γ i Sty p) (var i) 
| ty_view_arr t1 t2 : ty_view (arr t1 t2)
| ty_view_all t : ty_view (all t).

Definition build_ty_view (Γ : scope) (t : expr) (s : scoping Γ t Sty) : ty_view t.
depelim s ; constructor.
Defined.

Equations ty_size Γ t (s : scoping Γ t Sty) : nat :=
ty_size Γ t s with ty_view Γ t s :=
ty_size Γ (var i) s (ty_view_var _) := 0 ;
ty_size Γ (arr t1 t2)  (ty_view_arr _ _) := S (ty_size s1 + ty_size s2) ;

ty_size (scoping_var _ _ _ _) := 0 ;
ty_size (scoping_arr _ t1 t2 s1 s2) := S (ty_size s1 + ty_size s2) ;
ty_size (scoping_all _ t s) := S (ty_size s).*)

(*********************************************************************************)
(** *** Triggers. *)
(*********************************************************************************)

(*(** Trigger [rasimpl] on [rename _ _]. *)
Lemma autosubst_simpl_term_rename (r : ren) (t res : term) :
  TermSimplification (rename r t) res -> rename r t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_rename : asimpl_topdown.

(** Trigger [rasimpl] on [substitute _ _]. *)
Lemma autosubst_simpl_term_substitute (s : subst) (t res : term) :
  TermSimplification (substitute s t) res -> substitute s t = res.
Proof. intros H. now apply term_simplification. Qed.
#[export] Hint Rewrite -> autosubst_simpl_term_substitute : asimpl_topdown.

Axiom F : subst -> term.

(** Trigger [rasimpl] on a substitution occuring inside [F _]. *)
(*Lemma autosubst_simpl_F (s res : subst) :
  SubstSimplification s res -> F s = F res.
Proof. Admitted.
#[export] Hint Rewrite -> autosubst_simpl_F : asimpl_outermost.*)

Axiom r : ren.
Axiom s : subst.
Axiom t : term.
Lemma test : substitute (scomp s (scons (substitute (rscomp r s) t) s)) t = t.
Proof. rasimpl.
Admitted.*)