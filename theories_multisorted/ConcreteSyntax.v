From MPrototype Require Import Prelude Sig.
From MPrototype Require ParamSyntax.
Module P := ParamSyntax.

(*********************************************************************************)
(** *** Concrete syntax. *)
(*********************************************************************************)

Unset Elimination Schemes. 

Inductive ty : Set :=
| var_ty : nat -> ty
| arr : ty -> ty -> ty
| all : ty -> ty.
 
Inductive tm : Set :=
| app : tm -> tm -> tm
| tapp : tm -> ty -> tm
| vt : vl -> tm

with vl : Set :=
| var_vl : nat -> vl
| lam : ty -> tm -> vl
| tlam : tm -> vl.

Set Elimination Schemes.

Scheme ty_ind := Induction for ty Sort Prop.
Scheme tm_ind := Induction for tm Sort Prop 
  with vl_ind := Induction for vl Sort Prop.
Combined Scheme tm_vl_ind from tm_ind, vl_ind.

Scheme ty_rect := Induction for ty Sort Type.
Scheme tm_rect := Induction for tm Sort Type 
  with vl_rect := Induction for vl Sort Type.
Combined Scheme tm_vl_rect from tm_rect, vl_rect.

(*********************************************************************************)
(** *** Concrete renamings. *)
(*********************************************************************************)

Equations rename_ty : ren -> ty -> ty :=
rename_ty rty (var_ty i) := var_ty (rty i) ;
rename_ty rty (arr t1 t2) := arr (rename_ty rty t1) (rename_ty rty t2) ;
rename_ty rty (all t) := all (rename_ty (rup rty) t).

Equations rename_tm : ren -> ren -> tm -> tm :=
rename_tm rty rvl (app t1 t2) := app (rename_tm rty rvl t1) (rename_tm rty rvl t2) ;
rename_tm rty rvl (tapp t1 t2) := tapp (rename_tm rty rvl t1) (rename_ty rty t2) ;
rename_tm rty rvl (vt v) := vt (rename_vl rty rvl v)

with rename_vl : ren -> ren -> vl -> vl :=
rename_vl rty rvl (var_vl i) := var_vl (rvl i) ;
rename_vl rty rvl (lam t1 t2) := lam (rename_ty rty t1) (rename_tm rty (rup rvl) t2) ;
rename_vl rty rvl (tlam t) := tlam (rename_tm (rup rty) rvl t).

(*********************************************************************************)
(** *** Signature. *)
(*********************************************************************************)

Module ConcreteSignature.

  Inductive base := .
  Derive NoConfusion EqDec for base.

  Definition base_type (b : base) : Type :=
    match b with end.
  
  Inductive sort := Sty | Stm | Svl.
  Derive NoConfusion EqDec for sort.

  Inductive ctor_ty := Carr | Call.
  Inductive ctor_tm := Capp | Ctapp | Cvt.
  Inductive ctor_vl := Clam | Ctlam.
  Derive NoConfusion EqDec for ctor_ty ctor_tm ctor_vl.

  Definition ctor (s : sort) : Type :=
    match s with 
    | Sty => ctor_ty 
    | Stm => ctor_tm 
    | Svl => ctor_vl
    end.
  Definition ctor_EqDec (s : sort) : EqDec (ctor s).
  Proof. destruct s ; typeclasses eauto. Defined.
  
  Definition ctor_type (s : sort) (c : ctor s) : list (@arg_ty base sort) := 
    match s as s0 return ctor s0 -> list (@arg_ty base sort) with 
    | Sty => fun c => 
      match c with 
      | Carr => [ AT_term Sty ; AT_term Sty ]
      | Call => [ AT_bind Sty (AT_term Sty) ]
      end
    | Stm => fun c =>
      match c with 
      | Capp => [ AT_term Stm ; AT_term Stm ]
      | Ctapp => [ AT_term Stm ; AT_term Sty ]
      | Cvt => [ AT_term Svl ]
      end
    | Svl => fun c =>
      match c with 
      | Clam => [ AT_term Sty ; AT_bind Svl (AT_term Stm) ]
      | Ctlam => [ AT_bind Sty (AT_term Stm) ]
      end
    end c.

  Definition sig : signature := 
    Build_signature base base_EqDec base_type sort sort_EqDec ctor ctor_EqDec ctor_type.

End ConcreteSignature.
Import ConcreteSignature.
#[local] Existing Instance sig.

(*********************************************************************************)
(** *** Well formed terms. *)
(*********************************************************************************)

Section Wf.
  Context {has_var : sort -> bool}.

  Inductive wf : forall {k}, P.expr k -> Prop :=
  | wf_var m i : has_var m -> wf (P.E_var (m := m) i)
  | wf_ctor m (c : ctor m) al : wf al -> wf (P.E_ctor c al)
  | wf_al_nil : wf P.E_al_nil 
  | wf_al_cons {ty tys} (a : P.expr (Ka ty)) (al : P.expr (Kal tys)) : 
      wf a -> wf al -> wf (P.E_al_cons a al)
  | wf_abase b x : wf (P.E_abase b x)
  | wf_aterm {m} (t : P.expr (Kt m)) : wf t -> wf (P.E_aterm t)
  | wf_abind {ty} m (a : P.expr (Ka ty)) :
    has_var m -> wf a -> wf (P.E_abind m a).

  Derive Signature for wf.

  #[local] Hint Constructors wf : core.

  (** * Inversion lemmas. *)

  Lemma wf_var_inv {m} {i} : wf (P.E_var (m := m) i) -> has_var m.
  Proof. intros H. now depelim H. Qed.

  Lemma wf_ctor_inv {m} {c : ctor m} {al} : wf (P.E_ctor c al) -> wf al.
  Proof. intros H. now depelim H. Qed.

  Lemma wf_al_cons_inv1 {ty} {tys} {a : P.expr (Ka ty)} {al : P.expr (Kal tys)} :
    wf (P.E_al_cons a al) -> wf a.
  Proof. intros H. now depelim H. Qed.

  Lemma wf_al_cons_inv2 {ty} {tys} {a : P.expr (Ka ty)} {al : P.expr (Kal tys)} :
    wf (P.E_al_cons a al) -> wf al.
  Proof. intros H. now depelim H. Qed.

  Lemma wf_aterm_inv {m} {t : P.expr (Kt m)} : wf (P.E_aterm t) -> wf t.
  Proof. intros H. now depelim H. Qed.

  Lemma wf_abind_inv {ty} {m} {a : P.expr (Ka ty)} : 
    wf (P.E_abind m a) -> wf a.
  Proof. intros H. now depelim H. Qed.

  Lemma wf_abind_inv_var {ty} {m} {a : P.expr (Ka ty)} : 
    wf (P.E_abind m a) -> has_var m.
  Proof. intros H. now depelim H. Qed.

  (** * Well formed renamings/substitutions. *)

  Lemma wf_rename {k} r (t : P.expr k) : 
    wf t -> wf (P.rename r t).
  Proof.
  #[local] Hint Extern 1 => constructor : core.
  intros H. induction t in H, r |- * ; simp rename.
  all: solve [ depelim H ; auto ].
  Qed.

  Definition wf_subst {m} (s : P.subst m) :=
    forall i, wf (s i).

  Lemma wf_scons {m} (t : P.expr (Kt m)) (s : P.subst m) : 
    wf t -> wf_subst s -> wf_subst (P.scons t s).
  Proof. intros Ht Hs i. destruct i ; now cbn. Qed. 

  Definition wf_vsubst (s : P.vsubst) :=
    forall m, wf_subst (s m).

  Lemma wf_vsup m s : has_var m -> wf_vsubst s -> wf_vsubst (P.vsup m s).
  Proof.
  intros Hm Hs. intros m' i. unfold P.vsup. destruct (@eq_dec (@Sig.sort sig) _ m m').
  - subst. apply wf_scons.
    + now constructor.
    + intros i'. unfold P.svrcomp. apply wf_rename. apply Hs.
  - unfold P.svrcomp. apply wf_rename. apply Hs.
  Qed.

  Lemma wf_substitute {k} (s : P.vsubst) (t : P.expr k) :
    wf_vsubst s -> wf t -> wf (P.substitute s t).
  Proof.
  intros Hs Ht. induction t in s, Hs, Ht |- * ; simp substitute.
  all: try solve [ depelim Ht ; auto ].
  - apply Hs.
  - pose proof (Hm := wf_abind_inv_var Ht). constructor ; try assumption.
    apply wf_abind_inv in Ht. apply IHt ; auto using wf_vsup. 
  Qed.

End Wf.

(** * Specialization of [wf] to the sorts of system F. *)

Definition has_var (m : sort) : bool := 
  match m with Sty | Svl => true | Stm => false end.
 
Definition wf0 {k} (t : P.expr k) := @wf has_var k t.
Definition wf0_subst {m} (s : P.subst m) := @wf_subst has_var m s.
Definition wf0_vsubst (s : P.vsubst) := @wf_vsubst has_var s.

(*********************************************************************************)
(** *** Reification. *)
(*********************************************************************************)

Fixpoint reify_ty (t : ty) : P.expr (Kt Sty) :=
  match t with 
  | var_ty i => P.E_var i
  | arr t1 t2 => 
    P.E_ctor (m := Sty) Carr 
      (P.E_al_cons (P.E_aterm (reify_ty t1)) (P.E_al_cons (P.E_aterm (reify_ty t2)) P.E_al_nil))
  | all t => 
    P.E_ctor (m := Sty) Call 
      (P.E_al_cons (P.E_abind Sty (P.E_aterm (reify_ty t))) P.E_al_nil)
  end.

Fixpoint reify_tm (t : tm) : P.expr (Kt Stm) :=
  match t with 
  | app t1 t2 =>
    P.E_ctor (m := Stm) Capp (P.E_al_cons (P.E_aterm (reify_tm t1)) (P.E_al_cons (P.E_aterm (reify_tm t2)) P.E_al_nil))
  | tapp t1 t2 =>
    P.E_ctor (m := Stm) Ctapp (P.E_al_cons (P.E_aterm (reify_tm t1)) (P.E_al_cons (P.E_aterm (reify_ty t2)) P.E_al_nil))
  | vt t =>
    P.E_ctor (m := Stm) Cvt (P.E_al_cons (P.E_aterm (reify_vl t)) P.E_al_nil)
  end

with reify_vl (t : vl) : P.expr (Kt Svl) :=
  match t with 
  | var_vl i => P.E_var i
  | lam t1 t2 =>
    P.E_ctor (m := Svl) Clam 
      (P.E_al_cons (P.E_aterm (reify_ty t1)) (P.E_al_cons (P.E_abind Svl (P.E_aterm (reify_tm t2))) P.E_al_nil))
  | tlam t =>
    P.E_ctor (m := Svl) Ctlam 
      (P.E_al_cons (P.E_abind Sty (P.E_aterm (reify_tm t))) P.E_al_nil)
  end.

Lemma wf_reify_ty t : wf0 (reify_ty t).
Proof.
#[local] Hint Extern 1 => constructor : core.
induction t ; cbn ; auto.
Qed.

Lemma wf_reify_tm_vl : (forall t, wf0 (reify_tm t)) * (forall v, wf0 (reify_vl v)).
Proof.
apply tm_vl_rect ; intros ; cbn.
all: repeat constructor ; solve [ assumption | apply wf_reify_ty ].
Qed.

Lemma wf_reify_tm t : wf0 (reify_tm t).
Proof. now apply wf_reify_tm_vl. Qed.

Lemma wf_reify_vl t : wf0 (reify_vl t).
Proof. now apply wf_reify_tm_vl. Qed.
    
(* Testing... *)
Lemma wf_reify_subst_tm (s : nat -> tm) : wf0_subst (fun i => reify_tm (s i)).
Proof. intros i. apply wf_reify_tm. Qed.

(*********************************************************************************)
(** *** Evaluation. *)
(*********************************************************************************)

Definition eval_sort (s : sort) : Type :=
  match s with 
  | Sty => ty 
  | Stm => tm 
  | Svl => vl
  end.

Fixpoint eval_arg_ty (ty : @arg_ty base sort) : Type :=
  match ty with 
  | AT_base b => base_type b 
  | AT_term s => eval_sort s
  | AT_bind _ a => eval_arg_ty a
  end.

Fixpoint eval_arg_tys (tys : list (@arg_ty base sort)) : Type :=
  match tys with 
  | [] => unit 
  | ty :: tys => eval_arg_ty ty * eval_arg_tys tys 
  end.

Definition eval_kind (k : kind) : Type :=
  match k with 
  | Kt m => eval_sort m 
  | Ka ty => eval_arg_ty ty 
  | Kal tys => eval_arg_tys tys
  end.

(*Definition eval_ctor_Sty (c : ctor Sty) : eval_arg_tys (ctor_type Sty c) -> eval_sort Sty :=
  match c as c0 return eval_arg_tys (ctor_type Sty c0) -> eval_sort Sty with 
  | Carr => fun '(t1, (t2, tt)) => arr t1 t2
  | Call => fun '(t, tt) => all t
  end.*)

Definition eval_ctor (s : sort) (c : ctor s) : eval_arg_tys (ctor_type s c) -> eval_sort s :=
  match s as s0 return forall c : ctor s0, eval_arg_tys (ctor_type s0 c) -> eval_sort s0 with 
  | Sty => fun c =>
    match c as c0 return eval_arg_tys (ctor_type Sty c0) -> eval_sort Sty with 
    | Carr => fun '(t1, (t2, tt)) => arr t1 t2
    | Call => fun '(t, tt) => all t
    end
  | Stm => fun c =>
    match c as c0 return eval_arg_tys (ctor_type Stm c0) -> eval_sort Stm with 
    | Capp => fun '(t1, (t2, tt)) => app t1 t2 
    | Ctapp => fun '(t1, (t2, tt)) => tapp t1 t2
    | Cvt => fun '(t, tt) => vt t
    end
  | Svl => fun c =>
    match c as c0 return eval_arg_tys (ctor_type Svl c0) -> eval_sort Svl with 
    | Clam => fun '(t1, (t2, tt)) => lam t1 t2 
    | Ctlam => fun '(t, tt) => tlam t
    end
  end c.

Definition eval_var (m : sort) (i : nat) (H : wf0 (P.E_var (m := m) i)) : eval_sort m.
destruct m.
- exact (var_ty i).
- apply wf_var_inv in H. discriminate H.
- exact (var_vl i).
Defined.

Fixpoint eval {k} (t : P.expr k) (Ht : wf0 t) : eval_kind k :=
  match t as t0 in P.expr k0 return wf0 t0 -> eval_kind k0 with 
  | @P.E_var _ m i => eval_var m i
  | @P.E_ctor _ m c al => fun H => eval_ctor m c (eval al (wf_ctor_inv H)) 
  | P.E_al_nil => fun _ => tt
  | P.E_al_cons a al => fun H => (eval a (wf_al_cons_inv1 H), eval al (wf_al_cons_inv2 H))
  | P.E_abase b x => fun _ => x 
  | P.E_aterm t => fun H => eval t (wf_aterm_inv H)
  | P.E_abind m a => fun H => eval a (wf_abind_inv H)
  end Ht.

(*********************************************************************************)
(** *** Proof of bijection. *)
(*********************************************************************************)

Lemma eval_reify_ty (t : ty) (H : wf (reify_ty t)) : 
  eval (reify_ty t) H = t.
Proof. induction t ; cbn ; f_equal ; auto. Qed.

Lemma eval_reify_tm : 
  (forall t (H : wf (reify_tm t)), eval (reify_tm t) H = t) /\ 
  (forall v (H : wf (reify_vl v)), eval (reify_vl v) H = v).
Proof. apply tm_vl_ind. all: intros ; cbn ; f_equal ; auto using eval_reify_ty. Qed.

(*

Evaluation: 
  (t' : P.expr k) -> 
  (t : eval_kind k, H : wf0 t', eq : eval t' H = t)

*)

(*********************************************************************************)
(** *** Custom induction principle on level one terms. *)
(*********************************************************************************)

Section CustomInd.
  Context (P : forall m, P.expr (Kt m) -> Prop).
  
  Context (Hvar : forall m i, P m (P.E_var i)).

  Context (Harr : forall t1 t2, P Sty t1 -> P Sty t2 -> 
    P Sty (P.E_ctor (m := Sty) Carr (P.E_al_cons (P.E_aterm t1) (P.E_al_cons (P.E_aterm t2) P.E_al_nil)))).
  Context (Hall : forall t, P Sty t -> 
    P Sty (P.E_ctor (m := Sty) Call (P.E_al_cons (P.E_abind Sty (P.E_aterm t)) P.E_al_nil))).

  Context (Happ : forall t1 t2, P Stm t1 -> P Stm t2 ->
    P Stm (P.E_ctor (m := Stm) Capp (P.E_al_cons (P.E_aterm t1) (P.E_al_cons (P.E_aterm t2) P.E_al_nil)))).
  Context (Htapp : forall t1 t2, P Stm t1 -> P Sty t2 ->
    P Stm (P.E_ctor (m := Stm) Ctapp (P.E_al_cons (P.E_aterm t1) (P.E_al_cons (P.E_aterm t2) P.E_al_nil)))).
  Context (Hvt : forall t, P Svl t ->
    P Stm (P.E_ctor (m := Stm) Cvt (P.E_al_cons (P.E_aterm t) P.E_al_nil))).

  Context (Hlam : forall t1 t2, P Sty t1 -> P Stm t2 ->
    P Svl (P.E_ctor (m := Svl) Clam (P.E_al_cons (P.E_aterm t1) (P.E_al_cons (P.E_abind Svl (P.E_aterm t2)) P.E_al_nil)))).
  Context (Htlam : forall t1, P Stm t1 ->
    P Svl (P.E_ctor (m := Svl) Ctlam (P.E_al_cons (P.E_abind Sty (P.E_aterm t1)) P.E_al_nil))).
  
  Lemma custom_ind {m} : forall t : P.expr (Kt m), P m t.
  Proof.
  revert m. apply P.size_ind. intros m t IH. depelim m ; depelim t.
  all: try solve [ apply Hvar ].
  - depelim c.
    + depelim t. depelim t1. depelim t2. depelim t2_1. depelim t2_2. 
      apply Harr ; apply IH ; cbn ; lia.
    + depelim t. depelim t1. depelim t2. depelim t1. 
      apply Hall ; apply IH ; cbn ; lia.
  - depelim c.
    + depelim t. depelim t1. depelim t2. depelim t2_1. depelim t2_2. 
      apply Happ ; apply IH ; cbn ; lia.
    + depelim t. depelim t1. depelim t2. depelim t2_1. depelim t2_2. 
      apply Htapp ; apply IH ; cbn ; lia.
    + depelim t. depelim t1. depelim t2. 
      apply Hvt ; apply IH ; cbn ; lia.
  - depelim c.
    + depelim t. depelim t1. depelim t2. depelim t2_1. depelim t2_2. depelim t2_1.
      apply Hlam ; apply IH ; cbn ; lia.
    + depelim t. depelim t1. depelim t2. depelim t1. 
      apply Htlam ; apply IH ; cbn ; lia.
  Qed. 

End CustomInd.

(*********************************************************************************)
(** *** Transporting renamings. *)
(*********************************************************************************)
  
Definition eval_vren_type (m : sort) : Type :=
  match m with 
  | Sty => ren 
  | Stm => ren * ren 
  | Svl => ren * ren
  end.

Definition eval_vren m (r : P.vren) : eval_vren_type m :=
  match m with 
  | Sty => r Sty 
  | Stm => (r Sty, r Svl)
  | Svl => (r Sty, r Svl)
  end.

(** Evaluate [P.rename m] into a concrete function such as [rename_ty] or [rename_tm]. *)
Definition eval_rename m : eval_vren_type m -> eval_sort m -> eval_sort m :=
  match m as m0 return eval_vren_type m0 -> eval_sort m0 -> eval_sort m0 with 
  | Sty => fun rty t => rename_ty rty t
  | Stm => fun '(rty, rvl) t => rename_tm rty rvl t
  | Svl => fun '(rty, rvl) t => rename_vl rty rvl t
  end.

(*Lemma rename_ty_congr (r1 r2 : ren) (t1 t2 : ty) :
  r1 =₁ r2 -> t1 = t2 -> rename_ty r1 t1 = rename_ty r2 t2.
Proof.
intros H <-. induction t1 in r1, r2, H |- * ; simp rename_ty. 
- now rewrite H.
- f_equal ; auto.
- f_equal. apply IHt1. intros [|i] ; [reflexivity|]. cbv. now rewrite H.
Qed.*)

(*Definition wf_vren (m : sort) (r : P.vren) : Prop :=
  match m with 
  | Sty => r Stm =₁ rid /\ r Svl =₁ rid 
  | Stm => r Stm =₁ rid
  | Svl => r Stm =₁ rid
  end.*)


(** Push [eval] through renamings. *)
Lemma push_eval_rename {m} (r : P.vren) (t : P.expr (Kt m)) (H : wf t) (H' : wf (P.rename r t)) : 
   eval (P.rename r t) H' = eval_rename m (eval_vren m r) (eval t H).
Proof.
revert r H H'. pattern t. revert m t. apply custom_ind.
all: intros ; cbn in *.
- destruct m.
  + depelim H. depelim H'. reflexivity.
  + depelim H.
  + depelim H. depelim H'. reflexivity.    
- depelim H1. cbn in H1. depelim H1. depelim H1_. depelim H1_0. depelim H1_0_1. depelim H1_0_2. cbn.
  depelim H'. cbn in H'. depelim H'. depelim H'1. depelim H'2. depelim H'2_1. depelim H'2_2. cbn.
  f_equal.
  + apply H.
  + apply H0.   
apply H0.