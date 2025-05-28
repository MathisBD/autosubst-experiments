From Prototype Require Import MPrelude MSig.

(*********************************************************************************)
(** *** Level one. *)
(*********************************************************************************)

Section LevelOne.
Context {sig : signature}.

Lemma occurs_in {s1 s2 ty} {c : fin (nctor s2)} : 
  occurs_ty s1 ty -> In ty (ctor_type c) -> occurs s1 s2.
Proof.
intros H1 H2. apply occurs_base. exists c. rewrite Exists_exists. eauto.
Qed.

(** Level one terms. *)

Inductive term : fin nsort -> Type :=
| T_var {s} : has_var s -> nat -> term s
| T_ctor {s} (c : fin (nctor s)) : args (ctor_type c) -> term s

with args : list arg_ty -> Type :=
| AL_nil : args []
| AL_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)

with arg : arg_ty -> Type :=
| A_base b : base_type b -> arg (AT_base b)
| A_term {s} : term s -> arg (AT_term s)
| A_bind {s s'} : term s' -> arg (AT_bind s s'). 

Derive Signature NoConfusion NoConfusionHom for term args arg.

Definition ren (s : fin nsort) := nat -> nat.

(** Vector of renamings which can be applied to a term of sort [s]. *)
Definition ren_vec (s : fin nsort) :=
  forall s', occurs s' s -> has_var s' -> ren s'.

(** Select a subvector of a vector of renaming. *)
Equations? ren_subvector {s1 s2} (p : occurs s1 s2) (rv : ren_vec s2) : ren_vec s1 := 
ren_subvector p rv := fun s' pocc pvar => rv s' _ pvar.
Proof. eapply occurs_trans ; eauto. Qed.

(** Apply a vector of renamings to a term. *)
Equations? rename {s} (rv : ren_vec s) (t : term s) : term s :=
rename rv (T_var p i) := T_var p (rv s (occurs_refl s) p i) ;
rename rv (T_ctor c al) := T_ctor c (rename_args c _ rv al)

with rename_args {s} {tys : list arg_ty} (c : fin (nctor s)) (p : incl tys (ctor_type c)) 
  (rv : ren_vec s) (al : args tys) : args tys :=
rename_args c p rv AL_nil := AL_nil ;
rename_args c p rv (AL_cons a al) := AL_cons (rename_arg c _ rv a) (rename_args c _ rv al)

with rename_arg {s} {ty : arg_ty} (c : fin (nctor s)) (p : In ty (ctor_type c))
  (rv : ren_vec s) (a : arg ty) : arg ty :=
rename_arg c p rv (A_base b x) := A_base b x ;
rename_arg c p rv (A_term t) := A_term (rename (ren_subvector _ rv) t) ;
rename_arg c p rv (A_bind a) := A_bind a.

Proof.
- apply p. now left.
- apply p. now right.
- unshelve eapply (occurs_in _ p). constructor.
Qed.

Lemma has_var_aux s : has_varb s -> has_var s.
Proof. now destruct (has_var_spec s). Qed.

Lemma has_var_aux' s : has_var s -> has_varb s.
Proof. now destruct (has_var_spec s). Qed.

End LevelOne.

(*********************************************************************************)
(** *** Level zero. *)
(*********************************************************************************)

Inductive ty : Type :=
| var_ty : nat -> ty
| arr : ty -> ty -> ty
| all : ty -> ty.

Inductive tm : Type :=
| app : tm -> tm -> tm
| tapp : tm -> ty -> tm
| vt : vl -> tm

with vl : Type :=
| var_vl : nat -> vl
| lam : ty -> tm -> vl
| tlam : tm -> vl.

Equations rename_ty (rty : nat -> nat) : ty -> ty :=
rename_ty rty (var_ty i) := var_ty (rty i) ;
rename_ty rty (arr t1 t2) := arr (rename_ty rty t1) (rename_ty rty t2) ;
rename_ty rty (all t) := all (rename_ty (up_ren rty) t).

Equations rename_tm (rty rvl : nat -> nat) : tm -> tm :=
rename_tm rty rvl (app t1 t2) := app (rename_tm rty rvl t1) (rename_tm rty rvl t2) ;
rename_tm rty rvl (tapp t1 t2) := tapp (rename_tm rty rvl t1) (rename_ty rty t2) ;
rename_tm rty rvl (vt v) := vt (rename_vl rty rvl v)

with rename_vl (rty rvl : nat -> nat) : vl -> vl :=
rename_vl rty rvl (var_vl i) := var_vl (rvl i) ;
rename_vl rty rvl (lam t1 t2) := lam (rename_ty rty t1) (rename_tm rty (up_ren rvl ) t2) ;
rename_vl rty rvl (tlam t) := tlam (rename_tm (up_ren rty) rvl t).

(*********************************************************************************)
(** *** Signature. *)
(*********************************************************************************)

Definition nbase_ := 0.

Definition base_type_ (b : fin nbase_) : Type :=
  vector_nth b vnil.

Definition nsort_ := 3.
Notation sty := (finO) (only parsing).
Notation stm := (finS finO) (only parsing).
Notation svl := (finS (finS finO)) (only parsing).

Definition nctor_ (s : fin nsort_) : nat :=
  vector_nth s (vcons 2 (vcons 3 (vcons 2 vnil))).

Equations ctor_type_ (s : fin nsort_) (c : fin (nctor_ s)) : list (@arg_ty nbase_ nsort_) :=
ctor_type_ sty c := 
  vector_nth c [| [ AT_term sty ; AT_term sty ] ; [ AT_bind sty sty ] |] ;
ctor_type_ _ _ := [].

ctor_type_ stm finO := [ AT_term stm ; AT_term stm ] ;
ctor_type_ stm (finS finO) := [ AT_term stm ; AT_term sty ] ;
ctor_type_ stm (finS (finS finO)) := [ AT_term svl ] ;

ctor_type_ svl finO := [ AT_term sty ; AT_bind svl stm ] ;
ctor_type_ svl (finS finO) := [ AT_bind sty stm ].

Definition sig : signature := 
  Build_signature nbase_ base_type_ nsort_ nctor_ ctor_type_.

(*********************************************************************************)
(** *** Bijection between level zero and one. *)
(*********************************************************************************)

Lemma explode {A : Type} : is_true false -> A.
Proof. intros H. unfold is_true in H. discriminate. Qed.

Equations reify_ty : ty -> @term sig sty :=
reify_ty (var_ty i) := T_var (@has_var_aux sig sty eq_refl) i ;
reify_ty (arr t1 t2) := 
  @T_ctor sig sty finO (AL_cons (A_term (reify_ty t1)) (AL_cons (A_term (reify_ty t2)) AL_nil)) ;
reify_ty (all t) := 
  @T_ctor sig sty (finS finO) (AL_cons (A_bind (reify_ty t)) AL_nil).

Equations reify_tm : tm -> @term sig stm :=
reify_tm (app t1 t2) :=
  @T_ctor sig stm finO (AL_cons (A_term (reify_tm t1)) (AL_cons (A_term (reify_tm t2)) AL_nil)) ;
reify_tm (tapp t1 t2) :=
  @T_ctor sig stm (finS finO) (AL_cons (A_term (reify_tm t1)) (AL_cons (A_term (reify_ty t2)) AL_nil)) ;
reify_tm (vt t) :=
  @T_ctor sig stm (finS (finS finO)) (AL_cons (A_term (reify_vl t)) AL_nil)

with reify_vl : vl -> @term sig svl :=
reify_vl (var_vl i) := T_var (@has_var_aux sig svl eq_refl) i ;
reify_vl (lam t1 t2) :=
  @T_ctor sig svl finO (AL_cons (A_term (reify_ty t1)) (AL_cons (A_bind (reify_tm t2)) AL_nil)) ;
reify_vl (tlam t) :=
  @T_ctor sig svl (finS finO) (AL_cons (A_bind (reify_tm t)) AL_nil).

Equations eval_sort (s : fin (@nsort sig)) : Type :=
eval_sort sty := ty ;
eval_sort stm := tm ;
eval_sort svl := vl.

Equations eval_arg_ty (ty : @arg_ty (@nbase sig) (@nsort sig)) : Type :=
eval_arg_ty (AT_base b) := @base_type sig b ;
eval_arg_ty (AT_term s) := eval_sort s ;
eval_arg_ty (AT_bind _ s) := eval_sort s.

Equations eval_arg_tys (tys : list (@arg_ty (@nbase sig) (@nsort sig))) : Type :=
eval_arg_tys [] := unit ;
eval_arg_tys (ty :: tys) := eval_arg_ty ty * eval_arg_tys tys.

Equations eval_ctor (s : fin (@nsort sig)) (c : fin (nctor s)) : 
  eval_arg_tys (ctor_type c) -> eval_sort s :=
eval_ctor sty finO (t1, (t2, tt)) := arr t1 t2 ;
eval_ctor sty (finS finO) (t, tt) := all t ;

eval_ctor stm finO (t1, (t2, tt)) := app t1 t2 ;
eval_ctor stm (finS finO) (t1, (t2, tt)) := tapp t1 t2 ;
eval_ctor stm (finS (finS finO)) (t, tt) := vt t ;

eval_ctor svl finO (t1, (t2, tt)) := lam t1 t2 ;
eval_ctor svl (finS finO) (t, tt) := tlam t.

Equations eval {s} : @term sig s -> eval_sort s :=
@eval sty (T_var p i) := var_ty i ;
@eval stm (T_var p _) := explode (has_var_aux' _ p) ;
@eval svl (T_var _ i) := var_vl i ;
eval (T_ctor c al) := eval_ctor s c (eval_args al)

with eval_args {tys} (al : args tys) : eval_arg_tys tys :=
eval_args AL_nil := tt ;
eval_args (AL_cons a al) := (eval_arg a, eval_args al)

with eval_arg {ty} (a : arg ty) : eval_arg_ty ty :=
eval_arg (A_base b x) := x ;
eval_arg (A_term t) := eval t ;
eval_arg (A_bind t) := eval t.

Lemma eval_reify_ty (t : ty) : eval (reify_ty t) = t.
Proof.
induction t ; simp reify_ty eval.
- reflexivity.
- change (@ctor_type sig (@finO 2) (@finO 1)) with 
    [@AT_term nbase_ nsort_ sty ; AT_term sty].
  simp eval. rewrite IHt1, IHt2. reflexivity.
- change (@ctor_type sig (@finO 2) (@finS 1 (@finO 0))) with 
    [@AT_bind nbase_ nsort_ sty sty].
  simp eval. rewrite IHt. reflexivity.
Qed.

Lemma eval_reify_tm : 
  (forall t, eval (reify_tm t) = t) * (forall v, eval (reify_vl v) = v).
Proof.
apply reify_tm_elim with 
  (P := fun t res => eval res = t)
  (P0 := fun v res => eval res = v).
- intros t1 t2 H1 H2. simp eval. Set Printing Implicit.
Admitted.