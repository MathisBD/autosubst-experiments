From Prototype Require Import MPrelude MSig.

(** This file defines a generic term grammar with _admissible_ renamings 
    and substitutions, i.e. renamings are functions [nat -> nat] 
    and substitutions are functions [nat -> term m].
    
    We prove the main properties of substitution and renaming. *)

Module O.
Section WithSig.
Context {sig : signature}.

(*********************************************************************************)
(** *** Level one terms. *)
(*********************************************************************************)

(** Notations for expressions with known kinds. *)
#[local] Reserved Notation "'term' m" (at level 0).
#[local] Reserved Notation "'arg' ty" (at level 0, ty at level 0).
#[local] Reserved Notation "'args' tys" (at level 0, tys at level 0).

(** Terms over an abstract signature. Terms are indexed by a kind.
    Note that terms have a sort, but arguments and argument lists
    can't be assigned a unique sort in general (for instance 
    what would be the sort of [E_abase _ _] ?). *)
Inductive expr : kind -> Type :=
| (** Variable constructor. *)
  E_var {m} : nat -> term m
| (** Non-variable constructor applied to a list of arguments. *)
  E_ctor {m} : forall (c : ctor m), args (ctor_type c) -> term m
| (** Empty argument list. *)
  E_al_nil : args []
| (** Non-empty argument list. *)
  E_al_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)
| (** Base argument (e.g. bool or string). *)
  E_abase : forall b, base_type b -> arg (AT_base b)
| (** Term argument. *)
  E_aterm {m} : term m -> arg (AT_term m)
| (** Binder argument. *)
  E_abind {ty} : forall m, arg ty -> arg (AT_bind m ty)

where "'term' m" := (expr (Kt m))
  and "'arg' ty" := (expr (Ka ty))
  and "'args' tys" := (expr (Kal tys)).

Derive Signature NoConfusion NoConfusionHom for expr.

(*********************************************************************************)
(** *** Induction on expressions based on their size. *)
(*********************************************************************************)

(*(** Size of expressions. *)
Equations expr_size {k} : expr k -> nat :=
expr_size (E_var _) := 0 ;
expr_size (E_ctor c al) := S (expr_size al) ;
expr_size E_al_nil := 0 ;
expr_size (E_al_cons a al) := S (expr_size a + expr_size al) ;
expr_size (E_abase _ _) := 0 ;
expr_size (E_aterm t) := S (expr_size t) ;
expr_size (E_abind _ a) := S (expr_size a).

Section SizeInd.
  Context (P : forall k, expr k -> Prop).

  Context (IH : forall s (t : term s), 
    (forall s' (t' : term s'), expr_size t' < expr_size t -> P s' t') -> 
    P s t).

  Lemma size_ind : forall s t, P s t.
  Proof.
  intros s t. remember (term_size t) as n eqn:E.
  revert s t E. induction n using Wf_nat.lt_wf_ind. intros s t ->.
  apply IH. intros s' t' Hlt. eapply H ; eauto.
  Qed.
End SizeInd.*)

(** Notation for left to right function composition. *)
Notation "f >> g" := (fun i => g (f i)) (at level 30).

(*********************************************************************************)
(** *** Renamings. *)
(*********************************************************************************)

(** Vector of renamings. *)
Definition vren := sort -> ren.

(** A vector of identity renamings. *)
Definition vren_id : vren := fun _ => rid.

(** [vren_shift_point m] has [rshift] at position [m] and [rid] at other positions. *)
Definition vren_shift_point (m : sort) : vren :=
  fun m' => if eq_dec m m' then rshift else rid.

(** Lift a vector of renamings through a binder for sort [m]. *)
Definition vren_up (m : sort) (rv : vren) : vren :=
  fun m' => if eq_dec m m' then up_ren (rv m') else (rv m').

(** Apply a vector of renamings to an expression. *)
Equations rename {k} (rv : vren) (t : expr k) : expr k :=
rename rv (@E_var m i) := E_var (rv m i) ;
rename rv (E_ctor c al) := E_ctor c (rename rv al) ;
rename rv E_al_nil := E_al_nil ;
rename rv (E_al_cons a al) := E_al_cons (rename rv a) (rename rv al) ;
rename rv (E_abase b x) := E_abase b x ;
rename rv (E_aterm t) := E_aterm (rename rv t) ;
rename rv (E_abind m a) := E_abind m (rename (vren_up m rv) a).

(*********************************************************************************)
(** *** Substitutions. *)
(*********************************************************************************)

(** A single substitution which yields terms of sort [m]. *)
Definition subst m := nat -> term m.

(** The identity substitution. *)
Definition sid {m} : subst m := fun i => E_var i.

(** [sshift] shifts indices by one. *)
Definition sshift {m} : subst m := 
  fun i => E_var (S i).

(** Cons a term with a substitution. *)
Equations scons {m} (t : term m) (s : subst m) : subst m :=
scons t s 0 := t ;
scons t s (S i) := s i.

(** Left to right composition of a substitution with a vector of renamings. *)
Definition srcomp {m} (s : subst m) (r : vren) : subst m := 
  fun i => rename r (s i).

(** Left to right composition of a renaming with a vector of substitutions. *)
(*Definition rscomp {m} (r : ren) (s : subst m) : subst m := 
  fun i => s (r i).*)

(** A vector of substitutions. *)
Definition vsubst := forall m, subst m.

(** Lift a vector of substitutions through a binder of sort [m].*)
Definition up_vsubst (m : sort) (svec : vsubst) : vsubst :=
  let r := vren_shift_point m in 
  fun m' => 
    if eq_dec m m' 
    then scons (E_var 0) (srcomp (svec m') r) 
    else srcomp (svec m') r.

(** Apply a vector of substitutions to an expression. *)
Equations substitute {k} (svec : vsubst) (t : expr k) : expr k :=
substitute svec (@E_var m i) := svec m i ;
substitute svec (E_ctor c al) := E_ctor c (substitute svec al) ;
substitute svec E_al_nil := E_al_nil ;
substitute svec (E_al_cons a al) := E_al_cons (substitute svec a) (substitute svec al) ;
substitute svec (E_abase b x) := E_abase b x ;
substitute svec (E_aterm t) := E_aterm (substitute svec t) ;
substitute svec (E_abind m a) := E_abind m (substitute (up_vsubst m svec) a).

(** Left to right composition of a substitution with a vector of substitutions. *)
Definition scomp {m} (s : subst m) (svec : vsubst) : subst m :=
  fun i => substitute svec (s i).

(*********************************************************************************)
(** *** Setoid Rewrite lemmas. *)
(*********************************************************************************)

#[export] Instance vren_up_proper : Proper (eq ==> eq2 ==> eq2) vren_up.
Proof.
intros m ? <- rv rv' Hrv m' i. unfold vren_up.
destruct (eq_dec m m').
- apply up_ren_proper. apply Hrv.
- now rewrite Hrv. 
Qed.

#[export] Instance rename_proper k : Proper (eq2 ==> eq ==> eq) (@rename k).
Proof.
intros rv rv' Hr t _ <-. induction t in rv, rv', Hr |- * ; simp rename.
all: try solve [ f_equal ; auto ].
- now rewrite Hr. 
- f_equal. apply IHt. now rewrite Hr.
Qed. 

#[export] Instance substitute_proper k : Proper (eq2 ==> eq ==> eq) (@substitute k).

(*********************************************************************************)
(** *** Properties of renamings and substitutions. *)
(*********************************************************************************)

Lemma up_ren_id : up_ren rid =₁ rid.
Proof. intros [|i] ; reflexivity. Qed.

Lemma vren_up_id m : vren_up m vren_id =₂ vren_id.
Proof.
intros m'. unfold vren_up. destruct (eq_dec m m').
- rewrite up_ren_id. reflexivity.
- reflexivity.
Qed.    
Hint Rewrite vren_up_id : rename.

Lemma rename_id {k} (t : expr k) : 
  rename vren_id t = t.
Proof.
induction t ; simp rename.
all: now f_equal.
Qed.
Hint Rewrite @rename_id : rename.


End WithSig.
End O.
