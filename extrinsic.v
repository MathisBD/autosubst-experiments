From Coq Require Import String List.
Import ListNotations.

(** Convenience tactic. *)
Ltac inv H := inversion H ; subst.

(** Forall combinator in Type. *)
Inductive All {A} (P : A -> Type) : list A -> Type :=
| All_nil : All P []
| All_cons : forall (x : A) (l : list A),
    P x -> All P l -> All P (x :: l).
Arguments All {A} P%_type _.
Arguments All_nil {_ _}.
Arguments All_cons {_ _ _ _}.
#[global] Hint Constructors All : core.

(** Scoped de Bruijn indices. *)
(*Module DB.

Record t (n : nat) : Type :=
  { t_ : nat ; t_lt_n : t_ < n }.

Definition zero {n} : t (S n).
  refine {| t_ := 0 ; t_lt_n := _ |} ; lia.
Defined.

End DB.*)

(** Argument types over a set of base types. *)
Inductive arg_ty {base} :=
  | TBase : base -> arg_ty
  | TVar : arg_ty
  | TTerm : arg_ty
  | TBind : arg_ty -> arg_ty.

(** Signatures for abstract terms. *)
Module Type Signature.
  (** The set of base types, 
      e.g. [Inductive base := Unit | Bool | Nat]. *)
  Parameter base : Type.
  (** The actual type that each base type represents,
      e.g. a mapping Nat => nat ; Bool => bool ; Unit => unit. *)
  Parameter base_type : base -> Type.
  
  (** The set of constructors. *)
  Parameter ctor : Type.
  (** The number and type of each constructor argument. *)
  Parameter ctor_type : ctor -> list (@arg_ty base). 
End Signature.

Module AbstractTerms (S : Signature).
Export S.

Definition arg_ty := @arg_ty base.

(** Arguments, prior to taking the fixpoint in [term]. 
    [term] is the type of terms. *)
Inductive pre_arg {term : Type} :=
  | ABase : forall b, base_type b -> pre_arg
  | AVar : nat -> pre_arg
  | ATerm : term -> pre_arg
  | ABind : pre_arg -> pre_arg.

(** Abstract term grammar. *)
Inductive term :=
| Term : ctor -> list (@pre_arg term) -> term.

(** Arguments, after having taken the fixpoint. *)
Definition arg := @pre_arg term.

(** A nicer recursion principle for terms. *)
Section TermInd.
  Context (Parg : arg -> Type).
  Context (Pterm : term -> Type).
  Hypothesis Harg1 : forall b (x : base_type b), Parg (ABase b x).
  Hypothesis Harg2 : forall n, Parg (AVar n).
  Hypothesis Harg3 : forall t, Pterm t -> Parg (ATerm t).
  Hypothesis Harg4 : forall a, Parg a -> Parg (ABind a).
  Hypothesis Hterm : forall c args, (All Parg args) -> Pterm (Term c args).
  
  (* Don't use [induction] while proving this lemma, or it will 
     cause the guard checker to fail. *)
  Lemma better_term_rect : forall t, Pterm t.
  Proof.
  fix IHt 1. intros [c args]. apply Hterm.
  revert args. fix IHargs 1. intros [|a args] ; constructor.
  - revert a. fix IHa 1. intros [b x | n | t | a].
    + apply Harg1.
    + apply Harg2.
    + apply Harg3. apply IHt.
    + apply Harg4. apply IHa.      
  - apply IHargs.
  Qed.  
End TermInd.

(** Well-formedness of terms. *)
Inductive wf_term : term -> Type :=
| wf_term_intro c args : 
    wf_args args (ctor_type c) -> wf_term (Term c args)

with wf_args : list arg -> list arg_ty -> Type :=
| wf_args_nil : 
    wf_args [] []
| wf_args_cons a args ty tys : 
    wf_arg a ty -> wf_args args tys -> wf_args (a :: args) (ty :: tys)

with wf_arg : arg -> arg_ty -> Type :=
| wf_arg_base b (x : base_type b) : 
    wf_arg (ABase b x) (TBase b)
| wf_arg_var n : 
    wf_arg (AVar n) TVar
| wf_arg_term t : 
    wf_term t -> wf_arg (ATerm t) TTerm
| wf_arg_bind a ty : 
    wf_arg a ty -> wf_arg (ABind a) (TBind ty).

Hint Constructors wf_term : wf.
Hint Constructors wf_args : wf.
Hint Constructors wf_arg  : wf.

(** Lift a renaming, e.g. when we pass through a binder. *)
Definition up_ren (f : nat -> nat) : nat -> nat :=
  fun n =>
    match n with 
    | 0 => 0
    | S n => S (f n)
    end.

(** Rename an argument. *)
Fixpoint ren_arg (on_term : (nat -> nat) -> term -> term) 
  (f : nat -> nat) (a : arg) : arg :=
  match a with 
  | ABase b x => ABase b x
  | AVar v => AVar (f v)
  | ATerm t => ATerm (on_term f t)
  | ABind a => ABind (ren_arg on_term (up_ren f) a)
  end.

(** Rename a term. *)
Fixpoint ren (f : nat -> nat) (t : term) : term :=
  match t with 
  | Term c args => Term c (List.map (ren_arg ren f) args)
  end.

(** Renaming a term preserves well-formedness. *)
Lemma ren_term_wf f t :
  wf_term t -> wf_term (ren f t).
Proof. 
revert f.
pose (Harg := fun a => forall f ty, wf_arg a ty -> wf_arg (ren_arg ren f a) ty).
pattern t. apply (better_term_rect Harg) ; clear t.
- intros b x f ty H. inv H. constructor.
- intros n f ty H. inv H. constructor.
- intros t IHt f ty H. inv H. constructor.
  apply IHt. assumption.
- intros a IHa f ty H. inv H. constructor. fold ren_arg.
  apply IHa. assumption.
- intros c args H f Ht. constructor. fold ren.
  inv Ht. clear Ht. 
  remember (ctor_type c) as arg_tys. clear Heqarg_tys c.
  generalize dependent arg_tys. induction args as [| a args IHargs] ; simpl ; intros arg_tys H1.
  + inv H1. assumption.
  + inv H1. constructor.
    * inv H. auto.
    * apply IHargs ; [| now auto]. inv H ; auto.
Qed.

End AbstractTerms.

(** *** Example : lambda calculus. *)

(** Concrete terms. 
    Applications carry a boolean.
    Lambda abstractions contain the name of the bound variable as a string. *)
Inductive cterm :=
  | Var : nat -> cterm
  | App : bool -> cterm -> cterm -> cterm
  | Lam : string -> cterm -> cterm.

(** Abstract signature. *)

Module S.
  Inductive base_ := BString | BBool.
  Definition base := base_.
  
  Definition base_type (b : base) : Type :=
    match b with BString => string | BBool => bool end.
  
  Inductive ctor_ := CVar | CApp | CLam. 
  Definition ctor := ctor_. 

  Definition ctor_type (c : ctor) : list arg_ty :=
    match c with 
    | CVar => [ TVar ]
    | CApp => [ TBase BBool ; TTerm ; TTerm ]
    | CLam => [ TBase BString ; TBind (TTerm) ]
    end.
End S.
  
(** Abstract terms. *)
Module A := AbstractTerms (S).
Import A.
Definition aterm := term.

(** Mapping from concrete terms to abstract terms. *)
Fixpoint abstractize (t : cterm) : aterm :=
  match t with 
  | Var n => Term CVar [ AVar n ]
  | App b t1 t2 => 
    Term CApp [ ABase BBool b ; ATerm (abstractize t1) ; ATerm (abstractize t2) ]
  | Lam s t => 
    Term CLam [ ABase BString s ; ABind (ATerm (abstractize t)) ]
  end.

Definition view_base {b} {a : arg} (p : wf_arg a (TBase b)) : base_type b :=
  match p with 
  | wf_arg_base _ x => x
  end.

Definition view_var {a : arg} (p : wf_arg a TVar) : nat :=
  match p with 
  | wf_arg_var n => n
  end.

Definition view_term {a : arg} (p : wf_arg a TTerm) : { t : aterm & wf_term t } :=
  match p with 
  | wf_arg_term t p' => existT _ t p'
  end.

Definition view_bind {ty} {a : arg} (p : wf_arg a (TBind ty)) : { a : arg & wf_arg a ty } :=
  match p with 
  | wf_arg_bind a' ty' p' => existT _ a' p'
  end.

Definition view_args_hd {ty tys} {args : list arg} (p : wf_args args (ty :: tys)) : 
  { a : arg & wf_arg a ty } * { args : list arg & wf_args args tys } :=
  match p with 
  | wf_args_cons a args ty tys p0 p1 => (existT _ a p0, existT _ args p1)
  end.

(** Mapping from abstract terms to concrete terms. *)
Fixpoint concretize {t : aterm} (wf_t : wf_term t) {struct wf_t} : cterm :=
  match wf_t with 
  | wf_term_intro c args p => 
    match c, p with 
    | CVar, p => 
      let '(existT _ _ arg0, _) := view_args_hd p in
      let n := view_var arg0 in
      Var n
    | CApp, p =>
      let '(existT _ _ arg0, existT _ _ p) := view_args_hd p in
      let '(existT _ _ arg1, existT _ _ p) := view_args_hd p in
      (*let '(existT _ _ arg2, existT _ _ p) := view_args_hd p in*)
      let b := view_base arg0 in
      let '(existT _ _ t1) := view_term arg1 in
      (*let '(existT _ _ t2) := view_term arg2 in*)
      App b (concretize t1) (concretize t1)
    | CLam, p => Var 0
      (*let '(existT _ _ arg0, existT _ _ p) := view_args_hd p in
      let '(existT _ _ arg1, existT _ _ p) := view_args_hd p in
      let s := view_base arg0 in 
      let '(existT _ _ arg1) := view_bind arg1 in
      let '(existT _ _ t1) := view_term arg1 in
      Lam s (concretize t1)*)
    end
  end.