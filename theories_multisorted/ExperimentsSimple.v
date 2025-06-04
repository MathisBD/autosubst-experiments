From Prototype Require Import MPrelude MSig.

(*********************************************************************************)
(** *** Level one. *)
(*********************************************************************************)

Module O.
Section WithSig.
Context {sig : signature}.

(** Level one terms. *)

Inductive term : fin nsort -> Type :=
| T_var {s} : nat -> term s
| T_ctor {s} (c : fin (nctor s)) : args (ctor_type c) -> term s

with args : list arg_ty -> Type :=
| AL_nil : args []
| AL_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)

with arg : arg_ty -> Type :=
| A_base b : base_type b -> arg (AT_base b)
| A_term {s} : term s -> arg (AT_term s)
| A_bind {s s'} : term s' -> arg (AT_bind s s'). 

Derive Signature NoConfusion NoConfusionHom for term args arg.

(** Size of terms. *)

Equations term_size {s} : term s -> nat :=
term_size (T_var _) := 0 ;
term_size (T_ctor c al) := S (args_size al) ;

with args_size {tys} : args tys -> nat :=
args_size AL_nil := 0 ;
args_size (AL_cons a al) := S (arg_size a + args_size al)

with arg_size {ty} : arg ty -> nat :=
arg_size (A_base _ _) := 0 ;
arg_size (A_term t) := S (term_size t) ;
arg_size (A_bind t) := S (term_size t).

(** Well-founded induction on terms based on their size. *)

Section SizeInd.
  Context (P : forall s, term s -> Prop).

  Context (IH : forall s (t : term s), 
    (forall s' (t' : term s'), term_size t' < term_size t -> P s' t') -> 
    P s t).

  Lemma size_ind : forall s t, P s t.
  Proof.
  intros s t. remember (term_size t) as n eqn:E.
  revert s t E. induction n using Wf_nat.lt_wf_ind. intros s t ->.
  apply IH. intros s' t' Hlt. eapply H ; eauto.
  Qed.
End SizeInd.

(** Renamings. *)

(** Vector of renamings. *)
Definition ren_vec := vector ren nsort.

(** Apply a vector of renamings to a term. *)
Equations rename {s} (rv : ren_vec) (t : term s) : term s :=
rename rv (T_var i) := T_var (vector_nth s rv i) ;
rename rv (T_ctor c al) := T_ctor c (rename_args rv al)

with rename_args {tys : list arg_ty} (rv : ren_vec) (al : args tys) : args tys :=
rename_args rv AL_nil := AL_nil ;
rename_args rv (AL_cons a al) := AL_cons (rename_arg rv a) (rename_args rv al)

with rename_arg {ty : arg_ty} (rv : ren_vec) (a : arg ty) : arg ty :=
rename_arg rv (A_base b x) := A_base b x ;
rename_arg rv (A_term t) := A_term (rename rv t) ;
rename_arg rv (@A_bind s _ a) := A_bind (rename (vector_map_nth up_ren s rv) a).

End WithSig.
End O.

(*********************************************************************************)
(** *** Level zero. *)
(*********************************************************************************)

(** Types, terms, and values. *)

Unset Elimination Schemes. 

Inductive ty : Type :=
| var_ty : nat -> ty
| arr : ty -> ty -> ty
| all : ty -> ty.

Inductive tm : Type :=
| var_tm : nat -> tm
| app : tm -> tm -> tm
| tapp : tm -> ty -> tm
| vt : vl -> tm

with vl : Type :=
| var_vl : nat -> vl
| lam : ty -> tm -> vl
| tlam : tm -> vl.

Set Elimination Schemes.

Scheme ty_ind := Induction for ty Sort Prop.
Scheme tm_ind := Induction for tm Sort Prop 
  with vl_ind := Induction for vl Sort Prop.
Combined Scheme tm_vl_ind from tm_ind, vl_ind.

(** Renaming. *)

Fixpoint rename_ty (rty rtm rvl : ren) (t : ty) : ty :=
  match t with 
  | var_ty i => var_ty (rty i)
  | arr t1 t2 => arr (rename_ty rty rtm rvl t1) (rename_ty rty rtm rvl t2)
  | all t => all (rename_ty (up_ren rty) rtm rvl t)
  end.
  
Fixpoint rename_tm (rty rtm rvl : ren) (t : tm) : tm :=
  match t with 
  | var_tm i => var_tm (rtm i)
  | app t1 t2 => app (rename_tm rty rtm rvl t1) (rename_tm rty rtm rvl t2)
  | tapp t1 t2 => tapp (rename_tm rty rtm rvl t1) (rename_ty rty rtm rvl t2)
  | vt v => vt (rename_vl rty rtm rvl v)
  end
  
with rename_vl (rty rtm rvl : ren) (t : vl) : vl :=
  match t with 
  | var_vl i => var_vl (rvl i) 
  | lam t1 t2 => lam (rename_ty rty rtm rvl t1) (rename_tm rty rtm (up_ren rvl) t2)
  | tlam t => tlam (rename_tm (up_ren rty) rtm rvl t)
  end.

(*********************************************************************************)
(** *** Signature. *)
(*********************************************************************************)

Definition nbase_ := 0.

Definition base_type_ (b : fin nbase_) : Type :=
  vector_nth b [- -].

Definition nsort_ := 3.
Notation sty := (finO) (only parsing).
Notation stm := (finS finO) (only parsing).
Notation svl := (finS (finS finO)) (only parsing).

Definition nctor_ (s : fin nsort_) : nat :=
  vector_nth s [- 2 ; 3 ; 2 -].

Definition ctor_type_hvector : @hvector nsort_ (fun s => vector (list (@arg_ty nbase_ nsort_)) (nctor_ s)) :=
  let x := [- [ AT_term sty ; AT_term sty ] ; [ AT_bind sty sty ] -]%vector in
  let y := [- [ AT_term stm ; AT_term stm ] ; [ AT_term stm ; AT_term sty ] ; [ AT_term svl ] -]%vector in
  let z := [- [ AT_term sty ; AT_bind svl stm ] ; [ AT_bind sty stm ] -]%vector in
  [= x ; y ; z =].
  
Definition ctor_type_ (s : fin nsort_) (c : fin (nctor_ s)) : list (@arg_ty nbase_ nsort_) :=
  vector_nth c (hvector_nth s ctor_type_hvector).

Definition sig : signature := 
  Build_signature nbase_ base_type_ nsort_ nctor_ ctor_type_.

#[local] Existing Instance sig.

(*********************************************************************************)
(** *** Reification. *)
(*********************************************************************************)

Fixpoint reify_ty (t : ty) : O.term sty :=
  match t with 
  | var_ty i => O.T_var i
  | arr t1 t2 => 
      @O.T_ctor sig sty finO (O.AL_cons (O.A_term (reify_ty t1)) (O.AL_cons (O.A_term (reify_ty t2)) O.AL_nil))
  | all t => 
      @O.T_ctor sig sty (finS finO) (O.AL_cons (O.A_bind (reify_ty t)) O.AL_nil)
  end.

Fixpoint reify_tm (t : tm) : O.term stm :=
  match t with 
  | var_tm i => O.T_var i
  | app t1 t2 =>
      @O.T_ctor sig stm finO (O.AL_cons (O.A_term (reify_tm t1)) (O.AL_cons (O.A_term (reify_tm t2)) O.AL_nil))
  | tapp t1 t2 =>
      @O.T_ctor sig stm (finS finO) (O.AL_cons (O.A_term (reify_tm t1)) (O.AL_cons (O.A_term (reify_ty t2)) O.AL_nil))
  | vt t =>
      @O.T_ctor sig stm (finS (finS finO)) (O.AL_cons (O.A_term (reify_vl t)) O.AL_nil)
  end

with reify_vl (t : vl) : O.term svl :=
  match t with 
  | var_vl i => O.T_var i
  | lam t1 t2 =>
      @O.T_ctor sig svl finO (O.AL_cons (O.A_term (reify_ty t1)) (O.AL_cons (O.A_bind (reify_tm t2)) O.AL_nil))
  | tlam t =>
      @O.T_ctor sig svl (finS finO) (O.AL_cons (O.A_bind (reify_tm t)) O.AL_nil)
  end.

(*********************************************************************************)
(** *** Evaluation. *)
(*********************************************************************************)

Definition eval_sort (s : fin nsort) : Type :=
  vector_nth s [- ty ; tm ; vl -].

Definition eval_arg_ty (ty : @arg_ty nbase nsort) : Type :=
  match ty with 
  | AT_base b => base_type b 
  | AT_term s => eval_sort s
  | AT_bind _ s => eval_sort s
  end.

Fixpoint eval_arg_tys (tys : list (@arg_ty nbase nsort)) : Type :=
  match tys with 
  | [] => unit 
  | ty :: tys => eval_arg_ty ty * eval_arg_tys tys 
  end.

Definition eval_ctor_sty (c : fin (nctor sty)) : eval_arg_tys (ctor_type c) -> eval_sort sty :=
  let x '(t1, (t2, tt)) := arr t1 t2 in
  let y '(t, tt) := all t in 
  hvector_nth (T := fun c => eval_arg_tys (ctor_type c) -> eval_sort sty) c [= x ; y =].

Definition eval_ctor_stm (c : fin (nctor stm)) : eval_arg_tys (ctor_type c) -> eval_sort stm :=
  let x '(t1, (t2, tt)) := app t1 t2 in
  let y '(t1, (t2, tt)) := tapp t1 t2 in
  let z '(t, tt) := vt t in
  hvector_nth (T := fun c => eval_arg_tys (ctor_type c) -> eval_sort stm) c [= x ; y ; z =].

Definition eval_ctor_svl (c : fin (nctor svl)) : eval_arg_tys (ctor_type c) -> eval_sort svl :=
  let x '(t1, (t2, tt)) := lam t1 t2 in
  let y '(t, tt) := tlam t in
  hvector_nth (T := fun c => eval_arg_tys (ctor_type c) -> eval_sort svl) c [= x ; y =].

Definition eval_ctor (s : fin nsort) (c : fin (nctor s)) 
  (args : eval_arg_tys (ctor_type c)) : eval_sort s :=
  hvector_nth s (T := fun s => forall c : fin (nctor s), eval_arg_tys (ctor_type c) -> eval_sort s) 
    [= eval_ctor_sty ; eval_ctor_stm ; eval_ctor_svl =] c args.

Fixpoint eval {s} (t : O.term s) : eval_sort s :=
  match t in @O.term _ s0 return eval_sort s0 with 
  | @O.T_var _ s i => hvector_nth (T := eval_sort) s [= var_ty i ; var_tm i ; var_vl i =]
  | @O.T_ctor _ s c al => eval_ctor s c (eval_args al)
  end 

with eval_args {tys} (al : O.args tys) : eval_arg_tys tys :=
  match al with 
  | O.AL_nil => tt
  | O.AL_cons a al => (eval_arg a, eval_args al)
  end 

with eval_arg {ty} (a : O.arg ty) : eval_arg_ty ty :=
  match a with 
  | O.A_base b x => x 
  | O.A_term t => eval t 
  | O.A_bind t => eval t
  end.

(*********************************************************************************)
(** *** Proof of bijection. *)
(*********************************************************************************)

Lemma eval_reify_ty (t : ty) : eval (reify_ty t) = t.
Proof. induction t. all: cbn ; f_equal ; auto. Qed.

Lemma eval_reify_tm : 
  (forall t, eval (reify_tm t) = t) /\ (forall v, eval (reify_vl v) = v).
Proof. apply tm_vl_ind. all: intros ; cbn ; f_equal ; auto using eval_reify_ty. Qed.

(*********************************************************************************)
(** *** Custom induction principle on level one terms. *)
(*********************************************************************************)

Section CustomInd.
  #[local] Existing Instance sig.

  Context (P : forall s, O.term s -> Prop).
  
  Context (Hvar_ty : forall i, P sty (O.T_var i)).
  Context (Harr : forall t1 t2, P sty t1 -> P sty t2 -> 
    P sty (@O.T_ctor _ sty finO (O.AL_cons (O.A_term t1) (O.AL_cons (O.A_term t2) O.AL_nil)))).
  Context (Hall : forall t, P sty t -> 
    P sty (@O.T_ctor _ sty (finS finO) (O.AL_cons (O.A_bind t) O.AL_nil))).

  Context (Hvar_tm : forall i, P stm (O.T_var i)).
  Context (Happ : forall t1 t2, P stm t1 -> P stm t2 ->
    P stm (@O.T_ctor _ stm finO (O.AL_cons (O.A_term t1) (O.AL_cons (O.A_term t2) O.AL_nil)))).
  Context (Htapp : forall t1 t2, P stm t1 -> P sty t2 ->
    P stm (@O.T_ctor _ stm (finS finO) (O.AL_cons (O.A_term t1) (O.AL_cons (O.A_term t2) O.AL_nil)))).
  Context (Hvt : forall t, P svl t ->
    P stm (@O.T_ctor _ stm (finS (finS finO)) (O.AL_cons (O.A_term t) O.AL_nil))).

  Context (Hvar_vl : forall i, P svl (O.T_var i)).
  Context (Hlam : forall t1 t2, P sty t1 -> P stm t2 ->
    P svl (@O.T_ctor _ svl finO (O.AL_cons (O.A_term t1) (O.AL_cons (O.A_bind t2) O.AL_nil)))).
  Context (Htlam : forall t1, P stm t1 ->
    P svl (@O.T_ctor _ svl (finS finO) (O.AL_cons (O.A_bind t1) O.AL_nil))).
  
  Lemma custom_ind {s} : forall t : O.term s, P s t.
  Proof.
  revert s. apply O.size_ind. intros s t IH. (repeat depelim s) ; depelim t.
  - apply Hvar_ty.
  - repeat depelim c.
    + depelim a. depelim a1. depelim a2. depelim a. depelim a1. 
      apply Harr ; apply IH ; cbn ; lia.
    + depelim a. depelim a1. depelim a. 
      apply Hall ; apply IH ; cbn ; lia.
  - apply Hvar_tm.
  - repeat depelim c.
    + depelim a. depelim a. depelim a1. depelim a. depelim a1. 
      apply Happ ; apply IH ; cbn ; lia.
    + depelim a. depelim a. depelim a1. depelim a. depelim a1. 
      apply Htapp ; apply IH ; cbn ; lia.
    + depelim a. depelim a. depelim a1.
      apply Hvt ; apply IH ; cbn ; lia.
  - apply Hvar_vl.
  - repeat depelim c.
    + depelim a. depelim a. depelim a1. depelim a. depelim a1. 
      apply Hlam ; apply IH ; cbn ; lia.
    + depelim a. depelim a. depelim a1.
      apply Htlam ; apply IH ; cbn ; lia.
  Qed. 

End CustomInd.

(*********************************************************************************)
(** *** Transporting renamings. *)
(*********************************************************************************)

Definition ren_vec := (ren * (ren * ren))%type.

Definition eval_ren_vec (rv : O.ren_vec) : ren_vec :=
  (vector_nth finO rv, (vector_nth (finS finO) rv, vector_nth (finS (finS finO)) rv)).
  
(** Evaluate [O.rename s] into a concrete function such as [rename_ty] or [rename_tm]. *)
Definition eval_rename {s} (r : ren_vec) : eval_sort s -> eval_sort s :=
  let '(rty, (rtm, rvl)) := r in
  hvector_nth (T := fun s => eval_sort s -> eval_sort s) 
    s [= rename_ty rty rtm rvl ; rename_tm rty rtm rvl ; rename_vl rty rtm rvl =].

(*Ltac red_vector_nth :=
  repeat match goal with 
  | |- context [ vector_nth finO (vcons ?x ?xs) ] => 
    change (vector_nth finO (vcons x xs)) with x
  | |- context [ vector_nth (finS ?i) (vcons ?x ?xs) ] =>
    change (vector_nth (finS i) (vcons x xs)) with (vector_nth i xs)
  | |- context [ hvector_nth finO (hcons ?x ?xs) ] => 
    change (hvector_nth finO (hcons x xs)) with x
  | |- context [ hvector_nth (finS ?i) (hcons ?x ?xs) ] =>
    change (hvector_nth (finS i) (hcons x xs)) with (hvector_nth i xs)
  end ;
  cbn beta zeta iota.*)

#[export] Instance rename_ty_congr : Proper (point_eq ==> point_eq ==> point_eq ==> eq ==> eq) rename_ty.
Proof.
intros rty1 rty2 Hty rtm1 rtm2 Htm rvl1 rvl2 Hvl t1 t2 <-. 
induction t1 in rty1, rty2, rtm1, rtm2, rvl1, rvl2, Hty, Htm, Hvl |- * ; cbn.
- now rewrite Hty.
- f_equal ; auto.
- f_equal. apply IHt1 ; auto using congr_up_ren. 
Qed.

(** Push [eval] through renamings. *)
Lemma push_eval_rename {s} (rv : O.ren_vec) (t : O.term s) : 
  eval (O.rename rv t) = eval_rename (eval_ren_vec rv) (eval t).
Proof.
revert rv. pattern t. revert s t. apply custom_ind.
all: intros ; repeat depelim rv ; cbn.
- reflexivity. 
- f_equal.
  + apply H.
  + apply H0.
- f_equal. apply H.
- reflexivity.
- f_equal.
  + apply H.
  + apply H0.
- f_equal. 
  + apply H.
  + apply H0.
- f_equal. apply H.
- reflexivity.
- f_equal.
  + apply H.
  + apply H0.
- f_equal. apply H.
Qed.      

Axiom t1 t2 : ty.

Definition t : ty := arr t1 t2.
Definition t' : ty := rename_ty rshift rid rid t.

Definition s : @O.term sig sty := 
  @O.T_ctor sig sty finO (O.AL_cons (O.A_term (reify_ty t1)) (O.AL_cons (O.A_term (reify_ty t2)) O.AL_nil)).
Definition s' : @O.term sig sty := 
  O.rename [- rshift ; rid ; rid -]%vector s.

Lemma arr_congr : Proper (eq ==> eq ==> eq) arr.
Proof. now intros ? ? -> ? ? ->. Qed.

Definition p1 : eval s = t := 
  arr_congr _ _ (eval_reify_ty t1) _ _ (eval_reify_ty t2).

Definition p2 : eval s' = t' :=
  let x := push_eval_rename [- rshift ; rid ; rid -]%vector s in
  let y := rename_ty_congr rshift rshift peq_refl rid rid peq_refl rid rid peq_refl (eval s) t p1 in
  eq_trans x y.

    
