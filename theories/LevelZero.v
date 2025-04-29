From Prototype Require Import Prelude Sig.
From Prototype Require LevelOne LevelTwo LevelTwoIrred LevelTwoSimp.
Module P := Prelude.

(** Concrete terms, renamings and substitutions. *)

Inductive term :=
| Var : nat -> term
| App : term -> term -> term 
| Lam : string -> term -> term.

Fixpoint rename (t : term) (r : nat -> nat) : term :=
  match t with 
  | Var i => Var (r i)
  | App t1 t2 => App (rename t1 r) (rename t2 r)
  | Lam str t => Lam str (rename t (up_ren r))
  end.

Definition subst := nat -> term.

Definition srcomp (s : subst) (r : ren) : subst :=
  fun i => rename (s i) r.
  
Definition rscomp (r : ren) (s : subst) : subst :=
  fun i => s (r i).

Definition sid : subst :=
  fun i => Var i.

Definition sshift : subst :=
  fun i => Var (S i).

Definition scons (t : term) (s : subst) : subst :=
  fun i => match i with 0 => t | S i => s i end.

Definition up_subst (s : subst) : subst :=
  scons (Var 0) (srcomp s rshift).

Fixpoint substitute (t : term) (s : subst) : term :=
  match t with 
  | Var i => s i
  | App t1 t2 => App (substitute t1 s) (substitute t2 s)
  | Lam str t => Lam str (substitute t (up_subst s))
  end.

Definition scomp (s1 s2 : subst) : subst :=
  fun i => substitute (s1 i) s2.

(** Congruence lemmas. *)

Lemma congr_app {t1 t1' t2 t2'} :
  t1 = t1' -> t2 = t2' -> App t1 t2 = App t1' t2'.
Proof. intros -> ->. reflexivity. Qed.

Lemma congr_lam str {t t'} :
  t = t' -> Lam str t = Lam str t'.
Proof. intros ->. reflexivity. Qed.

Lemma congr_rename {t t' r r'} :
  t = t' -> r =₁ r' -> rename t r = rename t' r'.
Proof. 
intros <-. revert r r'. induction t ; intros r r' H ; cbn.
- auto.
- apply congr_app ; auto.
- apply congr_lam ; auto using congr_up_ren.
Qed.

Lemma congr_rscomp {r r' s s'} :
  r =₁ r' -> s =₁ s' -> rscomp r s =₁ rscomp r' s'.
Proof. intros H1 H2 i. unfold rscomp. setoid_rewrite H1. rewrite H2. reflexivity. Qed.

Lemma congr_srcomp {s s' r r'} :
  s =₁ s' -> r =₁ r' -> srcomp s r =₁ srcomp s' r'.
Proof. intros H1 H2 i. unfold srcomp. apply congr_rename ; auto. Qed.

Lemma congr_scons {t t' s s'} : 
  t = t' -> s =₁ s' -> scons t s =₁ scons t' s'.
Proof. intros -> H [|i] ; simpl ; auto. Qed.

Lemma congr_up_subst {s s'} :
  s =₁ s' -> up_subst s =₁ up_subst s'.
Proof. 
intros H. unfold up_subst. apply congr_scons ; auto. 
apply congr_srcomp ; easy.
Qed.

Lemma congr_substitute {t t' s s'} :
  t = t' -> s =₁ s' -> substitute t s = substitute t' s'.
Proof. 
intros <-. revert s s'. induction t ; intros s0 s0' H ; simpl ; auto.
- now erewrite IHt1, IHt2. 
- f_equal. apply IHt. now apply congr_up_subst.
Qed.

Lemma congr_scomp {s1 s1' s2 s2'} :
  s1 =₁ s1' -> s2 =₁ s2' -> scomp s1 s2 =₁ scomp s1' s2'.
Proof. intros H1 H2 i. cbv [scomp]. now apply congr_substitute. Qed.

(** Signature. *)

Inductive base := BString.
Definition denote_base (b : base) : Type := 
  match b with BString => string end.

Inductive ctor := CApp | CLam.
Definition ctor_type c : list (@arg_ty base) := 
  match c with 
  | CApp => [ AT_term ; AT_term ]
  | CLam => [ AT_base BString ; AT_bind AT_term ]
  end.

Module S.
Definition t := Build_signature base denote_base ctor ctor_type.
End S.

Module T := LevelTwoSimp.Make (S).
Module O := T.O.

(** Custom induction principle on level one terms. *)

(** Size of a level one expression. This is needed to prove a custom 
    induction principle for level one terms. *)
Equations esize {k} : O.expr k -> nat :=
esize (O.E_var _) := 0 ;
esize (O.E_ctor c al) := S (esize al) ;
esize O.E_al_nil := 0 ;
esize (O.E_al_cons a al) := S (esize a + esize al) ;
esize (O.E_abase _ _) := 0 ;
esize (O.E_aterm t) := S (esize t) ;
esize (O.E_abind a) := S (esize a).

Section TermInd.
  Context (P : O.expr Kt -> Prop).
  Context (H1 : forall i, P (O.E_var i)).
  Context (H2 : forall t1 t2, P t1 -> P t2 -> 
      P (O.E_ctor CApp (O.E_al_cons (O.E_aterm t1) (O.E_al_cons (O.E_aterm t2) O.E_al_nil)))).
  Context (H3 : forall str t, P t -> 
      P (O.E_ctor CLam (O.E_al_cons (O.E_abase BString str) (O.E_al_cons (O.E_abind (O.E_aterm t)) O.E_al_nil)))).

  Lemma term_ind' : forall t, P t.
  Proof.  
  apply PeanoNat.Nat.measure_induction with (f := esize).
  intros t IH. depelim t.
  - now apply H1.
  - depelim c ; simpl in *.
    + depelim t. depelim t1. depelim t2. depelim t2_1. depelim t2_2.
      apply H2 ; apply IH ; repeat (simp esize ; simpl) ; lia.
    + depelim t. depelim t1. depelim t2. depelim t2_1. depelim t2_2. depelim t2_1.
      apply H3. apply IH. repeat (simp esize ; simpl). lia.
  Qed.
End TermInd. 

(** Reification/evaluation functions. *)

(**

t -> t', p : eval t' = t

scomp s1 s2 -> scomp' s1' s2'

untyped lambda calculus (concrete)

level one (admissible subst) generic

level two (explicit subst) generic


*)

Fixpoint reify (t : term) : O.expr Kt :=
  match t with
  | Var i => O.E_var i
  | App t1 t2 =>
    O.E_ctor CApp 
      (O.E_al_cons (O.E_aterm (reify t1))
      (O.E_al_cons (O.E_aterm (reify t2))
       O.E_al_nil))
  | Lam str t =>
    O.E_ctor CLam 
      (O.E_al_cons (O.E_abase BString str)
      (O.E_al_cons (O.E_abind (O.E_aterm (reify t)))
       O.E_al_nil))
  end.

Definition sreify (s : subst) : O.subst :=
  fun i => reify (s i).
  
Fixpoint eval_arg (ty : arg_ty) : Type :=
  match ty with 
  | AT_base b => denote_base b 
  | AT_term => term 
  | AT_bind ty => eval_arg ty
  end.

Fixpoint eval_args (tys : list arg_ty) : Type :=
  match tys with 
  | [] => unit
  | ty :: tys => eval_arg ty * eval_args tys
  end. 

Definition eval_kind (k : kind) : Type :=
  match k with 
  | Kt => term
  | Ka ty => eval_arg ty
  | Kal tys => eval_args tys
  end.

Definition eval_ctor (c : ctor) : eval_args (ctor_type c) -> term :=
  match c return eval_args (ctor_type c) -> term with 
  | CApp => fun '(t1, (t2, _)) => App t1 t2 
  | CLam => fun '(str, (t, _)) => Lam str t
  end.

Fixpoint eval {k} (t : O.expr k) : eval_kind k :=
  match t in O.expr k0 return eval_kind k0 with 
  | O.E_var i => Var i 
  | O.E_ctor c al => eval_ctor c (eval al)
  | O.E_al_nil => tt
  | O.E_al_cons a al => (eval a, eval al)
  | O.E_abase b x => x 
  | O.E_aterm t => eval t 
  | O.E_abind a => eval a
  end. 

Definition seval (s : O.subst) : subst :=
  fun i => eval (s i).

(** Push [eval] inside terms. *)

Lemma eval_reify_inv (t : term) : 
  eval (reify t) = t.
Proof. induction t ; simpl ; f_equal ; auto. Qed.

Lemma seval_sreify_inv (s : LevelZero.subst) :
  seval (sreify s) =₁ s.
Proof. intros i ; cbv [seval sreify]. now rewrite eval_reify_inv. Qed.

Lemma eval_rename (t : O.expr Kt) (r : ren) :
  eval (O.rename t r) = rename (eval t) r.
Proof.
revert r ; induction t using term_ind' ; intros r.
- reflexivity.
- repeat (simp rename ; simpl). now rewrite IHt1, IHt2.
- repeat (simp rename ; simpl). now rewrite IHt.
Qed.   

Lemma eval_scons t s : 
  seval (O.scons t s) =₁ scons (eval t) (seval s).
Proof. intros [|i] ; reflexivity. Qed.

Lemma eval_srcomp s r : 
  seval (O.srcomp s r) =₁ srcomp (seval s) r.
Proof. intros i. cbv [seval srcomp O.srcomp]. now rewrite eval_rename. Qed. 

Lemma eval_up_subst s : 
  seval (O.up_subst s) =₁ up_subst (seval s).
Proof. 
unfold O.up_subst, up_subst. rewrite eval_scons. simpl. 
apply congr_scons ; [reflexivity|]. now rewrite eval_srcomp.
Qed.

Lemma eval_substitute (t : O.expr Kt) (s : O.subst) : 
  eval (O.substitute t s) = substitute (eval t) (seval s).
Proof.
revert t s. 
apply (@term_ind' (fun (t : O.expr Kt) => forall s, eval (O.substitute t s) = substitute (eval t) (seval s))).
- intros i s. simpl. simp substitute. reflexivity.
- intros t1 t2 H1 H2 s. repeat (simp substitute ; simpl). now rewrite H1, H2.
- intros str t H s. repeat (simp substitute ; simpl). rewrite H. f_equal.
  apply congr_substitute ; [reflexivity | now apply eval_up_subst].
Qed.

Lemma eval_scomp (s1 s2 : O.subst) :
  seval (O.scomp s1 s2) =₁ scomp (seval s1) (seval s2).
Proof. intros i. cbv [scomp O.scomp seval]. now rewrite eval_substitute. Qed.

Lemma eval_rscomp (r : P.ren) (s : O.subst) :
  seval (O.rscomp r s) =₁ rscomp r (seval s).
Proof. reflexivity. Qed.

(** Reification (Ltac). *)

(** Returns [(t', p)] such that [p : eval t' = t]. *)
Ltac2 rec reify (t : constr) : constr * constr :=
  lazy_match! t with 
  | Var ?i => constr:(O.E_var $i), constr:(@eq_refl _ (Var $i)) 
  | App ?t1 ?t2 => 
    let (t1', p1) := reify t1 in 
    let (t2', p2) := reify t2 in 
    let t' := constr:(
      O.E_ctor CApp 
        (O.E_al_cons (O.E_aterm $t1')
        (O.E_al_cons (O.E_aterm $t2')
         O.E_al_nil)))
    in 
    let p := constr:(congr_app $p1 $p2) in
    (t', p)
  | Lam ?str ?t1 =>
    let (t1', p1) := reify t1 in
    let t' := constr:(
      O.E_ctor CLam 
        (O.E_al_cons (O.E_abase BString $str)
        (O.E_al_cons (O.E_abind (O.E_aterm $t1'))
         O.E_al_nil)))
    in 
    let p := constr:(congr_lam $str $p1) in
    (t', p)
  | substitute ?t1 ?s =>
    let (t1', p1) := reify t1 in 
    let (s', p2) := reify_subst s in  
    let t' := constr:(O.substitute $t1' $s') in
    let p := constr:(
      transitivity (eval_substitute $t1' $s') (congr_substitute $p1 $p2)) 
    in
    (t', p)
  | ?t =>
    let t' := constr:(reify $t) in 
    let p := constr:(eval_reify_inv $t) in
    (t', p)
  end

(** Returns [(s', p)] such that [p : seval s' =₁ s]. *)
with reify_subst (s : constr) : constr * constr :=
  lazy_match! s with 
  | sshift => 
    constr:(O.sshift), constr:(@reflexivity subst point_eq _ sshift)
  | scons ?t ?s =>
    let (t', p1) := reify t in 
    let (s', p2) := reify_subst s in 
    constr:(O.scons $t' $s'), 
    constr:(transitivity (eval_scons $t' $s') (congr_scons $p1 $p2)) 
  | scomp ?s1 ?s2 =>
    let (s1', p1) := reify_subst s1 in 
    let (s2', p2) := reify_subst s2 in
    constr:(O.scomp $s1' $s2'),
    constr:(transitivity (eval_scomp $s1' $s2') (congr_scomp $p1 $p2)) 
  | ?s => 
    let s' := constr:(sreify $s) in 
    let p := constr:(seval_sreify_inv $s) in 
    (s', p)
  end.

(** Evaluation (Ltac). *)

(** Returns [(t, p)] such that [p : eval t' = t]. *)
Ltac2 rec eval (t' : constr) : constr * constr :=
  lazy_match! t' with 
  | O.E_var ?i => constr:(Var $i), constr:(@eq_refl _ (Var $i)) 
  | O.substitute ?t' ?s' => 
    let (t, p1) := eval t' in
    let (s, p2) := eval_subst s' in 
    constr:(substitute $t $s),
    constr:(transitivity (eval_substitute $t' $s') (congr_substitute $p1 $p2))
  | reify ?t => 
    t, constr:(eval_reify_inv $t)
  end

(** Returns [(s, p)] such that [p : seval s' =₁ s]. *)
with eval_subst (s' : constr) : constr * constr :=
  lazy_match! s' with 
  | O.scons ?t' ?s' =>
    let (t, p1) := eval t' in 
    let (s, p2) := eval_subst s' in 
    constr:(LevelZero.scons $t $s),
    constr:(transitivity (eval_scons $t' $s') (congr_scons $p1 $p2))
  | O.scomp ?s1' ?s2' => 
    let (s1, p1) := eval_subst s1' in 
    let (s2, p2) := eval_subst s2' in
    constr:(LevelZero.scomp $s1 $s2),
    constr:(transitivity (eval_scomp $s1' $s2') (congr_scomp $p1 $p2))
  | sreify ?s =>
    s, constr:(seval_sreify_inv $s)
  end.

(** Testing. *)

(*

t -> t'

reify (ltac) : zero -> one
reify t -> t', p : eval t' = t

eval (rocq) : one -> zero
reify (rocq) : zero -> one




eval t' = t


*)


(*Axiom t_ax : term.

Ltac2 Eval 
  let (t', p) := reify constr:(substitute t_ax (scons (Var 0) sshift)) in 
  constr:($p : eval $t' = substitute t_ax (scons (Var 0) sshift)).*)

Axiom x t : term.
Axiom s1 s2 : subst.

(*Definition left := substitute (substitute t (up_subst s1)) (scons x s2).
Definition right := substitute t (scons x (scomp s1 s2)).*)

Definition left := substitute (substitute t (scons x s1)) s2.
Definition right := substitute t (scons (substitute x s2) (scomp s1 s2)).

From Ltac2 Require Import Printf.

Ltac2 test_tac () : unit :=
  lazy_match! Control.goal () with 
  | @eq _ ?l0 ?r0 => 
    (* Reify zero -> one. *)
    let (l1, pl) := reify l0 in
    let (r1, pr) := reify r0 in
    rewrite <-$pl ;
    rewrite <-$pr ; 
    (* Reify one -> two. *)
    let e := T.empty_env () in
    let (e, l2) := T.reify_expr e l1 in 
    let (e, r2) := T.reify_expr e r1 in 
    let e := T.build_env e in
    change (eval (T.eeval $e $l2) = eval (T.eeval $e $r2)) ;
    (* Simplify. *)
    rewrite <-(T.esimp_sound $e $l2) ;
    rewrite <-(T.esimp_sound $e $r2)
    (* Eval two -> one. *)
    (*cbv [seval eeval seval_functional eeval_functional
         qeval reval qeval_functional reval_functional 
         assign_ren assign_qnat assign_term assign_subst nth
         esimp ssimp esimp_functional ssimp_functional 
         substitute scomp substitute_functional scomp_functional sren
         substitute_aux scomp_aux rsimp rsimp_functional qsimp_functional
         sapply qsimp sapply_functional rscomp_functional 
         sapply_aux] *)
    (*cbv [T.eeval T.seval T.seval_functional T.eeval_functional
         T.qeval T.reval T.qeval_functional T.reval_functional 
         T.assign_ren T.assign_qnat T.assign_term T.assign_subst List.nth
         T.esimp T.ssimp T.esimp_functional T.ssimp_functional 
         T.substitute T.scomp T.substitute_functional T.scomp_functional T.sren
         T.substitute_aux T.scomp_aux T.rsimp T.rsimp_functional T.qsimp_functional
         T.sapply T.qsimp T.sapply_functional T.rscomp_functional 
         T.sapply_aux]*)
  | _ => Control.throw_invalid_argument "not an equality"
  end.

Lemma aux k e (t t' : T.expr k) : 
  t = t' -> eval (T.eeval e t) = eval (T.eeval e t').
Proof. now intros ->. Qed.

Lemma test : left = right.
Proof.
unfold left, right.
ltac2:(test_tac ()).
apply aux. vm_cast_no_check (@eq_refl (T.expr Kt)).

(*ltac2:(
  lazy_match! Control.goal () with 
  | eval ?l1 = _ =>
    let (_, p) := eval l1 in 
    rewrite $p
  end).*)
Admitted.