From Prototype Require Import Prelude Sig LevelOne.

Module Make (S : Sig).
Module O := LevelOne.Make (S).

(** Meta-variables are represented by an index (a natural). *)
Definition mvar := nat.

(*********************************************************************************)
(** *** Quoted naturals and explicit renamings. *)
(*********************************************************************************)

(** Quoted natural. *)
Inductive qnat :=
| Q_zero : qnat 
| Q_succ : qnat -> qnat
| Q_plus : qnat -> qnat -> qnat 
| Q_ren : ren -> qnat -> qnat 
| Q_mvar : mvar -> qnat

(** Explicit renaming. *)
with ren :=
| R_shift : qnat -> ren
| R_cons : qnat -> ren -> ren
| R_comp : ren -> ren -> ren 
| R_mvar : mvar -> ren.

Notation "'Q_one'" := (Q_succ Q_zero).

(*********************************************************************************)
(** *** Expressions and explicit substitutions. *)
(*********************************************************************************)

(** Notations for expressions with known kinds. *)
Reserved Notation "'term'" (at level 0).
Reserved Notation "'arg' ty" (at level 0, ty at level 0).
Reserved Notation "'args' tys" (at level 0, tys at level 0).

(** Expressions over an abstract signature. 
    Expressions are indexed by a kind: this is to avoid having too many 
    distinct constructors for instantiation. *)
Inductive expr : kind -> Type :=

(** Variable term constructor (de Bruijn index). *)
| E_tvar : qnat -> term
(** Non-variable term constructor, applied to a list of arguments. *)
| E_tctor : forall c, args (ctor_type S.t c) -> term

(** Empty argument list. *)
| E_al_nil : args []
(** Non-empty argument list. *)
| E_al_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)

(** Base argument (e.g. bool or string). *)
| E_abase : forall b, denote_base S.t b -> arg (AT_base b)
(** Term argument. *)
| E_aterm : term -> arg AT_term
(** Binder argument. *)
| E_abind {ty} : arg ty -> arg (AT_bind ty)

(** Instantiate an expressions with a renaming. *)
| E_ren {k} : expr k -> ren -> expr k
(** Instantiate an expressions with a substitution. *)
| E_subst {k} : expr k -> subst -> expr k
(** Term metavariable. We don't need argument or argument-list metavariables. *)
| E_mvar : mvar -> term

with subst :=
(** Shift substitution. *)
| S_shift : qnat -> subst
(** Substitution expansion. *)
| S_cons : term -> subst -> subst
(** Substitution composition. *)
| S_comp : subst -> subst -> subst
(** View a renaming as a substitution. *)
| S_ren : ren -> subst
(** Substitution metavariable. *)
| S_mvar : mvar -> subst

where "'term'" := (expr Kt)
  and "'arg' ty" := (expr (Ka ty))
  and "'args' tys" := (expr (Kal tys)).

(** Notations for common expressions. *)

(*Notation "'↑ᵣ' k" := (R_shift k) (at level 0, k at level 0).
Notation "i '.ᵣ' r" := (R_cons i r) (at level 60, right associativity).
Notation "r1 '>>ᵣ' r2" := (R_comp r1 r2) (at level 50, left associativity).

Notation "'↑ₛ' k" := (E_sshift k) (at level 0, k at level 0).
Notation "t '.ₛ' s" := (E_scons t s) (at level 60, right associativity).
Notation "s1 '>>ₛ' s2" := (E_scomp s1 s2) (at level 50, left associativity).

Notation "t '[ᵣ' s ']'" := (E_rinst t s) (at level 15, s at level 0, no associativity).
Notation "t '[ₛ' s ']'" := (E_sinst t s) (at level 15, s at level 0, no associativity).*)

(** The identity renaming. *)
Notation "'rid'" := (R_shift Q_zero).

(** The identity substitution. *)
Notation "'sid'" := (S_shift Q_zero).

(** Lift a renaming through a binder. *)
(*Definition up_ren (r : ren) : ren :=
  R_cons Q_zero (R_comp r (R_shift Q_one)).

(** Lift a substitution through a binder. *)
Definition up_subst (s : subst) : subst :=
  S_cons (E_tvar Q_zero) (S_comp s (S_shift Q_one)).*)

(*********************************************************************************)
(** *** Evaluation. *)
(*********************************************************************************)

(** An environment is a mapping from meta-variables to level one expressions. *)
Record env := 
  { assign_qnat : mvar -> nat
  ; assign_ren : mvar -> O.ren 
  ; assign_term : mvar -> O.expr Kt
  ; assign_subst : mvar -> O.subst }. 

Section Evaluation.
  Context (e : env).

  Equations eval_qnat : qnat -> nat :=
  eval_qnat Q_zero := 0 ;
  eval_qnat (Q_succ i) := S (eval_qnat i) ;
  eval_qnat (Q_plus x y) := eval_qnat x + eval_qnat y ;
  eval_qnat (Q_ren r i) := eval_ren r (eval_qnat i) ;
  eval_qnat (Q_mvar x) := e.(assign_qnat) x
  
  with eval_ren : ren -> O.ren :=
  eval_ren (R_shift i) := O.rshift (eval_qnat i) ;
  eval_ren (R_cons i r) := O.rcons (eval_qnat i) (eval_ren r) ;
  eval_ren (R_comp r1 r2) := O.rcomp (eval_ren r1) (eval_ren r2) ;
  eval_ren (R_mvar x) := e.(assign_ren) x.

  Equations eval_expr {k} : expr k -> O.expr k :=
  eval_expr (E_tvar i) := O.E_var (eval_qnat i) ;
  eval_expr (E_tctor c al) := O.E_ctor c (eval_expr al) ;
  eval_expr E_al_nil := O.E_al_nil ;
  eval_expr (E_al_cons a al) := O.E_al_cons (eval_expr a) (eval_expr al) ;
  eval_expr (E_abase b x) := O.E_abase b x ;
  eval_expr (E_aterm t) := O.E_aterm (eval_expr t) ;
  eval_expr (E_abind a) := O.E_abind (eval_expr a) ;
  eval_expr (E_ren e r) := O.rename (eval_expr e) (eval_ren r) ;
  eval_expr (E_subst e s) := O.substitute (eval_expr e) (eval_subst s) ;
  eval_expr (E_mvar x) := e.(assign_term) x
  
  with eval_subst : subst -> O.subst :=
  eval_subst (S_shift k) := O.sshift (eval_qnat k) ;
  eval_subst (S_cons t s) := O.scons (eval_expr t) (eval_subst s) ;
  eval_subst (S_comp s1 s2) := O.scomp (eval_subst s1) (eval_subst s2) ;
  eval_subst (S_ren r) := O.rscomp (eval_ren r) O.E_var ;
  eval_subst (S_mvar x) := e.(assign_subst) x.

End Evaluation.
 
(*********************************************************************************)
(** *** Reification. *)
(*********************************************************************************)

Ltac2 rec nat_of_int (x : int) : constr := 
  if Int.le x 0 then constr:(0)
  else let y := nat_of_int (Int.sub x 1) in constr:(S $y).

(** Reification environment. *)
Ltac2 Type env := 
  { qnat_mvars : constr list 
  ; ren_mvars : constr list
  ; term_mvars : constr list
  ; subst_mvars : constr list }.

Ltac2 empty_env () := 
  { qnat_mvars := [] ; ren_mvars := [] ; term_mvars := [] ; subst_mvars := [] }.

Ltac2 add_qnat_mvar (t : constr) (e : env) : env :=
  { qnat_mvars := List.append (e.(qnat_mvars)) [t] 
  ; ren_mvars := e.(ren_mvars)
  ; term_mvars := e.(term_mvars)
  ; subst_mvars := e.(subst_mvars) }.
  
Ltac2 add_ren_mvar (t : constr) (e : env) : env :=
  { qnat_mvars := e.(qnat_mvars) 
  ; ren_mvars := List.append (e.(ren_mvars)) [t]
  ; term_mvars := e.(term_mvars)
  ; subst_mvars := e.(subst_mvars) }.

Ltac2 add_term_mvar (t : constr) (e : env) : env :=
  { qnat_mvars := e.(qnat_mvars) 
  ; ren_mvars := e.(ren_mvars)
  ; term_mvars := List.append (e.(term_mvars)) [t]
  ; subst_mvars := e.(subst_mvars) }.

Ltac2 add_subst_mvar (t : constr) (e : env) : env :=
  { qnat_mvars := e.(qnat_mvars) 
  ; ren_mvars := e.(ren_mvars)
  ; term_mvars := e.(term_mvars)
  ; subst_mvars := List.append (e.(subst_mvars)) [t] }.

Ltac2 rec reify_nat (e : env) (t : constr) : env * constr := 
  lazy_match! t with 
  | 0 => e, constr:(Q_zero)
  | S ?i =>
    let (e, i) := reify_nat e i in 
    e, constr:(Q_succ $i)
  | ?x + ?y => 
    let (e, x) := reify_nat e x in 
    let (e, y) := reify_nat e y in 
    e, constr:(Q_plus $x $y)
  | ?r ?i =>
    let (e, r) := reify_ren e r in
    let (e, i) := reify_nat e i in
    e, constr:(Q_ren $r $i)
  | ?i => 
    let idx := nat_of_int (List.length (e.(qnat_mvars))) in
    let e := add_qnat_mvar i e in
    e, constr:(Q_mvar $idx)
  end

with reify_ren (e : env) (t : constr) : env * constr :=
  lazy_match! t with 
  | O.rshift ?k =>
    let (e, k) := reify_nat e k in 
    e, constr:(R_shift $k) 
  | O.rcons ?i ?r =>
    let (e, i) := reify_nat e i in 
    let (e, r) := reify_ren e r in 
    e, constr:(R_cons $i $r)
  | O.rcomp ?r1 ?r2 =>
    let (e, r1) := reify_ren e r1 in 
    let (e, r2) := reify_ren e r2 in 
    e, constr:(R_comp $r1 $r2)
  | ?r => 
    let idx := nat_of_int (List.length (e.(ren_mvars))) in 
    let e := add_ren_mvar r e in
    e, constr:(R_mvar $idx)
  end.

Ltac2 rec reify_expr (e : env) (t : constr) : env * constr :=
  lazy_match! t with 
  | O.E_var ?i => 
    let (e, i) := reify_nat e i in
    e, constr:(E_tvar $i)
  | O.E_ctor ?c ?al => 
    let (e, al) := reify_expr e al in
    e, constr:(E_tctor $c $al)
  | O.E_al_nil => e, constr:(E_al_nil)
  | O.E_al_cons ?a ?al => 
    let (e, a) := reify_expr e a in
    let (e, al) := reify_expr e al in
    e, constr:(E_al_cons $a $al)
  | O.E_abase ?b ?x => e, constr:(E_abase $b $x)
  | O.E_aterm ?t => 
    let (e, t) := reify_expr e t in
    e, constr:(E_aterm $t)
  | O.E_abind ?a =>
    let (e, a) := reify_expr e a in
    e, constr:(E_abind $a)
  | O.rename ?t ?r =>
    let (e, t) := reify_expr e t in
    let (e, r) := reify_ren e r in
    e, constr:(E_ren $t $r)
  | O.substitute ?t ?s =>
    let (e, t) := reify_expr e t in
    let (e, s) := reify_subst e s in
    e, constr:(E_subst $t $s)
  | ?t => 
    let idx := nat_of_int (List.length (e.(term_mvars))) in
    let e := add_term_mvar t e in
    e, constr:(E_mvar $idx)
  end

with reify_subst (e : env) (s : constr) : env * constr :=
  lazy_match! s with 
  | O.sid => e, constr:(sid)
  | O.sshift ?k => 
    let (e, k) := reify_nat e k in 
    e, constr:(S_shift $k)
  | O.scons ?t ?s =>
    let (e, t) := reify_expr e t in 
    let (e, s) := reify_subst e s in 
    e, constr:(S_cons $t $s)
  | O.scomp ?s1 ?s2 =>
    let (e, s1) := reify_subst e s1 in 
    let (e, s2) := reify_subst e s2 in 
    e, constr:(S_comp $s1 $s2)
  | O.srcomp ?s ?r =>
    let (e, s) := reify_subst e s in 
    let (e, r) := reify_ren e r in
    e, constr:(S_comp $s (S_ren $r))
  | O.rscomp ?r ?s =>
    let (e, r) := reify_ren e r in
    let (e, s) := reify_subst e s in 
    e, constr:(S_comp (S_ren $r) $s)
  | ?s => 
    let idx := nat_of_int (List.length (e.(subst_mvars))) in
    let e := add_subst_mvar s e in
    e, constr:(S_mvar $idx)
  end.

(*********************************************************************************)
(** *** Normal forms. *)
(*********************************************************************************)

(** Reducible quoted natural. *)
Inductive qred : qnat -> Prop :=
| QR_succ x : qred x -> qred (Q_succ x)
| QR_plus x y : qred x \/ qred y -> qred (Q_plus x y)
| QR_ren r x : rred r \/ qred x -> qred (Q_ren r x)

| QR_plus_zero_l x : qred (Q_plus x Q_zero)
| QR_plus_zero_r x : qred (Q_plus Q_zero x)
| QR_plus_plus_l x y z : qred (Q_plus (Q_plus x y) z)
| QR_plus_succ_l x y : qred (Q_plus (Q_succ x) y)
| QR_plus_succ_r x y : qred (Q_plus x (Q_succ y))
| QR_ren_ren r1 r2 i : qred (Q_ren r1 (Q_ren r2 i))
| QR_ren_shift k i : qred (Q_ren (R_shift k) i)
| QR_rcons_zero i r : qred (Q_ren (R_cons i r) Q_zero)
| QR_rcons_succ i r k : qred (Q_ren (R_cons i r) (Q_succ k))

(** Reducible renaming. *)
with rred : ren -> Prop :=
| RR_shift k : qred k -> rred (R_shift k)
| RR_cons i r : qred i \/ rred r -> rred (R_cons i r)
| RR_comp r1 r2 : rred r1 \/ rred r2 -> rred (R_comp r1 r2)

| RR_rid_l r : rred (R_comp rid r)
| RR_rid_r r : rred (R_comp r rid)
| RR_comp_l r1 r2 r3 : rred (R_comp (R_comp r1 r2) r3)

| RR_cons_l i r1 r2 : rred (R_comp (R_cons i r1) r2)
| RR_shift_1 k1 k2 : rred (R_comp (R_shift k1) (R_shift k2))
| RR_shift_2 k1 k2 r : rred (R_comp (R_shift k1) (R_comp (R_shift k2) r))
| RR_shift_cons k i r : rred (R_comp (R_shift (Q_succ k)) (R_cons i r)).

Hint Constructors qred : core.
Hint Constructors rred : core.

(** Normal form quoted natural. *)
Definition qnorm x := ~ qred x.

(** Normal form renaming. *)
Definition rnorm r := ~ rred r.

(*********************************************************************************)
(** *** Normal form properties. *)
(*********************************************************************************)

Definition is_qsucc x := exists x', x = Q_succ x'.
Definition is_qplus x := exists y z, x = Q_plus y z.
Definition is_qren x := exists r y, x = Q_ren r y.

Definition is_rshift r := exists k, r = R_shift k.
Definition is_rcons r := exists i r', r = R_cons i r'.
Definition is_rcomp r := exists r1 r2 , r = R_comp r1 r2.
Definition is_rshift_l r := exists k r', r = R_comp (R_shift k) r'.

Lemma qnorm_succ x :
  qnorm (Q_succ x) <-> qnorm x.
Proof.
split ; intros H H' ; apply H ; clear H.
- now constructor.
- now inv H'.
Qed.

Lemma qnorm_plus x y : 
  qnorm (Q_plus x y) <-> 
    qnorm x /\ qnorm y /\
    x <> Q_zero /\ y <> Q_zero /\
    ~is_qsucc x /\ ~is_qsucc y /\
    ~is_qplus x.
Proof.
split.
- intros H. split7 ; intros H' ; apply H ; clear H.
  + constructor ; auto.
  + constructor ; auto.
  + subst. now constructor.
  + subst. now constructor.
  + destruct H' as (x' & ->). now constructor.
  + destruct H' as (y' & ->). now constructor.
  + destruct H' as (x1 & x2 & ->). now constructor.
- intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) H. inv H ; try easy.
  + destruct H8 ; auto.
  + apply H7. eexists ; eauto.
  + apply H5. eexists ; eauto.
  + apply H6. eexists ; eauto.
Qed.

Lemma rnorm_shift k : 
  rnorm (R_shift k) <-> qnorm k.
Proof. 
split ; intros H H' ; apply H ; clear H.
- now constructor.
- now inv H'.
Qed.

Lemma rnorm_cons i r : 
  rnorm (R_cons i r) <-> qnorm i /\ rnorm r.
Proof.
split.
- intros H. split ; intros H' ; apply H.
  all: constructor ; auto.
- intros [H1 H2] H. inv H. destruct H3 ; auto.
Qed.

Lemma rnorm_mvar_l m r : 
  rnorm (R_comp (R_mvar m) r) <-> rnorm r /\ r <> rid.
Proof.
split.
- intros H. split.
  + intros H'. apply H ; clear H. apply RR_comp. now right.
  + intros H' ; subst. apply H. now constructor. 
- intros (H & H') H''. inv H''.
  + destruct H1 ; easy.
  + easy.
Qed.      

Lemma rnorm_shift_l k r : 
  rnorm (R_comp (R_shift k) r) <-> 
    qnorm k /\ 
    rnorm r /\ 
    k <> Q_zero /\ 
    ~is_rshift r /\ 
    ~is_rshift_l r /\
    ~(is_qsucc k /\ is_rcons r).
Proof.
split.
- intros H. split6 ; intros H' ; apply H ; clear H.
  + constructor. left. now constructor.
  + constructor. now right.
  + subst. now constructor.
  + destruct H' as [k' ->]. now constructor.
  + destruct H' as (k' & r' & ->). now constructor. 
  + destruct H' as [(k' & ->) (i & r' & ->)]. now constructor.   
- intros (H1 & H2 & H3) H. inv H ; try easy.
  + destruct H4 ; auto. now inv H0.
  + destruct H3 as (_ & H3 & _) ; apply H3. eexists ; eauto.
  + destruct H3 as (_ & H3 & _) ; apply H3. eexists ; eauto.
  + destruct H3 as (_ & _ & H3 & _) ; apply H3. eexists ; eauto. 
  + destruct H3 as (_ & _ & H3) ; apply H3. split ; eexists ; eauto.
Qed. 

(*********************************************************************************)
(** *** Normalization. *)
(*********************************************************************************)

(** We define the size of expressions, which is used to prove 
    termination of some simplification functions by well founded induction. *)

(** Size of a quoted natural. *)
Equations qsize : qnat -> nat :=
qsize Q_zero := 0 ;
qsize (Q_succ x) := S (qsize x) ;
qsize (Q_plus x y) := S (qsize x + qsize y) ;
qsize (Q_ren r x) := S (rsize r + qsize x) ;
qsize (Q_mvar _) := 0

(** Size of a renaming. *)
with rsize : ren -> nat :=
rsize (R_shift k) := S (qsize k) ;
rsize (R_cons i r) := S (qsize i + rsize r) ;
rsize (R_comp r1 r2) := S (rsize r1 + rsize r2) ;
rsize (R_mvar _) := 0.

(** Add two normal form quoted naturals, where the left hand side
    is neutral (i.e. is not Q_zero, Q_succ or Q_plus). *)
Equations qplus_neutral : qnat -> qnat -> qnat :=
qplus_neutral n Q_zero := n ;
qplus_neutral n (Q_succ x) := Q_succ (qplus_neutral n x) ;
qplus_neutral n x := Q_plus n x.

Lemma qsize_qplus_neutral x y : 
  qsize (qplus_neutral x y) <= S (qsize x + qsize y).
Proof. funelim (qplus_neutral x y) ; simp qsize ; lia. Qed.
#[global] Hint Rewrite qsize_qplus_neutral : qsize.

Lemma qplus_neutral_sound e x y : 
  eval_qnat e (qplus_neutral x y) = eval_qnat e x + eval_qnat e y.
Proof.
funelim (qplus_neutral x y) ; simp eval_qnat ; try lia.
rewrite H. lia.
Qed.
#[global] Hint Rewrite qplus_neutral_sound : eval_qnat.

Lemma qplus_neutral_nf n x :
  n <> Q_zero -> ~is_qsucc n -> ~is_qplus n -> qnorm n -> qnorm x -> qnorm (qplus_neutral n x).
Proof.
intros H1 H2 H3 H4 H5. funelim (qplus_neutral n x) ; clear Heqcall ; try easy.
- rewrite qnorm_succ in *. now apply H.
- rewrite qnorm_plus in *. split7 ; try easy.  
  + now rewrite qnorm_plus.
  + intros (k & Hk). inv Hk.
- rewrite qnorm_plus. split7 ; try easy. intros (k & Hk). inv Hk.
- rewrite qnorm_plus. split7 ; try easy. intros (k & Hk). inv Hk.
Qed.  

(** Add two normal form quoted naturals. *)
Equations qplus : qnat -> qnat -> qnat :=
qplus Q_zero y := y ;
qplus (Q_succ x) y := Q_succ (qplus x y) ;
qplus (Q_plus x y) z := qplus x (qplus y z) ;
qplus x y := qplus_neutral x y.

Lemma qsize_qplus x y : 
  qsize (qplus x y) <= S (qsize x + qsize y).
Proof. funelim (qplus x y) ; simp qsize ; lia. Qed.
#[global] Hint Rewrite qsize_qplus : qsize.

Lemma qplus_sound e x y :
  eval_qnat e (qplus x y) = eval_qnat e x + eval_qnat e y.
Proof.
funelim (qplus x y) ; simp eval_qnat ; try lia.
+ rewrite H. lia.
+ rewrite H0, H. lia.
Qed.  
#[global] Hint Rewrite qplus_sound : eval_qnat.

Lemma qplus_nf x y : 
  qnorm x -> qnorm y -> qnorm (qplus x y).
Proof.
intros H1 H2. funelim (qplus x y) ; clear Heqcall ; try easy.
- rewrite qnorm_succ in *. now apply H.
- rewrite qnorm_plus in H1. apply H0 ; try easy. now apply H.
- apply qplus_neutral_nf ; try easy.
  + intros (k & Hk) ; inv Hk.
  + intros (x1 & x2 & H) ; inv H.
- apply qplus_neutral_nf ; try easy.
  + intros (k & Hk) ; inv Hk.
  + intros (x1 & x2 & H) ; inv H.
Qed.

(** Helper function for [rdrop]. *)
Equations do_shift : qnat -> ren -> ren :=
do_shift Q_zero r := r ;
do_shift k r := R_comp (R_shift k) r.

Lemma do_shift_sound e k r : 
  eval_ren e (do_shift k r) =₁ O.rcomp (O.rshift (eval_qnat e k)) (eval_ren e r).
Proof. funelim (do_shift k r) ; triv. Qed.
#[global] Hint Rewrite do_shift_sound : eval_ren.

Lemma do_shift_nf_aux k r :
  k <> Q_zero -> ~is_rshift r -> ~is_rshift_l r -> ~is_rcons r -> 
  qnorm k -> rnorm r -> rnorm (R_comp (R_shift k) r).
Proof. intros H1 H2 H3 H4 H5 H6. rewrite rnorm_shift_l ; split6 ; easy. Qed.
    
Lemma do_shift_nf1 k r :
  ~is_rshift r -> ~is_rshift_l r -> ~is_rcons r -> 
  qnorm k -> rnorm r -> rnorm (do_shift k r).
Proof. 
intros. funelim (do_shift k r) ; 
solve [ easy | now apply do_shift_nf_aux ]. 
Qed. 

Lemma do_shift_nf2 k r :
  ~is_qsucc k -> is_rcons r -> 
  qnorm k -> rnorm r -> rnorm (do_shift k r).
Proof.
intros H1 (i & r' & ->) H2 H3. funelim (do_shift k _) ; try easy.  
all: rewrite rnorm_shift_l ; split6 ; try easy.
all: solve [ intros (? & H') ; inv H' | intros (? & ? & H') ; inv H'].
Qed.

(** Drop the [k] first elements in a normal form renaming [r]. *)
Equations rdrop (k : qnat) (r : ren) : ren by wf (qsize k + rsize r) lt :=
rdrop k (R_shift k') := R_shift (qplus k k') ;
rdrop k (R_mvar m) := do_shift k (R_mvar m) ;
rdrop k (R_cons i r) with k => {
  | Q_succ k' => rdrop k' r ;
  | _ => do_shift k (R_cons i r) } ;
rdrop k (R_comp (R_shift k') r) := rdrop (qplus k k') r ;
rdrop k r := do_shift k r.

Next Obligation. simp qsize. lia. Qed.
Next Obligation. 
apply PeanoNat.Nat.le_lt_trans with (m := S (qsize k + qsize k') + rsize r).
- apply Arith_base.add_le_mono_r_proj_l2r. simp qsize. reflexivity.
- lia.
Qed.

Lemma rdrop_sound e k r : 
  eval_ren e (rdrop k r) =₁ O.rcomp (O.rshift (eval_qnat e k)) (eval_ren e r).
Proof.
funelim (rdrop k r) ; simp eval_ren eval_qnat ; triv.
- now rewrite O.rshift_plus.
- rewrite H. simp eval_qnat. now rewrite <-O.rcomp_assoc, O.rshift_plus.
Qed.
#[global] Hint Rewrite rdrop_sound : eval_ren.

Lemma is_rshift_comp r1 r2 : ~is_rshift (R_comp r1 r2).
Proof. intros (k & H) ; inv H. Qed.
#[global] Hint Immediate is_rshift_comp : core.

Lemma is_rshift_cons r1 r2 : ~is_rshift (R_cons r1 r2).
Proof. intros (k & H) ; inv H. Qed.
#[global] Hint Immediate is_rshift_cons : core.

Lemma is_rshift_mvar m : ~is_rshift (R_mvar m).
Proof. intros (? & H) ; inv H. Qed.
#[global] Hint Immediate is_rshift_mvar : core.

Lemma is_rshift_l_mvar m r : ~is_rshift_l (R_comp (R_mvar m) r).
Proof. intros (? & ? & H) ; inv H. Qed.
#[global] Hint Immediate is_rshift_l_mvar : core.

Lemma is_rcons_comp r1 r2 : ~is_rcons (R_comp r1 r2).
Proof. intros (? & ? & H) ; inv H. Qed.
#[global] Hint Immediate is_rcons_comp : core.

Lemma rdrop_nf k r : 
  qnorm k -> rnorm r -> rnorm (rdrop k r).
Proof with triv.
intros H1 H2. funelim (rdrop k r)...
- rewrite rnorm_shift in *. now apply qplus_nf.
- apply H.
  + rewrite rnorm_shift_l in H2. now apply qplus_nf.
  + now rewrite rnorm_shift_l in H2.
- exfalso... 
- exfalso...
- rewrite rnorm_mvar_l in H2. destruct H2 as [H2 H3]. 
  apply do_shift_nf1... now rewrite rnorm_mvar_l.
- apply do_shift_nf1...
  + intros (k' & r' & H') ; inv H'.
  + intros (k' & r' & H') ; inv H'.
- rewrite qnorm_succ in H1. rewrite rnorm_cons in H2. now apply H.
- apply do_shift_nf2...
  + intros (k' & H') ; inv H'.
  + eexists ; eauto.
- apply do_shift_nf2...
  + intros (k' & H') ; inv H'.
  + eexists. eauto.
- apply do_shift_nf2...
  + intros (k' & H') ; inv H'.
  + eexists. eauto.
Qed.

(** We define by mutual well founded induction:
    - composition of normal form renamings. 
    - application of a normal form renaming to a normal form quoted nat. 

    Since [Equations] does not support mutual well founded recursion, 
    we encode it using non-mutual well founded recursion.
*)


Ltac unfold_all :=
  repeat match goal with 
  | [ x := _ |- _ ] => unfold x in * ; clear x
  end.

(** Helper function for [rcomp]. *)
Equations rcomp_aux : ren -> ren -> ren :=
rcomp_aux r rid := r ;
rcomp_aux r1 r2 := R_comp r1 r2. 

Lemma rcomp_aux_nf r1 r2 :
  rnorm r1 -> rnorm r2 -> (r2 <> rid -> rnorm (R_comp r1 r2)) -> rnorm (rcomp_aux r1 r2).
Proof. 
intros H1 H2 H3. funelim (rcomp_aux r1 r2) ; triv.
all: apply H3 ; intros H ; inv H.
Qed.  

Inductive proto : Type -> Type -> Type -> Set := 
| proto_rapply : proto ren qnat qnat 
| proto_rcomp : proto ren ren ren.

Equations psize {A B C} : proto A B C -> A -> B -> nat :=
psize proto_rapply r i := rsize r + qsize i ;
psize proto_rcomp r1 r2 := rsize r1 + rsize r2.

Equations? rapply_rcomp {A B C} (p : proto A B C) (x : A) (y : B) : C by wf (psize p x y) lt := 
rapply_rcomp proto_rapply (R_shift k) i := qplus k i ;
rapply_rcomp proto_rapply (R_cons i1 r) i with i => {
  | Q_zero => i1
  | Q_succ i' => rapply_rcomp proto_rapply r i'
  | Q_ren r' i' => Q_ren (rapply_rcomp proto_rcomp r' (R_cons i1 r)) i'
  | i' => Q_ren (R_cons i1 r) i' } ;
rapply_rcomp proto_rapply (R_comp (R_shift k) r) i :=
  rapply_rcomp proto_rapply r (qplus k i) ;
rapply_rcomp proto_rapply r i with i => {
  | Q_ren r' i' => Q_ren (rapply_rcomp proto_rcomp r' r) i'
  | i' => Q_ren r i' } ;
  
rapply_rcomp proto_rcomp (R_shift k) r := rdrop k r ;
rapply_rcomp proto_rcomp (R_cons i r1) r2 := 
  R_cons (rapply_rcomp proto_rapply r2 i) (rapply_rcomp proto_rcomp r1 r2) ;
rapply_rcomp proto_rcomp (R_comp (R_mvar m) r1) r2 := 
  rcomp_aux (R_mvar m) (rapply_rcomp proto_rcomp r1 r2) ;
rapply_rcomp proto_rcomp (R_comp (R_shift k) r1) r2 := 
  rdrop k (rapply_rcomp proto_rcomp r1 r2) ;
rapply_rcomp proto_rcomp r1 r2 := rcomp_aux r1 r2.

Proof.
all: unfold_all ; simp qsize psize ; try lia.
generalize (qsize_qplus k i). lia.
Qed.

Lemma qnorm_ren_mvar m i : 
  qnorm (Q_ren (R_mvar m) i) <-> qnorm i /\ ~is_qren i.
Proof.
split.
- intros H. split ; intros H' ; apply H ; clear H.
  + apply QR_ren ; triv.
  + destruct H' as (? & ? & ->). now constructor.
- intros (H1 & H2) H3. inv H3.
  + destruct H0 ; triv.
  + apply H2. eexists ; eauto.
Qed.     

Lemma qnorm_ren r i : 
  qnorm (Q_ren r i) <-> 
    rnorm r /\ qnorm i /\ ~is_rshift r /\ ~is_qren i /\
    (is_rcons r -> i <> Q_zero /\ ~is_qsucc i).
Proof.
split.
- intros H. split5.
  + intros H' ; apply H ; clear H. apply QR_ren. now left.
  + intros H' ; apply H ; clear H. apply QR_ren. now right.
  + intros H' ; apply H ; clear H. destruct H' as (k & ->). now constructor.
  + intros H' ; apply H ; clear H. destruct H' as (? & ? & ->). now constructor.
  + intros (? & ? & ->). split ; intros H'' ; apply H ; clear H.
    * subst. now constructor.
    * destruct H'' as (? & H''). subst. now constructor.      
- intros (H1 & H2 & H3 & H4 & H5) H. inv H.
  + destruct H6 ; triv.
  + apply H4. eexists ; eauto.
  + apply H3. eexists ; eauto.
  + enough (Q_zero <> Q_zero) by auto. apply H5. eexists ; eauto.
  + enough (~is_qsucc (Q_succ k)).
    { apply H0. eexists ; eauto. }
    apply H5. eexists ; eauto.
Qed.

Lemma rapply_rcomp_nf : forall A B C (p : proto A B C) (x : A) (y : B),
  (fun A B C (p : proto A B C) =>
    match p in proto A0 B0 C0 return A0 -> B0 -> C0 -> Prop with 
    | proto_rapply => fun r i res => rnorm r -> qnorm i -> qnorm res
    | proto_rcomp => fun r1 r2 res => rnorm r1 -> rnorm r2 -> rnorm res
    end) A B C p x y (rapply_rcomp p x 
    y).
Proof.
apply rapply_rcomp_elim.
- intros k i H1 H2. rewrite rnorm_shift in H1. now apply qplus_nf.
- intros k r i H1 H2 H3. rewrite rnorm_shift_l in H2. apply H1 ; triv.
  now apply qplus_nf.
- intros k r H1 H2. rewrite rnorm_shift in H1. now apply rdrop_nf.
- intros i r1 r2 H1 H2 H3 H4. rewrite rnorm_cons in *. split.
  + now apply H1. 
  + now apply H2. 
- intros k r1 r2 H1 H2 H3. rewrite rnorm_shift_l in H2. 
  apply rdrop_nf ; triv. now apply H1.
- intros i r1 r2 r3 H1 H2. exfalso. apply H1. now constructor.
- intros r0 r1 r2 r3 H1 H2. exfalso. apply H1. now constructor.       
- intros m r1 r2 H1 H2 H3. rewrite rnorm_mvar_l in H2. apply rcomp_aux_nf ; triv.
  + now apply H1.
  + intros H. rewrite rnorm_mvar_l. split ; triv. now apply H1.
- intros m r H1 H2. apply rcomp_aux_nf ; triv. now rewrite rnorm_mvar_l.
- intros i r i' -> H _. now rewrite rnorm_cons in H.
- intros i1 r i2 i3 H1 -> H2 H3. rewrite rnorm_cons in H2.
  rewrite qnorm_succ in H3. now apply H1.
- intros i1 r ? i2 i3 -> H1 H2. intros H. inv H. now destruct H3.
- intros i1 r ? r' i' H1 -> H2 H3. rewrite qnorm_ren in *.
   

End Make.

(** Testing. *)

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

Module T := Make (S).
Import T.

Axiom n : nat.
Axiom m : nat.
Axiom r : O.ren.

Definition left := 
  O.E_ctor CApp 
    (O.E_al_cons (O.E_aterm (O.E_var (S (r (n + S m)) + n))) 
    (O.E_al_cons (O.E_aterm (O.E_var 1)) 
     O.E_al_nil)).
Definition right := O.E_var n.

From Ltac2 Require Import Printf.

Ltac2 rec coq_list (ty : constr) (xs : constr list) : constr :=
  match xs with 
  | [] => constr:(@nil $ty)
  | x :: xs =>
    let xs := coq_list ty xs in 
    constr:(@cons $ty $x $xs)
  end.

Ltac2 test_tac () : unit :=
  lazy_match! Control.goal () with 
  | @eq (O.expr Kt) ?l ?r => 
    let (e, l') := reify_expr (empty_env ()) l in 
    printf "%t" l' ;
    let e1 := coq_list constr:(nat) (e.(qnat_mvars)) in 
    let e2 := coq_list constr:(O.ren) (e.(ren_mvars)) in 
    let e3 := coq_list constr:(O.expr Kt) (e.(term_mvars)) in 
    let e4 := coq_list constr:(O.subst) (e.(subst_mvars)) in 
    printf "QNAT ENV %t" e1 ;
    printf "REN ENV %t" e2 ;
    printf "TERM ENV %t" e3 ;
    printf "SUBST ENV %t" e4 ;
    change 
      (eval_expr
        (fun idx => List.nth idx $e1 0) 
        (fun idx => List.nth idx $e2 O.rid) 
        (fun idx => List.nth idx $e3 (O.E_var 0))
        (fun idx => List.nth idx $e4 O.sid) 
        $l' = $r)
  | _ => Control.throw_invalid_argument "not an equality on level one terms"
  end.

Lemma test : left = right.
Proof.
unfold left, right.
ltac2:(test_tac ()).
cbv [eval_qnat eval_qnat_functional eval_ren_functional 
     eval_expr eval_expr_functional nth].
Admitted.
  
(*********************************************************************************)
(** *** Simplification. *)
(*********************************************************************************)

(** Apply a renaming to a quoted natural. *)
Equations rapply : ren -> qnat -> qnat :=
rapply (R_shift k) i := qplus k i ;
rapply (R_cons k _) Q_zero := k ;
rapply (R_cons _ r) (Q_succ i) := rapply r i ;
rapply (R_comp r1 r2) i := rapply r2 (rapply r1 i) ;
rapply r i := Q_mvar (eval_ren r (eval_qnat i)).

Lemma rapply_sound r i : 
  eval_qnat (rapply r i) = eval_ren r (eval_qnat i).
Proof. 
funelim (rapply r i) ; simp eval_qnat eval_ren ; try solve [ auto ].
rewrite H0, H. reflexivity.
Qed.
#[global] Hint Rewrite rapply_sound : eval_qnat.

(** Tail of a renaming. *)
Equations rtail : ren -> ren := 
rtail (R_shift k) := R_shift (Q_succ k) ;
rtail (R_cons _ r) := r ;
rtail (R_comp (R_shift k) r) := R_comp (R_shift (Q_succ k)) r ;
rtail r := R_comp (R_shift Q_one) r.

Lemma rtail_sound r : 
  eval_ren (rtail r) =₁ O.rcomp (O.rshift 1) (eval_ren r).
Proof. 
funelim (rtail r) ; simp eval_ren eval_qnat ; try easy.
- now rewrite O.rshift_succ_l.
- repeat rewrite <-O.rcomp_assoc. now rewrite O.rshift_succ_l.
Qed. 
#[global] Hint Rewrite rtail_sound : eval_ren.    

(** Drop the first [k] elements in a renaming. *)
Equations rdrop : qnat -> ren -> ren :=
rdrop Q_zero r := r ;
rdrop (Q_succ k) r := rtail (rdrop k r) ;
rdrop (Q_mvar k) r := R_comp (R_shift (Q_mvar k)) r.

Lemma rdrop_sound k r : 
  eval_ren (rdrop k r) =₁ O.rcomp (O.rshift (eval_qnat k)) (eval_ren r).
Proof.
funelim (rdrop k r) ; simp eval_ren eval_qnat ; try easy.
rewrite H. now rewrite <-O.rcomp_assoc, O.rshift_succ_l.
Qed.  
#[global] Hint Rewrite rdrop_sound : eval_ren.    
    
(** Compose two renamings. *)
Equations rcomp : ren -> ren -> ren :=
rcomp (R_shift k) r := rdrop k r ;
rcomp (R_cons i r1) r2 := R_cons (rapply r2 i) (rcomp r1 r2) ;
rcomp (R_comp r1 r2) r3 := R_comp r1 (rcomp r2 r3) ;
rcomp r1 r2 := R_comp r1 r2.

Lemma rcomp_sound r1 r2 : 
  eval_ren (rcomp r1 r2) =₁ O.rcomp (eval_ren r1) (eval_ren r2).
Proof.
funelim (rcomp r1 r2) ; simp eval_ren eval_qnat ; try easy.
- now rewrite O.rcomp_rcons_distrib, H.
- rewrite H. now repeat rewrite O.rcomp_assoc.
Qed.
#[global] Hint Rewrite rcomp_sound : eval_ren.    

(** Apply a normal form substitution to a de Bruijn index. *)
Equations sapply : subst -> qnat -> term :=
sapply (S_shift k) i := E_tvar (qplus k i) ;
sapply (S_cons t _) Q_zero := t ;
sapply (S_cons _ s) (Q_succ i) := sapply s i ;
sapply (S_comp (S_shift k) s) i := sapply s (qplus k i) ;
sapply (S_comp (S_ren r) s) i := sapply s (rapply r i) ;
sapply (S_ren r) i := E_tvar (rapply r i) ;
sapply s i := E_subst (E_tvar i) s.  

Lemma sapply_sound s i : 
  eval_expr (sapply s i) = eval_subst s (eval_qnat i).
Proof. funelim (sapply s i) ; simp eval_expr eval_qnat in * ;  easy. Qed.
    
(** Lift a renaming through a binder. *)
Equations rup : ren -> ren :=
rup r := R_cons Q_zero (rcomp r (R_shift Q_one)).

Lemma rup_sound r : eval_ren (rup r) =₁ O.up_ren (eval_ren r).
Proof. simp rup eval_ren. reflexivity. Qed.

(** Instantiate an expressions with a renaming. *)
Equations rinst {k} : nf_expr k -> nf_ren -> nf_expr k :=
rinst (E_tvar i) r := E_tvar (rapply r i) ;
rinst (E_tctor c al) r := E_tctor c (rinst al r) ;
rinst E_al_nil _ := E_al_nil ;
rinst (E_al_cons a al) r := E_al_cons (rinst a r) (rinst al r) ;
rinst (E_abase b x) _ := E_abase b x ;
rinst (E_aterm t) r := E_aterm (rinst t r) ;
rinst (E_abind a) r := E_abind (rinst a (rup r)) ;

rinst (E_ren t r1) r2 := E_ren t (rcomp r1 r2) ;
rinst (E_subst t s) r := E_subst t (srcomp s r)

rinst t r := E_ren t r

(*rinst (E_ren_mvar x r1) r2 := E_ren_mvar x (rcomp r1 r2) ;
rinst (E_subst_mvar x s) r := E_subst_mvar (srcomp s r) ;
rinst (E_subst_var i s) r := apply_subst (srcomp s r) i *)

(** Compose a substitution with a renaming. *)
with srcomp : nf_subst -> nf_ren -> nf_subst :=
srcomp (N_sshift k) r := N_sren (rdrop k r) ;
srcomp (N_scons t s) r := N_scons (rinst t r) (srcomp s r) ;
srcomp (N_scomp k xs s) r := N_scomp k xs (srcomp s r) ; 
srcomp (N_sren r1) r2 := N_sren (rcomp r1 r2).






(*********************************************************************************)
(** *** Normal forms. *)
(*********************************************************************************)

(** The goal of normal forms is not to precisely capture the structure
    of simplified terms/substitutions: rather, they add some structure 
    above plain terms/substitutions, while still remaining simple to work with.
    
    In particular, normal forms are not unique, and all functions 
    [term -> nf_term] are not equivalent. *)

(** Normal form renamings: the left hand side of a composition
    can't be a cons or a composition. *)
Inductive nf_ren : Type :=
(** [NR_shift k] represents [R_shift k]. *)
| NR_shift : qnat -> nf_ren
(** [NR_cons i r] represents [R_cons i r]. *)
| NR_cons : qnat -> nf_ren -> nf_ren 
(** [NR_comp_shift k r] represents [R_comp (R_shift k) r]. *)
| NR_comp_shift : qnat -> nf_ren -> nf_ren 
(** [NR_comp_mvar x r] represents [R_comp (R_mvar x) r]. *)
| NR_comp_mvar : O.ren -> nf_ren -> nf_ren 
(** [NR_mvar x] represents [R_mvar x]. *)
| NR_mvar : O.ren -> nf_ren.

Reserved Notation "'nf_term'" (at level 0).
Reserved Notation "'nf_arg' ty" (at level 0, ty at level 0).
Reserved Notation "'nf_args' tys" (at level 0, tys at level 0).

(** Normal form expression: the hand side of an instantiation
    (renaming/substitution) can only be a meta-variable or a de Bruijn index. *)
Inductive nf_expr : kind -> Type :=
| NE_tvar : qnat -> nf_term
| NE_tctor : forall c, nf_args (ctor_type S.t c) -> nf_term
| NE_al_nil : nf_args []
| NE_al_cons {ty tys} : nf_arg ty -> nf_args tys -> nf_args (ty :: tys)
| NE_abase : forall b, denote_base S.t b -> nf_arg (AT_base b)
| NE_aterm : nf_term -> nf_arg AT_term
| NE_abind {ty} : nf_arg ty -> nf_arg (AT_bind ty)
| NE_mvar {k} : mvar k -> nf_expr k
(** Renaming/substitution blocked on a metavariable. *)
| NE_ren_mvar {k} : mvar k -> nf_ren -> nf_expr k
| NE_subst_mvar {k} : mvar k -> nf_subst -> nf_expr k
(** Renaming/susbtitution blocked on a variable. *)
(*| NE_ren_var : qnat -> nf_ren -> nf_term*)
| NE_subst_var : qnat -> nf_subst -> nf_term

(** Normal form substitutions: the left hand side of a composition
    can't be a cons or a composition. *)
with nf_subst : Type :=
| NS_shift : qnat -> nf_subst 
| NS_cons : nf_term -> nf_subst -> nf_subst 
| NS_comp_shift : qnat -> nf_subst -> nf_subst 
| NS_comp_ren : nf_ren -> nf_subst -> nf_subst 
| NS_comp_mvar : O.subst -> nf_subst -> nf_subst 
| NS_ren : nf_ren -> nf_subst
| NS_mvar : O.subst -> nf_subst

where "'nf_term'" := (nf_expr Kt)
  and "'nf_arg' ty" := (nf_expr (Ka ty))
  and "'nf_args' tys" := (nf_expr (Kal tys)).

Equations eval_nf_ren : nf_ren -> O.ren :=
eval_nf_ren (NR_shift k) := O.rshift (eval_qnat k) ;
eval_nf_ren (NR_cons i r) := O.rcons (eval_qnat i) (eval_nf_ren r) ;
eval_nf_ren (NR_comp_shift k r) := O.rcomp (O.rshift (eval_qnat k)) (eval_nf_ren r) ;
eval_nf_ren (NR_comp_mvar x r) := O.rcomp x (eval_nf_ren r) ;
eval_nf_ren (NR_mvar x) := x.

Equations eval_nf_expr {k} : nf_expr k -> O.expr (eval_kind k) :=
eval_nf_expr (NE_tvar i) := O.E_var (eval_qnat i) ;
eval_nf_expr (NE_tctor c al) := O.E_ctor c (eval_nf_expr al) ;
eval_nf_expr NE_al_nil := O.E_al_nil ;
eval_nf_expr (NE_al_cons a al) := O.E_al_cons (eval_nf_expr a) (eval_nf_expr al) ;
eval_nf_expr (NE_abase b x) := O.E_abase b x ;
eval_nf_expr (NE_aterm t) := O.E_aterm (eval_nf_expr t) ;
eval_nf_expr (NE_abind a) := O.E_abind (eval_nf_expr a) ;
eval_nf_expr (NE_mvar x) := x ;
eval_nf_expr (NE_ren_mvar x r) := O.rename x (eval_nf_ren r) ;
eval_nf_expr (NE_subst_mvar x s) := O.substitute x (eval_nf_subst s) ;
(*eval_nf_expr (NE_ren_var i r) := O.E_var (eval_nf_ren r (eval_qnat i)) ;*)
eval_nf_expr (NE_subst_var i s) := eval_nf_subst s (eval_qnat i) 

with eval_nf_subst : nf_subst -> O.subst :=
eval_nf_subst (NS_shift k) := O.sshift (eval_qnat k) ;
eval_nf_subst (NS_cons t s) := O.scons (eval_nf_expr t) (eval_nf_subst s) ;
eval_nf_subst (NS_comp_shift k s) := O.scomp (O.sshift (eval_qnat k)) (eval_nf_subst s) ;
eval_nf_subst (NS_comp_ren r s) := O.rscomp (eval_nf_ren r) (eval_nf_subst s) ;
eval_nf_subst (NS_comp_mvar xs s) := O.scomp xs (eval_nf_subst s) ;
eval_nf_subst (NS_ren r) := O.rscomp (eval_nf_ren r) O.E_var ;
eval_nf_subst (NS_mvar xs) := xs.

(*********************************************************************************)
(** *** Simplification. *)
(*********************************************************************************)

(** Apply a normal form renaming to a quoted natural. *)
Equations rapply : nf_ren -> qnat -> qnat :=
rapply (NR_shift k) i := qplus k i ;
rapply (NR_cons k _) Q_zero := k ;
rapply (NR_cons _ r) (Q_succ i) := rapply r i ;
rapply (NR_comp_shift k r) i := rapply r (qplus k i) ;
rapply (NR_comp_mvar x r) i := rapply r (Q_mvar (x (eval_qnat i))) ;
rapply r i := Q_mvar (eval_nf_ren r (eval_qnat i)).

Lemma rapply_sound r i : 
  eval_qnat (rapply r i) = eval_nf_ren r (eval_qnat i).
Proof. 
funelim (rapply r i) ; simp eval_qnat eval_nf_ren ; try solve [ auto ].
rewrite H. simp eval_qnat. reflexivity.
Qed.
#[global] Hint Rewrite rapply_sound : eval_qnat.

(** Tail of a normal form renaming. *)
Equations rtail : nf_ren -> nf_ren := 
rtail (NR_shift k) := NR_shift (Q_succ k) ;
rtail (NR_cons _ r) := r ;
rtail (NR_comp_shift k r) := NR_comp_shift (Q_succ k) r ;
rtail r := NR_comp_shift Q_one r.

Lemma rtail_sound r : 
  eval_nf_ren (rtail r) =₁ O.rcomp (O.rshift 1) (eval_nf_ren r).
Proof. 
funelim (rtail r) ; simp eval_nf_ren eval_qnat ; try easy.
- now rewrite O.rshift_succ_l.
- repeat rewrite <-O.rcomp_assoc. now rewrite O.rshift_succ_l.
Qed. 
#[global] Hint Rewrite rtail_sound : eval_nf_ren.    

(** Drop the first [k] elements in a normal form renaming. *)
Equations rdrop : qnat -> nf_ren -> nf_ren :=
rdrop Q_zero r := r ;
rdrop (Q_succ k) r := rtail (rdrop k r) ;
rdrop (Q_mvar k) r := NR_comp_shift (Q_mvar k) r.

Lemma rdrop_sound k r : 
  eval_nf_ren (rdrop k r) =₁ O.rcomp (O.rshift (eval_qnat k)) (eval_nf_ren r).
Proof.
funelim (rdrop k r) ; simp eval_nf_ren eval_qnat ; try easy.
rewrite H. now rewrite <-O.rcomp_assoc, O.rshift_succ_l.
Qed.  
#[global] Hint Rewrite rdrop_sound : eval_nf_ren.    
    
(** Compose two normal form renamings. *)
Equations rcomp : nf_ren -> nf_ren -> nf_ren :=
rcomp (NR_shift k) r := rdrop k r ;
rcomp (NR_cons i r1) r2 := NR_cons (rapply r2 i) (rcomp r1 r2) ;
rcomp (NR_comp_shift k r1) r2 := NR_comp_shift k (rcomp r1 r2) ;
rcomp (NR_comp_mvar xr r1) r2 := NR_comp_mvar xr (rcomp r1 r2) ;
rcomp (NR_mvar xr) r := NR_comp_mvar xr r.

Lemma rcomp_sound r1 r2 : 
  eval_nf_ren (rcomp r1 r2) =₁ O.rcomp (eval_nf_ren r1) (eval_nf_ren r2).
Proof.
funelim (rcomp r1 r2) ; simp eval_nf_ren eval_qnat ; try easy.
- now rewrite O.rcomp_rcons_distrib, H.
- rewrite H. now repeat rewrite O.rcomp_assoc.
- rewrite H. now rewrite O.rcomp_assoc. 
Qed.
#[global] Hint Rewrite rcomp_sound : eval_nf_ren.    

(** Apply a normal form substitution to a de Bruijn index. *)
Equations sapply : nf_subst -> qnat -> nf_term :=
sapply (NS_shift k) i := NE_tvar (qplus k i) ;
sapply (NS_cons t _) Q_zero := t ;
sapply (NS_cons _ s) (Q_succ i) := sapply s i ;
sapply (NS_comp_shift k s) i := sapply s (qplus k i) ;
sapply (NS_comp_mvar xs s) i := sapply s (NE_subst_var i (NS_mvar xs)) ;
sapply (NS_comp_ren r s) i := sapply s (rapply r i) ;
sapply (NS_ren r) i := NE_tvar (rapply r i) ;
sapply s i := NE_subst_var i s.  

Lemma sapply_sound s i : eval_nf (sapply s i) = eval_nf s i.
Proof. 
funelim (sapply s i) ; simp eval_nf ; try reflexivity.
- now rewrite H.
- now rewrite rapply_sound.
Qed.    

(** Lift a normal form renaming through a binder. *)
Equations rup : nf_ren -> nf_ren :=
rup r := NR_cons Q_zero (rcomp r (NR_shift Q_one)).

Lemma rup_sound r : eval_nf_ren (rup r) =₁ O.up_ren (eval_nf_ren r).
Proof. simp rup eval_nf_ren. reflexivity. Qed.

(** Instantiate a normal form expressions with a normal form renaming. *)
Equations rinst {k} : nf_expr k -> nf_ren -> nf_expr k :=
rinst (NE_tvar i) r := NE_tvar (rapply r i) ;
rinst (NE_tctor c al) r := NE_tctor c (rinst al r) ;
rinst NE_al_nil _ := NE_al_nil ;
rinst (NE_al_cons a al) r := NE_al_cons (rinst a r) (rinst al r) ;
rinst (NE_abase b x) _ := NE_abase b x ;
rinst (NE_aterm t) r := NE_aterm (rinst t r) ;
rinst (NE_abind a) r := NE_abind (rinst a (rup r)) ;
rinst (NE_mvar x) r := NE_ren_mvar x r ;
rinst (NE_ren_mvar x r1) r2 := NE_ren_mvar x (rcomp r1 r2) ;
rinst (NE_subst_mvar x s) r := NE_subst_mvar (srcomp s r) ;
rinst (NE_subst_var i s) r := apply_subst (srcomp s r) i 

(** Compose a normal form substitution with a normal form renaming. *)
with srcomp : nf_subst -> nf_ren -> nf_subst :=
srcomp (N_sshift k) r := N_sren (rdrop k r) ;
srcomp (N_scons t s) r := N_scons (rinst t r) (srcomp s r) ;
srcomp (N_scomp k xs s) r := N_scomp k xs (srcomp s r) ; 
srcomp (N_sren r1) r2 := N_sren (rcomp r1 r2).

Lemma rinst_srcomp_sound_aux : 
  (forall k (t : nf_expr (K1 k)) r, 
    eval_nf (rinst t r) = O.rename (eval_nf t) (eval_nf r)) *
  (forall s r, 
    eval_nf (srcomp s r) =₁ fun i => O.rename (eval_nf s i) (eval_nf r)).
Proof.
apply rinst_elim with 
  (P := fun k (t : nf_expr (K1 k)) (r : nf_ren) (res : nf_expr (K1 k))  => 
    eval_nf res = O.rename (eval_nf t) (eval_nf r))
  (P0 := fun (s : nf_subst) (r : nf_ren) (res : nf_subst) =>
    eval_nf res =₁ fun i => O.rename (eval_nf s i) (eval_nf r)).
all: try (intros ; now simp eval_nf).
- intros c al r H. simp eval_nf. rewrite H. now simp rename.
- intros ty tys a al r H1 H2. simp eval_nf rename. now rewrite H1, H2.
- intros t r H. simp eval_nf rename. now rewrite H.
- intros ty a r H. simp eval_nf rename. now rewrite H, rup_sound.
- intros k xt r1 r2. destruct k ; simp eval_nf ; now rewrite O.ren_ren.
- intros k xt s r H. destruct k ; simp eval_nf ; now rewrite H, O.subst_ren.
- intros i xs s r H. simp eval_nf substitute. cbv [O.scomp]. 
  now rewrite H, O.subst_ren.
- intros k r. simp eval_nf. intros i. rewrite rdrop_sound. reflexivity.
- intros t s r H1 H2. simp eval_nf. rewrite H1, H2. intros [|i] ; reflexivity.
- intros k xs s r H. simp eval_nf. rewrite H. intros i. cbv [O.scomp O.sshift].
  simp substitute. now rewrite O.subst_ren.
- intros r1 r2. simp eval_nf. intros i. simp rename. now rewrite rcomp_sound.
Qed.

Lemma rinst_sound k (t : nf_expr (K1 k)) r :   
  eval_nf (rinst t r) = O.rename (eval_nf t) (eval_nf r).
Proof. now apply rinst_srcomp_sound_aux. Qed.

Lemma srcomp_sound s r :
  eval_nf (srcomp s r) =₁ fun i => O.rename (eval_nf s i) (eval_nf r).
Proof. now apply rinst_srcomp_sound_aux. Qed.

(** Tail of a normal form substitution. *)
Equations stail : nf_subst -> nf_subst :=
stail (N_sshift k) := N_sshift (S k) ;
stail (N_scons t s) := s ;
stail (N_scomp k xs s) := N_scomp (S k) xs s ;
stail (N_sren r) := N_sren (rtail r).

Lemma stail_sound s : eval_nf (stail s) =₁ O.scomp (O.sshift 1) (eval_nf s).
Proof. 
funelim (stail s) ; simp eval_nf.
- now rewrite O.sshift_succ_l.
- now rewrite O.sshift_scons.
- repeat rewrite <-O.scomp_assoc. now rewrite O.sshift_succ_l.
- intros i. now rewrite rtail_sound.
Qed.

(** Drop the first [k] elements in a normal form substitution. *)
Equations sdrop : nat -> nf_subst -> nf_subst :=
sdrop 0 s := s ;
sdrop (S k) s := stail (sdrop k s).

Lemma sdrop_sound k s : eval_nf (sdrop k s) =₁ O.scomp (O.sshift k) (eval_nf s).
Proof.
funelim (sdrop k s) ; simp eval_nf.
- now rewrite O.scomp_sid_l.
- rewrite stail_sound, H. now rewrite <-O.scomp_assoc, O.sshift_succ_l.
Qed.  

(** Lift a normal form substitution through a binder. *)
Equations sup : nf_subst -> nf_subst :=
sup s := N_scons (N_tvar 0) (srcomp s (N_rshift 1)).

Lemma sup_sound s : eval_nf (sup s) =₁ O.up_subst (eval_nf s).
Proof. simp sup eval_nf. unfold O.up_subst. now rewrite srcomp_sound. Qed.

(** Compose a normal form renaming with a normal form substitution. *)
Equations rscomp : nf_ren -> nf_subst -> nf_subst :=
rscomp (N_rshift k) s := sdrop k s ;
rscomp (N_rcons i r) s := N_scons (sapply s i) (rscomp r s) ;
rscomp (N_rcomp k xr r) s := N_scomp k (fun i => O.E_var (xr i)) (rscomp r s).

Lemma rscomp_sound r s : 
  eval_nf (rscomp r s) =₁ fun i => eval_nf s (eval_nf r i).
Proof.
funelim (rscomp r s) ; simp eval_nf.
- now rewrite sdrop_sound.
- rewrite sapply_sound, H. intros [|] ; reflexivity.
- now rewrite H.
Qed.     

(** Instantiate a normal form expression with a normal form substitution. *)
Equations sinst {k} (t : nf_expr (K1 k)) (s : nf_subst) : nf_expr (K1 k) by struct t :=
sinst (N_tvar i) s := sapply s i ;
sinst (N_tctor c al) s := N_tctor c (sinst al s) ;
sinst N_al_nil _ := N_al_nil ;
sinst (N_al_cons a al) s := N_al_cons (sinst a s) (sinst al s) ;
sinst (N_abase b x) _ := N_abase b x ;
sinst (N_aterm t) s := N_aterm (sinst t s) ;
sinst (N_abind a) s := N_abind (sinst a (sup s)) ;
sinst (N_rinst_l xt r) s := N_sinst_l xt (rscomp r s) ;
sinst (N_sinst_l xt s1) s2 := N_sinst_l xt (scomp s1 s2) ;
sinst (N_rinst_r i xr r) s := N_sinst_r i (fun i => O.E_var (xr i)) (rscomp r s) ;
sinst (N_sinst_r i xs s1) s2 := N_sinst_r i xs (scomp s1 s2)

(** Compose two normal form substitutions. *)
with scomp (s1 : nf_subst) (s2 : nf_subst) : nf_subst by struct s1 :=
scomp (N_sshift k) s := sdrop k s ;
scomp (N_scons t s1) s2 := N_scons (sinst t s2) (scomp s1 s2) ;
scomp (N_scomp k xs s1) s2 := N_scomp k xs (scomp s1 s2) ; 
scomp (N_sren r) s := rscomp r s.

Lemma sinst_scomp_sound_aux : 
  (forall k (t : nf_expr (K1 k)) s, 
    eval_nf (sinst t s) = O.substitute (eval_nf t) (eval_nf s)) *
  (forall s1 s2, 
    eval_nf (scomp s1 s2) =₁ O.scomp (eval_nf s1) (eval_nf s2)).
Proof.
apply sinst_elim with 
  (P := fun k (t : nf_expr (K1 k)) (s : nf_subst) (res : nf_expr (K1 k))  => 
    eval_nf res = O.substitute (eval_nf t) (eval_nf s))
  (P0 := fun (s1 s2 res : nf_subst) =>
    eval_nf res =₁ O.scomp (eval_nf s1) (eval_nf s2)).
- intros i s. now rewrite sapply_sound.
- intros c al s H. simp eval_nf. now rewrite H.
- reflexivity.
- intros ty tys a al s H1 H2. simp eval_nf substitute. now rewrite H1, H2.
- intros b x s. now simp eval_nf substitute.
- intros t s H. simp eval_nf substitute. now rewrite H.
- intros ty a s H. simp eval_nf substitute. now rewrite H, sup_sound.
- intros k xt r s. destruct k ; simp eval_nf substitute.
  all: now rewrite rscomp_sound, O.ren_subst.
- intros k xt s1 s2 H. destruct k ; simp eval_nf substitute.
  all: now rewrite H, O.subst_subst.
- intros i xr r s. simp eval_nf substitute rename.
  cbv [O.scomp]. simp substitute. now rewrite rscomp_sound.
- intros i xs s1 s2 H. simp eval_nf substitute. 
  cbv [O.scomp]. now rewrite H, O.subst_subst.
- intros k s. simp eval_nf. now rewrite sdrop_sound.
- intros t s1 s2 H1 H2. simp eval_nf. rewrite H1, H2.
  now rewrite O.scomp_scons_distrib.
- intros k xs s1 s2 H. simp eval_nf. rewrite H. now repeat rewrite O.scomp_assoc.
- intros r s. rewrite rscomp_sound. reflexivity.
Qed. 
    