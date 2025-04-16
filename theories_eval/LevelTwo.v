From Prototype Require Import Prelude Sig LevelOne.

(** This file defines a generic term grammar with _explicit_ renamings 
    and substitutions. Quoted naturals, terms, renamings, and substitutions
    can contain meta-variables, which stand in for arbitrary level one expressions.

    This file also implements _reification_ (mapping from level one to 
    level two) and _evaluation_ (mapping from level two to level one). *)

Module Make (S : Sig).
Module O := LevelOne.Make (S).

(** Meta-variables are represented by an index (a natural)
    into an environment (a list of level one expressions). *)
Definition mvar := nat.

(*********************************************************************************)
(** *** Quoted naturals and explicit renamings. *)
(*********************************************************************************)

(** Quoted natural. *)
Inductive qnat :=
(** Zero. *)
| Q_zero : qnat
(** Explicit renaming applied to a quoted natural. *)
| Q_rapply : ren -> qnat -> qnat 
(** Quoted natural meta-variable. *)
| Q_mvar : mvar -> qnat

(** Explicit renaming. *)
with ren :=
(** Identity renaming. *)
| R_id : ren
(** Explicit shift. *)
| R_shift : ren
(** Renaming expansion. *)
| R_cons : qnat -> ren -> ren
(** Left to right composition of renamings. *)
| R_comp : ren -> ren -> ren 
(** Renaming meta-variable. *)
| R_mvar : mvar -> ren.

(*********************************************************************************)
(** *** Expressions and explicit substitutions. *)
(*********************************************************************************)

(** Notations for expressions with known kinds. *)
Reserved Notation "'term'" (at level 0).
Reserved Notation "'arg' ty" (at level 0, ty at level 0).
Reserved Notation "'args' tys" (at level 0, tys at level 0).

(** Expressions are indexed by a kind: this is to avoid having too many 
    distinct constructors for instantiation by a renaming/substitution. *)
Inductive expr : kind -> Type :=

(** Variable term constructor (de Bruijn index). *)
| E_tvar : qnat -> term
(** Non-variable term constructor, applied to a list of arguments. *)
| E_tctor : forall c, args (ctor_type S.t c) -> term
(** Term metavariable. We don't need argument or argument-list metavariables. *)
| E_mvar : mvar -> term

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

with subst :=
(** Identity substitution. *)
| S_id : subst
(** Shift substitution. *)
| S_shift : subst
(** Substitution expansion. *)
| S_cons : term -> subst -> subst
(** Left to right composition of substitutions. *)
| S_comp : subst -> subst -> subst
(** View a renaming as a substitution. *)
| S_ren : ren -> subst
(** Substitution metavariable. *)
| S_mvar : mvar -> subst

where "'term'" := (expr Kt)
  and "'arg' ty" := (expr (Ka ty))
  and "'args' tys" := (expr (Kal tys)).

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

  Equations qeval : qnat -> nat :=
  qeval Q_zero := 0 ;
  qeval (Q_rapply r i) := reval r (qeval i) ;
  qeval (Q_mvar x) := e.(assign_qnat) x
  
  with reval : ren -> O.ren :=
  reval R_id := O.rid ;
  reval R_shift := O.rshift ;
  reval (R_cons i r) := O.rcons (qeval i) (reval r) ;
  reval (R_comp r1 r2) := O.rcomp (reval r1) (reval r2) ;
  reval (R_mvar x) := e.(assign_ren) x.

  Equations eeval {k} : expr k -> O.expr k :=
  eeval (E_tvar i) := O.E_var (qeval i) ;
  eeval (E_tctor c al) := O.E_ctor c (eeval al) ;
  eeval E_al_nil := O.E_al_nil ;
  eeval (E_al_cons a al) := O.E_al_cons (eeval a) (eeval al) ;
  eeval (E_abase b x) := O.E_abase b x ;
  eeval (E_aterm t) := O.E_aterm (eeval t) ;
  eeval (E_abind a) := O.E_abind (eeval a) ;
  eeval (E_ren e r) := O.rename (eeval e) (reval r) ;
  eeval (E_subst e s) := O.substitute (eeval e) (seval s) ;
  eeval (E_mvar x) := e.(assign_term) x
  
  with seval : subst -> O.subst :=
  seval S_id := O.sid ;
  seval S_shift := O.sshift ;
  seval (S_cons t s) := O.scons (eeval t) (seval s) ;
  seval (S_comp s1 s2) :=
    match s1, s2 with 
    | S_ren r, s => O.rscomp (reval r) (seval s)
    | s, S_ren r => O.srcomp (seval s) (reval r)
    | s1, s2 => O.scomp (seval s1) (seval s2)
    end ;
  seval (S_ren r) := O.rscomp (reval r) O.E_var ;
  seval (S_mvar x) := e.(assign_subst) x.

End Evaluation.

Lemma seval_comp e s1 s2 : 
  seval e (S_comp s1 s2) =₁ O.scomp (seval e s1) (seval e s2).
Proof.
destruct s1 ; destruct s2 ; simp eeval ; try now reflexivity.
- intros i. cbv [O.srcomp O.scomp]. now rewrite O.ren_is_subst.
- destruct s1_1 ; destruct s1_2.
all: try (intros i ; cbv [O.srcomp O.scomp] ; now rewrite O.ren_is_subst).
- intros i. cbv [O.srcomp O.scomp]. now rewrite O.ren_is_subst.
Qed.
#[global] Hint Rewrite seval_comp : eeval seval.

(*********************************************************************************)
(** *** Reification. *)
(*********************************************************************************)

(** Reification needs to inspect function composition, thus it can't be
    implemented as a Rocq function and is instead implemented in Ltac2. *)

(** Turn an Ltac2 [int] to a Rocq [nat]. 
    Negative integers are mapped to [0]. *)
Ltac2 rec nat_of_int (x : int) : constr := 
  if Int.le x 0 then constr:(0)
  else let y := nat_of_int (Int.sub x 1) in constr:(S $y).

(** Reification environment. *)
Ltac2 Type env := 
  { qnat_mvars : constr list 
  ; ren_mvars : constr list
  ; term_mvars : constr list
  ; subst_mvars : constr list }.

(** The empty environment. *)
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

(* TODO: handle renamings directly applied to naturals. *)
Ltac2 rec reify_nat (e : env) (t : constr) : env * constr := 
  lazy_match! t with 
  | 0 => e, constr:(Q_zero)
  | S ?i =>
    let (e, i) := reify_nat e i in 
    e, constr:(Q_rapply R_shift $i)
  | ?r ?i =>
    let (e, r) := reify_ren e r in
    let (e, i) := reify_nat e i in
    e, constr:(Q_rapply $r $i)
  | ?i => 
    let idx := nat_of_int (List.length (e.(qnat_mvars))) in
    let e := add_qnat_mvar i e in
    e, constr:(Q_mvar $idx)
  end

with reify_ren (e : env) (t : constr) : env * constr :=
  lazy_match! t with 
  | O.rid => e, constr:(R_id)
  | O.rshift => e, constr:(R_shift) 
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
  | O.sid => e, constr:(S_id)
  | O.sshift => e, constr:(S_shift)
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

(** Turn a list of [constr] into a Rocq list. 
    [ty] is the type of each element in the list, which is needed
    to build the empty list. *)
Ltac2 rec coq_list (ty : constr) (xs : constr list) : constr :=
  match xs with 
  | [] => constr:(@nil $ty)
  | x :: xs =>
    let xs := coq_list ty xs in 
    constr:(@cons $ty $x $xs)
  end.

(** Turn the Ltac2 representation of the environment into the equivalent
    Rocq representation. *)
Ltac2 build_env (e : env) : constr :=
  let e1 := coq_list constr:(nat) (e.(qnat_mvars)) in 
  let e2 := coq_list constr:(O.ren) (e.(ren_mvars)) in 
  let e3 := coq_list constr:(O.expr Kt) (e.(term_mvars)) in 
  let e4 := coq_list constr:(O.subst) (e.(subst_mvars)) in 
  constr:(
    Build_env 
      (fun n => List.nth n $e1 0)
      (fun n => List.nth n $e2 O.rid)
      (fun n => List.nth n $e3 (O.E_var 0))
      (fun n => List.nth n $e4 O.sid)).

End Make.
