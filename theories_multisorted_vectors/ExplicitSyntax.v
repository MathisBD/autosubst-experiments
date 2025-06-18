(** This file defines a generic term grammar with _explicit_ renamings 
    and substitutions. Quoted naturals, terms, renamings, and substitutions
    can contain meta-variables, which stand in for arbitrary level one expressions.

    This file also implements:
    - Reification i.e. mapping from parameterized syntax to explicit syntax.
    - Evvaluation i.e. mapping from explicit syntax to parameterized syntax. 
*)

From MPrototype Require Import Prelude Sig.
(*From MPrototype Require ParamSyntax.
Module P := ParamSyntax.*)

Section WithSignature.
Context {sig : signature}.

(** Meta-variables are represented by an index (a natural)
    into an environment (a list of level one expressions). *)
(*Definition mvar := nat.*)

(*********************************************************************************)
(** *** Quoted naturals and explicit renamings. *)
(*********************************************************************************)

Unset Elimination Schemes.

(** Quoted natural. *)
Inductive qnat :=
(** Zero. *)
| Q_zero : qnat
(** Successor. *)
| Q_succ : qnat -> qnat
(** Explicit renaming applied to a quoted natural. *)
| Q_rapply : ren -> qnat -> qnat 
(** Quoted natural meta-variable. *)
| Q_mvar : nat -> qnat

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
| R_mvar : nat -> ren.

Set Elimination Schemes.

Derive NoConfusion for qnat ren.

Scheme qnat_ind := Induction for qnat Sort Prop 
  with ren_ind := Induction for ren Sort Prop.
Combined Scheme qnat_ren_ind from qnat_ind, ren_ind.

(*********************************************************************************)
(** *** Expressions and explicit substitutions. *)
(*********************************************************************************)

(** Notations for expressions with known kinds. *)
Reserved Notation "'term' s" (at level 0).
Reserved Notation "'arg' ty" (at level 0, ty at level 0).
Reserved Notation "'args' tys" (at level 0, tys at level 0).

Unset Elimination Schemes.

Set Printing Universes.
Print hvec.

(** Expressions are indexed by a kind: this is to avoid having too many 
    distinct constructors for instantiation by a renaming/substitution. *)
Inductive expr : (@kind nbase nsort) -> Type :=

(** Variable term constructor (de Bruijn index). *)
(*| E_tvar {m} : qnat -> term m
(** Non-variable term constructor, applied to a list of arguments. *)
| E_tctor {m} : forall c : fin (nctor m), args (ctor_type c) -> term m
(** Term metavariable. 
    We don't need metavariables for arguments or argument-lists. *)
| E_mvar {m} : nat -> term m

(** Empty argument list. *)
| E_al_nil : args []
(** Non-empty argument list. *)
| E_al_cons {ty tys} : arg ty -> args tys -> args (ty :: tys)

(** Base argument (e.g. bool or string). *)
| E_abase : forall b, base_type b -> arg (AT_base b)
(** Term argument. *)
| E_aterm {m} : term m -> arg (AT_term m)
(** Binder argument. *)
| E_abind {ty} : forall m, arg ty -> arg (AT_bind m ty)*)

(** Explicit substitution applied to a quoted natural. *)
(*| E_sapply {m} : subst m -> qnat -> term m
(** Instantiate an expression with an explicit renaming. *)
| E_ren {k} : vec ren nsort -> expr k -> expr k*)
(** Instantiate an expression with an explicit substitution. *)
| E_subst {k} : (*forall m, subst m*) svec nsort -> expr k -> expr k

with subst : fin nsort -> Type :=
(** Identity substitution on a given sort. *)
| S_id {m} : subst m
(** Shift substitution on a given sort. *)
| S_shift {m} : subst m
(** Substitution expansion. *)
(*| S_cons {m} : term m -> subst m -> subst m*)
(** Left to right composition of substitutions. *)
(*| S_comp {m} : subst m -> hvec nsort subst -> subst m
(** View a renaming as a substitution. *)
| S_ren {m} : ren -> subst m
(** Substitution metavariable. *)
| S_mvar {m} : nat -> subst m*)

with svec : nat -> Type :=
| snil : svec 0
| scons {n} : subst finO -> svec n -> svec (S n).


where "'term' m" := (expr (Kt m))
  and "'arg' ty" := (expr (Ka ty))
  and "'args' tys" := (expr (Kal tys)).

Set Elimination Schemes.

Derive Signature NoConfusion NoConfusionHom for expr.
Derive NoConfusion for subst.

Scheme expr_ind := Induction for expr Sort Prop 
  with subst_ind := Induction for subst Sort Prop.
Combined Scheme expr_subst_ind from expr_ind, subst_ind.

(*********************************************************************************)
(** *** Compute the size of expressions. *)
(*********************************************************************************)

(** We define functions which compute the size of expressions/substitutions. 
    This is useful to prove inequations of the form [S_cons t s <> s]. *)

Equations qsize : qnat -> nat :=
qsize Q_zero := 0 ;
qsize (Q_succ i) := S (qsize i) ;
qsize (Q_rapply r i) := S (rsize r + qsize i) ;
qsize (Q_mvar _) := 0 

with rsize : ren -> nat :=
rsize R_id := 0 ;
rsize R_shift := 0 ;
rsize (R_cons i r) := S (qsize i + rsize r) ;
rsize (R_comp r1 r2) := S (rsize r1 + rsize r2) ;
rsize (R_mvar _) := 0.

Equations esize {k} : expr k -> nat :=
esize (E_tvar i) := S (qsize i) ;
esize (E_tctor c al) := S (esize al) ;
esize E_al_nil := 0 ;
esize (E_al_cons a al) := S (esize a + esize al) ;
esize (E_abase _ _) := 0 ;
esize (E_aterm t) := S (esize t) ;
esize (E_abind a) := S (esize a) ;
esize (E_ren r t) := S (rsize r + esize t) ;
esize (E_subst s t) := S (ssize s + esize t) ;
esize (E_sapply s i) := S (ssize s + qsize i) ;
esize (E_mvar _) := 0 

with ssize : subst -> nat :=
ssize S_id := 0 ;
ssize S_shift := 0 ;
ssize (S_cons t s) := S (esize t + ssize s) ;
ssize (S_comp s1 s2) := S (ssize s1 + ssize s2) ;
ssize (S_ren r) := S (rsize r) ;
ssize (S_mvar _) := 0.
