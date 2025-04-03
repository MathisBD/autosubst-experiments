From Equations Require Import Equations.
From Prototype Require Import Prelude Sig.
From Prototype Require LevelOne LevelTwo.

Module Make (S : Sig).
Module O := LevelOne.Make (S).
Module T := LevelTwo.Make (S).

(*********************************************************************************)
(** *** Denotation (level two -> level one). *)
(*********************************************************************************)

Definition denote_type (k : T.kind) : Type :=
  match k with 
  | T.Ks => O.subst
  | T.Km T.Kt => O.expr O.Kt
  | T.Km (T.Kal tys) => O.expr (O.Kal tys)
  | T.Km (T.Ka ty) => O.expr (O.Ka ty)
  end.
      
(** Denotation doesn't know how to handle metavariables: it thus works up to an
    assignment, which determines how to denote metavariables. *)
Definition assignment := forall k : T.kind, T.mvar k -> denote_type k.

(** Mapping from level two expressions to level one expressions and substitutions. *)
Equations denote {k} (m : assignment) (t : T.expr k) : denote_type k by struct t :=
denote m (T.E_var i) := O.E_var i ;
denote m (T.E_ctor c al) := O.E_ctor c (denote m al) ;
denote m T.E_al_nil := O.E_al_nil ;
denote m (T.E_al_cons a al) := O.E_al_cons (denote m a) (denote m al) ;
denote m (T.E_abase b x) := O.E_abase b x ;
denote m (T.E_aterm t) := O.E_aterm (denote m t) ;
denote m (T.E_abind a) := O.E_abind (denote m a) ;
denote m (@T.E_subst T.Kt t s) := O.substitute (denote m t) (denote m s) ;
denote m (@T.E_subst (T.Ka _) t s) := O.substitute (denote m t) (denote m s) ;
denote m (@T.E_subst (T.Kal _) t s) := O.substitute (denote m t) (denote m s) ;
denote m (T.E_sshift k) := O.sshift k ;
denote m (T.E_scons t s) := O.scons (denote m t) (denote m s) ;
denote m (T.E_scomp s1 s2) := O.scomp (denote m s1) (denote m s2) ;
denote m (T.E_mvar x) := m _ x.

(*********************************************************************************)
(** *** Correctness of denotation. *)
(*********************************************************************************)

(** Equality on denoted expressions. We use pointwise equality 
    for substitutions so as to not assume functional extensionality. *)
Definition denote_rel (k : T.kind) : relation (denote_type k) :=
  match k with 
  | T.Ks => @point_eq nat (O.expr O.Kt)
  | _ => eq
  end.

#[global] Instance denote_rel_equiv k : Equivalence (denote_rel k).
Proof. 
constructor ; destruct k ; try solve [easy].
- intros ?????. etransitivity ; eauto.
- intros ?????. etransitivity ; eauto.
Qed.

(** Main correctness result for [denote]: it transports level-two _sigma-equal_ terms 
    to level-one _equal_ terms. *)
#[global] Instance denote_proper {k} m : Proper (T.axiom_eq ==> denote_rel k) (@denote k m).
Proof.
intros t1 t2 Ht. induction Ht ; simpl in * ; simp denote.
all: try solve [ auto | easy ].
- etransitivity ; eauto. 
- destruct k ; simp denote ; now apply O.substitute_proper.
- now apply O.scons_proper.
- now apply O.scomp_proper.
- simp substitute. f_equal. apply O.substitute_proper ; auto.
  simp up_subst denote. rewrite O.up_subst_alt. reflexivity.
- destruct k ; simp denote ; now rewrite O.subst_subst.
- destruct k ; unfold T.sid ; simp denote ; now rewrite O.subst_sid.
- now rewrite O.sid_scons.
- unfold T.sid ; simp denote. now rewrite O.scomp_id_r.
- now rewrite O.scomp_assoc.
- now rewrite O.scomp_scons_distrib.
Qed.

(*********************************************************************************)
(** *** Reification (level one -> level two). *)
(*********************************************************************************)


End Make.
