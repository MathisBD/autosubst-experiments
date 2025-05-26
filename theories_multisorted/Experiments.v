From Prototype Require Import MPrelude MSig.

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

Equations rename_ty (rty : ren) : ty -> ty :=
rename_ty rty (var_ty i) := var_ty (rty i) ;
rename_ty rty (arr t1 t2) := arr (rename_ty rty t1) (rename_ty rty t2) ;
rename_ty rty (all t) := all (rename_ty (up_ren rty) t).

Equations rename_tm (rty : ren) (rvl : ren) : tm -> tm :=
rename_tm rty rvl (app t1 t2) := app (rename_tm rty rvl t1) (rename_tm rty rvl t2) ;
rename_tm rty rvl (tapp t1 t2) := tapp (rename_tm rty rvl t1) (rename_ty rty t2) ;
rename_tm rty rvl (vt v) := vt (rename_vl rty rvl v)

with rename_vl (rty : ren) (rvl : ren) : vl -> vl :=
rename_vl rty rvl (var_vl i) := var_vl (rvl i) ;
rename_vl rty rvl (lam t1 t2) := lam (rename_ty rty t1) (rename_tm rty (up_ren rvl ) t2) ;
rename_vl rty rvl (tlam t) := tlam (rename_tm (up_ren rty) rvl t).



(*********************************************************************************)
(** *** Level one. *)
(*********************************************************************************)

Section Sec.
Context (sig : signature).

(** [occurs_aux] *)

Inductive occurs_aux (s : fin nsort) : @arg_ty nbase nsort -> Prop :=
| occurs_aux_term : occurs_aux s (AT_term s)
| occurs_aux_bind {s' ty} : occurs_aux s ty -> occurs_aux s (AT_bind s' ty).

Equations occurs_auxb : fin nsort -> @arg_ty nbase nsort -> bool :=
occurs_auxb s (AT_base _) := false ;
occurs_auxb s (AT_term s') := eqb_fin s s' ;
occurs_auxb s (AT_bind _ ty) := occurs_auxb s ty.

Lemma occurs_aux_spec s ty : reflect (occurs_aux s ty) (occurs_auxb s ty).
Proof. Admitted.

(** [occurs] *)

Equations fin_existsb (n : nat) (P : fin n -> bool) : bool :=
fin_existsb 0 _ := false ;
fin_existsb (S n) P := P finO || fin_existsb n (fun i => P (finS i)).

Definition occurs (s s' : fin nsort) : Prop :=
  exists c : fin (nctor s'), Exists (occurs_aux s) (ctor_type c).

Definition occursb (s s' : fin nsort) : bool :=
  fin_existsb (nctor s') (fun c => existsb (occurs_auxb s) (ctor_type c)).
  
Lemma occurs_spec s s' : reflect (occurs s s') (occursb s s').
Proof. Admitted. 

(* TODO: transitive closure of [occurs]. *)

(** [binds_aux] *)

Inductive binds_aux (s : fin nsort) : @arg_ty nbase nsort -> Prop :=
| binds_aux_base {ty} : binds_aux s (AT_bind s ty)
| binds_aux_step {s' ty} : binds_aux s ty -> binds_aux s (AT_bind s' ty).
