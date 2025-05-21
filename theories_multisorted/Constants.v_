From Prototype Require Import Prelude Sig.
From Prototype Require LevelOne.

(** This module exposes various constants to the OCaml plugin.
    Constants are accessed in the plugin from [plugin/constants.ml]. *)

(** *** Basic constants. *)

Register unit as autosubst.unit.type.
Register tt as autosubst.unit.tt.

Register prod as autosubst.prod.type.
Register pair as autosubst.prod.pair.

Register nat as autosubst.nat.type.
Register O as autosubst.nat.zero.
Register S as autosubst.nat.succ.

Register list as autosubst.list.type.
Register nil as autosubst.list.nil.
Register cons as autosubst.list.cons.

Register string as autosubst.string.type.

Register eq as autosubst.eq.type.
Register eq_refl as autosubst.eq.eq_refl.
Register point_eq as autosubst.point_eq.type.
Register reflexivity as autosubst.reflexivity.
Register transitivity as autosubst.transitivity.

Register PeanoNat.Nat.measure_induction as autosubst.measure_induction.

(** *** Renamings. *)

Register ren as autosubst.ren.type.

Register rid as autosubst.ren.rid.
Register rshift as autosubst.ren.rshift.
Register rcons as autosubst.ren.rcons.
Register rcomp as autosubst.ren.rcomp.
Register up_ren as autosubst.ren.up_ren.

Register congr_rcons as autosubst.ren.congr_rcons.
Register congr_rcomp as autosubst.ren.congr_rcomp.
Register congr_up_ren as autosubst.ren.congr_up_ren.

(** *** Signatures. *)

Register arg_ty  as autosubst.arg_ty.type.
Register AT_base as autosubst.arg_ty.base.
Register AT_term as autosubst.arg_ty.term.
Register AT_bind as autosubst.arg_ty.bind.

Register kind as autosubst.kind.type.
Register Kt as autosubst.kind.t.
Register Ka as autosubst.kind.a.
Register Kal as autosubst.kind.al.

Register signature as autosubst.signature.type.
Register Build_signature as autosubst.signature.ctor.

(** *** Level One. *)

Register LevelOne.expr as autosubst.levelone.expr.type.
Register LevelOne.E_var as autosubst.levelone.expr.var.
Register LevelOne.E_ctor as autosubst.levelone.expr.ctor.
Register LevelOne.E_al_nil as autosubst.levelone.expr.al_nil.
Register LevelOne.E_al_cons as autosubst.levelone.expr.al_cons.
Register LevelOne.E_abase as autosubst.levelone.expr.abase.
Register LevelOne.E_aterm as autosubst.levelone.expr.aterm.
Register LevelOne.E_abind as autosubst.levelone.expr.abind.
Register LevelOne.subst as autosubst.levelone.subst.
Register LevelOne.esize as autosubst.levelone.esize.

Register LevelOne.rename as autosubst.levelone.rename.
Register LevelOne.substitute as autosubst.levelone.substitute.
Register LevelOne.sid as autosubst.levelone.sid.
Register LevelOne.sshift as autosubst.levelone.sshift.
Register LevelOne.scons as autosubst.levelone.scons.
Register LevelOne.up_subst as autosubst.levelone.up_subst.
Register LevelOne.scomp as autosubst.levelone.scomp.
Register LevelOne.rscomp as autosubst.levelone.rscomp.
Register LevelOne.srcomp as autosubst.levelone.srcomp.

Register LevelOne.inv_Kt as autosubst.levelone.inv_Kt.
Register LevelOne.inv_Kal_nil as autosubst.levelone.inv_Kal_nil.
Register LevelOne.inv_Kal_cons as autosubst.levelone.inv_Kal_cons.
Register LevelOne.inv_Ka_term as autosubst.levelone.inv_Ka_term.
Register LevelOne.inv_Ka_base as autosubst.levelone.inv_Ka_base.
Register LevelOne.inv_Ka_bind as autosubst.levelone.inv_Ka_bind.
