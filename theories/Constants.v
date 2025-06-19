From Prototype Require Import Prelude Sig.
From Prototype Require ParamSyntax.

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
Register eq_sym as autosubst.eq.eq_sym.
Register eq_trans as autosubst.eq.eq_trans.

Register eq1 as autosubst.eq1.type.
Register eq1_refl as autosubst.eq1.refl.
Register eq1_sym as autosubst.eq1.sym.
Register eq1_trans as autosubst.eq1.trans.

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
Register AT_functor as autosubst.arg_ty.functor.

Register kind as autosubst.kind.type.
Register Kt as autosubst.kind.t.
Register Ka as autosubst.kind.a.
Register Kal as autosubst.kind.al.

Register signature as autosubst.signature.type.
Register Build_signature as autosubst.signature.ctor.

(** *** Parameterized syntax. *)

Register ParamSyntax.expr as autosubst.param.expr.type.
Register ParamSyntax.E_var as autosubst.param.expr.var.
Register ParamSyntax.E_ctor as autosubst.param.expr.ctor.
Register ParamSyntax.E_al_nil as autosubst.param.expr.al_nil.
Register ParamSyntax.E_al_cons as autosubst.param.expr.al_cons.
Register ParamSyntax.E_abase as autosubst.param.expr.abase.
Register ParamSyntax.E_aterm as autosubst.param.expr.aterm.
Register ParamSyntax.E_abind as autosubst.param.expr.abind.
Register ParamSyntax.E_afunctor as autosubst.param.expr.afunctor.
Register ParamSyntax.subst as autosubst.param.subst.
Register ParamSyntax.esize as autosubst.param.esize.

Register ParamSyntax.rename as autosubst.param.rename.
Register ParamSyntax.substitute as autosubst.param.substitute.
Register ParamSyntax.sid as autosubst.param.sid.
Register ParamSyntax.sshift as autosubst.param.sshift.
Register ParamSyntax.scons as autosubst.param.scons.
Register ParamSyntax.up_subst as autosubst.param.up_subst.
Register ParamSyntax.scomp as autosubst.param.scomp.
Register ParamSyntax.rscomp as autosubst.param.rscomp.
Register ParamSyntax.srcomp as autosubst.param.srcomp.

Register ParamSyntax.inv_Kt as autosubst.param.inv_Kt.
Register ParamSyntax.inv_Kal_nil as autosubst.param.inv_Kal_nil.
Register ParamSyntax.inv_Kal_cons as autosubst.param.inv_Kal_cons.
Register ParamSyntax.inv_Ka_term as autosubst.param.inv_Ka_term.
Register ParamSyntax.inv_Ka_base as autosubst.param.inv_Ka_base.
Register ParamSyntax.inv_Ka_bind as autosubst.param.inv_Ka_bind.
Register ParamSyntax.inv_Ka_functor as autosubst.param.inv_Ka_functor.
