From Prototype Require Import Prelude Sig.

(** This module exposes various constants to the OCaml plugin.
    Constants are accessed in the plugin from [plugin/consts.ml]. *)

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