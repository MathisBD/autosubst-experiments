(** This module defines Rocq constants we need to access from OCaml. Rocq constants are
    registered in [theories/Constants.v] using the command [Register ... as ...]. *)

(** Before calling [Coqlib.lib_ref], we have to wait until Rocq is initialized: we use
    [Lazy.t] to do this. *)
let resolve (ref : string) : Names.GlobRef.t Lazy.t = lazy (Coqlib.lib_ref ref)

(**************************************************************************************)
(** *** Basic constants. *)
(**************************************************************************************)

let unit = resolve "autosubst.unit.type"
let tt = resolve "autosubst.unit.tt"
let prod = resolve "autosubst.prod.type"
let pair = resolve "autosubst.prod.pair"
let nat = resolve "autosubst.nat.type"
let zero = resolve "autosubst.nat.zero"
let succ = resolve "autosubst.nat.succ"
let list = resolve "autosubst.list.type"
let nil = resolve "autosubst.list.nil"
let cons = resolve "autosubst.list.cons"
let string = resolve "autosubst.string.type"
let eq = resolve "autosubst.eq.type"
let eq_refl = resolve "autosubst.eq.eq_refl"
let eq_sym = resolve "autosubst.eq.eq_sym"
let eq_trans = resolve "autosubst.eq.eq_trans"
let point_eq = resolve "autosubst.point_eq.type"
let peq_refl = resolve "autosubst.point_eq.peq_refl"
let peq_sym = resolve "autosubst.point_eq.peq_sym"
let peq_trans = resolve "autosubst.point_eq.peq_trans"
let measure_induction = resolve "autosubst.measure_induction"

(**************************************************************************************)
(** *** Renamings. *)
(**************************************************************************************)

let ren = resolve "autosubst.ren.type"
let rid = resolve "autosubst.ren.rid"
let rshift = resolve "autosubst.ren.rshift"
let rcons = resolve "autosubst.ren.rcons"
let rcomp = resolve "autosubst.ren.rcomp"
let up_ren = resolve "autosubst.ren.up_ren"
let congr_rcons = resolve "autosubst.ren.congr_rcons"
let congr_rcomp = resolve "autosubst.ren.congr_rcomp"
let congr_up_ren = resolve "autosubst.ren.congr_up_ren"

(**************************************************************************************)
(** *** Signatures. *)
(**************************************************************************************)

let arg_ty = resolve "autosubst.arg_ty.type"
let at_base = resolve "autosubst.arg_ty.base"
let at_term = resolve "autosubst.arg_ty.term"
let at_bind = resolve "autosubst.arg_ty.bind"
let kind = resolve "autosubst.kind.type"
let k_t = resolve "autosubst.kind.t"
let k_a = resolve "autosubst.kind.a"
let k_al = resolve "autosubst.kind.al"
let signature = resolve "autosubst.signature.type"
let build_signature = resolve "autosubst.signature.ctor"

(**************************************************************************************)
(** *** Level One. *)
(**************************************************************************************)

module O = struct
  let expr = resolve "autosubst.levelone.expr.type"
  let e_var = resolve "autosubst.levelone.expr.var"
  let e_ctor = resolve "autosubst.levelone.expr.ctor"
  let e_al_nil = resolve "autosubst.levelone.expr.al_nil"
  let e_al_cons = resolve "autosubst.levelone.expr.al_cons"
  let e_abase = resolve "autosubst.levelone.expr.abase"
  let e_aterm = resolve "autosubst.levelone.expr.aterm"
  let e_abind = resolve "autosubst.levelone.expr.abind"
  let subst = resolve "autosubst.levelone.subst"
  let esize = resolve "autosubst.levelone.esize"
  let rename = resolve "autosubst.levelone.rename"
  let substitute = resolve "autosubst.levelone.substitute"
  let sid = resolve "autosubst.levelone.sid"
  let sshift = resolve "autosubst.levelone.sshift"
  let scons = resolve "autosubst.levelone.scons"
  let up_subst = resolve "autosubst.levelone.up_subst"
  let scomp = resolve "autosubst.levelone.scomp"
  let rscomp = resolve "autosubst.levelone.rscomp"
  let srcomp = resolve "autosubst.levelone.srcomp"
  let inv_Kt = resolve "autosubst.levelone.inv_Kt"
  let inv_Kal_nil = resolve "autosubst.levelone.inv_Kal_nil"
  let inv_Kal_cons = resolve "autosubst.levelone.inv_Kal_cons"
  let inv_Ka_term = resolve "autosubst.levelone.inv_Ka_term"
  let inv_Ka_base = resolve "autosubst.levelone.inv_Ka_base"
  let inv_Ka_bind = resolve "autosubst.levelone.inv_Ka_bind"
end
