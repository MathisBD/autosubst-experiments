(** This module defines Rocq constants we need to access from OCaml. Rocq constants are
    registered in [theories/Constants.v] using the command [Register ... as ...]. *)

let resolve (ref : string) : EConstr.t Lazy.t =
  lazy
    begin
      EConstr.of_constr
      @@ UnivGen.constr_of_monomorphic_global (Global.env ())
      @@ Coqlib.lib_ref ref
    end

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
let point_eq = resolve "autosubst.point_eq.type"
let transitivity = resolve "autosubst.transitivity"
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
