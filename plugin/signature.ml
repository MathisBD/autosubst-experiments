(** This file defines the OCaml representation of signatures, as well utilities for
    parsing and validating signatures written by the user. *)

open Prelude

(**************************************************************************************)
(** *** Pre-signature. *)
(**************************************************************************************)

(** A pre-signature is a parse tree of what the user writes. It still contains location
    information, and can contain mistakes (for instance declaring the same constructor
    twice). A pre-signature can be checked and turned into a real signature using
    [validate_psignature]. *)

(** An argument type. *)
type parg_ty_r =
  | PAT_base of Constr.t
  | PAT_term of Names.lident
  | PAT_bind of Names.lident list * Names.lident

and parg_ty = parg_ty_r CAst.t

(** Declaration for a new sort of terms. *)
type term_decl_r = TermDecl of Names.lident

and term_decl = term_decl_r CAst.t

(** Declaration for a new constructor. *)
type pctor_decl_r =
  | CtorDecl of { name : Names.lident; arg_tys : parg_ty list; ret_ty : Names.lident }

and pctor_decl = pctor_decl_r CAst.t

(** A signature is a list of declarations. For now we require a single term declaration.
*)
type psignature_r = { term : term_decl; ctors : pctor_decl list }

and psignature = psignature_r CAst.t

(*let pp_list (pp_elem : formatter -> 'a -> unit) (fmt : formatter) (xs : 'a list) : unit =
  let n = List.length xs in
  fprintf fmt "[";
  List.iteri
    (fun i x ->
      pp_elem fmt x;
      if i < n - 1 then fprintf fmt ", ")
    xs;
  fprintf fmt "]"

let pp_pident (fmt : formatter) (id : Names.lident) : unit =
  match id.loc with
  | None -> fprintf fmt "%s" (Pp.string_of_ppcmds @@ Ppconstr.pr_id id.v)
  | Some loc ->
      fprintf fmt "%s[%d:%d:%d]"
        (Pp.string_of_ppcmds @@ Ppconstr.pr_id id.v)
        loc.line_nb (loc.bp - loc.bol_pos) (loc.ep - loc.bol_pos)

let pp_parg_ty (fmt : formatter) (ty : parg_ty) : unit =
  match ty.v with
  | PAT_base c -> fprintf fmt "(BASE %s)" (Pp.string_of_ppcmds @@ Constr.debug_print c)
  | PAT_term id -> fprintf fmt "(TERM %a)" pp_pident id
  | PAT_bind (ids, id) ->
      fprintf fmt "(BIND %a IN %a)" (pp_list pp_pident) ids pp_pident id

let pp_pdecl (fmt : formatter) (d : pdecl) : unit =
  match d.v with
  | TermDecl id -> fprintf fmt "TERM %a" pp_pident id
  | CtorDecl { name; arg_tys; ret_ty } ->
      fprintf fmt "CTOR %a %a %a" pp_pident name (pp_list pp_parg_ty) arg_tys pp_pident
        ret_ty

let pp_psignature (fmt : formatter) (s : psignature) : unit =
  List.iter (fprintf fmt "%a\n" pp_pdecl) s.v*)

(**************************************************************************************)
(** *** Signature. *)
(**************************************************************************************)

(** Argument type. Base types store the index of the type in the [base_types] array. *)
type arg_ty = AT_base of int | AT_term | AT_bind of arg_ty

(** An abstract signature:
    - [n_ctors] is the number of _non-variable_ constructors.
    - [ctor_names] contains the name of each constructor.
    - [ctor_sig] contains the argument types of each constructor.

    The length of [ctor_names] and [ctor_sig] should be equal to [n_ctors]. *)
type signature =
  { n_ctors : int
  ; base_types : Constr.t array
  ; ctor_names : string array
  ; ctor_types : arg_ty list array
  }

(** [arg_ty_constr sign ty ind] builds the [EConstr.t] corresponding to [ty]. We use [ind]
    as a placeholder for the inductive type of terms. *)
let rec arg_ty_constr (sign : signature) (ty : arg_ty) (ind : EConstr.t) : EConstr.t =
  match ty with
  | AT_base i -> EConstr.of_constr sign.base_types.(i)
  | AT_term -> ind
  | AT_bind ty -> arg_ty_constr sign ty ind

(** [ctor_ty_constr sign tys ind] build the type of a constructor as a [EConstr.t]. We use
    [ind] as a placeholder for the inductive type of terms. *)
let ctor_ty_constr (sign : signature) (tys : arg_ty list) (ind : EConstr.t) : EConstr.t =
  arrows (List.map (fun ty -> arg_ty_constr sign ty ind) tys) ind

(**************************************************************************************)
(** *** Validating a pre-signature. *)
(**************************************************************************************)

let validate_arg_ty (term : term_decl) (ty : parg_ty) : arg_ty =
  

(** Validate a declaration. Raises an error (using Rocq's error reporting mechanism) if
    the pre-signature is not valid. *)
let validate_psignature (s : psignature) : signature =

