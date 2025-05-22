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
  | PAT_sort of Names.lident
  | PAT_bind of Names.lident list * Names.lident

and parg_ty = parg_ty_r CAst.t

(** Declaration for a new sort. *)
type sort_decl_r = SortDecl of Names.lident

and sort_decl = sort_decl_r CAst.t

(** Declaration for a new constructor. *)
type pctor_decl_r =
  | CtorDecl of { name : Names.lident; arg_tys : parg_ty list; ret_ty : Names.lident }

and pctor_decl = pctor_decl_r CAst.t

(** A signature is a list of declarations. For now we require a single term declaration.
*)
type psignature_r = { sort : sort_decl; ctors : pctor_decl list }

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
    - [sort] is the name of the (unique) sort of terms.
    - [base_types] contains the list of base types.
    - [n_ctors] is the number of _non-variable_ constructors.
    - [ctor_names] (of length [n_ctors]) contains the name of each constructor.
    - [ctor_sig] (of length [n_ctors]) contains the argument types of each constructor. *)
type signature =
  { sort : Names.Id.t
  ; base_types : Constr.t array
  ; n_ctors : int
  ; ctor_names : Names.Id.t array
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

(** State we maintain while validating a pre-signature. *)
type state =
  { (* The (unique) sort. *)
    sort : Names.lident
  ; (* The list of base types, in order (i.e. most recent last). *)
    base_types : Constr.t list
  ; (* The list of declared constructors, in order (i.e. most recent last). *)
    ctors : (Names.Id.t * arg_ty list) list
  }

(** The empty state, which we use when starting validation. *)
let empty_state (sort : Names.lident) : state = { sort; base_types = []; ctors = [] }

let validate_sort (st : state) (sort : Names.lident) : unit =
  if not (Names.Id.equal sort.v st.sort.v)
  then Log.error ?loc:sort.loc "Undeclared sort %s." (Names.Id.to_string sort.v)

(** Validate an argument type. *)
let validate_arg_ty (st : state) (ty : parg_ty) : arg_ty * state =
  match ty.v with
  | PAT_base c ->
      let idx = List.length st.base_types in
      (AT_base idx, { st with base_types = st.base_types @ [ c ] })
  | PAT_sort sort ->
      validate_sort st sort;
      (AT_term, st)
  | PAT_bind (ids, id) ->
      List.iter (validate_sort st) ids;
      (validate_sort st) id;
      (List.fold_right (fun _ ty -> AT_bind ty) ids AT_term, st)

let validate_ctor_name (st : state) (name : Names.lident) : unit =
  if List.exists (fun (c, _) -> Names.Id.equal name.v c) st.ctors
  then
    Log.error ?loc:name.loc "Constructor %s is already declared."
      (Names.Id.to_string name.v)

(** Validate a constructor declaration. *)
let validate_ctor_decl (st : state) (d : pctor_decl) : state =
  let (CtorDecl d') = d.v in
  validate_ctor_name st d'.name;
  validate_sort st d'.ret_ty;
  (* validate the argument types. *)
  let rec loop (st : state) (ptys : parg_ty list) : arg_ty list * state =
    match ptys with
    | [] -> ([], st)
    | pty :: ptys ->
        let ty, st = validate_arg_ty st pty in
        let tys, st = loop st ptys in
        (ty :: tys, st)
  in
  let tys, st = loop st d'.arg_tys in
  { st with ctors = st.ctors @ [ (d'.name.v, tys) ] }

(** Validate a declaration. Raises an error (using Rocq's error reporting mechanism) if
    the pre-signature is not valid. *)
let validate_psignature (s : psignature) : signature =
  let (SortDecl sort) = s.v.sort.v in
  let st = List.fold_left validate_ctor_decl (empty_state sort) s.v.ctors in
  { sort = sort.v
  ; n_ctors = List.length st.ctors
  ; base_types = st.base_types |> Array.of_list
  ; ctor_names = List.map fst st.ctors |> Array.of_list
  ; ctor_types = List.map snd st.ctors |> Array.of_list
  }
