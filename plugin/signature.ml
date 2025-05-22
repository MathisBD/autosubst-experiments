(** This file defines the OCaml representation of signatures, as well utilities for
    parsing and validating signatures written by the user. *)

open Prelude

(**************************************************************************************)
(** *** Pre-signature. *)
(**************************************************************************************)

(** A pre-signature is a parse tree of a user-written signature. It still contains
    location information, and can contain mistakes (for instance declaring the same
    constructor twice). A pre-signature can be checked and turned into a real signature
    using [validate_psignature] followed by [interp_signature_base_types]. *)

(** An argument type. *)
type parg_ty_r =
  | PAT_base of Constrexpr.constr_expr
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
    - [ctor_sig] (of length [n_ctors]) contains the argument types of each constructor.

    Generic signatures are parameterized over a type ['constr] of base types. Right after
    parsing, ['constr] is [Constrexpr.constr_expr] but once we have access to a global
    environment we switch to [EConstr.t]. *)
type 'constr gen_signature =
  { sort : Names.Id.t
  ; base_types : 'constr array
  ; n_ctors : int
  ; ctor_names : Names.Id.t array
  ; ctor_types : arg_ty list array
  }

(** The notion of signature manipulated by most of the plugin. *)
type signature = EConstr.t gen_signature

(** [arg_ty_constr sign ty ind] builds the [EConstr.t] corresponding to [ty]. We use [ind]
    as a placeholder for the inductive type of terms. *)
let rec arg_ty_constr (sign : signature) (ty : arg_ty) (ind : EConstr.t) : EConstr.t =
  match ty with
  | AT_base i -> sign.base_types.(i)
  | AT_term -> ind
  | AT_bind ty -> arg_ty_constr sign ty ind

(** [ctor_ty_constr sign tys ind] build the type of a constructor as a [EConstr.t]. We use
    [ind] as a placeholder for the inductive type of terms. *)
let ctor_ty_constr (sign : signature) (tys : arg_ty list) (ind : EConstr.t) : EConstr.t =
  arrows (List.map (fun ty -> arg_ty_constr sign ty ind) tys) ind

(**************************************************************************************)
(** *** Validating a pre-signature. *)
(**************************************************************************************)

(** Validate a pre-signature i.e. check it is well formed. Validating a pre-signature is
    done at _parsing_ time. On the upside, this means that we can have nice error messages
    (with a location!) without even needing the user to execute the
    [Autosubst Generate ...] command. However it also means that we can't access the
    global environment during validation: to internalize [Constrexpr.constr_expr] to
    [EConstr.t] we have to wait until we actually execute the command (see
    [interp_signature_base_types]). *)

(** State we maintain while validating a pre-signature. *)
type state =
  { (* The (unique) sort. *)
    sort : Names.lident
  ; (* The list of base types in order (i.e. most recent last). *)
    base_types : Constrexpr.constr_expr list
  ; (* The list of declared constructors in order (i.e. most recent last). *)
    ctors : (Names.Id.t * arg_ty list) list
  }

(** The empty state, which we use when starting validation. *)
let empty_state (sort : Names.lident) : state = { sort; base_types = []; ctors = [] }

let validate_sort (st : state) (sort : Names.lident) : unit =
  if not (Names.Id.equal sort.v st.sort.v)
  then Log.error ?loc:sort.loc "Undeclared sort %s." (Names.Id.to_string sort.v)

let validate_base (st : state) (c : Constrexpr.constr_expr) : int * state =
  let idx = List.length st.base_types in
  (idx, { st with base_types = st.base_types @ [ c ] })

(** Validate an argument type. *)
let validate_arg_ty (st : state) (ty : parg_ty) : arg_ty * state =
  match ty.v with
  | PAT_base c ->
      let idx, st = validate_base st c in
      (AT_base idx, st)
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

(** Validate a pre-signature. Raises an error (using Rocq's error reporting mechanism) if
    the pre-signature is not valid. *)
let validate_psignature (s : psignature) : Constrexpr.constr_expr gen_signature =
  let (SortDecl sort) = s.v.sort.v in
  let st = List.fold_left validate_ctor_decl (empty_state sort) s.v.ctors in
  { sort = sort.v
  ; n_ctors = List.length st.ctors
  ; base_types = st.base_types |> Array.of_list
  ; ctor_names = List.map fst st.ctors |> Array.of_list
  ; ctor_types = List.map snd st.ctors |> Array.of_list
  }

(** Pre-type and internalize the base types of a signature. Raises an error (using Rocq's
    error reporting mechanism) if a base type is not a well-typed term of type [Set],
    [Type], or [Prop]. *)
let interp_signature_base_types (s : Constrexpr.constr_expr gen_signature) : signature m =
  let interp_one (c : Constrexpr.constr_expr) : EConstr.t m =
   fun env sigma ->
    let c, ustate = Constrintern.interp_type env sigma c in
    let sigma = Evd.merge_universe_context sigma ustate in
    (sigma, Evarutil.nf_evar sigma c)
  in
  let* new_base_types = List.monad_map interp_one @@ Array.to_list s.base_types in
  ret { s with base_types = Array.of_list new_base_types }
