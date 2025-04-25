open Monad
open Locally_nameless

(** Argument type. *)
type arg_ty = AT_base of EConstr.types | AT_term | AT_bind of arg_ty

(** An abstract signature:
    - [ctor_names] contains the name of each constructor.
    - [ctor_sig] contains the argument types of each constructor. *)
type signature = { ctor_names : string array; ctor_types : arg_ty list array }

(** Build the [EConstr.t] corresponding to an [arg_ty]. We use [ind] as a placeholder for
    the inductive type of terms. *)
let rec arg_ty_constr (ty : arg_ty) (ind : EConstr.t) : EConstr.t =
  match ty with AT_base b -> b | AT_term -> ind | AT_bind ty -> arg_ty_constr ty ind

(** Build the type of a constructor as a [EConstr.t]. We use [ind] as a placeholder for
    the inductive type of terms. *)
let ctor_ty_constr (tys : arg_ty list) (ind : EConstr.t) : EConstr.t =
  arrows (List.map (fun ty -> arg_ty_constr ty ind) tys) ind

(** Rocq inductive [nat]. *)
let nat : EConstr.t =
  EConstr.UnsafeMonomorphic.mkInd
    (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Init"; "Datatypes" ] "nat", 0)

(** Rocq inductive [string]. *)
let string : EConstr.t =
  EConstr.UnsafeMonomorphic.mkInd
    (Names.MutInd.make1 @@ mk_kername [ "Coq"; "Strings"; "String" ] "string", 0)

let declare_ind (s : signature) : unit =
  (* Constructor names and types. We add an extra constructor for variables. *)
  let ctor_names = "Var" :: Array.to_list s.ctor_names in
  let ctor_types =
    (fun ind -> ret @@ arrow nat (EConstr.mkVar ind))
    :: Array.to_list
         (Array.map
            (fun ty ind -> ret @@ ctor_ty_constr ty (EConstr.mkVar ind))
            s.ctor_types)
  in
  (* Declare the inductive. *)
  ignore @@ declare_ind "term" EConstr.mkSet ctor_names ctor_types

let main () =
  declare_ind
    { ctor_names = [| "App"; "Lam" |]
    ; ctor_types = [| [ AT_term; AT_term ]; [ AT_base string; AT_bind AT_term ] |]
    };
  Log.printf "plugin done"
