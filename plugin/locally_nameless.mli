open Monad

(** This module provides functions to build and destruct terms, in the locally nameless
    style. *)

(** We use ['a m] in the signatures of many functions. Formally [m] is a monad, but
    monadic programming in OCaml is awkward so we simply treat [m] as syntax sugar to have
    more readable function signatures. *)
(*type 'a m = Environ.env -> Evd.evar_map -> Evd.evar_map * 'a*)

(** [mk_kername path label] makes the kernel name with directory path [path] and label
    [label]. For instance to create the kernel name of [Nat.add] you can use
    [mk_kername ["Coq"; "Init"; "Nat"] "add"]. *)
val mk_kername : string list -> string -> Names.KerName.t

(** [fresh_ident basename] returns a fresh identifier built from [basename] and which is
    guaranteed to be distinct from all identifiers returned by this function so far. *)
val fresh_ident : string -> Names.Id.t

(** [with_local_decl basename ?def ty k] generates a fresh identifier [x] built from
    [basename] and executes the continuation [k x] in the environment extended with
    [x : ty := def]. *)
val with_local_decl :
  string -> ?def:EConstr.t -> EConstr.types -> (Names.Id.t -> 'a m) -> 'a m

(**************************************************************************************)
(** *** Building terms. *)
(**************************************************************************************)

(** [app f x] is a lightweight notation for an application to one argument. *)
val app : EConstr.t -> EConstr.t -> EConstr.t

(** [apps f xs] is a lightweight notation for an application to several arguments. *)
val apps : EConstr.t -> EConstr.t array -> EConstr.t

(** [arrow t1 t2] constructs the non-dependent product [t1 -> t2]. It takes care of
    lifting [t2]. *)
val arrow : EConstr.types -> EConstr.types -> EConstr.types

(** [arrows [t1 ; ... , tn] t] constructs the non-dependent product
    [t1 -> ... -> tn -> t]. It takes care of lifting. *)
val arrows : EConstr.types list -> EConstr.types -> EConstr.types

(** [lambda name ty body] makes a lambda abstraction with the given parameters, in the
    locally nameless style. *)
val lambda : string -> EConstr.types -> (Names.Id.t -> EConstr.t m) -> EConstr.t m

(** [prod name ty body] makes a dependent product with the given parameters, in the
    locally nameless style. *)
val prod : string -> EConstr.types -> (Names.Id.t -> EConstr.types m) -> EConstr.types m

(** [namedLetIn name def ty body] makes a local let-binding with the given parameters, in
    the locally nameless style. *)
val let_in :
  string -> EConstr.t -> EConstr.types -> (Names.Id.t -> EConstr.t m) -> EConstr.t m

(** [fix name rec_arg_idx ty body] makes a single fixpoint with the given parameters, in
    the locally nameless style :
    - [name] is the name of the fixpoint parameter.
    - [rec_arg_idx] is the index of the (structurally) recursive argument, starting at
      [0].
    - [ty] is the type of the fixpoint parameter.
    - [body] is the body of the fixpoint, which has access to the fixpoint parameter.

    For instance to build the fixpoint
    [fix add (n : nat) (m : nat) {struct_ m} : nat := ...] one could use
    [fix "add" 1 '(nat -> nat -> nat) (fun add -> ...)]. *)
val fix : string -> int -> EConstr.types -> (Names.Id.t -> EConstr.t m) -> EConstr.t m

(**************************************************************************************)
(** *** Declaring definitions/indutives. *)
(**************************************************************************************)

(** [declare_ind name arity ctor_names ctor_types] declares a single inductive
    (non-mutual) with no parameters, no indices, and not universe polymorphic. It also
    generates the associated elimination & induction principles.
    - [name] is the name of the inductive.
    - [ctor_names] contains the names of the constructors.
    - [ctor_types] contains the types of the constructors, which can depend on the
      inductive (and have access to an extended environment).

    It returns the name of the newly created inductive. *)
val declare_ind :
  string -> EConstr.t -> string list -> (Names.Id.t -> EConstr.t m) list -> Names.Ind.t

(**************************************************************************************)
(** *** Destructing terms. *)
(**************************************************************************************)
