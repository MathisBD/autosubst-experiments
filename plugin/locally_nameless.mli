open Monad

(** This module provides functions to build and destruct terms, in the locally nameless
    style. *)

(**************************************************************************************)
(** *** Miscellaneous. *)
(**************************************************************************************)

(** [mk_kername path label] makes the kernel name with directory path [path] and label
    [label]. For instance to create the kernel name of [Nat.add] you can use
    [mk_kername ["Coq"; "Init"; "Nat"] "add"]. *)
val mk_kername : string list -> string -> Names.KerName.t

(** [fresh_ident base] returns an identifier built from [base], which is guaranteed to be
    fresh in the current named (local) context. *)
val fresh_ident : Names.Id.t -> Names.Id.t m

(** [typecheck t] checks that [t] is well-typed and computes the type of [t], using typing
    information to resolve unification variable in [t]. *)
val typecheck : EConstr.t -> EConstr.types m

(** [retype t] computes the type of [t], assuming [t] is already well-typed. *)
val retype : EConstr.t -> EConstr.types m

(**************************************************************************************)
(** *** Manipulating contexts. *)
(**************************************************************************************)

(** [vass x ty] builds the local assumption [x : ty]. *)
val vass : string -> EConstr.types -> EConstr.rel_declaration

(** [vdef x def ty] builds the local assumption [x : ty := def]. *)
val vdef : string -> EConstr.t -> EConstr.types -> EConstr.rel_declaration

(** [with_local_decl decl k] generates a fresh identifier [x] from [decl] and executes the
    continuation [k x] in an environment extended with a _named_ declaration [decl']. *)
val with_local_decl : EConstr.rel_declaration -> (Names.Id.t -> 'a m) -> 'a m

(** Generalization of [with_local_decl] to a de Bruijn context. The continuation receives
    the variables from outermost to innermost. *)
val with_local_ctx : EConstr.rel_context -> (Names.Id.t list -> 'a m) -> 'a m

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

(** Instantiate an inductive with a fresh universe instance. *)
val fresh_ind : Names.Ind.t -> EConstr.t m

(** Instantiate a constructor with a fresh universe instance. *)
val fresh_ctor : Names.Construct.t -> EConstr.t m

(** Instantiate a constant with a fresh universe instance. *)
val fresh_const : Names.Constant.t -> EConstr.t m

(** [fresh_type] creates a [Type] term with a fresh universe level, and adds the new
    universe level to the evar map. *)
val fresh_type : EConstr.t m

(** [fresh_evar ty] creates a fresh evar with type [ty] (if provided). If [ty] is not
    provided, it creates another fresh evar (of type [Type]) for the type. *)
val fresh_evar : EConstr.t option -> EConstr.t m

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

(** [case scrutinee ?return branches] build a case expression on [scrutinee]. It assumes
    the type of [scrutinee] is and inductive without any parameters or indices.
    - [return] is the case return type. If not provided, an evar will be used instead.
    - [branches] is a function which builds the [i]-th branch (starting at [0]) of the
      case expression, with the arguments of the constructor in context. *)
val case :
  EConstr.t -> ?return:EConstr.t -> (int -> Names.Id.t list -> EConstr.t m) -> EConstr.t m

(**************************************************************************************)
(** *** Declaring definitions/indutives. *)
(**************************************************************************************)

(** [declare_def kind name ?ty body] adds a new definition [name : ty := body] to the
    global environment. Does not handle universe polymorphism.

    It returns the name of the newly created constant. *)
val declare_def :
     Decls.definition_object_kind
  -> string
  -> ?ty:EConstr.t
  -> EConstr.t
  -> Names.Constant.t m

(** [declare_ind name arity ctor_names ctor_types] adds an inductive to the global
    environment. It handles non-mutual inductives with no parameters, no indices, and not
    universe polymorphic. It also generates the associated elimination & induction
    principles.
    - [name] is the name of the inductive.
    - [ctor_names] contains the names of the constructors.
    - [ctor_types] contains the types of the constructors, which can depend on the
      inductive (and have access to an extended environment).

    It returns the name of the newly created inductive. *)
val declare_ind :
  string -> EConstr.t -> string list -> (Names.Id.t -> EConstr.t m) list -> Names.Ind.t m

(**************************************************************************************)
(** *** Destructing terms. *)
(**************************************************************************************)
