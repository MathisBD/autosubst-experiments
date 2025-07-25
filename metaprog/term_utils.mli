(** This module provides functions to build and destruct terms, in the locally nameless
    style. *)

open Monad

(**************************************************************************************)
(** *** Typing. *)
(**************************************************************************************)

(** [convertible ?pb t1 t2] checks for convertibility [t1 =?= t2] (if [pb] is [CONV]) or
    cumulativity [t1 <=? t2] (if [pb] is [CUMUL]). By default [pb] is [CONV]. *)
val convertible : ?pb:Conversion.conv_pb -> EConstr.t -> EConstr.t -> bool m

(** [unify ?pb t1 t2] unifies [t1 =?= t2] (if [pb] is [CONV]) or [t1 <=? t2] (if [pb] is
    [CUMUL]), instantiating evars. Raises an exception if unification fails. By default
    [pb] is [CONV]. *)
val unify : ?pb:Conversion.conv_pb -> EConstr.t -> EConstr.t -> unit m

(** [pretype t] turns a [Contrexpr.constr_expr] into an [EConstr.t] using pretyping. *)
val pretype : Constrexpr.constr_expr -> EConstr.t m

(** [typecheck ?solve_tc t ty] checks that [t] is well-typed and computes the type of [t],
    using typing information to resolve evars. If [solve_tc] is [true] we also attempt to
    solve evars using typeclass resolution (by default [solve_tc] is [false]).

    If [ty] is provided we additionally check that the type of [t] is a subtype of [ty]
    (using unification, and raising an exception if unification fails). [ty] should be
    well-typed. *)
val typecheck : ?solve_tc:bool -> EConstr.t -> EConstr.t option -> EConstr.types m

(** [retype t] computes the type of [t], assuming [t] is already well-typed. [retype] is
    much more efficient than [typecheck]. *)
val retype : EConstr.t -> EConstr.types m

(**************************************************************************************)
(** *** Building constants/inductives/constructors. *)
(**************************************************************************************)

(** [mk_qualid path label] makes the qualified identifier with directory path [path] and
    label [label]. For instance to create the qualid of [Nat.add] you can use
    [mk_qualid ["Coq"; "Init"; "Nat"] "add"]. *)
val mk_qualid : string list -> string -> Libnames.qualid

(** [mk_kername path label] makes the kernel name with directory path [path] and label
    [label]. For instance to create the kernel name of [Nat.add] you can use
    [mk_kername ["Coq"; "Init"; "Nat"] "add"]. *)
val mk_kername : string list -> string -> Names.KerName.t

(** [mkconst name] builds the _monomorphic_ constant [name]. *)
val mkconst : Names.Constant.t -> EConstr.t

(** [mkind cname] builds the _monomorphic_ inductive [name]. *)
val mkind : Names.Ind.t -> EConstr.t

(** [mkctor cname] builds the _monomorphic_ constructor [name]. *)
val mkctor : Names.Construct.t -> EConstr.t

(** [mkglob gname] builds the _monomorphic_ global reference [gname]. *)
val mkglob : Names.GlobRef.t -> EConstr.t

(** Same as [mkglob] but with a lazy global refenrece. *)
val mkglob' : Names.GlobRef.t Lazy.t -> EConstr.t

(** [fresh_const name] builds the constant [name], instantiated with a fresh universe
    instance. *)
val fresh_const : Names.Constant.t -> EConstr.t m

(** [fresh_ind name] builds the inductive [name], instantiated with a fresh universe
    instance. *)
val fresh_ind : Names.Ind.t -> EConstr.t m

(** [fresh_ctor name] builds the constructor [name], instantiated with a fresh universe
    instance. *)
val fresh_ctor : Names.Construct.t -> EConstr.t m

(**************************************************************************************)
(** *** Manipulating contexts. *)
(**************************************************************************************)

(** [fresh_ident base] returns an identifier built from [base], which is guaranteed to be
    fresh in the current named (local) context. *)
val fresh_ident : Names.Id.t -> Names.Id.t m

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

(** [fresh_type] creates a [Type] term with a fresh universe level, and adds the new
    universe level to the evar map. *)
val fresh_type : EConstr.t m

(** [fresh_evar ty] creates a fresh evar with type [ty] (if provided). If [ty] is not
    provided, it creates another fresh evar (of type [Type]) for the type. *)
val fresh_evar : EConstr.t option -> EConstr.t m

(** [app f x] is a lightweight notation for an application to one argument. *)
val app : EConstr.t -> EConstr.t -> EConstr.t

(** [apps f xs] is a lightweight notation for an application to several arguments. *)
val apps : EConstr.t -> EConstr.t array -> EConstr.t

(** [apps_ev f n args] builds the application [f args], inserting [n] evars before the
    arguments [args]. *)
val apps_ev : EConstr.t -> int -> EConstr.t array -> EConstr.t m

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

(** [case scrutinee ?return branches] build a case expression on [scrutinee].
    - The type of [scrutinee] must be an inductive applied to all of its parameters and
      indices.
    - [return] (if provided) gives the return type of the case expression, which can
      depend on the indices of the inductive and on the scrutinee.
    - [branches] is a function which builds the [i]-th branch (starting at [0]) of the
      case expression, wich can depend on the arguments of the [i]-th constructor. *)
val case :
     EConstr.t
  -> ?return:(Names.Id.t list -> Names.Id.t -> EConstr.t m)
  -> (int -> Names.Id.t list -> EConstr.t m)
  -> EConstr.t m

(**************************************************************************************)
(** *** Declaring definitions/inductives. *)
(**************************************************************************************)

(** The functions below typecheck all their arguments: we do this to solve any remaining
    evars and to collect universe constraints which are not already in the evar-map. *)

(** The functions below modify the global environment, but the new global entry is not
    visible until you reset the state of the monad, e.g. using [Global.env ()] or
    [monad_run]. *)

(** [declare_def kind name ?ty body] adds a new (transparent) definition
    [name : ty := body] to the global environment. Does not handle universe polymorphism.

    It returns the name of the newly created constant. *)
val declare_def :
     Decls.definition_object_kind
  -> Names.Id.t
  -> ?ty:EConstr.t
  -> EConstr.t
  -> Names.Constant.t m

(** [declare_theorem kind name stmt tac] adds a new (opaque) theorem [name : ty] to the
    global environment, proved with tactic [tac]. Does not handle universe polymorphism.

    It returns the name of the newly created constant. *)
val declare_theorem :
     Decls.theorem_kind
  -> Names.Id.t
  -> EConstr.t
  -> unit Proofview.tactic
  -> Names.Constant.t m

(** [declare_ind name arity ctor_names ctor_types] adds an inductive to the global
    environment. It handles non-mutual inductives with no parameters, no indices, and no
    universe polymorphism. It also generates the associated elimination & induction
    principles.
    - [name] is the name of the inductive.
    - [ctor_names] contains the names of the constructors.
    - [ctor_types] contains the types of the constructors, which can depend on the
      inductive (and have access to an extended environment).

    It returns the name of the newly created inductive. *)
val declare_ind :
     Names.Id.t
  -> EConstr.t
  -> Names.Id.t list
  -> (Names.Id.t -> EConstr.t m) list
  -> Names.Ind.t m
