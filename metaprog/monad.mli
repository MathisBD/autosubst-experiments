(** Most functions written against Rocq's API need to thread the global environment and
    evar map. Doing this manually leads to very verbose code, so we use a simple monad to
    alleviate this issue. This is not an awesome solution, because monadic programming in
    OCaml is quite annoying. *)

(** [m] is a monad which provides:
    - Read access to the global & local environment [Environ.env].
    - Read/write access to the unification state [Evd.evar_map]. *)
type 'a m = Environ.env -> Evd.evar_map -> Evd.evar_map * 'a

(** Monadic return. *)
val ret : 'a -> 'a m

(** Monadic bind. *)
val ( let* ) : 'a m -> ('a -> 'b m) -> 'b m

(** Run a monadic computation in the current global environment, with an empty evar map
    and empty local context. The final evar map is discarded. *)
val monad_run : 'a m -> 'a

(** Run a monadic computation as a tactic, using the proof's current environment and evar
    map, and updating the proof's evar map. New evars in the evar-map are not considered
    goals. Assumes exactly one goal is under focus. *)
val monad_run_tactic : 'a m -> 'a Proofview.tactic

(** Get the current environment. *)
val get_env : Environ.env m

(** Run a local computation in a modified environment. *)
val with_env : Environ.env -> 'a m -> 'a m

(** Same as [with_env], but the new environment can depend on the current one. *)
val with_env' : (Environ.env -> Environ.env) -> 'a m -> 'a m

(** Get the current evar map. *)
val get_sigma : Evd.evar_map m

(** Replace the evar map. *)
val set_sigma : Evd.evar_map -> unit m

(** Modify the current evar map. *)
val modify_sigma : (Evd.evar_map -> Evd.evar_map) -> unit m

(** Discard the result of a monadic computation, keeping only the effects. *)
val monad_ignore : 'a m -> unit m

(** Additional functions on lists. *)
module List : sig
  include module type of Stdlib.List

  (** Map a monadic function over a list, sequencing effects from left to right. *)
  val monad_map : ('a -> 'b m) -> 'a list -> 'b list m

  (** Same as [monad_map] but the function also gets the index of each argument. *)
  val monad_mapi : (int -> 'a -> 'b m) -> 'a list -> 'b list m

  (** Same as [monad_map] but the function takes two arguments. Throws an exception if the
      lengths of the lists differ. *)
  val monad_map2 : ('a -> 'b -> 'c m) -> 'a list -> 'b list -> 'c list m
end
