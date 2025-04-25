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
