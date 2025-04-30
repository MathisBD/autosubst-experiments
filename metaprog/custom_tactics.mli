(** This module provides wrappers around Rocq tactics (of type [Proofview.tactic]), such
    as custom versions of [intro] or [auto]). *)

(** Small module which provides monadic notation for the [Proofview.tactic] monad.
    Typically one would import this inside a function using [let open PVMonad in ...]. *)
module PVMonad : sig
  (** [t1 >> t2] executes [t1] followed by [t2]. *)
  val ( >> ) : unit Proofview.tactic -> 'a Proofview.tactic -> 'a Proofview.tactic

  (** Monadic bind. *)
  val ( >>= ) : 'a Proofview.tactic -> ('a -> 'b Proofview.tactic) -> 'b Proofview.tactic

  (** Monadic return. *)
  val ret : 'a -> 'a Proofview.tactic

  (** Monadic bind, as a (let) operator. *)
  val ( let* ) : 'a Proofview.tactic -> ('a -> 'b Proofview.tactic) -> 'b Proofview.tactic
end

(** [intro_n n] introduces [n] variables/hypotheses with fresh names, but does not return
    the generated names to the caller. *)
val intro_n : int -> unit Proofview.tactic

(** [intro_fresh x] introduces a single variable/hypothesis with a fresh identifier built
    from [x], and returns the identifier of the variable introduced.

    Assumes exactly one goal is under focus. *)
val intro_fresh : string -> Names.Id.t Proofview.tactic

(** [intro_rewrite dir] introduces a single equality and rewrites with it. [dir] controls
    whether to rewrite left-to-right (if [true]) or right-to-left (if [false]). Default is
    left-to-right. *)
val intro_rewrite : dir:bool -> unit Proofview.tactic

(** [print_open_goals] prints a debug representation of each open goal. *)
val print_open_goals : unit Proofview.tactic

(** [dispatch tac] applies [tac i] to the [i-th] open goal (starting at [0]). *)
val dispatch : (int -> unit Proofview.tactic) -> unit Proofview.tactic

(** [auto ?depth ?lemmas ()] runs the tactic [auto] with:
    - maximum search depth [depth].
    - additional lemmas [lemmas].
    - the default hint database [core]. *)
val auto : ?depth:int -> ?lemmas:EConstr.t list -> unit -> unit Proofview.tactic

(** [rewrite dir eq] rewrites with equality [eq], which can be a global constant or a
    local variable. [dir] controls whether to rewrite left-to-right (if [true]) or
    right-to-left (if [false]). Default is left-to-right.

    Under the hood it uses [setoid_rewrite] (instead of [rewrite_strat]). *)
val rewrite : dir:bool -> Names.GlobRef.t -> unit Proofview.tactic
