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

(** A direction in which to rewrite (using an equality). *)
type rewrite_direction = LeftToRight | RightToLeft

(** [intro_n n] introduces [n] variables/hypotheses with fresh names, but does not return
    the generated names to the caller. *)
val intro_n : int -> unit Proofview.tactic

(** [intro_fresh x] introduces a single variable/hypothesis with a fresh identifier built
    from [x], and returns the identifier of the variable introduced.

    Assumes exactly one goal is under focus. *)
val intro_fresh : string -> Names.Id.t Proofview.tactic

(** [intro_rewrite dir] introduces a single equality and rewrites with it. [dir] controls
    in which direction to rewrite. *)
val intro_rewrite : rewrite_direction -> unit Proofview.tactic

(** [print_open_goals ()] prints a debug representation of each open goal. *)
val print_open_goals : unit -> unit Proofview.tactic

(** [dispatch tac] applies [tac i] to the [i-th] open goal (starting at [0]). *)
val dispatch : (int -> unit Proofview.tactic) -> unit Proofview.tactic

(** [auto ?depth ?lemmas ()] runs the tactic [auto] with:
    - maximum search depth [depth].
    - additional lemmas [lemmas].
    - the default hint database [core]. *)
val auto : ?depth:int -> ?lemmas:EConstr.t list -> unit -> unit Proofview.tactic

(** [rewrite dir eq] rewrites with equality [eq], which can be a global constant or a
    local variable. [dir] controls in which direction to rewrite.

    Under the hood it uses [setoid_rewrite] (instead of [rewrite_strat]). *)
val rewrite : rewrite_direction -> Names.GlobRef.t -> unit Proofview.tactic

(** [repeat_n n tac] applies [tac] exactly [n] times and returns the list of results. *)
val repeat_n : int -> 'a Proofview.tactic -> 'a list Proofview.tactic

(** [pattern t] abstracts the conclusion over all occurences of [t]. *)
val pattern : EConstr.t -> unit Proofview.tactic

(** [induction t] performs induction over [t]. *)
val induction : EConstr.t -> unit Proofview.tactic

(** [destruct t] destruct [t]. *)
val destruct : EConstr.t -> unit Proofview.tactic
