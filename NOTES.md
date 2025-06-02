How to deal with multisorted terms?

# Option 1: generate terms using mutual inductives

Pros:
- Same as Autosubst 2.
- Similar to how we do things on paper, i.e. easy to work with for users.

Cons:
- Lots of OCaml code (much more than Autosubst 2 eventhough we don't generate all useful lemmas).
- We can't use Equations when generating Rocq code, which is an issue because the generated code is already difficult to write _with_ Equations...
- We (probably?) can't use ssreflect when generating Rocq code, which makes things more cumbersome.
- Hard to maintain/extend: the generated Rocq code is very complex (much more complex than what Autosubst 2 generates). The proofs needed for the mapping between level 0 <-> 1 are especially complex.

# Option 2: generate a single term inductive + a sort judgement
