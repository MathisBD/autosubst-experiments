# Building 

Create a local opam switch with the required packages:
```
opam switch create . 4.14.2 --repos=default,rocq-released='https://coq.inria.fr/opam/released' -y
```

Optionally install development packages, e.g. for VS Code:
```
opam install ocaml-lsp-server user-setup ocamlformat vscoq-language-server
```

Build and install with:
```
dune build && dune install
```

# Signatures

Here is the grammar of signatures. Non-terminals are surrounded with square brackets, 
and [ident] stands for valid Rocq identifiers.

```
[signature] ::= {{ [sort_decl] [ctor_decl]* }} (* There must be exactly one sort declaration. *)

[sort_decl] ::= [ident] : Type              (* Declare a sort. *)
              | [ident] ( [ident] ) : Type  (* Declare a sort, specifying the name of 
                                               the variable constructor between parentheses. *)

[ctor_decl] ::= [ident] : [ctor_type]       (* Declare a constructor with the given type. )

[ctor_type] ::= [ident]
              | [arg_typ] -> [ctor_type]

[arg_type] ::= [ident]                      (* Just a sort. )
             | ( bind [ident]+ in [ident] ) (* Bind a list of sorts (from left to right) in a sort. *)
             | {{ [constr] }}               (* [constr] is any Rocq term of type [Set], [Prop], or [Type].
                                               Universe polymorphic terms will be instantiated with
                                               new monomorphic (global) universes. *)
```
