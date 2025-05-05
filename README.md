# Building 

Create a local opam switch with the required packages:
```
opam switch create . 4.14.2 --repos=default,coq-released='https://coq.inria.fir/opam/released' -y
```

Optionally, install development packages, e.g. for VS Code:
```
opam install ocaml-lsp-server user-setup ocamlformat vscoq-language-server
```

Build with (`dune install` is required to step through Rocq files in VS Code):
```
dune build && dune install
```