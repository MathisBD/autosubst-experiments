(lang dune 3.16)

(using coq 0.9)

(name autosubst-experiments)

(generate_opam_files true)

(package
 (name autosubst-experiments)
 (maintainers "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (authors "Mathis Bouverot-Dupuis")
 (homepage "https://github.com/MathisBD/autosubst-experiments")
 (bug_reports "https://github.com/MathisBD/autosubst-experiments/issues")
 (synopsis "Experimenting with a reflexive version of autosubst")
 (depends
  (coq
   (>= 8.20.0))
  (ocaml
   (= 4.14.1))))
