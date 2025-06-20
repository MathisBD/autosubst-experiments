(lang dune 3.16)

(using coq 0.9)

(name rocq-sulfur)

(generate_opam_files true)

(package
 (name rocq-sulfur)
 (maintainers "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (authors "Mathis Bouverot-Dupuis")
 (homepage "https://github.com/MathisBD/autosubst-experiments")
 (bug_reports "https://github.com/MathisBD/autosubst-experiments/issues")
 (synopsis "A tool to deal with syntax and binders.")
 (depends
  (coq
   (= 8.20.0))
  coq-equations))
