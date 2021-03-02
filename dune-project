(lang dune 2.8)
(name monpoly-dev)

(generate_opam_files true)
(cram enable)

(license "LGPL-2.1-only WITH OCaml-LGPL-linking-exception")
(maintainers "Joshua Schneider <joshua.schneider@inf.ethz.ch>")
(source (uri "git+https://bitbucket.org/jshs/monpoly.git"))
(homepage "https://infsec.ethz.ch/research/software/monpoly.html")
(bug_reports "https://bitbucket.org/jshs/monpoly/issues")

(package
  (name monpoly-dev)
  (synopsis "Check compliance of log files with respect to policies")
  (description "\
MonPoly is a prototype monitoring tool. It checks the compliance of log files
with respect to policies that are specified by formulas in Metric First-Order
Temporal Logic (MFOTL) with aggregations.")
  (depends
    (ocaml (>= 4.11))
    (dune (>= 2.8))
    dune-build-info
    (zarith (>= 1.11))))
