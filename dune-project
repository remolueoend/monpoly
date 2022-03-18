(lang dune 3.0)
(name monpoly)

(generate_opam_files true)
(cram enable)

(license "LGPL-2.1-only WITH OCaml-LGPL-linking-exception")
(maintainers "Joshua Schneider <joshua.schneider@inf.ethz.ch>")
(source (uri "git+https://bitbucket.org/jshs/monpoly.git"))
(homepage "https://infsec.ethz.ch/research/software/monpoly.html")
(bug_reports "https://bitbucket.org/jshs/monpoly/issues")

(package
  (name libmonpoly)
  (synopsis "Library for the MonPoly and VeriMon monitoring tools")
  (depends
    (ocaml (>= 4.13))
    (zarith (>= 1.11))))

(package
  (name monpoly)
  (synopsis "Check compliance of log files with respect to policies")
  (description "\
MonPoly and VeriMon are monitoring tools. They check the compliance of log files
with respect to policies that are specified by formulas in Metric First-Order
Temporal Logic (MFOTL) with aggregations.")
  (depends
    (libmonpoly (= version))
    dune-build-info))

(package
  (name monpoly-tools)
  (synopsis "Additional tools for the MonPoly and VeriMon monitors")
  (depends
    (libmonpoly (= version))
    (qcheck (>= 0.18))))
