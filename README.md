# This is a development clone of the original repository

MonPoly is a monitor for checking whether log files are policy
compliant.  Policies are specified by formulas in metric first-order
temporal logic (MFOTL) with aggregations [1,2].  Details on MFOTL and
the core monitoring algorithm are described in [1], while [2] presents
the extension to function symbols and aggregation operators.  A brief
overview of MonPoly is given in [3], while [4] presents a more
complete overview.  Two case studies in which MonPoly was used are
described in [5] and [6].


Requirements
============

OCaml compiler (http://caml.inria.fr/ocaml/index.en.html)
  MonPoly has been tested with version 3.12.1 of OCaml
  under Linux. It should also compile and work with most not-too-old
  versions of OCaml under other operating systems.

The following additional OCaml tools are used:
  ocamllex  for generating the lexers
  ocamlyacc for generating the parsers
  ocamldep  for generating dependencies between modules
  ocamldoc  for generating the documentation (optional)

On a Debian or Ubuntu system, the OCaml compiler and tools can be
installed with the command
  apt-get install ocaml
For installing OCaml on other systems, see the OCaml website
(http://caml.inria.fr/).  There you also find links to binary OCaml
distributions for other Linux distributions (Fedora, Red Hat, and
Gentoo), Microsoft Windows, and MacOS X.  For Microsoft Windows you
may need to install the Cygwin environment (http://www.cygwin.com/).


Compiling
=========

$ make monpoly

$ make clean      # optional, to delete the object and other generated files
$ make clean-all  # also deletes the executable and the documentation


Running
=======

Usage:
monpoly -sig <file> -formula <file> [-negate] [-log <file>]
        [-help] [-version] [-debug <unit>] [-verbose]
        [-check] [-sigout] [-unix] [-mem] [-nonewlastts]
        [-nofilterrel] [-nofilteremptytp] [-testfilter]"

The options are:
    -sig              Choose the signature file
    -formula          Choose the formula file
    -negate           Analyze the negation of the input formula
    -log              Choose the log file
    -version          Display the version (and exit)
    -debug            Choose unit to debug
    -verbose          Turn on verbose mode
    -check            Check if formula is monitorable (and exit)
    -sigout           Show the output signature (and exit)
    -unix             Timestamps represent Unix time
    -mem              Show memory usage on stderr
    -nonewlastts      Do not add a last maximal time-stamp
    -nofilterrel      Disable filter_rel module
    -nofilteremptytp  Disable filter_empty_tp module
    -testfilter       Test filter on the log without evaluating the formula



Example
=======

To run MonPoly on the "rv11" example, which is contained in the
example directory, start MonPoly as follows from a Unix shell:
  ./monpoly -sig examples/rv11.sig -formula examples/rv11.mfotl -log examples/rv11.log -negate

In this example, the formula file (examples/rv11.mfotl) contains the
policy expressed as a formula in MFOTL.  For background on MFOTL, see
[1].  In the example, the formula is
  publish(r) IMPLIES ONCE[0,7d] approve(r)
It expresses the policy that if a report is published then the report
must have been approved within the last 7 days.

The log file (examples/rv11.log) shows for each time point the tuples
in the relations.  For instance, the following 2 lines
  @1307955600 approve (163)
              publish (160)
mean that at a time point with time 1307955600 the relation approve
consists of the value 163 and the relation publish consists of the
value 160.  If time units such as days or hours are used in the
formula, then time is assumed to be Unix time.  MonPoly reads from
stdin if no log file is specified with the switch -log.

The relations used in the formula and the log must be specified in the
signature file (examples/rv11.sig).  In the example, the signature file
contains the 2 lines:
   publish(int)
   approve(int)
These specify that there are two relations, publish and approve, each
with a single parameter of type integer.  Relations can have multiple
parameters (separated by a comma) and parameters can also be of type
string.

When MonPoly processes the log file examples/rv11.log, it outputs to
stdout
   @1307955600 (time-point 1): (160)
   @1308477599 (time-point 2): (152)
The output means that at time point 1 (with time 1307955600) the
policy was violated by report 160 and at time point 2 (with time
1308477599) the policy was violated by report 152.  Note that since we
use the -negate switch, these are the violations with respect to the
given policy.  In other words, the output consists of the time points
and the valuations at which the negation of the formula from the
formula file is satisfied.  Error messages are written to stderr.


File Description
================

AUTHORS                 Authors of the tool
CHANGES                 Change log
LICENSE                 License file
README                  This file
Makefile                Commands to compile the monitor
/doc                    Directory for the documentation (generated with 'make doc')
/examples               Directory with some simple formulas and log files
/src                    Directory with the source code
  misc.ml[i]            Miscellaneous helper functions
  dllist.ml[i]          Module for operations on doubly-linked lists
  mqueue.ml[i]          Module for operations on queues
  predicate.ml[i]       Module for operations on predicates
  MFOTL.ml[i]           Module for operations on MFOTL formulas
  tuple.ml[i]           Module for operations on tuples
  relation.ml[i]        Module for operations on relations (sets of tuples)
  table.ml[i]           Module for operations on tables (named relations)
  db.ml[i]              Module for operations on databases (sets of tables)
  rewriting.ml[i]       Module for rewriting operations on MFOTL formulas
  sliding.ml[i]         Module implementing the sliding window algorithm
  algorithm.ml[i]       The monitoring algorithm
  formula_lexer.mll     Lexer for MFOTL formulas
  formula_parser.mly    Parser for MFOTL formulas
  log_parser.mll        Lexer for logs (in the general format)
  log_parser.mly        Parser for logs (in the general format)
  log.ml[i]             Module for parsing log files
  filter_empty_tp.ml[i] Module for filtering empty time-points
  filter_rel.ml[i]      Module for filtering tuples and relations
  perf.ml[i]            Module for performance evaluation
  main.ml               The tool's entry point
/tools                  Directory with various independent modules
  mfotl2sql.ml          Module for translating MFORT formulas to SQL queries
  table2log.ml[i]       Module for putting PostrgreSQL output into MonPoly's format

Contact
=======

If you encounter problems, please contact Eugen Zalinescu
(eugen.zalinescu@gmail.com).

We would highly appreciate it if you drop us an email when you are using
the tool in a project.  Feedback of any kind on the tool is welcome.


References
==========

[1] D. Basin, F. Klaedtke, S. Mueller, E. Zalinescu:
    "Monitoring Metric First-Order Temporal Properties"
    Journal of ACM, 62(2), 2015.

[2] D. Basin, F. Klaedtke, S. Marinovic, E. Zalinescu:
    "Monitoring of Temporal First-order Properties with Aggregations"
    Formal Methods in System Design, 46(3):262--285, 2015.

[3] D. Basin, M. Harvan, F. Klaedtke, E. Zalinescu:
    "MONPOLY: Monitoring usage-control policies"
    In the Proc. of the 2nd Int. Conf. on Runtime Verification (RV'11).

[4] D. Basin, F. Klaedtke, E. Zalinescu:
    "The MonPoly monitoring tool"
    In the Proc. of the RV-CuBES Workshop 2017.

[5] D. Basin, M. Harvan, F. Klaedtke, E. Zalinescu:
    "Monitoring usage-control policies in distributed systems"
    IEEE Transactions on Software Engineering, 39(10):1403-1426, 2013.

[6] D. Basin, G. Carroni, S. Ereth, M. Harvan, and H. Mantel:
    "Scalable Offline Monitoring of Temporal Properties"
    Formal Methods in System Design, Volume 49, Issue 1-2, 2016. 