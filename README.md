MonPoly
=======

**This is a development fork of the [original
repository](https://bitbucket.org/monpoly/monpoly).**

MonPoly is a prototype monitoring tool. It checks the compliance of log files
with respect to policies that are specified by formulas in Metric First-Order
Temporal Logic (MFOTL).

An overview of the tool, including its usage and history, can be found in this
[paper](https://sourceforge.net/projects/monpoly/files/monpoly.pdf/download).

The tool is developed as part of an academic project at ETH Zurich. For more
details on the project please visit
[this link](https://www.infsec.ethz.ch/research/projects/mon_enf).


Installation
------------

To compile and install MonPoly, you need the [OCaml compiler](https://ocaml.org)
and the [Dune build system](https://dune.readthedocs.io). MonPoly has been
tested with version 4.13.1 of [OCaml](https://ocaml.org) under Linux. It should
also compile under other Unix-like operating systems (e.g., Apple macOS). For
Microsoft Windows you may need to install the [Cygwin
environment](https://www.cygwin.com/).

### Requirements

The easiest way to obtain the compiler and Dune is using the [OPAM package
manager](https://opam.ocaml.org). On a Debian or Ubuntu system, it can be
installed with the command
```
apt-get install opam
```
For installing OPAM on other systems, see the
[website](https://opam.ocaml.org/doc/Install.html).

Use the following commands to prepare the compiler. You can use a different
version of OCaml at your own risk.
```
opam init  # skip this if you have used OPAM before
opam switch create 4.13.1
eval $(opam env)
```

Missing dependencies including Dune can be installed with
```
opam install --deps-only --ignore-constraints-on=libmonpoly .
```

### Quick installation

To compile and install MonPoly, just do
```
dune build --release
dune install
```
in the root directory of the project. Assuming that OPAM has been set up
correctly, the `monpoly` command should then be available to the installing
user. You can pass a custom installation path to the install command with the
`--prefix=PATH` option. For example, `dune install --prefix=/usr/local` makes
MonPoly globally available to all users.

To uninstall MonPoly, do
```
dune uninstall
```
If you used `--prefix`, you must supply it again with the same path.

### Manual build

If you want to compile MonPoly manually, e.g., for development purposes, you may
find the following commands useful. They assume that Dune >= 2.8 is available.
```
# Compile the project:
dune build

# Compile the project in release mode:
dune build --release

# Run automatic tests:
dune test

# Run the previously compiled MonPoly executable:
dune exec -- monpoly [ARGUMENTS ...]

# Remove build artifacts:
dune clean
```

Running
-------

Usage:
```
monpoly -sig <file> -formula <file> [-negate] [-log <file>]
        [-help] [-version] [-debug <unit>] [-verbose]
        [-check] [-sigout] [-unix] [-mem] [-nonewlastts]
        [-nofilterrel] [-nofilteremptytp]
```

The options are:
```
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
    -nonewlastts      Do not add a last maximal timestamp
    -nofilterrel      Disable filter_rel module
    -nofilteremptytp  Disable filter_empty_tp module
```


Example
-------

To run MonPoly on the `rv11` example, which is contained in the
`examples` directory, start MonPoly as follows from a Unix shell:
```
  $ ./monpoly -sig examples/rv11.sig -formula examples/rv11.mfotl -log examples/rv11.log -negate
```

In this example, the formula file (`examples/rv11.mfotl`) contains the
policy expressed as a formula in MFOTL.  For background on MFOTL, see
[1].  In the example, the formula is
```
  publish(r) IMPLIES ONCE[0,7d] approve(r)
```
It expresses the policy that if a report is published then the report
must have been approved within the last 7 days.

The log file (`examples/rv11.log`) shows for each time point the tuples
in the relations.  For instance, the following 2 lines
```
  @1307955600 approve (163)
              publish (160)
```
mean that at a time point with time 1307955600 the relation approve
consists of the value 163 and the relation publish consists of the
value 160.  If time units such as days or hours are used in the
formula, then time is assumed to be Unix time.  MonPoly reads from
stdin if no log file is specified with the switch `-log`.

The relations used in the formula and the log must be specified in the
signature file (`examples/rv11.sig`).  In the example, the signature file
contains the 2 lines:
```
   publish(x:int)
   approve(x:int)
```
These specify that there are two relations, publish and approve, each
with a single parameter of type integer.  Relations can have multiple
parameters (separated by a comma) and parameters can also be of type
string.

When MonPoly processes the log file examples/rv11.log, it outputs to
stdout
```
   @1307955600 (time-point 1): (160)
   @1308477599 (time-point 2): (152)
```
The output means that at time point 1 (with time 1307955600) the
policy was violated by report 160 and at time point 2 (with time
1308477599) the policy was violated by report 152.  Note that since we
use the `-negate` switch, these are the violations with respect to the
given policy.  In other words, the output consists of the time points
and the valuations at which the negation of the formula from the
formula file is satisfied.  Error messages are written to stderr.


File Description
----------------

```
AUTHORS                 Authors of the tool
CHANGES                 Change log
LICENSE                 License file
README                  This file
dune-project            Project meta data for the Dune build system
monpoly.opam            OPAM package description (generated by Dune)
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
  dune                  Build instructions
/tests                  Directory with automated tests (run with 'dune test')
```

References
----------

Details on MFOTL and the core monitoring algorithm are described in
[1], while [2] presents the extension to function symbols and
aggregation operators.  A brief overview of MonPoly is given in [3],
while [4] presents a more complete overview.  Two case studies in
which MonPoly was used are described in [5] and [6].



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
