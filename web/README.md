# Web version of MonPoly & VeriMon

## Additional dependencies

Install the following packages using OPAM:

- `js_of_ocaml`
- `js_of_ocaml-lwt`
- `zarith_stubs_js`

The standard dependencies of MonPoly (see the main README) are needed as well.

## Build instructions

Run `dune build --profile=release` from this directory, or add the argument
`web` if your current directory is the project root.

This builds a ZIP archive `../_build/default/web/verimon_js.zip` which contains
all files needed to run the web version. The archive's contents can be deployed
to a web server, for example.
