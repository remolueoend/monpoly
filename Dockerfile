FROM ocaml/opam:alpine-3.15-ocaml-4.13-flambda AS build

RUN sudo apk add --no-cache \
    gmp-dev \
    m4 \
    && opam update

COPY --chown=opam:opam . build
WORKDIR build

RUN opam install -y --deps-only --ignore-constraints-on=libmonpoly . \
    && eval $(opam env) \
    && dune build --profile=release @install @runtest \
    && dune install --prefix=/home/opam/dist --relocatable monpoly monpoly-tools

FROM alpine:3.15

RUN apk add --no-cache gmp

COPY --from=build /home/opam/dist /usr/local/

ENV WDIR /work
WORKDIR $WDIR
ENTRYPOINT ["monpoly"]
