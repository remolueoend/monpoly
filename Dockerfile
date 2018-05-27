FROM ocaml/opam:ubuntu-14.04_ocaml-4.04.1

RUN sudo apt-get install --no-install-recommends -y \ 
    subversion \
    && sudo rm -rf /var/lib/apt/lists/*

RUN opam install \
    ocamlfind

USER opam
ENV WDIR /home/opam/monpoly
RUN mkdir -p ${WDIR}
WORKDIR ${WDIR}
ADD . ${WDIR}
RUN sudo chown -R opam:opam . && eval `opam config env` && make monpoly && make clean && sudo cp ./monpoly /usr/local/bin/monpoly