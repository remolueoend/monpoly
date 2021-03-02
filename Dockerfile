FROM ocaml/opam2:ubuntu-18.04

RUN sudo apt-get update \
    && sudo apt-get install -y \
    m4 \
    libgmp-dev \
    && sudo rm -rf /var/lib/apt/lists/* 

RUN rm -rf /home/opam/.opam \
    && opam init -y \
    && opam update \
    && opam switch create 4.11.1 

RUN eval $(opam env) 

USER opam
ENV MDIR /monpoly
ENV WDIR /work
RUN sudo mkdir -p ${WDIR} \
    && sudo mkdir -p ${MDIR}
WORKDIR ${MDIR}

ADD . ${MDIR}
RUN sudo chown -R opam:opam . \
    && opam install --deps-only . 
RUN eval $(opam env) \
    && dune build --release \
    && dune test \
    && dune install
    # TODO add log_generator fma_generator and verimon 
RUN chmod +x ${MDIR}/run.sh \
    && sudo mv ${MDIR}/run.sh /run.sh
WORKDIR ${WDIR}
ENTRYPOINT ["/run.sh"]
