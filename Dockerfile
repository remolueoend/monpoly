FROM ocaml/opam2:ubuntu-18.04

RUN sudo apt-get update \
    && sudo apt-get install -y \
    subversion \
    m4 \
    && sudo rm -rf /var/lib/apt/lists/* 

# RUN opam init -y \
RUN opam switch create 4.06.1 \
    && opam install \
       ocamlfind \
       num

# RUN useradd -ms /bin/bash monply
USER opam
ENV WDIR /home/opam/monpoly
RUN mkdir -p ${WDIR}
WORKDIR ${WDIR}

ADD . ${WDIR}
RUN sudo chown -R opam:opam . && eval `opam config env` && make && make generator && make clean && sudo cp ./monpoly /usr/local/bin/monpoly && sudo cp ./tools/gen_log /usr/local/bin/gen_log