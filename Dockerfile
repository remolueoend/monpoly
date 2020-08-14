FROM ocaml/opam2:ubuntu-18.04

RUN sudo apt-get update \
    && sudo apt-get install -y \
    subversion \
    m4 \
    libgmp-dev \
    && sudo rm -rf /var/lib/apt/lists/* 

# RUN opam init -y \
RUN opam update \
    && opam switch create 4.06.1 \
    && opam install \
       ocamlfind \
       qcheck \
       zarith \
       num

# RUN useradd -ms /bin/bash monply
USER opam
ENV WDIR /home/opam/monpoly
RUN mkdir -p ${WDIR}
WORKDIR ${WDIR}

ADD . ${WDIR}
RUN sudo chown -R opam:opam . \
    && eval `opam config env` \
    && make \
    && make log_generator \
    && make fma_generator \
    && sudo cp ./monpoly /usr/local/bin/monpoly \
    && sudo cp ./verimon /usr/local/bin/verimon \
    && sudo cp ./tools/gen_log /usr/local/bin/gen_log \
    && sudo cp ./tools/gen_fma /usr/local/bin/gen_fma \
    && make clean 

