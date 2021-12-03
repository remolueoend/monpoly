FROM infsec/verimon:1.3.0 as build-verimon
FROM infsec/monpoly:1.1.9 as build-monpoly
FROM infsec/aerial:1.0.0 as build-aerial
FROM infsec/hydra:1.0.0 as build-hydra
FROM infsec/monpoly:1.2.0 as build-verimon-old


FROM ubuntu:18.04

RUN apt-get update \
    && apt-get install --no-install-recommends -y \ 
        make \
        g++ \
        locales \
        gawk \
        bc \
        time \
        nano \
        scala \
        software-properties-common \
    && add-apt-repository ppa:openjdk-r/ppa \
    && apt-get update \
    && apt-get install --no-install-recommends -y \ 
       openjdk-11-jdk \
    && rm -rf /var/lib/apt/lists/*

RUN locale-gen en_US.UTF-8 \
    && echo "export LANG=en_US.UTF-8 LANGUAGE=en_US.en LC_ALL=en_US.UTF-8" >> /root/.bashrc

COPY --from=build-monpoly /usr/local/bin/monpoly /bin/monpoly
COPY --from=build-verimon /usr/local/bin/monpoly /bin/monpoly-verified
COPY --from=build-verimon /usr/local/bin/gen_log /bin/gen_log
COPY --from=build-verimon /usr/local/bin/gen_fma /bin/gen_fma
COPY --from=build-aerial /usr/local/bin/aerial /bin/aerial
COPY --from=build-aerial /usr/local/bin/gen_fma /bin/gen_mdl_fma
COPY --from=build-hydra /usr/local/bin/hydra /bin/hydra
COPY --from=build-verimon-old /usr/local/bin/monpoly /bin/monpoly-verified-old

USER root
ENV WDIR /home/root/monpoly
RUN mkdir -p ${WDIR}
WORKDIR ${WDIR}
ADD . ${WDIR}
RUN cp ./verimon /bin/verimon \
 && cp ./verimon-old /bin/verimon-old