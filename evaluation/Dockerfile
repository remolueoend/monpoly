FROM infsec/monpoly:1.2.0 as build

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

COPY --from=build /usr/local/bin/monpoly /bin/monpoly
COPY --from=build /usr/local/bin/gen_log /bin/gen_log
COPY --from=build /usr/local/bin/gen_fma /bin/gen_fma
USER root
ENV WDIR /home/root/monpoly
RUN mkdir -p ${WDIR}
WORKDIR ${WDIR}
ADD . ${WDIR}
