FROM infsec/monpoly:1.4.0 as build-monpoly
FROM infsec/aerial:1.1.0 as build-aerial
FROM infsec/hydra:1.1.0 as build-hydra
# FROM infsec/monpoly:1.2.0 as build-verimon-old


FROM openjdk:18-jdk-alpine3.14

RUN apk add --no-cache gmp-dev fftw-dev make g++ gawk  bc  nano 
    
ENV SCALA_HOME=/usr/share/scala

RUN SCALA_VERSION=2.12.3 && \
    SCALA_SHA256_SUM=2b796ab773fbedcc734ba881a6486d54180b699ade8ba7493e91912044267c8c && \
    apk add --no-cache --virtual=.build-dependencies wget ca-certificates && \
    apk add --no-cache bash && \
    cd "/tmp" && \
    wget "http://downloads.typesafe.com/scala/${SCALA_VERSION}/scala-${SCALA_VERSION}.tgz" && \
    echo "${SCALA_SHA256_SUM}  scala-${SCALA_VERSION}.tgz" | sha256sum -c - && \
    tar xzf "scala-${SCALA_VERSION}.tgz" && \
    mkdir "${SCALA_HOME}" && \
    rm "/tmp/scala-${SCALA_VERSION}/bin/"*.bat && \
    mv "/tmp/scala-${SCALA_VERSION}/bin" "/tmp/scala-${SCALA_VERSION}/lib" "${SCALA_HOME}" && \
    ln -s "${SCALA_HOME}/bin/"* "/usr/bin/" && \
    apk del .build-dependencies && \
    rm -rf "/tmp/"*


COPY --from=build-monpoly /usr/local/bin/monpoly /bin/monpoly
RUN echo '#!/usr/bin/env bash' > /bin/verimon \
    echo 'exec "/bin/monpoly" -verified "$@"' >> /bin/verimon \
    & chmod a+x /bin/verimon
# temporary
RUN cp /bin/verimon /bin/verimon-old  
COPY --from=build-monpoly /usr/local/bin/gen_log /bin/gen_log
COPY --from=build-monpoly /usr/local/bin/gen_fma /bin/gen_fma
COPY --from=build-aerial /usr/local/bin/aerial /bin/aerial
# COPY --from=build-aerial /usr/local/bin/gen_fma /bin/gen_mdl_fma
COPY --from=build-hydra /usr/local/bin/hydra /bin/hydra

USER root
ENV WDIR /home/root/monpoly
RUN mkdir -p ${WDIR}
WORKDIR ${WDIR}
ADD . ${WDIR}
