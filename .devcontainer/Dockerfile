# source: https://github.com/johnnymn/ocaml-devcontainer/blob/master/.devcontainer/Dockerfile

FROM ocaml/opam:debian-ocaml-4.13

# Avoid warnings by switching to noninteractive
ENV DEBIAN_FRONTEND=noninteractive

ARG USERNAME=vscode
ARG USER_UID=1000
ARG USER_GID=$USER_UID

USER root

# hadolint ignore=DL3008
RUN apt-get update \
    && apt-get -y install --no-install-recommends \
    libgmp-dev \
    m4 \
    #
    # Clean up
    && apt-get autoremove -y \
    && apt-get clean -y \
    && rm -rf /var/lib/apt/lists/*

# [Optional] Update UID/GID if needed
RUN if [ "$USER_GID" != "1000" ] || [ "$USER_UID" != "1000" ]; then \
    groupmod --gid $USER_GID $USERNAME \
    && usermod --uid $USER_UID --gid $USER_GID $USERNAME \
    && chown -R $USER_UID:$USER_GID /home/$USERNAME; \
    fi

USER opam

# Install Opam packages
RUN opam update && \
    opam install \
    dune \
    ocaml-lsp-server \
    ocamlformat=0.21.0 \
    ocamlformat-rpc \
    ppx_inline_test \
    qcheck \
    utop \
    zarith

# Switch back to dialog for any ad-hoc use of apt-get
ENV DEBIAN_FRONTEND=dialog

# Add opam binaries to PATH.
ENV PATH=/home/opam/.opam/4.13/bin:$PATH
