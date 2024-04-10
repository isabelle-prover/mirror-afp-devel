# syntax=docker/dockerfile:1

FROM makarius/isabelle AS builder

USER root

# install dependencies
RUN \
    apt-get update -y && \
    apt-get install -y --no-install-recommends \
        curl \
        libnuma-dev \
        zlib1g-dev \
        libgmp-dev \
        libgmp10 \
        git \
        wget \
        lsb-release \
        software-properties-common \
        gnupg2 \
        apt-transport-https \
        gcc \
        autoconf \
        automake \
        build-essential \
	texlive-luatex \
	texlive-latex-base \
	texlive-plain-generic \
	texlive-latex-recommended \
	texlive-fonts-recommended

# install ghcup
RUN \
    curl https://downloads.haskell.org/~ghcup/x86_64-linux-ghcup > /usr/bin/ghcup && \
    chmod +x /usr/bin/ghcup

ARG GHC=9.4.2
ARG CABAL=3.8.1.0

# install GHC and cabal
RUN \
    ghcup -v install ghc --isolate /usr/local --force ${GHC} && \
    ghcup -v install cabal --isolate /usr/local/bin --force ${CABAL}

USER isabelle

# set up Isabelle
ENV PATH="$PATH:/home/isabelle/Isabelle/bin"

# set up the AFP

RUN curl https://www.isa-afp.org/release/afp-current.tar.gz > afp-current.tar.gz && \
    tar xzf afp-current.tar.gz && \
    rm afp-current.tar.gz && \
    mv afp-* afp && \
    isabelle components -u /home/isabelle/afp/thys

WORKDIR /home/isabelle/secav-prover

USER root
RUN chown -R isabelle:isabelle /home/isabelle/secav-prover
USER isabelle

COPY --chown=isabelle  . .

RUN cabal update
RUN make
RUN cabal install secav-prover

FROM ubuntu:22.04

WORKDIR /root/
COPY --from=builder /home/isabelle/.cabal/bin/secav-prover ./

ENTRYPOINT ["./secav-prover"]
