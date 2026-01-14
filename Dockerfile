# syntax=docker/dockerfile:1.4

#############################################################
## Stage 1: Base image
#############################################################
FROM docker.io/ubuntu:22.04 AS base

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    ca-certificates \
    curl \
    git \
    make \
    patch \
    unzip \
    wget \
    libgmp-dev \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

#############################################################
## Stage 2: Rocq/Coq installation
#############################################################
FROM base AS rocq-builder

RUN wget https://github.com/ocaml/opam/releases/download/2.3.0/opam-2.3.0-x86_64-linux -O /usr/local/bin/opam && \
    chmod +x /usr/local/bin/opam

RUN opam init --disable-sandboxing --yes --bare && \
    opam switch create ocaml-4.14.2 4.14.2 && \
    opam repo add coq-released https://coq.inria.fr/opam/released --all-switches

RUN opam pin add -yn --with-version 9.1.0 git+https://github.com/JasonGross/coq.git#v9.1+recursive-assumptions
RUN opam install -y --confirm-level=unsafe-yes coq.9.1.0
RUN opam install -y --confirm-level=unsafe-yes rocq-lean-import

#############################################################
## Stage 3: Lean + lean4export
#############################################################
FROM base AS lean-builder

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
ENV PATH="/root/.elan/bin:${PATH}"

# Install lean4export - pin to commit compatible with rocq-lean-import 0.0.1
ENV LEAN4EXPORT_COMMIT="c9f8373f8a37a65c0ed9bfd20480a3d7481a163e"
RUN git clone https://github.com/leanprover/lean4export.git /tmp/lean4export && \
    cd /tmp/lean4export && \
    git checkout $LEAN4EXPORT_COMMIT && \
    LEAN_TOOLCHAIN=$(cat lean-toolchain) && \
    elan default $LEAN_TOOLCHAIN && \
    lake build && \
    cp .lake/build/bin/lean4export /usr/local/bin/ && \
    rm -rf /tmp/lean4export

#############################################################
## Stage 4: Pre-compile base theories
#############################################################
FROM rocq-builder AS theories-builder

WORKDIR /workdir

# Copy theories directory
COPY theories /workdir/theories

# Generate _CoqProject listing all .v files
RUN echo "-Q theories IsomorphismChecker" > /workdir/_CoqProject && \
    find theories -name "*.v" | sort >> /workdir/_CoqProject

# Generate Makefile.coq from _CoqProject
RUN opam exec -- coq_makefile -f _CoqProject -o Makefile.coq

# Compile base theories in dependency order
RUN opam exec -- rocq c -Q theories IsomorphismChecker theories/Original.v
RUN opam exec -- rocq c -Q theories IsomorphismChecker theories/Hiding.v
RUN opam exec -- rocq c -Q theories IsomorphismChecker theories/PermittedAxiomPrinting.v
RUN opam exec -- rocq c -Q theories IsomorphismChecker theories/CaseSchemeDefinitions.v
RUN opam exec -- rocq c -Q theories IsomorphismChecker theories/IsomorphismDefinitions.v
RUN opam exec -- rocq c -Q theories IsomorphismChecker theories/Ltac2Utils.v
RUN opam exec -- rocq c -Q theories IsomorphismChecker theories/EqualityLemmas.v
RUN opam exec -- rocq c -Q theories IsomorphismChecker theories/IsomorphismStatementAutomationDefinitions.v
RUN opam exec -- rocq c -Q theories IsomorphismChecker theories/AutomationDefinitions.v

# Pre-compile all Interface files using make (handles dependencies)
# First pass with -k to continue on errors, second pass to ensure all compile
RUN find theories/Interface -type f -name "*.v" -exec echo "{}o" \; | xargs opam exec -- make -f Makefile.coq -kj4 || true
RUN find theories/Interface -type f -name "*.v" -exec echo "{}o" \; | xargs opam exec -- make -f Makefile.coq

# Note: Isomorphisms files are NOT pre-compiled because they depend on Imported.v
# which requires a result-specific Imported.out file

#############################################################
## Final image
#############################################################
FROM base

# Copy Rocq/Coq
COPY --from=rocq-builder /usr/local/bin/opam /usr/local/bin/opam
COPY --from=rocq-builder --chmod=755 /root/.opam /root/.opam
RUN echo 'eval $(opam env)' >> /etc/bash.bashrc

# Copy Lean
COPY --from=lean-builder /root/.elan /root/.elan
COPY --from=lean-builder /usr/local/bin/lean4export /usr/local/bin/lean4export
ENV PATH="/root/.elan/bin:${PATH}"

# Copy pre-compiled theories and build files
COPY --from=theories-builder /workdir/theories /workdir/theories
COPY --from=theories-builder /workdir/_CoqProject /workdir/_CoqProject
COPY --from=theories-builder /workdir/Makefile.coq /workdir/Makefile.coq

# Copy results
COPY results /workdir/results

# Copy scripts
COPY scripts/verify.sh /usr/local/bin/verify
COPY scripts/test-build.sh /usr/local/bin/test-build
RUN chmod +x /usr/local/bin/verify /usr/local/bin/test-build

# Verify tools are working
RUN bash -c 'eval $(opam env) && rocq --version'
RUN lean --version

# Run build test to verify theories compiled correctly
RUN /usr/local/bin/test-build

WORKDIR /workdir
