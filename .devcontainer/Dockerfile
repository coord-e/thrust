# syntax=docker/dockerfile:1

FROM mcr.microsoft.com/devcontainers/rust:1-bookworm

ADD --checksum=sha256:bc31ad12446d7db1bd9d0ac82dec9d7b5129b8b8dd6e44b571a83ac6010d2f9b \
  https://github.com/Z3Prover/z3/releases/download/z3-4.13.0/z3-4.13.0-x64-glibc-2.31.zip \
  /tmp/
RUN unzip /tmp/z3-4.13.0-x64-glibc-2.31.zip -d /opt/ \
  && rm /tmp/z3-4.13.0-x64-glibc-2.31.zip \
  && echo 'PATH=$PATH:/opt/z3-4.13.0-x64-glibc-2.31/bin' > /etc/profile.d/99-z3.sh
