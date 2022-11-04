FROM ubuntu:20.04

ENV DEBIAN_FRONTEND noninteractive

# Update apt db
RUN apt-get -y update
RUN apt-get -y upgrade

# Install preliminaries
RUN apt-get -y install build-essential \
  git sudo libx11-dev software-properties-common autoconf automake libtool intltool cmake
RUN apt-get -y install flex bison
RUN apt-get -y install python3

# Install z3, cvc4, cvc5
RUN apt-get install -y z3
RUN apt-get install -y --no-install-recommends wget unzip libgomp1 
RUN cd /opt \
  && wget https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt \
  && mv cvc4-1.8-x86_64-linux-opt /usr/bin/cvc4 \
  && chmod +x /usr/bin/cvc4
RUN cd /opt \
 && wget https://github.com/cvc5/cvc5/releases/latest/download/cvc5-Linux \
 && mv cvc5-Linux /usr/bin/cvc5 \
 && chmod +x /usr/bin/cvc5
RUN apt-get remove -y wget unzip \
  && rm -rf /var/lib/apt/lists/*

# Clone and build ABC
RUN mkdir /tools
WORKDIR /tools
RUN git clone https://github.com/vlab-cs-ucsb/ABC.git
WORKDIR /tools/ABC/build
RUN ./install-build-deps.py

# Install ocaml and required packages
RUN echo "yes" | add-apt-repository ppa:avsm/ppa
RUN apt-get -y install opam
RUN opam init --disable-sandboxing
RUN opam -y install dune.2.9.0 
RUN opam -y install merlin
RUN opam -y install menhir yaml

# Clone servois2
RUN mkdir /home/s2
WORKDIR /home/s2
RUN git clone -b explicit-dfs https://github.com/veracity-lang/servois2.git

