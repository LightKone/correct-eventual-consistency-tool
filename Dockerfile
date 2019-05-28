FROM ubuntu:16.04

#Installing mono

RUN apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF
RUN echo "deb http://download.mono-project.com/repo/ubuntu stable-xenial main" | tee /etc/apt/sources.list.d/mono-official-stable.list
RUN apt-get update
RUN apt-get -y install mono-devel

#Installing Z3

RUN apt-get update \
  && apt-get install -y git \
  && apt-get install -y python \
  && apt-get install -y build-essential \
  && git clone https://github.com/Z3Prover/z3.git \
  && cd z3 \
  && python scripts/mk_make.py \
  && cd build \
  && make \
  && make install \
  && cd / 
  
#Installing boogie

RUN git clone https://github.com/boogie-org/boogie.git \
  && cd boogie \
  && apt-get install -y wget \
  && wget https://dist.nuget.org/win-x86-commandline/latest/nuget.exe \
  && mono ./nuget.exe restore Source/Boogie.sln \
  && xbuild Source/Boogie.sln \
  && ln -s /usr/bin/z3 Binaries/z3.exe \
  && cd /

#testing it
#> docker run -it boogie
##### now inside the container
##> which z3
##  /usr/bin/z3
##> echo "type t = [int]bool" > test.bpl
##> mono boogie/Binaries/Boogie.exe test.bpl
##  Boogie program verifier version 2.3.0.61016, Copyright (c) 2003-2014, Microsoft.
##  test.bpl(2,1): error: ";" expected
##  1 parse errors detected in test.bpl

#Installing java
RUN apt-get -y update && apt-get -y upgrade && apt-get clean
RUN apt-get -y install default-jdk && apt-get clean

RUN mkdir -p /usr/src/app
WORKDIR /usr/src/app
# COPY . /usr/src/app
