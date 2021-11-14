FROM ubuntu:bionic

RUN apt-get -y update
RUN apt-get -y upgrade

RUN apt-get -y install apt-utils
RUN apt-get -y install build-essential
RUN apt-get -y install git
RUN apt-get -y install wget
RUN apt-get -y install openjdk-8-jdk

RUN echo "SecC version 0.1.4"

WORKDIR /usr/local
RUN wget https://downloads.lightbend.com/scala/2.12.8/scala-2.12.8.tgz 
RUN tar xf scala-2.12.8.tgz 
ENV SCALA_HOME /usr/local/scala-2.12.8
ENV PATH "${SCALA_HOME}/bin:${PATH}"

WORKDIR /usr/local
RUN wget https://isabelle.in.tum.de/website-Isabelle2018/dist/Isabelle2018_app.tar.gz
RUN tar xf Isabelle2018_app.tar.gz
ENV ISABELLE_HOME /usr/local/Isabelle2018
ENV PATH "${ISABELLE_HOME}/bin:${PATH}"

RUN useradd -m -s /bin/bash secc
USER secc
WORKDIR /home/secc

RUN git clone https://bitbucket.org/covern/secc.git
RUN git clone https://bitbucket.org/covern/seccsl.git

WORKDIR /home/secc/secc
RUN make
RUN ./secc examples/*.c

WORKDIR /home/secc/seccsl
RUN isabelle build -c -d . -v SecCSL

WORKDIR /home/secc
