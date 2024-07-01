FROM ubuntu:22.04

COPY . ./home
RUN apt-get update
RUN apt-get install nano libxml2 gcc python3-distutils openjdk-8-jdk -y
RUN ln -s /usr/lib/x86_64-linux-gnu/libmpfr.so.6 /usr/lib/x86_64-linux-gnu/libmpfr.so.4
ENTRYPOINT ["/bin/bash"]
WORKDIR "/home"