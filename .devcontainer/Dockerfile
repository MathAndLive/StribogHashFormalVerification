FROM debian:latest

RUN apt-get update

RUN apt-get install -y opam libgmp-dev pkg-config m4 curl

# Initialize OPAM and setup environment
RUN opam init --disable-sandboxing -y

RUN opam update
RUN echo 'eval $(opam env)' >> /root/.bashrc

RUN opam install coq.8.20.1 -y
RUN opam install vscoq-language-server -y
RUN opam repo add coq-released https://coq.inria.fr/opam/released -y
RUN opam pin add coq-vst 2.15 -y

# Set environment variables permanently
ENV PATH="/root/.opam/default/bin:${PATH}"
ENV OPAMROOT="/root/.opam"

CMD ["/bin/bash"]