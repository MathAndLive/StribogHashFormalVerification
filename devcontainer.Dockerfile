FROM debian:latest

RUN apt-get update && apt-get install -y opam libgmp-dev pkg-config m4 curl

# Initialize OPAM and setup environment
RUN opam init --disable-sandboxing -y \
 && opam update \
 && echo 'eval $(opam env)' >> /root/.bashrc

# Use a login shell to install Coq and vscoq
RUN bash -c "source /root/.opam/opam-init/init.sh > /dev/null 2>&1 && \
             opam install coq.8.16.1 -y && \
             opam install vscoq-language-server -y && \
             opam repo add coq-released https://coq.inria.fr/opam/released -y && \
             opam pin add coq-vst 2.15"

# Set environment variables permanently
ENV PATH="/root/.opam/default/bin:${PATH}"
ENV OPAMROOT="/root/.opam"

CMD ["/bin/bash"]
