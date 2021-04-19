FROM rust:1.49
RUN apt-get update && apt-get install -y \
  git \
  && rm -rf /var/lib/apt/lists/*
#RUN useradd -m aptly
#USER aptly
RUN git clone -b releases/cav2021 https://github.com/eytans/TheSy.git /thesy/
WORKDIR /thesy/
RUN cargo build --release --features "stats"
RUN cargo install --path .