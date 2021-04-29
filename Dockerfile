FROM rust:1.49
RUN apt-get update && apt-get install -y \
  git python3-pip \
  && rm -rf /var/lib/apt/lists/*
RUN pip3 install pandas
RUN git clone -b releases/cav2021 https://github.com/eytans/TheSy.git /root/thesy/
WORKDIR /root/thesy/
RUN ln -s /usr/local/cargo/ ~/.cargo
RUN cargo build --release --features "stats"
RUN cargo install --path .