FROM krinkin/rv64-toolchain:latest

ENV RUST_VERSION=1.89.0 \
	PATH=/root/.cargo/bin:$PATH

COPY . /ws

RUN <<EOF
apt-get update && \
apt-get install -y curl && \
curl -O https://static.rust-lang.org/rustup/dist/x86_64-unknown-linux-gnu/rustup-init && \
chmod +x rustup-init && \
./rustup-init -y --no-modify-path --default-toolchain $RUST_VERSION && \
rm rustup-init && \
rustc --version && \
cargo --version && \
rm test.c && \
rustup component add rustfmt && \
cargo build && \
cp target/debug/risc-v-sim /usr/bin && \
cd riscv-samples && \
make capture
EOF