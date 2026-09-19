#!/bin/sh
set -eu

cargo build --release --target wasm32-unknown-unknown --bin lambda-microegg
mkdir -p pkg
wasm-bindgen \
  target/wasm32-unknown-unknown/release/lambda-microegg.wasm \
  --out-dir pkg \
  --out-name lambda_microegg \
  --target web \
  --no-typescript

# Exercise the generated JavaScript and WASM, rather than only the native
# Rust entry point used by `cargo test`.
node --experimental-default-type=module tests/web-smoke.mjs
