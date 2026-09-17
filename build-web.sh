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
