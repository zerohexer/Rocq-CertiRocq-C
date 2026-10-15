#!/bin/bash
# inside mattam82/metacoq:metarocq-1.5.1-rocq-9.1 (Rocq 9.1.1, MetaRocq 1.5.1, CompCert 3.17, coq-wasm 2.2.0 prebuilt)
# CertiRocq at the commit given as $1: pin, install (the steps of its CI)
set -ex
eval $(opam env) || true
sudo apt-get update -qq >/dev/null 2>&1 && sudo apt-get install -y -qq clang wabt >/dev/null 2>&1; clang --version | head -1
cd ~ && rm -rf certirocq && git clone -q https://github.com/CertiRocq/certirocq.git && cd certirocq && git checkout -q "$1"
git log -1 --format='COMMIT %H %cd'
grep -n "From MetaRocq" -r theories/Compiler/*.v | grep -o "Import.*" | tr ' ' '\n' | sort -u | grep "^E[A-Z]" | while read m; do find ~/.opam -name "$m.vo" | grep -q . || echo "MISSING-METAROCQ-MODULE $m"; done
opam pin add -n -y -k path rocq-certirocq .
date; opam install -y -j 2 rocq-certirocq --deps-only
date; opam install -y -v -j 2 rocq-certirocq
date; echo BUILD-DONE
