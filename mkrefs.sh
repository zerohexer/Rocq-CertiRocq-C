#!/bin/bash
# mkrefs.sh : (inside the image, in /w) evaluate the ORIGINAL programs (Z, lists) inside Rocq on the current random
# cases and keep "result checksum" per program in case/NAME.ref
eval $(opam env); cd /w/case && ulimit -s unlimited
for f in *_ref.v; do n=${f%_ref.v}
  timeout 400 rocq c $f 2>&1 | tr -d '\n' | sed 's/.*= *(\(-\{0,1\}[0-9]*\), *\(-\{0,1\}[0-9]*\)).*/\1 \2/' | cut -c1-80 > $n.ref
  echo "$n: $(cat $n.ref)"
done
