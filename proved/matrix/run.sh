#!/bin/bash
# proved/matrix/run.sh [OUT]: run the construct table.  Every cell (or only the cells whose names contain one of the
# patterns in PATT, separated by +) goes through the real translator and the real prover; one result line per cell is written
# to OUT/results.txt (default OUT: proved/matrix/out) and classify.py prints the verdicts.  MD=1 also writes
# proved/matrix/MATRIX.md, for a full run.  PJ cells run at a time (default 3).
# Run in the image, in the repository, after proved/make.sh.  Example: PATT=A_par_option+P_mem bash proved/matrix/run.sh
cd "$(dirname "$0")/../.." || exit 1
[ -f proved/KQLPrint.vo ] || { echo "run proved/make.sh first" >&2; exit 1; }
OUT=${1:-proved/matrix/out}
ulimit -c 0; ulimit -s unlimited
export KQ_STRICT=1 KQ_TIMEOUT=${KQ_TIMEOUT:-120} KQ_JOBS=1
rm -rf "$OUT"; python3 proved/matrix/gen.py "$OUT" > /dev/null || exit 1
for p in $(echo "${PATT:-_}" | tr + ' '); do ls "$OUT"/*"$p"*.body 2>/dev/null; done | sort -u > "$OUT/cells.list"
# every cell is translated afresh: the translator may have changed since its last run
for b in $(cat "$OUT/cells.list"); do n=$(basename "$b" .body); rm -f "proved/gen/${n}_t.vo" "proved/gen/${n}_t.glob"; done
xargs -P "${PJ:-3}" -I{} sh -c 'python3 proved/kitc.py --no-build {} 2>&1 | grep -v "^Warning\|^to KQC\|^$" | head -3 |
  tr "\n" " " | cut -c1-400; echo' < "$OUT/cells.list" > "$OUT/results.txt"
python3 proved/matrix/classify.py "$OUT/results.txt" ${MD:+--md proved/matrix/MATRIX.md}
