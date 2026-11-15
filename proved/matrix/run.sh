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
# (KQ_SESSION=2) PJ Rocq sessions, each checking cell after cell with the libraries loaded once (proved/kqsess.py); a cell takes a free one
if [ "$KQ_SESSION" = 2 ]; then
  export KQ_SESS_DIR=$(mktemp -d) KQ_SESS_N=${PJ:-3}; SP=""
  for i in $(seq 0 $((KQ_SESS_N - 1))); do python3 proved/kqsess.py "$KQ_SESS_DIR" $i & SP="$SP $!"; done
  for i in $(seq 0 $((KQ_SESS_N - 1))); do w=0; while [ ! -S "$KQ_SESS_DIR/s$i.sock" ] && [ $w -lt 600 ]; do sleep 0.1; w=$((w + 1)); done; done
fi
xargs -P "${PJ:-3}" -I{} sh -c 'python3 proved/kitc.py --no-build {} 2>&1 | grep -v "^Warning\|^to KQC\|^$" | head -3 |
  tr "\n" " " | cut -c1-400; echo' < "$OUT/cells.list" > "$OUT/results.txt"
[ "$KQ_SESSION" = 2 ] && { kill $SP 2>/dev/null; wait; rm -rf "$KQ_SESS_DIR"; }
python3 proved/matrix/classify.py "$OUT/results.txt" ${MD:+--md proved/matrix/MATRIX.md}
