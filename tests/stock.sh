#!/bin/bash
# tests/stock.sh   (inside the UNMODIFIED image kernelq-certirocq:1b45a1aa, in /w, after setup.sh)   STOCK, FOR COMPARISON.
# Every program of hand/ and every corpus text (rebuilt pairs removed, as in the table), compiled the way CertiRocq
# comes: no translator, no checker, no compiler patch, its default settings, its own runtime and integer operations
# (a nat is Rocq's own chain of cells), no clean-up of the C.  What it shares with our pipeline: the memory (rd / upd
# and the test harness of sup/v4: a program of this kind needs one) and the C compiler with the same flags.  The line
# `let kq_keep := kq_case ..` of every `main` (dead: it keeps KQNat.v's three definitions in the compiled program) is
# left out, since there is no KQNat.v here.
# Then each is run on its problem's large input as table.sh runs ours (best of N, one pinned core), answers compared.
cd /w && ulimit -s unlimited; eval $(opam env)
N=${N:-3}; D=stock; mkdir -p $D bin
RT=$(ls -d ~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime)
cp KQRun.v $D/ && (cd $D && rocq c -R . KQ KQRun.v) || exit 1
EXT='Extract Constants [ rd => "kq_rdb", upd => "kq_updb", kq_arg => "kq_arg", kq_input => "kq_input", kq_sum => "kq_sum", kq_in => "kq_in", kq_out => "kq_out", rd32 => "kq_rd32", upd32 => "kq_upd32" ]'
ftr() { echo; echo "CertiRocq Compile --output \"$1_prog\" main"; echo "$EXT"; echo 'Include [ "kq_io.h" ].'; }
build() {  # build NAME   ($D/NAME.v written)
  local n=$1
  (cd $D && timeout 900 rocq c -R . KQ $n.v > $n.log 2>&1) || { echo "$n ROCQ-FAIL: $(grep -A3 '^Error' $D/$n.log | head -4 | tr '\n' ' ' | cut -c1-200)"; return; }
  clang -w -O2 -flto -DKQ_NO_PRIM_INLINE -Isup/v4 -I$RT -I$D -o bin/stock_$n sup/v4/kq_io3.c $D/${n}_prog.c $RT/gc_stack.c $RT/prim_int63.c 2> $D/$n.err || echo "$n CC-FAIL: $(grep -m2 error $D/$n.err)"
}
for b in hand/*.body; do x=$(basename $b .body)
  { echo 'From CertiRocq.Plugin Require Import CertiRocq.'; echo 'Require Import KQ.KQRun.'; echo 'Open Scope sint63_scope.'; echo 'Open Scope bool_scope.'; echo
    sed '/let kq_keep := kq_case/d' $b; ftr H_$x; } > $D/H_$x.v; build H_$x
done
for f in sv/*.sv; do x=$(basename $f .sv)
  python3 sv2fast.py --eta $f E_$x 2> /dev/null | sed -e 's/^Require Import KQ\..*/Require Import KQ.KQRun./' -e '/^MetaRocq Run/d' -e '/^CertiRocq Extract Inline/d' \
    -e '/^CertiRocq Compile/d' -e '/^Extract Constants/d' -e '/^Include \[/d' -e '/let kq_keep := kq_case/d' > $D/E_$x.v && ftr E_$x >> $D/E_$x.v && build E_$x
done
E=()
while read -r name p mem what; do m=""; [ "$mem" = "-" ] || m=":$mem"; E+=("stock H_$name=bin/stock_H_$name:$p$m"); done < <(grep -v '^#' hand.tsv)
while read -r p d prog; do [ "$prog" = "-" ] || E+=("stock E_$prog=bin/stock_E_$prog:$p"); done < <(grep -v '^#' problems.tsv)
LW=34 N=$N bash bench.sh "${E[@]}"
