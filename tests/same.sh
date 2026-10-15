#!/bin/bash
# tests/same.sh [TAG]   (inside the PATCHED image, in /w, after regen.sh)  THE SAME LOOP WRITTEN MANY WAYS.
# "Consistent" as something a machine can check: two ways of writing the same loop must give the same speed.
# Every way of every kernel of tests/mksame.py is
#   1  put in the standard form by the translator, with each choice between two numbers COUNTING its wrong guesses,
#      and run once (as prof.sh does for a real program);
#   2  put in the standard form with the choices made as measured, compiled, built;
#   3  run: every way of a kernel must give the same answer; the time of each (best of N, one pinned fast core) is
#      set against the kernel's first way.
# Two ways that come out of the translator as THE SAME C (letter for letter, names aside: tests/cnorm.py) are marked
# with the same letter: they are the same machine code, whatever a clock says.
#   TOL=1.15      a way marked `same` that is slower than TOL times its kernel's first way fails the gate
#   KQ=0          build every way AS WRITTEN (no translator, no measured choices): what the test showed before
#   KQBOUNDS=proofs   the bounds proofs (step 3 of the translator) for every way; the default is the tests
#   SKIPGEN=1     do not write and compile the Rocq again (the C is there)       SKIPBUILD=1   time what is built
#   XFLAGS=".."   more flags for the C compiler       GEN=FILE  another generator of ways (same layout)
#   D=DIR         where the ways are written          PFX=S     the prefix of the programs' names
# On the host (not in a container) the machine's counters are read too: instructions and wrong guesses per way.
[ -d /w ] && cd /w; ulimit -s unlimited
T=${1:-same}; N=${N:-5}; KQCPU=${KQCPU:-4}; TOL=${TOL:-1.15}; D=${D:-dbg/same}; GEN=${GEN:-tests/mksame.py}; PFX=${PFX:-S}
KQ=${KQ:-1}; TH=${TH:-10}; MINN=${MINN:-1000}
gen() {  # gen NAME PROGRAM MODE   (MODE empty: as written)
  if [ -z "$3" ]; then { cat hand/hdr.txt; echo; cat $D/$1.body; sed "s/%s/$2/" hand/ftr.txt; } > fast/$2.v
  else { cat hand/hdr.txt; echo; cat $D/$1.body; sed -e "s/%s/$2/" -e "s/%m/$3/" -e "s/%o/${KQORD:-3}/" -e "s/%b/$(bash bounds.sh $1)/" hand/ftr_kq.txt; } > fast/$2.v; fi
  timeout 300 rocq c -R . KQ fast/$2.v > fast/$2.log 2>&1 || echo "$2 ROCQ-FAIL: $(grep -A6 '^Error' fast/$2.log | head -7 | tr '\n' ' ' | cut -c1-260)"
}
if [ -z "$SKIPBUILD" ]; then
  eval $(opam env)
  if [ -z "$SKIPGEN" ]; then
    python3 $GEN $D > /dev/null || exit 1
    if [ "$KQ" = 1 ]; then
      SET=""; while IFS=$'\t' read -r name kernel kind; do gen $name ${PFX}I_$name PInstr; SET="$SET ${PFX}I_$name"; done < $D/same.tsv
      MODES=gc SET="$SET" bash mk.sh ${T}i | grep -i fail
      while IFS=$'\t' read -r name kernel kind; do
        KQ_MEM=$D/same.mem timeout 300 bin/${T}i_${PFX}I_${name}_gc $(cat $D/same.args) > $D/$name.prof 2>&1
        python3 kqsel.py $D/$name.prof fast/${PFX}I_$name.log $TH $MINN | head -1 > $D/$name.sel
        gen $name ${PFX}_$name "(PUse $(cat $D/$name.sel))"
      done < $D/same.tsv
    else
      while IFS=$'\t' read -r name kernel kind; do gen $name ${PFX}_$name ""; echo "-" > $D/$name.sel; done < $D/same.tsv
    fi
  fi
  SET=""; while IFS=$'\t' read -r name kernel kind; do SET="$SET ${PFX}_$name"; done < $D/same.tsv
  MODES=gc SET="$SET" bash mk.sh $T $XFLAGS | grep -i fail
fi
: > $D/times.txt
while IFS=$'\t' read -r name kernel kind; do b=bin/${T}_${PFX}_${name}_gc
  [ -x $b ] || { printf "%s\t%s\t%s\t-\t-\t-\t-\t-\n" "$name" "$kernel" "$kind" >> $D/times.txt; continue; }
  o=$(KQ_PERF=1 KQ_MEM=$D/same.mem timeout 300 taskset -c $KQCPU $b $(cat $D/same.args) 2>&1)
  res=$(echo "$o" | grep "^result" | awk '{print $2}')
  cnt=$(echo "$o" | grep "^perf" | awk '{ if ($5 + 0 > 0) printf "%.0f/%.1f", $5 / 1e6, $9 / 1e6; else printf "-" }'); [ -n "$cnt" ] || cnt="-"   # million instructions / million wrong guesses
  t=$(for i in $(seq $N); do KQ_MEM=$D/same.mem timeout 300 taskset -c $KQCPU $b $(cat $D/same.args) 2>&1 | head -1 | awk '{print $NF}'; done | sort -n | head -1)
  sum=$(python3 tests/cnorm.py bld/$T/${PFX}_${name}_gc.c ${PFX}_${name} 2>/dev/null | md5sum | cut -c1-12)
  sel=$(cat $D/$name.sel 2>/dev/null | tr -d ' '); [ -n "$sel" ] || sel="-"
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$kernel" "$kind" "$res" "$t" "$cnt" "$sum" "$sel" >> $D/times.txt
done < $D/same.tsv
# A way that seems slower than allowed is timed again, in turn with its loop's first way (a busy machine slows whatever
# program it happens to meet; what stays slower when the two are timed side by side is slower).  A way whose C is the
# very same as the first way's is the same machine code: it is not timed again, and a difference is not counted.
python3 - "$D/times.txt" "$TOL" "$N" "$KQCPU" "$T" "$PFX" "$D" <<'PYEOF'
import sys, subprocess
path, tol, n, cpu, tag, pfx, d = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5], sys.argv[6], sys.argv[7]
rows = [l.rstrip('\n').split('\t') for l in open(path) if l.strip()]
first = {}
for r in rows:
    if r[1] not in first: first[r[1]] = r
args = open(d + '/same.args').read().split()
def best(name, k):
    ts = []
    for _ in range(k):
        o = subprocess.run(['taskset', '-c', cpu, 'bin/%s_%s_%s_gc' % (tag, pfx, name)] + args, capture_output=True, text=True,
                           env={'KQ_MEM': d + '/same.mem', 'PATH': '/usr/bin:/bin'}, timeout=300)
        try: ts.append(float(o.stdout.splitlines()[0].split()[-1]))
        except Exception: pass
    return min(ts) if ts else None
for r in rows:
    f = first[r[1]]
    if r is f or r[2] != 'same' or r[4] == '-' or f[4] == '-' or r[6] == f[6]: continue
    if float(r[4]) <= tol * float(f[4]): continue
    a, b = [], []
    for _ in range(2 * n):
        x = best(f[0], 1); y = best(r[0], 1)
        if x: a.append(x)
        if y: b.append(y)
    if a and b:
        f[4] = '%.3f' % min(float(f[4]), min(a)); r[4] = '%.3f' % min(float(r[4]), min(b))
open(path, 'w').write(''.join('\t'.join(r) + '\n' for r in rows))
PYEOF
awk -F'\t' -v TOL=$TOL '
  { name[NR] = $1; ker[NR] = $2; kind[NR] = $3; res[NR] = $4; t[NR] = $5; cnt[NR] = $6; sum[NR] = $7; sel[NR] = $8
    if (!($2 in first)) { first[$2] = $5; fres[$2] = $4 } }
  END { printf "%-34s %-8s %9s %7s  %-4s %-9s %s\n", "the same loop, written this way", "must be", "ms", "x first", "C", "no jump", "M instructions / M wrong guesses (host only)"
        for (i = 1; i <= NR; i++) { k = ker[i]
          if (i == 1 || ker[i - 1] != k) { printf "--- %s\n", k; nl = 0; delete letter }
          r = (t[i] != "-" && first[k] > 0) ? t[i] / first[k] : 0
          if (!(sum[i] in letter)) letter[sum[i]] = sprintf("%c", 65 + nl++)
          note = ""
          if (t[i] == "-") { note = "  DID NOT BUILD"; bad++ }
          else if (res[i] != fres[k]) { note = "  A DIFFERENT ANSWER (" res[i] " against " fres[k] ")"; bad++ }
          else if (kind[i] == "same") { ns++
                 if (letter[sum[i]] == "A") { nsame++; if (r > TOL) note = "  (the very same C as the first way: the machine was busy)" }
                 else { if (r > TOL) { note = "  SLOWER THAN ITS KERNEL ALLOWS"; slow++ } if (r > worst) worst = r; if (r < bestr || bestr == 0) bestr = r } }
          sub(/^[a-z]+_/, "", name[i])
          printf "  %-32s %-8s %9s %7.2f  %-4s %-9s %s%s\n", name[i], kind[i], t[i], r, (t[i] == "-" ? "-" : letter[sum[i]]), sel[i], cnt[i], note }
        printf "\nways that must be the same: %d; %d of them are the very same C as their kernel%s first way; of the others the slowest is %.2f times it, the fastest %.2f (allowed: %.2f)\n", ns, nsame, "\047s", worst, bestr, TOL
        if (bad) print "GATE: A WAY OF WRITING A LOOP DID NOT BUILD OR GAVE A DIFFERENT ANSWER"
        else if (slow) print "GATE: " slow " WAY(S) OF WRITING THE SAME LOOP ARE SLOWER THAN ALLOWED"
        else print "GATE: every way of writing the same loop gives the same answer and the same speed" }' $D/times.txt
