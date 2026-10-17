#!/bin/bash
# all.sh   (inside the PATCHED image, in /w)  the whole experiment from nothing, and the gate for any later change:
#   1  Rocq -> C for every program: the corpus text exactly (F), the corpus text with rebuilt pairs removed (E), and
#      the programs written by the guideline (H) -- those THROUGH THE TRANSLATOR (KQFast.v): each put in the standard
#      form, the kernel checking that the standard form is equal to the program; then the checker (a refused program
#      does not compile); the checker also on small programs with a known verdict;  and the programs written by the
#      guideline once more with the bounds PROOFS (P: step 3 of the translator, a setting that is off by default),
#      so that setting is checked too -- every proof, and every answer;
#   2  the choices between two numbers MEASURED again (prof.sh) and compared with the stored ones (hand/*.sel);
#   3  clean-up, build;  every corpus program compared with the ORIGINAL on a random input, with the normal collector
#      and with one that collects every few values built (and the control: with every save removed it must go wrong);
#   4  the machine-integer operations against a plain reference;  Rocq's division against Z's;
#   5  what is left in the generated C of each program (values built in loops, closures);
#   6  THE SAME LOOP WRITTEN MANY WAYS (tests/same.sh): same answers, same speed, and how many come out as the same C;
#   7  the two tasks with input and output (demo/run.sh): same output as the C++, and as Rocq's own run of the text;
#   8  THE TABLE: every timed problem against its C++ reference, every answer compared;
#   9  the same answers once more with the stress collector;
#  10  the proved route (proved/): every proof, every program of hand.tsv through it, every answer, timed.
# A line that starts with GATE says whether one of these went wrong.
cd /w && bash setup.sh || exit 1
eval $(opam env)
bash regen.sh F E H P > dbg/regen.txt 2>&1; tail -4 dbg/regen.txt
k=$(grep -l "KQ-FAST" fast/H_C_*.log | wc -l); kept=$(grep -h "KQ-FAST" fast/H_C_*.log | grep -vc " 0 kept as written")
hf=$(grep "^set H:" dbg/regen.txt | grep -o "[0-9]* failed" | awk '{print $1}')
two=$(grep -h "KQ-FAST" fast/H_C_*.log | grep -o "[0-9]* step(s) of the second kind" | awk '{s += $1} END {print s + 0}')
three=$(grep -h "KQ-FAST" fast/H_C_*.log | grep -o "[0-9]* loop(s) without tests" | awk '{s += $1} END {print s + 0}')
echo "translator: $k programs written by the guideline put in the standard form, each equal to its program (the kernel checks every proof: by computation, and by induction for the $two step(s) of the second kind); $kept of them have a function kept as written; $(grep -h "KQ-FAST" fast/H_C_*.log | grep -c "bounds: proofs") of them built with the bounds proofs (the setting; $three loop(s) without tests)"
[ "$k" = "$(ls hand/*.body | wc -l)" ] && [ "$kept" = 0 ] && [ "$hf" = 0 ] && echo "GATE: every program written by the guideline is in the standard form, and equal to it" || echo "GATE: THE TRANSLATOR LEFT SOMETHING AS WRITTEN OR A PROGRAM DID NOT COMPILE"
pk=$(grep -l "KQ-FAST" fast/P_C_*.log | wc -l); pf=$(grep "^set P:" dbg/regen.txt | grep -o "[0-9]* failed" | awk '{print $1}')
pthree=$(grep -h "KQ-FAST" fast/P_C_*.log | grep -o "[0-9]* loop(s) without tests" | awk '{s += $1} END {print s + 0}')
echo "bounds proofs (set P, every program with the setting KQProofs): $pk programs compiled, $pf failed; $pthree loop(s) read and write without tests, each proved by the copy of the loop that carries the proofs (checked by the kernel)"
[ "$pk" = "$k" ] && [ "$pf" = 0 ] && echo "GATE: every program written by the guideline also compiles with the bounds proofs" || echo "GATE: A PROGRAM DOES NOT COMPILE WITH THE BOUNDS PROOFS"
bash shape.sh > dbg/shape.txt
awk '/^[FE]_/ { if ($2 == "OK" || $2 == "OK,") ca++; else cr++ } /^H_/ { if ($2 == "OK" || $2 == "OK,") ha++; else { hr++; bad = bad " " $1 } }
     END { printf "checker: corpus texts %d accepted, %d refused;  written by the guideline %d accepted, %d refused\n", ca, cr, ha, hr
           print (hr ? "GATE: THE CHECKER REFUSES" bad : "GATE: the checker accepts every program written by the guideline") }' dbg/shape.txt
bash tests/shape.sh
QUIET=1 CHECK=1 bash prof.sh | grep "one sequence\|^choices\|^GATE"
d=$(rocq c -R . KQ tests/TestDiv.v 2>&1 | grep "^     = " | tr -d ' ')
echo "Rocq's division and remainder against Z's (pairs tried, pairs wrong): $d"
case "$d" in *',[])') echo "GATE: division agrees";; *) echo "GATE: DIVISION DIFFERS";; esac
r=$(bash compile.sh examples/neg.body 2>&1 | grep "^main = ")
[ "$r" = "main = 10000" ] && echo "GATE: a negative block or cell number is outside the memory (a read gives 0, a write does nothing)" || echo "GATE: A NEGATIVE NUMBER REACHES A CELL (got: $r)"
ALL=""; for r in case/*.ref; do b=$(basename $r .ref); ALL="$ALL F_$b E_$b"; done
H=""; for b in hand/*.body; do H="$H H_C_$(basename $b .body) P_C_$(basename $b .body)"; done
SET="$ALL $H" bash mk.sh fin | tail -3;                c1=$(bash check.sh fin F gc);  c2=$(bash check.sh fin E gc);  echo "$c1"; echo "$c2"
SET="$ALL $H" SUP=sup/stress bash mk.sh sfin | tail -3; c3=$(bash check.sh sfin F gc); c4=$(bash check.sh sfin E gc); echo "$c3"; echo "$c4"
echo "$c1 $c2 $c3 $c4" | grep -q "[1-9][0-9]* different" && echo "GATE: A PROGRAM DIFFERS FROM THE ORIGINAL" || echo "GATE: every corpus program agrees with the original, with both collectors"
bash tests/control.sh
RT=$(ls -d ~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime)
for o in -O0 -O2; do clang -w $o -Isup/v4 -I$RT -o dbg/test_arith tests/test_arith.c && ./dbg/test_arith | tail -3; done
echo "--- what is left in the generated C (a program with nothing here never touches the collector in a loop)"
flat=""; notflat=""
for f in bld/fin/*_gc.post; do n=$(basename $f _gc.post)
  v=$(grep -o "[0-9]* of them inside a loop" $f | awk '{print $1}'); c=$(grep -o "[0-9]* closures built" $f | awk '{print $1}'); k=$(grep -o "[0-9]* calls through a closure" $f | awk '{print $1}')
  if [ "$v" = 0 ] && [ "$c" = 0 ] && [ "$k" = 0 ]; then flat="$flat $n"
  else printf "  %-16s %s values built inside loops, %s closures built, %s calls through a closure\n" $n "$v" "$c" "$k"; notflat="$notflat $n"; fi
done
echo "  nothing left (FLAT):$flat" | fold -s -w 118
hb=""; for n in $notflat; do case $n in H_*) hb="$hb $n";; esac; done
[ -z "$hb" ] && echo "GATE: every program written by the guideline is flat" || echo "GATE: NOT FLAT:$hb"
grep -l "NOT FLAT: closures" bld/fin/*_gc.post > /dev/null 2>&1 && echo "GATE: A CLOSURE IS LEFT IN $(grep -l 'NOT FLAT: closures' bld/fin/*_gc.post | tr '\n' ' ')" || echo "GATE: no closure is left in any program"
echo "--- the same loop written many ways"
N=${N:-5} bash tests/same.sh same | tee dbg/same.txt | tail -3
echo "--- two tasks, input and output"
bash demo/run.sh
echo "--- the table"
N=${N:-5} bash table.sh fin
grep -q "DIFFERS\|WRONG\|missing" dbg/table_fin.txt && echo "GATE: AN ANSWER DIFFERS FROM THE C++ RUN" || echo "GATE: every answer equals the C++ run's"
echo "--- the programs written by the guideline with the bounds proofs (set P): answers only"
pa=$(HP=P bash table.sh fin answers | tail -1); echo "$pa"
echo "$pa" | grep -q " 0 do not" && echo "GATE: with the bounds proofs every answer equals the C++ run's" || echo "GATE: WITH THE BOUNDS PROOFS AN ANSWER DIFFERS"
echo "--- the proved route (proved/): every proof, every program of hand.tsv through it, every answer, timed next to the kit's build"
pr=$(N=${N:-5} bash proved/corpus.sh times | tee dbg/proved_run.txt | tail -1); echo "$pr"
grep -q "^core-ok" dbg/proved_run.txt && echo "GATE: every proof of the proved route is accepted by the kernel" || echo "GATE: A PROOF OF THE PROVED ROUTE FAILS"
echo "$pr" | grep -q " 0 do not agree" && echo "GATE: every program through the proved route gives the C++ run's answer" || echo "GATE: A PROGRAM THROUGH THE PROVED ROUTE DIFFERS"
mkdir -p results; cp dbg/table_fin.txt results/table.txt; python3 mktable.py results/table.txt > results/table.md       # the table, as lines and as Markdown
cp dbg/same.txt results/same.txt 2>/dev/null
echo "--- the stress collector on the large inputs (answers only)"
bash table.sh sfin answers | tail -1
echo "  and with the bounds proofs (set P): $(HP=P bash table.sh sfin answers | tail -1)"
