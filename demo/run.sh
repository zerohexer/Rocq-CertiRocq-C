#!/bin/bash
# demo/run.sh   (inside the PATCHED image, in /w, after regen.sh)  THE TWO TASKS, three ways:
#   1  the Rocq text (demo/coop.body) through the pipeline: translator, checker, CertiRocq, clang -- and run on
#      2 million numbers; its output compared with
#   2  the C++ program that does the same (demo/coop.cpp);
#   3  the same Rocq text with the memory, input and output DEFINED in Rocq (demo/model_hdr.v), run by Rocq itself on
#      2000 numbers; its output compared with the native run's on those 2000.
cd /w; eval $(opam env); ulimit -s unlimited; mkdir -p dbg/demo; KQCPU=${KQCPU:-4}
python3 demo/mkin.py 2000000 dbg/demo/big.in; python3 demo/mkin.py 2000 dbg/demo/small.in
n=D_coop
{ cat hand/hdr.txt; echo; cat demo/coop.body; sed -e "s/%s/$n/" -e "s/%m/PPlain/" -e "s/%o/${KQORD:-3}/" -e "s/%b/$(bash bounds.sh $n)/" hand/ftr_kq.txt; } > fast/$n.v
timeout 300 rocq c -R . KQ fast/$n.v > fast/$n.log 2>&1 || { echo "ROCQ-FAIL"; grep -A8 "^Error" fast/$n.log | head -12; exit 1; }
grep "KQ-FAST\|^KQ-SHAPE" fast/$n.log | cut -c1-200
MODES=gc SET="$n" bash mk.sh demo | grep -i fail
sed 's/.*one-sided tests, /left in the C: /' bld/demo/${n}_gc.post | cut -c1-200
clang++ -O2 -std=c++17 -o dbg/demo/coop_cpp demo/coop.cpp
printf "4\n1024 z\n4 z\n4 z\n4 z\n" > dbg/demo/coop.mem           # four blocks of zeros: the ring, task A's cells, task B's, the shared ones
for i in 1 2 3 4 5; do KQ_MEM=dbg/demo/coop.mem KQ_IN=dbg/demo/big.in KQ_OUT=dbg/demo/rocq.out taskset -c $KQCPU bin/demo_${n}_gc 100000000 | head -1 | awk '{print $NF}'; done | sort -n | head -1 > dbg/demo/t_rocq
for i in 1 2 3 4 5; do { taskset -c $KQCPU dbg/demo/coop_cpp dbg/demo/big.in > dbg/demo/cpp.out; } 2>&1 | awk '{print $3}'; done | sort -n | head -1 > dbg/demo/t_cpp
echo "2 000 000 numbers through the two tasks:  Rocq $(cat dbg/demo/t_rocq) ms,  C++ $(cat dbg/demo/t_cpp) ms;  $(wc -l < dbg/demo/rocq.out) lines of output"
cmp -s dbg/demo/rocq.out dbg/demo/cpp.out && echo "GATE: the Rocq program's output is the C++ program's" || echo "GATE: THE OUTPUTS DIFFER"
# 3: the same text, run by Rocq
{ cat demo/model_hdr.v; echo "Definition kq_arg (i : Z) : Z := 1000000."
  echo "Definition kq_input (_ : Z) : mem := mkW [repeat 0 1024; repeat 0 4; repeat 0 4; repeat 0 4] [$(tr '\n' ';' < dbg/demo/small.in | sed 's/;$//')] []."
  cat demo/coop.body
  echo "Eval vm_compute in (rev (out (solve (kq_nat (kq_arg 0)) (kq_input 0))))."; } > dbg/demo/Model.v
timeout 300 rocq c dbg/demo/Model.v > dbg/demo/Model.log 2>&1 || { echo "the model does not compile"; grep -A8 "^Error" dbg/demo/Model.log | head -12; }
grep -A3 "^     = " dbg/demo/Model.log | tr -d '\n' | sed 's/.*= \[//; s/\].*//; s/; */\n/g' | tr -d ' ' | sed '/^$/d' > dbg/demo/model.out
KQ_MEM=dbg/demo/coop.mem KQ_IN=dbg/demo/small.in KQ_OUT=dbg/demo/rocq_small.out bin/demo_${n}_gc 100000000 > /dev/null
echo "2000 numbers: Rocq itself computes the output $(tr '\n' ' ' < dbg/demo/model.out); the compiled program wrote $(tr '\n' ' ' < dbg/demo/rocq_small.out)"
[ -s dbg/demo/model.out ] && [ "$(echo $(cat dbg/demo/model.out))" = "$(echo $(cat dbg/demo/rocq_small.out))" ] && echo "GATE: the compiled program's output is what Rocq computes from the same text" || echo "GATE: THE COMPILED PROGRAM AND ROCQ DISAGREE"
