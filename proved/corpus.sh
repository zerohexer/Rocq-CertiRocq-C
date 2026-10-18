#!/bin/bash
# corpus.sh [times]   (inside the image, in /w)   every program of hand.tsv through the proved route:
#   the proofs checked (proved/make.sh), each program translated and proved (kitc.py), built, and its answer
#   compared with the C++ run's (bench.sh); with "times", also timed next to the kit's own build of the same program
#   (bin/fin_H_C_NAME_gc, from all.sh or regen.sh).
#   SKIP="NAME .."  programs left out;  ONLY="NAME .."  only these.
#   A function whose lemma the kernel does not finish in KQ_TIMEOUT (300 s) is left unproved: the program is still built
#   and its answer checked against the C++ run, and the last line counts it apart.
# The last line says how many agree.
cd /w && ulimit -s unlimited; eval $(opam env)
mkdir -p dbg
bash proved/make.sh | tail -1
SKIP=${SKIP-}
names=$(grep -v '^#' hand.tsv | awk 'NF { print $1 }' | grep -vxF -f <(printf '%s\n' $SKIP x))
[ -z "$ONLY" ] || names=$(printf '%s\n' $names | grep -xF -f <(printf '%s\n' $ONLY))
python3 proved/kitc.py $names 2>&1 | tee dbg/proved_kitc.txt | grep -v "built bin"
out=dbg/proved_table.txt; : > $out
agree=0; differ=0; none=0
while read -r name prob mem what; do
  [ -n "$name" ] || continue
  [ -z "$ONLY" ] || case " $ONLY " in *" $name "*) ;; *) continue;; esac
  if [ ! -x bin/P_$name ]; then none=$((none + 1)); continue; fi
  m=""; [ "$mem" = "-" ] || m=":$mem"
  E=("proved=bin/P_$name:$prob$m")
  if [ "$1" = times ]; then
    [ -x bin/fin_H_C_${name}_gc ] && E=("kit=bin/fin_H_C_${name}_gc:$prob$m" "${E[@]}")
    r=$(N=${N:-5} bash bench.sh "${E[@]}" | tail -n +2)
  else
    r=$(ANSWERS=1 N=1 bash bench.sh "${E[@]}" | tail -n +2)
  fi
  echo "$name: $r" | tee -a $out
  echo "$r" | grep -q " ok$" && agree=$((agree + 1)) || differ=$((differ + 1))
done < <(grep -v '^#' hand.tsv)
unp=$(grep -c " UNPROVED " dbg/proved_kitc.txt)
echo "proved route: $agree programs built and equal to the C++ run's answer ($unp of them with a function left unproved); $differ do not agree; $none not translated"
