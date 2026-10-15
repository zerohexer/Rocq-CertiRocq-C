#!/bin/bash
# table.sh [TAG] [answers]   (inside the image, in /w)  THE TABLE: every problem of problems.tsv --
#   the C++ reference (and its variants, where there are any), the corpus program with its text exactly as it is and
#   with rebuilt pairs removed, and every program of hand.tsv for that problem; built under TAG (default fin).
# One line per run: best and median of N (one pinned fast core), and whether every answer equals the C++ run's.
# Then a summary: per problem the C++ time, the unchanged program's, the best rewritten one's, and the two ratios.
#   answers: no timing, only the comparison of the answers (for the stress build).
#   HP=P: the programs of hand.tsv as built in set P of regen.sh (the bounds proofs for every program) instead of H.
cd /w && ulimit -s unlimited
T=${1:-fin}; MODE=${2:-times}; N=${N:-5}; out=dbg/table_$T${HP:+_$HP}.txt
# the width of the first column: the longest label there is (the first line of the file says which width was used)
LW=$(grep -v '^#' hand.tsv | awk 'NF { d = $0; sub(/^[^ ]+ +[^ ]+ +[^ ]+ +/, "", d); if (length(d) > m) m = length(d) } END { print (m + 18 > 38 ? m + 18 : 38) + 2 }')
export LW; echo "#LW $LW" > $out
while read -r p d prog; do
  [ -n "$p" ] || continue
  [ -z "$ONLY" ] || case " $ONLY " in *" $p "*) ;; *) continue;; esac       # ONLY="CF61E CF7D": those problems only
  E=()
  if [ "$MODE" = times ]; then
    E+=("C++=cpp:$p")
    [ -f cpp64/${p}_64.cpp ] && E+=("C++ with 64-bit cells=cpp64:$p")
    [ -f cppw/${p}_w.cpp ] && E+=("C++ written the way the fast Rocq is=cppw:$p")
  fi
  [ "$prog" = "-" ] || E+=("corpus text, exactly=bin/${T}_F_${prog}_gc:$p" "corpus text, pairs not rebuilt=bin/${T}_E_${prog}_gc:$p")
  while read -r name prob mem what; do
    [ "$prob" = "$p" ] || continue
    m=""; [ "$mem" = "-" ] || m=":$mem"
    E+=("by the guideline, $what=bin/${T}_${HP:-H}_C_${name}_gc:$p$m")
  done < <(grep -v '^#' hand.tsv)
  if [ "$MODE" = answers ]; then ANSWERS=1 N=1 bash bench.sh "${E[@]}" | tail -n +2 | tee -a $out
  else N=$N bash bench.sh "${E[@]}" | tail -n +2 | tee -a $out; fi
done < <(grep -v '^#' problems.tsv)
if [ "$MODE" = answers ]; then echo "answers: $(grep -v '^#' $out | grep -c ' ok$') agree, $(grep -v '^#' $out | grep -vc ' ok$') do not"; exit 0; fi
echo
printf "%-8s %8s %8s %8s %9s %9s %7s %7s   %s\n" problem "C++" "C++/64" "C++/same" "unchanged" "guideline" "unch/C" "guid/C" "(ms, best of $N)"
awk -v LW=$LW '
  /^#/ { next }
  { label = substr($0, 1, LW); rest = substr($0, LW + 2); split(rest, f, " "); p = f[1]; t = f[2]; ok = f[4]
    if (!(p in seen)) { seen[p] = 1; order[++n] = p }
    if (ok != "ok") bad[p] = 1
    gsub(/ +$/, "", label)
    if (label == "C++") cpp[p] = t
    else if (label == "C++ with 64-bit cells") c64[p] = t
    else if (label == "C++ written the way the fast Rocq is") cw[p] = t
    else if (label ~ /^corpus text, pairs not rebuilt/) unch[p] = t
    else if (label ~ /^by the guideline/) { if (!(p in best) || t + 0 < best[p] + 0) best[p] = t } }
  function r(a, b) { return (a != "-" && b + 0 > 0) ? sprintf("%.2f", a / b) : "-" }
  END { for (i = 1; i <= n; i++) { p = order[i]
          u = (p in unch) ? unch[p] : "-"; b = (p in best) ? best[p] : "-"
          printf "%-8s %8s %8s %8s %9s %9s %7s %7s   %s\n", p, cpp[p], (p in c64) ? c64[p] : "-", (p in cw) ? cw[p] : "-", u, b, r(u, cpp[p]), r(b, cpp[p]), (p in bad) ? "AN ANSWER DIFFERS" : ""
          if (u != "-") { nu++; su[nu] = u / cpp[p] }
          x = (b != "-") ? b : u; if (x != "-") { nb++; sb[nb] = x / cpp[p] } }
        printf "\nC++/64: the C++ with every array 64 bits wide (the layout a Rocq program is given).  C++/same: the C++ written the way the fast Rocq version is.\n"
        printf "guideline: the fastest program written by the guideline; where there is none, the corpus text already follows it.\n" }' $out
