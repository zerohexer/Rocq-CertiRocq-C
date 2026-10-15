#!/bin/bash
# bounds.sh NAME   what a read or a write of a block does about its bounds in program NAME (KQFast.v, `kq_bounds`):
#   KQBOUNDS=tests|proofs   for every program of this run;  else
#   hand/NAME.bounds        one word, tests or proofs, for that program;  else
#   tests                   THE DEFAULT: every read and write tests its cell, as the model defines `rd` and `upd`.
# proofs = step 3 of the translator: a loop that counts reads and writes with no test, after one test at its start,
# and the translator proves that none leaves its block.
# Prints KQTests or KQProofs.  Anything else stops the build: what it prints then is a name Rocq does not know.
f=hand/$1.bounds; b=${KQBOUNDS:-$([ -f $f ] && tr -d ' \t\n' < $f)}
case ${b:-tests} in
  tests) echo KQTests;;
  proofs) echo KQProofs;;
  *) echo "bounds.sh: '$b' (KQBOUNDS, or hand/$1.bounds) is neither tests nor proofs" >&2; echo KQ_BOUNDS_ARE_TESTS_OR_PROOFS;;
esac
