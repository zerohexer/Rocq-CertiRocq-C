#!/bin/bash
# inside kernelq-certirocq:1b45a1aa : patch the build tree opam left behind, rebuild what depends on it, install
set -ex
ulimit -s unlimited
eval $(opam env) || true
B=$(ls -d ~/.opam/*/.opam-switch/build/rocq-certirocq.dev+9.0); cd $B
python3 /kq_patch.py $B
date; make -j2 all
date; make plugin
date; make -C theories install > /out/install_theories.log 2>&1; make -C plugins/plugin install > /out/install_plugin.log 2>&1
date; echo REBUILD-DONE
