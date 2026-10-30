#!/bin/sh
# rocq-fork/rebuild.sh   (inside kernelq-certirocq:1b45a1aa-kq2, as its opam user, with the network; run by images.sh)
# Rocq 9.1.1 with the conversion memo (rocq-fork/conv-memo-v9.1.1.patch, Rocq-C-solution.md D28) under every package of the
# image: opam pins rocq-runtime / rocq-core / coqide-server to the patched source and recompiles every package that depends
# on them; then the kq2 layer's CertiRocq patch is applied again (as patch/rebuild.sh does).  Disk-safe (F47): no build
# folder is kept but CertiRocq's, which the kq2 patch rebuilds in; the patched source stays in ~/rocq-9.1.1-fork (the pins
# point there).  About 70 minutes; the container grows about 4 GB.
set -ex
ulimit -s unlimited; ulimit -c 0
eval $(opam env) || true
SRC=$HOME/rocq-9.1.1-fork
mkdir -p $SRC && cd $SRC
curl -sL -o /tmp/V9.1.1.tar.gz https://codeload.github.com/rocq-prover/rocq/tar.gz/refs/tags/V9.1.1
echo "35cd03fc4193969b1cce01190340e5c129c1ba8f02242a9e6dff4b83be118759  /tmp/V9.1.1.tar.gz" | sha256sum -c -
tar xzf /tmp/V9.1.1.tar.gz --strip-components=1 && rm /tmp/V9.1.1.tar.gz
git apply -p1 /rocq-fork/conv-memo-v9.1.1.patch
python3 /rocq-fork/check_patch.py $SRC
opam pin add -y -n -k path rocq-runtime.9.1.1 $SRC
opam pin add -y -n -k path rocq-core.9.1.1 $SRC
opam pin add -y -n -k path coqide-server.9.1.1 $SRC
date; opam reinstall -y -j 3 rocq-runtime rocq-core coqide-server
date; opam reinstall -y -j 3 --keep-build-dir rocq-certirocq
B=$(ls -d ~/.opam/*/.opam-switch/build/rocq-certirocq.dev+9.0); cd $B
python3 /kq_patch.py $B
date; make -j2 all
make plugin
make -C theories install > /out/fork_install_theories.log 2>&1; make -C plugins/plugin install > /out/fork_install_plugin.log 2>&1
rm -rf ~/.opam/download-cache/* /tmp/opam-* 2>/dev/null || true
date; echo FORK-REBUILD-DONE
