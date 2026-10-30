#!/bin/bash
# images.sh   (on the host: Docker and the network)   the images every script here runs in, built as they were:
#   kernelq-certirocq:1b45a1aa      CertiRocq at commit 1b45a1aa (2026-05-07: the newest that builds unchanged against
#                                   MetaRocq 1.5.1) installed in mattam82/metacoq:metarocq-1.5.1-rocq-9.1 (Rocq 9.1.1,
#                                   MetaRocq 1.5.1, CompCert 3.17) by docker/build.sh -- about 20 minutes
#   kernelq-certirocq:1b45a1aa-kq2  the same with patch/kq_patch.py applied and CertiRocq rebuilt (patch/rebuild.sh) --
#                                   about 4 minutes
#   kernelq-certirocq:1b45a1aa-kq2-fork  the same on our fork of Rocq: 9.1.1 with the kernel's conversion memo
#                                   (rocq-fork/, Rocq-C-solution.md D28), every package recompiled on it
#                                   (rocq-fork/rebuild.sh) -- about 70 minutes, 8 GB of memory, the network
# Each step runs in a container capped in memory, which is then saved as the image.  Logs: images-log/.
# KQ_BASE_IMAGE, KQ_IMAGE and KQ_FORK_IMAGE give the images other names.
set -e
cd "$(dirname "$0")"
BASE=${KQ_BASE_IMAGE:-kernelq-certirocq:1b45a1aa}; IMAGE=${KQ_IMAGE:-kernelq-certirocq:1b45a1aa-kq2}
FORK=${KQ_FORK_IMAGE:-kernelq-certirocq:1b45a1aa-kq2-fork}
L=$PWD/images-log; mkdir -p "$L"; chmod 777 "$L"
if ! docker image inspect "$BASE" > /dev/null 2>&1; then
  docker rm -f kq-certirocq-build > /dev/null 2>&1 || true
  docker run --name kq-certirocq-build --memory=6g --memory-swap=8g -v "$L":/out -v "$PWD/docker/build.sh":/build.sh:ro \
    mattam82/metacoq:metarocq-1.5.1-rocq-9.1 bash -lc '/build.sh 1b45a1aa > /out/build.log 2>&1; echo "EXIT=$?" >> /out/build.log'
  grep -q "BUILD-DONE" "$L/build.log" || { echo "the CertiRocq build failed: $L/build.log"; exit 1; }
  docker commit -c 'CMD ["bash"]' kq-certirocq-build "$BASE" > /dev/null
  docker rm kq-certirocq-build > /dev/null
  echo "built $BASE"
fi
if ! docker image inspect "$IMAGE" > /dev/null 2>&1; then
  docker rm -f kq-certirocq-patch > /dev/null 2>&1 || true
  docker run --name kq-certirocq-patch --memory=6g --memory-swap=8g --network=none -v "$L":/out \
    -v "$PWD/patch/kq_patch.py":/kq_patch.py:ro -v "$PWD/patch/rebuild.sh":/rebuild.sh:ro \
    "$BASE" bash -lc '/rebuild.sh > /out/rebuild.log 2>&1; echo "EXIT=$?" >> /out/rebuild.log'
  grep -q "REBUILD-DONE" "$L/rebuild.log" || { echo "the patched rebuild failed: $L/rebuild.log"; exit 1; }
  docker commit -c 'CMD ["bash"]' kq-certirocq-patch "$IMAGE" > /dev/null
  docker rm kq-certirocq-patch > /dev/null
  echo "built $IMAGE"
fi
if ! docker image inspect "$FORK" > /dev/null 2>&1; then
  docker rm -f kq-certirocq-fork > /dev/null 2>&1 || true
  docker run --name kq-certirocq-fork --memory=8g --memory-swap=8g --ulimit core=0 -v "$L":/out \
    -v "$PWD/rocq-fork":/rocq-fork:ro -v "$PWD/patch/kq_patch.py":/kq_patch.py:ro \
    "$IMAGE" bash -lc '/rocq-fork/rebuild.sh > /out/fork_rebuild.log 2>&1; echo "EXIT=$?" >> /out/fork_rebuild.log'
  grep -q "FORK-REBUILD-DONE" "$L/fork_rebuild.log" || { echo "the fork rebuild failed: $L/fork_rebuild.log"; exit 1; }
  docker commit -c 'CMD ["bash"]' kq-certirocq-fork "$FORK" > /dev/null
  docker rm kq-certirocq-fork > /dev/null
  echo "built $FORK"
fi
