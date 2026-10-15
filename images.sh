#!/bin/bash
# images.sh   (on the host: Docker and the network)   the two images every script here runs in, built as they were:
#   kernelq-certirocq:1b45a1aa      CertiRocq at commit 1b45a1aa (2026-05-07: the newest that builds unchanged against
#                                   MetaRocq 1.5.1) installed in mattam82/metacoq:metarocq-1.5.1-rocq-9.1 (Rocq 9.1.1,
#                                   MetaRocq 1.5.1, CompCert 3.17) by docker/build.sh -- about 20 minutes
#   kernelq-certirocq:1b45a1aa-kq2  the same with patch/kq_patch.py applied and CertiRocq rebuilt (patch/rebuild.sh) --
#                                   about 4 minutes
# Each step runs in a container capped at 6 GB of memory, which is then saved as the image.  Logs: images-log/.
set -e
cd "$(dirname "$0")"
L=$PWD/images-log; mkdir -p "$L"; chmod 777 "$L"
if ! docker image inspect kernelq-certirocq:1b45a1aa > /dev/null 2>&1; then
  docker rm -f kq-certirocq-build > /dev/null 2>&1 || true
  docker run --name kq-certirocq-build --memory=6g --memory-swap=8g -v "$L":/out -v "$PWD/docker/build.sh":/build.sh:ro \
    mattam82/metacoq:metarocq-1.5.1-rocq-9.1 bash -lc '/build.sh 1b45a1aa > /out/build.log 2>&1; echo "EXIT=$?" >> /out/build.log'
  grep -q "BUILD-DONE" "$L/build.log" || { echo "the CertiRocq build failed: $L/build.log"; exit 1; }
  docker commit -c 'CMD ["bash"]' kq-certirocq-build kernelq-certirocq:1b45a1aa > /dev/null
  docker rm kq-certirocq-build > /dev/null
  echo "built kernelq-certirocq:1b45a1aa"
fi
if ! docker image inspect kernelq-certirocq:1b45a1aa-kq2 > /dev/null 2>&1; then
  docker rm -f kq-certirocq-patch > /dev/null 2>&1 || true
  docker run --name kq-certirocq-patch --memory=6g --memory-swap=8g --network=none -v "$L":/out \
    -v "$PWD/patch/kq_patch.py":/kq_patch.py:ro -v "$PWD/patch/rebuild.sh":/rebuild.sh:ro \
    kernelq-certirocq:1b45a1aa bash -lc '/rebuild.sh > /out/rebuild.log 2>&1; echo "EXIT=$?" >> /out/rebuild.log'
  grep -q "REBUILD-DONE" "$L/rebuild.log" || { echo "the patched rebuild failed: $L/rebuild.log"; exit 1; }
  docker commit -c 'CMD ["bash"]' kq-certirocq-patch kernelq-certirocq:1b45a1aa-kq2 > /dev/null
  docker rm kq-certirocq-patch > /dev/null
  echo "built kernelq-certirocq:1b45a1aa-kq2"
fi
