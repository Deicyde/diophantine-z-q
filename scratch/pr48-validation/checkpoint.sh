#!/usr/bin/env bash
# Checkpoint only the newly imported FLT proof artifacts for this candidate.
set -euo pipefail

mode=${1:?give pack or restore}
folder=${2:?give a checkpoint directory}
baseline=da47dac4524b4ed001cf2468d7da44228f7991a0
source_sha=$(git rev-parse HEAD)

if [[ $mode == restore ]]; then
  test "$(cat "$folder/source.txt")" = "$source_sha"
  (cd "$folder" && sha256sum --strict -c SHA256SUMS)
  zstd -dc -- "$folder/flt.tar.zst" | tar --extract --no-same-owner --no-same-permissions -f -
  exit
fi
test "$mode" = pack

mkdir -p "$folder"
list="$folder/modules.nul"
git diff --name-only --diff-filter=A -z "$baseline" HEAD -- ZInQKernel/Contrib/ |
while IFS= read -r -d '' path; do
  [[ $path == *.lean ]] || continue
  for base in .lake/build/lib/lean .lake/build/ir; do
    stem="$base/${path%.lean}"
    for artifact in "$stem".*; do
      if [[ -f $artifact && ! -L $artifact && $artifact != *.setup.json ]]; then
        printf '%s\0' "$artifact"
      fi
    done
  done
done > "$list"
if [[ ! -s $list ]]; then
  echo "No new FLT artifacts to keep."
  exit
fi

tar --create --null -T "$list" -f - |
  zstd -T2 -3 -o "$folder/flt.tar.zst"
printf '%s\n' "$source_sha" > "$folder/source.txt"
(cd "$folder" && sha256sum flt.tar.zst > SHA256SUMS)
du -h "$folder/flt.tar.zst"
