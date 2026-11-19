#!/bin/bash
# Declaration indexes of the two repositories (and of nasqret's dependency) from their source at the pins.
# Usage: build.sh <fc> <fork> <nasqret> <ndep> <scratch dir> <data dir>
# decls-fork.json is over 50 MB: it stays in the scratch directory and data/decls-fork.json.sha256 records it.
# The dependency (elliotglazer/diophantine-z-q at 2358394, no licence) is indexed for lookups only.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
fc=$1 fork=$2 nas=$3 ndep=$4 s=$5 data=$6
py() { python3 -I "$@"; }
py "$here/decls.py" "$fc" "$fork" https://github.com/Deicyde/diophantine-z-q "$(git -C "$fork" rev-parse HEAD)" \
  "$s/decls-fork.raw.json" ZInQKernel,ZInQKernel.lean,lean,ThirdParty --vendored ThirdParty,Vendor --skip scratch,contrib-upstream
py "$here/decls.py" "$fc" "$nas" https://github.com/nasqret/z-in-q-lean "$(git -C "$nas" rev-parse HEAD)" \
  "$s/decls-nasqret.raw.json" .
py "$here/decls.py" "$fc" "$ndep" https://github.com/elliotglazer/diophantine-z-q "$(git -C "$ndep" rev-parse HEAD)" \
  "$s/decls-ndep.raw.json" . --vendored ThirdParty,Vendor --skip scratch,contrib-upstream
py "$here/standing.py" "$fc" "$s/decls-fork.raw.json" "$s/decls-fork.json" --root "$fork" \
  --headline ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness,ZInQ.OneProof.frozenTarget \
  --open "$fork/docs/one-proof/OPEN.md"
py "$here/standing.py" "$fc" "$s/decls-nasqret.raw.json" "$data/decls-nasqret.json" --root "$nas" \
  --headline ZOverQ.Bounded.bounded_from_height_tian_gross_zagier,ZOverQ.Qualitative.PicardConclusion.integer_polynomial_of_arithmetic_geometry \
  --dep "$s/decls-ndep.raw.json"
py "$here/mark_dependency.py" "$s/decls-ndep.raw.json" "$data/decls-nasqret.json" "$s/decls-ndep.json"
(cd "$s" && sha256sum decls-fork.json) > "$data/decls-fork.json.sha256"
(cd "$s" && sha256sum decls-ndep.json) > "$data/decls-ndep.json.sha256"
