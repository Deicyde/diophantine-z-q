#!/bin/bash
# assemble W.lean from parts
cd "$(dirname "$0")"
{ echo "import ZInQKernel.Contrib.OneProof.ShimuraMainCM"; sed -n '2,$p' A_Charts.lean | sed '$d'; for f in "$@"; do cat $f; done; } > W.lean
