#!/bin/bash
# Regenerate one H module from its committed pre-dedupe state: redo.sh MODULE BASEREV DELETED_MODULES...
set -e
cd "$(dirname "$0")/../.."
M=$1; REV=$2; shift 2
git show $REV:ZInQKernel/OneProof/H/$M.lean > ZInQKernel/OneProof/H/$M.lean
python3 scratch/one-proof/del_decls.py . $M.lean | grep -E 'deleting|skip'
python3 scratch/one-proof/add_opens.py . $M.lean "$@"
[ -f scratch/one-proof/fixes/$M.py ] && python3 scratch/one-proof/fixes/$M.py
true
