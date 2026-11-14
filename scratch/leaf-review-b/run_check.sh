#!/bin/bash
# leaf-review-b: compile Leaves3.lean with PrintFields.lean.tail appended (one Lean process).
set -e
cd "$(dirname "$0")/../.."
cat scratch/leaf-fold3/Leaves3.lean scratch/leaf-review-b/PrintFields.lean.tail > /tmp/lrb_check.lean
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
rc=0; lake env lean /tmp/lrb_check.lean > /tmp/lrb_check.out 2>&1 || rc=$?; echo "exit $rc" >> /tmp/lrb_check.out
