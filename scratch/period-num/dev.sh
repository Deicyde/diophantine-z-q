#!/bin/bash
# Check a development file that imports PNBase (olean in scratch/period-num/olean). Run from the repo root.
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
LP=$(lake env printenv LEAN_PATH)
LEAN_PATH="$LP:scratch/period-num/olean" lean "$@"
