#!/bin/bash
# Seeds: candidate declarations per item and repository (hints for the mapping session).
# Usage: build.sh <fork> <nasqret> <seed items.json (71 statements)> <items-text.json> <scratch dir>
set -eu
here=$(cd "$(dirname "$0")" && pwd)
data=$here/../../data
python3 -I "$here/harvest.py" "$1" "$3" "$5/harvest-fork.json"
python3 -I "$here/build_seeds.py" "$data/items.json" "$4" "$5/harvest-fork.json" "$5/decls-fork.json" \
  "$data/decls-nasqret.json" "$5/decls-ndep.json" "$2" "$data/seeds.json"
