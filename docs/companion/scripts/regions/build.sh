#!/bin/bash
# Regions of every item of repo/data/items.json on the committed PDF.
# Usage: build.sh <diophantine_zq.tex> <diophantine_zq.pdf> <workdir>
set -eu
here=$(cd "$(dirname "$0")" && pwd)
data=$here/../../data
mkdir -p "$3"
python3 -I "$here/regions.py" "$1" "$2" "$data/items.json" "$3" "$data/regions.json" "$3/regions-report.json"
