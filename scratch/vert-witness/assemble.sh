#!/bin/sh
# Assemble VertWitness.lean: NoVert.lean (hecke-rest) without its trailing #print lines + VertMain.
cd "$(dirname "$0")"
N=$(grep -n '^#print' ../hecke-rest/NoVert.lean | head -1 | cut -d: -f1)
head -n $((N-1)) ../hecke-rest/NoVert.lean > VertWitness.lean
cat VertMain.lean.part >> VertWitness.lean
