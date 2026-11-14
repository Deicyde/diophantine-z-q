#!/bin/sh
# Assemble ModelGlue.lean: scratch/vert-witness/VertWitness.lean (verbatim, whole file) + ModelGlue.lean.part.
cd "$(dirname "$0")"
cat ../vert-witness/VertWitness.lean ModelGlue.lean.part > ModelGlue.lean
