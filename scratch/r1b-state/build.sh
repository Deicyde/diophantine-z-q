#!/bin/bash
# Assemble R1b.lean = PkgI1Copy.part (pkg-I1 definitions copied from h-decomposition/Leaves.lean)
# + R1b.part (the leaf and its glue) + further parts.
cd "$(dirname "$0")"
cat PkgI1Copy.part R1b.part $(ls Part*.part 2>/dev/null | LC_ALL=C sort) > R1b.lean
