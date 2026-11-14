#!/bin/bash
# parts/b05_conjtwist.lean: scratch/conj-twist/ConjTwist.lean lines 1624-2004 (§13-§16, conjTwistNontrivial_of_leaves),
# verbatim, with the file's `open`s (lines 41-43, 718). Part a30 holds its lines 84-191, 206-1612 (g0-assemble2).
cd "$(dirname "$0")"
S=1624; E=$(grep -n "^end G0Galois" ../conj-twist/ConjTwist.lean | head -1 | cut -d: -f1)
{ echo "/-! ## leaf-fold2: conj-twist's later sections (scratch/conj-twist/ConjTwist.lean lines $S-$((E-1)), verbatim; commits"; echo "3ecdd95e, 94802c43): §13 N1-surj from T5, §14-§16 N3a and \`TwistCEval\` proved, and"; echo "\`conjTwistNontrivial_of_leaves : T5 → T26 → T35 → HomLinearLift → ConjTwistNontrivial\`. Part a30 holds"; echo "lines 84-191, 206-1612 (g0-assemble2). The \`open\`s are the file's lines 41-43 and 718. -/"; echo "noncomputable section"; echo; echo "namespace G0Galois"; echo; sed -n 41,43p ../conj-twist/ConjTwist.lean; sed -n 718p ../conj-twist/ConjTwist.lean; echo; sed -n "${S},$((E-1))p" ../conj-twist/ConjTwist.lean; echo "end G0Galois"; echo; echo "end"; } > parts/b05_conjtwist.lean
