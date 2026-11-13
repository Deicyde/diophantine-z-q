#!/bin/bash
# Assembles KfGlue.lean from verbatim copies (scratch files cannot import each other).
set -e
cd "$(dirname "$0")/../.."
O=scratch/kf-glue/KfGlue.lean
{
# Porting fix (proof term only): R1fpProps has 6 clauses on this base (pin-apply), so its
# naturality clause is hR1.2.2.2.1 (kernel-field's base had 4 clauses).
grep -v '^#print' scratch/kernel-field/KernelField.lean | sed 's/obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2 K Qbar/obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2.1 K Qbar/'
echo
echo "/-! # Part MR. scratch/mul-rigidity/MulRigidity.lean lines 3-182 (verbatim; namespace MulRigidity)."
echo "The copy of \`RigidityHom\` there (lines 189-196) is identical to the one above (New.lean). -/"
echo "section PartMulRigidity"
sed -n 3,182p scratch/mul-rigidity/MulRigidity.lean
echo "end -- closes the noncomputable section opened at line 15 of the copy"
echo "end PartMulRigidity"
echo
cat scratch/kf-glue/New.lean
} > $O
wc -l $O
