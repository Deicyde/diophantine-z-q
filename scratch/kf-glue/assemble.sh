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
echo "/-! # Part MR. scratch/mul-rigidity/MulRigidity.lean lines 3-182 and 205-604 (verbatim)."
echo "The copy of \`RigidityHom\` there (lines 189-196) is identical to the one above (New.lean). -/"
echo "section PartMulRigidity"
sed -n 3,182p scratch/mul-rigidity/MulRigidity.lean
echo "/-! MulRigidity.lean lines 205-604 (verbatim; Mul.lean body: \`MulIsogeny\` and its reductions).
Lines 184-203 (\`RigidityHom\` again and \`rigidityHom\`) are omitted: \`RigidityHom\` is above and
\`rigidityHom\` is restated in New.lean. -/"
sed -n 205,604p scratch/mul-rigidity/MulRigidity.lean | grep -v "^#print axioms"
echo "end -- closes the noncomputable section opened at line 222 of the copy"
echo "end -- closes the noncomputable section opened at line 15 of the copy"
echo "end PartMulRigidity"
echo
echo "/-! # Part PTS. scratch/kf-glue/Points.lean (new; the two point lemmas from Mathlib) -/"
echo "section PartPoints"
grep -v "^import " scratch/kf-glue/Points.lean
echo "end -- closes Points.lean's noncomputable section"
echo "end PartPoints"
echo
cat scratch/kf-glue/New.lean
} > $O
wc -l $O
