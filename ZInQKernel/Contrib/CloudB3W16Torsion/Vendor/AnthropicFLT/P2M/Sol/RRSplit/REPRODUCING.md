# Generic local reproduction instructions

These commands are **examples for a local working copy**, not the original
verification command transcript. They have not been rerun for the documentation-
only public-evidence update. Keep the repository's Lean 4.35.0 and Mathlib pins
unchanged, install the matching dependency cache, and use the complete reviewed
source tree including the canonical prerequisite modules. Do not replace a
missing prerequisite with an assumption or change a target statement.

Build only the named source modules, with concurrency and memory appropriate to
the local environment. One generic serialized target-build sequence is:

```bash
export LEAN_NUM_THREADS=4
BUILD_LOCK=.curve-build.lock
PREFIX=ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol
for module in \
  S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed \
  S_AlgebraicCurve_residueTheoremK_of_isAlgClosed \
  S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed \
  S_AlgebraicCurve_tateAgreement \
  S_AlgebraicCurve_tateTraceCompat_of_isSeparable \
  S_AlgebraicCurve_tateChainRule
do
  flock -x "$BUILD_LOCK" lake build "+$PREFIX.$module"
done
```

Save the following as a local scratch file named `CurveProofCheck.lean`. It is a
check file, not an additional proof contribution:

```lean
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_tateAgreement
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_tateTraceCompat_of_isSeparable
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_tateChainRule

#check P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.solution
#print axioms P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.solution
#check P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.solution
#print axioms P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.solution
#check P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.solution
#print axioms P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.solution
#check P2MW.S_AlgebraicCurve_tateAgreement.solution
#print axioms P2MW.S_AlgebraicCurve_tateAgreement.solution
#check P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.solution
#print axioms P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.solution
#check P2MW.S_AlgebraicCurve_tateChainRule.solution
#print axioms P2MW.S_AlgebraicCurve_tateChainRule.solution
```

Then run a bounded, locked check in that working copy:

```bash
flock -x .curve-build.lock lake env lean -j 4 -M 16000 CurveProofCheck.lean
```

Inspect the types and original inputs as well as the axiom lists. The recorded
solution axiom list is exactly `[propext, Classical.choice, Quot.sound]` for each
of the six exports. The existing residue input of the conditional RR theorem is
not removed from its statement; the separate proved global residue theorem
supplies it. A matching axiom list alone does not establish a final H102
`#discharges` result or geometric integration.

Labeled selections of the original successful type and axiom output appear in
`Compile/PUBLIC_TYPE_AXIOM_EXCERPTS.md`. Complete raw output is preserved unchanged
privately; no rewritten or abbreviated file is presented as a raw transcript.
