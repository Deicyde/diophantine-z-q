import ZInQKernel.OneProof.H.TailW
import ZInQKernel.Contrib.CloudB3W12Tame.QuotProper
import ZInQKernel.Contrib.CloudB3W12Tame.TameQuotSmooth

/-!
# H-91 (Cloud Worker 12, author D): mcr-glue's leaf L3 `HDec.MCRGlue.TameQuotientSmooth`, proved

For `𝒴` proper and smooth of relative dimension 1 over `ℤ_(p)`, a finite group `G` of `ℤ_(p)`-automorphisms with
`p ∤ |G|`, and `q : 𝒴 → 𝒵` over `ℤ_(p)` with `IsGQuotient G q.left` and `q.left` finite, `𝒵` is proper and smooth
of relative dimension 1 over `ℤ_(p)`.

* Properness: `HDec.CloudB3W12Tame.QuotProper.isProper_of_isGQuotient` (copied from task p1-quot2/p1-quot3).
* Smoothness: `HDec.CloudB3W12Tame.TameQuotScheme.tameQuotientSmoothRelDim_proof` (copied from task p1-quot3, with
  its one non-proved input, the textbook field `CurveSplit.RegularSmoothPerfect` (Stacks 00TV), removed: over a
  perfect field, the local rings of the invariant ring are normal of dimension `≤ 1`, hence fields (Mathlib
  `Algebra.FormallySmooth.of_perfectField`) or DVRs (vendored FLT
  `Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField`, anthropics/fermats-last-theorem @ 6e837e75)).

No hypotheses, no `sorry`, no `axiom`.
-/

namespace HDec.CloudB3W12Tame

/-- **mcr-glue's L3 `TameQuotientSmooth`, proved with no hypotheses.** -/
theorem tameQuotientSmooth_proof : HDec.MCRGlue.TameQuotientSmooth :=
  tameQuotientSmooth_of_relDim TameQuotScheme.tameQuotientSmoothRelDim_proof

end HDec.CloudB3W12Tame
