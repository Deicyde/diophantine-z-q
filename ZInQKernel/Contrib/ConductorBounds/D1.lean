import ZInQKernel.Contrib.HilbertDifferent.GlobalFormula
import ZInQKernel.Contrib.DifferentBound.SerreGlobal
import ZInQKernel.HDecomp.Conductor.Breaks

/-!
# D1 application with proved global literature leaves

This theorem is a direct application of the baseline `D1_genuine`, with only
its two literature-leaf arguments supplied by the closed global contributions.
All original field, prime, ramification, factorial and nontriviality hypotheses
remain explicit. It is not H, a height theorem, registry integration, independent
acceptance or a polynomial/manuscript record.

The same-tree type and proof-body check is documented in
`docs/research/conductor-d1-closed.md`. No protected acceptance is asserted.
-/

namespace ZInQ.Contrib.ConductorBounds

open NumberField

/-- The genuine D1 numerical upper-break bound, without an assumed Hilbert or
Serre literature leaf. The original mathematical hypotheses are retained. -/
theorem D1_closed
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (a : ℕ) (ha : 1 ≤ a) (hea : P.ramificationIdx ℤ ≤ a.factorial)
    (b : ℕ) (hb : GlueConductor.ramGroup L P b ≠ ⊥) :
    GlueConductor.phi (GlueConductor.ramCard L P) b ≤ 4 * a ^ 2 :=
  GlueConductor.D1_genuine
    ZInQ.Contrib.HilbertDifferent.hilbertDifferentFormula
    ZInQ.Contrib.DifferentBound.serreDifferentBound
    L p P a ha hea b hb

#check @D1_closed
#print axioms D1_closed

end ZInQ.Contrib.ConductorBounds
