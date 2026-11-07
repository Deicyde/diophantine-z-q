import ZInQKernel.Multiplication.Completeness.Core
import ZInQKernel.Multiplication.Certificate.Guard

/-!
# Completeness of the multiplication template

Blueprint: `multiplication/completeness/completeness.md`.

For all `a, b ∈ ℤ` the multiplication template accepts `(ι(a), ι(b), ι(ab))`. By the unfolding of
the template it suffices to give the height certificate at `(ι(n₁), ι(n₂), ι(n₃))` with shift
points `ι(c_*), ι(c_* n_i)`, and the guard; the guard passes true triples, and the witnesses of the
height certificate are those of `completeness_core`.

Besides pole completeness and the prime pattern, the statement takes as hypotheses the facts
about the constructors `I` that the specification chapter proves: the fixed-scalar semantics of
`S_{c_*}` (`hS`) and the guard polynomial (`hI`), and `M₀ ≥ 1` (size chapter).
-/

namespace ZInQ.Mult

open Syntax

/-- **Completeness of the multiplication template.** -/
theorem multiply_complete (hPC : PoleCompleteness) (h22 : FixedPrimePattern)
    (hM0 : 1 ≤ Syntax.M0) {E : Type} (I : Constructors E) (T : ℤ)
    (hS : ∀ (m : ℤ) (r : Fin 5 → ℚ),
      (scalarTemplate I Syntax.cstar).Rel (Fin.append (iota m) r) ↔ r = iota (Syntax.cstar * m))
    (hI : I.guard T = guardPoly T) (a b : ℤ) :
    (multiplyTemplate I Syntax.cstar Syntax.ell T).Rel (codes3 (iota a) (iota b) (iota (a * b))) := by
  sorry

end ZInQ.Mult
