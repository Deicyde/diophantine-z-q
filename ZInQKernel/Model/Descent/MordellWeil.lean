import ZInQKernel.Model.Descent.Index

/-!
# Mordell–Weil for `E/K₀` from the descent

Blueprint: `model/descent/mordell-weil-from-descent.md`.

`E(K₀)` is finitely generated. The descent theorem `AddCommGroup.fg_of_descent'` (Mathlib,
`GroupTheory/Descent.lean`) needs a finite index `[E(K₀) : 2E(K₀)]` (here `8`, by
`index_two_E`), a nonnegative height with the approximate parallelogram law and the
Northcott property. The naïve height `Point.naiveHeight` of
`Mathlib/NumberTheory/Height/EllipticCurve.lean` has all three over the number field `K₀`
(`approx_parallelogram_law`; the Northcott instance comes from the number field `K₀` through
`Mathlib/NumberTheory/Height/NumberField.lean`).

This discharges the hypothesis `MordellWeilE` of the main theorem.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine Height

/-- **Mordell–Weil for `E/K₀`**: `E(K₀)` is finitely generated. -/
theorem mordellWeilE : MordellWeilE := by
  show AddGroup.FG (shortCurve (-genD ^ 2)).toAffine.Point
  obtain ⟨C, hC⟩ := approx_parallelogram_law (shortCurve (-genD ^ 2)).toAffine
  exact AddCommGroup.fg_of_descent' finiteIndex_two_E
    (fun P => by rw [Point.naiveHeight_eq_logHeight]; exact logHeight_nonneg _) hC

end ZInQ
