/-
# H5 / NOS round 2, lane 1: amplifying a finite presentation of a positive power to a closed one

Newly authored glue (H5 round-2 lane 1, 2026-11-15), additive to cp13. Combines cp13
(`exists_closedImmersionBySections_tensorPow_of_finiteBySections`), the double-power comparison
`SourcePowMul.tensorPowMul` and the Source theorem `ProjPresentation.exists_of_iso` (FLT @ 6e837e75…,
Apache-2.0, Anthropic, PBC). No monoidal notation is written in this file.
-/
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.FiniteProjAssembly
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.SourcePowMul
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- `ClosedImmersionBySections` transports along an isomorphism of modules (Source `exists_of_iso`,
which keeps the SAME presentation map). -/
theorem closedImmersionBySections_of_iso {M M' : X.Modules} (e : M ≅ M')
    (h : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections M f) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections M' f := by
  obtain ⟨N, 𝔓, h𝔓⟩ := h
  obtain ⟨𝔓', h1, -⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_of_iso 𝔓 e
  exact ⟨N, 𝔓', by rw [h1]; exact h𝔓⟩

/-- **Amplification.** If a POSITIVE Source power `M^{⊗a}` is finite-by-sections, then some positive
Source power `M^{⊗n}` (with `n = a·b`) is closed-immersion-by-sections. -/
theorem exists_closedImmersionBySections_tensorPow_of_finiteBySections_tensorPow {M : X.Modules}
    (a : ℕ) (ha : 0 < a)
    (h : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M a) f) :
    ∃ n : ℕ, 0 < n ∧
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections
        (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow M n) f := by
  obtain ⟨b, hb, hc⟩ := exists_closedImmersionBySections_tensorPow_of_finiteBySections h
  exact ⟨a * b, Nat.mul_pos ha hb,
    closedImmersionBySections_of_iso (ZInQ.Contrib.CloudR2NOS.SingleOrder.SourcePowMul.tensorPowMul M a b) hc⟩

end ZInQ.Contrib.CloudR2NOS.SingleOrder.FiniteProjPower
