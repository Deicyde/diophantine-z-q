/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 Step-2 small obligation for C3's B1 (`Step2B1/HeightOneMax.lean` f1947a81; statement used
verbatim through the import): `InvertibleSupportNeUniv`, PROVED. SOURCE ONLY, UNCOMPILED.
Native HELD. Universe u, default options.

If `supp D = X` then `D = ⊥` (Mathlib `IdealSheafData.support_eq_top_iff`, `X` reduced). But an
invertible `D` is generated near any point `x` (one exists: `X` integral) by a non-zerodivisor
`s` of the domain `Γ(X, U)` (`U ∋ x` nonempty), and `D = ⊥` forces `s = 0`, which is not a
non-zerodivisor in a nontrivial ring. Truth: TRUE (this is the proof).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.HeightOneMax
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.EffectiveCartier

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small

/-- **`InvertibleSupportNeUniv` proved.** -/
theorem invertibleSupportNeUniv : ZInQ.Contrib.CloudR2NOS.Step2B1.InvertibleSupportNeUniv.{u} := by
  intro X _ D hD hsupp
  have htop : D.support = ⊤ := Closeds.ext (hsupp.trans Closeds.coe_top.symm)
  have hbot : D = ⊥ := Scheme.IdealSheafData.support_eq_top_iff.1 htop
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hxU, s, hs, hspan⟩ := hD x
  haveI : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have hs0 : s = 0 := by
    have hmem : s ∈ D.ideal U := by
      rw [hspan]
      exact Ideal.subset_span rfl
    rw [hbot, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Ideal.mem_bot] at hmem
    exact hmem
  exact nonZeroDivisors.ne_zero hs hs0

end ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small
