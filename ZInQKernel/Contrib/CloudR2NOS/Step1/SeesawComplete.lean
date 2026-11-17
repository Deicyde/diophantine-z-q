/-
H5 lane3 Step 1: `OpenImmersionFibreIff` (SeesawLocus.lean) PROVED from H72's native fibre
restriction. GM1 is thereby COMPLETE modulo compile, from H72 single producers only. 2026-11-17.
New file. SOURCE-ONLY, UNCOMPILED. Universe u, any field.

Producer (single, exact path/SHA): `ZInQ.Contrib.CloudR2Poincare.L2.fibrePicardClass_open_baseChange_iff`,
in swarm/h72/src/ZInQKernel/Contrib/CloudR2Poincare/L2/FibreRestriction.lean, sha256
75cc638b2c46298e5a8ef779ccd3c90900827ac81dec2b4c1ca133f9724137bb.
* Hypotheses: `IsPullback fst snd f g` with `[IsOpenImmersion g]`.
* Conclusion: the base-changed residue-fibre class is trivial at `u` iff the original one is
  trivial at `g u`.
* It goes through an actual fibre isomorphism (`fibreComparison_isIso`). There is no CharZero
  and no field restriction.

The square `(X ×_K W) → (X ×_K T)` over `φ : W ⟶ T` is a pullback by Mathlib
`IsPullback.of_right`, pasting with the two `of_hasPullback` squares.

GM1 single producers (all native H72, read by exact SHA):
* L1/ReducedGlobalSeesaw 4ac58f79;
* L1/NativeTrivialityLocus fd0f9728;
* L1/PicardKernel (`pic_map_injective_of_isIso`);
* L2/FibreRestriction 75cc638b.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.SeesawLocus
import ZInQKernel.Contrib.CloudR2Poincare.L2.FibreRestriction

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem openImmersionFibreIff : OpenImmersionFibreIff.{u} := by
  intro K _ X T W fX fT φ _ L _ w
  have hψfst : pullback.map fX (φ ≫ fT) fX fT (𝟙 X) φ (𝟙 _) (by simp) (by simp) ≫
      pullback.fst fX fT = pullback.fst fX (φ ≫ fT) := by simp
  have hψsnd : pullback.map fX (φ ≫ fT) fX fT (𝟙 X) φ (𝟙 _) (by simp) (by simp) ≫
      pullback.snd fX fT = pullback.snd fX (φ ≫ fT) ≫ φ := by simp
  have hsq : IsPullback (pullback.map fX (φ ≫ fT) fX fT (𝟙 X) φ (𝟙 _) (by simp) (by simp))
      (pullback.snd fX (φ ≫ fT)) (pullback.snd fX fT) φ :=
    IsPullback.of_right (by rw [hψfst]; exact IsPullback.of_hasPullback fX (φ ≫ fT)) hψsnd
      (IsPullback.of_hasPullback fX fT)
  simpa only [Scheme.Pic.map_mk] using
    (ZInQ.Contrib.CloudR2Poincare.L2.fibrePicardClass_open_baseChange_iff hsq
      (Scheme.Pic.mk L) w).symm

/-- GM1 `SeesawPulledBack`, with no remaining obligation of this lane. It rests on the H72 native
single producers only. -/
theorem seesawPulledBack_native : SeesawPulledBack.{u} :=
  seesawPulledBack_v3'' openImmersionFibreIff

end ZInQ.Contrib.CloudR2NOS.Step1
