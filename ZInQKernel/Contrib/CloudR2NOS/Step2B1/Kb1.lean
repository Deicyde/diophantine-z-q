/-
H5 lane3 Step 2, B1 KEY (K-b.1) `HeightOnePointBehaviour` (KbPlan.lean fd92404a) PROVED from ONE
height obligation and C4's `PointsOfSupportInComponents`. 2026-11-17. New file. SOURCE-ONLY,
UNCOMPILED. Universe u. No purity is needed.

Obligation (TRUE), `HeightOneMaximalInSupport`: for a height-one point `η = U.fromSpec p` of
`supp D` (`D` invertible) and an irreducible closed `Y` with `η ∈ Y ⊆ supp D`, we have
`Y = closure {η}`.
* Let `ξ` be the generic point of `Y` (sober), so `ξ ⤳ η`, and `ξ ∈ U` since opens are
  generization-closed.
* `supp D ≠ univ`: `D` is invertible, hence `≠ ⊥`, and Mathlib `support_eq_top_iff` applies on
  the reduced `A`. So `ξ` is not the generic point of `A`.
* If `ξ ≠ η`, the primes give a chain `⊥ < q_ξ < p` in the domain `Γ(U)`, so `height p ≥ 2`.
  This contradicts `height p = 1`.

Proof of (K-b.1):
* Part 1: `η` lies in a component `C` (`PointsOfSupportInComponents`), and `C = closure {η}` by
  the obligation. From `t_x⁻¹ C = C`: `t_x η ∈ C`, so `η ⤳ t_x η`. Likewise `η ⤳ t_x⁻¹ η`, and
  applying the continuous `t_x` gives `t_x η ⤳ η`. Schemes are T0, so `t_x η = η`.
* Part 2: if `t_x η ∈ supp D`, it lies in a component `C'`, so `η ∈ t_x⁻¹ C' = C' ⊆ supp D`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.KbPlan
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.MumfordSmall

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

local notation "tr" => H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation

/-- (TRUE; chain of primes) A height-one point of the support is generic in every irreducible
closed subset of the support containing it. -/
def HeightOneMaximalInSupport : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData), D.IsInvertible →
    ∀ (U : A.X.left.affineOpens) (p : PrimeSpectrum Γ(A.X.left, U.1)), p.asIdeal.height = 1 →
      U.2.fromSpec p ∈ (D.support : Set A.X.left) →
      ∀ Y : Set A.X.left, IsIrreducible Y → IsClosed Y → U.2.fromSpec p ∈ Y →
        Y ⊆ (D.support : Set A.X.left) → Y = closure {U.2.fromSpec p}

theorem heightOnePointBehaviour (hH : HeightOneMaximalInSupport.{u})
    (hJ4 : ZInQ.Contrib.CloudR2NOS.Step2B2.PointsOfSupportInComponents.{u}) :
    HeightOnePointBehaviour.{u} := by
  intro K _ _ A _ D hD x hfix U p hp
  set η := U.2.fromSpec p
  have hinv : ∀ a, tr A x (tr A x⁻¹ a) = a := by
    intro a
    have h := congrArg (fun φ : A.X.left ⟶ A.X.left => φ a) (tr_mul A x⁻¹ x)
    rw [inv_mul_cancel, tr_one] at h
    simpa using h.symm
  have hinv' : ∀ a, tr A x⁻¹ (tr A x a) = a := by
    intro a
    have h := congrArg (fun φ : A.X.left ⟶ A.X.left => φ a) (tr_mul A x x⁻¹)
    rw [mul_inv_cancel, tr_one] at h
    simpa using h.symm
  constructor
  · intro hη
    obtain ⟨C, hC, hηC⟩ := hJ4 A D η hη
    have hCcl : IsClosed C := by
      have h3 : closure C ⊆ C :=
        hC.2 ⟨closure_minimal hC.1.1 D.support.isClosed, hC.1.2.closure⟩ subset_closure
      exact closure_subset_iff_isClosed.mp h3
    have hCeq : C = closure {η} := hH A D hD U p hp hη C hC.1.2 hCcl hηC hC.1.1
    have hfixC : (tr A x) ⁻¹' C = C := hfix C hC.1.1 hC
    -- `η ⤳ t_x η`
    have h1 : η ⤳ tr A x η := by
      rw [specializes_iff_mem_closure, ← hCeq]
      have : η ∈ (tr A x) ⁻¹' C := by rw [hfixC]; exact hηC
      exact this
    -- `η ⤳ t_x⁻¹ η`, hence `t_x η ⤳ η`
    have h2 : η ⤳ tr A x⁻¹ η := by
      rw [specializes_iff_mem_closure, ← hCeq]
      have : tr A x (tr A x⁻¹ η) ∈ C := by rw [hinv]; exact hηC
      rw [← hfixC]
      exact this
    have h3 : tr A x η ⤳ η := by
      have := h2.map (tr A x).continuous
      rwa [hinv] at this
    exact (h1.antisymm h3).symm
  · intro hη hcontra
    obtain ⟨C', hC', hxC'⟩ := hJ4 A D (tr A x η) hcontra
    have : η ∈ (tr A x) ⁻¹' C' := hxC'
    rw [hfix C' hC'.1.1 hC'] at this
    exact hη (hC'.1.1 this)

end ZInQ.Contrib.CloudR2NOS.Step2B1
