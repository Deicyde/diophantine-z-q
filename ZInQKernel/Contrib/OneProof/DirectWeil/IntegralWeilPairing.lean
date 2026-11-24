import ZInQKernel.Contrib.OneProof.DirectWeil.TateWeilPairing
import ZInQKernel.Contrib.OneProof.DirectWeil.PolarizationTateRadical
import ZInQKernel.Contrib.OneProof.DirectWeil.VeryAmplePolarizationKernel

noncomputable section

open CategoryTheory AlgebraicGeometry
open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing
open scoped CategoryTheory.MonObj

namespace PicDict.DirectPairing

variable {K : Type} [Field K] (A : AbVar K) (L : A.X.left.Pic) {ℓ : ℕ} [Fact ℓ.Prime]
variable (hℓ : (ℓ : K) ≠ 0)

theorem tatePairing_right_radical (hfin : {x : A.Pt (AlgebraicClosure K) | polarization A L x = 1}.Finite)
    (y : A.T ℓ) (hy : ∀ x, tatePairing A L hℓ x y = 0) : y = 0 := by
  apply tate_eq_zero_of_finitePairing_eq_zero A L hℓ y hfin
  intro k z
  obtain ⟨x, hx⟩ := levelPoint_surjective A hℓ k z
  have hh := congrArg (fun s : TMu K ℓ => s.1 k) (hy x)
  change tateSeq A L hℓ x y k = 0 at hh
  have hv := congrArg Additive.toMul hh
  change (levelPairing A L hℓ k (levelPoint A x k) (levelPoint A y k)).val = 1 at hv
  apply Mu.val_injective
  rw [Mu.val_zero]
  simpa only [levelPairing, hx] using hv

theorem tatePairing_left_radical (hfin : {x : A.Pt (AlgebraicClosure K) | polarization A L x = 1}.Finite)
    (x : A.T ℓ) (hx : ∀ y, tatePairing A L hℓ x y = 0) : x = 0 := by
  apply tatePairing_right_radical A L hℓ hfin x
  intro y
  have h := tatePairing_self A L hℓ (x + y)
  simp only [map_add, LinearMap.add_apply, tatePairing_self, hx, zero_add, add_zero] at h
  exact h

theorem exists_tateWeilForm_of_finite_kernel
    (hfin : {x : A.Pt (AlgebraicClosure K) | polarization A L x = 1}.Finite) :
    ∃ B : LinearMap.BilinForm ℤ_[ℓ] (A.T ℓ), B.SeparatingLeft ∧ (∀ x, B x x = 0) ∧
      (∀ (σ : Gal K) (x y : A.T ℓ),
        B (A.galT σ x) (A.galT σ y) =
          ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * B x y) ∧
      ∀ x y, B x y = 0 ↔ tatePairing A L hℓ x y = 0 := by
  let : NeZero (ℓ : K) := ⟨hℓ⟩
  obtain ⟨g, hg⟩ := exists_tmu_gen K ℓ
  refine ⟨(tatePairing A L hℓ).compr₂ (tmuCoordLin hg), ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply tatePairing_left_radical A L hℓ hfin x
    intro y
    exact tmuCoordLin_injective hg ((hx y).trans (map_zero (tmuCoordLin hg)).symm)
  · intro x
    simp only [LinearMap.compr₂_apply, tatePairing_self, map_zero]
  · intro σ x y
    have h := congrArg (tmuCoordLin hg) (tatePairing_cyclotomic A L hℓ σ x y)
    simpa only [LinearMap.compr₂_apply, map_smul, smul_eq_mul] using h
  · intro x y
    change tmuCoordLin hg (tatePairing A L hℓ x y) = 0 ↔ _
    rw [← (tmuCoordLin hg).map_zero, (tmuCoordLin_injective hg).eq_iff]

include hℓ in
/-- Every abelian variety admits a nondegenerate alternating integral Weil form with
cyclotomic multiplier for each prime invertible in the ground field. -/
theorem exists_tateWeilForm :
    ∃ B : LinearMap.BilinForm ℤ_[ℓ] (A.T ℓ), B.SeparatingLeft ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Gal K) (x y : A.T ℓ),
        B (A.galT σ x) (A.galT σ y) =
          ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * B x y := by
  obtain ⟨L, hfin⟩ := exists_finite_polarization_kernel A
  obtain ⟨B, hsep, halt, hgal, _⟩ := exists_tateWeilForm_of_finite_kernel A L hℓ hfin
  exact ⟨B, hsep, halt, hgal⟩

end PicDict.DirectPairing
