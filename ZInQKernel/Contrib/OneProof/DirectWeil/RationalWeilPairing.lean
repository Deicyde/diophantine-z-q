import ZInQKernel.Contrib.OneProof.DirectWeil.IntegralWeilPairing
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

noncomputable section

open PkgI3 PkgI3.AbVar HDec.WeilPairing TensorProduct
open scoped CategoryTheory.MonObj

set_option synthInstance.maxHeartbeats 80000

namespace PicDict.DirectPairing

variable {ℓ : ℕ} [Fact ℓ.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[ℓ] T]

private theorem bilin_ext_tmul {B C : LinearMap.BilinForm ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] T)}
    (h : ∀ (a b : ℚ_[ℓ]) (x y : T), B (a ⊗ₜ x) (b ⊗ₜ y) = C (a ⊗ₜ x) (b ⊗ₜ y)) :
    B = C := by
  apply AlgebraTensorModule.ext
  intro a x
  apply AlgebraTensorModule.ext
  intro b y
  exact h a b x y

/-- Scalar extension of the Weil form associated to the given line bundle.
Vanishing on the Tate lattice is measured by the original tower pairing. -/
theorem exists_rationalWeilForm_of_finite_kernel {K : Type} [Field K] (A : AbVar K)
    (L : A.X.left.Pic) (hℓ : (ℓ : K) ≠ 0)
    (hfin : {x : A.Pt (AlgebraicClosure K) | polarization A L x = 1}.Finite)
    (g : ℕ) (hdim : A.dim = g) :
    ∃ (_ : FiniteDimensional ℚ_[ℓ] (A.V ℓ)) (B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ)),
      Module.finrank ℚ_[ℓ] (A.V ℓ) = 2 * g ∧ B.Nondegenerate ∧ (∀ x, B x x = 0) ∧
      (∀ (σ : Gal K) (x y : A.V ℓ),
        B (A.galRep ℓ σ x) (A.galRep ℓ σ y) =
          algebraMap ℤ_[ℓ] ℚ_[ℓ] (cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv) * B x y) ∧
      ∀ x y : A.T ℓ, B (1 ⊗ₜ[ℤ_[ℓ]] x) (1 ⊗ₜ[ℤ_[ℓ]] y) = 0 ↔ tatePairing A L hℓ x y = 0 := by
  classical
  obtain ⟨B0, hsep, halt, hgal, hzero⟩ := exists_tateWeilForm_of_finite_kernel A L hℓ hfin
  have hT5 := HDec.HSyn.torsionStructure_ofK5 (AvSplit.torsionStructure_of_mumford
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof)
  obtain ⟨hfree, hfinite, hrank⟩ := HDec.HSyn.tateModuleFree_of_t5' hT5 K A ℓ hℓ
  let hdomain : IsDomain ℚ_[ℓ] := Field.isDomain
  let : Nontrivial ℚ_[ℓ] := hdomain.toNontrivial
  let : StrongRankCondition ℚ_[ℓ] := commRing_strongRankCondition _
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  let bV : Module.Basis _ ℚ_[ℓ] (A.V ℓ) := Algebra.TensorProduct.basis ℚ_[ℓ] b
  have hfinV : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := Module.Finite.of_basis bV
  let B := B0.baseChange ℚ_[ℓ]
  refine ⟨hfinV, B, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Module.finrank_baseChange (R := ℚ_[ℓ]) (S := ℤ_[ℓ]) (M' := A.T ℓ)]
    rw [hdim] at hrank
    have h : (((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((2 * g : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [hrank]
      push_cast
      rfl
    exact_mod_cast WithBot.coe_injective h
  · let f := algebraMap ℤ_[ℓ] ℚ_[ℓ]
    have hi : Function.Injective f := IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
    have hmatrix : LinearMap.BilinForm.toMatrix bV B = f.mapMatrix (LinearMap.BilinForm.toMatrix b B0) := by
      ext i j
      simp only [LinearMap.BilinForm.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, bV,
        Algebra.TensorProduct.basis_apply, B, LinearMap.BilinForm.baseChange_tmul, mul_one,
        ← Algebra.algebraMap_eq_smul_one, f]
    have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
      (LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep)
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bV, hmatrix, ← RingHom.map_det]
    exact fun h => hdet (hi (h.trans (map_zero f).symm))
  · have hflip : B.flip = -B := by
      apply bilin_ext_tmul
      intro a b x y
      change B (b ⊗ₜ y) (a ⊗ₜ x) = -B (a ⊗ₜ x) (b ⊗ₜ y)
      simp only [B, LinearMap.BilinForm.baseChange_tmul]
      rw [mul_comm b a, HDec.G0Galois.skew_of_alt' B0 halt x y, neg_smul]
    intro x
    have h := congrArg (fun C : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) => C x x) hflip
    change B x x = -B x x at h
    have h2 : (2 : ℚ_[ℓ]) * B x x = 0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro σ x y
    let c := algebraMap ℤ_[ℓ] ℚ_[ℓ] (cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv)
    have hc : B.comp (A.galRep ℓ σ) (A.galRep ℓ σ) = c • B := by
      apply bilin_ext_tmul
      intro a b x y
      change B ((A.galT σ).baseChange ℚ_[ℓ] (a ⊗ₜ x)) ((A.galT σ).baseChange ℚ_[ℓ] (b ⊗ₜ y)) =
        c * B (a ⊗ₜ x) (b ⊗ₜ y)
      simp only [B, LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hgal,
        Algebra.smul_def, map_mul, mul_assoc, c]
    exact congrArg (fun C : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) => C x y) hc
  · intro x y
    rw [LinearMap.BilinForm.baseChange_tmul, mul_one, ← Algebra.algebraMap_eq_smul_one,
      map_eq_zero_iff (algebraMap ℤ_[ℓ] ℚ_[ℓ]) (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]), hzero]

/-- Nondegenerate alternating Weil form on the rational Tate module, with the cyclotomic
character as its multiplier over every field of characteristic different from `ℓ`. -/
theorem exists_rationalWeilForm {K : Type} [Field K] (A : AbVar K) (hℓ : (ℓ : K) ≠ 0)
    (g : ℕ) (hdim : A.dim = g) :
    ∃ (_ : FiniteDimensional ℚ_[ℓ] (A.V ℓ)) (B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ)),
      Module.finrank ℚ_[ℓ] (A.V ℓ) = 2 * g ∧ B.Nondegenerate ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Gal K) (x y : A.V ℓ),
        B (A.galRep ℓ σ x) (A.galRep ℓ σ y) =
          algebraMap ℤ_[ℓ] ℚ_[ℓ] (cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv) * B x y := by
  obtain ⟨L, hfin⟩ := exists_finite_polarization_kernel A
  obtain ⟨hfd, B, hrank, hB, halt, hgal, _⟩ :=
    exists_rationalWeilForm_of_finite_kernel A L hℓ hfin g hdim
  exact ⟨hfd, B, hrank, hB, halt, hgal⟩

end PicDict.DirectPairing
