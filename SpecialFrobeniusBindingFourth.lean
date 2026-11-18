import SpecialPointBindingThird

/-!
# The exact original Frobenius power on actual special-fibre points

The power of the constructed residue algebra automorphism is the literal
native residue action of the original decomposition element power. Thus
fixedness of an original generic point yields fixedness of its actual
reduced point of the actual base-change special fibre.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace SemistableGeometry.SpecialFrobeniusBinding

open SemistableGeometry.IntegralGalois
open SemistableGeometry.IntegralResidueActions
open SemistableGeometry.ActualResidueFrobenius
open SemistableGeometry.SpecialPointBinding
open SemistableGeometry.FrobeniusFixed

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
variable {w : ValuationSubring Ω}

/-- The two native Spec actions are equal, including the exact power and base orientation. -/
theorem specialAction_eq_frobenius_power (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1) (r : ℕ) :
    letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
    algebraPointMap (residueFrobeniusAlg hw σ hD hcong ^ r).toAlgHom =
      specialActionArrow hw (σ ^ r) (pow_mem hD r) := by
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (residueFrobeniusAlg hw σ hD hcong ^ r).toAlgHom.toRingHom) =
    Spec.map (CommRingCat.ofHom (residueRingAction w (σ ^ r) (pow_mem hD r)))
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  change (residueFrobeniusAlg hw σ hD hcong ^ r) a =
    residueRingAction w (σ ^ r) (pow_mem hD r) a
  rw [residueFrobeniusAlg_pow_apply]
  change MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w)
      ((⟨σ, hD⟩ : w.decompositionSubgroup K) ^ r) a =
    MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w)
      ⟨σ ^ r, pow_mem hD r⟩ a
  congr 1

/-- Fixed original Frobenius-power points reduce into the genuine fixed geometric special-point set. -/
theorem specialPoint_fixed_of_original_fixed {A : PkgI3.AbVar K}
    (hw : w.comap (algebraMap K Ω) = O)
    (N : Over (Spec (CommRingCat.of O))) [IsSeparated N.hom]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1)
    (r : ℕ) (a : valuationDomain w hw ⟶ N)
    (hfix : A.galAct (σ ^ r) (originalPoint N gen w hw a) = originalPoint N gen w hw a) :
    letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
    algebraPointMap (residueFrobeniusAlg hw σ hD hcong ^ r).toAlgHom ≫
      specialPoint hw N (reductionArrow w hw ≫ a) =
        specialPoint hw N (reductionArrow w hw ≫ a) := by
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
  have he : algebraPointMap (residueFrobeniusAlg hw σ hD hcong ^ r).toAlgHom =
      specialActionArrow hw (σ ^ r) (pow_mem hD r) :=
    specialAction_eq_frobenius_power hw σ hD hcong r
  have hc := specialPoint_covariance hw N (σ ^ r) (pow_mem hD r) (reductionArrow w hw ≫ a)
  have hf := reduction_fixed_of_original_fixed N gen w hw (σ ^ r) (pow_mem hD r) a hfix
  exact (congrArg (fun f : specialDomain hw ⟶ specialDomain hw ↦
      f ≫ specialPoint hw N (reductionArrow w hw ≫ a)) he).trans
    (hc.trans (congrArg (specialPoint hw N) hf))

end SemistableGeometry.SpecialFrobeniusBinding
