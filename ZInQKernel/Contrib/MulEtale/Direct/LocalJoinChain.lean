/-
Multiplication-etale construction: LocalJoinChain.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.LocalCotangentCriterion
import ZInQKernel.Contrib.MulEtale.Direct.CotangentDerivationNaturality

open scoped TensorProduct

noncomputable section

namespace H101DirectFieldRoute

/-- The concrete local callchain: actual derivation restriction -> actual
residue cotangent map -> actual full cotangent map -> formal etaleness.
For the origin of multiplication, R/S/T are the ACTUAL base/source/target
stalks. Finiteness/freeness follows from their given native smoothness data. -/
theorem formallyEtale_of_bijective_derivationRestriction
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalRing T]
    [Algebra.EssFiniteType R S] [Algebra.EssFiniteType R T]
    [Algebra.FormallySmooth R S] [Algebra.FormallySmooth R T]
    (h : Function.Bijective
      (fun d : Derivation R T (IsLocalRing.ResidueField T) => d.compAlgebraMap S)) :
    Algebra.FormallyEtale S T := by
  let κ := IsLocalRing.ResidueField T
  let l := KaehlerDifferential.mapBaseChange R S T
  let E := TensorProduct.AlgebraTensorModule.cancelBaseChange S T κ κ Ω[S⁄R]
  have hb : Function.Bijective (residueCotangentMap R S T κ) :=
    residueCotangentMap_bijective_of_derivationRestriction R S T κ h
  have hl : Function.Bijective (l.baseChange κ) := by
    constructor
    · intro x y hxy
      apply E.injective
      apply hb.1
      change l.baseChange κ (E.symm (E x)) = l.baseChange κ (E.symm (E y))
      simpa only [LinearEquiv.symm_apply_apply] using hxy
    · intro y
      obtain ⟨x, hx⟩ := hb.2 y
      exact ⟨E.symm x, hx⟩
  apply formallyEtale_of_residue_cotangent_bijective R S T
  simpa only [LinearMap.baseChange_eq_lTensor] using hl

end H101DirectFieldRoute
