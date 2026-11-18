import IntegralGaloisThird
import NeronGenericFibreV001

/-!
# Binding the native integral generic map to the original point supplier

The two geometric constructions have the same actual Spec maps and
pullback projections. Separatedness therefore gives injectivity of the
original integral generic map, and its proved original Galois covariance
reflects fixedness back to the native integral section.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace SemistableGeometry.OriginalPointBinding

open SemistableGeometry.IntegralGalois

variable {K : Type} [Field K] {O : ValuationSubring K}
variable {Ω : Type} [Field Ω] [Algebra K Ω]

/-- The actual integral-point map agrees with the previously constructed native generic-fibre map. -/
theorem originalPoint_eq_genericFibre {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (a : valuationDomain w hw ⟶ N) :
    originalPoint N gen w hw a = NeronInvariantTorsion.genericFibre O w hw gen a := by
  rfl

/-- Native separatedness, not a supplied desired injection, makes the original generic map injective. -/
theorem originalPoint_injective {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) [IsSeparated N.hom]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    Function.Injective (originalPoint N gen w hw) := by
  exact NeronInvariantTorsion.genericFibre_injective O w hw gen

/-- Literal original Galois fixedness reflects to the actual integral section. -/
theorem integral_fixed_of_original_fixed {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) [IsSeparated N.hom]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (a : valuationDomain w hw ⟶ N)
    (hfix : A.galAct σ (originalPoint N gen w hw a) = originalPoint N gen w hw a) :
    valuationActionArrow w hw σ hD ≫ a = a := by
  apply originalPoint_injective N gen w hw
  rw [originalPoint_covariance, hfix]

end SemistableGeometry.OriginalPointBinding
