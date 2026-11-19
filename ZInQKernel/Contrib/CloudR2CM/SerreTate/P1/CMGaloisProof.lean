import ZInQKernel.Contrib.CloudR2CM.SerreTate.ArithmeticInputStatements
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.OriginalTateGeometry
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.TateRationalComparison
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.RationalCMAction
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.QuadraticCentralizer
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Commutativity of the original whole CM Galois image

The actual completed quadratic action is faithful on both factors when
it splits. Geometric Tate rank two and the full quadratic commutant give
rational commutation; the actual injective Tate comparison reflects it
to the original integral Galois operators.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj TensorProduct

namespace HDec.CMSerreTate.P1

/-- The whole original Galois image is abelian for a base-defined CM
elliptic curve, at every prime. No faithful-action, freeness, rank-one or
prime-to-conductor premise is added. -/
theorem cmGaloisImageAbelian_proved : HDec.CMSerreTate.CMGaloisImageAbelian := by
  intro K hK hNF A hA k hk hNFk R hR hCM ℓ hPrime
  obtain ⟨e⟩ := hCM
  have hℓ : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hFree, hFinite, _⟩ := originalTateModuleFree_proved K A ℓ hℓ
  letI : Module.Free ℤ_[ℓ] (A.T ℓ) := hFree
  letI : Module.Finite ℤ_[ℓ] (A.T ℓ) := hFinite
  haveI : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := Module.Finite.base_change ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)
  haveI : FiniteDimensional ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] k) := Module.Finite.base_change ℚ ℚ_[ℓ] k
  have hB : Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] k) = 2 := by
    rw [Module.finrank_baseChange]
    exact hR.2.1
  have hV : Module.finrank ℚ_[ℓ] (A.V ℓ) = 2 := original_rational_tate_rank_two A hA ℓ
  apply galoisImageAbelian_of_galRep_commutation A ℓ
  intro σ τ
  exact commute_of_faithful_quadratic (cmTensorAction A ℓ R e hR)
    (cmTensorAction_injective A ℓ hℓ R e hR) hB hV (A.galRep ℓ σ) (A.galRep ℓ τ)
    (galRep_commute_cmTensor A ℓ R e hR σ) (galRep_commute_cmTensor A ℓ R e hR τ)

end HDec.CMSerreTate.P1
