import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelDiamondFromProducts
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence

/-!
# Prime Hecke rationality from an explicit principal torsion-product representation

The actual cusp-form Hecke recurrence is combined with the proved conditional
all-diamond descent. The principal product representation remains a visible
hypothesis; it is not supplied by this file. The divisibility guard on the
second term is retained, and bad primes use the existing zero extension.
-/

noncomputable section
set_option autoImplicit false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelHeckeFromProducts

variable {N : ℕ} [NeZero N] {J : Type*} [Fintype J]

/-- The cusp-form diamond conclusion uses the same actual principal representation. -/
theorem diamond_cusp_rational_of_product_representation
    (k : ℕ) (g : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ))
    (hg : ∀ n, ∃ q : ℚ, (qExpansion 1 g).coeff n = (q : ℂ))
    (v : J → Fin k → ℤ × ℤ) (hv : ∀ j i, AllLevelForms.Good N (v j i))
    (c : J → ℂ)
    (hRep : _root_.ModularForm.restrict (Subgroup.map_mono (Gamma_le_Gamma1 N))
      (g : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ)) =
        ∑ j, c j • AllLevelProducts.productForm N (NeZero.pos N) k (v j) (hv j)) :
    ∀ u : (ZMod N)ˣ, ∀ n, ∃ q : ℚ,
      (qExpansion 1 (diamondOpCusp (k : ℤ) u g)).coeff n = (q : ℂ) := by
  have h := AllLevelDiamondFromProducts.diamond_coefficients_rational_of_product_representation
    N k (g : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ)) hg v hv c hRep
  intro u n
  have hu := h u n
  rw [diamondOp_coe_cuspForm] at hu
  exact hu

/-- The actual prime-Hecke conclusion, including bad primes, conditional only
on the displayed principal product representation and rational input. -/
theorem rational_hecke_of_product_representation
    (k : ℕ) {p : ℕ} (hp : p.Prime)
    (g : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ))
    (hg : ∀ n, ∃ q : ℚ, (qExpansion 1 g).coeff n = (q : ℂ))
    (v : J → Fin k → ℤ × ℤ) (hv : ∀ j i, AllLevelForms.Good N (v j i))
    (c : J → ℂ)
    (hRep : _root_.ModularForm.restrict (Subgroup.map_mono (Gamma_le_Gamma1 N))
      (g : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ)) =
        ∑ j, c j • AllLevelProducts.productForm N (NeZero.pos N) k (v j) (hv j)) :
    ∀ n, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd (k : ℤ) (diagCosetGamma1 N p) g)).coeff n =
        (q : ℂ) := by
  intro m
  rw [qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime
    (k := (k : ℤ)) hp g m]
  obtain ⟨q1, hq1⟩ := hg (p * m)
  rw [hq1]
  split_ifs with hpm
  · by_cases hcop : Nat.Coprime p N
    · rw [diamondOpCuspNat_of_coprime _ hcop]
      obtain ⟨q2, hq2⟩ := diamond_cusp_rational_of_product_representation k g hg v hv c hRep
        (ZMod.unitOfCoprime p hcop) (m / p)
      exact ⟨q1 + (p : ℚ) ^ ((k : ℤ) - 1) * q2, by rw [hq2]; push_cast; ring⟩
    · rw [diamondOpCuspNat_of_not_coprime _ hcop, LinearMap.zero_apply]
      exact ⟨q1, by simp [qExpansion_zero]⟩
  · exact ⟨q1, by simp⟩

/-- Integral input is a special case. The representation hypothesis is still explicit. -/
theorem integral_input_hecke_rational_of_product_representation
    (k : ℕ) {p : ℕ} (hp : p.Prime)
    (g : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ))
    (hg : ∀ n, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ))
    (v : J → Fin k → ℤ × ℤ) (hv : ∀ j i, AllLevelForms.Good N (v j i))
    (c : J → ℂ)
    (hRep : _root_.ModularForm.restrict (Subgroup.map_mono (Gamma_le_Gamma1 N))
      (g : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ)) =
        ∑ j, c j • AllLevelProducts.productForm N (NeZero.pos N) k (v j) (hv j)) :
    ∀ n, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd (k : ℤ) (diagCosetGamma1 N p) g)).coeff n =
        (q : ℂ) := by
  apply rational_hecke_of_product_representation k hp g _ v hv c hRep
  intro n
  obtain ⟨z, hz⟩ := hg n
  exact ⟨(z : ℚ), by simpa using hz⟩

end ZInQ.Contrib.HeckePrimeRationality.AllLevelHeckeFromProducts
