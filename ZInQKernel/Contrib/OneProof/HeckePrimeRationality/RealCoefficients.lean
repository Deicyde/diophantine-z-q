import ZInQKernel.Contrib.OneProof.HeckePrimeRationality
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Conjugate

/-!
# Complex conjugation and non-sign diamond action

This file proves an unconditional all-level conjugation identity for the
actual diamond operator, and preservation of real Fourier coefficients.
Real coefficients are NOT rational coefficients. These results do not
prove the full `CoeffRational.HeckePrimeIntegralToRational` leaf.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped ModularForm MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- Conjugation commutes with every actual diamond class, not merely ±1.
The proof uses representatives with unchanged lower-right labels. -/
theorem conjugate_diamond_commutes (d : (ZMod N)ˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.conj (TauCeti.Gamma1_map_le_conjAct_inv_J N) (diamondOpCusp k d g) =
      diamondOpCusp k d (CuspForm.conj (TauCeti.Gamma1_map_le_conjAct_inv_J N) g) := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  let γ' : ↥(Gamma0 N) := ⟨conjJ (γ : SL(2, ℤ)), TauCeti.conjJ_mem_Gamma0 γ.2⟩
  have hγ' : (Gamma0Map N).toHomUnits γ' = d :=
    (TauCeti.Gamma0Map_conjJ γ).trans hγ
  apply DFunLike.coe_injective
  rw [CuspForm.coe_conj, coe_diamondOpCusp k d γ hγ,
    coe_diamondOpCusp k d γ' hγ', CuspForm.coe_conj]
  have hγJ : mapGL ℝ (γ : SL(2, ℤ)) * J = J * mapGL ℝ (conjJ (γ : SL(2, ℤ))) := by
    rw [← J_mul_mapGL_mul_J, ← mul_assoc, ← mul_assoc, ← sq, J_sq, one_mul]
  rw [← SlashAction.slash_mul, hγJ, SlashAction.slash_mul]

/-- A real-coefficient predicate is explicit about the coefficient field.
It is strictly weaker than rationality, and is not substituted for it. -/
def HasRealQExpansion (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∀ n : ℕ, ∃ r : ℝ, (qExpansion 1 g).coeff n = (r : ℂ)

private theorem exists_real_of_conjugation_fixed (c : ℂ)
    (hc : starRingEnd ℂ c = c) : ∃ r : ℝ, c = (r : ℂ) := by
  have him := congrArg Complex.im hc
  change -c.im = c.im at him
  have hz : c.im = 0 := by linarith
  refine ⟨c.re, ?_⟩
  apply Complex.ext
  · rfl
  · simpa using hz

/-- A cusp form with real coefficients equals its actual conjugate form,
by q-expansion injectivity, not by pointwise Galois conjugation. -/
theorem conjugate_eq_self_of_real_qExpansion
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : HasRealQExpansion g) :
    CuspForm.conj (TauCeti.Gamma1_map_le_conjAct_inv_J N) g = g := by
  apply CuspForm.qExpansion_injective one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)
  dsimp only
  rw [CuspForm.qExpansion_conj one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)]
  ext n
  rw [PowerSeries.coeff_map]
  obtain ⟨r, hr⟩ := hg n
  rw [hr]
  simp

/-- Every diamond class preserves real Fourier coefficients. No rationality
or arithmetic q-expansion bridge is smuggled into this theorem. -/
theorem diamond_preserves_real_qExpansion (d : (ZMod N)ˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : HasRealQExpansion g) :
    HasRealQExpansion (diamondOpCusp k d g) := by
  have hfix : CuspForm.conj (TauCeti.Gamma1_map_le_conjAct_inv_J N)
      (diamondOpCusp k d g) = diamondOpCusp k d g := by
    rw [conjugate_diamond_commutes, conjugate_eq_self_of_real_qExpansion g hg]
  have hq := CuspForm.qExpansion_conj one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (TauCeti.Gamma1_map_le_conjAct_inv_J N) (diamondOpCusp k d g)
  rw [hfix] at hq
  intro n
  have hn := congrArg (fun s : PowerSeries ℂ => s.coeff n) hq
  rw [PowerSeries.coeff_map] at hn
  exact exists_real_of_conjugation_fixed _ hn.symm

/-- The actual prime-Hecke operator preserves real coefficients at every
nonzero level and every good prime, with the recurrence's guard retained. -/
theorem hecke_preserves_real_qExpansion {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : HasRealQExpansion g) :
    HasRealQExpansion (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g) := by
  have hcop : Nat.Coprime p N := (hp.coprime_iff_not_dvd).mpr hpN
  have hD := diamond_preserves_real_qExpansion (ZMod.unitOfCoprime p hcop) g hg
  intro m
  rw [qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime k hp g m]
  obtain ⟨r₁, hr₁⟩ := hg (p * m)
  rw [hr₁]
  split_ifs with hpm
  · rw [diamondOpCuspNat_of_coprime k hcop]
    obtain ⟨r₂, hr₂⟩ := hD (m / p)
    refine ⟨r₁ + (p : ℝ) ^ (k - 1) * r₂, ?_⟩
    rw [hr₂]
    push_cast
    ring
  · exact ⟨r₁, by simp⟩

/-- The necessary real-coefficient consequence for the leaf's integral
input. This is NOT the required rational-coefficient conclusion. -/
theorem integral_input_hecke_has_real_qExpansion {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    HasRealQExpansion (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g) := by
  apply hecke_preserves_real_qExpansion hp hpN g
  intro n
  obtain ⟨z, hz⟩ := hg n
  exact ⟨(z : ℝ), by simpa using hz⟩

end ZInQ.Contrib.HeckePrimeRationality
