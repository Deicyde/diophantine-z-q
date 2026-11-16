import ZInQKernel.Contrib.OneProof.DSThm965Weak
import ZInQKernel.Contrib.T25.Bridge
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Eigenform
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Eigenvector

noncomputable section

namespace DSCoeffExt

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
open ZInQ.Contrib.G9.PkgI4 (CF coeff HasNebentypus IsNormalizedEigenform)

variable {N : ℕ} {k : ℤ}

/-- Diamond–Shurman Def. 5.8.1: a normalized eigenform in `S_k(N, χ)`. -/
def IsNormalizedEigenformDS [NeZero N] (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∃ F : HeckeRing.GL2.Eigenform N k, F.toCuspForm = f ∧ F.χ = MulChar.toUnitHom χ ∧ coeff f 1 = 1

theorem ofUnitHom_toUnitHom (χ : DirichletCharacter ℂ N) :
    (MulChar.ofUnitHom (MulChar.toUnitHom χ) : DirichletCharacter ℂ N) = χ := by
  rw [MulChar.ofUnitHom_eq]
  exact MulChar.equivToUnitHom.symm_apply_apply χ

theorem ne_zero_of_coeff_one {f : CF N k} (h : coeff f 1 = 1) : f ≠ 0 := by
  rintro rfl
  simp only [coeff, FunLike.coe_zero, qExpansion_zero, map_zero] at h
  exact zero_ne_one h

/-- The `T_p`-eigenrelation at every prime `p`, the primes `p ∣ N` (`U_p`) included, from the kernel's
coefficient form. -/
theorem heckeTCuspNat_eq_coeff_smul_all [NeZero N] {g : CF N k} {χ : DirichletCharacter ℂ N}
    (hg : IsNormalizedEigenform g χ) {p : ℕ} (hp : p.Prime) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) g = coeff g p • g := by
  rw [heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom hp
    (T25.mem_cuspFormCharSpace_of_hasNebentypus hg.1), ofUnitHom_toUnitHom]
  intro m
  change coeff g (p * m) = coeff g p * coeff g m - _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : coeff g 0 = 0 := T25.coeff_zero g
    simp only [mul_zero, Nat.zero_div, dvd_zero, ↓reduceIte]
    change coeff g 0 = coeff g p * coeff g 0 - _ * coeff g 0
    rw [h0]; ring
  have key := hg.2.2 p m hp.pos hm
  by_cases hpm : p ∣ m
  · obtain ⟨m', rfl⟩ := hpm
    have e1 : p * (p * m') / 1 ^ 2 = p * (p * m') := by simp
    have e2 : p * (p * m') / p ^ 2 = m' := by
      rw [← mul_assoc, ← pow_two, Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)]
    have e3 : p * m' / p = m' := Nat.mul_div_cancel_left _ hp.pos
    rw [Nat.gcd_eq_left (dvd_mul_right p m'), hp.divisors, Finset.sum_pair hp.one_lt.ne, e1,
      e2] at key
    simp only [dvd_mul_right, ↓reduceIte, e3]
    simp only [Nat.cast_one, map_one, one_zpow, one_mul] at key
    change _ = _ - _ * _ * coeff g m'
    linear_combination -key
  · have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.divisors_one, Finset.sum_singleton] at key
    simp only [Nat.cast_one, map_one, one_zpow, one_mul, one_pow, Nat.div_one] at key
    simp only [hpm, ↓reduceIte, sub_zero]
    linear_combination -key

/-- **Coefficient form ⇒ Diamond–Shurman's definition.** -/
theorem isNormalizedEigenformDS_of [NeZero N] {g : CF N k} {χ : DirichletCharacter ℂ N}
    (hg : IsNormalizedEigenform g χ) : IsNormalizedEigenformDS g χ := by
  have hχ := T25.mem_cuspFormCharSpace_of_hasNebentypus hg.1
  refine ⟨Eigenform.ofForallPrime hχ (ne_zero_of_coeff_one hg.2.1)
    (fun p hp => ⟨coeff g p, ?_⟩), rfl, rfl, hg.2.1⟩
  apply Subtype.ext
  rw [coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k _ hp]
  exact heckeTCuspNat_eq_coeff_smul_all hg hp

/-- **Diamond–Shurman's definition ⇒ coefficient form.** -/
theorem isNormalizedEigenform_of_DS [NeZero N] {g : CF N k} {χ : DirichletCharacter ℂ N}
    (hg : IsNormalizedEigenformDS g χ) : IsNormalizedEigenform g χ := by
  obtain ⟨F, rfl, hχ, h1⟩ := hg
  have hneb := T25.hasNebentypus_of_mem_cuspFormCharSpace F.mem_charSpace
  rw [hχ, ofUnitHom_toUnitHom] at hneb
  refine ⟨hneb, h1, fun m n _ hn => ?_⟩
  lift n to ℕ+ using hn
  have h := qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 (N := N) (k := k)
    (χ := F.χ) (n := n) n.ne_zero ⟨F.toCuspForm, F.mem_charSpace⟩ m
  rw [F.isEigen n, Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _),
    PowerSeries.coeff_smul, smul_eq_mul, ← F.qExpansion_coeff_eq_eigenvalue h1 n] at h
  have hχ' : χ = MulChar.ofUnitHom F.χ := by rw [hχ, ofUnitHom_toUnitHom]
  rw [hχ', mul_comm]
  exact h

theorem isNormalizedEigenform_iff_DS [NeZero N] {g : CF N k} {χ : DirichletCharacter ℂ N} :
    IsNormalizedEigenform g χ ↔ IsNormalizedEigenformDS g χ :=
  ⟨isNormalizedEigenformDS_of, isNormalizedEigenform_of_DS⟩

end DSCoeffExt
#print axioms DSCoeffExt.isNormalizedEigenform_iff_DS
