import ZInQKernel.Contrib.OneProof.BShTracesCosets
import ZInQKernel.Contrib.OneProof.BShStandardWeber
import ZInQKernel.Contrib.OneProof.HeckePin

/-! ON THE SPOT (provenance (c)): enumerate the cosets in the upper triangular
and horizontal superlattices, and compare the two coordinates after rescaling
the horizontal one. -/

noncomputable section

namespace BShTraces

open PeriodPair T5Glue UpperHalfPlane AfTateLam
open scoped MatrixGroups

private theorem rem_lt (p : ℕ) (hp : 0 < p) (n : ℤ) : (n % (p : ℤ)).toNat < p := by
  have hpos : (0 : ℤ) < p := by exact_mod_cast hp
  have hnon := Int.emod_nonneg n hpos.ne'
  have hlt := Int.emod_lt_of_pos n hpos
  omega

private def intBlocks (p : ℕ) (hp : 0 < p) : Fin p × ℤ ≃ ℤ where
  toFun x := (p : ℤ) * x.2 + (x.1.val : ℤ)
  invFun n := (⟨(n % (p : ℤ)).toNat, rem_lt p hp n⟩, n / (p : ℤ))
  left_inv := by
    rintro ⟨i, n⟩
    have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    have hi : (i.val : ℤ) < p := by exact_mod_cast i.isLt
    ext
    · change (((p : ℤ) * n + (i.val : ℤ)) % (p : ℤ)).toNat = i.val
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) hi]
      simp
    · change ((p : ℤ) * n + (i.val : ℤ)) / (p : ℤ) = n
      rw [Int.mul_add_ediv_left _ _ hp', Int.ediv_eq_zero_of_lt (by positivity) hi, add_zero]
  right_inv n := by
    have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    change (p : ℤ) * (n / (p : ℤ)) + ((n % (p : ℤ)).toNat : ℤ) = n
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hp'), Int.mul_ediv_add_emod]

private def coordinateEquiv {L M : PeriodPair} {ι : Type*}
    (f : ι × (ℤ × ℤ) ≃ ℤ × ℤ) : ι × L.lattice ≃ M.lattice :=
  ((Equiv.prodCongr (Equiv.refl ι) L.latticeEquivProd.toEquiv).trans f).trans
    M.latticeEquivProd.symm.toEquiv

private theorem coordinateEquiv_apply {L M : PeriodPair} {ι : Type*}
    (f : ι × (ℤ × ℤ) ≃ ℤ × ℤ) (i : ι) (m n : ℤ) :
    (coordinateEquiv (L := L) (M := M) f (i, L.latticeEquivProd.symm (m, n)) : ℂ) =
      (f (i, m, n)).1 * M.ω₁ + (f (i, m, n)).2 * M.ω₂ := by
  simp [coordinateEquiv, latticeEquiv_symm_apply]

private def triCoords (p : ℕ) (hp : 0 < p) (j : Fin p) : Fin p × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun x := (x.2.1 - x.2.2 * j.val, intBlocks p hp (x.1, x.2.2))
  invFun x := ((intBlocks p hp).symm x.2 |>.1,
    x.1 + ((intBlocks p hp).symm x.2).2 * j.val, ((intBlocks p hp).symm x.2).2)
  left_inv := by rintro ⟨i, m, n⟩; simp
  right_inv := by rintro ⟨m, n⟩; simp

/-- The (p) cosets of the old lattice in the lattice of ((τ+j)/p). -/
def triangularCosets (p : ℕ) (hp : 0 < p) (j : Fin p) (τ : ℍ) :
    CosetEnumeration (pp τ) (pp (shiftDiv p j τ)) (Fin p) where
  representative i := -(i.val : ℂ) * (↑(shiftDiv p j τ) : ℂ)
  equiv := coordinateEquiv (triCoords p hp j)
  coe_equiv i l := by
    obtain ⟨⟨m, n⟩, rfl⟩ := (pp τ).latticeEquivProd.symm.surjective l
    rw [coordinateEquiv_apply, latticeEquiv_symm_apply]
    unfold triCoords intBlocks
    simp only [Equiv.coe_fn_mk, pp, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [HeckePin.coe_shiftDiv _ _ hp]
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    field_simp
    ring

private def horizCoords (p : ℕ) (hp : 0 < p) : Fin p × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun x := (intBlocks p hp (x.1, x.2.1), x.2.2)
  invFun x := (((intBlocks p hp).symm x.1).1, ((intBlocks p hp).symm x.1).2, x.2)
  left_inv := by rintro ⟨i, m, n⟩; simp
  right_inv := by rintro ⟨m, n⟩; simp

/-- The lattice obtained by adjoining (1/p). The definition retains
the homothety with the period pair of (pτ). -/
def horizontal (p : ℕ) (hp : 0 < p) (τ : ℍ) : PeriodPair :=
  ppScale (p : ℂ)⁻¹ (inv_ne_zero (by exact_mod_cast hp.ne')) (mulNat p τ)

theorem horizontal_periods (p : ℕ) (hp : 0 < p) (τ : ℍ) :
    (horizontal p hp τ).ω₁ = (p : ℂ)⁻¹ ∧ (horizontal p hp τ).ω₂ = τ := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  refine ⟨rfl, ?_⟩
  change (p : ℂ)⁻¹ * (↑(mulNat p τ) : ℂ) = τ
  rw [HeckePin.coe_mulNat _ hp, inv_mul_cancel_left₀ hp']

/-- The (p) horizontal cosets, including exactly one zero representative. -/
def horizontalCosets (p : ℕ) (hp : 0 < p) (τ : ℍ) :
    CosetEnumeration (pp τ) (horizontal p hp τ) (Fin p) where
  representative i := -(i.val : ℂ) / p
  equiv := coordinateEquiv (horizCoords p hp)
  coe_equiv i l := by
    obtain ⟨⟨m, n⟩, rfl⟩ := (pp τ).latticeEquivProd.symm.surjective l
    rw [coordinateEquiv_apply, latticeEquiv_symm_apply,
      (horizontal_periods p hp τ).1, (horizontal_periods p hp τ).2]
    unfold horizCoords intBlocks
    simp only [Equiv.coe_fn_mk, pp, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    field_simp
    ring

/-- The two coordinates of the horizontal lattice with the original mark
are those of the good-prime branch, with the specified diamond correction. -/
theorem horizontal_diamond (p : ℕ) (hp : 0 < p) (τ : ℍ) (N : ℕ)
    (g : SL(2, ℤ)) (hg : (N : ℤ) ∣ g 1 0) (hd : (g 1 1 : ZMod N) = (p : ZMod N)) :
    (jL (horizontal p hp τ), weber (horizontal p hp τ) (1 / (N : ℂ))) =
      (jL (pp (g • mulNat p τ)), weber (pp (g • mulNat p τ)) (1 / (N : ℂ))) := by
  have hs : IsScale (horizontal p hp τ) (pp (mulNat p τ)) (p : ℂ)⁻¹ :=
    ppScale_isScale _ _ _
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hd' : (g 1 1 : ZMod N) = ((p : ℤ) : ZMod N) := by simpa using hd
  apply Prod.ext
  · exact hs.jL.trans (BShStandard.j_diamond g (mulNat p τ)).symm
  · change weber (horizontal p hp τ) (1 / (N : ℂ)) = _
    rw [BShStandard.weber_diamond g hg hd', Int.cast_natCast,
      ← hs.weber, inv_mul_cancel_left₀ hp']

/-- For a real point of the plane, only the integral real periods can
contribute to membership in the lattice `ℤ + ℤτ`. -/
theorem mem_pp_of_im_zero_iff (τ : ℍ) {z : ℂ} (hz : z.im = 0) :
    z ∈ (pp τ).lattice ↔ ∃ n : ℤ, z = (n : ℂ) := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, e⟩
    have hi := congrArg Complex.im e
    simp only [pp, mul_one, Complex.add_im, Complex.intCast_im, Complex.mul_im,
      Complex.intCast_re, zero_mul, add_zero, zero_add, hz] at hi
    have hn : (n : ℝ) = 0 := (mul_eq_zero.mp hi).resolve_right τ.im_pos.ne'
    have h : n = 0 := by exact_mod_cast hn
    exact ⟨m, by simpa [h, pp] using e.symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, 0, by simp [pp]⟩

/-- The triangular branch retains the full order (N) of the mark. -/
theorem triangular_mark_order (p i : ℕ) (τ : ℍ) {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (k : ℂ) / N ∈ (pp (shiftDiv p i τ)).lattice ↔ N ∣ k := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hreal : ((k : ℂ) / N).im = 0 := by
    simp [Complex.div_im]
  rw [mem_pp_of_im_zero_iff _ hreal, ← Int.natCast_dvd_natCast]
  constructor
  · rintro ⟨n, e⟩
    exact ⟨n, by exact_mod_cast (div_eq_iff hN').mp e |>.trans (mul_comm _ _)⟩
  · rintro ⟨n, e⟩
    refine ⟨n, (div_eq_iff hN').mpr ?_⟩
    exact_mod_cast e.trans (mul_comm _ _)

/-- In the horizontal branch the (k)-fold multiple of the mark vanishes
exactly when (N) divides (pk). This is the level test for this branch. -/
theorem horizontal_mark_order (p : ℕ) (hp : 0 < p) (τ : ℍ) {N : ℕ} (hN : 0 < N)
    (k : ℕ) : (k : ℂ) / N ∈ (horizontal p hp τ).lattice ↔ N ∣ p * k := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : IsScale (horizontal p hp τ) (pp (mulNat p τ)) (p : ℂ)⁻¹ :=
    ppScale_isScale _ _ _
  rw [hs.mem_iff, inv_inv, ← mul_div_assoc, ← Nat.cast_mul]
  have hreal : (((p * k : ℕ) : ℂ) / N).im = 0 := by
    simp [Complex.div_im]
  rw [mem_pp_of_im_zero_iff _ hreal, ← Int.natCast_dvd_natCast]
  constructor
  · rintro ⟨n, e⟩
    have h := (div_eq_iff hN').mp e
    exact ⟨n, by exact_mod_cast h.trans (mul_comm _ _)⟩
  · rintro ⟨n, e⟩
    refine ⟨n, (div_eq_iff hN').mpr ?_⟩
    exact_mod_cast e.trans (mul_comm _ _)

#print axioms rem_lt
#print axioms coordinateEquiv_apply
#print axioms horizontal_periods
#print axioms horizontal_diamond
#print axioms mem_pp_of_im_zero_iff
#print axioms triangular_mark_order
#print axioms horizontal_mark_order

end BShTraces
