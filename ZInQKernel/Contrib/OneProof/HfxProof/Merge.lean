import ZInQKernel.Contrib.OneProof.HfxProof.Sg

/-!
# hfx-proof: merging double cosets with elements of `K_2^×`

Task hfx-proof. If `α ∈ K^×` (commuting with `τ(√−n)`), `ρ ∈ B^×` integral of norm `1` or `2`, and
`β_t α ∈ ρ β_{t'} (1 + 4O_{B,2})` at `2`, then `twoRep t ∈ B^× twoRep t' H` (`twoRep_mem_DC_of`): the
element `(ρ twoRep t')⁻¹ twoRep t ιAt(α)` lies in `1 + 4Ô_B ⊂ R̂_n^×`, and `ιAt(α) ∈ K_{n,2}^×`. The
condition at `2` follows from an integer congruence `Ā(B − A) ≡ 0 (mod 4·2^b)` (`local_merge_cond`).
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The explicit inverse `nrd⁻¹ · conj` in `ℍ[ℚ_p]`. -/
abbrev qinv {p : ℕ} [Fact p.Prime] (A : ℍ[ℚ_[p]]) : ℍ[ℚ_[p]] := (Quaternion.normSq A)⁻¹ • star A

theorem qinv_mul_self {p : ℕ} [Fact p.Prime] {A : ℍ[ℚ_[p]]} (hA : Quaternion.normSq A ≠ 0) :
    qinv A * A = 1 := by
  rw [qinv, smul_mul_assoc, Quaternion.star_mul_self, ← Quaternion.coe_mul_eq_smul,
    ← Quaternion.coe_mul, inv_mul_cancel₀ hA, Quaternion.coe_one]

theorem mul_qinv_self {p : ℕ} [Fact p.Prime] {A : ℍ[ℚ_[p]]} (hA : Quaternion.normSq A ≠ 0) :
    A * qinv A = 1 := by
  rw [qinv, mul_smul_comm, Quaternion.self_mul_star, ← Quaternion.coe_mul_eq_smul,
    ← Quaternion.coe_mul, inv_mul_cancel₀ hA, Quaternion.coe_one]

/-- **The merge lemma.** -/
theorem twoRep_mem_DC_of {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : IsPlaceTwo v) {t t' : T8} {α ρ : ℍ[ℚ]} (hα0 : α ≠ 0)
    (hαc : α * τ (sqrtNeg n) = τ (sqrtNeg n) * α) (hρ0 : ρ ≠ 0) (hρZ : IsHurZ ρ)
    (hρn : Quaternion.normSq ρ = 1 ∨ Quaternion.normSq ρ = 2)
    (hloc : IsHur (Zp (Pw v : ℕ)) (((1 / 4 : ℚ) : ℚ_[Pw v]) •
        (qinv (qp (Pw v : ℕ) (ρ * twoRepQ t')) * qp (Pw v : ℕ) (twoRepQ t * α) - 1)) ∧
      IsHur (Zp (Pw v : ℕ)) (((1 / 4 : ℚ) : ℚ_[Pw v]) •
        (qinv (qp (Pw v : ℕ) (twoRepQ t * α)) * qp (Pw v : ℕ) (ρ * twoRepQ t') - 1))) :
    twoRep v t ∈ DC n τ (twoRep v t') := by
  set αU : ℍ[AQ]ˣ := ιAtU v α hα0
  have hαK : αU ∈ HgrpN n τ := by
    refine Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (Or.inr ⟨?_, ?_⟩)))
    · show ιAt v α * qι (τ (sqrtNeg n)) = qι (τ (sqrtNeg n)) * ιAt v α
      apply piQ_injective; intro w
      rw [map_mul, map_mul, piQ_qι]
      by_cases hw : w = v
      · subst hw; rw [piQ_ιAt_self, ← map_mul, ← map_mul, hαc]
      · rw [piQ_ιAt_ne hw, one_mul, mul_one]
    · intro w hw
      have hwv : w ≠ v := fun h => hw (h ▸ hv)
      have h1 := piQ_ιAt_ne hwv α
      have key : ∀ (a : AQ) (r : ℚ_[Pw w]), ev w a = r → a w = (pe w).symm r := by
        intro a r h; rw [← h, ev_apply, RingEquiv.symm_apply_apply]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := congrArg (·.re) h1; simp only [piQ, qmap_re] at this
        show (ιAt v α).re w = 1
        rw [key _ _ this]; simp
      · have := congrArg (·.imI) h1; simp only [piQ, qmap_imI] at this
        show (ιAt v α).imI w = 0
        rw [key _ _ this]; simp
      · have := congrArg (·.imJ) h1; simp only [piQ, qmap_imJ] at this
        show (ιAt v α).imJ w = 0
        rw [key _ _ this]; simp
      · have := congrArg (·.imK) h1; simp only [piQ, qmap_imK] at this
        show (ιAt v α).imK w = 0
        rw [key _ _ this]; simp
  set a : ℍ[AQ]ˣ := qιU ρ hρ0 * twoRepU v t'
  set W : ℍ[AQ]ˣ := a⁻¹ * (twoRepU v t * αU)
  have hac : (a : ℍ[AQ]) = qι ρ * twoRep v t' := rfl
  have hbc : ((twoRepU v t * αU : ℍ[AQ]ˣ) : ℍ[AQ]) = twoRep v t * ιAt v α := rfl
  have hρodd : ∀ w, w ≠ v → ‖Quaternion.normSq (qp (Pw w : ℕ) ρ)‖ = 1 := by
    intro w hw
    rw [normSq_qp]
    have hne := Pw_ne_two hv hw
    rcases hρn with h | h <;> rw [h]
    · simp
    · push_cast
      have : ‖((2 : ℕ) : ℚ_[Pw w])‖ = 1 := by
        rw [Padic.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes (Pw w).2 Nat.prime_two).mpr hne
      exact_mod_cast this
  have hWc : (W : ℍ[AQ]) = ((a⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) * (twoRep v t * ιAt v α) := rfl
  have hWic : ((W⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) =
      (((twoRepU v t * αU)⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) * (a : ℍ[AQ]) := by
    simp only [W, mul_inv_rev, inv_inv, Units.val_mul]
  have e1 : piQ v (a : ℍ[AQ]) = qp (Pw v : ℕ) (ρ * twoRepQ t') := by
    rw [hac, map_mul, piQ_qι, twoRep, piQ_ιAt_self, map_mul]
  have e2 : piQ v ((twoRepU v t * αU : ℍ[AQ]ˣ) : ℍ[AQ]) = qp (Pw v : ℕ) (twoRepQ t * α) := by
    rw [hbc, map_mul, twoRep, piQ_ιAt_self, piQ_ιAt_self, map_mul]
  have e1' : ∀ w, w ≠ v → piQ w (a : ℍ[AQ]) = qp (Pw w : ℕ) ρ := by
    intro w hw; rw [hac, map_mul, piQ_qι, twoRep, piQ_ιAt_ne hw, mul_one]
  have e2' : ∀ w, w ≠ v → piQ w ((twoRepU v t * αU : ℍ[AQ]ˣ) : ℍ[AQ]) = 1 := by
    intro w hw; rw [hbc, map_mul, twoRep, piQ_ιAt_ne hw, piQ_ιAt_ne hw, mul_one]
  have hW1 : LH ((1 / 4 : ℚ) • ((W : ℍ[AQ]) - 1)) := by
    intro w
    rw [piQ_qsmul, map_sub, map_one, Units.val_mul, map_mul, piQ_unit_inv]
    by_cases hw : w = v
    · subst hw; rw [e1, e2]; exact hloc.1
    · rw [e1' w hw, e2' w hw, mul_one]
      refine IsHur.smul (quarter_mem (Pw_ne_two hv hw)) (IsHur.sub ?_ isHur_one)
      exact isHur_inv_star (isHur_qp_hurZ' hρZ) (hρodd w hw)
  have hW2 : LH ((1 / 4 : ℚ) • (((W⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) - 1)) := by
    intro w
    rw [piQ_qsmul, map_sub, map_one, hWic, map_mul, piQ_unit_inv]
    by_cases hw : w = v
    · subst hw; rw [e1, e2]; exact hloc.2
    · rw [e1' w hw, e2' w hw]
      simp only [map_one, star_one, inv_one, one_smul, one_mul]
      exact IsHur.smul (quarter_mem (Pw_ne_two hv hw)) (IsHur.sub (isHur_qp_hurZ' hρZ) isHur_one)
  have hWH : W ∈ HgrpN n τ := mem_HgrpN_of τ hW1 hW2
  refine ⟨ρ, hρ0, W * αU⁻¹, Subgroup.mul_mem _ hWH (Subgroup.inv_mem _ hαK), ?_⟩
  have hu : twoRepU v t = a * (W * αU⁻¹) := by simp only [W]; group
  rw [← hac, ← Units.val_mul, ← hu]
  rfl

/-! ## The condition at `2` from an integer congruence -/

theorem hurZ_sub {R : Type*} [Field R] [CharZero R] (a b : H4 ℤ) :
    (hurZ a : ℍ[R]) - hurZ b = hurZ ⟨a.a0 - b.a0, a.a1 - b.a1, a.a2 - b.a2, a.a3 - b.a3⟩ := by
  apply hc_injective; rw [hc_sub, hc_hurZ, hc_hurZ, hc_hurZ]; ext <;> simp [mapH]

theorem qinv_mul_qinv {p : ℕ} [Fact p.Prime] (x y : ℍ[ℚ_[p]]) : qinv (x * y) = qinv y * qinv x := by
  simp only [qinv, star_mul, map_mul, smul_mul_smul, mul_inv]
  rw [mul_comm (Quaternion.normSq y)⁻¹]

theorem norm_normSq_one_add_four {p : ℕ} [Fact p.Prime] (hp : p = 2) {w : ℍ[ℚ_[p]]}
    (hw : IsHur (Zp p) w) : ‖Quaternion.normSq (1 + (4 : ℚ_[p]) • w)‖ = 1 := by
  subst hp
  have h := norm_normSq_add_smul_sub_lt (p := 2) (a := 1) (b := (2 : ℚ_[2]) • w) isHur_one
    (hw.smul (by simpa [mem_Zp] using Padic.norm_int_le_one (p := 2) 2))
  rw [smul_smul, show ((2 : ℕ) : ℚ_[2]) * 2 = 4 by norm_num, map_one] at h
  have e : Quaternion.normSq (1 + (4 : ℚ_[2]) • w) = 1 + (Quaternion.normSq (1 + (4 : ℚ_[2]) • w) - 1) := by ring
  rw [e]
  have h1 : ‖(1 : ℚ_[2])‖ = 1 := norm_one
  rw [← h1]
  exact Padic.add_eq_max_of_ne (by rw [h1]; exact ne_of_gt h) |>.trans (max_eq_left (le_of_lt (h1 ▸ h)))

/-- **The congruence criterion.** -/
theorem local_merge_cond {p : ℕ} [Fact p.Prime] (hp : p = 2) (A B C : H4 ℤ) (b : ℕ) (oA : ℤ)
    (hoA : Odd oA) (hnA : nrdH A = 2 ^ b * oA)
    (hC : mulH (starH A) ⟨B.a0 - A.a0, B.a1 - A.a1, B.a2 - A.a2, B.a3 - A.a3⟩ = smulH (4 * 2 ^ b) C) :
    IsHur (Zp p) (((1 / 4 : ℚ) : ℚ_[p]) • (qinv (qp p (hurZ A)) * qp p (hurZ B) - 1)) ∧
      IsHur (Zp p) (((1 / 4 : ℚ) : ℚ_[p]) • (qinv (qp p (hurZ B)) * qp p (hurZ A) - 1)) := by
  rw [qp_hurZ, qp_hurZ]
  have hnA' : Quaternion.normSq (hurZ A : ℍ[ℚ_[p]]) = (2 : ℚ_[p]) ^ b * oA := by
    rw [normSq_hurZ, hnA]; push_cast; rfl
  have hoA0 : (oA : ℚ_[p]) ≠ 0 := by
    intro h; have : oA = 0 := by exact_mod_cast h
    obtain ⟨r, hr⟩ := hoA; omega
  have hA0 : Quaternion.normSq (hurZ A : ℍ[ℚ_[p]]) ≠ 0 := by
    rw [hnA']; exact mul_ne_zero (pow_ne_zero _ (by subst hp; norm_num)) hoA0
  -- `A⁻¹ B = 1 + 4 w` with `w = oA⁻¹ C`
  set w : ℍ[ℚ_[p]] := (oA : ℚ_[p])⁻¹ • hurZ C with hwdef
  have hoAu : ‖(oA : ℚ_[p])‖ = 1 := by subst hp; exact norm_odd_int hoA
  have hCH : IsHur (Zp p) (hurZ C : ℍ[ℚ_[p]]) := by
    have := isHur_qp_hurZ (p := p) C; rwa [qp_hurZ] at this
  have hwH : IsHur (Zp p) w := IsHur.smul (by rw [mem_Zp, norm_inv, hoAu, inv_one]) hCH
  have hAB : qinv (hurZ A : ℍ[ℚ_[p]]) * hurZ B = 1 + (4 : ℚ_[p]) • w := by
    have h1 : qinv (hurZ A : ℍ[ℚ_[p]]) * hurZ B - 1 = qinv (hurZ A) * (hurZ B - hurZ A) := by
      rw [mul_sub, qinv_mul_self hA0]
    have h2 : star (hurZ A : ℍ[ℚ_[p]]) * (hurZ B - hurZ A) = (4 * 2 ^ b : ℚ_[p]) • hurZ C := by
      rw [star_hurZ, hurZ_sub, ← hurZ_mulH, hC, hurZ_smulH]; push_cast; ring_nf
    have h3 : qinv (hurZ A : ℍ[ℚ_[p]]) * hurZ B - 1 = (4 : ℚ_[p]) • w := by
      rw [h1, qinv, smul_mul_assoc, h2, hnA', hwdef, smul_smul, smul_smul]
      congr 1
      have h2b : (2 : ℚ_[p]) ^ b ≠ 0 := pow_ne_zero _ (by subst hp; norm_num)
      field_simp
    rw [← h3]; abel
  constructor
  · rw [hAB, add_sub_cancel_left, smul_smul,
      show ((1 / 4 : ℚ) : ℚ_[p]) * 4 = 1 by push_cast; norm_num, one_smul]
    exact hwH
  · -- `B = A (1 + 4w)`, so `B⁻¹ A = (1 + 4w)⁻¹`
    have hB : (hurZ B : ℍ[ℚ_[p]]) = hurZ A * (1 + (4 : ℚ_[p]) • w) := by
      rw [← hAB, ← mul_assoc, mul_qinv_self hA0, one_mul]
    have hu1 := norm_normSq_one_add_four hp hwH
    have hu0 : Quaternion.normSq (1 + (4 : ℚ_[p]) • w) ≠ 0 := normSq_ne_zero_of hu1
    rw [hB, qinv_mul_qinv, mul_assoc, qinv_mul_self hA0, mul_one]
    have e : qinv (1 + (4 : ℚ_[p]) • w) - 1 = -((4 : ℚ_[p]) • (qinv (1 + (4 : ℚ_[p]) • w) * w)) := by
      have := qinv_mul_self hu0
      rw [mul_add, mul_one, mul_smul_comm] at this
      rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, this, sub_self]
    rw [e, smul_neg, smul_smul]
    have h4 : ((1 / 4 : ℚ) : ℚ_[p]) * 4 = 1 := by push_cast; norm_num
    rw [h4, one_smul]
    have hI : IsHur (Zp p) (qinv (1 + (4 : ℚ_[p]) • w)) :=
      isHur_inv_star (isHur_one.add (hwH.smul four_mem)) hu1
    have := (hI.mul hwH).smul ((Zp p).neg_mem (Zp p).one_mem)
    rwa [neg_smul, one_smul] at this

end ZInQ.Contrib.HfxProof
