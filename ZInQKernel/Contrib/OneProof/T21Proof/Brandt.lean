import ZInQKernel.Contrib.OneProof.T21Proof.K2

/-!
# t21-proof: the double coset of `1` in `B^× \ B̂^× / ℚ̂^× U_3`

Task t21-proof. For an admissible `τ` (signs `s`) and the place `v` above `2`:
* `Sg v s`: the subgroup of `B̂^×` of elements lying in `ℚ_p^× O_{B,p}^×` at odd places and in
  `ℚ_2^× R_2^×` at `v`;
* `H τ = ⟨U_3, ℚ̂^×⟩ ≤ Sg v s` (`H_le_Sg`): the generators `R̂_3^×` (via `tauHat_integral`),
  `K_{3,2}^×` (via `loc2OK_of_commute`) and the centre;
* `twoRep_not_mem`: for the 6 classes `t ∉ {0, t*}`, `twoRep v t ∉ B^× H`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open ZInQ.Contrib.TYZDecomp.H29Split IsDedekindDomain NumberField
open scoped Quaternion FiniteAdeleExtension
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ## Local lemmas -/

theorem eq_of_mul_eq_one' {p : ℕ} [Fact p.Prime] {c : ℚ_[p]} {u z : ℍ[ℚ_[p]]} (hc : c ≠ 0)
    (hn : Quaternion.normSq u ≠ 0) (h : z * (c • u) = 1) :
    z = c⁻¹ • ((Quaternion.normSq u)⁻¹ • star u) := by
  have h1 : (z * (c • u)) * star u = star u := by rw [h, one_mul]
  have h2 : (z * (c • u)) * star u = (c * Quaternion.normSq u) • z := by
    rw [mul_assoc, smul_mul_assoc, Quaternion.self_mul_star, ← Quaternion.coe_mul_eq_smul,
      ← Quaternion.coe_mul, Quaternion.mul_coe_eq_smul]
  rw [h2] at h1
  rw [← h1, smul_smul, smul_smul, ← mul_assoc, mul_comm c⁻¹, mul_assoc]
  have : c⁻¹ * (c * Quaternion.normSq u) = Quaternion.normSq u := by field_simp
  rw [mul_assoc, this, inv_mul_cancel₀ hn, one_smul]

theorem LocOK.of_mul_eq_one' {p : ℕ} [Fact p.Prime] {y z : ℍ[ℚ_[p]]} (hy : LocOK y)
    (h : z * y = 1) : LocOK z := by
  obtain ⟨c, hc, u, rfl, hu, hn⟩ := hy
  exact ⟨c⁻¹, inv_ne_zero hc, _, eq_of_mul_eq_one' hc (normSq_ne_zero_of hn) h,
    isHur_inv_star hu hn, normSq_inv_star hn⟩

theorem InR.zero {p : ℕ} [Fact p.Prime] {ω : ℍ[ℚ_[p]]} : InR ω 0 :=
  ⟨0, 0, by simp, by simp, 0, isHur_zero, by simp⟩

theorem InR.add {p : ℕ} [Fact p.Prime] {ω u u' : ℍ[ℚ_[p]]} (hu : InR ω u) (hu' : InR ω u') :
    InR ω (u + u') := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hu
  obtain ⟨x', z', hx', hz', a', ha', rfl⟩ := hu'
  refine ⟨x + x', z + z', (Zp p).add_mem hx hx', (Zp p).add_mem hz hz', a + a', ha.add ha', ?_⟩
  simp only [add_smul, smul_add]; abel

theorem InR.neg {p : ℕ} [Fact p.Prime] {ω u : ℍ[ℚ_[p]]} (hu : InR ω u) : InR ω (-u) := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hu
  refine ⟨-x, -z, by rwa [norm_neg], by rwa [norm_neg], -a, ?_, ?_⟩
  · simpa using ha.smul ((Zp p).neg_mem (Zp p).one_mem)
  · simp only [neg_smul, smul_neg, neg_add]

theorem ωp_mul {p : ℕ} [Fact p.Prime] (s : Signs) :
    qp p (ωq s) * qp p (ωq s) = qp p (ωq s) - 1 := by
  rw [qp_ωq]
  have h1 := sgp_sq (p := p) s.1
  have h2 := sgp_sq (p := p) s.2.1
  have h3 := sgp_sq (p := p) s.2.2
  ext <;> simp
  · linear_combination (-1/4 : ℚ_[p]) * h1 - (1/4 : ℚ_[p]) * h2 - (1/4 : ℚ_[p]) * h3
  all_goals ring

theorem ωp_star {p : ℕ} [Fact p.Prime] (s : Signs) :
    star (qp p (ωq s)) = 1 - qp p (ωq s) := by
  rw [qp_ωq]; ext <;> simp <;> ring

/-! ## The subgroup `Sg` -/

/-- The local condition at a place `w`. -/
def Cond (v : HeightOneSpectrum (𝓞 ℚ)) (s : Signs) (w : HeightOneSpectrum (𝓞 ℚ))
    (y : ℍ[ℚ_[Pw w]]) : Prop :=
  (w = v → Loc2OK (qp (Pw w : ℕ) (ωq s)) y) ∧ (w ≠ v → LocOK y)

theorem Cond.mul {v : HeightOneSpectrum (𝓞 ℚ)} {s : Signs} {w} {y z : ℍ[ℚ_[Pw w]]}
    (hy : Cond v s w y) (hz : Cond v s w z) : Cond v s w (y * z) :=
  ⟨fun h => (hy.1 h).mul (isHur_qp_hurZ _) (ωp_mul s) (hz.1 h),
    fun h => (hy.2 h).mul (hz.2 h)⟩

theorem Cond.one {v : HeightOneSpectrum (𝓞 ℚ)} {s : Signs} {w} : Cond v s w 1 :=
  ⟨fun _ => Loc2OK.one, fun _ => LocOK.one⟩

theorem Cond.of_mul_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {s : Signs} {w} {y z : ℍ[ℚ_[Pw w]]}
    (hy : Cond v s w y) (h : y * z = 1) : Cond v s w z :=
  ⟨fun hw => (hy.1 hw).of_mul_eq_one (ωp_star s) h, fun hw => (hy.2 hw).of_mul_eq_one h⟩

/-- **The subgroup `Sg v s ⊂ B̂^×`**: `ℚ_p^× O_{B,p}^×` at odd places, `ℚ_2^× R_2^×` at `v`. -/
def Sg (v : HeightOneSpectrum (𝓞 ℚ)) (s : Signs) : Subgroup ℍ[AQ]ˣ where
  carrier := {h | ∀ w, Cond v s w (piQ w (h : ℍ[AQ]))}
  mul_mem' {a b} ha hb w := by
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    exact (ha w).mul (hb w)
  one_mem' w := by simp only [Units.val_one, map_one]; exact Cond.one
  inv_mem' {a} ha w := by
    refine (ha w).of_mul_eq_one ?_
    rw [← map_mul, Units.mul_inv, map_one]

/-! ## The generators -/

/-- `H τ = ⟨U_3, ℚ̂^×⟩`. -/
def Hgrp (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) : Subgroup ℍ[AQ]ˣ :=
  Subgroup.closure ((Un 3 τ : Set ℍ[AQ]ˣ) ∪ Set.range (Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom))

theorem centre_mem_Sg (v : HeightOneSpectrum (𝓞 ℚ)) (s : Signs) (z : AQˣ) :
    Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom z ∈ Sg v s := by
  intro w
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, piQ_algebraMap]
  have hz : ev w (z : AQ) ≠ 0 := by
    intro h0
    have := congrArg (ev w) z.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have he : ((ev w z : ℚ_[Pw w]) : ℍ[ℚ_[Pw w]]) = (ev w z) • (1 : ℍ[ℚ_[Pw w]]) := by
    rw [← Quaternion.coe_mul_eq_smul, mul_one]
  rw [he]
  exact ⟨fun _ => ⟨_, hz, 1, rfl, isHur_one, by simp, InR.one⟩,
    fun _ => ⟨_, hz, 1, rfl, isHur_one, by simp⟩⟩

theorem piQ_eq_one_of_comps {w : HeightOneSpectrum (𝓞 ℚ)} {y : ℍ[AQ]}
    (h : y.re w = 1 ∧ y.imI w = 0 ∧ y.imJ w = 0 ∧ y.imK w = 0) : piQ w y = 1 := by
  ext <;> simp [piQ, ev_apply, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem commute_ω_of {p : ℕ} [Fact p.Prime] {s : Signs} {τ' : ℍ[ℚ]} (hτ' : τ' = 2)
    {y : ℍ[ℚ_[p]]}
    (h : y * qp p (τ' * ωq s - 1) = qp p (τ' * ωq s - 1) * y) :
    y * qp p (ωq s) = qp p (ωq s) * y := by
  subst hτ'
  have e : qp p ((2 : ℍ[ℚ]) * ωq s - 1) = (2 : ℚ_[p]) • qp p (ωq s) - 1 := by
    rw [map_sub, map_mul, map_one, ← Quaternion.coe_mul_eq_smul]
    congr 1
  rw [e, mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc] at h
  have h' : (2 : ℚ_[p]) • (y * qp p (ωq s)) = (2 : ℚ_[p]) • (qp p (ωq s) * y) := by
    have := congrArg (· + y) h
    simpa using this
  exact smul_right_injective _ two_ne_zero h'

theorem K2Units_sub_Sg {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceTwo v) {s : Signs}
    {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} (hs : τ ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ωq s) :
    K2Units 3 τ ⊆ Sg v s := by
  intro k hk w
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · subst hw
    have hc := congrArg (piQ w) hk.1.eq
    rw [map_mul, map_mul, piQ_qι, sqrtNeg_eq, map_sub, map_mul, map_one, hs] at hc
    have hc' := commute_ω_of (s := s) (map_ofNat τ 2) hc
    have hne : piQ w ↑k ≠ 0 := by
      intro h0
      have := congrArg (piQ w) k.mul_inv
      rw [map_mul, h0, zero_mul, map_one] at this
      exact zero_ne_one this
    exact loc2OK_of_commute (Pw_eq_two hv) s hne hc'
  · rw [piQ_eq_one_of_comps (hk.2 w (not_isPlaceTwo_of_ne hv hw))]
    exact LocOK.one

theorem hurwitzHat_isHur (w : HeightOneSpectrum (𝓞 ℚ)) {h : ℍ[AQ]} (hh : h ∈ hurwitzHat) :
    IsHur (Zp (Pw w : ℕ)) (piQ w h) := by
  obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he, rfl⟩ := hh
  have A := ev_mem_Zp_of_integral w ha
  have B := ev_mem_Zp_of_integral w hb
  have C := ev_mem_Zp_of_integral w hc
  have D := ev_mem_Zp_of_integral w hd
  have E := ev_mem_Zp_of_integral w he
  have h2 : ev w (algebraMap ℚ AQ (1 / 2)) = 1 / 2 := by rw [ev_algebraMap]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert (Zp _).add_mem (mem_Zp.mpr A) (mem_Zp.mpr D) using 1
    simp only [ZInQ.Contrib.T21Proof.hc, piQ, qmap_re, qmap_imK, map_sub, map_add, map_mul, h2]; ring
  · convert (Zp _).sub_mem (mem_Zp.mpr B) (mem_Zp.mpr D) using 1
    simp only [ZInQ.Contrib.T21Proof.hc, piQ, qmap_imI, qmap_imK, map_add, map_mul, h2]; ring
  · convert (Zp _).sub_mem (mem_Zp.mpr C) (mem_Zp.mpr D) using 1
    simp only [ZInQ.Contrib.T21Proof.hc, piQ, qmap_imJ, qmap_imK, map_add, map_mul, h2]; ring
  · convert (Zp _).add_mem ((Zp _).add_mem (mem_Zp.mpr D) (mem_Zp.mpr D)) (mem_Zp.mpr E) using 1
    simp only [ZInQ.Contrib.T21Proof.hc, piQ, qmap_imK, map_add, map_mul, h2]; ring

/-- **`R̂_3 ⊂ ∏_w R_w`**: every element of `R̂_3 = τ̂(Ô_K) + 4Ô_B` lies in `ℤ_p + ℤ_p ω + 4O_{B,p}`. -/
theorem RnHat_InR {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} {s : Signs}
    (hs : τ ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ωq s) (w : HeightOneSpectrum (𝓞 ℚ)) {y : ℍ[AQ]}
    (hy : y ∈ RnHat 3 τ) : InR (qp (Pw w : ℕ) (ωq s)) (piQ w y) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨h, hh, rfl⟩
    · exact piQ_tauHat_mem hs ha w
    · refine ⟨0, 0, by simp, by simp, piQ w h, hurwitzHat_isHur w hh, ?_⟩
      rw [map_mul, map_ofNat, zero_smul, zero_smul, zero_add, zero_add,
        ← Quaternion.coe_mul_eq_smul]
      rfl
  | zero => rw [map_zero]; exact InR.zero
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg

theorem norm_eq_one_of_mul {p : ℕ} [Fact p.Prime] {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (h : a * b = 1) : ‖a‖ = 1 := by
  have := congrArg norm h
  rw [norm_mul, norm_one] at this
  refine le_antisymm ha (not_lt.mp fun hlt => ?_)
  have : ‖a‖ * ‖b‖ < 1 := by
    calc ‖a‖ * ‖b‖ ≤ ‖a‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  linarith

theorem RnUnits_sub_Sg {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} {v : HeightOneSpectrum (𝓞 ℚ)} {s : Signs}
    (hs : τ ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ωq s) : RnUnits 3 τ ⊆ Sg v s := by
  intro r hr w
  have h1 := RnHat_InR hs w hr.1
  have h2 := RnHat_InR hs w hr.2
  have hω := isHur_qp_hurZ (p := (Pw w : ℕ)) (ωH s)
  rw [← ωq] at hω
  have hu1 := h1.isHur hω
  have hu2 := h2.isHur hω
  have hprod : piQ w (r : ℍ[AQ]) * piQ w ((r⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hn : ‖Quaternion.normSq (piQ w (r : ℍ[AQ]))‖ = 1 := by
    refine norm_eq_one_of_mul hu1.normSq_mem hu2.normSq_mem ?_
    rw [← map_mul, hprod, map_one]
  exact ⟨fun _ => ⟨1, one_ne_zero, _, by simp, hu1, hn, h1⟩,
    fun _ => ⟨1, one_ne_zero, _, by simp, hu1, hn⟩⟩

/-- **`H τ ≤ Sg v s`.** -/
theorem Hgrp_le_Sg {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceTwo v)
    {s : Signs} (hs : τ ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ωq s) : Hgrp τ ≤ Sg v s := by
  refine (Subgroup.closure_le _).mpr (Set.union_subset ?_ ?_)
  · exact (Subgroup.closure_le _).mpr (Set.union_subset (RnUnits_sub_Sg hs) (K2Units_sub_Sg hv hs))
  · rintro _ ⟨z, rfl⟩
    exact centre_mem_Sg v s z

/-! ## Non-membership -/

theorem twoRepQ_eq (t : Fin 2 × Fin 2 × Fin 2) : twoRepQ t = hurZ (βZ t) := by
  apply hc_injective
  rw [hurZ, hc_hur]
  ext <;> simp [twoRepQ, βZ, hc, mapH] <;> ring

theorem two_adic_step' {p : ℕ} [Fact p.Prime] (hp : p = 2) (q : ℚ) (hq : q ≠ 0) (n : H4 ℤ)
    (k : ℕ) (hk : nrdH n = 2 ^ k) (β : H4 ℤ) (hβ : Odd (nrdH β)) (ωc : H4 ℤ) (c : ℚ_[p])
    (hc0 : c ≠ 0) (u : ℍ[ℚ_[p]]) (hu : IsHur (Zp p) u) (hnu : ‖Quaternion.normSq u‖ = 1)
    (hR : InR (hurZ ωc) u) (heq : qp p (q • hurZ n) * (c • u) = hurZ β) :
    ∃ μ : H4 ℤ, nrdH μ = 1 ∧ ∃ X Y : ZMod 4, Mod4Rel ωc (mulH μ β) X Y := by
  subst hp
  exact two_adic_step q hq n k hk β hβ ωc c hc0 u hu hnu hR heq

/-- **The six classes `t ∉ {0, t*(s)}` are not in `B^× Sg`** (hence not in `B^× H`). -/
theorem twoRep_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceTwo v) (s : Signs)
    (t : Fin 2 × Fin 2 × Fin 2) (ht0 : t ≠ (0, 0, 0)) (hts : t ≠ tstar s) {γ : ℍ[ℚ]} (hγ : γ ≠ 0)
    {h : ℍ[AQ]ˣ} (hh : h ∈ Sg v s) : twoRep v t ≠ qι γ * ↑h := by
  intro heq
  have hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → LocOK (qp p γ) := by
    intro p hpp hp2
    obtain ⟨w, hw⟩ := exists_place_of_prime p hpp.out
    subst hw
    have hwv : w ≠ v := fun h => hp2 (by rw [h]; exact Pw_eq_two hv)
    have e := congrArg (piQ w) heq
    rw [twoRep, piQ_ιAt_ne hwv, map_mul, piQ_qι] at e
    exact ((hh w).2 hwv).of_mul_eq_one' e.symm
  obtain ⟨q, n, k, hq, hγq, hk⟩ := global_step γ hγ hodd
  have e := congrArg (piQ v) heq
  rw [twoRep, piQ_ιAt_self, map_mul, piQ_qι, twoRepQ_eq, qp_hurZ] at e
  obtain ⟨c, hc0, u, hcu, hu, hnu, hR⟩ := (hh v).1 rfl
  rw [hcu, hγq] at e
  rw [ωq, qp_hurZ] at hR
  obtain ⟨μ, hμ, X, Y, hrel⟩ := two_adic_step' (Pw_eq_two hv) q hq n k hk (βZ t) (nrdH_βZ_odd t)
    (ωH s) c hc0 u hu hnu hR e.symm
  exact mod4_check s t ht0 hts μ (mem_unitList hμ) X Y hrel

end ZInQ.Contrib.T21Proof
