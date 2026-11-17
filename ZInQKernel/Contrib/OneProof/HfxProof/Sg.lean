import ZInQKernel.Contrib.OneProof.HfxProof.TauData

/-!
# hfx-proof: local obstructions to double-coset membership

Task hfx-proof. Generalizes t21-proof's `Sg`/`twoRep_ne` (the class of `1` at `n = 3`). A local condition
`C` at `2` closed under products and inverses defines `SgC ≤ B̂^×` (`ℚ_p^× O_{B,p}^×` at odd places,
`C` at `2`). If `H = ⟨U_n, ℚ̂^×⟩ ≤ SgC` and no relation `q n β_{t'} y = β_t` (`n` integral of norm `2^k`,
`y ∈ C`) holds in `ℍ[ℚ_2]`, then `twoRep t ∉ B^× twoRep t' H` (`twoRep_not_mem_DC`). `HgrpN_le_SgC`
reduces `H ≤ SgC` to three local facts about `C`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- A local condition at `2`, closed under products and inverses. -/
structure LocCond where
  P : ∀ (p : ℕ) [Fact p.Prime], ℍ[ℚ_[p]] → Prop
  one : ∀ (p : ℕ) [Fact p.Prime], p = 2 → P p 1
  mul : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ y z, P p y → P p z → P p (y * z)
  inv : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ y z, P p y → y * z = 1 → P p z

/-- `SgC`: `ℚ_p^× O_{B,p}^×` at odd places, `C` at `v`. -/
def SgC (v : HeightOneSpectrum (𝓞 ℚ)) (hv : IsPlaceTwo v) (C : LocCond) : Subgroup ℍ[AQ]ˣ where
  carrier := {h | ∀ w, (w = v → C.P (Pw w : ℕ) (piQ w (h : ℍ[AQ]))) ∧ (w ≠ v → LocOK (piQ w (h : ℍ[AQ])))}
  mul_mem' {a b} ha hb w := by
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    refine ⟨fun h => C.mul _ (h ▸ Pw_eq_two hv) _ _ ((ha w).1 h) ((hb w).1 h),
      fun h => ((ha w).2 h).mul ((hb w).2 h)⟩
  one_mem' w := by
    simp only [Set.mem_setOf_eq, Units.val_one, map_one]
    exact ⟨fun h => C.one _ (h ▸ Pw_eq_two hv), fun _ => LocOK.one⟩
  inv_mem' {a} ha w := by
    have e : piQ w (a : ℍ[AQ]) * piQ w ((a⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact ⟨fun h => C.inv _ (h ▸ Pw_eq_two hv) _ _ ((ha w).1 h) e,
      fun h => ((ha w).2 h).of_mul_eq_one e⟩

/-- **The local obstruction.** -/
theorem twoRep_not_mem_DC {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : IsPlaceTwo v) (C : LocCond) (hH : HgrpN n τ ≤ SgC v hv C) {t t' : T8}
    (hfin : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ (q : ℚ) (nn : H4 ℤ) (k : ℕ), q ≠ 0 →
      nrdH nn = 2 ^ k → ∀ y, C.P p y → qp p (q • hurZ nn) * hurZ (βZ t') * y ≠ hurZ (βZ t)) :
    twoRep v t ∉ DC n τ (twoRep v t') := by
  rintro ⟨γ, hγ, h, hh, e⟩
  have hS := hH hh
  have hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → LocOK (qp p γ) := by
    intro p hpp hp2
    obtain ⟨w, hw⟩ := exists_place_of_prime p hpp.out
    subst hw
    have hwv : w ≠ v := fun h => hp2 (by rw [h]; exact Pw_eq_two hv)
    have e' := congrArg (piQ w) e
    rw [twoRep, twoRep, piQ_ιAt_ne hwv, map_mul, map_mul, piQ_qι, piQ_ιAt_ne hwv, mul_one] at e'
    exact ((hS w).2 hwv).of_mul_eq_one' e'.symm
  obtain ⟨q, nn, k, hq, hγq, hk⟩ := global_step γ hγ hodd
  have e' := congrArg (piQ v) e
  rw [twoRep, twoRep, piQ_ιAt_self, map_mul, map_mul, piQ_qι, piQ_ιAt_self, twoRepQ_eq,
    twoRepQ_eq, qp_hurZ, qp_hurZ, hγq] at e'
  exact hfin _ (Pw_eq_two hv) q nn k hq hk _ ((hS v).1 rfl) e'.symm

/-! ## `H ≤ SgC` -/

theorem centre_mem_SgC (v : HeightOneSpectrum (𝓞 ℚ)) (hv : IsPlaceTwo v) (C : LocCond)
    (hc : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ c : ℚ_[p], c ≠ 0 → C.P p (c • 1)) (z : AQˣ) :
    Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom z ∈ SgC v hv C := by
  intro w
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, piQ_algebraMap]
  have hz : ev w (z : AQ) ≠ 0 := by
    intro h0
    have := congrArg (ev w) z.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have he : ((ev w z : ℚ_[Pw w]) : ℍ[ℚ_[Pw w]]) = (ev w z) • (1 : ℍ[ℚ_[Pw w]]) := by
    rw [← Quaternion.coe_mul_eq_smul, mul_one]
  rw [he]
  exact ⟨fun h => hc _ (h ▸ Pw_eq_two hv) _ hz, fun _ => ⟨_, hz, 1, rfl, isHur_one, by simp⟩⟩

/-- `τ̂(Ô_K)` lies in `ℤ_p + ℤ_p ω` at every place, when `τ(O_K) ⊂ ℤ + ℤω`. -/
theorem piQ_tauHat_mem' {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} {ωq : ℍ[ℚ]}
    (hspan : ∀ x : 𝓞 (QNeg n), ∃ m s : ℤ, τ x = (m : ℍ[ℚ]) + (s : ℚ) • ωq)
    {a : FiniteAdeleRing (𝓞 (QNeg n)) (QNeg n)}
    (ha : a ∈ FiniteAdeleRing.integralAdeles (𝓞 (QNeg n)) (QNeg n))
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    InR (qp (Pw w : ℕ) ωq) (piQ w (tauHat n τ a)) := by
  obtain ⟨c, hc, he⟩ := tauHat_integral n τ ha w
  choose m s hms using fun i => hspan (RingOfIntegers.basis (QNeg n) i)
  have hτb : ∀ i, qp (Pw w : ℕ) (τ (bK n i)) =
      (m i : ℚ_[Pw w]) • (1 : ℍ[ℚ_[Pw w]]) + (s i : ℚ_[Pw w]) • qp (Pw w : ℕ) ωq := by
    intro i
    rw [bK, hms i, map_add, map_intCast, qp_smul]
    congr 1
    ext <;> simp
  refine ⟨∑ i, c i * m i, ∑ i, c i * s i, ?_, ?_, 0, isHur_zero, ?_⟩
  · exact (Zp _).sum_mem fun i _ => (Zp _).mul_mem (hc i) (Padic.norm_int_le_one _)
  · exact (Zp _).sum_mem fun i _ => (Zp _).mul_mem (hc i) (Padic.norm_int_le_one _)
  · rw [he, smul_zero, add_zero, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hτb, smul_add, smul_smul, smul_smul]

theorem RnHat_InR' {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} {ωq : ℍ[ℚ]}
    (hspan : ∀ x : 𝓞 (QNeg n), ∃ m s : ℤ, τ x = (m : ℍ[ℚ]) + (s : ℚ) • ωq)
    (w : HeightOneSpectrum (𝓞 ℚ)) {y : ℍ[AQ]} (hy : y ∈ RnHat n τ) :
    InR (qp (Pw w : ℕ) ωq) (piQ w y) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨h, hh, rfl⟩
    · exact piQ_tauHat_mem' hspan ha w
    · refine ⟨0, 0, by simp, by simp, piQ w h, hurwitzHat_isHur w hh, ?_⟩
      rw [map_mul, map_ofNat, zero_smul, zero_smul, zero_add, zero_add,
        ← Quaternion.coe_mul_eq_smul]
      rfl
  | zero => rw [map_zero]; exact InR.zero
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg

/-- **`H ≤ SgC`** from three local facts about `C`. -/
theorem HgrpN_le_SgC {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : IsPlaceTwo v) (C : LocCond) {ωq : ℍ[ℚ]} (hωZ : IsHurZ ωq)
    (hspan : ∀ x : 𝓞 (QNeg n), ∃ m s : ℤ, τ x = (m : ℍ[ℚ]) + (s : ℚ) • ωq)
    (hc : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ c : ℚ_[p], c ≠ 0 → C.P p (c • 1))
    (hR : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ u, IsHur (Zp p) u → ‖Quaternion.normSq u‖ = 1 →
      InR (qp p ωq) u → C.P p u)
    (hK : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ y : ℍ[ℚ_[p]], y ≠ 0 →
      y * qp p (τ (sqrtNeg n)) = qp p (τ (sqrtNeg n)) * y → C.P p y) :
    HgrpN n τ ≤ SgC v hv C := by
  refine (Subgroup.closure_le _).mpr (Set.union_subset ?_ ?_)
  · refine (Subgroup.closure_le _).mpr (Set.union_subset ?_ ?_)
    · intro r hr w
      have h1 := RnHat_InR' hspan w hr.1
      have h2 := RnHat_InR' hspan w hr.2
      have hω := isHur_qp_hurZ' (p := (Pw w : ℕ)) hωZ
      have hu1 := h1.isHur hω
      have hu2 := h2.isHur hω
      have hprod : piQ w (r : ℍ[AQ]) * piQ w ((r⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      have hn : ‖Quaternion.normSq (piQ w (r : ℍ[AQ]))‖ = 1 := by
        refine norm_eq_one_of_mul hu1.normSq_mem hu2.normSq_mem ?_
        rw [← map_mul, hprod, map_one]
      exact ⟨fun h => hR _ (h ▸ Pw_eq_two hv) _ hu1 hn h1,
        fun _ => ⟨1, one_ne_zero, _, by simp, hu1, hn⟩⟩
    · intro k hk w
      refine ⟨fun hw => ?_, fun hw => ?_⟩
      · subst hw
        have hc' := congrArg (piQ w) hk.1.eq
        rw [map_mul, map_mul, piQ_qι] at hc'
        have hne : piQ w (k : ℍ[AQ]) ≠ 0 := piQ_unit_ne_zero w k
        exact hK _ (Pw_eq_two hv) _ hne hc'
      · rw [piQ_eq_one_of_comps (hk.2 w (not_isPlaceTwo_of_ne hv hw))]
        exact LocOK.one
  · rintro _ ⟨z, rfl⟩
    exact centre_mem_SgC v hv C hc z

end ZInQ.Contrib.HfxProof
