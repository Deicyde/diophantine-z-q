import ZInQKernel.Contrib.OneProof.TYZProp23Printed

/-!
# tyz-genus: reduced norms on a double coset, and `F = 0` on the classes with `χ₀ = −1` (`n ≡ 1 (mod 8)`)

* `dc_norm`: if `y ∈ B^× twoRep(t) H` and `H ⊆ SgC` (local conditions: `ℚ_p^× O_{B,p}^×` at odd `p`, and at `2`
  reduced norms in `2^ℤ(1 + 4ℤ₂)`), then `nrd(y)` is, at every odd place, a positive rational `g` times a square
  times a unit, and at `2`, `g · nrd(twoRep t) · κ` with `κ ∈ 2^ℤ(1 + 4ℤ₂)`.
* `chi0_eq_of_mem_DC`: two representatives in the same double coset have the same `χ₀(nrd)`, i.e. the same
  `t.2.2`.
* `F_zero`: the explicit generator `F` of hfx-proof/hp23-proof vanishes on the classes with `t.2.2 ≠ 0`
  (`χ₀ = −1`): `chi0Rep · F` has the same invariance and orthogonality as `F`, so it is `c F` by rank one, and
  `c = 1` at the class of `1`, where `F` is odd.
-/

set_option linter.style.longLine false
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.TYZGenusFold

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof ZInQ.Contrib.HfxProof ZInQ.Contrib.HP23Proof
open IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

section DC

variable {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} {v : HeightOneSpectrum (𝓞 ℚ)}

/-- **Reduced norms on a double coset.** -/
theorem dc_norm (hv : IsPlaceTwo v) (C : LocCond) (hH : HgrpN n τ ≤ SgC v hv C)
    (hC : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ y : ℍ[ℚ_[p]], C.P p y → Good (Quaternion.normSq y))
    {y : ℍ[AQ]} {t : T8} (hy : y ∈ DC n τ (twoRep v t)) :
    ∃ g : ℚ, 0 < g ∧
      (∀ w, w ≠ v → ∃ c e : ℚ_[Pw w], c ≠ 0 ∧ ‖e‖ = 1 ∧
        Quaternion.normSq (piQ w y) = (g : ℚ_[Pw w]) * (c ^ 2 * e)) ∧
      ∃ κ : ℚ_[Pw v], Good κ ∧
        Quaternion.normSq (piQ v y) = (g : ℚ_[Pw v]) * ((nrdH (βZ t) : ℤ) : ℚ_[Pw v]) * κ := by
  obtain ⟨γ, hγ, u, hu, e⟩ := hy
  have hS := hH hu
  refine ⟨Quaternion.normSq γ, normSq_pos' hγ, fun w hwv => ?_, ?_⟩
  · have e' := congrArg (piQ w) e
    rw [map_mul, map_mul, piQ_qι, twoRep, piQ_ιAt_ne hwv, mul_one] at e'
    obtain ⟨c, hc, u0, hu0, -, hn0⟩ := (hS w).2 hwv
    refine ⟨c, Quaternion.normSq u0, hc, hn0, ?_⟩
    rw [e', hu0, map_mul, normSq_qp, Quaternion.normSq_smul]
  · have e' := congrArg (piQ v) e
    rw [map_mul, map_mul, piQ_qι, twoRep, piQ_ιAt_self, twoRepQ_eq, qp_hurZ] at e'
    refine ⟨Quaternion.normSq (piQ v (u : ℍ[AQ])), hC _ (Pw_eq_two hv) _ ((hS v).1 rfl), ?_⟩
    rw [e', map_mul, map_mul, normSq_qp, normSq_hurZ]

theorem nrdH_βZ_mul_mod4 : ∀ t t' : T8, (nrdH (βZ t) * nrdH (βZ t')) % 4 ≠ 3 → t.2.2 = t'.2.2 := by
  decide +kernel

/-- **Representatives in one double coset have the same `χ₀(nrd)`.** -/
theorem chi0_eq_of_mem_DC (hv : IsPlaceTwo v) (C : LocCond) (hH : HgrpN n τ ≤ SgC v hv C)
    (hC : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ y : ℍ[ℚ_[p]], C.P p y → Good (Quaternion.normSq y))
    {t t' : T8} (h : twoRep v t ∈ DC n τ (twoRep v t')) : t.2.2 = t'.2.2 := by
  obtain ⟨g, hg, hodd, κ, hκ, h2⟩ := dc_norm hv C hH hC h
  have hev : ∀ r : ℕ, r.Prime → r ≠ 2 → Even (padicValRat r g) := by
    intro r hr hr2
    obtain ⟨w, hw⟩ := exists_place_of_prime r hr
    have hwv : w ≠ v := fun h' => hr2 (by rw [← hw, h']; exact Pw_eq_two hv)
    obtain ⟨c, e, hc, he, hN⟩ := hodd w hwv
    rw [twoRep, piQ_ιAt_ne hwv, map_one] at hN
    rw [← hw]
    exact even_padicValRat_of_eq hg.ne' one_ne_zero hc he (by rw [one_pow, hN])
  rw [twoRep, piQ_ιAt_self, twoRepQ_eq, qp_hurZ, normSq_hurZ] at h2
  apply nrdH_βZ_mul_mod4
  have key : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ (κ : ℚ_[p]) (a b : ℤ), Good κ → Odd b →
      ((a : ℤ) : ℚ_[p]) = (g : ℚ_[p]) * ((b : ℤ) : ℚ_[p]) * κ → (a * b) % 4 ≠ 3 := by
    intro p _ hp
    subst hp
    intro κ a b hκ hb e2 h3
    have hb0 : ((b : ℤ) : ℚ_[2]) ≠ 0 := by
      exact_mod_cast (show b ≠ 0 by rintro rfl; exact (by norm_num : ¬ Odd (0 : ℤ)) hb)
    have h1 : Good (((a * b : ℤ) : ℚ_[2])) := by
      have e3 : ((a * b : ℤ) : ℚ_[2]) = (g : ℚ_[2]) * (((b : ℤ) : ℚ_[2]) ^ 2 * κ) := by
        push_cast; rw [e2]; ring
      rw [e3]
      exact (good_rat hg hev).mul ((good_sq hb0).mul hκ)
    exact not_good_int h3 h1
  exact key _ (Pw_eq_two hv) κ _ _ hκ (nrdH_βZ_odd t') h2

/-- **`F` vanishes on the classes with `χ₀ = −1`** (`t.2.2 ≠ 0`). -/
theorem F_zero (hv : IsPlaceTwo v) {F : T8 → ℤ} (hP : PartData n τ v F)
    (hodd : ∀ t : T8, t.2.2 = 0 → Odd (F t)) (C : LocCond) (hH : HgrpN n τ ≤ SgC v hv C)
    (hC : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ y : ℍ[ℚ_[p]], C.P p y → Good (Quaternion.normSq y)) :
    ∀ t : T8, t.2.2 ≠ 0 → F t = 0 := by
  obtain ⟨-, hM, -, ⟨hs1, hs2⟩, hrk, -⟩ := hP
  have hchi : ∀ t t' : T8, t.2.2 = t'.2.2 → chi0Rep t = chi0Rep t' := fun t t' h => by
    unfold chi0Rep; rw [h]
  have hsq : ∀ t : T8, chi0Rep t * chi0Rep t = 1 := fun t => by
    unfold chi0Rep; rw [← pow_add, ← two_mul, pow_mul]; simp
  obtain ⟨c, hc⟩ := hrk (fun t => chi0Rep t * F t)
    (fun t t' h => by rw [hchi t t' (chi0_eq_of_mem_DC hv C hH hC (hM t t' h)), h]) hs2
    (by
      rw [← hs1]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← mul_assoc, hsq, one_mul])
  have h0 : (0, 0, 0) ∈ (Finset.univ : Finset T8) := Finset.mem_univ _
  have hc1 : c = 1 := by
    have e := hc (0, 0, 0)
    have hO := hodd (0, 0, 0) rfl
    have hr : chi0Rep ((0, 0, 0) : T8) = 1 := by decide
    rw [hr, one_mul] at e
    have hF0 : F (0, 0, 0) ≠ 0 := fun h => by rw [h] at hO; exact (by norm_num : ¬ Odd (0 : ℤ)) hO
    have : (c - 1) * F (0, 0, 0) = 0 := by linear_combination -e
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hF0
  intro t ht
  have e := hc t
  rw [hc1, one_mul] at e
  have hr : chi0Rep t = -1 := by
    unfold chi0Rep
    have : (t.2.2 : ℕ) = 1 := by have := t.2.2.isLt; omega
    rw [this]; norm_num
  rw [hr] at e
  linarith

end DC

end ZInQ.Contrib.TYZGenusFold
