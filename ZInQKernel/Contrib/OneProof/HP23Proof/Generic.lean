import ZInQKernel.Contrib.OneProof.HP23Proof.Good
import ZInQKernel.Contrib.OneProof.HfxProof.Sg

/-!
# hp23-proof: test vectors are `±F`, and squares avoid the classes with `χ₀ = −1`

Task hp23-proof (report `docs/research/hp23-proof.md`).

* `tv_eq_sign`: given the partition data of hfx-proof's `testVector_of_partition` (`PartData`), every
  test vector `f` (TYZ's `f_n`, a `ℤ`-generator of `π_ℤ^{U_n}`) equals `±F t` on the double coset
  `B^× twoRep(t) H`: `f` is `c F` on the representatives (rank one), and `fOf F` is in `π_ℤ^{U_n}`, so
  it is `d f`; `F ≠ 0` forces `dc = 1`.
* `sq_class`: if `H = ⟨U_n, ℚ̂^×⟩` lies in a local-condition subgroup `SgC` whose condition at `2` forces
  `nrd ∈ 2^ℤ(1 + 4ℤ₂)` (`Good`), then a square `h²` of a unit of `B̂` lies only in double cosets of
  `twoRep t` with `t.2.2 = 0` (`χ₀(nrd twoRep t) = 1`). From `h² = γ twoRep(t) u`: at an odd place the
  valuation of `nrd γ` is even (`even_padicValRat_of_eq`), so `nrd γ ∈ 2^ℤ(1 + 4ℤ₂)` (`good_rat`);
  at `2`, `nrd(h)² = nrd γ · nrd(twoRep t) · nrd u` then puts `nrd(twoRep t) ≡ 3 (mod 4)` in that
  subgroup, which is impossible (`not_good_int`).
-/

set_option linter.style.longLine false
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.HP23Proof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof ZInQ.Contrib.HfxProof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The hypotheses of hfx-proof's `testVector_of_partition` for `n`, `τ`, the place `v` and `F`. -/
def PartData (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (v : HeightOneSpectrum (𝓞 ℚ)) (F : T8 → ℤ) :
    Prop :=
  (∀ x : ℍ[AQ]ˣ, ∃ t, (x : ℍ[AQ]) ∈ DC n τ (twoRep v t)) ∧
  (∀ t t', F t = F t' → twoRep v t ∈ DC n τ (twoRep v t')) ∧
  (∀ t t', F t ≠ F t' → twoRep v t ∉ DC n τ (twoRep v t')) ∧
  (∑ t : T8, F t = 0 ∧ ∑ t : T8, chi0Rep t * F t = 0) ∧
  (∀ G : T8 → ℤ, (∀ t t', F t = F t' → G t = G t') → ∑ t : T8, G t = 0 →
    ∑ t : T8, chi0Rep t * G t = 0 → ∃ c : ℤ, ∀ t, G t = c * F t) ∧
  (∃ t, F t ≠ 0)

section TV

variable {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} {v : HeightOneSpectrum (𝓞 ℚ)}

/-- `fOf F` lies in `π_ℤ^{U_n}` (the first half of hfx-proof's `testVector_of_partition`). -/
theorem inPiZ_fOf (hv : IsPlaceTwo v) {F : T8 → ℤ}
    (hN : ∀ t t', F t ≠ F t' → twoRep v t ∉ DC n τ (twoRep v t'))
    (hsum : ∑ t : T8, F t = 0 ∧ ∑ t : T8, chi0Rep t * F t = 0) : InPiZ n τ (fOf n τ v F) := by
  have hval : ∀ t, fOf n τ v F (twoRep v t) = F t := fun t => fOf_eq F hN (mem_DC_self _)
  have hinv : ∀ {x y : ℍ[AQ]}, y ∈ DC n τ x → x ∈ DC n τ y →
      fOf n τ v F y = fOf n τ v F x := by
    intro x y hxy hyx
    classical
    by_cases h : ∃ t, x ∈ DC n τ (twoRep v t)
    · obtain ⟨t, ht⟩ := h
      rw [fOf_eq F hN ht, fOf_eq F hN (DC_trans ht hxy)]
    · have h' : ¬ ∃ t, y ∈ DC n τ (twoRep v t) := fun ⟨t, ht⟩ => h ⟨t, DC_trans ht hyx⟩
      rw [fOf, dif_neg h', fOf, dif_neg h]
  have hplace : ∀ v', IsPlaceTwo v' → v' = v := fun v' hv' =>
    eq_of_Pw_eq (by rw [Pw_eq_two hv', Pw_eq_two hv])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ hγ x
    exact hinv ⟨γ, hγ, 1, Subgroup.one_mem _, by simp⟩
      ⟨γ⁻¹, inv_ne_zero hγ, 1, Subgroup.one_mem _, by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hγ, map_one]; simp⟩
  · intro x u hu
    have hu' : u ∈ HgrpN n τ := Subgroup.subset_closure (Or.inl hu)
    exact hinv ⟨1, one_ne_zero, u, hu', by simp⟩ ⟨1, one_ne_zero, u⁻¹, Subgroup.inv_mem _ hu', by
      rw [map_one, one_mul, mul_assoc, Units.mul_inv, mul_one]⟩
  · intro x z
    have hz : Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom z ∈ HgrpN n τ :=
      Subgroup.subset_closure (Or.inr ⟨z, rfl⟩)
    have e : algebraMap AQ ℍ[AQ] (z : AQ) =
        ((Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom z : ℍ[AQ]ˣ) : ℍ[AQ]) := rfl
    rw [e]
    exact hinv ⟨1, one_ne_zero, _, hz, by simp⟩ ⟨1, one_ne_zero, _, Subgroup.inv_mem _ hz, by
      rw [map_one, one_mul, mul_assoc, Units.mul_inv, mul_one]⟩
  · intro v' hv'
    obtain rfl := hplace v' hv'
    simp only [hval]
    exact hsum

/-- **Test vectors are `±F`.** Every test vector `f` equals `s F t` (`s = ±1`, independent of `t`) on the
double coset of `twoRep t`. -/
theorem tv_eq_sign (hv : IsPlaceTwo v) {F : T8 → ℤ} (hP : PartData n τ v F) {f : ℍ[AQ] → ℤ}
    (hf : IsTestVector n τ f) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ (x : ℍ[AQ]ˣ) (t : T8), (x : ℍ[AQ]) ∈ DC n τ (twoRep v t) → f x = s * F t := by
  obtain ⟨-, hM, hN, hsum, hrk, t0, ht0⟩ := hP
  have hpi := inPiZ_fOf hv hN hsum
  have hval : ∀ t, fOf n τ v F (twoRep v t) = F t := fun t => fOf_eq F hN (mem_DC_self _)
  have hG : ∀ t t', F t = F t' → f (twoRep v t) = f (twoRep v t') := fun t t' h =>
    inPiZ_eq_of_mem_DC hf.1 (x := twoRepU v t') (y := twoRepU v t) (hM t t' h)
  have h4 := hf.1.2.2.2 v hv
  obtain ⟨c, hc⟩ := hrk (fun t => f (twoRep v t)) hG h4.1 h4.2
  obtain ⟨d, hd⟩ := hf.2 _ hpi
  have e := hd (twoRepU v t0)
  rw [twoRepU_coe, hval, hc t0] at e
  have hdc : d * c = 1 := by
    have h0 : (d * c - 1) * F t0 = 0 := by linear_combination (-1 : ℤ) * e
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exact absurd h ht0
  refine ⟨c, Int.eq_one_or_neg_one_of_mul_eq_one (by rwa [mul_comm] at hdc), fun x t hx => ?_⟩
  rw [inPiZ_eq_of_mem_DC hf.1 (x := twoRepU v t) hx]
  exact hc t

end TV

/-! ## Squares -/

theorem nrdH_βZ_mod4 : ∀ t : T8, t.2.2 ≠ 0 → nrdH (βZ t) % 4 = 3 := by decide +kernel

/-- **Squares avoid the classes with `χ₀ = −1`.** -/
theorem sq_class {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : IsPlaceTwo v) (C : LocCond) (hH : HgrpN n τ ≤ SgC v hv C)
    (hC : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ y : ℍ[ℚ_[p]], C.P p y → Good (Quaternion.normSq y))
    (h : ℍ[AQ]ˣ) {t : T8} (ht : ((h * h : ℍ[AQ]ˣ) : ℍ[AQ]) ∈ DC n τ (twoRep v t)) : t.2.2 = 0 := by
  obtain ⟨γ, hγ, u, hu, e⟩ := ht
  have hS := hH hu
  have hNγ : 0 < Quaternion.normSq γ := normSq_pos' hγ
  -- odd places: the valuations of `nrd γ` are even
  have hev : ∀ r : ℕ, r.Prime → r ≠ 2 → Even (padicValRat r (Quaternion.normSq γ)) := by
    intro r hr hr2
    obtain ⟨w, hw⟩ := exists_place_of_prime r hr
    have hwv : w ≠ v := fun h' => hr2 (by rw [← hw, h']; exact Pw_eq_two hv)
    have e' := congrArg (piQ w) e
    rw [Units.val_mul, map_mul, twoRep, map_mul, map_mul, piQ_qι, piQ_ιAt_ne hwv, mul_one] at e'
    obtain ⟨c, hc, u0, hu0, -, hn0⟩ := (hS w).2 hwv
    rw [hu0] at e'
    have eN := congrArg Quaternion.normSq e'
    rw [map_mul, map_mul, normSq_qp, Quaternion.normSq_smul] at eN
    rw [← hw]
    exact even_padicValRat_of_eq hNγ.ne' (normSq_piQ_unit_ne_zero w h) hc hn0 (by rw [sq]; exact eN)
  -- the place 2
  by_contra ht2
  have hβ := nrdH_βZ_mod4 t ht2
  have e' := congrArg (piQ v) e
  rw [Units.val_mul, map_mul, twoRep, map_mul, map_mul, piQ_qι, piQ_ιAt_self, twoRepQ_eq,
    qp_hurZ] at e'
  have eN := congrArg Quaternion.normSq e'
  rw [map_mul, map_mul, map_mul, normSq_qp, normSq_hurZ] at eN
  have key : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ (a x : ℚ_[p]) (q : ℚ) (m : ℤ), a ≠ 0 → Good x →
      0 < q → (∀ r : ℕ, r.Prime → r ≠ 2 → Even (padicValRat r q)) → m % 4 = 3 →
      a * a = (q : ℚ_[p]) * (m : ℚ_[p]) * x → False := by
    intro p _ hp
    subst hp
    intro a x q m ha hx hq hevq hm e2
    have h1 : Good (a * a) := by rw [← sq]; exact good_sq ha
    rw [e2] at h1
    exact not_good_int hm ((h1.of_mul_right hx).of_mul_left (good_rat hq hevq))
  exact key _ (Pw_eq_two hv) _ _ _ _ (normSq_piQ_unit_ne_zero v h)
    (hC _ (Pw_eq_two hv) _ ((hS v).1 rfl)) hNγ hev hβ eN

end ZInQ.Contrib.HP23Proof
