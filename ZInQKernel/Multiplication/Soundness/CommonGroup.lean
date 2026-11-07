import ZInQKernel.Multiplication.Soundness.ContactValuations
import ZInQKernel.Multiplication.Soundness.PoleObstruction
import ZInQKernel.Multiplication.Local.PrimesAbove
import ZInQKernel.Multiplication.Local.Valuations

/-!
# The trace forces one common group and place

Blueprint: `multiplication/soundness/common-group.md`.

Let `t, η, q, R₀, a, R` be as in the slope predicate (`t ∉ 𝒞 ∪ {1}`, `a ≠ 0`), let
`D_{gj} ∈ K₀` (`g < 6`, `j < 12`) be arbitrary, `C_{gj} = D_{gj} / (R₀^{k_j} (t-1)^{k_j+1})`,
`W_g = ∏_j (1 + R C_{gj}²)` and `Θ = Tr Σ_g W_g⁻¹`, with `W_g ≠ 0`, `Θ ≠ 0` and `Φ(R/Θ²)`. At an
odd contact prime `p` of `t` with `p > 324` and `v_p(ℓ) = 0` (the article's `p ∉ S_b`), some
group `g` and some prime `π ∣ p` of `ℤ[s]` have `v_π(D_{gj}) ≥ k_j` for every `j`.

The quantities of the slope predicate are spelled out here (`slopeR₀`, `slopeA`, `slopeR`,
`slopeC`, `slopeW`, `slopeTheta`); `testPrec j = k_j`.
-/

namespace ZInQ

open Mult

/-- The test precisions `k_j = 1` for `j < 8` and `k_j = 25` for `8 ≤ j < 12` (indices from `0`). -/
def testPrec (j : Fin 12) : ℕ := if (j : ℕ) < 8 then 1 else 25

/-- `R₀ = η F(t) / (t - 1)⁸`. -/
def slopeR₀ (η t : ℚ) : ℚ := η * contactPoly t / (t - 1) ^ 8

/-- `a = 1 - R₀ q²`. -/
def slopeA (η t q : ℚ) : ℚ := 1 - slopeR₀ η t * q ^ 2

/-- `R = ℓ² a² R₀`. -/
def slopeR (ℓ η t q : ℚ) : ℚ := ℓ ^ 2 * slopeA η t q ^ 2 * slopeR₀ η t

/-- `C = D / (R₀^{k_j} (t - 1)^{k_j + 1})`. -/
noncomputable def slopeC (η t : ℚ) (D : K0) (j : Fin 12) : K0 :=
  D / ((slopeR₀ η t : K0) ^ testPrec j * ((t - 1 : ℚ) : K0) ^ (testPrec j + 1))

/-- `W_g = ∏_j (1 + R C_{gj}²)`. -/
noncomputable def slopeW (ℓ η t q : ℚ) (D : Fin 12 → K0) : K0 :=
  ∏ j, (1 + (slopeR ℓ η t q : K0) * slopeC η t (D j) j ^ 2)

/-- `Θ = Tr Σ_g W_g⁻¹`. -/
noncomputable def slopeTheta (ℓ η t q : ℚ) (D : Fin 6 → Fin 12 → K0) : ℚ :=
  QuadraticAlgebra.trace (∑ g, (slopeW ℓ η t q (D g))⁻¹)

/-- Every rational prime has a prime of `ℤ[s]` above it. -/
theorem exists_prime_dvd_natCast (p : ℕ) [hp : Fact p.Prime] :
    ∃ π : Zs, Prime π ∧ π ∣ (p : Zs) := by
  have h0 : (p : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this; exact hp.out.ne_zero this
  have hu : ¬ IsUnit (p : Zs) := by
    intro hu
    have := hu.map QuadraticAlgebra.norm
    rw [norm_natCast_Zs, Int.isUnit_iff] at this
    have h1 := hp.out.one_lt
    rcases this with h | h
    · have : ((p : ℤ)) ^ 2 = 1 ^ 2 := by rw [h]; ring
      have := (sq_eq_sq₀ (by positivity) (by norm_num)).mp this
      omega
    · nlinarith
  obtain ⟨π, hirr, hdvd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
  exact ⟨π, UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr, hdvd⟩

theorem star_dvd_natCast {π : Zs} {p : ℕ} (h : π ∣ (p : Zs)) : star π ∣ (p : Zs) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨star c, by rw [← star_mul', ← hc]; simp⟩

theorem vp_prod {π : Zs} (hπ : Prime π) {ι : Type*} (s : Finset ι) (f : ι → K0)
    (h : ∀ i ∈ s, f i ≠ 0) : vp π (∏ i ∈ s, f i) = ∑ i ∈ s, vp π (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vp_isUnit hπ isUnit_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      vp_mul hπ (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem vp_one' {π : Zs} (hπ : Prime π) : vp π (1 : K0) = 0 := by
  simpa using vp_isUnit hπ isUnit_one

section

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_π(1 + R C²) = min(0, r + 2 v_π(C))` when `v_π(R) = r` is odd and `C ≠ 0`. -/
theorem vp_one_add_mul_sq {π : Zs} (hπ : Prime π) {R C : K0} (hR : R ≠ 0) (hC : C ≠ 0)
    (hodd : Odd (vp π R)) : vp π (1 + R * C ^ 2) = min 0 (vp π R + 2 * vp π C) := by
  have hRC : R * C ^ 2 ≠ 0 := mul_ne_zero hR (pow_ne_zero _ hC)
  have hv : vp π (R * C ^ 2) = vp π R + 2 * vp π C := by
    rw [vp_mul hπ hR (pow_ne_zero _ hC), vp_pow hπ]; push_cast; ring
  rw [vp_add_eq_min_of_ne hπ one_ne_zero hRC (by
    rw [vp_one' hπ, hv]; obtain ⟨j, hj⟩ := hodd; omega), vp_one' hπ, hv]

/-- **The trace forces one common group and place.** -/
theorem common_group (hp324 : 324 < p) {t η q ℓ c : ℚ} (ht : t ∉ contactSet) (ht1 : t ≠ 1)
    (hη : η = 1 ∨ η = -1) (hℓ0 : ℓ ≠ 0) (hℓ : padicValRat p ℓ = 0) (ha : slopeA η t q ≠ 0)
    (D : Fin 6 → Fin 12 → K0) (hW : ∀ g, slopeW ℓ η t q (D g) ≠ 0)
    (hΘ : slopeTheta ℓ η t q D ≠ 0)
    (hΦ : PoleSoluble (slopeR ℓ η t q / slopeTheta ℓ η t q D ^ 2))
    (hc : c ∈ contactSet) (hk : 0 < padicValRat p (t - c)) (hodd : Odd (padicValRat p (t - c))) :
    ∃ g : Fin 6, ∃ π : Zs, ∃ hπ : Prime π, π ∣ (p : Zs) ∧
      ∀ j, ((testPrec j : ℤ) : WithTop ℤ) ≤ vP π hπ (D g j) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, hone, hR₀v, -, hrodd, hrk⟩ :=
    contact_valuations (p := p) (by omega) ht ht1 hη hℓ0 hℓ ha hc hk hodd
  replace hR₀v : padicValRat p (slopeR₀ η t) = padicValRat p (t - c) := hR₀v
  replace hrodd : Odd (padicValRat p (slopeR ℓ η t q)) := hrodd
  replace hrk : padicValRat p (slopeR ℓ η t q) ≤ padicValRat p (t - c) := hrk
  set k := padicValRat p (t - c) with hkdef
  set R₀ := slopeR₀ η t with hR₀def
  set R := slopeR ℓ η t q with hRdef
  have hR₀0 : R₀ ≠ 0 := by
    intro h; rw [h, padicValRat.zero] at hR₀v; omega
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, padicValRat.zero] at hrodd; obtain ⟨i, hi⟩ := hrodd; omega
  set r := padicValRat p R with hrdef
  have hrodd' : Odd r := hrodd
  have hrk' : r ≤ k := hrk
  have ht10 : (t - 1 : ℚ) ≠ 0 := sub_ne_zero.mpr ht1
  -- valuations at a prime above `p`
  have hvq : ∀ {π : Zs} (hπ : Prime π), π ∣ (p : Zs) → ∀ x : ℚ, vp π (x : K0) = padicValRat p x :=
    fun hπ hπp x => vp_ratCast hp2 hπ hπp x
  -- the factors and their valuations
  set C : Fin 6 → Fin 12 → K0 := fun g j => slopeC η t (D g j) j with hCdef
  set f : Fin 6 → Fin 12 → K0 := fun g j => 1 + (R : K0) * C g j ^ 2 with hfdef
  have hf0 : ∀ g j, f g j ≠ 0 := fun g j =>
    Finset.prod_ne_zero_iff.mp (hW g) j (Finset.mem_univ j)
  have hWf : ∀ g, slopeW ℓ η t q (D g) = ∏ j, f g j := fun g => rfl
  have hfle : ∀ {π : Zs} (hπ : Prime π), π ∣ (p : Zs) → ∀ g j, vp π (f g j) ≤ 0 := by
    intro π hπ hπp g j
    by_cases hC : C g j = 0
    · simp only [hfdef, hC]; simp [vp_one' hπ]
    · rw [hfdef]; dsimp only
      rw [vp_one_add_mul_sq hπ (Rat.cast_ne_zero.mpr hR0) hC (by rw [hvq hπ hπp]; exact hrodd')]
      exact min_le_left _ _
  -- `s(g, π) = v_π(W_g⁻¹) = -Σ_j v_π(f_{gj}) ≥ 0`
  have hWinv : ∀ {π : Zs} (hπ : Prime π), ∀ g,
      vp π (slopeW ℓ η t q (D g))⁻¹ = -∑ j, vp π (f g j) := by
    intro π hπ g
    rw [vp_inv hπ, hWf, vp_prod hπ _ _ fun j _ => hf0 g j]
  -- some group and place have `2 s < r`
  obtain ⟨π₀, hπ₀, hπ₀p⟩ := exists_prime_dvd_natCast p
  have hσ : Prime (star π₀) := prime_star hπ₀
  have hσp : star π₀ ∣ (p : Zs) := star_dvd_natCast hπ₀p
  have hex : ∃ g, ∃ π : Zs, ∃ hπ : Prime π, π ∣ (p : Zs) ∧
      2 * vp π (slopeW ℓ η t q (D g))⁻¹ < r := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    obtain ⟨i, hi⟩ := hrodd'
    have hge : ∀ {π : Zs} (hπ : Prime π), π ∣ (p : Zs) →
        Vge (vP π hπ) (i + 1) (∑ g, (slopeW ℓ η t q (D g))⁻¹) := by
      intro π hπ hπp
      apply Vge.sum_of_le
      intro g _
      have := hcon g π hπ hπp
      exact (le_vP_iff hπ _ _).mpr (Or.inr (by omega))
    set y := ∑ g, (slopeW ℓ η t q (D g))⁻¹ with hy
    have hy0 : y ≠ 0 := by
      intro h0; apply hΘ; rw [slopeTheta, ← hy, h0, map_zero]
    have h1 := ((le_vP_iff hπ₀ y _).mp (hge hπ₀ hπ₀p)).resolve_left hy0
    have h2 := ((le_vP_iff hσ y _).mp (hge hσ hσp)).resolve_left hy0
    have htr := (vp_trace_ge hp2 hπ₀ hπ₀p h1 h2).resolve_left (by rw [hy]; exact hΘ)
    -- the pole input has negative odd valuation
    have hB0 : R / slopeTheta ℓ η t q D ^ 2 ≠ 0 := div_ne_zero hR0 (pow_ne_zero _ hΘ)
    apply pole_obstruction (p := p) hB0 hΦ (by
      simp only [poleS0, Finset.mem_insert, Finset.mem_singleton]; omega)
    rw [padicValRat.div hR0 (pow_ne_zero _ hΘ), padicValRat.pow]
    change i + 1 ≤ padicValRat p (slopeTheta ℓ η t q D) at htr
    refine ⟨by push_cast; omega, ⟨i - padicValRat p (slopeTheta ℓ η t q D), by push_cast; omega⟩⟩
  obtain ⟨g, π, hπ, hπp, hs⟩ := hex
  refine ⟨g, π, hπ, hπp, fun j => ?_⟩
  set s := vp π (slopeW ℓ η t q (D g))⁻¹ with hsdef
  have hs0 : 0 ≤ s := by
    rw [hsdef, hWinv hπ]
    have := Finset.sum_nonpos (s := Finset.univ) fun j _ => hfle hπ hπp g j
    linarith
  by_cases hD : D g j = 0
  · rw [hD, (vP π hπ).map_zero]; exact le_top
  have hden : (R₀ : K0) ^ testPrec j * ((t - 1 : ℚ) : K0) ^ (testPrec j + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Rat.cast_ne_zero.mpr hR₀0)) (pow_ne_zero _ (Rat.cast_ne_zero.mpr ht10))
  have hC0 : C g j ≠ 0 := div_ne_zero hD hden
  set e := vp π (C g j) with he
  -- `4 e ≥ 1 - 3 r`
  have he4 : 1 - 3 * r ≤ 4 * e := by
    have hf := vp_one_add_mul_sq hπ (Rat.cast_ne_zero.mpr hR0) hC0
      (by rw [hvq hπ hπp]; exact hrodd')
    rw [hvq hπ hπp] at hf
    obtain ⟨i, hi⟩ := hrodd'
    by_cases hpos : 0 < r + 2 * e
    · omega
    · have hfj : vp π (f g j) = r + 2 * e := by
        show vp π (1 + (R : K0) * C g j ^ 2) = _
        rw [hf, ← hrdef, ← he]; omega
      have hsum : ∑ j', vp π (f g j') ≤ vp π (f g j) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        have := Finset.sum_nonpos (s := Finset.univ.erase j) fun j' _ => hfle hπ hπp g j'
        linarith
      have : s = -∑ j', vp π (f g j') := by rw [hsdef, hWinv hπ]
      omega
  -- `v_π(D) = e + k_j k`
  have hDeq : D g j = C g j * ((R₀ : K0) ^ testPrec j * ((t - 1 : ℚ) : K0) ^ (testPrec j + 1)) := by
    simp only [hCdef, slopeC, ← hR₀def]
    rw [div_mul_cancel₀ _ hden]
  have hDv : vp π (D g j) = e + testPrec j * k := by
    rw [hDeq, vp_mul hπ hC0 hden,
      vp_mul hπ (pow_ne_zero _ (Rat.cast_ne_zero.mpr hR₀0)) (pow_ne_zero _ (Rat.cast_ne_zero.mpr ht10)),
      vp_pow hπ, vp_pow hπ, hvq hπ hπp, hvq hπ hπp, hR₀v, hone, ← he]
    ring
  rw [vP_apply hπ hD, hDv, WithTop.coe_le_coe]
  have hk1 : 1 ≤ k := hk
  unfold testPrec
  split_ifs <;> push_cast <;> omega

end

end ZInQ
