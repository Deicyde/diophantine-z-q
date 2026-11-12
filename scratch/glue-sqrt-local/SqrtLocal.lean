import Mathlib

/-!
# glue-sqrt-local: the local square-root criterion, `p`-power cyclotomic part

* `cyclotomic_prime_pow_irreducible_padic`: `Φ_{p^{n+1}}` is irreducible over `ℚ_p` (Eisenstein).
* `galEquivUnits`, `finrank_eq_totient`: `Gal(L/ℚ_p) ≅ (ℤ/p^{n+1})ˣ`, `[L:ℚ_p] = φ(p^{n+1})` for any
  `p^{n+1}`-th cyclotomic extension `L` of `ℚ_p`.
* `gal_sqrt_criterion` (`p` odd): a `ℚ/ℤ`-character of `Gal(L/ℚ_p)` is twice a character iff it
  kills `τ₋₁` (`τ₋₁ ζ = ζ⁻¹`, `tauNeg_mul_self`).
* `sqrt_criterion_finite` (every `p`): the same criterion on the finite model
  `(ℤ/p^{k+1})ˣ × ℤ/2f → (ℤ/p^k)ˣ × ℤ/f` of `Gal(ℚ_p(μ_{p^{k+1}m'})/ℚ_p) → Gal(ℚ_p(μ_{p^k m})/ℚ_p)`.
-/

open Polynomial

namespace GlueSqrtLocal

variable (p : ℕ) [hp : Fact p.Prime]

/-- `Φ_{p^{n+1}}(X + 1)` is Eisenstein at the maximal ideal `(p)` of `ℤ_p`. -/
theorem cyclotomic_prime_pow_comp_isEisensteinAt_padicInt (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1)).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
  have hZ := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n
  have hmap : (cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1) =
      ((cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[p]) := by
    simp [map_comp]
  have hne : Ideal.span {(p : ℤ_[p])} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PadicInt.p_nonunit
  rw [hmap]
  refine Monic.isEisensteinAt_of_mem_of_notMem ?_ hne ?_ ?_
  · refine Monic.map _ ?_
    rw [show (X + 1 : ℤ[X]) = X + C 1 by simp]
    refine (cyclotomic.monic _ ℤ).comp (monic_X_add_C 1) fun h => ?_
    rw [natDegree_X_add_C] at h
    exact zero_ne_one h.symm
  · intro i hi
    rw [coeff_map]
    have hi' : i < ((cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)).natDegree := by
      rwa [natDegree_map_eq_of_injective (RingHom.injective_int _)] at hi
    have hm := hZ.mem hi'
    rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    rw [Ideal.mem_span_singleton]
    exact ⟨(c : ℤ_[p]), by rw [hc]; simp⟩
  · rw [coeff_map, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one, zero_add,
      eval_one_cyclotomic_prime_pow]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 : (p : ℤ_[p]) * (1 - p * c) = 0 := by
      simp only [map_natCast] at hc
      linear_combination hc
    rcases mul_eq_zero.mp h1 with h | h
    · exact hp.out.ne_zero (by exact_mod_cast h)
    · apply PadicInt.p_nonunit (p := p)
      exact IsUnit.of_mul_eq_one c (by linear_combination -h)

/-- **`Φ_{p^{n+1}}` is irreducible over `ℚ_p`.** -/
theorem cyclotomic_prime_pow_irreducible_padic (n : ℕ) :
    Irreducible (cyclotomic (p ^ (n + 1)) ℚ_[p]) := by
  have hE := cyclotomic_prime_pow_comp_isEisensteinAt_padicInt p n
  have hmon : ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1)).Monic := by
    rw [show (X + 1 : ℤ_[p][X]) = X + C 1 by simp]
    refine (cyclotomic.monic _ ℤ_[p]).comp (monic_X_add_C 1) fun h => ?_
    rw [natDegree_X_add_C] at h
    exact zero_ne_one h.symm
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)]
    exact PadicInt.prime_p
  have hdeg : 0 < ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1)).natDegree := by
    rw [natDegree_comp, natDegree_cyclotomic]
    simp only [show (X + 1 : ℤ_[p][X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]
    exact Nat.totient_pos.mpr (pow_pos hp.out.pos _)
  have hirr := hE.irreducible hprime hmon.isPrimitive hdeg
  have hirrQ := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirr
  have hmapQ : ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1)).map (algebraMap ℤ_[p] ℚ_[p]) =
      algEquivAevalXAddC (1 : ℚ_[p]) (cyclotomic (p ^ (n + 1)) ℚ_[p]) := by
    rw [map_comp, map_cyclotomic]
    simp [algEquivAevalXAddC, ← comp_eq_aeval]
  rw [hmapQ] at hirrQ
  exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : ℚ_[p])).toMulEquiv).mp hirrQ




/-! Copied verbatim from `scratch/glue-I6-rest/SqrtChar.lean` (glue-I6-rest). -/
/-- `χ : Γ → ℚ/ℤ` is twice a character iff `χ` vanishes on the `2`-torsion `Γ[2]`. -/
theorem exists_half_iff {Γ : Type} [AddCommGroup Γ] (χ : Γ →+ AddCircle (1 : ℚ)) :
    (∃ ψ : Γ →+ AddCircle (1 : ℚ), ∀ g, 2 • ψ g = χ g) ↔ ∀ g : Γ, 2 • g = 0 → χ g = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩ g hg
    rw [← hψ, ← map_nsmul, hg, map_zero]
  · intro h
    let d : Γ →+ Γ :=
      { toFun := fun g => 2 • g, map_zero' := smul_zero 2, map_add' := fun a b => smul_add 2 a b }
    have hker : d.ker ≤ χ.ker := fun g hg => h g (AddMonoidHom.mem_ker.mp hg)
    let χq := QuotientAddGroup.lift d.ker χ hker
    let e := QuotientAddGroup.quotientKerEquivRange d
    let χr : d.range →+ AddCircle (1 : ℚ) := χq.comp e.symm.toAddMonoidHom
    obtain ⟨ψ, hψ⟩ := CharacterModule.dual_surjective_of_injective (R := ℤ)
      d.range.subtype.toIntLinearMap Subtype.val_injective χr
    refine ⟨ψ, fun g => ?_⟩
    have hm : d g ∈ d.range := AddMonoidHom.mem_range.mpr ⟨g, rfl⟩
    have h1 := DFunLike.congr_fun hψ ⟨d g, hm⟩
    have h2 : e.symm ⟨d g, hm⟩ = (g : Γ ⧸ d.ker) := by
      rw [AddEquiv.symm_apply_eq]; rfl
    calc 2 • ψ g = ψ (d g) := (map_nsmul ψ 2 g).symm
      _ = χr ⟨d g, hm⟩ := h1
      _ = χ g := by
        simp only [χr, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h2, χq,
          QuotientAddGroup.lift_mk]


/-- Odd prime powers: `p^k ∣ x² - 1` forces `p^k ∣ x - 1` or `p^k ∣ x + 1`. -/
theorem dvd_sub_or_add_of_dvd_sq_sub_one_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ)
    {x : ℤ} (h : (p : ℤ) ^ k ∣ x ^ 2 - 1) : (p : ℤ) ^ k ∣ x - 1 ∨ (p : ℤ) ^ k ∣ x + 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hfac : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [hfac] at h
  by_cases h1 : (p : ℤ) ∣ x + 1
  · by_cases h2 : (p : ℤ) ∣ x - 1
    · exfalso
      have h3 : (p : ℤ) ∣ 2 := by
        have := dvd_sub h1 h2
        rwa [show x + 1 - (x - 1) = 2 by ring] at this
      have h4 : p ∣ 2 := by exact_mod_cast h3
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
      · exact hp.ne_one h5
      · exact hp2 h5
    · right
      have hc : IsCoprime ((p : ℤ) ^ k) (x - 1) :=
        ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr h2).pow_left
      exact hc.dvd_of_dvd_mul_left h
  · left
    have hc : IsCoprime ((p : ℤ) ^ k) (x + 1) :=
      ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr h1).pow_left
    exact hc.dvd_of_dvd_mul_right h

/-- All primes, losing one power of `p`: `p^{k+1} ∣ x² - 1` forces `p^k ∣ x ∓ 1`. -/
theorem dvd_sub_or_add_of_dvd_sq_sub_one {p : ℕ} (hp : p.Prime) (k : ℕ)
    {x : ℤ} (h : (p : ℤ) ^ (k + 1) ∣ x ^ 2 - 1) : (p : ℤ) ^ k ∣ x - 1 ∨ (p : ℤ) ^ k ∣ x + 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    rcases k with _ | j
    · simp
    have hfac : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [hfac] at h
    -- `x` is odd
    have h2 : (2 : ℤ) ∣ (x - 1) * (x + 1) := dvd_trans (dvd_pow_self (2 : ℤ) (by omega : j + 1 + 1 ≠ 0)) (by exact_mod_cast h)
    have hx : (2 : ℤ) ∣ x - 1 := by
      rcases (Int.prime_two.dvd_or_dvd h2) with h3 | h3
      · exact h3
      · have := dvd_sub h3 (dvd_refl 2)
        rwa [show x + 1 - 2 = x - 1 by ring] at this
    obtain ⟨a, ha⟩ := hx
    have hxa : x + 1 = 2 * (a + 1) := by linarith
    rw [ha, hxa, show (2 * a) * (2 * (a + 1)) = 2 ^ 2 * (a * (a + 1)) by ring] at h
    push_cast at h
    rw [show j + 1 + 1 = 2 + j by ring, pow_add] at h
    have h' : (2 : ℤ) ^ j ∣ a * (a + 1) := (mul_dvd_mul_iff_left (by norm_num)).mp h
    by_cases hev : (2 : ℤ) ∣ a
    · left
      have hc : IsCoprime ((2 : ℤ) ^ j) (a + 1) := by
        refine IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd Int.prime_two.irreducible).mpr ?_)
        intro hd
        have := dvd_sub hd hev
        rw [show a + 1 - a = 1 by ring] at this
        norm_num at this
      have := hc.dvd_of_dvd_mul_right h'
      push_cast
      rw [ha, pow_succ, mul_comm]
      exact mul_dvd_mul_left 2 this
    · right
      have hc : IsCoprime ((2 : ℤ) ^ j) a :=
        ((Irreducible.coprime_iff_not_dvd Int.prime_two.irreducible).mpr hev).pow_left
      have := hc.dvd_of_dvd_mul_left h'
      push_cast
      rw [hxa, pow_succ, mul_comm]
      exact mul_dvd_mul_left 2 this
  · exact dvd_sub_or_add_of_dvd_sq_sub_one_odd hp hp2 k
      (dvd_trans (pow_dvd_pow _ (Nat.le_succ k)) h)


/-- Reduction `(ℤ/p^{k+1})ˣ → (ℤ/p^k)ˣ`. -/
noncomputable def redU (p k : ℕ) : (ZMod (p ^ (k + 1)))ˣ →* (ZMod (p ^ k))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))).toMonoidHom

theorem redU_val (p k : ℕ) (u : (ZMod (p ^ (k + 1)))ˣ) :
    ((redU p k u : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) =
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) u := rfl

theorem redU_neg_one (p k : ℕ) : redU p k (-1) = -1 := by
  ext; rw [redU_val]; simp only [Units.val_neg, Units.val_one, map_neg, map_one]

theorem intCast_eq_one_or_neg_one {n : ℕ} {x : ℤ} (h : (n : ℤ) ∣ x - 1 ∨ (n : ℤ) ∣ x + 1) :
    (x : ZMod n) = 1 ∨ (x : ZMod n) = -1 := by
  rcases h with h | h
  · left
    have : ((x - 1 : ℤ) : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    push_cast at this
    exact sub_eq_zero.mp this
  · right
    have : ((x + 1 : ℤ) : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this

theorem dvd_of_sq_eq_one {n : ℕ} (u : (ZMod n)ˣ) (hu : u ^ 2 = 1) {x : ℤ}
    (hx : (x : ZMod n) = u) : (n : ℤ) ∣ x ^ 2 - 1 := by
  have : ((x ^ 2 - 1 : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [hx, ← Units.val_pow_eq_pow_val, hu]
    simp
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

/-- For odd `p`, the only square roots of `1` in `(ℤ/p^k)ˣ` are `±1`. -/
theorem units_sq_eq_one_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ)
    (u : (ZMod (p ^ k))ˣ) (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  obtain ⟨x, hx⟩ := ZMod.intCast_surjective (u : ZMod (p ^ k))
  have h := dvd_of_sq_eq_one u hu hx
  push_cast at h
  have h2 := intCast_eq_one_or_neg_one (n := p ^ k) (x := x)
    (by push_cast; exact dvd_sub_or_add_of_dvd_sq_sub_one_odd hp hp2 k h)
  rw [hx] at h2
  rcases h2 with h2 | h2
  · left; ext; simpa using h2
  · right; ext; simpa using h2

/-- For every prime `p`, a square root of `1` in `(ℤ/p^{k+1})ˣ` reduces to `±1` in `(ℤ/p^k)ˣ`. -/
theorem redU_sq_eq_one {p : ℕ} (hp : p.Prime) (k : ℕ) (u : (ZMod (p ^ (k + 1)))ˣ)
    (hu : u ^ 2 = 1) : redU p k u = 1 ∨ redU p k u = -1 := by
  obtain ⟨x, hx⟩ := ZMod.intCast_surjective (u : ZMod (p ^ (k + 1)))
  have h := dvd_of_sq_eq_one u hu hx
  push_cast at h
  have h2 := intCast_eq_one_or_neg_one (n := p ^ k) (x := x)
    (by push_cast; exact dvd_sub_or_add_of_dvd_sq_sub_one hp k h)
  have hred : ((redU p k u : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) = (x : ZMod (p ^ k)) := by
    rw [redU_val, ← hx, map_intCast]
  rcases h2 with h2 | h2
  · left; ext; rw [hred, h2]; simp
  · right; ext; rw [hred, h2]; simp

/-- `2a = 0` in `ℤ/2f` forces `a ↦ 0` in `ℤ/f`. -/
theorem cast_eq_zero_of_two_nsmul (f : ℕ) (a : ZMod (2 * f)) (ha : 2 • a = 0) :
    ZMod.castHom (dvd_mul_left f 2) (ZMod f) a = 0 := by
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective a
  rw [map_intCast]
  have h : (((2 * x : ℤ)) : ZMod (2 * f)) = 0 := by push_cast; rw [← ha]; simp [two_mul]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  push_cast at h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h

/-- The finite model `(ℤ/p^{k+1})ˣ × ℤ/2f` of a quotient of `G_{ℚ_p}^{ab}`, and its quotient
`(ℤ/p^k)ˣ × ℤ/f`. -/
abbrev Gbig (p k f : ℕ) := Additive (ZMod (p ^ (k + 1)))ˣ × ZMod (2 * f)
abbrev Gsmall (p k f : ℕ) := Additive (ZMod (p ^ k))ˣ × ZMod f

noncomputable def proj (p k f : ℕ) : Gbig p k f →+ Gsmall p k f :=
  (MonoidHom.toAdditive (redU p k)).prodMap
    (ZMod.castHom (dvd_mul_left f 2) (ZMod f)).toAddMonoidHom

theorem proj_apply (p k f : ℕ) (u : Additive (ZMod (p ^ (k + 1)))ˣ) (a : ZMod (2 * f)) :
    proj p k f (u, a) = (Additive.ofMul (redU p k (Additive.toMul u)),
      ZMod.castHom (dvd_mul_left f 2) (ZMod f) a) := rfl

/-- The image of the `2`-torsion of `(ℤ/p^{k+1})ˣ × ℤ/2f` in `(ℤ/p^k)ˣ × ℤ/f` is
`{0, (-1, 0)}`. -/
theorem proj_two_torsion {p : ℕ} (hp : p.Prime) (k f : ℕ) (g : Gbig p k f) (hg : 2 • g = 0) :
    proj p k f g = 0 ∨ proj p k f g = (Additive.ofMul (-1), 0) := by
  obtain ⟨u, a⟩ := g
  rw [Prod.ext_iff] at hg
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero] at hg
  obtain ⟨hu, ha⟩ := hg
  have hu' : (Additive.toMul u) ^ 2 = 1 := by
    have := congrArg Additive.toMul hu
    simpa using this
  have hb := cast_eq_zero_of_two_nsmul f a ha
  rcases redU_sq_eq_one hp k _ hu' with h | h
  · left
    rw [proj_apply, Prod.ext_iff]
    exact ⟨by simpa using congrArg Additive.ofMul h, hb⟩
  · right
    rw [proj_apply, Prod.ext_iff]
    exact ⟨by simpa using congrArg Additive.ofMul h, hb⟩

/-- **Square-root criterion on the finite model, every prime `p`.** A character `χ` of
`(ℤ/p^k)ˣ × ℤ/f` becomes twice a character after pulling back to `(ℤ/p^{k+1})ˣ × ℤ/2f` iff
`χ(-1, 0) = 0`. -/
theorem sqrt_criterion_finite {p : ℕ} (hp : p.Prime) (k f : ℕ)
    (χ : Gsmall p k f →+ AddCircle (1 : ℚ)) :
    (∃ ψ : Gbig p k f →+ AddCircle (1 : ℚ), ∀ g, 2 • ψ g = χ (proj p k f g)) ↔
      χ (Additive.ofMul (-1), 0) = 0 := by
  rw [show (∃ ψ : Gbig p k f →+ AddCircle (1 : ℚ), ∀ g, 2 • ψ g = χ (proj p k f g)) ↔
      (∃ ψ : Gbig p k f →+ AddCircle (1 : ℚ), ∀ g, 2 • ψ g = (χ.comp (proj p k f)) g) from
      Iff.rfl, exists_half_iff]
  constructor
  · intro h
    have h1 := h (Additive.ofMul (-1), 0) (by
      rw [Prod.ext_iff]
      refine ⟨?_, by simp⟩
      change Additive.ofMul ((-1 : (ZMod (p ^ (k + 1)))ˣ) ^ 2) = Additive.ofMul 1
      simp)
    have h2 : proj p k f (Additive.ofMul (-1), 0) = (Additive.ofMul (-1), 0) := by
      rw [proj_apply, Prod.ext_iff]
      refine ⟨?_, by simp⟩
      change Additive.ofMul (redU p k (-1)) = _
      rw [redU_neg_one]
    simpa [h2] using h1
  · intro h g hg
    rcases proj_two_torsion hp k f g hg with h1 | h1
    · simp [h1]
    · simp [h1, h]


/-! ## The Galois group of a `p^{n+1}`-th cyclotomic extension of `ℚ_p` -/

section Gal

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (L : Type) [Field L] [Algebra ℚ_[p] L]
  [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] L]

/-- `Gal(L/ℚ_p) ≃* (ℤ/p^{n+1})ˣ`, `σ ↦ a` with `σ ζ = ζ^a`. -/
noncomputable def galEquivUnits : Gal(L/ℚ_[p]) ≃* (ZMod (p ^ (n + 1)))ˣ :=
  IsCyclotomicExtension.autEquivPow L (cyclotomic_prime_pow_irreducible_padic p n)

/-- `[L : ℚ_p] = φ(p^{n+1})`. -/
theorem finrank_eq_totient : Module.finrank ℚ_[p] L = (p ^ (n + 1)).totient :=
  IsCyclotomicExtension.finrank L (cyclotomic_prime_pow_irreducible_padic p n)

/-- The element `τ₋₁ ∈ Gal(L/ℚ_p)` corresponding to `-1 ∈ (ℤ/p^{n+1})ˣ`. -/
noncomputable def tauNeg : Gal(L/ℚ_[p]) := (galEquivUnits p n L).symm (-1)

/-- `τ₋₁` acts by `ζ ↦ ζ⁻¹` on all `p^{n+1}`-th roots of unity of `L`. -/
theorem tauNeg_mul_self (x : L) (hx : x ^ (p ^ (n + 1)) = 1) : tauNeg p n L x * x = 1 := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ (n + 1)) ℚ_[p] L
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  have h1 : hζ.autToPow ℚ_[p] (tauNeg p n L) = -1 := by
    have := (galEquivUnits p n L).apply_symm_apply (-1)
    exact this
  have h2 := hζ.autToPow_spec ℚ_[p] (tauNeg p n L)
  rw [h1] at h2
  rw [map_pow, ← h2, ← pow_mul, ← pow_add]
  rw [hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id, Units.val_neg, Units.val_one]
  ring

theorem tauNeg_sq : tauNeg p n L ^ 2 = 1 := by
  apply (galEquivUnits p n L).injective
  rw [map_pow, tauNeg, MulEquiv.apply_symm_apply, map_one]
  simp

/-- `Gal(L/ℚ_p)` is commutative (it embeds in `(ℤ/p^{n+1})ˣ`). -/
noncomputable abbrev galCommGroup : CommGroup Gal(L/ℚ_[p]) :=
  { (inferInstance : Group Gal(L/ℚ_[p])) with
    mul_comm := fun a b => (galEquivUnits p n L).injective (by rw [map_mul, map_mul, mul_comm]) }

/-- **Square-root criterion for `Gal(ℚ_p(μ_{p^{n+1}})/ℚ_p)`, `p` odd.** A character `χ` of the
Galois group (values in `ℚ/ℤ`) is twice a character iff `χ(τ₋₁) = 0`. -/
theorem gal_sqrt_criterion (hp2 : p ≠ 2)
    (χ : Additive Gal(L/ℚ_[p]) →+ AddCircle (1 : ℚ)) :
    (∃ ψ : Additive Gal(L/ℚ_[p]) →+ AddCircle (1 : ℚ), ∀ g, 2 • ψ g = χ g) ↔
      χ (Additive.ofMul (tauNeg p n L)) = 0 := by
  letI := galCommGroup p n L
  refine (exists_half_iff χ).trans ?_
  constructor
  · intro h
    apply h
    change Additive.ofMul (tauNeg p n L ^ 2) = Additive.ofMul 1
    rw [tauNeg_sq]
  · intro h g hg
    have hσ : (Additive.toMul g) ^ 2 = 1 := by
      have := congrArg Additive.toMul hg
      simpa using this
    have he : (galEquivUnits p n L (Additive.toMul g)) ^ 2 = 1 := by
      rw [← map_pow, hσ, map_one]
    rcases units_sq_eq_one_odd hp.out hp2 (n + 1) _ he with h1 | h1
    · have : Additive.toMul g = 1 := by
        apply (galEquivUnits p n L).injective; rw [h1, map_one]
      have hg0 : g = 0 := congrArg Additive.ofMul this
      rw [hg0, map_zero]
    · have : Additive.toMul g = tauNeg p n L := by
        rw [tauNeg, ← h1, MulEquiv.symm_apply_apply]
      have hg0 : g = Additive.ofMul (tauNeg p n L) := congrArg Additive.ofMul this
      rw [hg0, h]

/-- The action of `Gal(L/ℚ_p)` on `μ_{p^n}` (`L` of level `p^{n+1}`), as a map to `(ℤ/p^n)ˣ`. -/
noncomputable def actLower : Additive Gal(L/ℚ_[p]) →+ Additive (ZMod (p ^ n))ˣ :=
  MonoidHom.toAdditive ((redU p n).comp (galEquivUnits p n L).toMonoidHom)

theorem actLower_apply (g : Gal(L/ℚ_[p])) :
    actLower p n L (Additive.ofMul g) = Additive.ofMul (redU p n (galEquivUnits p n L g)) := rfl

/-- `actLower` describes the action on `p^n`-th roots of unity: `g x = x^a` with
`a = actLower g`. -/
theorem apply_eq_pow_actLower (g : Gal(L/ℚ_[p])) (x : L) (hx : x ^ (p ^ n) = 1) :
    g x = x ^ ((redU p n (galEquivUnits p n L g) : ZMod (p ^ n)).val) := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ (n + 1)) ℚ_[p] L
  have hx' : x ^ (p ^ (n + 1)) = 1 := by
    rw [pow_succ, pow_mul, hx, one_pow]
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx'
  have h2 := hζ.autToPow_spec ℚ_[p] g
  set a := ((galEquivUnits p n L g : (ZMod (p ^ (n + 1)))ˣ) : ZMod (p ^ (n + 1)))
  have ha : (hζ.autToPow ℚ_[p] g : ZMod (p ^ (n + 1))) = a := rfl
  rw [ha] at h2
  have step1 : g ((IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] L) ^ i) =
      ((IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] L) ^ i) ^ a.val := by
    rw [map_pow, ← h2, ← pow_mul, ← pow_mul, mul_comm]
  rw [step1]
  have hred : ∀ u : ℕ, ((IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] L) ^ i) ^ u =
      ((IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] L) ^ i) ^ (u % p ^ n) := fun u => by
    conv_lhs => rw [← Nat.mod_add_div u (p ^ n)]
    rw [pow_add, pow_mul, hx, one_pow, mul_one]
  rw [hred a.val]
  conv_rhs => rw [hred]
  congr 1
  have hb : ((redU p n (galEquivUnits p n L g) : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) =
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) a := rfl
  have : ((a.val : ℕ) : ZMod (p ^ n)) =
      (((redU p n (galEquivUnits p n L g) : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)).val : ZMod (p ^ n)) := by
    rw [ZMod.natCast_zmod_val, hb, ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp this

/-- **Square-root criterion on `Gal(ℚ_p(μ_{p^{n+1}})/ℚ_p)`, every prime `p` (including `2`).**
A character `χ₀` of `(ℤ/p^n)ˣ`, pulled back along the action on `μ_{p^n}`, is twice a character
of `Gal(L/ℚ_p)` iff `χ₀(−1) = 0`. -/
theorem gal_sqrt_criterion_lower (χ₀ : Additive (ZMod (p ^ n))ˣ →+ AddCircle (1 : ℚ)) :
    (∃ ψ : Additive Gal(L/ℚ_[p]) →+ AddCircle (1 : ℚ),
        ∀ g, 2 • ψ g = χ₀ (actLower p n L g)) ↔ χ₀ (Additive.ofMul (-1)) = 0 := by
  letI := galCommGroup p n L
  refine (exists_half_iff (χ₀.comp (actLower p n L))).trans ?_
  constructor
  · intro h
    have h1 := h (Additive.ofMul (tauNeg p n L)) (by
      change Additive.ofMul (tauNeg p n L ^ 2) = Additive.ofMul 1
      rw [tauNeg_sq])
    rw [AddMonoidHom.comp_apply, actLower_apply, tauNeg, MulEquiv.apply_symm_apply,
      redU_neg_one] at h1
    exact h1
  · intro h g hg
    have hσ : (Additive.toMul g) ^ 2 = 1 := by
      have := congrArg Additive.toMul hg
      simpa using this
    have he : (galEquivUnits p n L (Additive.toMul g)) ^ 2 = 1 := by
      rw [← map_pow, hσ, map_one]
    rw [AddMonoidHom.comp_apply, show g = Additive.ofMul (Additive.toMul g) from rfl,
      actLower_apply]
    rcases redU_sq_eq_one hp.out n _ he with h1 | h1
    · rw [h1]; exact map_zero χ₀
    · rw [h1]; exact h

end Gal

end GlueSqrtLocal

#print axioms GlueSqrtLocal.cyclotomic_prime_pow_irreducible_padic
#print axioms GlueSqrtLocal.sqrt_criterion_finite
#print axioms GlueSqrtLocal.finrank_eq_totient
#print axioms GlueSqrtLocal.tauNeg_mul_self
#print axioms GlueSqrtLocal.gal_sqrt_criterion
#print axioms GlueSqrtLocal.gal_sqrt_criterion_lower
#print axioms GlueSqrtLocal.apply_eq_pow_actLower
