/-! # Fold of t30-adelic, part T30 (leaf-adopt3)
Source: scratch/t30-adelic/SqrtCrit.lean. It imports `ZInQKernel.HDecomp.Sqrt.Disj` (which imports
`Sqrt.SqrtLocal`, `Conductor.SqrtChar`, `Conductor.I6Base`) and `ZInQKernel.HDecomp.Descent.B2Glue`.
`GlueDescent.B2Q` (B2Glue) and `PkgI6.LocalKroneckerWeber` (I6Base) are already in this file
(textually identical). The namespaces `GlueI6Rest`, `GlueSqrtLocal`, `GlueSqrtDisj` are NOT, so the
three kernel files `Conductor/SqrtChar.lean`, `Sqrt/SqrtLocal.lean`, `Sqrt/Disj.lean` are copied
below verbatim (imports dropped), each in its own section (their top-level `open`s are file-scoped
there). The G1-adelic part (Adelic.lean, G1Count.lean) is NOT folded. -/

section T30Sec

section T30KernelSqrtCharSec
/-! ### Copied from `ZInQKernel/HDecomp/Conductor/SqrtChar.lean` (kernel; namespace `GlueI6Rest`). -/

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-I6-rest/SqrtChar.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-I6-rest: the group-theoretic core of B2's square-root criterion

pkg-I6 (§2, B2, glue item 2): "a character of a profinite abelian group `Γ` is a square iff it
kills `Γ[2]`".  For characters with values in `ℚ/ℤ` (written additively; finite-order characters
of a profinite group take values in `μ_∞ ≅ ℚ/ℤ`) and any abelian group `Γ`, this is proved here
from the divisibility (Baer injectivity) of `ℚ/ℤ`, Mathlib's
`CharacterModule.dual_surjective_of_injective`.  Applied to a finite quotient `Γ` of `G_{ℚ_p}^{ab}`
through which `χ` factors, it gives a square root on `Γ`, hence a continuous one on `G_{ℚ_p}`.
-/

namespace GlueI6Rest

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

end GlueI6Rest

end T30KernelSqrtCharSec

section T30KernelSqrtLocalSec
/-! ### Copied from `ZInQKernel/HDecomp/Sqrt/SqrtLocal.lean` (kernel; namespace `GlueSqrtLocal`). -/

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-sqrt-local/SqrtLocal.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


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




/-! Proved by `GlueI6Rest.exists_half_iff` (`Conductor/SqrtChar.lean`). -/
/-- `χ : Γ → ℚ/ℤ` is twice a character iff `χ` vanishes on the `2`-torsion `Γ[2]`. -/
theorem exists_half_iff {Γ : Type} [AddCommGroup Γ] (χ : Γ →+ AddCircle (1 : ℚ)) :
    (∃ ψ : Γ →+ AddCircle (1 : ℚ), ∀ g, 2 • ψ g = χ g) ↔ ∀ g : Γ, 2 • g = 0 → χ g = 0 :=
  GlueI6Rest.exists_half_iff χ


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
    have h2 : (2 : ℤ) ∣ (x - 1) * (x + 1) := dvd_trans (dvd_pow_self (2 : ℤ) (by omega : j + 1 + 1 ≠
        0)) (by exact_mod_cast h)
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
        refine IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd Int.prime_two.irreducible).mpr
            ?_)
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
      (((redU p n (galEquivUnits p n L g) : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)).val : ZMod (p ^ n)) :=
          by
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

end T30KernelSqrtLocalSec

section T30KernelDisjSec
/-! ### Copied from `ZInQKernel/HDecomp/Sqrt/Disj.lean` (kernel; namespaces `GlueSqrtLocal`,
`GlueSqrtDisj`). -/

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-sqrt-disj/Disj.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


open Polynomial IsLocalRing
open scoped Pointwise

namespace GlueSqrtLocal

variable (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

/-! ### Locality of the integral closure (spectral norm) -/

/-- `y ∈ L` is integral over `ℤ_p` iff its spectral norm is at most `1`. -/
theorem isIntegral_iff_spectralNorm_le_one (y : L) :
    IsIntegral ℤ_[p] y ↔ spectralNorm ℚ_[p] L y ≤ 1 := by
  have hyQ : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

local notation "N" => spectralNorm ℚ_[p] L

theorem spectralNorm_mul' (x y : L) : N (x * y) = N x * N y :=
  (spectralMulAlgNorm ℚ_[p] L).map_mul x y

/-- **The integral closure of `ℤ_p` in a finite extension `L` of `ℚ_p` is a local ring.** -/
theorem isLocalRing_integralClosure : IsLocalRing (integralClosure ℤ_[p] L) := by
  have hle : ∀ x : integralClosure ℤ_[p] L, N (x : L) ≤ 1 := fun x =>
    (isIntegral_iff_spectralNorm_le_one p L x).mp x.2
  have hunit : ∀ x : integralClosure ℤ_[p] L, IsUnit x ↔ N (x : L) = 1 := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      have h1 : N ((u : integralClosure ℤ_[p] L) : L) * N (((u⁻¹ : _ˣ) : integralClosure ℤ_[p] L) :
          L)
          = 1 := by
        rw [← spectralNorm_mul', ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one,
          spectralNorm_one]
      have a1 := hle u
      have a2 := hle (u⁻¹ : _ˣ)
      have b1 := spectralNorm_nonneg (K := ℚ_[p]) ((u : integralClosure ℤ_[p] L) : L)
      have b2 := spectralNorm_nonneg (K := ℚ_[p]) (((u⁻¹ : _ˣ) : integralClosure ℤ_[p] L) : L)
      nlinarith
    · intro h
      have hx0 : (x : L) ≠ 0 := by
        intro h0; rw [h0, spectralNorm_zero] at h; exact zero_ne_one h
      have hinv : N ((x : L)⁻¹) = 1 := by
        have := spectralNorm_mul' p L (x : L) (x : L)⁻¹
        rw [mul_inv_cancel₀ hx0, spectralNorm_one, h, one_mul] at this
        exact this.symm
      have hint : IsIntegral ℤ_[p] ((x : L)⁻¹) :=
        (isIntegral_iff_spectralNorm_le_one p L _).mpr hinv.le
      refine IsUnit.of_mul_eq_one (⟨_, hint⟩ : integralClosure ℤ_[p] L) ?_
      apply Subtype.ext
      simp [hx0]
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, hunit] at ha hb ⊢
  have ha' : N (a : L) < 1 := lt_of_le_of_ne (hle a) ha
  have hb' : N (b : L) < 1 := lt_of_le_of_ne (hle b) hb
  have := isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := L) (a : L) (b : L)
  rw [Subalgebra.coe_add]
  intro hab
  rw [hab] at this
  exact absurd this (not_le.mpr (max_lt ha' hb'))


/-- `ℤ_p/(p)` has `p` elements. -/
theorem card_quotient_maximalIdeal : Nat.card (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) = p := by
  rw [← PadicInt.ker_toZMod]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZMod (p := p)))).toEquiv]
  simp

/-- **Frobenius in a finite Galois extension of `ℚ_p`.** There is `σ ∈ Gal(L/ℚ_p)` with
`σ ζ = ζ^p` for every root of unity `ζ ∈ L` of order prime to `p`. -/
theorem exists_frobenius :
    ∃ σ : Gal(L/ℚ_[p]), ∀ (m : ℕ), ¬ p ∣ m → ∀ ζ : L, ζ ^ m = 1 → σ ζ = ζ ^ p := by
  let S := integralClosure ℤ_[p] L
  have : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension ℚ_[p] L
  have : IsGaloisGroup Gal(L/ℚ_[p]) ℤ_[p] S :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ_[p]) ℤ_[p] S ℚ_[p] L
  have : Module.Finite ℤ_[p] S := IsIntegralClosure.finite ℤ_[p] ℚ_[p] L S
  have hinjL : Function.Injective (algebraMap ℤ_[p] L) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] L]
    exact (algebraMap ℚ_[p] L).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have : FaithfulSMul ℤ_[p] S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinjL
    rw [IsScalarTower.algebraMap_apply ℤ_[p] S L, h, ← IsScalarTower.algebraMap_apply]
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S)
    (maximalIdeal ℤ_[p])
  have hunder : Q.under ℤ_[p] = maximalIdeal ℤ_[p] := (Ideal.liesOver_iff _ _).mp hQ |>.symm
  have : Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) := by
    rw [hunder]
    exact Nat.finite_of_card_ne_zero (by rw [card_quotient_maximalIdeal p]; exact hp.out.ne_zero)
  have : Module.Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) (S ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have : Finite (S ⧸ Q) := Module.finite_of_finite (ℤ_[p] ⧸ Q.under ℤ_[p])
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ_[p] Gal(L/ℚ_[p]) Q
  refine ⟨σ, fun m hm ζ hζ => ?_⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hζS : IsIntegral ℤ_[p] ζ := ⟨X ^ m - C 1, monic_X_pow_sub_C 1 hm0, by simp [hζ]⟩
  let z : S := ⟨ζ, hζS⟩
  have hz : z ^ m = 1 := Subtype.ext (by simp [z, hζ])
  have hmQ : (m : S) ∉ Q := by
    intro h
    have h1 : (m : ℤ_[p]) ∈ Q.under ℤ_[p] := by
      rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact h
    rw [hunder, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast,
      ZMod.natCast_eq_zero_iff] at h1
    exact hm h1
  have key := hσ.apply_of_pow_eq_one hz hmQ
  rw [hunder, card_quotient_maximalIdeal p] at key
  have := congrArg (fun s : S => (s : L)) key
  simp only [SubmonoidClass.coe_pow, z] at this
  exact this

/-- Two `m`-th roots of unity congruent modulo a prime `Q` with `m ∉ Q` are equal. -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) {m : ℕ}
    {x y : R} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ Q) (hm : (m : R) ∉ Q) :
    x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)) = 0 := by
    have := geom_sum₂_mul x y m
    rw [hx, hy, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have h2 : Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q y := Ideal.Quotient.eq.mpr hxy
  have h3 := congrArg (Ideal.Quotient.mk Q) h1
  simp only [map_sum, map_mul, map_pow, h2, map_zero] at h3
  have h4 : ∀ i ∈ Finset.range m, (Ideal.Quotient.mk Q y) ^ i * (Ideal.Quotient.mk Q y) ^ (m - 1 -
      i)
      = (Ideal.Quotient.mk Q y) ^ (m - 1) := fun i hi => by
    rw [← pow_add]; congr 1; have := Finset.mem_range.mp hi; omega
  rw [Finset.sum_congr rfl h4, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
  have h5 : (Ideal.Quotient.mk Q y) ^ (m - 1) * Ideal.Quotient.mk Q y = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), ← map_pow, hy, map_one]
  have h6 : (m : R ⧸ Q) = 0 := by
    have := congrArg (· * Ideal.Quotient.mk Q y) h3
    simp only [zero_mul, mul_assoc, h5, mul_one] at this
    exact this
  apply hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h6

attribute [local instance] Ideal.Quotient.field in
/-- **Every element of `Gal(L/ℚ_p)` acts as a power of Frobenius on prime-to-`p` roots of
unity**, provided the integral closure of `ℤ_p` in `L` is local (true for every finite `L/ℚ_p`;
not proved here). -/
theorem pow_frobenius_of_isLocalRing (hloc : IsLocalRing (integralClosure ℤ_[p] L))
    (τ : Gal(L/ℚ_[p])) :
    ∃ n : ℕ, ∀ m : ℕ, ¬ p ∣ m → ∀ ζ : L, ζ ^ m = 1 → τ ζ = ζ ^ (p ^ n) := by
  let S := integralClosure ℤ_[p] L
  have : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension ℚ_[p] L
  have : IsGaloisGroup Gal(L/ℚ_[p]) ℤ_[p] S :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ_[p]) ℤ_[p] S ℚ_[p] L
  have : Module.Finite ℤ_[p] S := IsIntegralClosure.finite ℤ_[p] ℚ_[p] L S
  have hinjL : Function.Injective (algebraMap ℤ_[p] L) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] L]
    exact (algebraMap ℚ_[p] L).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have : FaithfulSMul ℤ_[p] S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinjL
    rw [IsScalarTower.algebraMap_apply ℤ_[p] S L, h, ← IsScalarTower.algebraMap_apply]
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S)
    (maximalIdeal ℤ_[p])
  have hunder : Q.under ℤ_[p] = maximalIdeal ℤ_[p] := (Ideal.liesOver_iff _ _).mp hQ |>.symm
  have : Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) := by
    rw [hunder]
    exact Nat.finite_of_card_ne_zero (by rw [card_quotient_maximalIdeal p]; exact hp.out.ne_zero)
  have : Module.Finite (ℤ_[p] ⧸ Q.under ℤ_[p]) (S ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have : Finite (S ⧸ Q) := Module.finite_of_finite (ℤ_[p] ⧸ Q.under ℤ_[p])
  have hQeq : Q = maximalIdeal S := IsLocalRing.eq_maximalIdeal hQmax
  have hstab : τ ∈ MulAction.stabilizer Gal(L/ℚ_[p]) Q := by
    rw [MulAction.mem_stabilizer_iff, hQeq]
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, IsLocalRing.mem_maximalIdeal,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
    exact isUnit_map_iff (MulSemiringAction.toRingEquiv Gal(L/ℚ_[p]) S τ⁻¹) x
  have : (Q.under ℤ_[p]).IsMaximal := by rw [hunder]; infer_instance
  let φ := Ideal.Quotient.stabilizerHom Q (Q.under ℤ_[p]) Gal(L/ℚ_[p]) ⟨τ, hstab⟩
  have : Fintype (ℤ_[p] ⧸ Q.under ℤ_[p]) := Fintype.ofFinite _
  obtain ⟨⟨n, _hnlt⟩, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ℤ_[p] ⧸ Q.under ℤ_[p]) (S ⧸ Q)).2 φ
  have hcard : Fintype.card (ℤ_[p] ⧸ Q.under ℤ_[p]) = p := by
    rw [Fintype.card_eq_nat_card, Nat.card_congr (Ideal.quotEquivOfEq hunder).toEquiv,
      card_quotient_maximalIdeal p]
  refine ⟨n, fun m hm ζ hζ => ?_⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hζS : IsIntegral ℤ_[p] ζ := ⟨X ^ m - C 1, monic_X_pow_sub_C 1 hm0, by simp [hζ]⟩
  let z : S := ⟨ζ, hζS⟩
  have hz : z ^ m = 1 := Subtype.ext (by simp [z, hζ])
  have hmQ : (m : S) ∉ Q := by
    intro h
    have h1 : (m : ℤ_[p]) ∈ Q.under ℤ_[p] := by
      rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact h
    rw [hunder, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast,
      ZMod.natCast_eq_zero_iff] at h1
    exact hm h1
  have h1 : Ideal.Quotient.mk Q (τ • z) = Ideal.Quotient.mk Q (z ^ (p ^ n)) := by
    have := congrArg (fun f => f (Ideal.Quotient.mk Q z)) hn
    simp only at this
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hcard] at this
    beta_reduce at this
    rw [map_pow, this]
    rfl
  have hτz : (τ • z) ^ m = 1 := by rw [← smul_pow', hz, smul_one]
  have hzp : (z ^ (p ^ n)) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have h2 := eq_of_pow_eq_one_of_sub_mem Q hτz hzp (Ideal.Quotient.eq.mp h1) hmQ
  have := congrArg (fun s : S => (s : L)) h2
  simp only [SubmonoidClass.coe_pow, z] at this
  exact this

/-- If `σ ζ = ζ^k` for a primitive `m`-th root `ζ`, then `autToPow σ = k` in `ZMod m`. -/
theorem autToPow_eq_of_apply {K F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ} [NeZero m]
    {ζ : F} (hζ : IsPrimitiveRoot ζ m) (σ : Gal(F/K)) (k : ℕ) (h : σ ζ = ζ ^ k) :
    ((hζ.autToPow K σ : (ZMod m)ˣ) : ZMod m) = k := by
  have h1 := hζ.autToPow_spec K σ
  rw [h] at h1
  have hk : ζ ^ k = ζ ^ (k % m) := by
    conv_lhs => rw [← Nat.mod_add_div k m]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  rw [hk] at h1
  have h2 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos m)) h1
  rw [← ZMod.natCast_zmod_val ((hζ.autToPow K σ : (ZMod m)ˣ) : ZMod m), h2, ZMod.natCast_mod]

/-- **The unramified Galois group.** For `p ∤ m` and an `m`-th cyclotomic extension `L` of `ℚ_p`,
the image of `Gal(L/ℚ_p) ↪ (ℤ/m)ˣ` (`σ ζ = ζ^a`) is the cyclic group generated by `p`, provided the
integral closure of `ℤ_p` in `L` is local. -/
theorem range_autToPow_eq_zpowers (hloc : IsLocalRing (integralClosure ℤ_[p] L)) {m : ℕ}
    [NeZero m] (hm : ¬ p ∣ m) {ζ : L} (hζ : IsPrimitiveRoot ζ m) :
    (hζ.autToPow ℚ_[p]).range =
      Subgroup.zpowers (ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)) := by
  set u := ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)
  apply le_antisymm
  · rintro _ ⟨τ, rfl⟩
    obtain ⟨n, hn⟩ := pow_frobenius_of_isLocalRing p L hloc τ
    refine ⟨n, ?_⟩
    ext
    rw [autToPow_eq_of_apply hζ τ (p ^ n) (hn m hm ζ hζ.pow_eq_one)]
    simp [u]
  · rw [Subgroup.zpowers_le]
    obtain ⟨σ, hσ⟩ := exists_frobenius p L
    refine ⟨σ, ?_⟩
    ext
    rw [autToPow_eq_of_apply hζ σ p (hσ m hm ζ hζ.pow_eq_one)]
    simp [u]

/-- **The unramified Galois group, unconditionally.** For `p ∤ m` and a primitive `m`-th root of
unity `ζ` in a finite Galois extension `L/ℚ_p`, the image of `Gal(L/ℚ_p) → (ℤ/m)ˣ` is `⟨p⟩`. -/
theorem range_autToPow_eq_zpowers' {m : ℕ} [NeZero m] (hm : ¬ p ∣ m) {ζ : L}
    (hζ : IsPrimitiveRoot ζ m) :
    (hζ.autToPow ℚ_[p]).range =
      Subgroup.zpowers (ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)) :=
  range_autToPow_eq_zpowers p L (isLocalRing_integralClosure p L) hm hζ

/-- Every element of `Gal(L/ℚ_p)` acts as a power of Frobenius on prime-to-`p` roots of unity. -/
theorem pow_frobenius (τ : Gal(L/ℚ_[p])) :
    ∃ n : ℕ, ∀ m : ℕ, ¬ p ∣ m → ∀ ζ : L, ζ ^ m = 1 → τ ζ = ζ ^ (p ^ n) :=
  pow_frobenius_of_isLocalRing p L (isLocalRing_integralClosure p L) τ

/-- **Degree of the unramified cyclotomic extension.** If `p ∤ m` and `L` is an `m`-th cyclotomic
extension of `ℚ_p`, then `[L : ℚ_p] = ord_m(p)`, and `Gal(L/ℚ_p) ≃* ⟨p⟩ ⊆ (ℤ/m)ˣ`. -/
theorem finrank_eq_orderOf {m : ℕ} [NeZero m] (hm : ¬ p ∣ m)
    [IsCyclotomicExtension {m} ℚ_[p] L] :
    Module.finrank ℚ_[p] L =
      orderOf (ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm)) := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ_[p] L
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_zpowers, ← range_autToPow_eq_zpowers' p L hm hζ]
  exact (Nat.card_congr (Equiv.ofInjective _ (hζ.autToPow_injective ℚ_[p])))

/-- `Gal(L/ℚ_p)` is cyclic for an `m`-th cyclotomic extension with `p ∤ m`. -/
theorem isCyclic_gal {m : ℕ} [NeZero m] (hm : ¬ p ∣ m) [IsCyclotomicExtension {m} ℚ_[p] L] :
    IsCyclic Gal(L/ℚ_[p]) := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ_[p] L
  have e := MonoidHom.ofInjective (hζ.autToPow_injective ℚ_[p])
  rw [range_autToPow_eq_zpowers' p L hm hζ] at e
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end GlueSqrtLocal

/-! `GlueSqrtLocal.exists_half_iff`, `redU`, `redU_sq_eq_one` and their helpers
(copied in the draft) are imported from `ZInQKernel.HDecomp.Sqrt.SqrtLocal`. -/

namespace GlueSqrtDisj

variable (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

/-- `ℤ_p/(p)` has `p` elements (copied from glue-sqrt-local). -/
theorem card_quotient_maximalIdeal : Nat.card (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) = p := by
  rw [← PadicInt.ker_toZMod]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZMod (p := p)))).toEquiv]
  simp

/-- Two `m`-th roots of unity congruent modulo a prime `Q` with `m ∉ Q` are equal
(copied from glue-sqrt-local). -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) {m : ℕ}
    {x y : R} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ Q) (hm : (m : R) ∉ Q) :
    x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)) = 0 := by
    have := geom_sum₂_mul x y m
    rw [hx, hy, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have h2 : Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q y := Ideal.Quotient.eq.mpr hxy
  have h3 := congrArg (Ideal.Quotient.mk Q) h1
  simp only [map_sum, map_mul, map_pow, h2, map_zero] at h3
  have h4 : ∀ i ∈ Finset.range m, (Ideal.Quotient.mk Q y) ^ i * (Ideal.Quotient.mk Q y) ^ (m - 1 -
      i)
      = (Ideal.Quotient.mk Q y) ^ (m - 1) := fun i hi => by
    rw [← pow_add]; congr 1; have := Finset.mem_range.mp hi; omega
  rw [Finset.sum_congr rfl h4, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
  have h5 : (Ideal.Quotient.mk Q y) ^ (m - 1) * Ideal.Quotient.mk Q y = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), ← map_pow, hy, map_one]
  have h6 : (m : R ⧸ Q) = 0 := by
    have := congrArg (· * Ideal.Quotient.mk Q y) h3
    simp only [zero_mul, mul_assoc, h5, mul_one] at this
    exact this
  apply hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h6

/-- In a domain, if `p` lies in a prime `Q` and `z` is a primitive `p^k`-th root of unity, then
`p ∈ Q^φ(p^k)`: `p = Φ_{p^k}(1) = ∏ (1 - μ)` over the primitive roots `μ`, and each `1 - μ`
lies in `Q`. -/
theorem prime_mem_pow_totient {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) [Q.IsPrime]
    {k : ℕ} {z : R} (hz : IsPrimitiveRoot z (p ^ k)) (hpQ : (p : R) ∈ Q) :
    (p : R) ∈ Q ^ (p ^ k).totient := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hpQ
  have hpk : 0 < p ^ k := pow_pos hp.out.pos k
  have hprod : (p : R) = ∏ μ ∈ primitiveRoots (p ^ k) R, (1 - μ) := by
    have h1 := congrArg (eval 1) (cyclotomic_eq_prod_X_sub_primitiveRoots hz)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [eval_one_cyclotomic_prime_pow (R := R) (p := p) j, eval_prod] at h1
    simpa using h1
  -- some `1 - μ₀` lies in `Q`
  obtain ⟨μ₀, hμ₀, hμ₀Q⟩ : ∃ μ₀ ∈ primitiveRoots (p ^ k) R, 1 - μ₀ ∈ Q := by
    rw [hprod] at hpQ
    exact (Ideal.IsPrime.prod_mem_iff (p := Q)).mp hpQ
  have hμ₀' : IsPrimitiveRoot μ₀ (p ^ k) := (mem_primitiveRoots hpk).mp hμ₀
  have hall : ∀ μ ∈ primitiveRoots (p ^ k) R, 1 - μ ∈ Q := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ (p ^ k) := (mem_primitiveRoots hpk).mp hμ
    obtain ⟨i, -, rfl⟩ := hμ₀'.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨c, hc⟩ := one_sub_dvd_one_sub_pow μ₀ i
    rw [hc]
    exact Q.mul_mem_right c hμ₀Q
  have := Ideal.prod_mem_prod (s := primitiveRoots (p ^ k) R) (I := fun _ => Q)
    (x := fun μ => 1 - μ) hall
  rw [Finset.prod_const, hz.card_primitiveRoots] at this
  rw [hprod]
  exact this


/-- **Degree bound.** Let `L/ℚ_p` be finite Galois, containing a primitive `p^k`-th root of
unity `ζ` and a primitive `m`-th root of unity `η` with `p ∤ m`. Then
`φ(p^k) · ord_m(p) ≤ [L:ℚ_p]`. Proof: the fundamental identity `g·e·f = |Gal(L/ℚ_p)|` for the
integral closure `S` of `ℤ_p`; `e ≥ φ(p^k)` because `p ∈ Q^φ(p^k)`; `f ≥ ord_m(p)` because
`η^(p^f) = η` (Frobenius of `S/Q`, and `m`-th roots of unity stay distinct mod `Q`). -/
theorem totient_mul_orderOf_le_finrank {k m : ℕ} [NeZero m] (hcop : p.Coprime m) {ζ η : L}
    (hζ : IsPrimitiveRoot ζ (p ^ k)) (hη : IsPrimitiveRoot η m) :
    (p ^ k).totient * orderOf (ZMod.unitOfCoprime p hcop) ≤ Module.finrank ℚ_[p] L := by
  let S := integralClosure ℤ_[p] L
  have : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension ℚ_[p] L
  have : IsGaloisGroup Gal(L/ℚ_[p]) ℤ_[p] S :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ_[p]) ℤ_[p] S ℚ_[p] L
  have : Module.Finite ℤ_[p] S := IsIntegralClosure.finite ℤ_[p] ℚ_[p] L S
  have hinjL : Function.Injective (algebraMap ℤ_[p] L) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] L]
    exact (algebraMap ℚ_[p] L).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have : FaithfulSMul ℤ_[p] S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinjL
    rw [IsScalarTower.algebraMap_apply ℤ_[p] S L, h, ← IsScalarTower.algebraMap_apply]
  have : IsDedekindDomain S := integralClosure.isDedekindDomain ℤ_[p] ℚ_[p] L
  have : Module.Flat ℤ_[p] S := inferInstance
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S)
    (maximalIdeal ℤ_[p])
  have hunder : Q.under ℤ_[p] = maximalIdeal ℤ_[p] := (Ideal.liesOver_iff _ _).mp hQ |>.symm
  -- the fundamental identity
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (maximalIdeal ℤ_[p]) S Gal(L/ℚ_[p])
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal ℤ_[p]) Q Gal(L/ℚ_[p]),
    Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal ℤ_[p]) Q Gal(L/ℚ_[p]),
    IsGalois.card_aut_eq_finrank] at hfund
  have hG : 0 < Module.finrank ℚ_[p] L := Module.finrank_pos
  have hef : Q.ramificationIdx ℤ_[p] * Q.inertiaDeg ℤ_[p] ≤ Module.finrank ℚ_[p] L := by
    rw [← hfund]
    apply Nat.le_mul_of_pos_left
    rcases Nat.eq_zero_or_pos (Ideal.primesOver (maximalIdeal ℤ_[p]) S).ncard with h | h
    · rw [h, zero_mul] at hfund; omega
    · exact h
  refine le_trans (Nat.mul_le_mul ?_ ?_) hef
  · -- `e ≥ φ(p^k)`
    have hpQ : (p : S) ∈ Q := by
      have : (p : ℤ_[p]) ∈ Q.under ℤ_[p] := by
        rw [hunder, PadicInt.maximalIdeal_eq_span_p]
        exact Ideal.subset_span rfl
      rw [Ideal.under, Ideal.mem_comap, map_natCast] at this
      exact this
    have hζS : IsIntegral ℤ_[p] ζ := ⟨X ^ (p ^ k) - C 1,
      monic_X_pow_sub_C 1 (pow_pos hp.out.pos k).ne', by simp [hζ.pow_eq_one]⟩
    let z : S := ⟨ζ, hζS⟩
    have hz : IsPrimitiveRoot z (p ^ k) :=
      IsPrimitiveRoot.of_map_of_injective (f := (integralClosure ℤ_[p] L).val) hζ
        Subtype.val_injective
    have hmem := prime_mem_pow_totient p Q hz hpQ
    have hne : Ideal.map (algebraMap ℤ_[p] S) (maximalIdeal ℤ_[p]) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot (by
        rw [PadicInt.maximalIdeal_eq_span_p]; simp [hp.out.ne_zero])
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (maximalIdeal ℤ_[p]) Q hne]
    have hQ0 : ¬ IsUnit Q := by
      rw [Ideal.isUnit_iff]; exact hQmax.ne_top
    apply (FiniteMultiplicity.of_not_isUnit hQ0 hne).le_multiplicity_of_pow_dvd
    rw [Ideal.dvd_iff_le, PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      Ideal.span_le, Set.singleton_subset_iff, map_natCast]
    exact hmem
  · -- `f ≥ ord_m(p)`
    have hm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp.out).mp hcop
    have hm0 : m ≠ 0 := NeZero.ne m
    have hcard := Ideal.cardQuot_pow_inertiaDeg (maximalIdeal ℤ_[p]) Q
    rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hcard
    change Nat.card (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) ^ _ = Nat.card (S ⧸ Q) at hcard
    rw [card_quotient_maximalIdeal p] at hcard
    set f := Q.inertiaDeg ℤ_[p]
    have hf : 0 < f := Ideal.inertiaDeg_pos (R := ℤ_[p]) Q
    let _ : Field (S ⧸ Q) := Ideal.Quotient.field Q
    have : Finite (S ⧸ Q) := Nat.finite_of_card_ne_zero (by
      rw [← hcard]; exact pow_ne_zero _ hp.out.ne_zero)
    let _ := Fintype.ofFinite (S ⧸ Q)
    have hηS : IsIntegral ℤ_[p] η := ⟨X ^ m - C 1, monic_X_pow_sub_C 1 hm0,
      by simp [hη.pow_eq_one]⟩
    let w : S := ⟨η, hηS⟩
    have hw : w ^ m = 1 := Subtype.ext (by simp [w, hη.pow_eq_one])
    have hmQ : (m : S) ∉ Q := by
      intro h
      have h1 : (m : ℤ_[p]) ∈ Q.under ℤ_[p] := by
        rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact h
      rw [hunder, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast,
        ZMod.natCast_eq_zero_iff] at h1
      exact hm h1
    have hfrob : Ideal.Quotient.mk Q (w ^ (p ^ f)) = Ideal.Quotient.mk Q w := by
      rw [map_pow, hcard, Nat.card_eq_fintype_card, FiniteField.pow_card]
    have hwf : w ^ (p ^ f) = w := by
      refine eq_of_pow_eq_one_of_sub_mem Q (m := m) ?_ hw (Ideal.Quotient.eq.mp hfrob) hmQ
      rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
    have hηf : η ^ (p ^ f) = η := by
      have := congrArg Subtype.val hwf
      simpa [w] using this
    have hpf : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.out.pos
    have h1 : η ^ (p ^ f - 1) = 1 := by
      apply mul_right_cancel₀ (hη.ne_zero hm0)
      rw [← pow_succ, Nat.sub_add_cancel hpf, one_mul]; exact hηf
    have h2 : m ∣ p ^ f - 1 := hη.dvd_of_pow_eq_one _ h1
    have h3 : ((p ^ f - 1 : ℕ) : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h2
    rw [Nat.cast_sub hpf, sub_eq_zero, Nat.cast_pow, Nat.cast_one] at h3
    apply orderOf_le_of_pow_eq_one hf
    ext
    simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one]
    exact h3


/-! ### Disjointness: `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)ˣ × ⟨p⟩` -/

section Disj

theorem card_subgroup_prod {G N : Type*} [Group G] [Group N] (H : Subgroup G) (K : Subgroup N) :
    Nat.card (H.prod K) = Nat.card H * Nat.card K := by
  rw [Nat.card_congr (Subgroup.prodEquiv H K).toEquiv, Nat.card_prod]

open GlueSqrtLocal

variable {p L} (k m : ℕ) [NeZero m] (hcop : p.Coprime m) [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L]

include hp in
theorem zeta_pow_m :
    IsPrimitiveRoot ((IsCyclotomicExtension.zeta (p ^ k * m) ℚ_[p] L) ^ m) (p ^ k) :=
  (IsCyclotomicExtension.zeta_spec (p ^ k * m) ℚ_[p] L).pow
    (Nat.mul_pos (pow_pos hp.out.pos k) (NeZero.pos m)) (mul_comm _ _)

include hp in
theorem zeta_pow_pk :
    IsPrimitiveRoot ((IsCyclotomicExtension.zeta (p ^ k * m) ℚ_[p] L) ^ (p ^ k)) m :=
  (IsCyclotomicExtension.zeta_spec (p ^ k * m) ℚ_[p] L).pow
    (Nat.mul_pos (pow_pos hp.out.pos k) (NeZero.pos m)) rfl

instance neZero_pow : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- The action on `μ_{p^k}` and on `μ_m`: `g ↦ (a, b)` with `g ζ₁ = ζ₁^a`, `g ζ₂ = ζ₂^b`. -/
noncomputable def galToProd : Gal(L/ℚ_[p]) →* (ZMod (p ^ k))ˣ × (ZMod m)ˣ :=
  ((zeta_pow_m (p := p) (L := L) k m).autToPow ℚ_[p]).prod
    ((zeta_pow_pk (p := p) (L := L) k m).autToPow ℚ_[p])

omit [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L] in
theorem fix_of_autToPow_eq_one {n : ℕ} [NeZero n] {μ : L} (hμ : IsPrimitiveRoot μ n)
    (g : Gal(L/ℚ_[p])) (h : hμ.autToPow ℚ_[p] g = 1) : g μ = μ := by
  rw [← hμ.autToPow_spec ℚ_[p] g, h, Units.val_one, ZMod.val_one_eq_one_mod,
    hμ.eq_orderOf, pow_mod_orderOf, pow_one]

include hcop in
theorem galToProd_injective : Function.Injective (galToProd (p := p) (L := L) k m) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  set ζ := IsCyclotomicExtension.zeta (p ^ k * m) ℚ_[p] L
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ k * m) ℚ_[p] L
  have hg1 : g (ζ ^ m) = ζ ^ m :=
    fix_of_autToPow_eq_one (zeta_pow_m k m) g (congrArg Prod.fst hg)
  have hg2 : g (ζ ^ (p ^ k)) = ζ ^ (p ^ k) :=
    fix_of_autToPow_eq_one (zeta_pow_pk k m) g (congrArg Prod.snd hg)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne _)
  have hbez : ((Nat.gcd m (p ^ k) : ℕ) : ℤ) = m * Nat.gcdA m (p ^ k) + p ^ k * Nat.gcdB m (p ^ k) :=
      by
    rw [Nat.gcd_eq_gcd_ab]; push_cast; ring
  have hgcd : Nat.gcd m (p ^ k) = 1 := (Nat.Coprime.pow_left k hcop).symm
  rw [hgcd, Nat.cast_one] at hbez
  have hdecomp : ζ = (ζ ^ m) ^ Nat.gcdA m (p ^ k) * (ζ ^ (p ^ k)) ^ Nat.gcdB m (p ^ k) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0]
    conv_lhs => rw [← zpow_one ζ]
    congr 1
  have hfix : g ζ = ζ := by
    conv_lhs => rw [hdecomp]
    rw [map_mul, map_zpow₀, map_zpow₀, hg1, hg2, ← hdecomp]
  apply hζ.autToPow_injective ℚ_[p]
  rw [map_one]
  ext
  rw [autToPow_eq_of_apply hζ g 1 (by rw [pow_one]; exact hfix)]
  simp

/-- **Disjointness.** For `p ∤ m`, the image of `Gal(ℚ_p(μ_{p^k m})/ℚ_p)` in
`(ℤ/p^k)ˣ × (ℤ/m)ˣ` is `(ℤ/p^k)ˣ × ⟨p⟩`. -/
theorem range_galToProd :
    (galToProd (p := p) (L := L) k m).range =
      (⊤ : Subgroup (ZMod (p ^ k))ˣ).prod (Subgroup.zpowers (ZMod.unitOfCoprime p hcop)) := by
  have hm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp.out).mp hcop
  have hle : (galToProd (p := p) (L := L) k m).range ≤
      (⊤ : Subgroup (ZMod (p ^ k))ˣ).prod (Subgroup.zpowers (ZMod.unitOfCoprime p hcop)) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨Subgroup.mem_top _, ?_⟩
    have := range_autToPow_eq_zpowers' p L hm (zeta_pow_pk (p := p) (L := L) k m)
    have hmem : (zeta_pow_pk (p := p) (L := L) k m).autToPow ℚ_[p] g ∈
        ((zeta_pow_pk (p := p) (L := L) k m).autToPow ℚ_[p]).range := ⟨g, rfl⟩
    rw [this] at hmem
    exact hmem
  have hcardG : Nat.card (galToProd (p := p) (L := L) k m).range = Module.finrank ℚ_[p] L := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr (Equiv.ofInjective _ (galToProd_injective k m hcop)).symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hcardG, card_subgroup_prod, Subgroup.card_top, Nat.card_zpowers,
    Nat.card_eq_fintype_card (α := (ZMod (p ^ k))ˣ), ZMod.card_units_eq_totient]
  exact totient_mul_orderOf_le_finrank p L hcop (zeta_pow_m (p := p) (L := L) k m)
    (zeta_pow_pk (p := p) (L := L) k m)

/-- **The Galois group of `ℚ_p(μ_{p^k m})`** for `p ∤ m`:
`Gal(L/ℚ_p) ≃* (ℤ/p^k)ˣ × ⟨p⟩`, through the action on `μ_{p^k}` and `μ_m`. -/
noncomputable def galEquivProd : Gal(L/ℚ_[p]) ≃*
    ((⊤ : Subgroup (ZMod (p ^ k))ˣ).prod (Subgroup.zpowers (ZMod.unitOfCoprime p hcop)) :
      Subgroup ((ZMod (p ^ k))ˣ × (ZMod m)ˣ)) :=
  (MonoidHom.ofInjective (galToProd_injective (p := p) (L := L) k m hcop)).trans
    (MulEquiv.subgroupCongr (range_galToProd k m hcop))

/-- **Degree.** `[ℚ_p(μ_{p^k m}):ℚ_p] = φ(p^k) · ord_m(p)` for `p ∤ m`. -/
theorem finrank_eq_totient_mul_orderOf :
    Module.finrank ℚ_[p] L = (p ^ k).totient * orderOf (ZMod.unitOfCoprime p hcop) := by
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (galEquivProd (L := L) k m hcop).toEquiv,
    card_subgroup_prod, Subgroup.card_top, Nat.card_zpowers,
    Nat.card_eq_fintype_card (α := (ZMod (p ^ k))ˣ), ZMod.card_units_eq_totient]


/-- `galToProd` is the action on `μ_{p^k}`: `g x = x^a` for every `x` with `x^{p^k} = 1`. -/
theorem galToProd_fst_spec (g : Gal(L/ℚ_[p])) (x : L) (hx : x ^ (p ^ k) = 1) :
    g x = x ^ (((galToProd (p := p) (L := L) k m g).1 : ZMod (p ^ k))).val := by
  obtain ⟨i, -, rfl⟩ := (zeta_pow_m (p := p) (L := L) k m).eq_pow_of_pow_eq_one hx
  rw [map_pow, ← (zeta_pow_m (p := p) (L := L) k m).autToPow_spec ℚ_[p] g]
  simp only [galToProd, MonoidHom.prod_apply]
  simp only [← pow_mul]
  ring_nf

/-- `galToProd` is the action on `μ_m`: `g y = y^b` for every `y` with `y^m = 1`. -/
theorem galToProd_snd_spec (g : Gal(L/ℚ_[p])) (y : L) (hy : y ^ m = 1) :
    g y = y ^ (((galToProd (p := p) (L := L) k m g).2 : ZMod m)).val := by
  obtain ⟨i, -, rfl⟩ := (zeta_pow_pk (p := p) (L := L) k m).eq_pow_of_pow_eq_one hy
  rw [map_pow, ← (zeta_pow_pk (p := p) (L := L) k m).autToPow_spec ℚ_[p] g]
  simp only [galToProd, MonoidHom.prod_apply]
  simp only [← pow_mul]
  ring_nf

omit [NeZero m] [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L] in
/-- **Compatibility with restriction.** For a subextension `K` of level `p^{k'} m'`
(`k' ≤ k`, `m' ∣ m`), restriction `Gal(L/ℚ_p) → Gal(K/ℚ_p)` corresponds to reduction
`(ℤ/p^k)ˣ × (ℤ/m)ˣ → (ℤ/p^{k'})ˣ × (ℤ/m')ˣ`. -/
theorem galToProd_restrict [NeZero m] [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L]
    (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (k' m' : ℕ) [NeZero m'] [IsCyclotomicExtension {p ^ k' * m'} ℚ_[p] K]
    [Algebra K L] [IsScalarTower ℚ_[p] K L] (hk : k' ≤ k) (hm : m' ∣ m) (g : Gal(L/ℚ_[p])) :
    (((galToProd (p := p) (L := K) k' m' (g.restrictNormal K)).1 : ZMod (p ^ k')) =
        ZMod.castHom (pow_dvd_pow p hk) _ ((galToProd (p := p) (L := L) k m g).1 : ZMod (p ^ k))) ∧
    (((galToProd (p := p) (L := K) k' m' (g.restrictNormal K)).2 : ZMod m') =
        ZMod.castHom hm _ ((galToProd (p := p) (L := L) k m g).2 : ZMod m)) := by
  constructor
  · set a := ((galToProd (p := p) (L := L) k m g).1 : ZMod (p ^ k))
    have h := autToPow_eq_of_apply (zeta_pow_m (p := p) (L := K) k' m') (g.restrictNormal K) a.val
      (by
        apply (algebraMap K L).injective
        rw [AlgEquiv.restrictNormal_commutes, map_pow _ _ a.val]
        refine galToProd_fst_spec (p := p) (L := L) k m g _ ?_
        rw [← map_pow, ← map_one (algebraMap K L)]
        congr 1
        obtain ⟨c, hc⟩ := pow_dvd_pow p hk
        rw [hc, pow_mul, (zeta_pow_m (p := p) (L := K) k' m').pow_eq_one, one_pow])
    simp only [galToProd, MonoidHom.prod_apply] at h ⊢
    rw [h, ZMod.castHom_apply, ZMod.cast_eq_val]
  · set b := ((galToProd (p := p) (L := L) k m g).2 : ZMod m)
    have h := autToPow_eq_of_apply (zeta_pow_pk (p := p) (L := K) k' m') (g.restrictNormal K) b.val
      (by
        apply (algebraMap K L).injective
        rw [AlgEquiv.restrictNormal_commutes, map_pow _ _ b.val]
        refine galToProd_snd_spec (p := p) (L := L) k m g _ ?_
        rw [← map_pow, ← map_one (algebraMap K L)]
        congr 1
        obtain ⟨c, hc⟩ := hm
        rw [hc, pow_mul, (zeta_pow_pk (p := p) (L := K) k' m').pow_eq_one, one_pow])
    simp only [galToProd, MonoidHom.prod_apply] at h ⊢
    rw [h, ZMod.castHom_apply, ZMod.cast_eq_val]

end Disj


/-! ### The local square-root criterion at a finite level, with the level change -/

section Crit

open GlueSqrtLocal

variable {p L}

/-- `Gal(ℚ_p(μ_{p^k m})/ℚ_p)` is commutative (it embeds in `(ℤ/p^k)ˣ × (ℤ/m)ˣ`). -/
noncomputable abbrev galCommGroup (k m : ℕ) [NeZero m] (hcop : p.Coprime m)
    [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L] : CommGroup Gal(L/ℚ_[p]) :=
  { (inferInstance : Group Gal(L/ℚ_[p])) with
    mul_comm := fun a b => galToProd_injective (p := p) (L := L) k m hcop
      (by rw [map_mul, map_mul, mul_comm]) }

/-- **Local square-root criterion, finite level, every prime `p` (including `2`).**
`K = ℚ_p(μ_{p^k m})` and `L = ℚ_p(μ_{p^{k+1} m'})` with `p ∤ m m'`, `m ∣ m'`, `K ⊆ L`, and
`ord_{m'}(p) = 2 ord_m(p)` (e.g. `m' = p^{2f} - 1`, see `Level.lean`). Let `τ ∈ Gal(K/ℚ_p)` act
by `ζ ↦ ζ⁻¹` on `μ_{p^k}` and trivially on `μ_m`. A `ℚ/ℤ`-character `χ` of `Gal(K/ℚ_p)`,
inflated to `Gal(L/ℚ_p)`, is twice a character of `Gal(L/ℚ_p)` iff `χ(τ) = 0`. -/
theorem sqrt_criterion_level (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (k m m' : ℕ) [NeZero m] [NeZero m'] (hcop : p.Coprime m) (hcop' : p.Coprime m')
    [IsCyclotomicExtension {p ^ k * m} ℚ_[p] K] [IsCyclotomicExtension {p ^ (k + 1) * m'} ℚ_[p] L]
    [Algebra K L] [IsScalarTower ℚ_[p] K L] (hm : m ∣ m')
    (hord : orderOf (ZMod.unitOfCoprime p hcop') = 2 * orderOf (ZMod.unitOfCoprime p hcop))
    (τ : Gal(K/ℚ_[p])) (hτ : galToProd (p := p) (L := K) k m τ = (-1, 1))
    (χ : Additive Gal(K/ℚ_[p]) →+ AddCircle (1 : ℚ)) :
    (∃ ψ : Additive Gal(L/ℚ_[p]) →+ AddCircle (1 : ℚ),
        ∀ g : Gal(L/ℚ_[p]), 2 • ψ (Additive.ofMul g) = χ (Additive.ofMul (g.restrictNormal K))) ↔
      χ (Additive.ofMul τ) = 0 := by
  letI := galCommGroup (p := p) (L := L) (k + 1) m' hcop'
  have hk : k ≤ k + 1 := Nat.le_succ k
  have hres := fun g => galToProd_restrict (p := p) (L := L) (k + 1) m' K k m hk hm g
  have hinjK := galToProd_injective (p := p) (L := K) k m hcop
  let φ : Additive Gal(L/ℚ_[p]) →+ AddCircle (1 : ℚ) :=
    χ.comp (MonoidHom.toAdditive (AlgEquiv.restrictNormalHom (F := ℚ_[p]) (K₁ := L) K))
  have hφ : ∀ g : Gal(L/ℚ_[p]), φ (Additive.ofMul g) = χ (Additive.ofMul (g.restrictNormal K)) :=
    fun g => rfl
  have key : (∃ ψ : Additive Gal(L/ℚ_[p]) →+ AddCircle (1 : ℚ),
      ∀ g : Gal(L/ℚ_[p]), 2 • ψ (Additive.ofMul g) = χ (Additive.ofMul (g.restrictNormal K))) ↔
      (∃ ψ : Additive Gal(L/ℚ_[p]) →+ AddCircle (1 : ℚ), ∀ g, 2 • ψ g = φ g) :=
    ⟨fun ⟨ψ, h⟩ => ⟨ψ, fun g => h (Additive.toMul g)⟩, fun ⟨ψ, h⟩ => ⟨ψ, fun g => h (Additive.ofMul
        g)⟩⟩
  rw [key, exists_half_iff φ]
  constructor
  · intro h
    obtain ⟨g0, hg0⟩ : ((-1 : (ZMod (p ^ (k + 1)))ˣ), (1 : (ZMod m')ˣ)) ∈
        (galToProd (p := p) (L := L) (k + 1) m').range := by
      rw [range_galToProd (k + 1) m' hcop']
      exact ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
    have hsq : g0 ^ 2 = 1 := galToProd_injective (p := p) (L := L) (k + 1) m' hcop' (by
      rw [map_pow, hg0, map_one]
      ext <;> simp)
    have hr : g0.restrictNormal K = τ := by
      apply hinjK
      rw [hτ]
      obtain ⟨h1, h2⟩ := hres g0
      rw [hg0] at h1 h2
      ext
      · rw [h1]
        first
          | simp [-ZMod.castHom_apply]
          | (dsimp only; rw [Units.val_neg, Units.val_one, map_neg, map_one, Units.val_neg,
              Units.val_one])
      · rw [h2]
        first
          | simp [-ZMod.castHom_apply]
          | (dsimp only; rw [Units.val_one, map_one, Units.val_one])
    have := h (Additive.ofMul g0) (by
      change Additive.ofMul (g0 ^ 2) = Additive.ofMul 1
      rw [hsq])
    rw [hφ, hr] at this
    exact this
  · intro hχ g hg
    set g' := Additive.toMul g with hg'def
    have hgg : g = Additive.ofMul g' := rfl
    have hg2 : g' ^ 2 = 1 := by
      have := congrArg Additive.toMul hg
      simpa [toMul_nsmul] using this
    set a := (galToProd (p := p) (L := L) (k + 1) m' g').1 with ha_def
    set b := (galToProd (p := p) (L := L) (k + 1) m' g').2 with hb_def
    have hsq : galToProd (p := p) (L := L) (k + 1) m' g' ^ 2 = 1 := by
      rw [← map_pow, hg2, map_one]
    have ha : a ^ 2 = 1 := by rw [ha_def, ← Prod.pow_fst, hsq, Prod.fst_one]
    have hb : b ^ 2 = 1 := by rw [hb_def, ← Prod.pow_snd, hsq, Prod.snd_one]
    have hbmem : b ∈ Subgroup.zpowers (ZMod.unitOfCoprime p hcop') := by
      have hmem : galToProd (p := p) (L := L) (k + 1) m' g' ∈
          (galToProd (p := p) (L := L) (k + 1) m').range := ⟨g', rfl⟩
      rw [range_galToProd (k + 1) m' hcop'] at hmem
      exact hmem.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hbmem
    have h2j : (orderOf (ZMod.unitOfCoprime p hcop') : ℤ) ∣ j * 2 := by
      rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, hj]
      exact_mod_cast hb
    rw [hord] at h2j
    push_cast at h2j
    have hfj : (orderOf (ZMod.unitOfCoprime p hcop) : ℤ) ∣ j := by
      rw [mul_comm j] at h2j
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2j
    have hbK : ZMod.castHom hm (ZMod m) (b : ZMod m') = 1 := by
      have hU : Units.map (ZMod.castHom hm (ZMod m)).toMonoidHom (ZMod.unitOfCoprime p hcop') =
          ZMod.unitOfCoprime p hcop := Units.ext (by simp)
      have := congrArg (Units.map (ZMod.castHom hm (ZMod m)).toMonoidHom) hj
      rw [map_zpow, hU, orderOf_dvd_iff_zpow_eq_one.mp hfj] at this
      have := congrArg Units.val this
      simpa using this.symm
    obtain ⟨h1, h2⟩ := hres g'
    rw [← ha_def] at h1
    rw [← hb_def, hbK] at h2
    have hsnd : (galToProd (p := p) (L := K) k m (g'.restrictNormal K)).2 = 1 := Units.ext h2
    rw [hgg, hφ]
    rcases redU_sq_eq_one hp.out k a ha with hpos | hneg
    · have : g'.restrictNormal K = 1 := by
        apply hinjK
        rw [map_one]
        ext
        · rw [h1, ← redU_val, hpos]; rfl
        · rw [hsnd]; rfl
      rw [this]; exact map_zero χ
    · have : g'.restrictNormal K = τ := by
        apply hinjK
        rw [hτ]
        ext
        · rw [h1, ← redU_val, hneg]
        · rw [hsnd]
      rw [this]; exact hχ


/-! ### Level change `m ↦ p^{2f} - 1` (copied from `Level.lean`) -/

/-- `p` is a unit mod `p^n - 1` (`n ≥ 1`). -/
theorem coprime_pow_sub_one {p : ℕ} (hp : 2 ≤ p) {n : ℕ} (hn : 0 < n) : p.Coprime (p ^ n - 1) := by
  have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ (by omega)
  have hd : Nat.gcd p (p ^ n - 1) ∣ p ^ n := (Nat.gcd_dvd_left _ _).trans (dvd_pow_self p hn.ne')
  have hd' : Nat.gcd p (p ^ n - 1) ∣ p ^ n - 1 := Nat.gcd_dvd_right _ _
  have := Nat.dvd_sub hd hd'
  rwa [Nat.sub_sub_self h1, Nat.dvd_one] at this

/-- **Level change.** The order of `p` modulo `p^n - 1` is `n` (for `p ≥ 2`, `n ≥ 1`). -/
theorem orderOf_unit_pow_sub_one {p : ℕ} (hp : 2 ≤ p) {n : ℕ} (hn : 0 < n) :
    orderOf (ZMod.unitOfCoprime p (coprime_pow_sub_one hp hn)) = n := by
  have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ (by omega)
  have key : ∀ d, ((ZMod.unitOfCoprime p (coprime_pow_sub_one hp hn)) ^ d = 1 ↔
      p ^ n - 1 ∣ p ^ d - 1) := by
    intro d
    have hd1 : 1 ≤ p ^ d := Nat.one_le_pow _ _ (by omega)
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one,
      ← Nat.cast_pow, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub hd1, sub_eq_zero, Nat.cast_one,
      Nat.cast_pow]
  rw [orderOf_eq_iff hn]
  refine ⟨(key n).mpr dvd_rfl, fun d hdn hd0 h => ?_⟩
  have hdvd := (key d).mp h
  have hlt : p ^ d < p ^ n := Nat.pow_lt_pow_right (by omega) hdn
  have hpos : 0 < p ^ d - 1 := by
    have : p ≤ p ^ d := Nat.le_self_pow hd0.ne' p
    omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- If `f = ord_m(p)` then `m ∣ p^f - 1`, hence `m ∣ p^(2f) - 1`. -/
theorem dvd_pow_orderOf_sub_one {p m : ℕ} (hcop : p.Coprime m) (t : ℕ) :
    m ∣ p ^ (t * orderOf (ZMod.unitOfCoprime p hcop)) - 1 := by
  have h := pow_orderOf_eq_one (ZMod.unitOfCoprime p hcop)
  have h' : (ZMod.unitOfCoprime p hcop) ^ (t * orderOf (ZMod.unitOfCoprime p hcop)) = 1 := by
    rw [mul_comm, pow_mul, h, one_pow]
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · have : m = 1 := by simpa using hcop
    subst this; exact one_dvd _
  have hd1 : 1 ≤ p ^ (t * orderOf (ZMod.unitOfCoprime p hcop)) := Nat.one_le_pow _ _ hp0
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one,
    ← Nat.cast_pow] at h'
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hd1, sub_eq_zero, Nat.cast_one]
  exact h'


/-- `τ₋₁` exists: some `τ ∈ Gal(ℚ_p(μ_{p^k m})/ℚ_p)` acts by `ζ ↦ ζ⁻¹` on `μ_{p^k}` and
trivially on `μ_m`. -/
theorem exists_tau (k m : ℕ) [NeZero m] (hcop : p.Coprime m)
    [IsCyclotomicExtension {p ^ k * m} ℚ_[p] L] :
    ∃ τ : Gal(L/ℚ_[p]), galToProd (p := p) (L := L) k m τ = (-1, 1) := by
  have : ((-1 : (ZMod (p ^ k))ˣ), (1 : (ZMod m)ˣ)) ∈ (galToProd (p := p) (L := L) k m).range := by
    rw [range_galToProd k m hcop]
    exact ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
  exact this

/-- **`sqrt_criterion_level` at the level `m' = p^{2f} - 1`, `f = ord_m(p)`.** The hypotheses
`m ∣ m'` and `ord_{m'}(p) = 2f` are discharged. -/
theorem sqrt_criterion_level_pow (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (k m : ℕ) [NeZero m] (hcop : p.Coprime m)
    [NeZero (p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) - 1)]
    [IsCyclotomicExtension {p ^ k * m} ℚ_[p] K]
    [IsCyclotomicExtension {p ^ (k + 1) * (p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) - 1)}
      ℚ_[p] L]
    [Algebra K L] [IsScalarTower ℚ_[p] K L]
    (τ : Gal(K/ℚ_[p])) (hτ : galToProd (p := p) (L := K) k m τ = (-1, 1))
    (χ : Additive Gal(K/ℚ_[p]) →+ AddCircle (1 : ℚ)) :
    (∃ ψ : Additive Gal(L/ℚ_[p]) →+ AddCircle (1 : ℚ),
        ∀ g : Gal(L/ℚ_[p]), 2 • ψ (Additive.ofMul g) = χ (Additive.ofMul (g.restrictNormal K))) ↔
      χ (Additive.ofMul τ) = 0 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hf : 0 < orderOf (ZMod.unitOfCoprime p hcop) := orderOf_pos _
  have h2f : 0 < 2 * orderOf (ZMod.unitOfCoprime p hcop) := by omega
  refine sqrt_criterion_level K k m _ hcop (coprime_pow_sub_one hp2 h2f) ?_ ?_ τ hτ χ
  · exact dvd_pow_orderOf_sub_one hcop 2
  · rw [orderOf_unit_pow_sub_one hp2 h2f]

end Crit

end GlueSqrtDisj

/-! `PkgI6.LocalKroneckerWeber` is imported from `Conductor/I6Base.lean`. -/

namespace GlueSqrtDisj

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ℚ_p(μ_n) ⊆ \bar ℚ_p`. -/
noncomputable abbrev muField (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] {x : PadicAlgCl p | x ^ n = 1}

/-- `ℚ_p(μ_n) ⊆ \bar ℚ_p` is an `n`-th cyclotomic extension of `ℚ_p`. -/
theorem isCyclotomicExtension_muField (n : ℕ) [NeZero n] :
    IsCyclotomicExtension {n} ℚ_[p] (muField p n) := by
  have hn : NeZero ((n : ℕ) : PadicAlgCl p) := NeZero.charZero
  have h := IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot {n} ℚ_[p]
    (L := PadicAlgCl p) (fun n' hn' _ => by
      rw [Set.mem_singleton_iff] at hn'
      subst hn'
      exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl p) n')
  have hset : {b : PadicAlgCl p | ∃ n' ∈ ({n} : Set ℕ), n' ≠ 0 ∧ b ^ n' = 1} =
      {x : PadicAlgCl p | x ^ n = 1} := by
    ext b
    simp [NeZero.ne n]
  rw [hset] at h
  exact h

/-- Levels are monotone: `ℚ_p(μ_a) ≤ ℚ_p(μ_b)` when `a ∣ b`. -/
theorem muField_mono {a b : ℕ} (hab : a ∣ b) : muField p a ≤ muField p b := by
  apply IntermediateField.adjoin.mono
  intro x hx
  obtain ⟨c, rfl⟩ := hab
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [pow_mul, hx, one_pow]

/-- **I6.3, normalized.** Under local Kronecker–Weber, every finite abelian `M ⊆ \bar ℚ_p` lies in
`ℚ_p(μ_{p^k m})` for some `k` and some `m ≥ 1` prime to `p`. -/
theorem le_muField_of_lkw (hLKW : PkgI6.LocalKroneckerWeber p)
    (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M]
    [IsAbelianGalois ℚ_[p] M] :
    ∃ k m : ℕ, 0 < m ∧ p.Coprime m ∧ M ≤ muField p (p ^ k * m) := by
  obtain ⟨n, hn, hM⟩ := hLKW M inferInstance inferInstance
  obtain ⟨e, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.one_lt.ne'
  refine ⟨e, m, Nat.pos_of_ne_zero ?_, (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm, hM⟩
  rintro rfl
  simp at hn

/-- The bigger level used by the criterion: `p^k m ∣ p^{k+1} (p^{2f} - 1)`, `f = ord_m(p)`, so
`ℚ_p(μ_{p^k m}) ≤ ℚ_p(μ_{p^{k+1}(p^{2f}-1)})`. -/
theorem muField_le_level (k m : ℕ) (hcop : p.Coprime m) :
    muField p (p ^ k * m) ≤
      muField p (p ^ (k + 1) * (p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) - 1)) := by
  apply muField_mono
  apply Nat.mul_dvd_mul (pow_dvd_pow p (Nat.le_succ k))
  -- `m ∣ p^{2f} - 1`
  have h := pow_orderOf_eq_one (ZMod.unitOfCoprime p hcop)
  have h' : (ZMod.unitOfCoprime p hcop) ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) = 1 := by
    rw [pow_mul', h, one_pow]
  have hd1 : 1 ≤ p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) :=
    Nat.one_le_pow _ _ hp.out.pos
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one,
    ← Nat.cast_pow] at h'
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hd1, sub_eq_zero, Nat.cast_one]
  exact h'

end GlueSqrtDisj


/-! ### The criterion on the subfields `ℚ_p(μ_n)` of `\bar ℚ_p` -/

namespace GlueSqrtDisj

section MuField

variable (p : ℕ) [hp : Fact p.Prime]

instance neZero_prime : NeZero p := ⟨hp.out.ne_zero⟩

instance (n : ℕ) [NeZero n] : IsCyclotomicExtension {n} ℚ_[p] (muField p n) :=
  isCyclotomicExtension_muField p n

instance (n : ℕ) [NeZero n] : FiniteDimensional ℚ_[p] (muField p n) :=
  IsCyclotomicExtension.finiteDimensional {n} ℚ_[p] _

instance (n : ℕ) [NeZero n] : IsGalois ℚ_[p] (muField p n) :=
  IsCyclotomicExtension.isGalois {n} ℚ_[p] _

/-- The inclusion `ℚ_p(μ_a) ⊆ ℚ_p(μ_b)` for `a ∣ b`, as an algebra. -/
noncomputable instance muAlgebra (a b : ℕ) [Fact (a ∣ b)] : Algebra (muField p a) (muField p b) :=
  (IntermediateField.inclusion (muField_mono p (Fact.out : a ∣ b))).toRingHom.toAlgebra

instance (a b : ℕ) [Fact (a ∣ b)] : IsScalarTower ℚ_[p] (muField p a) (muField p b) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- **The local square-root criterion on `ℚ_p(μ_{p^k m}) ⊆ ℚ_p(μ_{p^{k+1}(p^{2f}-1)}) ⊆ \bar ℚ_p`**,
every `p` (including `2`), `p ∤ m`, `f = ord_m(p)`: a character `χ` of `Gal(ℚ_p(μ_{p^k m})/ℚ_p)`
inflated to the bigger level is twice a character iff `χ(τ₋₁) = 0`. -/
theorem sqrt_criterion_muField (k m : ℕ) [NeZero m] (hcop : p.Coprime m)
    [NeZero (p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) - 1)]
    [Fact (p ^ k * m ∣ p ^ (k + 1) * (p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) - 1))]
    (τ : Gal(muField p (p ^ k * m)/ℚ_[p]))
    (hτ : galToProd (p := p) (L := muField p (p ^ k * m)) k m τ = (-1, 1))
    (χ : Additive Gal(muField p (p ^ k * m)/ℚ_[p]) →+ AddCircle (1 : ℚ)) :
    (∃ ψ : Additive Gal(muField p (p ^ (k + 1) *
          (p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) - 1))/ℚ_[p]) →+ AddCircle (1 : ℚ),
        ∀ g, 2 • ψ (Additive.ofMul g) =
          χ (Additive.ofMul (g.restrictNormal (muField p (p ^ k * m))))) ↔
      χ (Additive.ofMul τ) = 0 :=
  sqrt_criterion_level_pow (muField p (p ^ k * m)) k m hcop τ hτ χ

/-- The divisibility needed for `sqrt_criterion_muField`'s `Fact` instance. -/
theorem level_dvd (k m : ℕ) (hcop : p.Coprime m) :
    p ^ k * m ∣ p ^ (k + 1) * (p ^ (2 * orderOf (ZMod.unitOfCoprime p hcop)) - 1) :=
  Nat.mul_dvd_mul (pow_dvd_pow p (Nat.le_succ k)) (dvd_pow_orderOf_sub_one hcop 2)

end MuField

end GlueSqrtDisj

end T30KernelDisjSec

section T30SqrtCritSec
/-! ### t30-adelic: `scratch/t30-adelic/SqrtCrit.lean` (verbatim, imports and `#print` dropped).
Bridge: `T30.leafSqrtCrit_of_t16a : (∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p) →
GlueDescent.B2Q.LeafSqrtCrit` (HSyn's `t16a` ⇒ HSyn's `t30`). -/

/-!
# t30-adelic, part T30: the local square-root criterion from local Kronecker–Weber

`GlueDescent.B2Q.LeafSqrtCrit` (leaf L-B2c) is proved from `PkgI6.LocalKroneckerWeber p` at
every prime `p` (leaf T16).  The finite-level criterion is `GlueSqrtDisj` (imported); this file
does the descent through `Gal(ℚ_p(μ_n)/ℚ_p)` and the inflation to `G_{ℚ_p}`.
-/

open GlueDescent.B2Q GlueSqrtDisj

namespace T30

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ### Elementary lemmas on roots of unity -/

section Roots

variable {F : Type*} [Field F]

theorem zpow_congr_of_dvd {x : F} {q : ℕ} (hq : x ^ q = 1) (hx : x ≠ 0) {s t : ℤ}
    (h : (q : ℤ) ∣ s - t) : x ^ s = x ^ t := by
  obtain ⟨c, hc⟩ := h
  have : s = t + q * c := by linarith
  rw [this, zpow_add₀ hx, zpow_mul, zpow_natCast, hq, one_zpow, mul_one]

theorem ne_zero_of_pow_eq_one {x : F} {q : ℕ} (hq0 : 0 < q) (hq : x ^ q = 1) : x ≠ 0 := by
  rintro rfl
  rw [zero_pow hq0.ne'] at hq
  exact zero_ne_one hq

/-- Bezout decomposition of a root of unity of order dividing `a b` with `a ⊥ b`. -/
theorem exists_decomp {a b : ℕ} (hab : a.Coprime b) (h0 : 0 < a * b) {z : F}
    (hz : z ^ (a * b) = 1) : ∃ x y : F, x ^ a = 1 ∧ y ^ b = 1 ∧ z = x * y := by
  have hz0 : z ≠ 0 := ne_zero_of_pow_eq_one h0 hz
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hab
  have hzab : z ^ ((a * b : ℕ) : ℤ) = 1 := by rw [zpow_natCast, hz]
  refine ⟨z ^ (v * b), z ^ (u * a), ?_, ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul, show v * (b : ℤ) * a = (a * b : ℕ) * v by push_cast; ring,
      zpow_mul, hzab, one_zpow]
  · rw [← zpow_natCast, ← zpow_mul, show u * (a : ℤ) * b = (a * b : ℕ) * u by push_cast; ring,
      zpow_mul, hzab, one_zpow]
  · rw [← zpow_add₀ hz0, show v * (b : ℤ) + u * a = 1 by linarith, zpow_one]

/-- An automorphism acting by `x ↦ x^e` on `μ_a` and on `μ_b` (`a ⊥ b`) acts so on `μ_{ab}`. -/
theorem act_crt (f : F ≃+* F) {a b : ℕ} (hab : a.Coprime b) (h0 : 0 < a * b) (e : ℕ)
    (h1 : ∀ x : F, x ^ a = 1 → f x = x ^ e) (h2 : ∀ y : F, y ^ b = 1 → f y = y ^ e)
    (z : F) (hz : z ^ (a * b) = 1) : f z = z ^ e := by
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_decomp hab h0 hz
  rw [map_mul, h1 x hx, h2 y hy, mul_pow]

/-- `((a.val : ℤ) : ZMod N) = a`. -/
theorem intCast_val {N : ℕ} [NeZero N] (a : ZMod N) : (((a.val : ℕ) : ℤ) : ZMod N) = a := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem dvd_val_sub {N : ℕ} [NeZero N] (a : ZMod N) (t : ℤ) (h : (t : ZMod N) = a) :
    (N : ℤ) ∣ ((a.val : ℕ) : ℤ) - t := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, h, intCast_val]

end Roots

/-! ### The decomposition map and the cyclotomic character -/

section Resp

variable (p : Nat.Primes)

/-- An element of `G_{ℚ_p}` as an automorphism of `\bar ℚ_p`. -/
def actp (σ : GQp p) : PadicAlgCl (p : ℕ) ≃ₐ[ℚ_[(p : ℕ)]] PadicAlgCl (p : ℕ) := σ

/-- `resp p σ` is the restriction of `σ` along an embedding `ℚ̄ → ℚ̄_p`. -/
theorem exists_emb : ∃ g : AlgebraicClosure ℚ →+* PadicAlgCl (p : ℕ),
    ∀ (σ : GQp p) (x : AlgebraicClosure ℚ), g (act (resp p σ) x) = actp p σ (g x) := by
  letI : Algebra ℚ ℚ_[(p : ℕ)] := (algebraMap ℚ ℚ_[(p : ℕ)]).toAlgebra
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[(p : ℕ)] := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[(p : ℕ)]) := g.toAlgebra
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact (AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x)

/-- **The cyclotomic character of `resp p σ`** is read off from the action of `σ` on the `N`-th
roots of unity of `\bar ℚ_p`. -/
theorem cyc_resp_eq (N : ℕ) [NeZero N] (σ : GQp p) (u : (ZMod N)ˣ)
    (h : ∀ x : PadicAlgCl (p : ℕ), x ^ N = 1 → actp p σ x = x ^ ((u : ZMod N)).val) :
    cyc N (resp p σ) = u := by
  obtain ⟨g, hg⟩ := exists_emb p
  apply Units.ext
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (toRingAut (resp p σ)) (c := (u : ZMod N)) ?_).symm
  intro t ht
  apply g.injective
  have ht' : (t : AlgebraicClosure ℚ) ^ N = 1 := by
    rw [mem_rootsOfUnity] at ht
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  change g (act (resp p σ) t) = _
  rw [hg, map_pow]
  exact h _ (by rw [← map_pow, ht', map_one])

theorem cyc_resp_eq_one (N : ℕ) [NeZero N] (σ : GQp p)
    (h : ∀ x : PadicAlgCl (p : ℕ), x ^ N = 1 → actp p σ x = x) : cyc N (resp p σ) = 1 := by
  apply cyc_resp_eq
  intro x hx
  rw [h x hx]
  have hx0 := ne_zero_of_pow_eq_one (Nat.pos_of_ne_zero (NeZero.ne N)) hx
  have := zpow_congr_of_dvd hx hx0 (dvd_val_sub ((1 : (ZMod N)ˣ) : ZMod N) 1 (by simp))
  rw [zpow_natCast, zpow_one] at this
  exact this.symm

/-- If `σ` inverts `μ_{p^k}` and fixes `μ_{N'}`, `N = p^k N'`, then `cyc_N(σ) = u` for the unit
`u ≡ -1 mod p^k`, `u ≡ 1 mod N'`. -/
theorem cyc_resp_eq_u (N k N' : ℕ) [NeZero N] (hN : N = (p : ℕ) ^ k * N')
    (hcop : ((p : ℕ) ^ k).Coprime N') (σ : GQp p) (u : (ZMod N)ˣ)
    (hu1 : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ k)) = -1)
    (hu2 : ((u : ZMod N).cast : ZMod N') = 1)
    (h1 : ∀ x : PadicAlgCl (p : ℕ), x ^ ((p : ℕ) ^ k) = 1 → actp p σ x = x⁻¹)
    (h2 : ∀ y : PadicAlgCl (p : ℕ), y ^ N' = 1 → actp p σ y = y) :
    cyc N (resp p σ) = u := by
  have hN0 : 0 < (p : ℕ) ^ k * N' := hN ▸ Nat.pos_of_ne_zero (NeZero.ne N)
  have hpk0 : 0 < (p : ℕ) ^ k := Nat.pos_of_ne_zero (fun h => by simp [h] at hN0)
  have hN'0 : 0 < N' := Nat.pos_of_ne_zero (fun h => by simp [h] at hN0)
  haveI : NeZero ((p : ℕ) ^ k) := ⟨hpk0.ne'⟩
  haveI : NeZero N' := ⟨hN'0.ne'⟩
  set e := (u : ZMod N).val with he
  have he1 : (((p : ℕ) ^ k : ℕ) : ℤ) ∣ (-1 : ℤ) - (e : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := hu1
    rw [ZMod.cast_eq_val] at this
    push_cast
    exact this
  have he2 : (N' : ℤ) ∣ (1 : ℤ) - (e : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := hu2
    rw [ZMod.cast_eq_val] at this
    push_cast
    exact this
  apply cyc_resp_eq
  intro z hz
  rw [hN] at hz
  refine act_crt (actp p σ).toRingEquiv hcop hN0 e (fun x hx => ?_) (fun y hy => ?_) z hz
  · rw [AlgEquiv.coe_toRingEquiv, h1 x hx]
    have hx0 := ne_zero_of_pow_eq_one hpk0 hx
    have := zpow_congr_of_dvd hx hx0 he1
    rw [zpow_neg_one, zpow_natCast] at this
    exact this
  · rw [AlgEquiv.coe_toRingEquiv, h2 y hy]
    have hy0 := ne_zero_of_pow_eq_one hN'0 hy
    have := zpow_congr_of_dvd hy hy0 he2
    rw [zpow_one, zpow_natCast] at this
    exact this

end Resp

/-! ### The action of `σ` on the roots of unity of a cyclotomic level -/

section Level

variable (p : Nat.Primes)

/-- If `τ' ∈ Gal(ℚ_p(μ_{p^k m})/ℚ_p)` is the restriction of `σ`, then `σ` acts on `μ_{p^k}` and
`μ_m` through `galToProd τ'`. -/
theorem act_of_gal (k m : ℕ) [NeZero m] (σ : GQp p)
    (τ' : Gal(muField (p : ℕ) ((p : ℕ) ^ k * m)/ℚ_[(p : ℕ)]))
    (hc : ∀ x : muField (p : ℕ) ((p : ℕ) ^ k * m), ((τ' x : _) : PadicAlgCl (p : ℕ)) = actp p σ x) :
    (∀ x : PadicAlgCl (p : ℕ), x ^ ((p : ℕ) ^ k) = 1 → actp p σ x =
        x ^ (((galToProd (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ').1 :
          ZMod ((p : ℕ) ^ k))).val) ∧
    (∀ y : PadicAlgCl (p : ℕ), y ^ m = 1 → actp p σ y =
        y ^ (((galToProd (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ').2 :
          ZMod m)).val) := by
  have hmem : ∀ x : PadicAlgCl (p : ℕ), x ^ ((p : ℕ) ^ k * m) = 1 →
      x ∈ muField (p : ℕ) ((p : ℕ) ^ k * m) := fun x hx => IntermediateField.subset_adjoin _ _ hx
  constructor
  · intro x hx
    have hxK := hmem x (by rw [pow_mul, hx, one_pow])
    have h2 := galToProd_fst_spec (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ'
      ⟨x, hxK⟩ (Subtype.ext (by simpa using hx))
    have h1 := hc ⟨x, hxK⟩
    rw [h2] at h1
    rw [← h1]
    simp
  · intro y hy
    have hyK := hmem y (by rw [mul_comm, pow_mul, hy, one_pow])
    have h2 := galToProd_snd_spec (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ'
      ⟨y, hyK⟩ (Subtype.ext (by simpa using hy))
    have h1 := hc ⟨y, hyK⟩
    rw [h2] at h1
    rw [← h1]
    simp

/-- The restriction of `σ` satisfies the compatibility of `act_of_gal`. -/
theorem restrictNormal_compat (n : ℕ) [NeZero n] (σ : GQp p) (x : muField (p : ℕ) n) :
    ((((actp p σ).restrictNormal (muField (p : ℕ) n)) x : _) : PadicAlgCl (p : ℕ)) =
      actp p σ x :=
  AlgEquiv.restrictNormal_commutes (actp p σ) (muField (p : ℕ) n) x

end Level

/-! ### Square roots of `ℂˣ`-valued characters -/

section SqrtC

theorem complexUnits_pow_surj {n : ℕ} (hn : n ≠ 0) : Function.Surjective (fun a : ℂˣ => a ^ n) := by
  intro x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact x.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩

/-- **A `ℂˣ`-valued character of an abelian group is a square iff it kills the `2`-torsion.**
(`ℂˣ` is divisible, hence an injective `ℤ`-module.) -/
theorem exists_sqrt_iff {Γ : Type*} [CommGroup Γ] (χ : Γ →* ℂˣ) :
    (∃ ψ : Γ →* ℂˣ, ∀ g, ψ g ^ 2 = χ g) ↔ ∀ g : Γ, g ^ 2 = 1 → χ g = 1 := by
  constructor
  · rintro ⟨ψ, hψ⟩ g hg
    rw [← hψ, ← map_pow, hg, map_one]
  · intro h
    letI : RootableBy ℂˣ ℕ := rootableByOfPowLeftSurj _ _ complexUnits_pow_surj
    letI : RootableBy ℂˣ ℤ := Group.rootableByIntOfRootableByNat ℂˣ
    letI : DivisibleBy (Additive ℂˣ) ℤ := divisibleByOfSMulRightSurj _ _ (fun {n} hn a => by
      obtain ⟨b, hb⟩ := RootableBy.surjective_pow ℂˣ ℤ hn (Additive.toMul a)
      exact ⟨Additive.ofMul b, by show n • Additive.ofMul b = a; rw [← ofMul_zpow]; exact congrArg Additive.ofMul hb⟩)
    let χa : Additive Γ →+ Additive ℂˣ := MonoidHom.toAdditive χ
    let d : Additive Γ →+ Additive Γ :=
      { toFun := fun g => 2 • g, map_zero' := smul_zero 2, map_add' := fun a b => smul_add 2 a b }
    have hker : d.ker ≤ χa.ker := fun g hg => by
      have h2 : (Additive.toMul g) ^ 2 = 1 := AddMonoidHom.mem_ker.mp hg
      exact AddMonoidHom.mem_ker.mpr (congrArg Additive.ofMul (h _ h2))
    let χq := QuotientAddGroup.lift d.ker χa hker
    let e := QuotientAddGroup.quotientKerEquivRange d
    let χr : d.range →+ Additive ℂˣ := χq.comp e.symm.toAddMonoidHom
    obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
      d.range.subtype Subtype.val_injective χr
    refine ⟨MonoidHom.toAdditive.symm ψ, fun g => ?_⟩
    have hm : d (Additive.ofMul g) ∈ d.range := AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h1 := DFunLike.congr_fun hψ ⟨d (Additive.ofMul g), hm⟩
    have h2 : e.symm ⟨d (Additive.ofMul g), hm⟩ = ((Additive.ofMul g : Additive Γ) : _ ⧸ d.ker) := by
      rw [AddEquiv.symm_apply_eq]; rfl
    have h3 : ψ (d (Additive.ofMul g)) = χa (Additive.ofMul g) := by
      rw [show ψ (d (Additive.ofMul g)) = (ψ.comp d.range.subtype) ⟨d (Additive.ofMul g), hm⟩
        from rfl, h1]
      simp only [χr, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h2, χq,
        QuotientAddGroup.lift_mk]
    have h4 : ψ (d (Additive.ofMul g)) = 2 • ψ (Additive.ofMul g) := map_nsmul ψ 2 _
    rw [h4] at h3
    exact congrArg Additive.toMul h3

end SqrtC

/-! ### Two-torsion at the bigger level (from the proof of `sqrt_criterion_level`) -/

section Torsion

open GlueSqrtLocal

/-- At the level `L = ℚ_p(μ_{p^{k+1} m'})` with `ord_{m'}(p) = 2 ord_m(p)`, an element of order
`≤ 2` restricts to `1` or to `τ₋₁` on `K = ℚ_p(μ_{p^k m})`. -/
theorem restrict_sq_eq_one {p : ℕ} [hp : Fact p.Prime] {L : Type} [Field L] [Algebra ℚ_[p] L]
    [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]
    (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (k m m' : ℕ) [NeZero m] [NeZero m'] (hcop : p.Coprime m) (hcop' : p.Coprime m')
    [IsCyclotomicExtension {p ^ k * m} ℚ_[p] K] [IsCyclotomicExtension {p ^ (k + 1) * m'} ℚ_[p] L]
    [Algebra K L] [IsScalarTower ℚ_[p] K L] (hm : m ∣ m')
    (hord : orderOf (ZMod.unitOfCoprime p hcop') = 2 * orderOf (ZMod.unitOfCoprime p hcop))
    (g' : Gal(L/ℚ_[p])) (hg2 : g' ^ 2 = 1) :
    galToProd (p := p) (L := K) k m (g'.restrictNormal K) = 1 ∨
      galToProd (p := p) (L := K) k m (g'.restrictNormal K) = (-1, 1) := by
  have hk : k ≤ k + 1 := Nat.le_succ k
  have hres := fun g => galToProd_restrict (p := p) (L := L) (k + 1) m' K k m hk hm g
  set a := (galToProd (p := p) (L := L) (k + 1) m' g').1 with ha_def
  set b := (galToProd (p := p) (L := L) (k + 1) m' g').2 with hb_def
  have hsq : galToProd (p := p) (L := L) (k + 1) m' g' ^ 2 = 1 := by
    rw [← map_pow, hg2, map_one]
  have ha : a ^ 2 = 1 := by rw [ha_def, ← Prod.pow_fst, hsq, Prod.fst_one]
  have hb : b ^ 2 = 1 := by rw [hb_def, ← Prod.pow_snd, hsq, Prod.snd_one]
  have hbmem : b ∈ Subgroup.zpowers (ZMod.unitOfCoprime p hcop') := by
    have hmem : galToProd (p := p) (L := L) (k + 1) m' g' ∈
        (galToProd (p := p) (L := L) (k + 1) m').range := ⟨g', rfl⟩
    rw [range_galToProd (k + 1) m' hcop'] at hmem
    exact hmem.2
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hbmem
  have h2j : (orderOf (ZMod.unitOfCoprime p hcop') : ℤ) ∣ j * 2 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, hj]
    exact_mod_cast hb
  rw [hord] at h2j
  push_cast at h2j
  have hfj : (orderOf (ZMod.unitOfCoprime p hcop) : ℤ) ∣ j := by
    rw [mul_comm j] at h2j
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2j
  have hbK : ZMod.castHom hm (ZMod m) (b : ZMod m') = 1 := by
    have hU : Units.map (ZMod.castHom hm (ZMod m)).toMonoidHom (ZMod.unitOfCoprime p hcop') =
        ZMod.unitOfCoprime p hcop := Units.ext (by simp)
    have := congrArg (Units.map (ZMod.castHom hm (ZMod m)).toMonoidHom) hj
    rw [map_zpow, hU, orderOf_dvd_iff_zpow_eq_one.mp hfj] at this
    have := congrArg Units.val this
    simpa using this.symm
  obtain ⟨h1, h2⟩ := hres g'
  rw [← ha_def] at h1
  rw [← hb_def, hbK] at h2
  have hsnd : (galToProd (p := p) (L := K) k m (g'.restrictNormal K)).2 = 1 := Units.ext h2
  rcases redU_sq_eq_one hp.out k a ha with hpos | hneg
  · left
    ext
    · rw [h1, ← redU_val, hpos]; rfl
    · rw [hsnd]; rfl
  · right
    ext
    · rw [h1, ← redU_val, hneg]
    · rw [hsnd]

end Torsion

/-! ### The criterion over `G_{ℚ_p}` -/

section Main

theorem pow_val_one {F : Type*} [Field F] {q : ℕ} [NeZero q] {x : F} (hx : x ^ q = 1) :
    x ^ ((1 : ZMod q).val) = x := by
  have hx0 := ne_zero_of_pow_eq_one (Nat.pos_of_ne_zero (NeZero.ne q)) hx
  have := zpow_congr_of_dvd hx hx0 (dvd_val_sub (1 : ZMod q) 1 (by simp))
  rwa [zpow_natCast, zpow_one] at this

theorem pow_val_neg_one {F : Type*} [Field F] {q : ℕ} [NeZero q] {x : F} (hx : x ^ q = 1) :
    x ^ ((-1 : ZMod q).val) = x⁻¹ := by
  have hx0 := ne_zero_of_pow_eq_one (Nat.pos_of_ne_zero (NeZero.ne q)) hx
  have := zpow_congr_of_dvd hx hx0 (dvd_val_sub (-1 : ZMod q) (-1) (by simp))
  rwa [zpow_natCast, zpow_neg_one] at this

variable (p : Nat.Primes)

/-- The type of `G_{ℚ_p}` written as a Galois group. -/
abbrev Gp := PadicAlgCl (p : ℕ) ≃ₐ[ℚ_[(p : ℕ)]] PadicAlgCl (p : ℕ)

/-- `σ` restricts to `1` on `ℚ_p(μ_{p^k m})`: it fixes `μ_{p^k m}`. -/
theorem fix_of_galToProd_one (k m : ℕ) [NeZero m] (σ : GQp p)
    (τ' : Gal(muField (p : ℕ) ((p : ℕ) ^ k * m)/ℚ_[(p : ℕ)]))
    (hc : ∀ x : muField (p : ℕ) ((p : ℕ) ^ k * m), ((τ' x : _) : PadicAlgCl (p : ℕ)) = actp p σ x)
    (h : galToProd (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ' = 1) :
    (∀ x : PadicAlgCl (p : ℕ), x ^ ((p : ℕ) ^ k) = 1 → actp p σ x = x) ∧
      (∀ y : PadicAlgCl (p : ℕ), y ^ m = 1 → actp p σ y = y) := by
  obtain ⟨h1, h2⟩ := act_of_gal p k m σ τ' hc
  rw [h] at h1 h2
  exact ⟨fun x hx => by rw [h1 x hx]; exact pow_val_one hx,
    fun y hy => by rw [h2 y hy]; exact pow_val_one hy⟩

/-- `σ` restricts to `τ₋₁` on `ℚ_p(μ_{p^k m})`: it inverts `μ_{p^k}` and fixes `μ_m`. -/
theorem act_of_galToProd_tau (k m : ℕ) [NeZero m] (σ : GQp p)
    (τ' : Gal(muField (p : ℕ) ((p : ℕ) ^ k * m)/ℚ_[(p : ℕ)]))
    (hc : ∀ x : muField (p : ℕ) ((p : ℕ) ^ k * m), ((τ' x : _) : PadicAlgCl (p : ℕ)) = actp p σ x)
    (h : galToProd (p := (p : ℕ)) (L := muField (p : ℕ) ((p : ℕ) ^ k * m)) k m τ' = (-1, 1)) :
    (∀ x : PadicAlgCl (p : ℕ), x ^ ((p : ℕ) ^ k) = 1 → actp p σ x = x⁻¹) ∧
      (∀ y : PadicAlgCl (p : ℕ), y ^ m = 1 → actp p σ y = y) := by
  obtain ⟨h1, h2⟩ := act_of_gal p k m σ τ' hc
  rw [h] at h1 h2
  refine ⟨fun x hx => ?_, fun y hy => by rw [h2 y hy]; exact pow_val_one hy⟩
  rw [h1 x hx]
  simpa using pow_val_neg_one hx

/-- Abstract inflation: a character `χ'` of `G_{ℚ_p}` trivial on `Gal(\bar ℚ_p/L)` (`L` finite
abelian) and on every element whose image in `Gal(L/ℚ_p)` has order `≤ 2` has a locally constant
square root. -/
theorem sqrt_of_inflated (L : IntermediateField ℚ_[(p : ℕ)] (PadicAlgCl (p : ℕ)))
    [FiniteDimensional ℚ_[(p : ℕ)] L] [IsGalois ℚ_[(p : ℕ)] L]
    (hcomm : ∀ a b : Gal(L/ℚ_[(p : ℕ)]), a * b = b * a) (χ' : Gp p →* ℂˣ)
    (hker : ∀ σ : Gp p, AlgEquiv.restrictNormalHom L σ = 1 → χ' σ = 1)
    (htor : ∀ σ : Gp p, (AlgEquiv.restrictNormalHom L σ) ^ 2 = 1 → χ' σ = 1) :
    ∃ φ : Gp p →* ℂˣ, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = χ' x := by
  let rL : Gp p →* Gal(L/ℚ_[(p : ℕ)]) := AlgEquiv.restrictNormalHom L
  have hsurj : Function.Surjective rL := AlgEquiv.restrictNormalHom_surjective _
  have hker' : rL.ker ≤ χ'.ker := fun σ hσ => hker σ hσ
  let χL : Gal(L/ℚ_[(p : ℕ)]) →* ℂˣ :=
    rL.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨χ', hker'⟩
  have hχL : ∀ σ, χL (rL σ) = χ' σ := fun σ =>
    rL.liftOfRightInverse_comp_apply _ _ ⟨χ', hker'⟩ σ
  letI : CommGroup Gal(L/ℚ_[(p : ℕ)]) := { (inferInstance : Group Gal(L/ℚ_[(p : ℕ)])) with
    mul_comm := hcomm }
  obtain ⟨ψ, hψ⟩ := (exists_sqrt_iff χL).mpr (by
    intro g' hg'
    obtain ⟨σ, rfl⟩ := hsurj g'
    rw [hχL]
    exact htor σ hg')
  refine ⟨ψ.comp rL, ?_, fun x => ?_⟩
  · exact (IsLocallyConstant.of_discrete ψ).comp_continuous
      (InfiniteGalois.restrictNormalHom_continuous L)
  · show ψ (rL x) ^ 2 = χ' x
    rw [hψ]
    exact hχL x

/-- `σ` trivial on `ℚ_p(μ_n)`, `N ∣ n`, has trivial `cyc_N`. -/
theorem cyc_eq_one_of_restrict (N n : ℕ) [NeZero N] [NeZero n] (hNn : N ∣ n) (σ : Gp p)
    (hσ : AlgEquiv.restrictNormalHom (muField (p : ℕ) n) σ = 1) : cyc N (resp p σ) = 1 := by
  apply cyc_resp_eq_one
  intro x hx
  have hxL : x ∈ muField (p : ℕ) n := IntermediateField.subset_adjoin _ _ (by
    obtain ⟨c, hc⟩ := hNn
    show x ^ n = 1
    rw [hc, pow_mul, hx, one_pow])
  have := AlgEquiv.restrictNormalHom_apply (muField (p : ℕ) n) σ ⟨x, hxL⟩
  rw [hσ, AlgEquiv.one_apply] at this
  exact this.symm

theorem coe_algebraMap_mu (a b : ℕ) [Fact (a ∣ b)] (y : muField (p : ℕ) a) :
    ((algebraMap (muField (p : ℕ) a) (muField (p : ℕ) b) y : muField (p : ℕ) b) :
      PadicAlgCl (p : ℕ)) = y := by
  have : algebraMap (muField (p : ℕ) a) (muField (p : ℕ) b) y =
      IntermediateField.inclusion (muField_mono (p : ℕ) (Fact.out : a ∣ b)) y := rfl
  rw [this, IntermediateField.coe_inclusion]

/-- Restriction in two steps `\bar ℚ_p ⊇ ℚ_p(μ_b) ⊇ ℚ_p(μ_a)`. -/
theorem restrict_restrict_compat (a b : ℕ) [NeZero a] [NeZero b] [Fact (a ∣ b)] (σ : Gp p)
    (x : muField (p : ℕ) a) :
    ((((AlgEquiv.restrictNormalHom (muField (p : ℕ) b) σ).restrictNormal
      (muField (p : ℕ) a)) x : muField (p : ℕ) a) : PadicAlgCl (p : ℕ)) = actp p σ x := by
  have e1 := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormalHom (muField (p : ℕ) b) σ)
    (muField (p : ℕ) a) x
  calc _ = ((algebraMap (muField (p : ℕ) a) (muField (p : ℕ) b)
        (((AlgEquiv.restrictNormalHom (muField (p : ℕ) b) σ).restrictNormal
          (muField (p : ℕ) a)) x) : muField (p : ℕ) b) : PadicAlgCl (p : ℕ)) :=
        (coe_algebraMap_mu p a b _).symm
    _ = ((AlgEquiv.restrictNormalHom (muField (p : ℕ) b) σ
          (algebraMap (muField (p : ℕ) a) (muField (p : ℕ) b) x) : muField (p : ℕ) b) :
          PadicAlgCl (p : ℕ)) := by rw [e1]
    _ = actp p σ (algebraMap (muField (p : ℕ) a) (muField (p : ℕ) b) x) :=
        AlgEquiv.restrictNormalHom_apply _ σ _
    _ = actp p σ x := by rw [coe_algebraMap_mu]

/-- The two-torsion step at the level `L = ℚ_p(μ_{p^{k+1}(p^{2f}-1)})`. -/
theorem cyc_of_torsion (N k N' : ℕ) [NeZero N] [NeZero N'] (hN : N = (p : ℕ) ^ k * N')
    (hcopN' : (p : ℕ).Coprime N')
    [NeZero ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1)]
    [Fact ((p : ℕ) ^ k * N' ∣
      (p : ℕ) ^ (k + 1) * ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1))]
    (u : (ZMod N)ˣ)
    (hu1 : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ k)) = -1)
    (hu2 : ((u : ZMod N).cast : ZMod N') = 1) (σ : Gp p)
    (hσ : (AlgEquiv.restrictNormalHom (muField (p : ℕ) ((p : ℕ) ^ (k + 1) *
      ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1))) σ) ^ 2 = 1) :
    cyc N (resp p σ) = 1 ∨ cyc N (resp p σ) = u := by
  have hcop : ((p : ℕ) ^ k).Coprime N' := hcopN'.pow_left k
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hf0 : 0 < orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN') := orderOf_pos _
  have h2f : 0 < 2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN') := by omega
  have hcop' := coprime_pow_sub_one hp2 h2f
  have hord := orderOf_unit_pow_sub_one hp2 h2f
  have hm := dvd_pow_orderOf_sub_one hcopN' 2
  have hc := restrict_restrict_compat p ((p : ℕ) ^ k * N') ((p : ℕ) ^ (k + 1) *
      ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1)) σ
  rcases restrict_sq_eq_one (L := muField (p : ℕ) ((p : ℕ) ^ (k + 1) *
      ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1)))
      (muField (p : ℕ) ((p : ℕ) ^ k * N')) k N' _ hcopN' hcop' hm hord.symm.symm _ hσ with h1 | h1
  · left
    obtain ⟨a1, a2⟩ := fix_of_galToProd_one p k N' σ _ hc h1
    apply cyc_resp_eq_one
    intro z hz
    rw [hN] at hz
    have := act_crt (actp p σ).toRingEquiv hcop (hN ▸ Nat.pos_of_ne_zero (NeZero.ne N)) 1
      (fun x hx => by rw [AlgEquiv.coe_toRingEquiv, a1 x hx, pow_one])
      (fun y hy => by rw [AlgEquiv.coe_toRingEquiv, a2 y hy, pow_one]) z hz
    rwa [pow_one] at this
  · right
    obtain ⟨a1, a2⟩ := act_of_galToProd_tau p k N' σ _ hc h1
    exact cyc_resp_eq_u p N k N' hN hcop σ u hu1 hu2 a1 a2

/-- **The "if" direction** (no Kronecker–Weber needed), with `N = p^k N'` given. -/
theorem sqrt_of_chi' (N k N' : ℕ) [NeZero N] [NeZero N'] (hN : N = (p : ℕ) ^ k * N')
    (hcopN' : (p : ℕ).Coprime N') (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ)
    (hu1 : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ k)) = -1)
    (hu2 : ((u : ZMod N).cast : ZMod N') = 1) (hχ : χ.toUnitHom u = 1) :
    ∃ φ : Gp p →* ℂˣ, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = χ.toUnitHom (cyc N (resp p x)) := by
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hf0 : 0 < orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN') := orderOf_pos _
  have h2f : 0 < 2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN') := by omega
  have hcop' := coprime_pow_sub_one hp2 h2f
  have hm'0 : (p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1 ≠ 0 := by
    have := Nat.le_self_pow h2f.ne' (p : ℕ)
    omega
  haveI : NeZero ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1) := ⟨hm'0⟩
  haveI : Fact ((p : ℕ) ^ k * N' ∣
      (p : ℕ) ^ (k + 1) * ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1)) :=
    ⟨level_dvd (p : ℕ) k N' hcopN'⟩
  have hNL : N ∣ (p : ℕ) ^ (k + 1) *
      ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1) :=
    hN ▸ level_dvd (p : ℕ) k N' hcopN'
  refine sqrt_of_inflated p (muField (p : ℕ) ((p : ℕ) ^ (k + 1) *
      ((p : ℕ) ^ (2 * orderOf (ZMod.unitOfCoprime (p : ℕ) hcopN')) - 1)))
    (fun a b => galToProd_injective (p := (p : ℕ)) (k + 1) _ hcop' (by
      rw [map_mul, map_mul]; exact mul_comm _ _))
    ((χ.toUnitHom.comp (cyc N)).comp (resp p)) (fun σ hσ => ?_) (fun σ hσ => ?_)
  · show χ.toUnitHom (cyc N (resp p σ)) = 1
    rw [cyc_eq_one_of_restrict p N _ hNL σ hσ, map_one]
  · show χ.toUnitHom (cyc N (resp p σ)) = 1
    rcases cyc_of_torsion p N k N' hN hcopN' u hu1 hu2 σ hσ with h | h
    · rw [h, map_one]
    · rw [h, hχ]

/-- **The "only if" direction, from local Kronecker–Weber.** -/
theorem chi_of_sqrt' (hLKW : PkgI6.LocalKroneckerWeber (p : ℕ)) (N k N' : ℕ) [NeZero N]
    [NeZero N'] (hN : N = (p : ℕ) ^ k * N') (hcopN' : (p : ℕ).Coprime N')
    (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ)
    (hu1 : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ k)) = -1)
    (hu2 : ((u : ZMod N).cast : ZMod N') = 1) (φ : Gp p →* ℂˣ) (hφl : IsLocallyConstant φ)
    (hφ : ∀ x, φ x ^ 2 = χ.toUnitHom (cyc N (resp p x))) : χ.toUnitHom u = 1 := by
  have hcop := hcopN'.pow_left k
  have hHo : IsOpen ((φ.ker : Subgroup (Gp p)) : Set (Gp p)) := by
    have := hφl.isOpen_fiber 1
    convert this using 1
    ext x
    simp
  have hHc : IsClosed ((φ.ker : Subgroup (Gp p)) : Set (Gp p)) :=
    Subgroup.isClosed_of_isOpen _ hHo
  have hMH : (IntermediateField.fixedField φ.ker).fixingSubgroup = φ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨φ.ker, hHc⟩
  haveI : FiniteDimensional ℚ_[(p : ℕ)] (IntermediateField.fixedField φ.ker) :=
    (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hMH]; exact hHo)
  haveI hgal : IsGalois ℚ_[(p : ℕ)] (IntermediateField.fixedField φ.ker) :=
    (InfiniteGalois.normal_iff_isGalois _).mp (by rw [hMH]; exact φ.normal_ker)
  have hsM : Function.Surjective
      (AlgEquiv.restrictNormalHom (IntermediateField.fixedField φ.ker) : Gp p →* _) :=
    AlgEquiv.restrictNormalHom_surjective _
  have hcommM : ∀ a b : Gal(IntermediateField.fixedField φ.ker/ℚ_[(p : ℕ)]), a * b = b * a := by
    intro a b
    obtain ⟨σ, rfl⟩ := hsM a
    obtain ⟨τ, rfl⟩ := hsM b
    rw [← map_mul, ← map_mul, MonoidHom.eq_iff, IntermediateField.restrictNormalHom_ker, hMH,
      MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_comm (φ τ) (φ σ),
      inv_mul_cancel]
  haveI : IsAbelianGalois ℚ_[(p : ℕ)] (IntermediateField.fixedField φ.ker) :=
    { toIsGalois := hgal, toIsMulCommutative := ⟨⟨hcommM⟩⟩ }
  obtain ⟨a, b, hb, hcopb, hMle⟩ := le_muField_of_lkw (p : ℕ) hLKW
    (IntermediateField.fixedField φ.ker)
  haveI : NeZero (N' * b) := ⟨Nat.mul_ne_zero (NeZero.ne N') hb.ne'⟩
  have hcop0 : (p : ℕ).Coprime (N' * b) := Nat.Coprime.mul_right hcopN' hcopb
  have hMK : IntermediateField.fixedField φ.ker ≤ muField (p : ℕ) ((p : ℕ) ^ (k + a) * (N' * b)) :=
    hMle.trans (muField_mono _ (Nat.mul_dvd_mul (pow_dvd_pow _ (Nat.le_add_left a k))
      (dvd_mul_left b N')))
  obtain ⟨τ, hτ⟩ := exists_tau (p := (p : ℕ))
    (L := muField (p : ℕ) ((p : ℕ) ^ (k + a) * (N' * b))) (k + a) (N' * b) hcop0
  have hsK : Function.Surjective (AlgEquiv.restrictNormalHom
      (muField (p : ℕ) ((p : ℕ) ^ (k + a) * (N' * b))) : Gp p →* _) :=
    AlgEquiv.restrictNormalHom_surjective _
  obtain ⟨σ, hσ⟩ := hsK τ
  have hτ2 : τ ^ 2 = 1 := galToProd_injective (p := (p : ℕ)) (k + a) (N' * b) hcop0 (by
    rw [map_pow, hτ, map_one]
    ext <;> simp)
  have hσ2 : σ ^ 2 ∈ φ.ker := by
    rw [← hMH]
    apply IntermediateField.fixingSubgroup_antitone hMK
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_pow, hσ, hτ2]
  have hc : ∀ x : muField (p : ℕ) ((p : ℕ) ^ (k + a) * (N' * b)),
      ((τ x : _) : PadicAlgCl (p : ℕ)) = actp p σ x := fun x => by
    rw [← hσ]
    exact AlgEquiv.restrictNormalHom_apply _ σ x
  obtain ⟨a1, a2⟩ := act_of_galToProd_tau p (k + a) (N' * b) σ τ hc hτ
  have hcyc := cyc_resp_eq_u p N k N' hN hcop σ u hu1 hu2
    (fun x hx => a1 x (by
      obtain ⟨c, hc⟩ := pow_dvd_pow (p : ℕ) (Nat.le_add_right k a)
      rw [hc, pow_mul, hx, one_pow]))
    (fun y hy => a2 y (by rw [pow_mul, hy, one_pow]))
  rw [← hcyc, ← hφ σ, ← map_pow]
  exact hσ2

end Main

/-! ### The leaf -/

/-- **T30 at one prime:** the square-root criterion at `p` follows from local Kronecker–Weber at
`p` (only the "only if" direction uses it). -/
theorem sqrtCrit_at (p : Nat.Primes) (hLKW : PkgI6.LocalKroneckerWeber (p : ℕ)) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ)
    (hu1 : ((u : ZMod N).cast : ZMod ((p : ℕ) ^ N.factorization p)) = -1)
    (hu2 : ((u : ZMod N).cast : ZMod (N / (p : ℕ) ^ N.factorization p)) = 1) :
    (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = galChar χ (resp p x)) ↔
      χ.toUnitHom u = 1 := by
  have hN : N = (p : ℕ) ^ N.factorization p * (N / (p : ℕ) ^ N.factorization p) :=
    (Nat.ordProj_mul_ordCompl_eq_self N p).symm
  have hcopN' := Nat.coprime_ordCompl p.2 (NeZero.ne N)
  haveI : NeZero (N / (p : ℕ) ^ N.factorization p) :=
    ⟨fun h => NeZero.ne N (by rw [hN, h, mul_zero])⟩
  constructor
  · rintro ⟨φ, hφl, hφ⟩
    exact chi_of_sqrt' p hLKW N _ _ hN hcopN' χ u hu1 hu2 φ hφl hφ
  · intro hχ
    exact sqrt_of_chi' p N _ _ hN hcopN' χ u hu1 hu2 hχ

/-- **T30: the local square-root criterion `LeafSqrtCrit` (leaf L-B2c) follows from local
Kronecker–Weber (leaf T16, `PkgI6.LocalKroneckerWeber`) at every prime.** -/
theorem leafSqrtCrit_of_localKroneckerWeber
    (hLKW : ∀ p : Nat.Primes, PkgI6.LocalKroneckerWeber (p : ℕ)) : LeafSqrtCrit :=
  fun p N _ χ u hu1 hu2 => sqrtCrit_at p (hLKW p) N χ u hu1 hu2

/-- The same with T16 in the form of the field `t16a` of `HSyn` (`scratch/h-decomposition`). -/
theorem leafSqrtCrit_of_t16a (h : ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p) :
    LeafSqrtCrit :=
  leafSqrtCrit_of_localKroneckerWeber fun p => h (p : ℕ)

end T30

end T30SqrtCritSec

end T30Sec
