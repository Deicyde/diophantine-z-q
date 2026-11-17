import ZInQKernel.Contrib.OneProof.CMBranch

/-! # cm-branch2: `ReducedCMPeriod` (manuscript L598-599) reduced to the period lattice of a CM curve

The manuscript's sentence "For a reduced CM period `τ = x + iy` we have `√3/2 ≤ y ≤ √|Δ|/2`"
(diophantine_zq.tex L598-599, no citation) is cm-branch's glue `CMBranch.ReducedCMPeriod`. Here it is
proved from

* `CMPeriodLattice` (**glue, on-the-spot**): `E(ℂ)_σ` has an analytic uniformization (T35) whose period
  lattice `Λ ⊂ ℂ` has multiplier ring `{α ∈ ℂ | αΛ ⊆ Λ}` isomorphic to `End(E_{K̄}) ≅ R` (T11a for
  `E_ℂ`, T11b rigidity `End(E_{K̄}) = End(E_ℂ)`);
* `CoxProperLattice` (**leaf, textbook, consequence**): a lattice `c(ℤ + τℤ)`, `Im τ > 0`, whose
  multiplier ring is isomorphic to an order `R` of an imaginary quadratic field has `τ` a root of a
  primitive form `(a, b, c)` with `a > 0` and `b² − 4ac = Δ_R` (Cox, *Primes of the form x² + ny²*,
  Lemma 7.5 with Lemma 7.2 and §7.A's `D = f²d_K`; numbers UNVERIFIED);
* pure lattice mathematics proved here: every full lattice in `ℂ` is `c(ℤ + τℤ)` with `τ` in the
  closed fundamental domain of `SL₂(ℤ)` (`exists_reduced_basis`, from Mathlib's
  `ModularGroup.exists_smul_mem_fd`), so `Im τ ≥ √3/2` (`ModularGroup.three_le_four_mul_im_sq_of_mem_fd`);
  and a root of `aτ² + bτ + c = 0` with `a ≥ 1`, `Im τ > 0` has `Im τ = √(4ac − b²)/(2a) ≤ √|b² − 4ac|/2`
  (`im_le_of_quadratic`).
-/

namespace HDec
namespace CMBranch

open _root_.ZInQ

/-! ## 1. Multipliers of a lattice -/

/-- The multiplier ring `{α ∈ ℂ | αΛ ⊆ Λ}` of an additive subgroup `Λ ⊂ ℂ¹`. -/
def latticeMultipliers (Λ : Submodule ℤ (Fin 1 → ℂ)) : Subring ℂ where
  carrier := {α | ∀ z ∈ Λ, α • z ∈ Λ}
  mul_mem' := fun {a b} ha hb z hz => by rw [mul_smul]; exact ha _ (hb z hz)
  one_mem' := fun z hz => by simpa using hz
  add_mem' := fun {a b} ha hb z hz => by rw [add_smul]; exact Λ.add_mem (ha z hz) (hb z hz)
  zero_mem' := fun z _ => by simp only [zero_smul]; exact Λ.zero_mem
  neg_mem' := fun {a} ha z hz => by rw [neg_smul]; exact Λ.neg_mem (ha z hz)

/-! ## 2. The new Props -/

/-- **Glue (on-the-spot; manuscript L598, "a reduced CM period", first half).** For an elliptic curve `E/K`
with `End(E_{K̄}) ≅ R` and every `σ : K → ℂ`, `E(ℂ)_σ` has an analytic uniformization by `ℂ` whose kernel `Λ`
is a full lattice with multiplier ring isomorphic to `R`. Sketch: T35 gives a uniformization of `E_ℂ`
(base change along `σ`) and hence, composing with the projection `E_ℂ(ℂ) ≅ E(ℂ)_σ`, of `E(ℂ)_σ`; T11a
identifies `End(E_ℂ)` with the `ℂ`-linear maps of `ℂ` preserving `Λ`, i.e. with the multiplier ring of
`Λ`, and the identification is a ring isomorphism (uniqueness in T11a); T11b (rigidity, `K̄ ⊂ ℂ` through
an extension of `σ`) gives `End(E_{K̄}) ≅ End(E_ℂ)`. -/
def CMPeriodLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : ZInQ.DefFaltings.AbVar K), E.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k), IsImagQuadOrder k R → IsCMBy E k R →
      ∀ σ : K →+* ℂ, ∃ (Λ : Submodule ℤ (Fin 1 → ℂ))
        (Φ : (Fin 1 → ℂ) → ZInQ.LeafPush2.CPts (LeafAdopt.abVarEquiv K E) σ),
        ZInQ.LeafPush2.IsUniformization σ Λ Φ ∧ (∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ) ∧
          Nonempty (R ≃+* latticeMultipliers Λ)

/-- **Leaf (textbook, consequence): proper fractional ideals of an imaginary quadratic order.** Let `R` be an
order of an imaginary quadratic field and `Λ = c(ℤ + τℤ) ⊂ ℂ`, `c ≠ 0`, `Im τ > 0`, a lattice whose ring of
multipliers is isomorphic to `R`. Then `τ` is a root of a primitive positive definite form `ax² + bx + c'`,
`a > 0`, of discriminant `b² − 4ac' = Δ_R = f² d_k`. Cox, *Primes of the form x² + ny²* (Wiley, 1989),
Lemma 7.5 (if `aτ² + bτ + c' = 0` with `(a, b, c')` primitive, then `[1, τ]` is a proper fractional ideal
of the order of discriminant `b² − 4ac'`), with Lemma 7.2 and (7.3) (the order of conductor `f` has
discriminant `f² d_K`, and an order is determined up to isomorphism by its discriminant); numbers
UNVERIFIED (no network on this host). Consequence form: the ring isomorphism replaces "the multiplier ring
is the order of discriminant `D`" (the discriminant of an order is a ring invariant). -/
def CoxProperLattice : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (R : Subring k), IsImagQuadOrder k R →
    ∀ (Λ : Submodule ℤ (Fin 1 → ℂ)) (c τ : ℂ), c ≠ 0 → 0 < τ.im →
      (∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = c * (m + n * τ)) →
      Nonempty (R ≃+* latticeMultipliers Λ) →
      ∃ a b c' : ℤ, 0 < a ∧ Int.gcd (Int.gcd a b) c' = 1 ∧
        (a : ℂ) * τ ^ 2 + b * τ + c' = 0 ∧ b ^ 2 - 4 * a * c' = orderDisc R

/-! ## 3. Imaginary part of a root of a quadratic form -/

/-- A root `τ`, `Im τ > 0`, of `aτ² + bτ + c = 0` with `a ≥ 1` has `Im τ ≤ √|b² − 4ac|/2`. -/
theorem im_le_of_quadratic {a b c : ℤ} {τ : ℂ} (ha : 0 < a) (hτ : 0 < τ.im)
    (h : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    τ.im ≤ Real.sqrt |((b ^ 2 - 4 * a * c : ℤ) : ℝ)| / 2 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, pow_two,
    Complex.mul_im, Complex.add_im, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero,
    add_zero, zero_add] at hre him
  set x := τ.re
  set y := τ.im
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  -- `y (2 a x + b) = 0`, so `x = -b/(2a)`
  have hx : 2 * (a : ℝ) * x + b = 0 := by
    have : y * (2 * (a : ℝ) * x + b) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hτ.ne'
    · exact h0
  -- `4 a² y² = 4ac − b²`
  have hy : 4 * (a : ℝ) ^ 2 * y ^ 2 = -((b : ℝ) ^ 2 - 4 * a * c) := by
    have hx' : (b : ℝ) = -(2 * a * x) := by linarith
    rw [hx'] at hre ⊢
    linear_combination (-4 * (a : ℝ)) * hre
  have hD : ((b ^ 2 - 4 * a * c : ℤ) : ℝ) = (b : ℝ) ^ 2 - 4 * a * c := by push_cast; ring
  rw [hD]
  have hneg : (b : ℝ) ^ 2 - 4 * a * c < 0 := by
    have : 0 < 4 * (a : ℝ) ^ 2 * y ^ 2 := by positivity
    linarith
  rw [abs_of_neg hneg]
  have hy2 : (2 * y) ^ 2 ≤ -((b : ℝ) ^ 2 - 4 * a * c) := by
    rw [← hy]
    have : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg y]
  have : 2 * y ≤ Real.sqrt (-((b : ℝ) ^ 2 - 4 * a * c)) :=
    Real.le_sqrt_of_sq_le hy2
  linarith

/-! ## 4. Reduced bases of lattices in `ℂ` -/

/-- Every full lattice `Λ ⊂ ℂ¹` is `c(ℤ + τℤ)` for some `c ≠ 0` and some `τ` in the closed fundamental
domain `𝒟` of `SL₂(ℤ)` (so `Im τ > 0`, `|Re τ| ≤ 1/2`, `|τ| ≥ 1`). -/
theorem exists_basis_upper (Λ : Submodule ℤ (Fin 1 → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ (c τ : ℂ), c ≠ 0 ∧ 0 < τ.im ∧ ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = c * (m + n * τ) := by
  classical
  have hfin : Module.finrank ℤ Λ = 2 := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
  let b : Module.Basis (Fin 2) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hfin
  let bR : Module.Basis (Fin 2) ℝ (Fin 1 → ℂ) := b.ofZLatticeBasis ℝ Λ
  have hbR : ∀ i, bR i = (b i : Fin 1 → ℂ) := fun i => b.ofZLatticeBasis_apply ℝ Λ i
  set w₀ : ℂ := (b 0 : Fin 1 → ℂ) 0 with hw₀
  set w₁ : ℂ := (b 1 : Fin 1 → ℂ) 0 with hw₁
  have hfun : ∀ v : Fin 1 → ℂ, v = fun _ => v 0 := fun v => funext fun i => by
    rw [Subsingleton.elim i 0]
  -- membership in terms of the basis
  have hmem0 : ∀ z : Fin 1 → ℂ, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = m * w₀ + n * w₁ := by
    intro z
    constructor
    · intro hz
      have hs := b.sum_repr ⟨z, hz⟩
      rw [Fin.sum_univ_two] at hs
      refine ⟨b.repr ⟨z, hz⟩ 0, b.repr ⟨z, hz⟩ 1, ?_⟩
      have := congrArg (fun v : Λ => (v : Fin 1 → ℂ) 0) hs
      simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
        zsmul_eq_mul] at this
      rw [← this]
      simp [hw₀, hw₁]
    · rintro ⟨m, n, h⟩
      have hv : z = m • (b 0 : Fin 1 → ℂ) + n • (b 1 : Fin 1 → ℂ) := by
        rw [hfun z, hfun (m • (b 0 : Fin 1 → ℂ) + n • (b 1 : Fin 1 → ℂ))]
        funext _
        simp only [Pi.add_apply, Pi.smul_apply, zsmul_eq_mul]
        rw [h]
        simp [hw₀, hw₁]
      rw [hv]
      exact Λ.add_mem (Λ.smul_mem m (b 0).2) (Λ.smul_mem n (b 1).2)
  -- linear independence over `ℝ`
  have hli : ∀ s t : ℝ, s • (b 0 : Fin 1 → ℂ) + t • (b 1 : Fin 1 → ℂ) = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    have h := (Fintype.linearIndependent_iff.mp bR.linearIndependent) ![s, t]
      (by rw [Fin.sum_univ_two, hbR, hbR]; simpa using hst)
    exact ⟨h 0, h 1⟩
  have hw₀0 : w₀ ≠ 0 := by
    intro h0
    have := hli 1 0 (by
      rw [hfun ((1 : ℝ) • (b 0 : Fin 1 → ℂ) + (0 : ℝ) • (b 1 : Fin 1 → ℂ))]
      funext _
      simp [← hw₀, h0])
    exact one_ne_zero this.1
  have him : (w₁ / w₀).im ≠ 0 := by
    intro h0
    set r := (w₁ / w₀).re
    have hr : w₁ = (r : ℂ) * w₀ := by
      have : w₁ / w₀ = (r : ℂ) := Complex.ext (by simp [r]) (by simp [h0])
      field_simp at this
      rw [this, mul_comm]
    have := hli r (-1) (by
      rw [hfun (r • (b 0 : Fin 1 → ℂ) + (-1 : ℝ) • (b 1 : Fin 1 → ℂ))]
      funext _
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply]
      rw [← hw₀, ← hw₁, hr, Complex.real_smul, Complex.real_smul]
      push_cast; ring)
    norm_num at this
  rcases lt_or_gt_of_ne him with hneg | hpos
  · refine ⟨w₀, -(w₁ / w₀), hw₀0, by simpa using hneg, fun z => ?_⟩
    rw [hmem0]
    constructor
    · rintro ⟨m, n, h⟩
      exact ⟨m, -n, by rw [h]; field_simp; push_cast; ring⟩
    · rintro ⟨m, n, h⟩
      exact ⟨m, -n, by rw [h]; field_simp; push_cast; ring⟩
  · refine ⟨w₀, w₁ / w₀, hw₀0, hpos, fun z => ?_⟩
    rw [hmem0]
    constructor
    · rintro ⟨m, n, h⟩
      exact ⟨m, n, by rw [h]; field_simp⟩
    · rintro ⟨m, n, h⟩
      exact ⟨m, n, by rw [h]; field_simp⟩

/-- Change of basis by `SL₂(ℤ)`: `c(ℤ + τ₀ℤ) = c(cτ₀ + d)(ℤ + (g • τ₀)ℤ)`. -/
theorem exists_reduced_of_upper (Λ : Submodule ℤ (Fin 1 → ℂ)) (c₀ τ₀ : ℂ) (hc₀ : c₀ ≠ 0)
    (hτ₀ : 0 < τ₀.im) (hmem : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = c₀ * (m + n * τ₀)) :
    ∃ (c : ℂ) (τ : UpperHalfPlane), c ≠ 0 ∧ τ ∈ ModularGroup.fd ∧
      ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = c * (m + n * (τ : ℂ)) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd (⟨τ₀, hτ₀⟩ : UpperHalfPlane)
  set a : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set c : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hdet : a * d - b * c = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hdetC : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  set D : ℂ := c * τ₀ + d
  have hD : D ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    have hre := congrArg Complex.re h0
    simp [D] at him hre
    rcases him with hc | hc
    · have hc' : c = 0 := by exact_mod_cast hc
      rw [hc'] at hre
      simp at hre
      have hd' : d = 0 := by exact_mod_cast hre
      rw [hc', hd'] at hdet
      simp at hdet
    · exact absurd hc hτ₀.ne'
  have hτ : ((g • (⟨τ₀, hτ₀⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) = (a * τ₀ + b) / D := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [a, b, c, d, D]
  refine ⟨c₀ * D, g • (⟨τ₀, hτ₀⟩ : UpperHalfPlane), mul_ne_zero hc₀ hD, hg, fun z => ?_⟩
  rw [hmem, hτ]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨a * m - b * n, -c * m + d * n, ?_⟩
    rw [h]
    have hDD : D * ((a * τ₀ + b) / D) = a * τ₀ + b := mul_div_cancel₀ _ hD
    have e : c₀ * D * (((a * m - b * n : ℤ) : ℂ) + ((-c * m + d * n : ℤ) : ℂ) * ((a * τ₀ + b) / D)) =
        c₀ * (((a * m - b * n : ℤ) : ℂ) * D + ((-c * m + d * n : ℤ) : ℂ) * (a * τ₀ + b)) := by
      field_simp
    rw [e]
    simp only [D]
    push_cast
    linear_combination (-(c₀ * (m + n * τ₀))) * hdetC
  · rintro ⟨m, n, h⟩
    refine ⟨m * d + n * b, m * c + n * a, ?_⟩
    rw [h]
    field_simp
    push_cast
    ring

theorem exists_reduced_basis (Λ : Submodule ℤ (Fin 1 → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ (c : ℂ) (τ : UpperHalfPlane), c ≠ 0 ∧ τ ∈ ModularGroup.fd ∧
      ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = c * (m + n * (τ : ℂ)) := by
  obtain ⟨c₀, τ₀, hc₀, hτ₀, hmem⟩ := exists_basis_upper Λ
  exact exists_reduced_of_upper Λ c₀ τ₀ hc₀ hτ₀ hmem

/-! ## 5. `ReducedCMPeriod` -/

/-- **`ReducedCMPeriod` from `CMPeriodLattice` and `CoxProperLattice`.** -/
theorem reducedCMPeriod_of (hL : CMPeriodLattice) (hC : CoxProperLattice) : ReducedCMPeriod := by
  intro K _ _ E hE1 k _ _ R hR hCM σ
  obtain ⟨Λ, Φ, hΦ, ⟨hd, hZ⟩, ⟨iso⟩⟩ := hL K E hE1 k R hR hCM σ
  obtain ⟨c, τ, hc, hfd, hmem⟩ := @exists_reduced_basis Λ hd hZ
  obtain ⟨a, b, c', ha, -, hq, hdisc⟩ := hC k R hR Λ c τ hc τ.im_pos hmem ⟨iso⟩
  refine ⟨τ, ⟨Λ, Φ, hΦ, c, hc, hmem⟩, ?_, ?_⟩
  · have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hfd
    have hpos := τ.im_pos
    have : Real.sqrt 3 ≤ 2 * τ.im := by
      rw [show (3 : ℝ) = 3 by rfl]
      refine Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    show Real.sqrt 3 / 2 ≤ τ.im
    linarith
  · have := im_le_of_quadratic ha τ.im_pos hq
    rw [hdisc] at this
    exact this

end CMBranch
end HDec
