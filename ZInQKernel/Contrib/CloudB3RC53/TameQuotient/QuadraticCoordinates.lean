import ZInQKernel.Contrib.CloudB3RC53.TameQuotient.TameCharacter
import Mathlib.Topology.Instances.ZMod

/-!
# Quadratic characters of an inert local Galois group: the tame coordinates

Manuscript `diophantine_zq.tex`, tex L5027–5037: with `𝔽₂` coefficients and odd residue
characteristic, a continuous character `z : G_K → 𝔽₂` is determined by its values at a Frobenius
lift `φ` and a tame inertia generator `σ`, and `z(σ) = 0` forces `z` to vanish on inertia.

Setting: `K` a nonarchimedean local field with residue characteristic `p ≠ 2`, `ϖ` a uniformizer,
`α ∈ K^{alg}` with `α² = ϖ`, `σ ∈ I_K` with `σ α = −α` (a tame generator at level `2`,
`exists_tame_generator`), `φ` an arithmetic Frobenius lift (one fixing `α` exists,
`exists_frobeniusLift_fix`). A **character** is a continuous additive `z : G_K → ZMod 2`.

* `eq_zero_on_inertia_of_apply_tame_eq_zero` (**hI**): `z(σ) = 0 ⇒ z = 0` on `I_K`. Proof: by
  Kummer theory (Tau Ceti's `kummerMap_surjective`, `μ₂ ⊂ K` so coboundaries vanish) `z` is the
  Kummer character `g ↦ g β / β` of a square root `β` of some `a ∈ Kˣ`; writing `a = u ϖ^k` with
  `u` a unit, `β = γ α^k` with `γ² = u` unramified, so on `I_K` the character is
  `g ↦ (g α / α)^k`; `z(σ) = 0` makes `k` even, hence `z = 0` on `I_K`.
* `eq_zero_of_eq_zero_on_inertia`: `z(φ) = 0` and `z = 0` on `I_K` give `z = 0` (Frobenius and
  inertia generate `G_K` topologically, Tau Ceti).
* `ramChar`, `urChar`: the ramified character `g ↦ [g α ≠ α]` and the unramified character (parity
  of the `ℤ̂`-coordinate), with values `(0, 1)` and `(1, 0)` at `(φ, σ)` when `φ α = α`;
* `coord_bijective`: `z ↦ (z(φ), z(σ))` is a bijection from the characters onto `𝔽₂ × 𝔽₂`.

All PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TameQuotient

open TauCeti ValuativeRel IntermediateField ContCohomology

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Every element of `μ₂(Kˢ)` is fixed by `G_K` (it is `±1`). -/
theorem smul_kummerCoeff_two (τ : AbsoluteGaloisGroup K) (x : KummerCoeff K 2) : τ • x = x := by
  refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
  have hx : ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) *
      ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) = 1 := by
    have := congrArg (fun u : (SeparableClosure K)ˣ => (u : SeparableClosure K))
      ((mem_rootsOfUnity _ _).1 x.toMul.2)
    simpa [sq] using this
  simp only [Additive.toMul_smul, rootsOfUnity.coe_smul, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_ofClass]
  rcases mul_self_eq_one_iff.1 hx with h | h <;> rw [h] <;> simp

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An element of `K^{alg}` with the same square as `α ≠ 0` is `± α`. -/
theorem eq_or_eq_neg_of_sq_eq {α β : AlgebraicClosure K} (h : β ^ 2 = α ^ 2) : β = α ∨ β = -α :=
  sq_eq_sq_iff_eq_or_eq_neg.1 h

/-- **(hI) A character vanishing at the tame generator vanishes on inertia.** -/
theorem eq_zero_on_inertia_of_apply_tame_eq_zero (hp : ringChar 𝓀[K] ≠ 2)
    {ϖ : Kˣ} (hϖ : normalizedValuation K ϖ = .ofAdd 1)
    {α : AlgebraicClosure K} (hα : α ^ 2 = algebraMap K (AlgebraicClosure K) ϖ)
    {σ : Gal(AlgebraicClosure K/K)} (hσI : σ ∈ inertiaSubgroup K) (hσα : σ α = -α)
    (z : Gal(AlgebraicClosure K/K) → ZMod 2) (hz : Continuous z)
    (hadd : ∀ g h, z (g * h) = z g + z h) (hzσ : z σ = 0) :
    ∀ g : Gal(AlgebraicClosure K/K), g ∈ inertiaSubgroup K → z g = 0 := by
  -- arithmetic of `2`
  have hpr : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar 𝓀[K]
  have h2c : (2 : ℕ).Coprime (ringChar 𝓀[K]) :=
    (Nat.coprime_primes Nat.prime_two hpr).2 (Ne.symm hp)
  have h2K : (2 : K) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_coprime_ringChar h2c
  have hn2 : IsUnit ((2 : ℕ) : K) := isUnit_iff_ne_zero.2 (by exact_mod_cast h2K)
  have h2S : (2 : SeparableClosure K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (SeparableClosure K)) 2]
    exact (map_ne_zero _).2 h2K
  have h2A : (2 : AlgebraicClosure K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (AlgebraicClosure K)) 2]
    exact (map_ne_zero _).2 h2K
  have hneg1 : (-1 : SeparableClosure K) ≠ 1 := by
    intro h
    apply h2S
    linear_combination -h
  -- the coefficient map `e : ZMod 2 → μ₂`
  set mneg : KummerCoeff K 2 := Additive.ofMul ⟨-1, by
    rw [mem_rootsOfUnity]; simp⟩ with hmneg
  have hm2 : mneg + mneg = 0 := by
    refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
    simp [hmneg]
  have hm0 : mneg ≠ 0 := by
    intro h
    have := congrArg (fun x : KummerCoeff K 2 =>
      (((Additive.toMul x : rootsOfUnity 2 (SeparableClosure K)) : (SeparableClosure K)ˣ) :
        SeparableClosure K)) h
    simp [hmneg] at this
    exact hneg1 this
  let e : ZMod 2 → KummerCoeff K 2 := fun x => if x = 0 then 0 else mneg
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have he_add : ∀ x y, e (x + y) = e x + e y := by
    intro x y
    rcases h01 x with rfl | rfl <;> rcases h01 y with rfl | rfl
    · simp [e]
    · simp [e]
    · simp [e]
    · simp [e, h11, hm2]
  have he_inj : ∀ x, e x = 0 → x = 0 := by
    intro x hx
    rcases h01 x with rfl | rfl
    · rfl
    · exact absurd hx (by simpa [e] using hm0)
  -- the cocycle attached to `z`
  set R := absoluteGaloisGroupRestrictEquiv K
  let c : AbsoluteGaloisGroup K → KummerCoeff K 2 := fun τ => e (z (R.symm τ))
  have hc : c ∈ Z1 (AbsoluteGaloisGroup K) (KummerCoeff K 2) := by
    refine mem_Z1_iff.2 ⟨?_, fun g h => ?_⟩
    · exact (continuous_of_discreteTopology (f := e)).comp (hz.comp R.symm.continuous)
    · change e (z (R.symm (g * h))) = g • e (z (R.symm h)) + e (z (R.symm g))
      rw [smul_kummerCoeff_two, map_mul]
      rw [show z (R.symm g * R.symm h) = z (R.symm g) + z (R.symm h) from hadd _ _, he_add,
        add_comm]
  -- Kummer: `c` is the Kummer cocycle of a square root `β` of some `a ∈ Kˣ`
  obtain ⟨a, ha⟩ := kummerMap_surjective hn2
    (Multiplicative.ofAdd (H1pi (AbsoluteGaloisGroup K) (KummerCoeff K 2) ⟨c, hc⟩))
  obtain ⟨β, hβ⟩ := exists_pow_eq_units_map hn2 a
  have hcl := kummerMap_eq_kummerCocycleClass hn2 hβ
  rw [ha, toAdd_ofAdd, kummerCocycleClass_def, eq_comm] at hcl
  simp only [QuotientAddGroup.mk'_apply] at hcl
  rw [H1pi_eq_iff, mem_B1_iff] at hcl
  obtain ⟨m, hm⟩ := hcl
  have hκc : ∀ τ, kummerCocycle hβ τ = c τ := by
    intro τ
    have := hm τ
    rw [smul_kummerCoeff_two, sub_self] at this
    exact sub_eq_zero.1 this.symm
  -- the root `b` of `a` in `K^{alg}`
  set b : AlgebraicClosure K := ((β : SeparableClosure K) : AlgebraicClosure K) with hb
  have hb2 : b ^ 2 = algebraMap K (AlgebraicClosure K) a := by
    have := congrArg (fun v : (SeparableClosure K)ˣ ↦
      ((v : SeparableClosure K) : AlgebraicClosure K)) hβ
    simpa using this
  have hb0 : b ≠ 0 := by simp [hb]
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hα
    exact ϖ.ne_zero ((map_eq_zero _).1 hα.symm)
  have hfix : ∀ g : Gal(AlgebraicClosure K/K), kummerCocycle hβ (R g) = 0 ↔ g b = b := by
    intro g
    rw [kummerCocycle_eq_zero_iff, Units.ext_iff, AlgEquiv.smul_units_def, Units.coe_map,
      MonoidHom.coe_ofClass, ← coe_absoluteGaloisGroupRestrictEquiv_apply K g, SetLike.coe_eq_coe]
  have hcz : ∀ g : Gal(AlgebraicClosure K/K), c (R g) = e (z g) := by
    intro g
    exact congrArg (fun x => e (z x)) (R.symm_apply_apply g)
  -- decomposition `a = u ϖ^k`
  set k : ℤ := (normalizedValuation K a).toAdd with hk
  have hu := mul_zpow_neg_mem_unitFiltration_zero hϖ a
  set γ : AlgebraicClosure K := b / α ^ k with hγ
  have hγ2 : γ ^ 2 = algebraMap K (AlgebraicClosure K) ((a * ϖ ^ (-k) : Kˣ) : K) := by
    have hpow : (α ^ k) ^ 2 = (α ^ 2) ^ k := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [hγ, div_pow, hpow, hα, hb2, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, zpow_neg,
      div_eq_mul_inv]
  have hγur : γ ∈ maximalUnramifiedExtension K (AlgebraicClosure K) :=
    mem_maximalUnramifiedExtension_of_pow_eq (by
      intro h
      exact hp ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 h)) hu hγ2
  -- on inertia, `g b = ε^k b` with `g α = ε α`
  have hbI : ∀ g : Gal(AlgebraicClosure K/K), g ∈ inertiaSubgroup K →
      ∀ ε : AlgebraicClosure K, g α = ε * α → g b = ε ^ k * b := by
    intro g hg ε hε
    have hgγ : g γ = γ := mem_inertiaSubgroup_iff.1 hg γ hγur
    have hbγ : b = γ * α ^ k := by rw [hγ, div_mul_cancel₀ _ (zpow_ne_zero _ hα0)]
    rw [hbγ, map_mul, hgγ, map_zpow₀, hε, mul_zpow]
    ring
  -- at `σ`: `(-1)^k = 1`, so `k` is even
  have hσb : σ b = b := by
    rw [← hfix, hκc, hcz, hzσ]
    simp [e]
  have hkeven : Even k := by
    have h1 := hbI σ hσI (-1) (by rw [hσα]; ring)
    rw [hσb] at h1
    have h2 : ((-1 : AlgebraicClosure K)) ^ k = 1 :=
      mul_right_cancel₀ hb0 (h1.symm.trans (one_mul b).symm)
    rcases Int.even_or_odd k with he | ho
    · exact he
    · rw [ho.neg_one_zpow] at h2
      exact absurd (by linear_combination -h2 : (2 : AlgebraicClosure K) = 0) h2A
  -- on inertia the character vanishes
  intro g hg
  have hgα : (g α) ^ 2 = α ^ 2 := by rw [← map_pow, hα, AlgEquiv.commutes]
  have hgb : g b = b := by
    rcases eq_or_eq_neg_of_sq_eq hgα with h | h
    · rw [hbI g hg 1 (by rw [h, one_mul]), one_zpow, one_mul]
    · rw [hbI g hg (-1) (by rw [h]; ring), hkeven.neg_one_zpow, one_mul]
  apply he_inj
  rw [← hcz, ← hκc]
  exact (hfix g).2 hgb

/-- **A character vanishing on inertia and at a Frobenius lift vanishes**: Frobenius and inertia
generate `G_K` topologically. -/
theorem eq_zero_of_eq_zero_on_inertia {φ : Gal(AlgebraicClosure K/K)} (hφ : IsArithFrobeniusLift K φ)
    (z : Gal(AlgebraicClosure K/K) → ZMod 2) (hz : Continuous z)
    (hadd : ∀ g h, z (g * h) = z g + z h) (hzφ : z φ = 0)
    (hI : ∀ g : Gal(AlgebraicClosure K/K), g ∈ inertiaSubgroup K → z g = 0) :
    ∀ g, z g = 0 := by
  have h1 : z 1 = 0 := by
    have := hadd 1 1
    rw [mul_one] at this
    simpa using this
  let N : Subgroup (Field.absoluteGaloisGroup K) :=
    { carrier := {g | z g = 0}
      one_mem' := h1
      mul_mem' := fun {a b} (ha : z a = 0) (hb : z b = 0) =>
        show z (a * b) = 0 from (hadd a b).trans (by rw [ha, hb, add_zero])
      inv_mem' := fun {a} (ha : z a = 0) => by
        show z a⁻¹ = 0
        let a' : Gal(AlgebraicClosure K/K) := a
        have := hadd a'⁻¹ a'
        rw [inv_mul_cancel, h1, show z a' = 0 from ha, add_zero] at this
        exact this.symm }
  have hN : IsClosed (N : Set (Field.absoluteGaloisGroup K)) :=
    isClosed_eq hz continuous_const
  have hle : Subgroup.zpowers (show Field.absoluteGaloisGroup K from φ) ⊔ inertiaSubgroup K ≤ N :=
    sup_le ((Subgroup.zpowers_le (G := Field.absoluteGaloisGroup K)).2 hzφ) hI
  have htop := hφ.topologicalClosure_zpowers_sup_inertiaSubgroup
  intro g
  have : g ∈ N := Subgroup.topologicalClosure_minimal _ hle hN (htop ▸ Subgroup.mem_top g)
  exact this

/-! ### The two basic characters -/

variable (K) in
/-- **The unramified character**: the parity of the `ℤ̂`-coordinate of the restriction to
`K^{ur}`. -/
def urChar (g : Gal(AlgebraicClosure K/K)) : ZMod 2 :=
  Multiplicative.toAdd ((zHat.lift (Multiplicative.ofAdd (1 : ZMod 2)) :
    zHat →ₜ* Multiplicative (ZMod 2))
    (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)
      (restrictMaximalUnramifiedHom K g)))

theorem urChar_mul (g h : Gal(AlgebraicClosure K/K)) :
    urChar K (g * h) = urChar K g + urChar K h := by
  simp only [urChar]
  rw [show restrictMaximalUnramifiedHom K (g * h) =
    restrictMaximalUnramifiedHom K g * restrictMaximalUnramifiedHom K h from map_mul _ _ _,
    map_mul, map_mul, toAdd_mul]

theorem continuous_urChar : Continuous (urChar K) :=
  (continuous_of_discreteTopology (f := (Multiplicative.toAdd : Multiplicative (ZMod 2) → ZMod 2))).comp
    ((zHat.lift (Multiplicative.ofAdd (1 : ZMod 2))).continuous.comp
      ((maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)).continuous.comp
        (continuous_restrictMaximalUnramifiedHom K)))

theorem urChar_frobenius {φ : Gal(AlgebraicClosure K/K)} (hφ : IsArithFrobeniusLift K φ) :
    urChar K φ = 1 := by
  simp only [urChar]
  rw [show restrictMaximalUnramifiedHom K φ = maximalUnramifiedFrobenius K (AlgebraicClosure K)
    from hφ, maximalUnramifiedGaloisGroupEquivZHat_apply_frobenius, zHat.lift_gen, toAdd_ofAdd]

theorem urChar_inertia {g : Gal(AlgebraicClosure K/K)} (hg : g ∈ inertiaSubgroup K) :
    urChar K g = 0 := by
  have hk : restrictMaximalUnramifiedHom K g = 1 := by
    rw [← ker_restrictMaximalUnramifiedHom] at hg
    exact hg
  simp only [urChar, hk]
  rw [show (maximalUnramifiedGaloisGroupEquivZHat K (AlgebraicClosure K)) 1 = 1 from map_one _,
    show ((zHat.lift (Multiplicative.ofAdd (1 : ZMod 2)) : zHat →ₜ* Multiplicative (ZMod 2))) 1 = 1
      from map_one _]
  rfl

open scoped Classical in
/-- **The ramified character** of a square root `α` of an element of `K`: `g ↦ [g α ≠ α]`. -/
def ramChar (α : AlgebraicClosure K) (g : Gal(AlgebraicClosure K/K)) : ZMod 2 :=
  if g α = α then 0 else 1

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem ramChar_mul {c : K} {α : AlgebraicClosure K}
    (hα : α ^ 2 = algebraMap K (AlgebraicClosure K) c) (hα0 : α ≠ 0)
    (h2A : (2 : AlgebraicClosure K) ≠ 0) (g h : Gal(AlgebraicClosure K/K)) :
    ramChar α (g * h) = ramChar α g + ramChar α h := by
  have hsign : ∀ g : Gal(AlgebraicClosure K/K), g α = α ∨ g α = -α := fun g =>
    eq_or_eq_neg_of_sq_eq (by rw [← map_pow, hα, AlgEquiv.commutes])
  have hne : -α ≠ α := by
    intro h
    exact mul_ne_zero h2A hα0 (by linear_combination -h)
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  simp only [ramChar]
  rw [AlgEquiv.mul_apply]
  rcases hsign h with hh | hh <;> rcases hsign g with hg | hg
  · simp [hh, hg]
  · simp [hh, hg, hne]
  · rw [hh, map_neg, hg]; simp [hne]
  · rw [hh, map_neg, hg, neg_neg]; simp [hne, h11]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem continuous_ramChar {c : K} {α : AlgebraicClosure K}
    (hα : α ^ 2 = algebraMap K (AlgebraicClosure K) c) (hα0 : α ≠ 0)
    (h2A : (2 : AlgebraicClosure K) ≠ 0) : Continuous (ramChar α) := by
  let f : Gal(AlgebraicClosure K/K) →* Multiplicative (ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd (ramChar α g)
      map_one' := by simp [ramChar]
      map_mul' := fun g h => by rw [ramChar_mul hα hα0 h2A, ofAdd_add] }
  have : FiniteDimensional K K⟮α⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)
  have hopen := IntermediateField.fixingSubgroup_isOpen K⟮α⟯
  have hf : ContinuousAt f 1 := by
    refine (continuousAt_const (y := (1 : Multiplicative (ZMod 2)))).congr ?_
    filter_upwards [hopen.mem_nhds (K⟮α⟯).fixingSubgroup.one_mem] with g hg
    have hgα : g α = α := hg ⟨α, IntermediateField.mem_adjoin_simple_self K α⟩
    change (1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd (ramChar α g)
    simp [ramChar, hgα]
  exact (continuous_of_discreteTopology
    (f := (Multiplicative.toAdd : Multiplicative (ZMod 2) → ZMod 2))).comp
    (continuous_of_continuousAt_one f hf)

/-- **The tame coordinates** (tex L5027–5037), `p ≠ 2`: for a Frobenius lift `φ` fixing `α`
(`α² = ϖ`) and `σ ∈ I_K` with `σ α = −α`, the map `z ↦ (z(φ), z(σ))` from the continuous characters
`G_K → 𝔽₂` to `𝔽₂ × 𝔽₂` is bijective. -/
theorem coord_bijective (hp : ringChar 𝓀[K] ≠ 2)
    {ϖ : Kˣ} (hϖ : normalizedValuation K ϖ = .ofAdd 1)
    {α : AlgebraicClosure K} (hα : α ^ 2 = algebraMap K (AlgebraicClosure K) ϖ)
    {φ : Gal(AlgebraicClosure K/K)} (hφ : IsArithFrobeniusLift K φ) (hφα : φ α = α)
    {σ : Gal(AlgebraicClosure K/K)} (hσI : σ ∈ inertiaSubgroup K) (hσα : σ α = -α) :
    Function.Bijective (fun z : {z : Gal(AlgebraicClosure K/K) → ZMod 2 //
        Continuous z ∧ ∀ g h, z (g * h) = z g + z h} => (z.1 φ, z.1 σ)) := by
  have hpr : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar 𝓀[K]
  have h2c : (2 : ℕ).Coprime (ringChar 𝓀[K]) :=
    (Nat.coprime_primes Nat.prime_two hpr).2 (Ne.symm hp)
  have h2K : (2 : K) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_coprime_ringChar h2c
  have h2A : (2 : AlgebraicClosure K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (AlgebraicClosure K)) 2]
    exact (map_ne_zero _).2 h2K
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hα
    exact ϖ.ne_zero ((map_eq_zero _).1 hα.symm)
  have hne : -α ≠ α := by
    intro h
    exact mul_ne_zero h2A hα0 (by linear_combination -h)
  constructor
  · rintro ⟨z₁, hc₁, ha₁⟩ ⟨z₂, hc₂, ha₂⟩ h
    simp only [Prod.mk.injEq] at h
    have hd := eq_zero_of_eq_zero_on_inertia hφ (fun g => z₁ g - z₂ g) (hc₁.sub hc₂)
      (fun g h => by rw [ha₁, ha₂]; ring) (by rw [h.1, sub_self])
      (eq_zero_on_inertia_of_apply_tame_eq_zero hp hϖ hα hσI hσα (fun g => z₁ g - z₂ g)
        (hc₁.sub hc₂) (fun g h => by rw [ha₁, ha₂]; ring) (by rw [h.2, sub_self]))
    exact Subtype.ext (funext fun g => sub_eq_zero.1 (hd g))
  · rintro ⟨x, y⟩
    refine ⟨⟨fun g => x * urChar K g + y * ramChar α g,
      (continuous_of_discreteTopology (f := fun q : ZMod 2 × ZMod 2 => x * q.1 + y * q.2)).comp
        (continuous_urChar.prodMk (continuous_ramChar hα hα0 h2A)),
      fun g h => by
        show x * urChar K (g * h) + y * ramChar α (g * h) =
          (x * urChar K g + y * ramChar α g) + (x * urChar K h + y * ramChar α h)
        rw [urChar_mul, ramChar_mul hα hα0 h2A]; ring⟩, ?_⟩
    have hσne : ¬ σ α = α := fun h => hne (hσα.symm.trans h)
    simp [urChar_frobenius hφ, urChar_inertia hσI, ramChar, hφα, hσne]

/-- **The tame coordinates exist** (`p ≠ 2`): there are an arithmetic Frobenius lift `φ` and
`σ ∈ I_K` such that `z ↦ (z(φ), z(σ))` is a bijection from the continuous characters `G_K → 𝔽₂` onto
`𝔽₂ × 𝔽₂`, and every character vanishing at `σ` vanishes on `I_K`. PROVED (the GLUE content of
SwitchInputs' `TameCoordinates` for trivial coefficients `𝔽₂`). -/
theorem exists_tame_coordinates (hp : ringChar 𝓀[K] ≠ 2) :
    ∃ φ σ : Gal(AlgebraicClosure K/K), IsArithFrobeniusLift K φ ∧ σ ∈ inertiaSubgroup K ∧
      Function.Bijective (fun z : {z : Gal(AlgebraicClosure K/K) → ZMod 2 //
        Continuous z ∧ ∀ g h, z (g * h) = z g + z h} => (z.1 φ, z.1 σ)) ∧
      ∀ z : Gal(AlgebraicClosure K/K) → ZMod 2, Continuous z → (∀ g h, z (g * h) = z g + z h) →
        z σ = 0 → ∀ g : Gal(AlgebraicClosure K/K), g ∈ inertiaSubgroup K → z g = 0 := by
  have hpr : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar 𝓀[K]
  have h2c : (2 : ℕ).Coprime (ringChar 𝓀[K]) :=
    (Nat.coprime_primes Nat.prime_two hpr).2 (Ne.symm hp)
  obtain ⟨ϖ, hϖu⟩ := exists_isUniformizer (K := K)
  have hϖ : normalizedValuation K ϖ = .ofAdd 1 := (isUniformizer_def ϖ).1 hϖu
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (ϖ : K)) two_pos
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hα
    exact ϖ.ne_zero ((map_eq_zero _).1 hα.symm)
  have hv : (normalizedValuation K (Units.mk0 (ϖ : K) ϖ.ne_zero)).toAdd = 1 := by
    rw [Units.mk0_val, hϖ, toAdd_ofAdd]
  obtain ⟨φ, hφ, hφα⟩ := exists_frobeniusLift_fix h2c hα hα0 ϖ.ne_zero hv
  obtain ⟨σ, hσI, hσprim⟩ := exists_tame_generator h2c hα hα0 ϖ.ne_zero hv
  have hσα : σ α = -α := by
    rw [apply_eq_kummerVal_mul hα0, hσprim.eq_neg_one_of_two_right, neg_one_mul]
  exact ⟨φ, σ, hφ, hσI, coord_bijective hp hϖ hα hφ hφα hσI hσα,
    fun z hz hadd hzσ => eq_zero_on_inertia_of_apply_tame_eq_zero hp hϖ hα hσI hσα z hz hadd hzσ⟩

end ZInQ.Contrib.CloudB3RC53.TameQuotient
