import FrobLift.ProfiniteLiftV004

/-!
# Action of the Frobenius lift: decomposition group, residue surjectivity, powers, roots of unity

Same setting as `FrobLift.ProfiniteLiftV004`. With `B` the integral closure of `O` in `Ω` and
`Q = 𝔪_w ∩ B`:

* the decomposition group of `w` equals the stabilizer of `Q` (`decomposition_eq_stabilizer`);
* it surjects onto `Aut((B/Q)/(O/𝔪_O))` (`decomposition_residue_surjective`);
* a Frobenius lift `σ` is an arithmetic Frobenius at `Q` (`isArithFrobAt_of_congr`), its powers
  satisfy `σ^r x ≡ x^(q^r)` on `w` (`pow_congr`), and `σ^r ζ = ζ^(q^r)` exactly for roots of unity of
  order invertible in `O` (`pow_apply_rootOfUnity`).
-/

noncomputable section

namespace FrobLift

open scoped Pointwise

attribute [local instance] Ideal.Quotient.field primeQ_liesOver

variable {K : Type} [Field K] [NumberField K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {w : ValuationSubring Ω}

omit [NumberField K] [IsAlgClosure K Ω] in
theorem mem_iff_of_decomp {g : Ω ≃ₐ[K] Ω} (hg : g ∈ w.decompositionSubgroup K) (z : Ω) :
    g z ∈ w ↔ z ∈ w := by
  have h : g • w = w := hg
  have h2 := ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := w) (x := z)
  rw [h] at h2
  exact h2

theorem val_lt_one_iff_inv (w : ValuationSubring Ω) (y : Ω) :
    w.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ w := by
  by_cases hy : y = 0
  · simp [hy]
  have h1 : 0 < w.valuation y := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hy)
  rw [← not_le, ← inv_le_one₀ h1, ← map_inv₀, ValuationSubring.valuation_le_one_iff]
  simp [hy]

omit [NumberField K] [IsAlgClosure K Ω] in
theorem decomp_val_lt_one {g : Ω ≃ₐ[K] Ω} (hg : g ∈ w.decompositionSubgroup K) (y : Ω) :
    w.valuation (g y) < 1 ↔ w.valuation y < 1 := by
  rw [val_lt_one_iff_inv, val_lt_one_iff_inv, ← map_inv₀, mem_iff_of_decomp hg,
    map_eq_zero_iff g g.injective]

/-- **The decomposition group of `w` is the stabilizer of `Q = 𝔪_w ∩ B`.** -/
theorem decomposition_eq_stabilizer (hw : w.comap (algebraMap K Ω) = O) :
    w.decompositionSubgroup K = MulAction.stabilizer (Ω ≃ₐ[K] Ω) (primeQ hw) := by
  have hden := fun x (hx : x ∈ w) => exists_unit_denom_intClosure hw hx
  ext g
  constructor
  · intro hg
    show g • primeQ hw = primeQ hw
    ext b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_primeQ, mem_primeQ]
    exact decomp_val_lt_one (inv_mem hg) (b : Ω)
  · intro hg
    have hginv : g⁻¹ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) (primeQ hw) := inv_mem hg
    show g • w = w
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hy
      have := stab_maps_mem hw hden hg hy
      rwa [AlgEquiv.smul_def, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at this
    · intro hy
      exact stab_maps_mem hw hden hginv hy

/-- **Residue surjectivity for the decomposition group** (profinite stabilization): every
automorphism of `B/Q` over `O/𝔪_O` is induced by an element of the decomposition group of `w`. -/
theorem decomposition_residue_surjective (hw : w.comap (algebraMap K Ω) = O)
    (τ : (integralClosure O Ω ⧸ primeQ hw) ≃ₐ[O ⧸ IsLocalRing.maximalIdeal O]
      (integralClosure O Ω ⧸ primeQ hw)) :
    ∃ σ : Ω ≃ₐ[K] Ω, σ ∈ w.decompositionSubgroup K ∧ ∀ b : integralClosure O Ω,
      Ideal.Quotient.mk (primeQ hw) (σ • b) = τ (Ideal.Quotient.mk (primeQ hw) b) := by
  set B := integralClosure O Ω
  set G := Ω ≃ₐ[K] Ω
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  haveI : ContinuousSMul G B := continuousSMul K O Ω
  haveI : Algebra.IsInvariant O B G := isInvariant K O Ω
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G)
    (IsLocalRing.maximalIdeal O) (primeQ hw) τ
  refine ⟨σ.1, (decomposition_eq_stabilizer hw).symm ▸ σ.2, fun b => ?_⟩
  have h1 := congrArg (fun e => e (Ideal.Quotient.mk (primeQ hw) b)) hσ
  simp only [Ideal.Quotient.stabilizerHom_apply] at h1
  exact h1

omit [NumberField K] [IsAlgClosure K Ω] in
theorem pow_sub_pow_lt {a b : Ω} (ha : a ∈ w) (hb : b ∈ w) (h : w.valuation (a - b) < 1)
    (n : ℕ) : w.valuation (a ^ n - b ^ n) < 1 := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨a, ha⟩ : w) ⟨b, hb⟩ n
  have hc' : a ^ n - b ^ n = (a - b) * (c : Ω) := by
    have := congrArg Subtype.val hc
    simpa using this
  rw [hc', map_mul]
  calc w.valuation (a - b) * w.valuation (c : Ω) ≤ w.valuation (a - b) * 1 := by
        gcongr
        exact (ValuationSubring.valuation_le_one_iff w _).2 c.2
    _ < 1 := by rw [mul_one]; exact h

omit [NumberField K] [IsAlgClosure K Ω] in
/-- **Powers of a Frobenius lift**: `σ^r x ≡ x^(q^r) (mod 𝔪_w)` for all `x ∈ w`. -/
theorem pow_congr {σ : Ω ≃ₐ[K] Ω} (hD : σ ∈ w.decompositionSubgroup K) {q : ℕ}
    (hq : ∀ x ∈ w, w.valuation (σ x - x ^ q) < 1) (r : ℕ) :
    ∀ x ∈ w, w.valuation ((σ ^ r) x - x ^ (q ^ r)) < 1 := by
  induction r with
  | zero =>
    intro x _
    simp
  | succ r ih =>
    intro x hx
    have hy : (σ ^ r) x ∈ w := (mem_iff_of_decomp (pow_mem hD r) x).2 hx
    have hz : x ^ (q ^ r) ∈ w := pow_mem hx _
    have e : (σ ^ (r + 1)) x - x ^ (q ^ (r + 1)) =
        (σ ((σ ^ r) x) - ((σ ^ r) x) ^ q) + (((σ ^ r) x) ^ q - (x ^ (q ^ r)) ^ q) := by
      rw [pow_succ', AlgEquiv.mul_apply, pow_succ, pow_mul]
      ring
    rw [e]
    exact Valuation.map_add_lt _ (hq _ hy) (pow_sub_pow_lt hy hz (ih x hx) q)

/-- A Frobenius lift is an arithmetic Frobenius at `Q` (in Mathlib's `IsArithFrobAt` sense). -/
theorem isArithFrobAt_of_congr (hw : w.comap (algebraMap K Ω) = O) {σ : Ω ≃ₐ[K] Ω}
    (hq : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1) :
    IsArithFrobAt O σ (primeQ hw) := by
  intro b
  rw [← (primeQ_liesOver hw).over, mem_primeQ]
  exact hq b (intClosure_mem hw b)

/-- **Roots of unity**: a Frobenius lift acts on roots of unity of order invertible in `O`
by `ζ ↦ ζ^q` exactly. -/
theorem apply_rootOfUnity (hw : w.comap (algebraMap K Ω) = O) {σ : Ω ≃ₐ[K] Ω}
    (hq : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1)
    {ζ : Ω} {N : ℕ} (hζ : ζ ^ N = 1) (hN : IsUnit (N : O)) :
    σ ζ = ζ ^ Nat.card (IsLocalRing.ResidueField O) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have hint : IsIntegral O ζ :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hN0) (by rw [hζ]; exact isIntegral_one)
  set ζB : integralClosure O Ω := ⟨ζ, (mem_integralClosure_iff O Ω).mpr hint⟩
  have H := isArithFrobAt_of_congr hw hq
  have hζB : ζB ^ N = 1 := Subtype.ext (by simpa [ζB] using hζ)
  have hNQ : (N : integralClosure O Ω) ∉ primeQ hw := by
    rw [mem_primeQ]
    have hc : ((N : integralClosure O Ω) : Ω) = algebraMap K Ω (N : K) := by simp
    rw [hc, val_lt_one_iff_of_comap hw]
    intro hlt
    have hmem : (N : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [ValuationSubring.valuation_lt_one_iff]
      simpa using hlt
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hN
  have key := H.apply_of_pow_eq_one hζB hNQ
  rw [← (primeQ_liesOver hw).over] at key
  exact congrArg Subtype.val key

/-- **Powers on roots of unity**: `σ^r ζ = ζ^(q^r)`. -/
theorem pow_apply_rootOfUnity (hw : w.comap (algebraMap K Ω) = O) {σ : Ω ≃ₐ[K] Ω}
    (hq : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1)
    {ζ : Ω} {N : ℕ} (hζ : ζ ^ N = 1) (hN : IsUnit (N : O)) (r : ℕ) :
    (σ ^ r) ζ = ζ ^ (Nat.card (IsLocalRing.ResidueField O) ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, apply_rootOfUnity hw hq hζ hN, ← pow_mul,
      pow_succ, mul_comm]

end FrobLift
