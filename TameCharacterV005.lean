import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Algebraic.Integral

/-!
# The tame character of inertia and the Frobenius congruence

For a valuation subring `w` of a field `L` and `K`-automorphisms of `L`:

* an automorphism `σ` preserving the valuation and acting trivially on residues of
  units (the inertia conditions) has a residue ratio `σ x / x` that depends only on
  the valuation of `x` modulo the maximal ideal (`ratio_cong`);
* its powers satisfy `σ^n x / x ≡ (σ x / x)^n` (`pow_ratio_cong`);
* **Frobenius congruence**: if `φ` preserves the valuation and induces `u ↦ u^q` on
  residues of units, then `σ^q x ≡ φ σ φ⁻¹ x` with strict displacement, i.e.
  `(φ σ φ⁻¹)⁻¹ σ^q` is wild (`frobenius_congr`, `isWild_frobenius`);
* inertia elements commute modulo wild ones (`commutator_congr`);
* on an algebraic extension, elements of the decomposition group preserve the
  valuation (`preserves_of_mem_decomposition`), and elements of the inertia group
  satisfy the inertia conditions (`inertia_conditions`), so the congruences hold for
  the inertia subgroup itself (`isWild_frobenius_of_inertia`,
  `isWild_commutator_of_inertia`).

Here *wild* is the strict displacement condition `v(σ x − x) < v(x)` for all
`x ≠ 0`. These are the valuation computations behind the tame character
`σ ↦ (σ x / x mod 𝔪)`, written without uniformizers, so they apply to the
non-discrete valuation ring of an algebraic closure.
-/

noncomputable section
set_option autoImplicit false

namespace WildTameCharacter

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {w : ValuationSubring L}

/-- Strict displacement (the wild condition). -/
def IsWild (w : ValuationSubring L) (σ : L ≃ₐ[K] L) : Prop :=
  ∀ x : L, x ≠ 0 → w.valuation (σ x - x) < w.valuation x

/-- Congruence modulo the maximal ideal, in valuation form. -/
def Cong (w : ValuationSubring L) (a b : L) : Prop :=
  w.valuation (a - b) < 1

/-- An automorphism preserves the valuation. -/
def Preserves (w : ValuationSubring L) (g : L ≃ₐ[K] L) : Prop :=
  ∀ x : L, w.valuation (g x) = w.valuation x

theorem Cong.refl (a : L) : Cong w a a := by
  simp [Cong]

theorem Cong.symm {a b : L} (h : Cong w a b) : Cong w b a := by
  unfold Cong at *
  rwa [Valuation.map_sub_swap]

theorem Cong.trans {a b c : L} (h1 : Cong w a b) (h2 : Cong w b c) : Cong w a c := by
  unfold Cong at *
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]
  exact Valuation.map_add_lt _ h1 h2

theorem Cong.mul {a a' b b' : L} (ha : w.valuation a = 1) (hb' : w.valuation b' = 1)
    (h1 : Cong w a a') (h2 : Cong w b b') : Cong w (a * b) (a' * b') := by
  unfold Cong at *
  have : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [this]
  apply Valuation.map_add_lt
  · rw [Valuation.map_mul, ha, one_mul]
    exact h2
  · rw [Valuation.map_mul, hb', mul_one]
    exact h1

theorem Cong.pow {a b : L} (ha : w.valuation a = 1) (hb : w.valuation b = 1)
    (h : Cong w a b) (n : ℕ) : Cong w (a ^ n) (b ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Cong.refl (1 : L)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact Cong.mul (by rw [Valuation.map_pow, ha, one_pow]) hb ih h

theorem Preserves.inv {g : L ≃ₐ[K] L} (hg : Preserves w g) : Preserves w g⁻¹ := by
  intro x
  have h := hg (g⁻¹ x)
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h
  exact h.symm

theorem Preserves.mul {g h : L ≃ₐ[K] L} (hg : Preserves w g) (hh : Preserves w h) :
    Preserves w (g * h) := by
  intro x
  rw [AlgEquiv.mul_apply, hg, hh]

theorem Preserves.pow {g : L ≃ₐ[K] L} (hg : Preserves w g) (n : ℕ) : Preserves w (g ^ n) := by
  induction n with
  | zero => intro x; simp
  | succ n ih => rw [pow_succ']; exact hg.mul ih

/-- The residue ratio of a valuation-preserving automorphism is a unit. -/
theorem val_ratio {σ : L ≃ₐ[K] L} (hv : Preserves w σ) {x : L} (hx : x ≠ 0) :
    w.valuation (σ x / x) = 1 := by
  rw [Valuation.map_div, hv, div_self ((Valuation.ne_zero_iff _).2 hx)]

/-- **The residue ratio depends only on the valuation.** For `σ` preserving the
valuation and acting trivially on residues of units, `σ y / y ≡ σ x / x` whenever
`v x = v y`. -/
theorem ratio_cong {σ : L ≃ₐ[K] L} (hv : Preserves w σ)
    (hres : ∀ u : L, w.valuation u = 1 → Cong w (σ u) u)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : w.valuation x = w.valuation y) :
    Cong w (σ y / y) (σ x / x) := by
  set u := y / x with hu
  have hu0 : u ≠ 0 := div_ne_zero hy hx
  have hvu : w.valuation u = 1 := by
    rw [hu, Valuation.map_div, hxy, div_self ((Valuation.ne_zero_iff _).2 hy)]
  have hy' : y = u * x := by rw [hu, div_mul_cancel₀ y hx]
  have hσx : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  have key : σ y / y - σ x / x = (σ x / x) * ((σ u - u) / u) := by
    rw [hy', map_mul]
    field_simp
  unfold Cong
  rw [key, Valuation.map_mul, val_ratio hv hx, one_mul, Valuation.map_div, hvu, div_one]
  exact hres u hvu

/-- `σ^n x / x ≡ (σ x / x)^n`. -/
theorem pow_ratio_cong {σ : L ≃ₐ[K] L} (hv : Preserves w σ)
    (hres : ∀ u : L, w.valuation u = 1 → Cong w (σ u) u) {z : L} (hz : z ≠ 0) (n : ℕ) :
    Cong w ((σ ^ n) z / z) ((σ z / z) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, AlgEquiv.one_apply, div_self hz]
    exact Cong.refl 1
  | succ n ih =>
    have hzn : (σ ^ n) z ≠ 0 := (map_ne_zero (σ ^ n)).mpr hz
    have h1 : (σ ^ (n + 1)) z / z = (σ ((σ ^ n) z) / (σ ^ n) z) * ((σ ^ n) z / z) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
    rw [h1, pow_succ']
    exact Cong.mul (val_ratio hv hzn) (by rw [Valuation.map_pow, val_ratio hv hz, one_pow])
      (ratio_cong hv hres hz hzn (hv.pow n z).symm) ih

/-- From a congruence of ratios to a strict displacement. -/
theorem lt_of_cong_div {a b z : L} (hz : z ≠ 0) (h : Cong w (a / z) (b / z)) :
    w.valuation (a - b) < w.valuation z := by
  unfold Cong at h
  rw [← sub_div, Valuation.map_div] at h
  exact (div_lt_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hz))).1 h

/-- **Frobenius congruence.** Let `σ` preserve the valuation and act trivially on
residues of units, and let `φ` preserve the valuation and induce `u ↦ u ^ q` on
residues of units. Then `σ^q z` and `φ σ φ⁻¹ z` differ by less than `z`. -/
theorem frobenius_congr {σ φ : L ≃ₐ[K] L} (q : ℕ) (hv : Preserves w σ)
    (hres : ∀ u : L, w.valuation u = 1 → Cong w (σ u) u)
    (hφv : Preserves w φ) (hφq : ∀ u : L, w.valuation u = 1 → Cong w (φ u) (u ^ q))
    {z : L} (hz : z ≠ 0) :
    w.valuation ((σ ^ q) z - φ (σ (φ⁻¹ z))) < w.valuation z := by
  set y := φ⁻¹ z with hy
  have hzy : φ y = z := by
    rw [hy, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hy0 : y ≠ 0 := (map_ne_zero φ⁻¹).mpr hz
  have hvy : w.valuation z = w.valuation y := by rw [← hzy, hφv]
  have hfr : φ (σ y) / z = φ (σ y / y) := by rw [map_div₀, hzy]
  have c1 : Cong w ((σ ^ q) z / z) ((σ z / z) ^ q) := pow_ratio_cong hv hres hz q
  have c2 : Cong w (φ (σ y / y)) ((σ y / y) ^ q) := hφq _ (val_ratio hv hy0)
  have c3 : Cong w ((σ y / y) ^ q) ((σ z / z) ^ q) :=
    Cong.pow (val_ratio hv hy0) (val_ratio hv hz) (ratio_cong hv hres hz hy0 hvy) q
  have c4 : Cong w ((σ ^ q) z / z) (φ (σ y) / z) := by
    rw [hfr]
    exact c1.trans (c3.symm.trans c2.symm)
  exact lt_of_cong_div hz c4

/-- **Frobenius congruence, group form**: `(φ σ φ⁻¹)⁻¹ σ^q` is wild. -/
theorem isWild_frobenius {σ φ : L ≃ₐ[K] L} (q : ℕ) (hv : Preserves w σ)
    (hres : ∀ u : L, w.valuation u = 1 → Cong w (σ u) u)
    (hφv : Preserves w φ) (hφq : ∀ u : L, w.valuation u = 1 → Cong w (φ u) (u ^ q)) :
    IsWild w ((φ * σ * φ⁻¹)⁻¹ * σ ^ q) := by
  intro z hz
  set c := φ * σ * φ⁻¹ with hc
  have hcv : Preserves w c⁻¹ := ((hφv.mul hv).mul hφv.inv).inv
  have h1 : (c⁻¹ * σ ^ q) z - z = c⁻¹ ((σ ^ q) z - c z) := by
    rw [AlgEquiv.mul_apply, map_sub, ← AlgEquiv.mul_apply c⁻¹ c, inv_mul_cancel,
      AlgEquiv.one_apply]
  rw [h1, hcv]
  have hcz : c z = φ (σ (φ⁻¹ z)) := by
    rw [hc, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
  rw [hcz]
  exact frobenius_congr q hv hres hφv hφq hz

/-- **Inertia commutes modulo wild elements**: for two automorphisms satisfying the
inertia conditions, `σ τ z` and `τ σ z` differ by less than `z`. -/
theorem commutator_congr {σ τ : L ≃ₐ[K] L} (hσ : Preserves w σ)
    (hσr : ∀ u : L, w.valuation u = 1 → Cong w (σ u) u)
    (hτ : Preserves w τ) (hτr : ∀ u : L, w.valuation u = 1 → Cong w (τ u) u)
    {z : L} (hz : z ≠ 0) :
    w.valuation (σ (τ z) - τ (σ z)) < w.valuation z := by
  have hτz : τ z ≠ 0 := (map_ne_zero τ).mpr hz
  have hσz : σ z ≠ 0 := (map_ne_zero σ).mpr hz
  have e1 : σ (τ z) / z = (σ (τ z) / τ z) * (τ z / z) := by field_simp
  have e2 : τ (σ z) / z = (τ (σ z) / σ z) * (σ z / z) := by field_simp
  have c1 : Cong w (σ (τ z) / z) ((σ z / z) * (τ z / z)) := by
    rw [e1]
    exact Cong.mul (val_ratio hσ hτz) (val_ratio hτ hz)
      (ratio_cong hσ hσr hz hτz (hτ z).symm) (Cong.refl _)
  have c2 : Cong w (τ (σ z) / z) ((τ z / z) * (σ z / z)) := by
    rw [e2]
    exact Cong.mul (val_ratio hτ hσz) (val_ratio hσ hz)
      (ratio_cong hτ hτr hz hσz (hσ z).symm) (Cong.refl _)
  have c3 : Cong w (σ (τ z) / z) (τ (σ z) / z) := by
    refine c1.trans ?_
    rw [mul_comm]
    exact c2.symm
  exact lt_of_cong_div hz c3


/-! ### From the decomposition and inertia subgroups to the inertia conditions -/

open scoped Pointwise

theorem mem_iff_of_mem_decomposition {g : L ≃ₐ[K] L} (hg : g ∈ w.decompositionSubgroup K)
    (y : L) : g y ∈ w ↔ y ∈ w := by
  have h : g • w = w := hg
  have h2 := ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := w) (x := y)
  rw [h] at h2
  exact h2

theorem val_le_iff_of_mem_decomposition {g : L ≃ₐ[K] L} (hg : g ∈ w.decompositionSubgroup K)
    {a b : L} (hb : b ≠ 0) :
    w.valuation (g a) ≤ w.valuation (g b) ↔ w.valuation a ≤ w.valuation b := by
  have hgb : g b ≠ 0 := (map_ne_zero g).mpr hb
  have hpos : 0 < w.valuation b := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hb)
  have hpos' : 0 < w.valuation (g b) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hgb)
  rw [← div_le_one₀ hpos', ← div_le_one₀ hpos, ← Valuation.map_div, ← Valuation.map_div,
    ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, ← map_div₀,
    mem_iff_of_mem_decomposition hg]

/-- Every element has a finite orbit under a `K`-automorphism of an algebraic
extension: its iterates are roots of its minimal polynomial. -/
theorem exists_pow_apply_eq [Algebra.IsAlgebraic K L] (σ : L ≃ₐ[K] L) (x : L) :
    ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x := by
  have hint : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hp : minpoly K x ≠ 0 := minpoly.ne_zero hint
  have hmem : ∀ k : ℕ, (σ ^ k) x ∈ (minpoly K x).rootSet L := by
    intro k
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]
  have hfin : Finite ((minpoly K x).rootSet L) := (Polynomial.rootSet_finite _ _).to_subtype
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨(σ ^ k) x, hmem k⟩ : (minpoly K x).rootSet L))
  have heq' : (σ ^ a) x = (σ ^ b) x := congrArg Subtype.val heq
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨b - a, by omega, ?_⟩
    have e : (σ ^ b) x = (σ ^ a) ((σ ^ (b - a)) x) := by
      rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le]
    rw [e] at heq'
    exact ((σ ^ a).injective heq').symm
  · refine ⟨a - b, by omega, ?_⟩
    have e : (σ ^ a) x = (σ ^ b) ((σ ^ (a - b)) x) := by
      rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le]
    rw [e] at heq'
    exact (σ ^ b).injective heq'

/-- **Decomposition elements preserve the valuation** on an algebraic extension:
if `v(σ x) < v(x)` the iterates would strictly decrease, contradicting the finite
orbit; symmetrically for `>`. -/
theorem preserves_of_mem_decomposition [Algebra.IsAlgebraic K L] {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ w.decompositionSubgroup K) : Preserves w σ := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hσx : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  obtain ⟨N, hN, hfix⟩ := exists_pow_apply_eq σ x
  have hσk : ∀ k : ℕ, σ ^ k ∈ w.decompositionSubgroup K := fun k => Subgroup.pow_mem _ hσ k
  set f : ℕ → w.ValueGroup := fun k => w.valuation ((σ ^ k) x) with hf
  have hshift : ∀ k : ℕ, (σ ^ k) (σ x) = (σ ^ (k + 1)) x := by
    intro k
    rw [← AlgEquiv.mul_apply, ← pow_succ]
  have hstep : ∀ k : ℕ, (f (k + 1) ≤ f k ↔ w.valuation (σ x) ≤ w.valuation x) := by
    intro k
    have h := val_le_iff_of_mem_decomposition (hσk k) (a := σ x) (b := x) hx
    rw [hshift] at h
    exact h
  have hstep' : ∀ k : ℕ, (f k ≤ f (k + 1) ↔ w.valuation x ≤ w.valuation (σ x)) := by
    intro k
    have h := val_le_iff_of_mem_decomposition (hσk k) (a := x) (b := σ x) hσx
    rw [hshift] at h
    exact h
  have hf0 : f 0 = w.valuation x := by simp [hf]
  have hfN : f N = w.valuation x := by simp only [hf, hfix]
  rcases lt_trichotomy (w.valuation (σ x)) (w.valuation x) with hlt | heq | hgt
  · exfalso
    have hanti : StrictAnti f := strictAnti_nat_of_succ_lt fun k =>
      not_le.mp fun h => (not_le.mpr hlt) ((hstep' k).1 h)
    have := hanti hN
    rw [hfN, hf0] at this
    exact lt_irrefl _ this
  · exact heq
  · exfalso
    have hmono : StrictMono f := strictMono_nat_of_lt_succ fun k =>
      not_le.mp fun h => (not_le.mpr hgt) ((hstep k).1 h)
    have := hmono hN
    rw [hfN, hf0] at this
    exact lt_irrefl _ this

/-- Elements of the inertia subgroup act trivially on residues. -/
theorem cong_of_mem_inertia {σ : L ≃ₐ[K] L} (h : σ ∈ w.decompositionSubgroup K)
    (hI : (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) (u : L) (hu : u ∈ w) :
    Cong w (σ u) u := by
  have h1 : MulSemiringAction.toRingAut (w.decompositionSubgroup K)
      (IsLocalRing.ResidueField w) ⟨σ, h⟩ = 1 := hI
  have h2 : (⟨σ, h⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w ⟨u, hu⟩ =
      IsLocalRing.residue w ⟨u, hu⟩ := by
    have := congrArg (fun e => e (IsLocalRing.residue w ⟨u, hu⟩)) h1
    exact this
  rw [← IsLocalRing.ResidueField.residue_smul] at h2
  have h3 : (⟨σ, h⟩ : w.decompositionSubgroup K) • (⟨u, hu⟩ : w) - ⟨u, hu⟩ ∈
      IsLocalRing.maximalIdeal w := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h2, sub_self]
  rw [ValuationSubring.valuation_lt_one_iff] at h3
  exact h3

/-- **The inertia conditions for the inertia subgroup** (in the form used by the
kernel's `IsInertia`) on an algebraic extension. -/
theorem inertia_conditions [Algebra.IsAlgebraic K L] {σ : L ≃ₐ[K] L}
    (hI : ∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) :
    Preserves w σ ∧ ∀ u : L, w.valuation u = 1 → Cong w (σ u) u := by
  obtain ⟨h, hI⟩ := hI
  refine ⟨preserves_of_mem_decomposition h, fun u hu => ?_⟩
  exact cong_of_mem_inertia h hI u ((ValuationSubring.valuation_le_one_iff w u).1 hu.le)

/-- **Frobenius congruence for the inertia subgroup.** On an algebraic extension, if
`σ` is in the inertia subgroup of `w` and `φ` is in its decomposition subgroup and
induces `u ↦ u ^ q` on residues, then `(φ σ φ⁻¹)⁻¹ σ^q` is wild. -/
theorem isWild_frobenius_of_inertia [Algebra.IsAlgebraic K L] {σ φ : L ≃ₐ[K] L} (q : ℕ)
    (hI : ∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K)
    (hφ : φ ∈ w.decompositionSubgroup K) (hφq : ∀ u : L, u ∈ w → Cong w (φ u) (u ^ q)) :
    IsWild w ((φ * σ * φ⁻¹)⁻¹ * σ ^ q) := by
  obtain ⟨hv, hres⟩ := inertia_conditions hI
  exact isWild_frobenius q hv hres (preserves_of_mem_decomposition hφ)
    (fun u hu => hφq u ((ValuationSubring.valuation_le_one_iff w u).1 hu.le))

/-- **Inertia is abelian modulo wild inertia.** On an algebraic extension, for `σ, τ`
in the inertia subgroup of `w`, `(τ σ)⁻¹ (σ τ)` is wild. -/
theorem isWild_commutator_of_inertia [Algebra.IsAlgebraic K L] {σ τ : L ≃ₐ[K] L}
    (hσ : ∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K)
    (hτ : ∃ h : τ ∈ w.decompositionSubgroup K,
      (⟨τ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) :
    IsWild w ((τ * σ)⁻¹ * (σ * τ)) := by
  obtain ⟨hσv, hσr⟩ := inertia_conditions hσ
  obtain ⟨hτv, hτr⟩ := inertia_conditions hτ
  intro z hz
  have hcv : Preserves w (τ * σ)⁻¹ := (hτv.mul hσv).inv
  have h1 : ((τ * σ)⁻¹ * (σ * τ)) z - z = (τ * σ)⁻¹ (σ (τ z) - τ (σ z)) := by
    rw [map_sub]
    have e2 : (τ * σ)⁻¹ (τ (σ z)) = z := by
      change (τ * σ)⁻¹ ((τ * σ) z) = z
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [e2]
    rfl
  rw [h1, hcv]
  exact commutator_congr hσv hσr hτv hτr hz

end WildTameCharacter
