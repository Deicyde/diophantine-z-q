import ZInQKernel.Contrib.OneProof.CMBranch.ReducedPeriod

/-! # cm-branch2: `CoxProperLattice` proved

The textbook leaf `CMBranch.CoxProperLattice` (Cox, *Primes of the form x² + ny²*, Lemma 7.5 with Lemma 7.2; used for
the manuscript's uncited L598-599) is a theorem of Mathlib:

* `CoxCore.discr_pair`, `CoxCore.discr_order`: for an order `R = ℤ + ℤθ ⊆ 𝓞_k` of a quadratic field with
  `θ² + bθ + N = 0`, `b² − 4N = [𝓞_k : R]² · d_k` (trace discriminant of `(1, θ)` computed from the left-multiplication
  matrix; `AddSubgroup.relIndex_eq_abs_det` against Mathlib's integral basis; `NumberField.coe_discr`);
* `mult_iff_dvd` (Cox 7.5, the elementary half): for a primitive `(a, b, c)` with `aτ² + bτ + c = 0`, `Im τ > 0`,
  `m + nτ` multiplies `ℤ + ℤτ` into itself iff `a ∣ n`;
* `coxProperLattice_proof`: a non-integral multiplier gives the quadratic relation of `τ`, normalized to a primitive form;
  the multiplier ring is `ℤ + ℤaτ`; transported through `R ≃+* {α | αΛ ⊆ Λ}` it gives `R = ℤ + ℤθ`, `θ ↦ aτ`, and
  `discr_order` gives `b² − 4ac = Δ_R`.
-/

namespace HDec
namespace CMBranch

namespace CoxCore
open NumberField Module

variable {k : Type} [Field k] [NumberField k]

/-- The trace discriminant of `(1, θ)` for `θ² + bθ + N = 0`, `θ ∉ ℚ`, `[k:ℚ] = 2`. -/
theorem discr_pair (hk : finrank ℚ k = 2) {θ : k} (hnq : θ ∉ Set.range (algebraMap ℚ k)) {b N : ℤ}
    (hθ : θ ^ 2 + b * θ + N = 0) (hli : LinearIndependent ℚ ![(1 : k), θ]) :
    Algebra.discr ℚ ![(1 : k), θ] = (b : ℚ) ^ 2 - 4 * N := by
  classical
  let B : Basis (Fin 2) ℚ k := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hk])
  have hB : ∀ i, B i = ![(1 : k), θ] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hB0 : B 0 = 1 := hB 0
  have hB1 : B 1 = θ := hB 1
  have hθ2 : θ * θ = (-(N : ℚ)) • B 0 + (-(b : ℚ)) • B 1 := by
    rw [hB0, hB1, Algebra.smul_def, Algebra.smul_def]
    simp only [map_neg, map_intCast, mul_one]
    linear_combination hθ
  have htr : ∀ x : k, Algebra.trace ℚ k x = (Algebra.leftMulMatrix B x).trace :=
    fun x => Algebra.trace_eq_matrix_trace B x
  have hrep : ∀ x : k, ∀ i j, Algebra.leftMulMatrix B x i j = B.repr (x * B j) i :=
    fun x i j => Algebra.leftMulMatrix_eq_repr_mul B x i j
  have t1 : Algebra.trace ℚ k 1 = 2 := by
    rw [htr, Matrix.trace_fin_two, hrep, hrep, one_mul, one_mul, B.repr_self, B.repr_self]
    simp; norm_num
  have tθ : Algebra.trace ℚ k θ = -b := by
    rw [htr, Matrix.trace_fin_two, hrep, hrep, hB0, mul_one, ← hB1, B.repr_self, hB1, hθ2]
    simp [Finsupp.single_apply]
  have tθθ : Algebra.trace ℚ k (θ * θ) = b ^ 2 - 2 * N := by
    rw [hθ2, map_add, map_smul, map_smul, hB0, hB1, t1, tθ]
    simp; ring
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_one, one_mul]
  rw [t1, tθ, tθθ]
  ring

/-- `𝓞_k` as the additive closure of an integral basis. -/
theorem ringOfIntegers_eq_closure {ι : Type} [Fintype ι] (e : Free.ChooseBasisIndex ℤ (𝓞 k) ≃ ι) :
    (integralClosure ℤ k).toSubring.toAddSubgroup =
      AddSubgroup.closure (Set.range ((integralBasis k).reindex e)) := by
  rw [Basis.range_reindex]
  apply le_antisymm
  · intro x hx
    let y : 𝓞 k := ⟨x, hx⟩
    have hy := (RingOfIntegers.basis k).sum_repr y
    have hx' : x = ∑ i, ((RingOfIntegers.basis k).repr y i) • integralBasis k i := by
      have := congrArg (algebraMap (𝓞 k) k) hy
      simp only [map_sum, map_zsmul] at this
      simp only [integralBasis_apply]
      rw [this]
      rfl
    rw [hx']
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [integralBasis_apply]
    exact (RingOfIntegers.basis k i).2

/-- **The discriminant of `ℤ[θ]`**: for `R = ℤ + ℤθ ⊆ 𝓞_k`, `θ² + bθ + N = 0`, `[k:ℚ] = 2`,
`b² − 4N = [𝓞_k : R]² · d_k`. -/
theorem discr_order (hk : finrank ℚ k = 2) (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    {θ : k} (hθR : θ ∈ R) (hgen : ∀ r ∈ R, ∃ m n : ℤ, r = m + n * θ)
    (hnq : θ ∉ Set.range (algebraMap ℚ k)) (hli : LinearIndependent ℚ ![(1 : k), θ]) {b N : ℤ}
    (hθ : θ ^ 2 + b * θ + N = 0) :
    b ^ 2 - 4 * N =
      (R.toAddSubgroup.relIndex (integralClosure ℤ k).toSubring.toAddSubgroup : ℤ) ^ 2 * discr k := by
  classical
  let B₁ : Basis (Fin 2) ℚ k := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hk])
  have hB₁ : ⇑B₁ = ![(1 : k), θ] := by
    funext i; simp [B₁, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 k)) = Fintype.card (Fin 2) := by
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, hk, Fintype.card_fin]
  let e := Fintype.equivOfCardEq hcard
  let B₂ : Basis (Fin 2) ℚ k := (integralBasis k).reindex e
  have h₁ : R.toAddSubgroup = AddSubgroup.closure (Set.range B₁) := by
    rw [hB₁]
    apply le_antisymm
    · intro r hr
      obtain ⟨m, n, rfl⟩ := hgen r hr
      refine AddSubgroup.add_mem _ ?_ ?_
      · have : ((m : ℤ) : k) = m • (1 : k) := by simp
        rw [this]; exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (0 : Fin 2))) _
      · have : (n : k) * θ = n • θ := by simp [zsmul_eq_mul]
        rw [this]; exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (1 : Fin 2))) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact R.one_mem
      · exact hθR
  have h₂ := ringOfIntegers_eq_closure (k := k) e
  have hidx := AddSubgroup.relIndex_eq_abs_det R.toAddSubgroup
    (integralClosure ℤ k).toSubring.toAddSubgroup hR B₁ B₂ h₁ h₂
  have hdisc : Algebra.discr ℚ ⇑B₁ = (B₂.det B₁) ^ 2 * Algebra.discr ℚ ⇑B₂ := by
    conv_lhs => rw [← B₂.toMatrix_map_vecMul B₁]
    rw [Algebra.discr_of_matrix_vecMul, Basis.det_apply]
  have hB₂ : Algebra.discr ℚ ⇑B₂ = discr k := by
    rw [coe_discr]
    have := Algebra.discr_reindex ℚ (integralBasis k) e
    rw [← this]
    simp [B₂, Basis.coe_reindex]
  have hp := discr_pair hk hnq hθ hli
  rw [← hB₁] at hp
  have key : ((b ^ 2 - 4 * N : ℤ) : ℚ) =
      ((R.toAddSubgroup.relIndex (integralClosure ℤ k).toSubring.toAddSubgroup : ℤ) ^ 2 * discr k : ℤ) := by
    push_cast
    rw [← hp, hdisc, hB₂, ← sq_abs (B₂.det B₁), ← hidx]
  exact_mod_cast key


end CoxCore

open NumberField Module

/-- `a ∣ nb`, `a ∣ nc` and `gcd(a, b, c) = 1` give `a ∣ n`. -/
theorem dvd_of_dvd_mul_prim {a b c n : ℤ} (hprim : Int.gcd (Int.gcd a b) c = 1) (hb : a ∣ n * b)
    (hc : a ∣ n * c) : a ∣ n := by
  have e1 := Int.gcd_eq_gcd_ab ((Int.gcd a b : ℕ) : ℤ) c
  have e2 := Int.gcd_eq_gcd_ab a b
  rw [hprim] at e1
  generalize Int.gcdA ((Int.gcd a b : ℕ) : ℤ) c = A at e1
  generalize Int.gcdB ((Int.gcd a b : ℕ) : ℤ) c = B at e1
  rw [e2] at e1
  have hn : n = n * a * (Int.gcdA a b * A) + n * b * (Int.gcdB a b * A) + n * c * B := by
    have : (n : ℤ) = n * ((1 : ℕ) : ℤ) := by simp
    conv_lhs => rw [this, e1]
    ring
  rw [hn]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_mul_left a n) _) (dvd_mul_of_dvd_left hb _))
    (dvd_mul_of_dvd_left hc _)

/-- **Cox, Lemma 7.5 (elementary half).** For `Im τ ≠ 0` and a primitive `(a, b, c)` with `aτ² + bτ + c = 0`, `a ≠ 0`:
`(m + nτ)τ ∈ ℤ + ℤτ` iff `a ∣ n`. -/
theorem mult_iff_dvd {τ : ℂ} (hτ : τ.im ≠ 0) {a b c : ℤ} (ha : a ≠ 0)
    (hprim : Int.gcd (Int.gcd a b) c = 1) (hq : (a : ℂ) * τ ^ 2 + b * τ + c = 0) (m n : ℤ) :
    (∃ p q : ℤ, ((m : ℂ) + n * τ) * τ = p + q * τ) ↔ a ∣ n := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  constructor
  · rintro ⟨p, q, h⟩
    -- a(m + nτ)τ = amτ + n(-bτ - c) = -nc + (am - nb)τ
    have h' : ((-(n * c) : ℤ) : ℂ) + ((m * a - n * b : ℤ) : ℂ) * τ = ((p * a : ℤ) : ℂ) + ((q * a : ℤ) : ℂ) * τ := by
      push_cast
      linear_combination (a : ℂ) * h - n * hq
    have hre := congrArg Complex.re h'
    have him := congrArg Complex.im h'
    simp only [Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.mul_im, zero_mul, sub_zero, add_zero, zero_add] at hre him
    have e2 : ((m * a - n * b : ℤ) : ℝ) = ((q * a : ℤ) : ℝ) := by
      have := mul_right_cancel₀ hτ him
      exact this
    have e1 : ((-(n * c) : ℤ) : ℝ) = ((p * a : ℤ) : ℝ) := by
      have e2' : ((m * a - n * b : ℤ) : ℝ) * τ.re = ((q * a : ℤ) : ℝ) * τ.re := by rw [e2]
      linarith
    have e1' : -(n * c) = p * a := by exact_mod_cast e1
    have e2'' : m * a - n * b = q * a := by exact_mod_cast e2
    refine dvd_of_dvd_mul_prim hprim ⟨m - q, by linarith⟩ ⟨-p, by linarith⟩
  · rintro ⟨t, rfl⟩
    refine ⟨-(t * c), m - t * b, ?_⟩
    push_cast
    linear_combination (t : ℂ) * hq

/-- A quadratic relation with nonzero leading coefficient normalizes to a primitive one with `a > 0`. -/
theorem exists_prim {τ : ℂ} {q0 B C : ℤ} (hq0 : q0 ≠ 0) (h : (q0 : ℂ) * τ ^ 2 + B * τ + C = 0) :
    ∃ a b c : ℤ, 0 < a ∧ Int.gcd (Int.gcd a b) c = 1 ∧ (a : ℂ) * τ ^ 2 + b * τ + c = 0 := by
  set g : ℕ := Int.gcd (Int.gcd q0 B) C with hg
  have hg0 : g ≠ 0 := by
    intro h0
    rw [hg, Int.gcd_eq_zero_iff] at h0
    exact hq0 (Int.gcd_eq_zero_iff.mp (by exact_mod_cast h0.1)).1
  have dq : (g : ℤ) ∣ q0 := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  have dB : (g : ℤ) ∣ B := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  have dC : (g : ℤ) ∣ C := Int.gcd_dvd_right _ _
  obtain ⟨a1, ha1⟩ := dq
  obtain ⟨b1, hb1⟩ := dB
  obtain ⟨c1, hc1⟩ := dC
  have hprim1 : Int.gcd (Int.gcd a1 b1) c1 = 1 := by
    have : g = g * Int.gcd (Int.gcd a1 b1) c1 := by
      conv_lhs => rw [hg, ha1, hb1, hc1, Int.gcd_mul_left, Int.natAbs_natCast, Nat.cast_mul, Int.gcd_mul_left]
      simp [Int.natAbs_mul]
    have hg' : 0 < g := Nat.pos_of_ne_zero hg0
    nlinarith [Nat.le_of_eq this]
  have heq1 : (a1 : ℂ) * τ ^ 2 + b1 * τ + c1 = 0 := by
    have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg0
    rw [ha1, hb1, hc1] at h
    push_cast at h
    have : (g : ℂ) * ((a1 : ℂ) * τ ^ 2 + b1 * τ + c1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hgC
    · exact h'
  have ha10 : a1 ≠ 0 := by rintro rfl; simp at ha1; exact hq0 ha1
  rcases lt_or_gt_of_ne ha10 with hneg | hpos
  · refine ⟨-a1, -b1, -c1, by linarith, ?_, ?_⟩
    · simpa [Int.gcd_neg] using hprim1
    · push_cast; linear_combination -heq1
  · exact ⟨a1, b1, c1, hpos, hprim1, heq1⟩

/-- The discriminant of a quadratic form with a non-real root is negative. -/
theorem disc_neg_of_root {τ : ℂ} (hτ : τ.im ≠ 0) {a b c : ℤ} (ha : a ≠ 0)
    (hq : (a : ℂ) * τ ^ 2 + b * τ + c = 0) : b ^ 2 - 4 * a * c < 0 := by
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, pow_two,
    Complex.mul_im, Complex.add_im, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero,
    add_zero, zero_add] at hre him
  set x := τ.re
  set y := τ.im
  have hx : 2 * (a : ℝ) * x + b = 0 := by
    have : y * (2 * (a : ℝ) * x + b) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hτ
    · exact h0
  have hy : 4 * (a : ℝ) ^ 2 * y ^ 2 = -((b : ℝ) ^ 2 - 4 * a * c) := by
    have hx' : (b : ℝ) = -(2 * a * x) := by linarith
    rw [hx'] at hre ⊢
    linear_combination (-4 * (a : ℝ)) * hre
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have : 0 < 4 * (a : ℝ) ^ 2 * y ^ 2 := by positivity
  have : ((b ^ 2 - 4 * a * c : ℤ) : ℝ) < 0 := by push_cast; linarith
  exact_mod_cast this

/-- **`CoxProperLattice`, proved.** -/
theorem coxProperLattice_proof : CoxProperLattice := by
  intro k _ _ R hR Λ c τ hc hτ hmem hiso
  obtain ⟨e⟩ := hiso
  obtain ⟨-, hk, hRO, hf⟩ := hR
  have hτ0 : τ.im ≠ 0 := hτ.ne'
  -- (A) the multipliers of `Λ = c(ℤ + ℤτ)`
  have memΛ : ∀ m n : ℤ, (fun _ => c * (m + n * τ) : Fin 1 → ℂ) ∈ Λ := fun m n => (hmem _).2 ⟨m, n, rfl⟩
  have memM : ∀ α : ℂ, α ∈ latticeMultipliers Λ ↔
      (∃ p q : ℤ, α = p + q * τ) ∧ (∃ p q : ℤ, α * τ = p + q * τ) := by
    intro α
    constructor
    · intro h
      obtain ⟨p, q, hpq⟩ := (hmem _).1 (h _ (memΛ 1 0))
      obtain ⟨p', q', hpq'⟩ := (hmem _).1 (h _ (memΛ 0 1))
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_one, Int.cast_zero, zero_mul, add_zero,
        mul_one, zero_add, one_mul] at hpq hpq'
      refine ⟨⟨p, q, mul_left_cancel₀ hc ?_⟩, ⟨p', q', mul_left_cancel₀ hc ?_⟩⟩
      · rw [← hpq]; ring
      · rw [← hpq']; ring
    · rintro ⟨⟨p, q, hpq⟩, ⟨p', q', hpq'⟩⟩ z hz
      obtain ⟨m, n, hz0⟩ := (hmem z).1 hz
      refine (hmem _).2 ⟨m * p + n * p', m * q + n * q', ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, hz0]
      push_cast
      linear_combination (c * m) * hpq + (c * n) * hpq'
  -- the integers of `M`
  have eint : ∀ n : ℤ, ((e (n : R) : latticeMultipliers Λ) : ℂ) = n := fun n => by simp
  -- (B) an element of `R` not in `ℚ`
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 k)) = Fintype.card (Fin 2) := by
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, hk, Fintype.card_fin]
  let B₂ : Basis (Fin 2) ℚ k := (integralBasis k).reindex (Fintype.equivOfCardEq hcard)
  have hB₂O : ∀ i, B₂ i ∈ integralClosure ℤ k := fun i => by
    simp only [B₂, Basis.reindex_apply, integralBasis_apply]
    exact (RingOfIntegers.basis k _).2
  obtain ⟨y, hyO, hyq⟩ : ∃ y : k, y ∈ integralClosure ℤ k ∧ y ∉ Set.range (algebraMap ℚ k) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨q0, hq0⟩ := hcon (B₂ 0) (hB₂O 0)
    obtain ⟨q1, hq1⟩ := hcon (B₂ 1) (hB₂O 1)
    have hli := Fintype.linearIndependent_iff.mp B₂.linearIndependent ![q1, -q0]
      (by rw [Fin.sum_univ_two, ← hq0, ← hq1]; simp [Algebra.smul_def]; ring)
    have h1 : q1 = 0 := by simpa using hli 0
    exact B₂.ne_zero 1 (by rw [← hq1, h1, map_zero])
  set f := LeafQM.AV.conductor R with hfdef
  have hr0 : f • y ∈ R := AddSubgroup.nsmul_relIndex_mem R.toAddSubgroup (K := (integralClosure ℤ k).toSubring.toAddSubgroup) hyO
  have hr0q : f • y ∉ Set.range (algebraMap ℚ k) := by
    rintro ⟨q, hq⟩
    apply hyq
    refine ⟨q / f, ?_⟩
    have hf' : (f : k) ≠ 0 := by exact_mod_cast hf
    rw [map_div₀, hq, map_natCast, nsmul_eq_mul]
    field_simp
  -- (C) its image in `M` and the quadratic relation of `τ`
  set α : ℂ := (e ⟨f • y, hr0⟩ : ℂ) with hα
  obtain ⟨⟨p0, q0, h0⟩, ⟨p1, q1, h1⟩⟩ := (memM α).1 (e ⟨f • y, hr0⟩).2
  have hq0 : q0 ≠ 0 := by
    rintro rfl
    apply hr0q
    refine ⟨p0, ?_⟩
    have : e ⟨f • y, hr0⟩ = e (p0 : R) := by
      apply Subtype.ext; rw [eint, ← hα, h0]; simp
    have := congrArg Subtype.val (e.injective this)
    simp only [SubringClass.coe_intCast] at this
    rw [this]; simp
  have hquad : (q0 : ℂ) * τ ^ 2 + ((p0 - q1 : ℤ) : ℂ) * τ + ((-p1 : ℤ) : ℂ) = 0 := by
    rw [h0] at h1; push_cast; linear_combination h1
  obtain ⟨a, b, c', ha, hprim, hq⟩ := exists_prim hq0 hquad
  have ha0 : a ≠ 0 := ha.ne'
  -- (D) `θ ↦ aτ`
  have hmemθ : (a : ℂ) * τ ∈ latticeMultipliers Λ :=
    (memM _).2 ⟨⟨0, a, by simp⟩, ⟨-c', -b, by push_cast; linear_combination hq⟩⟩
  set θR : R := e.symm ⟨(a : ℂ) * τ, hmemθ⟩ with hθRdef
  have eθ : ((e θR : latticeMultipliers Λ) : ℂ) = (a : ℂ) * τ := by simp [hθRdef]
  have hgen : ∀ r ∈ R, ∃ m n : ℤ, r = m + n * (θR : k) := by
    intro r hr
    obtain ⟨⟨m, n, hw⟩, ⟨p, q, hwτ⟩⟩ := (memM _).1 (e ⟨r, hr⟩).2
    obtain ⟨t, rfl⟩ := (mult_iff_dvd hτ0 ha0 hprim hq m n).1 ⟨p, q, hw ▸ hwτ⟩
    refine ⟨m, t, ?_⟩
    have : e ⟨r, hr⟩ = e ((m : R) + (t : R) * θR) := by
      apply Subtype.ext
      rw [hw, map_add, map_mul, Subring.coe_add, Subring.coe_mul, eint, eint, eθ]
      push_cast; ring
    have := congrArg Subtype.val (e.injective this)
    simpa using this
  have hrel : (θR : k) ^ 2 + b * (θR : k) + ((a * c' : ℤ) : k) = 0 := by
    have h1 : e (θR ^ 2 + (b : R) * θR + ((a * c' : ℤ) : R)) = 0 := by
      apply Subtype.ext
      rw [map_add, map_add, map_pow, map_mul, Subring.coe_add, Subring.coe_add, Subring.coe_mul,
        SubmonoidClass.coe_pow, eint, eint, eθ]
      push_cast
      linear_combination (a : ℂ) * hq
    rw [map_eq_zero_iff _ e.injective] at h1
    have := congrArg Subtype.val h1
    simpa using this
  have hnq : (θR : k) ∉ Set.range (algebraMap ℚ k) := by
    rintro ⟨q, hq'⟩
    have hd := disc_neg_of_root hτ0 ha0 hq
    have : (q : ℚ) ^ 2 + b * q + ((a * c' : ℤ) : ℚ) = 0 := by
      apply (algebraMap ℚ k).injective
      rw [map_zero, ← hrel, ← hq']; simp
    have h2 : (2 * q + b) ^ 2 = ((b ^ 2 - 4 * a * c' : ℤ) : ℚ) := by
      push_cast at this ⊢; linear_combination 4 * this
    have : ((b ^ 2 - 4 * a * c' : ℤ) : ℚ) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * q + b)]
  have hli : LinearIndependent ℚ ![(1 : k), (θR : k)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht; simp at hst; exact ⟨hst, rfl⟩
    · exfalso; apply hnq
      refine ⟨-s / t, ?_⟩
      rw [map_div₀, map_neg]
      have : (θR : k) = -(algebraMap ℚ k s) / algebraMap ℚ k t := by
        have ht' : algebraMap ℚ k t ≠ 0 := by simpa using ht
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        field_simp; linear_combination hst
      exact this.symm
  -- (E) the discriminant
  have hD := CoxCore.discr_order hk R hRO θR.2 hgen hnq hli (b := b) (N := a * c') (by simpa using hrel)
  refine ⟨a, b, c', ha, hprim, hq, ?_⟩
  rw [orderDisc]
  have : b ^ 2 - 4 * a * c' = b ^ 2 - 4 * (a * c') := by ring
  rw [this, hD]
  rfl

end CMBranch
end HDec
