import ZInQKernel.Contrib.OneProof.CMBranch.PeriodLattice

/-! # cox-lattice: the textbook leaf `CMBranch.CoxProperLattice`, proved

`HDec.CMBranch.CoxProperLattice` (`CMBranch/ReducedPeriod.lean`, cm-branch2's leaf for the manuscript's uncited step
"For a reduced CM period `τ = x + iy` we have `√3/2 ≤ y ≤ √|Δ|/2`", diophantine_zq.tex L598-599) is proved here from
Mathlib alone (`CoxLattice.coxProperLattice_proof`; cm-branch2 later proved it independently as
`CMBranch.coxProperLattice_proof` in `CMBranch/CoxProof.lean`, so this file keeps its theorem in the sub-namespace
`CoxLattice` to avoid a duplicate name), so `ReducedCMPeriod` follows from the chain's textbook fields `t35`,
`homLatticeCorr`, `t11b` only (`reducedCMPeriod_of_leaves_cox`). The statement is unchanged.

Proof (Cox, *Primes of the form x² + ny²*, the argument of Lemma 7.5 and the discriminant of Lemma 7.2; locators
UNVERIFIED, the steps are on-the-spot, see docs/research/cox-lattice.md):

1. `exists_nonint`: an order `R` of finite index `f` in `𝓞_k` contains `f·ω ∉ ℤ` (`ω ∈ 𝓞_k \ ℚ`).
2. Its image `α` under `φ : R ≃+* {multipliers of Λ}` is a multiplier `∉ ℤ`; `α = p + qτ` with `q ≠ 0` and
   `ατ ∈ ℤ + ℤτ` give an integral quadratic for `τ`, made primitive with `a > 0` (`exists_prim_form`).
3. `mem_mult_iff_order` (Cox 7.5, the elementary half): the multipliers of `c(ℤ + ℤτ)` are `ℤ + ℤ·aτ`.
4. `θ := φ⁻¹(aτ)` generates `R = ℤ + ℤθ`, `θ² + bθ + ac' = 0`, `θ ∉ ℚ` (negative discriminant, `disc_neg`).
5. `discr_order` (cm-branch2's `CoxCore`, scratch/cm-branch2/CoxCore.lean, copied): `b² − 4ac' = [𝓞_k : R]² d_k`,
   via `AddSubgroup.relIndex_eq_abs_det` and `Algebra.discr_of_matrix_vecMul`. This is `orderDisc R`.

The ring isomorphism is only used to pull the generator `aτ` back into `R`; no invariance of discriminants under ring
isomorphisms is needed.
-/

namespace HDec
namespace CMBranch
namespace CoxLattice

open NumberField Module


open NumberField Module

section Disc
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


end Disc

/-! ## The lattice `ℤ + ℤτ` and its multipliers (Cox, Lemma 7.5, elementary half) -/

/-- Multipliers of `c(ℤ + ℤτ)` are the multipliers of `ℤ + ℤτ`. -/
theorem mem_mult_iff {Λ : Submodule ℤ (Fin 1 → ℂ)} {c τ : ℂ} (hc : c ≠ 0)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = c * (m + n * τ)) (α : ℂ) :
    α ∈ latticeMultipliers Λ ↔ ∀ m n : ℤ, ∃ p q : ℤ, α * (m + n * τ) = p + q * τ := by
  show (∀ z ∈ Λ, α • z ∈ Λ) ↔ _
  constructor
  · intro h m n
    have hz : (fun _ : Fin 1 => c * (m + n * τ)) ∈ Λ := (hΛ _).2 ⟨m, n, rfl⟩
    obtain ⟨p, q, hpq⟩ := (hΛ _).1 (h _ hz)
    refine ⟨p, q, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul] at hpq
    apply mul_left_cancel₀ hc
    linear_combination hpq
  · intro h z hz
    obtain ⟨m, n, hmn⟩ := (hΛ z).1 hz
    obtain ⟨p, q, hpq⟩ := h m n
    refine (hΛ _).2 ⟨p, q, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hmn, ← hpq]; ring

/-- `X τ = Y` with `X, Y ∈ ℤ` and `Im τ > 0` forces `X = Y = 0`. -/
theorem int_coeff_zero {τ : ℂ} (hτ : 0 < τ.im) {X Y : ℤ} (h : (X : ℂ) * τ = Y) : X = 0 ∧ Y = 0 := by
  have him := congrArg Complex.im h
  simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero] at him
  have hX : X = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hτ.ne'
  subst hX
  refine ⟨rfl, ?_⟩
  simp only [Int.cast_zero, zero_mul] at h
  exact_mod_cast h.symm

/-- `a ∣ nb`, `a ∣ nc` and `gcd(a, b, c) = 1` give `a ∣ n`. -/
theorem dvd_of_prim {a b c n : ℤ} (hprim : Int.gcd (Int.gcd a b) c = 1) (hb : a ∣ n * b)
    (hc : a ∣ n * c) : a ∣ n := by
  have h1 : a ∣ n * (Int.gcd a b : ℤ) := by
    rw [Int.gcd_eq_gcd_ab a b]
    have : n * (a * Int.gcdA a b + b * Int.gcdB a b) =
        a * (n * Int.gcdA a b) + (n * b) * Int.gcdB a b := by ring
    rw [this]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hb _)
  have h2 : a ∣ n * (Int.gcd (Int.gcd a b) c : ℤ) := by
    rw [Int.gcd_eq_gcd_ab (Int.gcd a b : ℤ) c]
    have : n * ((Int.gcd a b : ℤ) * Int.gcdA (Int.gcd a b : ℤ) c + c * Int.gcdB (Int.gcd a b : ℤ) c) =
        (n * (Int.gcd a b : ℤ)) * Int.gcdA (Int.gcd a b : ℤ) c + (n * c) * Int.gcdB (Int.gcd a b : ℤ) c := by
      ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left hc _)
  simpa [hprim] using h2

/-- **Cox, Lemma 7.5 (the computation in its proof).** For `aτ² + bτ + c = 0`, `(a, b, c)` primitive,
`a > 0`, `Im τ > 0`: if `(m + nτ)τ ∈ ℤ + ℤτ` then `a ∣ n`. -/
theorem dvd_of_mul_tau {τ : ℂ} (hτ : 0 < τ.im) {a b c : ℤ}
    (hprim : Int.gcd (Int.gcd a b) c = 1) (hq : (a : ℂ) * τ ^ 2 + b * τ + c = 0) {m n p q : ℤ}
    (h : ((m : ℂ) + n * τ) * τ = p + q * τ) : a ∣ n := by
  have h' : ((a * m - n * b - a * q : ℤ) : ℂ) * τ = ((a * p + n * c : ℤ) : ℂ) := by
    push_cast
    linear_combination (a : ℂ) * h - (n : ℂ) * hq
  obtain ⟨h1, h2⟩ := int_coeff_zero hτ h'
  refine dvd_of_prim hprim ⟨m - q, by linarith⟩ ⟨-p, by linarith⟩

/-- **Cox, Lemma 7.5 (elementary half), lattice form.** The multipliers of `c(ℤ + ℤτ)` are `ℤ + ℤ·aτ`. -/
theorem mem_mult_iff_order {Λ : Submodule ℤ (Fin 1 → ℂ)} {c τ : ℂ} (hc : c ≠ 0) (hτ : 0 < τ.im)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = c * (m + n * τ)) {a b c' : ℤ}
    (hprim : Int.gcd (Int.gcd a b) c' = 1) (hq : (a : ℂ) * τ ^ 2 + b * τ + c' = 0) (β : ℂ) :
    β ∈ latticeMultipliers Λ ↔ ∃ m n : ℤ, β = m + n * (a * τ) := by
  rw [mem_mult_iff hc hΛ]
  constructor
  · intro h
    obtain ⟨p, q, hpq⟩ := h 1 0
    obtain ⟨p', q', hpq'⟩ := h 0 1
    have e1 : β = p + q * τ := by simpa using hpq
    have e2 : ((p : ℂ) + q * τ) * τ = p' + q' * τ := by rw [← e1]; simpa using hpq'
    obtain ⟨n, rfl⟩ := dvd_of_mul_tau hτ hprim hq e2
    exact ⟨p, n, by rw [e1]; push_cast; ring⟩
  · rintro ⟨m, n, rfl⟩ m' n'
    refine ⟨m * m' - n * n' * c', m * n' + n * a * m' - n * n' * b, ?_⟩
    push_cast
    linear_combination ((n : ℂ) * n') * hq

/-- A root `τ ∉ ℝ` of an integral quadratic is a root of a primitive form with `a > 0`. -/
theorem exists_prim_form {τ : ℂ} {A B C : ℤ} (hA : A ≠ 0)
    (h : (A : ℂ) * τ ^ 2 + B * τ + C = 0) :
    ∃ a b c : ℤ, 0 < a ∧ Int.gcd (Int.gcd a b) c = 1 ∧ (a : ℂ) * τ ^ 2 + b * τ + c = 0 := by
  set g : ℕ := Int.gcd (Int.gcd A B) C with hgdef
  have hg : g ≠ 0 := by
    intro h0
    rw [hgdef, Int.gcd_eq_zero_iff] at h0
    have := h0.1
    simp only [Nat.cast_eq_zero, Int.gcd_eq_zero_iff] at this
    exact hA this.1
  obtain ⟨a1, ha1⟩ : (g : ℤ) ∣ A := (Int.gcd_dvd_left _ _).trans (by exact_mod_cast Int.gcd_dvd_left _ _)
  obtain ⟨b1, hb1⟩ : (g : ℤ) ∣ B := (Int.gcd_dvd_left _ _).trans (by exact_mod_cast Int.gcd_dvd_right _ _)
  obtain ⟨c1, hc1⟩ : (g : ℤ) ∣ C := Int.gcd_dvd_right _ _
  have hprim : Int.gcd (Int.gcd a1 b1) c1 = 1 := by
    have e : g = g * Int.gcd (Int.gcd a1 b1) c1 := by
      conv_lhs => rw [hgdef, ha1, hb1, hc1, Int.gcd_mul_left, Int.natAbs_natCast, Nat.cast_mul,
        Int.gcd_mul_left, Int.natAbs_natCast]
    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg) (e.symm.trans (mul_one g).symm)
    exact this
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  have h1 : (a1 : ℂ) * τ ^ 2 + b1 * τ + c1 = 0 := by
    have : (g : ℂ) * ((a1 : ℂ) * τ ^ 2 + b1 * τ + c1) = 0 := by
      rw [← h, ha1, hb1, hc1]; push_cast; ring
    exact (mul_eq_zero.mp this).resolve_left hg'
  have ha1' : a1 ≠ 0 := by rintro rfl; simp at ha1; exact hA ha1
  rcases lt_or_gt_of_ne ha1' with hneg | hpos
  · refine ⟨-a1, -b1, -c1, by omega, by simpa using hprim, ?_⟩
    push_cast; linear_combination -h1
  · exact ⟨a1, b1, c1, hpos, hprim, h1⟩

/-- The discriminant of a form with a non-real root is negative. -/
theorem disc_neg {τ : ℂ} (hτ : 0 < τ.im) {a b c : ℤ} (ha : a ≠ 0)
    (h : (a : ℂ) * τ ^ 2 + b * τ + c = 0) : b ^ 2 - 4 * a * c < 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, pow_two,
    Complex.mul_im, Complex.add_im, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero,
    add_zero, zero_add] at hre him
  have hx : 2 * (a : ℝ) * τ.re + b = 0 := by
    have : τ.im * (2 * (a : ℝ) * τ.re + b) = 0 := by linear_combination him
    exact (mul_eq_zero.mp this).resolve_left hτ.ne'
  have key : ((b ^ 2 - 4 * a * c : ℤ) : ℝ) = -(4 * (a : ℝ) ^ 2 * τ.im ^ 2) := by
    push_cast
    linear_combination (-4 * (a : ℝ)) * hre + (2 * (a : ℝ) * τ.re + b) * hx
  have ha' : (0 : ℝ) < (a : ℝ) ^ 2 := by positivity
  have : ((b ^ 2 - 4 * a * c : ℤ) : ℝ) < 0 := by rw [key]; nlinarith [mul_pos ha' (pow_pos hτ 2)]
  exact_mod_cast this

/-! ## An order contains a non-integer -/

section Order
variable {k : Type} [Field k] [NumberField k]

theorem exists_nonint (hk : finrank ℚ k = 2) (R : Subring k) (hcond : LeafQM.AV.conductor R ≠ 0) :
    ∃ θ ∈ R, θ ∉ Set.range (Int.cast : ℤ → k) := by
  -- a non-rational element of `k`
  obtain ⟨x, hx⟩ : ∃ x : k, x ∉ Set.range (algebraMap ℚ k) := by
    by_contra hcon
    push Not at hcon
    have htop : (⊥ : Subalgebra ℚ k) = ⊤ := by
      ext x; simp only [Algebra.mem_top, iff_true, Algebra.mem_bot]; exact hcon x
    have := (Subalgebra.bot_eq_top_iff_finrank_eq_one).mp htop
    omega
  -- an integral multiple
  have hxa : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ k).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyi⟩ := hxa.exists_integral_multiple
  set ω : k := y • x
  have hωO : ω ∈ (integralClosure ℤ k).toSubring.toAddSubgroup := hyi
  have hωq : ω ∉ Set.range (algebraMap ℚ k) := by
    rintro ⟨q, hq⟩
    apply hx
    refine ⟨q / y, ?_⟩
    have hy' : (y : k) ≠ 0 := by exact_mod_cast hy0
    rw [map_div₀, hq, map_intCast]
    simp only [ω, zsmul_eq_mul]
    field_simp
  set f := LeafQM.AV.conductor R
  have hfR : f • ω ∈ R.toAddSubgroup := AddSubgroup.nsmul_relIndex_mem R.toAddSubgroup hωO
  refine ⟨f • ω, hfR, ?_⟩
  rintro ⟨n, hn⟩
  apply hωq
  refine ⟨n / f, ?_⟩
  have hf' : (f : k) ≠ 0 := by exact_mod_cast hcond
  rw [map_div₀, map_intCast, map_natCast, hn, nsmul_eq_mul]
  field_simp

end Order

/-! ## The leaf -/

/-- **`CoxProperLattice`, proved.** -/
theorem coxProperLattice_proof : CoxProperLattice := by
  intro k _ _ R hR Λ c τ hc hτ hΛ ⟨φ⟩
  obtain ⟨_, hk, hRO, hcond⟩ := hR
  -- 1. a multiplier `α ∉ ℤ` (the image of a non-integer of `R`)
  obtain ⟨θ0, hθ0R, hθ0⟩ := exists_nonint hk R hcond
  set α : ℂ := (φ ⟨θ0, hθ0R⟩ : ℂ) with hα
  have hαm : α ∈ latticeMultipliers Λ := (φ ⟨θ0, hθ0R⟩).2
  have hαnz : α ∉ Set.range (Int.cast : ℤ → ℂ) := by
    rintro ⟨n, hn⟩
    apply hθ0
    refine ⟨n, ?_⟩
    have h1 : φ ⟨θ0, hθ0R⟩ = (n : latticeMultipliers Λ) := Subtype.ext (by simp [← hα, hn])
    have h2 : (⟨θ0, hθ0R⟩ : R) = (n : R) := by
      apply φ.injective; rw [h1, map_intCast]
    have := congrArg Subtype.val h2
    simpa using this.symm
  -- 2. `τ` is a root of an integral quadratic with nonzero leading coefficient
  rw [mem_mult_iff hc hΛ] at hαm
  obtain ⟨p, q, hpq⟩ := hαm 1 0
  obtain ⟨p', q', hpq'⟩ := hαm 0 1
  have e1 : α = p + q * τ := by simpa using hpq
  have e2 : α * τ = p' + q' * τ := by simpa using hpq'
  have hq0 : q ≠ 0 := by
    rintro rfl; exact hαnz ⟨p, by simp [e1]⟩
  have hquad : (q : ℂ) * τ ^ 2 + ((p - q' : ℤ) : ℂ) * τ + ((-p' : ℤ) : ℂ) = 0 := by
    push_cast; linear_combination e2 - τ * e1
  -- 3. the primitive form, and the multiplier ring `ℤ + ℤ·aτ` (Cox 7.5)
  obtain ⟨a, b, c', ha, hprim, hform⟩ := exists_prim_form hq0 hquad
  have hmult := mem_mult_iff_order hc hτ hΛ hprim hform
  have haτ : (a : ℂ) * τ ∈ latticeMultipliers Λ := (hmult _).2 ⟨0, 1, by simp⟩
  -- 4. transport to `R`: `R = ℤ[θ]`, `θ² + bθ + ac' = 0`
  set θ : R := φ.symm ⟨a * τ, haτ⟩ with hθdef
  have hφθ : φ θ = ⟨a * τ, haτ⟩ := φ.apply_symm_apply _
  have hθeq : θ ^ 2 + (b : R) * θ + ((a * c' : ℤ) : R) = 0 := by
    apply φ.injective
    rw [map_zero, map_add, map_add, map_pow, map_mul, map_intCast, map_intCast, hφθ]
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_pow, Subring.coe_mul, Subring.coe_intCast,
      Subring.coe_zero]
    push_cast
    linear_combination (a : ℂ) * hform
  have hgen : ∀ r ∈ R, ∃ m n : ℤ, r = m + n * (θ : k) := by
    intro r hr
    obtain ⟨m, n, hmn⟩ := (hmult _).1 (φ ⟨r, hr⟩).2
    refine ⟨m, n, ?_⟩
    have h1 : (⟨r, hr⟩ : R) = (m : R) + (n : R) * θ := by
      apply φ.injective
      rw [map_add, map_mul, map_intCast, map_intCast, hφθ]
      apply Subtype.ext
      simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast]
      exact hmn
    have := congrArg Subtype.val h1
    simpa using this
  have hθk : (θ : k) ^ 2 + (b : k) * θ + ((a * c' : ℤ) : k) = 0 := by
    have := congrArg Subtype.val hθeq
    simpa using this
  have hD : b ^ 2 - 4 * (a * c') < 0 := by
    have := disc_neg hτ ha.ne' hform; linarith
  have hnq : (θ : k) ∉ Set.range (algebraMap ℚ k) := by
    rintro ⟨r, hr⟩
    have hr' : algebraMap ℚ k (r ^ 2 + b * r + (a * c' : ℤ)) = 0 := by
      rw [← hθk, ← hr]; simp
    have hr0 : r ^ 2 + b * r + ((a * c' : ℤ) : ℚ) = 0 :=
      (map_eq_zero_iff _ (algebraMap ℚ k).injective).mp hr'
    have hD' : ((b ^ 2 - 4 * (a * c') : ℤ) : ℚ) < 0 := by exact_mod_cast hD
    push_cast at hD' hr0
    nlinarith [sq_nonneg (2 * r + b)]
  have hli : LinearIndependent ℚ ![(1 : k), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hnq
      refine ⟨-s / t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have ht' : algebraMap ℚ k t ≠ 0 := by simpa using ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hst
  -- 5. the discriminant (Cox Lemma 7.2 / (7.3) bookkeeping)
  have hdisc := discr_order hk R hRO θ.2 hgen hnq hli hθk
  refine ⟨a, b, c', ha, hprim, hform, ?_⟩
  show _ = (LeafQM.AV.conductor R : ℤ) ^ 2 * NumberField.discr k
  unfold LeafQM.AV.conductor
  rw [← hdisc]
  ring

end CoxLattice

/-- **`ReducedCMPeriod` without `CoxProperLattice`** (manuscript L598-599): from the chain's textbook fields
`t35`, `homLatticeCorr`, `t11b` only. -/
theorem reducedCMPeriod_of_leaves_cox (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hcorr : HomUnify.HomLatticeCorr) (h11b : ZInQ.LeafPush2.T11b_Rigidity) : ReducedCMPeriod :=
  reducedCMPeriod_of_leaves hT35 hcorr h11b CoxLattice.coxProperLattice_proof

end CMBranch
end HDec
