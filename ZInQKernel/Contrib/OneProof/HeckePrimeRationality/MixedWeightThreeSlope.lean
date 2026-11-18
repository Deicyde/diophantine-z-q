import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RepeatedPrimeMixedTraceBinder

/-!
# Arbitrary-slope mixed weight-three correlations

For positive `n, m` with `m ≥ 3`, an integer slope `σ` and integer labels `A, B`, the mixed
correlation at level `nm`

`C(n, m; σ; A, B) = ∑_{r,t < n} x_{A + m(r,t)} λ_{B - σ m (r,t)}`

equals a finite combination of terms `x_{aA + bB} λ_{cA + dB}` at level `nm` with
`n ∣ a - σ b`, `n ∣ c - σ d`, plus the value of a weight-three congruence-class series form at a
level divisible by `nm` (`corr3_rows`).

The proof is a Euclidean recursion: a root-point enlargement to level `s·nm` followed by the second
weight-three distribution congruence gives
`C(n,m;s;A,B) = rows + (n/s) C(s, nm; -n; sA+B, nB) + series` (`corr3_step`), and the slope is
reduced modulo the new torsion order. No caller-supplied correlation or slope statement is used.

As a consequence the slope statement `SlopeClosed` of the repeated-prime mixed trace holds for
every slope (`slopeClosed_all`), giving the repeated-prime mixed trace in the degree-three product
span for every prime `p ∣ ℓ`, `ℓ ≥ 3` (`trace_cross_mem_degreeThree`).
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.MixedWeightThreeSlope

open TorsionWeierstrassData TorsionWeightThree MixedWeightThreeAddition MixedWeightThreeDistribution
open DivisionEisensteinLevelMaps RepeatedPrimeMixedTrace RepeatedPrimeMixedTraceBinder
open AllWeightSeriesTrace

/-! ### Series values -/

/-- `f` is the value of a member of the weight-three class-series span at level `K`. -/
def SeriesVal (K : ℕ) (f : ℍ → ℂ) : Prop :=
  ∃ hK : 0 < K, ∃ E ∈ classSeriesSpan K hK, ∀ τ, E τ = f τ

theorem SeriesVal.of_mem {K : ℕ} (hK : 0 < K) {E : Weight K 3} (hE : E ∈ classSeriesSpan K hK) :
    SeriesVal K (fun τ => E τ) := ⟨hK, E, hE, fun _ => rfl⟩

theorem SeriesVal.zero {K : ℕ} (hK : 0 < K) : SeriesVal K (fun _ => 0) :=
  ⟨hK, 0, Submodule.zero_mem _, fun _ => rfl⟩

theorem SeriesVal.congr {K : ℕ} {f g : ℍ → ℂ} (hfg : ∀ τ, f τ = g τ) (hf : SeriesVal K f) :
    SeriesVal K g := by
  obtain ⟨hK, E, hE, he⟩ := hf
  exact ⟨hK, E, hE, fun τ => (he τ).trans (hfg τ)⟩

theorem SeriesVal.add {K : ℕ} {f g : ℍ → ℂ} (hf : SeriesVal K f) (hg : SeriesVal K g) :
    SeriesVal K (fun τ => f τ + g τ) := by
  obtain ⟨hK, E, hE, he⟩ := hf
  obtain ⟨_, F, hF, hf'⟩ := hg
  refine ⟨hK, E + F, Submodule.add_mem _ hE hF, fun τ => ?_⟩
  rw [FunLike.coe_add, Pi.add_apply, he, hf']

theorem SeriesVal.smul {K : ℕ} (c : ℂ) {f : ℍ → ℂ} (hf : SeriesVal K f) :
    SeriesVal K (fun τ => c * f τ) := by
  obtain ⟨hK, E, hE, he⟩ := hf
  refine ⟨hK, c • E, Submodule.smul_mem _ c hE, fun τ => ?_⟩
  rw [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, he]

theorem SeriesVal.sub {K : ℕ} {f g : ℍ → ℂ} (hf : SeriesVal K f) (hg : SeriesVal K g) :
    SeriesVal K (fun τ => f τ - g τ) :=
  (hf.add (hg.smul (-1))).congr fun τ => by ring

theorem SeriesVal.sum {K : ℕ} (hK : 0 < K) {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, SeriesVal K (f i)) : SeriesVal K (fun τ => ∑ i ∈ s, f i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (SeriesVal.zero hK).congr fun τ => by simp
  | insert i s hi ih =>
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    exact (h1.add h2).congr fun τ => by rw [Finset.sum_insert hi]

theorem SeriesVal.sum2 {K : ℕ} (hK : 0 < K) (s : ℕ) (f : Fin s → Fin s → ℍ → ℂ)
    (h : ∀ u v, SeriesVal K (f u v)) :
    SeriesVal K (fun τ => ∑ u : Fin s, ∑ v : Fin s, f u v τ) :=
  SeriesVal.sum hK _ _ fun u _ => SeriesVal.sum hK _ _ fun v _ => h u v

theorem SeriesVal.level {K K' : ℕ} {f : ℍ → ℂ} (h : K = K') (hf : SeriesVal K f) :
    SeriesVal K' f := h ▸ hf

theorem restriction3_eq (N M : ℕ) (hNM : N ∣ M) :
    restriction3 N M hNM = restrictionK N M 3 hNM := rfl

theorem classSeries_restrict (K t : ℕ) (h3 : 3 ≤ K) (ht : 0 < t) {E : Weight K 3}
    (hE : E ∈ classSeriesSpan K (by omega)) :
    restriction3 K (t * K) (dvd_mul_left K t) E ∈ classSeriesSpan (t * K) (by positivity) := by
  have h3' : 3 ≤ t * K := by nlinarith
  rw [classSeriesSpan_eq_seriesSpanK K h3] at hE
  rw [classSeriesSpan_eq_seriesSpanK (t * K) h3', restriction3_eq]
  have hle : seriesSpanK K h3 3 le_rfl ≤
      (seriesSpanK (t * K) h3' 3 le_rfl).comap (restrictionK K (t * K) 3 (dvd_mul_left K t)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, restrictionK_generator_mul K t 3 h3 ht le_rfl a]
    exact generator_mem_seriesSpanK _ _ _ _ _
  exact hle hE

theorem SeriesVal.restrict {K K' : ℕ} {f : ℍ → ℂ} (h3 : 3 ≤ K) (hKK' : K ∣ K') (hK' : 0 < K')
    (hf : SeriesVal K f) : SeriesVal K' f := by
  obtain ⟨t, rfl⟩ := hKK'
  have ht : 0 < t := Nat.pos_of_mul_pos_left hK'
  obtain ⟨_, E, hE, he⟩ := hf
  have hmem := classSeries_restrict K t h3 ht hE
  refine SeriesVal.level (mul_comm t K) ⟨by positivity, _, hmem, fun τ => ?_⟩
  rw [restriction3_apply, he]

/-! ### Basic value identities -/

theorem lambdaValue_scale {s : ℕ} (hs : 0 < s) (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    lambdaValue (s * N) ((s : ℤ) * a) ((s : ℤ) * b) τ = lambdaValue N a b τ := by
  unfold lambdaValue
  rw [TorsionCorrelation.reg_scale s N hs hN a b τ]

/-- The weight-three correlation. -/
def corr3 (n m : ℕ) (σ : ℤ) (A B : ℤ × ℤ) (τ : ℍ) : ℂ :=
  ∑ r : Fin n, ∑ t : Fin n,
    xValue (n * m) (A.1 + m * ((r : ℕ) : ℤ)) (A.2 + m * ((t : ℕ) : ℤ)) τ *
      lambdaValue (n * m) (B.1 - σ * (m * ((r : ℕ) : ℤ))) (B.2 - σ * (m * ((t : ℕ) : ℤ))) τ

/-- The four lower terms of one recursion step, at level `nm`. -/
def stepRows (n m s : ℕ) (A B : ℤ × ℤ) (τ : ℍ) : ℂ :=
  -((n : ℂ) * s) * (xValue (n * m) (n * A.1) (n * A.2) τ * lambdaValue (n * m) (n * A.1) (n * A.2) τ) +
    (n : ℂ) ^ 2 * (xValue (n * m) (n * A.1) (n * A.2) τ *
      lambdaValue (n * m) (s * A.1 + B.1) (s * A.2 + B.2) τ) +
    (n : ℂ) * s * (xValue (n * m) (s * A.1 + B.1) (s * A.2 + B.2) τ *
      lambdaValue (n * m) (n * A.1) (n * A.2) τ) -
    (n : ℂ) ^ 2 * (xValue (n * m) (s * A.1 + B.1) (s * A.2 + B.2) τ *
      lambdaValue (n * m) (s * A.1 + B.1) (s * A.2 + B.2) τ)

/-- The second distribution congruence as a series value. -/
theorem cross_seriesVal (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (a b c d : ℤ) :
    SeriesVal (n * N) (fun τ =>
      (∑ r : Fin n, ∑ t : Fin n,
        xValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((t : ℕ) : ℤ)) τ *
          lambdaValue (n * N) (c - N * ((r : ℕ) : ℤ)) (d - N * ((t : ℕ) : ℤ)) τ) -
      (-(n : ℂ) * (xValue (n * N) (n * a) (n * b) τ * lambdaValue (n * N) (n * a) (n * b) τ) +
        (n : ℂ) ^ 2 * (xValue (n * N) (n * a) (n * b) τ * lambdaValue (n * N) (a + c) (b + d) τ) +
        (n : ℂ) * (xValue (n * N) (a + c) (b + d) τ * lambdaValue (n * N) (n * a) (n * b) τ) +
        (n : ℂ) * (xValue (n * N) (a + c) (b + d) τ * lambdaValue (n * N) (n * c) (n * d) τ) -
        (n : ℂ) ^ 2 * (xValue (n * N) (a + c) (b + d) τ * lambdaValue (n * N) (a + c) (b + d) τ))) := by
  refine (SeriesVal.of_mem (Nat.mul_pos hn hN) (cross_distribution_mem n N hn hN a b c d)).congr ?_
  intro τ
  simp only [_root_.sum_apply, _root_.smul_apply, _root_.sub_apply, _root_.add_apply,
    smul_eq_mul, crossForm_apply, xlamForm_apply]

/-- The first distribution congruence as a series value, with the scaled term at level `N`. -/
theorem xlam_seriesVal (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (a b : ℤ) :
    SeriesVal (n * N) (fun τ =>
      (∑ r : Fin n, ∑ t : Fin n,
        xValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((t : ℕ) : ℤ)) τ *
          lambdaValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((t : ℕ) : ℤ)) τ) -
      (n : ℂ) * (xValue N a b τ * lambdaValue N a b τ)) := by
  refine (SeriesVal.of_mem (Nat.mul_pos hn hN) (xlam_distribution_mem n N hn hN a b)).congr ?_
  intro τ
  simp only [_root_.sum_apply, _root_.smul_apply, _root_.sub_apply, smul_eq_mul, xlamForm_apply]
  rw [TorsionMuDistributionNat.xValue_scale hn N a b τ, lambdaValue_scale hn N hN a b τ]

/-! ### One recursion step -/

theorem corr3_V1 (n m s : ℕ) (hn : 0 < n) (hm : 0 < m) (hs : 0 < s) (A B : ℤ × ℤ) (τ : ℍ) :
    (∑ u : Fin s, ∑ v : Fin s, ∑ r : Fin n, ∑ t : Fin n,
      xValue (n * (s * m)) (s * A.1 + (s * m : ℕ) * ((r : ℕ) : ℤ))
          (s * A.2 + (s * m : ℕ) * ((t : ℕ) : ℤ)) τ *
        lambdaValue (n * (s * m)) ((B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)) - (s * m : ℕ) * ((r : ℕ) : ℤ))
          ((B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ)) - (s * m : ℕ) * ((t : ℕ) : ℤ)) τ) =
      (s : ℂ) * corr3 n m s A B τ := by
  have hM : 0 < n * m := Nat.mul_pos hn hm
  rw [TorsionMuDistributionNat.swap4]
  unfold corr3
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hx : xValue (n * (s * m)) (s * A.1 + (s * m : ℕ) * ((r : ℕ) : ℤ))
      (s * A.2 + (s * m : ℕ) * ((t : ℕ) : ℤ)) τ =
      xValue (n * m) (A.1 + m * ((r : ℕ) : ℤ)) (A.2 + m * ((t : ℕ) : ℤ)) τ := by
    rw [show n * (s * m) = s * (n * m) by ring, ← TorsionMuDistributionNat.xValue_scale hs (n * m)]
    congr 1 <;> push_cast <;> ring
  simp_rw [hx, ← Finset.mul_sum]
  have hl := lam_sum (n := s) (N := n * m) hs hM (B.1 - (s : ℤ) * (m * ((r : ℕ) : ℤ)))
    (B.2 - (s : ℤ) * (m * ((t : ℕ) : ℤ))) τ
  have he : (∑ u : Fin s, ∑ v : Fin s,
      lambdaValue (n * (s * m)) ((B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)) - (s * m : ℕ) * ((r : ℕ) : ℤ))
        ((B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ)) - (s * m : ℕ) * ((t : ℕ) : ℤ)) τ) =
      ∑ u : Fin s, ∑ v : Fin s,
        lambdaValue (s * (n * m)) (B.1 - (s : ℤ) * (m * ((r : ℕ) : ℤ)) + (n * m : ℕ) * ((u : ℕ) : ℤ))
          (B.2 - (s : ℤ) * (m * ((t : ℕ) : ℤ)) + (n * m : ℕ) * ((v : ℕ) : ℤ)) τ := by
    rw [show n * (s * m) = s * (n * m) by ring]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    congr 1 <;> push_cast <;> ring
  rw [he, hl]
  ring

theorem corr3_step (n m s : ℕ) (hn : 0 < n) (hm : 0 < m) (hs : 0 < s) (A B : ℤ × ℤ) :
    SeriesVal (n * (s * m)) (fun τ => corr3 n m s A B τ - stepRows n m s A B τ -
      ((n : ℂ) / s) * corr3 s (n * m) (-(n : ℤ)) (s * A.1 + B.1, s * A.2 + B.2)
        (n * B.1, n * B.2) τ) := by
  have hM : 0 < n * m := Nat.mul_pos hn hm
  have hsm : 0 < s * m := Nat.mul_pos hs hm
  have hK : 0 < n * (s * m) := Nat.mul_pos hn hsm
  have hs0 : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
  set a : ℤ := s * A.1 with ha
  set b : ℤ := s * A.2 with hb
  -- second congruence for each shift of `B`
  have hV2 := SeriesVal.sum2 hK s (fun (u v : Fin s) τ =>
      (∑ r : Fin n, ∑ t : Fin n,
        xValue (n * (s * m)) (a + (s * m : ℕ) * ((r : ℕ) : ℤ)) (b + (s * m : ℕ) * ((t : ℕ) : ℤ)) τ *
          lambdaValue (n * (s * m)) ((B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)) - (s * m : ℕ) * ((r : ℕ) : ℤ))
            ((B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ)) - (s * m : ℕ) * ((t : ℕ) : ℤ)) τ) -
      (-(n : ℂ) * (xValue (n * (s * m)) (n * a) (n * b) τ *
          lambdaValue (n * (s * m)) (n * a) (n * b) τ) +
        (n : ℂ) ^ 2 * (xValue (n * (s * m)) (n * a) (n * b) τ *
          lambdaValue (n * (s * m)) (a + (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)))
            (b + (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ) +
        (n : ℂ) * (xValue (n * (s * m)) (a + (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)))
            (b + (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ *
          lambdaValue (n * (s * m)) (n * a) (n * b) τ) +
        (n : ℂ) * (xValue (n * (s * m)) (a + (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)))
            (b + (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ *
          lambdaValue (n * (s * m)) (n * (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)))
            (n * (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ) -
        (n : ℂ) ^ 2 * (xValue (n * (s * m)) (a + (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)))
            (b + (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ *
          lambdaValue (n * (s * m)) (a + (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)))
            (b + (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ)))
    (fun u v => cross_seriesVal n (s * m) hn hsm a b _ _)
  -- first congruence at level `s·nm`
  have hV3 := (xlam_seriesVal s (n * m) hs hM (s * A.1 + B.1) (s * A.2 + B.2)).level
    (show s * (n * m) = n * (s * m) by ring)
  refine ((hV2.smul (1 / (s : ℂ))).sub (hV3.smul ((n : ℂ) ^ 2 / s))).congr ?_
  intro τ
  -- notation for the pieces
  set XA : ℂ := xValue (n * m) (n * A.1) (n * A.2) τ with hXA
  set LA : ℂ := lambdaValue (n * m) (n * A.1) (n * A.2) τ with hLA
  set XV : ℂ := xValue (n * m) (s * A.1 + B.1) (s * A.2 + B.2) τ with hXV
  set LV : ℂ := lambdaValue (n * m) (s * A.1 + B.1) (s * A.2 + B.2) τ with hLV
  have hP1 : xValue (n * (s * m)) (n * a) (n * b) τ = XA := by
    rw [hXA, show n * (s * m) = s * (n * m) by ring, ← TorsionMuDistributionNat.xValue_scale hs (n * m)]
    congr 1 <;> ring
  have hP2 : lambdaValue (n * (s * m)) (n * a) (n * b) τ = LA := by
    rw [hLA, show n * (s * m) = s * (n * m) by ring, ← lambdaValue_scale hs (n * m) hM]
    congr 1 <;> ring
  have hP3 : (∑ u : Fin s, ∑ v : Fin s, lambdaValue (n * (s * m))
      (a + (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ))) (b + (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ) =
      (s : ℂ) * LV := by
    rw [hLV, ← lam_sum (n := s) (N := n * m) hs hM, show n * (s * m) = s * (n * m) by ring]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    congr 1 <;> ring
  have hP4 : (∑ u : Fin s, ∑ v : Fin s, xValue (n * (s * m))
      (a + (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ))) (b + (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ) =
      (s : ℂ) ^ 2 * XV := by
    rw [hXV, ← WeierstrassDistributionNat.x_distribution_nat s (n * m) hs hM τ,
      show n * (s * m) = s * (n * m) by ring]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    congr 1 <;> ring
  have hP5 : (∑ u : Fin s, ∑ v : Fin s, xValue (n * (s * m))
      (a + (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ))) (b + (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ *
      lambdaValue (n * (s * m)) (n * (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)))
        (n * (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ) =
      corr3 s (n * m) (-(n : ℤ)) (s * A.1 + B.1, s * A.2 + B.2) (n * B.1, n * B.2) τ := by
    unfold corr3
    rw [show n * (s * m) = s * (n * m) by ring]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    congr 1
    · congr 1 <;> push_cast <;> ring
    · congr 1 <;> push_cast <;> ring
  have hP6 : (∑ u : Fin s, ∑ v : Fin s, xValue (n * (s * m))
      (a + (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ))) (b + (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ *
      lambdaValue (n * (s * m)) (a + (B.1 + (n * m : ℕ) * ((u : ℕ) : ℤ)))
        (b + (B.2 + (n * m : ℕ) * ((v : ℕ) : ℤ))) τ) =
      ∑ r : Fin s, ∑ t : Fin s,
        xValue (s * (n * m)) (s * A.1 + B.1 + (n * m : ℕ) * ((r : ℕ) : ℤ))
          (s * A.2 + B.2 + (n * m : ℕ) * ((t : ℕ) : ℤ)) τ *
        lambdaValue (s * (n * m)) (s * A.1 + B.1 + (n * m : ℕ) * ((r : ℕ) : ℤ))
          (s * A.2 + B.2 + (n * m : ℕ) * ((t : ℕ) : ℤ)) τ := by
    rw [show n * (s * m) = s * (n * m) by ring]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    congr 1
    · congr 1 <;> ring
    · congr 1 <;> ring
  have hV1 := corr3_V1 n m s hn hm hs A B τ
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    hP1, hP2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hV1 ⊢
  rw [hP3, hP4, hP5, ← hP6, hV1]
  unfold stepRows
  rw [← hXA, ← hLA, ← hXV, ← hLV]
  field_simp
  ring

/-! ### Rows -/

open TorsionCorrelationRows (Rows)

/-- The value `x_{aA+bB} λ_{cA+dB}` of a row at level `M`. -/
def rowVal3 (M : ℕ) (A B : ℤ × ℤ) (R : Rows) (τ : ℍ) : ℂ :=
  xValue M (R.a * A.1 + R.b * B.1) (R.a * A.2 + R.b * B.2) τ *
    lambdaValue M (R.c * A.1 + R.d * B.1) (R.c * A.2 + R.d * B.2) τ

/-- A finite weighted row combination. -/
def rowSum3 (M : ℕ) (A B : ℤ × ℤ) (L : List (ℂ × Rows)) (τ : ℍ) : ℂ :=
  (L.map fun T => T.1 * rowVal3 M A B T.2 τ).sum

/-- The slope congruences of a row. -/
def Valid3 (n : ℕ) (σ : ℤ) (R : Rows) : Prop :=
  (n : ℤ) ∣ R.a - σ * R.b ∧ (n : ℤ) ∣ R.c - σ * R.d

/-- Transport of a row from level `s·M` (labels `sA + B`, `nB`) to level `M`. -/
def tr3 (n s : ℕ) (R : Rows) : Rows :=
  ⟨R.a, (R.a + n * R.b) / s, R.c, (R.c + n * R.d) / s⟩

theorem rowVal3_transport (n s M : ℕ) (hs : 0 < s) (hM : 0 < M) (A B : ℤ × ℤ) (R : Rows)
    (hv : Valid3 s (-(n : ℤ)) R) (τ : ℍ) :
    rowVal3 (s * M) (s * A.1 + B.1, s * A.2 + B.2) (n * B.1, n * B.2) R τ =
      rowVal3 M A B (tr3 n s R) τ := by
  have h1 : (s : ℤ) ∣ R.a + n * R.b := by
    have := hv.1; rwa [show R.a - -(n : ℤ) * R.b = R.a + n * R.b by ring] at this
  have h2 : (s : ℤ) ∣ R.c + n * R.d := by
    have := hv.2; rwa [show R.c - -(n : ℤ) * R.d = R.c + n * R.d by ring] at this
  have hq1 : (s : ℤ) * ((R.a + n * R.b) / s) = R.a + n * R.b := Int.mul_ediv_cancel' h1
  have hq2 : (s : ℤ) * ((R.c + n * R.d) / s) = R.c + n * R.d := Int.mul_ediv_cancel' h2
  unfold rowVal3 tr3
  dsimp only
  rw [← TorsionMuDistributionNat.xValue_scale hs M, ← lambdaValue_scale hs M hM]
  congr 1
  · congr 1
    · linear_combination (-B.1) * hq1
    · linear_combination (-B.2) * hq1
  · congr 1
    · linear_combination (-B.1) * hq2
    · linear_combination (-B.2) * hq2

theorem rowSum3_append (M : ℕ) (A B : ℤ × ℤ) (L L' : List (ℂ × Rows)) (τ : ℍ) :
    rowSum3 M A B (L ++ L') τ = rowSum3 M A B L τ + rowSum3 M A B L' τ := by
  simp [rowSum3]

theorem rowSum3_transport (n s M : ℕ) (hs : 0 < s) (hM : 0 < M) (A B : ℤ × ℤ) (c : ℂ) (τ : ℍ) :
    ∀ L : List (ℂ × Rows), (∀ T ∈ L, Valid3 s (-(n : ℤ)) T.2) →
      rowSum3 M A B (L.map fun T => (c * T.1, tr3 n s T.2)) τ =
        c * rowSum3 (s * M) (s * A.1 + B.1, s * A.2 + B.2) (n * B.1, n * B.2) L τ
  | [], _ => by simp [rowSum3]
  | T :: L, hL => by
    have ih := rowSum3_transport n s M hs hM A B c τ L fun U hU => hL U (by simp [hU])
    unfold rowSum3 at ih ⊢
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, rowVal3_transport n s M hs hM A B T.2 (hL T (by simp)) τ]
    ring

theorem tr3_valid {n s : ℕ} {σ : ℤ} (_hs : 0 < s) (hcong : (n : ℤ) ∣ (s : ℤ) - σ) {R : Rows}
    (hv : Valid3 s (-(n : ℤ)) R) : Valid3 n σ (tr3 n s R) := by
  have h1 : (s : ℤ) ∣ R.a + n * R.b := by
    have := hv.1; rwa [show R.a - -(n : ℤ) * R.b = R.a + n * R.b by ring] at this
  have h2 : (s : ℤ) ∣ R.c + n * R.d := by
    have := hv.2; rwa [show R.c - -(n : ℤ) * R.d = R.c + n * R.d by ring] at this
  have hq1 : (s : ℤ) * ((R.a + n * R.b) / s) = R.a + n * R.b := Int.mul_ediv_cancel' h1
  have hq2 : (s : ℤ) * ((R.c + n * R.d) / s) = R.c + n * R.d := Int.mul_ediv_cancel' h2
  unfold Valid3 tr3
  dsimp only
  constructor
  · rw [show R.a - σ * ((R.a + n * R.b) / s) = ((s : ℤ) - σ) * ((R.a + n * R.b) / s) + n * (-R.b) by
      linear_combination (-1 : ℤ) * hq1]
    exact dvd_add (dvd_mul_of_dvd_left hcong _) (dvd_mul_right _ _)
  · rw [show R.c - σ * ((R.c + n * R.d) / s) = ((s : ℤ) - σ) * ((R.c + n * R.d) / s) + n * (-R.d) by
      linear_combination (-1 : ℤ) * hq2]
    exact dvd_add (dvd_mul_of_dvd_left hcong _) (dvd_mul_right _ _)

/-- The rows of one recursion step. -/
def stepList (n s : ℕ) : List (ℂ × Rows) :=
  [(-((n : ℂ) * s), ⟨n, 0, n, 0⟩), ((n : ℂ) ^ 2, ⟨n, 0, s, 1⟩), ((n : ℂ) * s, ⟨s, 1, n, 0⟩),
    (-((n : ℂ) ^ 2), ⟨s, 1, s, 1⟩)]

theorem rowSum3_stepList (n m s : ℕ) (A B : ℤ × ℤ) (τ : ℍ) :
    rowSum3 (n * m) A B (stepList n s) τ = stepRows n m s A B τ := by
  simp only [rowSum3, rowVal3, stepList, stepRows, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, zero_mul, add_zero, one_mul]
  ring

theorem stepList_valid {n s : ℕ} {σ : ℤ} (hcong : (n : ℤ) ∣ (s : ℤ) - σ) :
    ∀ T ∈ stepList n s, Valid3 n σ T.2 := by
  intro T hT
  simp only [stepList, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_⟩ <;> simp only [mul_zero, sub_zero,
    mul_one]
  · exact dvd_refl _
  · exact dvd_refl _
  · exact dvd_refl _
  · exact hcong
  · exact hcong
  · exact dvd_refl _
  · exact hcong
  · exact hcong

/-! ### Slope reduction and the base case -/

theorem corr3_slope_congr (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (σ σ' : ℤ) (h : (n : ℤ) ∣ σ - σ')
    (A B : ℤ × ℤ) (τ : ℍ) : corr3 n m σ A B τ = corr3 n m σ' A B τ := by
  have : NeZero (n * m) := ⟨(Nat.mul_pos hn hm).ne'⟩
  obtain ⟨k, hk⟩ := h
  unfold corr3
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
  congr 1
  apply lambdaValue_congr
  · exact ⟨-(k * ((r : ℕ) : ℤ)), by push_cast; linear_combination (-(m : ℤ) * ((r : ℕ) : ℤ)) * hk⟩
  · exact ⟨-(k * ((t : ℕ) : ℤ)), by push_cast; linear_combination (-(m : ℤ) * ((t : ℕ) : ℤ)) * hk⟩

theorem corr3_base (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (A B : ℤ × ℤ) (τ : ℍ) :
    corr3 n m 0 A B τ = rowSum3 (n * m) A B [((n : ℂ) ^ 2, ⟨n, 0, 0, 1⟩)] τ := by
  unfold corr3
  simp only [zero_mul, sub_zero]
  simp_rw [← Finset.sum_mul]
  rw [WeierstrassDistributionNat.x_distribution_nat n m hn hm τ A.1 A.2,
    ← TorsionMuDistributionNat.xValue_scale hn m A.1 A.2 τ]
  simp [rowSum3, rowVal3]
  ring

/-! ### The Euclidean recursion -/

/-- **Arbitrary-slope correlation identity.** -/
theorem corr3_rows : ∀ n : ℕ, 0 < n → ∀ m : ℕ, 3 ≤ m → ∀ (σ : ℤ) (A B : ℤ × ℤ),
    ∃ L : List (ℂ × Rows), (∀ T ∈ L, Valid3 n σ T.2) ∧
      ∃ K : ℕ, n * m ∣ K ∧ SeriesVal K (fun τ => corr3 n m σ A B τ - rowSum3 (n * m) A B L τ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn m hm σ A B
    have hm0 : 0 < m := by omega
    have hM : 0 < n * m := Nat.mul_pos hn hm0
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    set r : ℕ := (σ % n).toNat with hrdef
    have hr : ((r : ℕ) : ℤ) = σ % n := Int.toNat_of_nonneg (Int.emod_nonneg σ hnZ.ne')
    have hrn : r < n := by
      have := Int.emod_lt_of_pos σ hnZ
      omega
    have hσr : (n : ℤ) ∣ σ - r := by
      rw [hr]
      exact ⟨σ / n, by linarith [Int.emod_add_mul_ediv σ n]⟩
    by_cases hr0 : r = 0
    · refine ⟨[((n : ℂ) ^ 2, ⟨n, 0, 0, 1⟩)], ?_, n * m, dvd_refl _, ?_⟩
      · intro T hT
        simp only [List.mem_singleton] at hT
        subst hT
        refine ⟨by simp, ?_⟩
        rw [hr0] at hσr
        simpa using hσr
      · refine (SeriesVal.zero hM).congr fun τ => ?_
        rw [corr3_slope_congr n m hn hm0 σ 0 (by rw [hr0] at hσr; simpa using hσr) A B τ,
          corr3_base n m hn hm0 A B τ]
        ring
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have hcong : (n : ℤ) ∣ (r : ℤ) - σ := by
        rw [show (r : ℤ) - σ = -(σ - r) by ring]; exact (dvd_neg).mpr hσr
      obtain ⟨L', hL', K, hK, hS⟩ := ih r hrn hrpos (n * m) (by nlinarith) (-(n : ℤ))
        (r * A.1 + B.1, r * A.2 + B.2) (n * B.1, n * B.2)
      refine ⟨stepList n r ++ L'.map (fun T => ((n : ℂ) / r * T.1, tr3 n r T.2)), ?_, K,
        (dvd_mul_left _ _).trans hK, ?_⟩
      · intro T hT
        rcases List.mem_append.mp hT with hT | hT
        · exact stepList_valid hcong T hT
        · obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hT
          exact tr3_valid hrpos hcong (hL' U hU)
      · have hstep := (corr3_step n m r hn hm0 hrpos A B).restrict (by nlinarith)
          (show n * (r * m) ∣ K from by rw [show n * (r * m) = r * (n * m) by ring]; exact hK)
          hS.fst
        refine (hstep.add (hS.smul ((n : ℂ) / r))).congr fun τ => ?_
        rw [corr3_slope_congr n m hn hm0 σ r hσr A B τ, rowSum3_append, rowSum3_stepList,
          rowSum3_transport n r (n * m) hrpos hM A B _ τ L' hL']
        ring

/-! ### All slopes of the repeated-prime mixed trace -/

open AllLevelForms AllLevelPrincipal in
/-- **Every slope.** -/
theorem slopeClosed_all (p ell : ℕ) [Fact p.Prime] (h3 : 3 ≤ ell) (hpl : p ∣ ell) (σ : ℤ) :
    SlopeClosed p ell (by omega) σ := by
  intro a b c d hab hc hd
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hl : 0 < ell := by omega
  set hM := Nat.mul_pos hp hl
  have : NeZero (p * ell) := ⟨hM.ne'⟩
  rw [trace_fibre3_average p ell hl hpl a b c d σ hab hc hd]
  apply Submodule.smul_mem
  apply trace_upperGood hl hM
  obtain ⟨L, hL, K, hK, hS⟩ := corr3_rows p hp ell h3 (-σ) (a, b) (c, d)
  have hrowv : ∀ (L' : List (ℂ × Rows)) (τ : ℍ), (L'.map fun T => T.1 • crossForm (p * ell) hM
      (T.2.a * a + T.2.b * c) (T.2.a * b + T.2.b * d) (T.2.c * a + T.2.d * c)
      (T.2.c * b + T.2.d * d)).sum τ = rowSum3 (p * ell) (a, b) (c, d) L' τ := by
    intro L' τ
    induction L' with
    | nil => simp [rowSum3]
    | cons T L' ih =>
      rw [List.map_cons, List.sum_cons, _root_.add_apply, ih]
      simp only [rowSum3, List.map_cons, List.sum_cons, _root_.smul_apply, smul_eq_mul,
        crossForm_apply, rowVal3]
  -- the row forms
  set rowsForm : Weight (p * ell) 3 := (L.map fun T => T.1 • crossForm (p * ell) hM
    (T.2.a * a + T.2.b * c) (T.2.a * b + T.2.b * d) (T.2.c * a + T.2.d * c)
    (T.2.c * b + T.2.d * d)).sum with hrows
  have hrows_mem : rowsForm ∈ upperGood p ell hl hM := by
    rw [hrows]
    have : ∀ L' : List (ℂ × Rows), (∀ T ∈ L', Valid3 p (-σ) T.2) →
        (L'.map fun T => T.1 • crossForm (p * ell) hM
          (T.2.a * a + T.2.b * c) (T.2.a * b + T.2.b * d) (T.2.c * a + T.2.d * c)
          (T.2.c * b + T.2.d * d)).sum ∈ upperGood p ell hl hM := by
      intro L' hL'
      induction L' with
      | nil => exact Submodule.zero_mem _
      | cons T L' ih =>
        rw [List.map_cons, List.sum_cons]
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (ih fun U hU => hL' U (by simp [hU]))
        obtain ⟨h1, h2⟩ := hL' T (by simp)
        rw [show T.2.a - -σ * T.2.b = T.2.a + σ * T.2.b by ring] at h1
        rw [show T.2.c - -σ * T.2.d = T.2.c + σ * T.2.d by ring] at h2
        have e1 : T.2.a * a + T.2.b * c = (T.2.a + σ * T.2.b) * a + T.2.b * (c - σ * a) := by ring
        have e2 : T.2.a * b + T.2.b * d = (T.2.a + σ * T.2.b) * b + T.2.b * (d - σ * b) := by ring
        have e3 : T.2.c * a + T.2.d * c = (T.2.c + σ * T.2.d) * a + T.2.d * (c - σ * a) := by ring
        have e4 : T.2.c * b + T.2.d * d = (T.2.c + σ * T.2.d) * b + T.2.d * (d - σ * b) := by ring
        refine cross_mem_upper hp hl hM ?_ ?_ ?_ ?_
        · rw [e1]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right hc _)
        · rw [e2]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right hd _)
        · rw [e3]; exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right hc _)
        · rw [e4]; exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right hd _)
    exact this L hL
  -- the value of the fibre and of the row forms
  have hfib : ∀ τ, fibre3 p ell hM a b c d σ τ = corr3 p ell (-σ) (a, b) (c, d) τ := by
    intro τ
    unfold fibre3 corr3
    simp only [_root_.sum_apply, crossForm_apply]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
    congr 2 <;> ring
  -- the difference is a level `pℓ` form with series values at level `K`
  set G : Weight (p * ell) 3 := fibre3 p ell hM a b c d σ - rowsForm with hG
  have hGv : ∀ τ, G τ = corr3 p ell (-σ) (a, b) (c, d) τ - rowSum3 (p * ell) (a, b) (c, d) L τ := by
    intro τ
    rw [hG, _root_.sub_apply, hfib, hrows, hrowv]
  obtain ⟨hK0, E, hE, hEv⟩ := hS
  have h3K : 3 ≤ K := (show 3 ≤ p * ell by nlinarith).trans (Nat.le_of_dvd hK0 hK)
  have h3M : 3 ≤ p * ell := by nlinarith
  have hres : restrictionK (p * ell) K 3 hK G = E := by
    apply _root_.ModularForm.ext
    intro τ
    rw [restrictionK_apply, hGv, hEv]
  have hmemK : restrictionK (p * ell) K 3 hK G ∈ seriesSpanK K h3K 3 le_rfl := by
    rw [hres, ← classSeriesSpan_eq_seriesSpanK K h3K]
    exact hE
  obtain ⟨g, hg, hge⟩ := invariant_seriesK_descent K (p * ell) h3M hK0 hK 3 le_rfl
    (restrictionK (p * ell) K 3 hK G) hmemK (fun γ hγ => G.slash_action_eq' γ hγ)
  have hgG : g = G := restrictionK_injective (p * ell) K 3 hK hge
  have hGmem : G ∈ upperGood p ell hl hM := by
    apply classSeries_le_upper hl hM
    rw [classSeriesSpan_eq_seriesSpanK (p * ell) h3M, ← hgG]
    exact hg
  have hsplit : fibre3 p ell hM a b c d σ = G + rowsForm := by rw [hG]; abel
  rw [hsplit]
  exact Submodule.add_mem _ hGmem hrows_mem

/-- **Repeated-prime mixed trace, every prime** `p ∣ ℓ`, `ℓ ≥ 3`, all integer labels: lower mixed
forms plus the trace of the upper class series. -/
theorem trace_cross_mem_target (p ell : ℕ) [Fact p.Prime] (h3 : 3 ≤ ell) (hpl : p ∣ ell)
    (a b c d : ℤ) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) a b c d) ∈
      target p ell (by omega) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) :=
  trace_cross_mem_of_slopes p ell (by omega) hpl (slopeClosed_all p ell h3 hpl) a b c d

/-- **Repeated-prime mixed trace, every prime**: lower mixed forms plus lower class series. -/
theorem trace_cross_mem_lower (p ell : ℕ) [Fact p.Prime] (h3 : 3 ≤ ell) (hpl : p ∣ ell)
    (a b c d : ℤ) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) a b c d) ∈
      lowerMixedSpan ell (by omega) ⊔ classSeriesSpan ell (by omega) :=
  target_le p ell h3 _ (trace_cross_mem_target p ell h3 hpl a b c d)

/-- **Repeated-prime mixed trace, every prime**: in the degree-three product span. -/
theorem trace_cross_mem_degreeThree (p ell : ℕ) [Fact p.Prime] (h3 : 3 ≤ ell) (hpl : p ∣ ell)
    (a b c d : ℤ) :
    normalizedTrace3 ell (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (crossForm (p * ell) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) a b c d) ∈
      degreeThreeProductSpan ell (by omega) :=
  trace_cross_mem_degreeThree_of_slopes p ell h3 hpl (slopeClosed_all p ell h3 hpl) a b c d

end ZInQ.Contrib.HeckePrimeRationality.MixedWeightThreeSlope
