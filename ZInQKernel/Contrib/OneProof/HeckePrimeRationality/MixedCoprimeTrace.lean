import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.MixedWeightThreeSlope
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimePrincipalProductTrace

/-!
# Coprime-prime trace of mixed weight-three products

Let `p` be prime, `ℓ ≥ 3` and `p` coprime to `ℓ`. For the actual normalized weight-three trace
from `Γ(pℓ)` to `Γ(ℓ)`, the trace of every mixed form `x_P λ_Q` at level `pℓ` (all integer labels)
lies in the span of admissible degree-three products at level `ℓ` (`trace_cross_coprime_mem`).

Proof: split `P = pA + ℓT`, `Q = pB + ℓU` by the Chinese remainder theorem. Principal-group motions
fix the lower parts and act on `(T, U)` through `SL(2, 𝔽_p)`, and the normalized trace is constant
along them; an orbit average reduces to the trace of an orbit sum. The orbit sums are:

* `T = U = 0`: a restricted lower mixed form;
* `T = 0`, `U ≠ 0`: `x_A (p λ_{pB} - λ_B)` by the `λ`-distribution;
* `T ≠ 0`, `U = sT`: the full slope-`(-s)` correlation at labels `(pA, pB)` minus its `T = 0` term;
  the arbitrary-slope correlation identity writes it as restricted lower mixed forms plus a
  class-series form;
* `det(T, U) = d ≠ 0`: the `λ`-Fourier duality of the second factor and the determinant-line
  character sum reduce it to slope correlations of the previous case.

All orbit sums lie in restricted lower mixed forms plus the upper class-series span, whose trace is
in lower mixed forms plus the lower class-series span.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups Matrix ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.MixedCoprimeTrace

open TorsionWeierstrassData TorsionWeightThree MixedWeightThreeAddition MixedWeightThreeDistribution
open RepeatedPrimeMixedTrace RepeatedPrimeMixedTraceBinder MixedWeightThreeSlope
open AllLevelPrincipal (CongrN)
open TorsionCorrelation (Point label label_val h_label)
open TorsionCorrelationLower (pointAction pointAction_label)
open CoprimeProductTrace (splitPoint splitPointEquiv lambdaPointValue pairing det Pair
  DeterminantPairs phase coordinate determinant_kernel exists_Gamma_split_pair_move
  exists_SL2_determinant_pair_move split_lambda_fourier determinant_pair_reduction nonzero_components
  finite_residue_val)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-! ### Point-level mixed forms -/

theorem congr_of_label_eq {M : ℕ} {u v : ℤ × ℤ} (he : label M u.1 u.2 = label M v.1 v.2) :
    CongrN M u v :=
  ⟨(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ M).mp (congrArg Prod.fst he).symm,
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ M).mp (congrArg Prod.snd he).symm⟩

/-- The value `x` at a residue point. -/
def xPoint (M : ℕ) (τ : ℍ) (P : Point M) : ℂ := xValue M (P.1.val : ℤ) (P.2.val : ℤ) τ

/-- The mixed form at residue points. -/
def crossPoint (M : ℕ) (hM : 0 < M) (P Q : Point M) : Weight M 3 :=
  crossForm M hM (P.1.val : ℤ) (P.2.val : ℤ) (Q.1.val : ℤ) (Q.2.val : ℤ)

theorem crossPoint_apply (M : ℕ) (hM : 0 < M) (P Q : Point M) (τ : ℍ) :
    crossPoint M hM P Q τ = xPoint M τ P * lambdaPointValue M τ Q := by
  rw [crossPoint, crossForm_apply]
  rfl

theorem crossPoint_label (M : ℕ) (hM : 0 < M) (a b c d : ℤ) :
    crossPoint M hM (label M a b) (label M c d) = crossForm M hM a b c d :=
  crossForm_congr (U := (((label M a b).1.val : ℤ), ((label M a b).2.val : ℤ)))
    (V := (((label M c d).1.val : ℤ), ((label M c d).2.val : ℤ))) (U' := (a, b)) (V' := (c, d)) hM
    (congr_of_label_eq (label_val hM (label M a b))) (congr_of_label_eq (label_val hM (label M c d)))

theorem trace_crossPoint_action (N M : ℕ) (hM : 0 < M) (P Q : Point M) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma N) :
    normalizedTrace3 N M hM (crossPoint M hM (pointAction M γ P) (pointAction M γ Q)) =
      normalizedTrace3 N M hM (crossPoint M hM P Q) := by
  have hc : ∀ R : Point M, CongrN M (ThetaFiveTorsion.act ((R.1.val : ℤ), (R.2.val : ℤ)) γ)
      (((pointAction M γ R).1.val : ℤ), ((pointAction M γ R).2.val : ℤ)) := by
    intro R
    apply congr_of_label_eq
    have h1 := pointAction_label M γ (R.1.val : ℤ) (R.2.val : ℤ)
    have h2 := label_val hM R
    have h3 := label_val hM (pointAction M γ R)
    rw [h2] at h1
    exact h1.symm.trans h3.symm
  have h := normalizedTrace3_cross_move N M hM ((P.1.val : ℤ), (P.2.val : ℤ))
    ((Q.1.val : ℤ), (Q.2.val : ℤ)) (((pointAction M γ P).1.val : ℤ), ((pointAction M γ P).2.val : ℤ))
    (((pointAction M γ Q).1.val : ℤ), ((pointAction M γ Q).2.val : ℤ)) γ hγ (hc P) (hc Q)
  unfold crossPoint
  exact h

/-- Orbit averaging into any target subspace. -/
theorem trace_mem_of_orbit {I : Type*} [Fintype I] (i0 : I) {N M : ℕ} (hM : 0 < M)
    (S : Submodule ℂ (Weight N 3)) (f : I → Weight M 3) (f0 : Weight M 3)
    (hsum : normalizedTrace3 N M hM (∑ i, f i) ∈ S)
    (hconst : ∀ i, normalizedTrace3 N M hM (f i) = normalizedTrace3 N M hM f0) :
    normalizedTrace3 N M hM f0 ∈ S := by
  have : Nonempty I := ⟨i0⟩
  have hc : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [map_sum] at hsum
  simp only [hconst, Finset.sum_const, Finset.card_univ] at hsum
  have h := Submodule.smul_mem S ((Fintype.card I : ℂ)⁻¹) hsum
  rwa [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul] at h

/-! ### Split labels -/

theorem crossPoint_split (p N : ℕ) (hM : 0 < p * N) (A B : Point N) (T U : Point p) :
    crossPoint (p * N) hM (splitPoint p N A T) (splitPoint p N B U) =
      crossForm (p * N) hM ((p : ℤ) * A.1.val + (N : ℤ) * T.1.val)
        ((p : ℤ) * A.2.val + (N : ℤ) * T.2.val) ((p : ℤ) * B.1.val + (N : ℤ) * U.1.val)
        ((p : ℤ) * B.2.val + (N : ℤ) * U.2.val) :=
  crossPoint_label _ hM _ _ _ _

theorem sum_point (p : ℕ) [NeZero p] (G : ℤ → ℤ → ℂ) :
    (∑ U : Point p, G (U.1.val : ℤ) (U.2.val : ℤ)) =
      ∑ r : Fin p, ∑ t : Fin p, G ((r : ℕ) : ℤ) ((t : ℕ) : ℤ) := by
  rw [← (Equiv.prodCongr (ZMod.finEquiv p).toEquiv (ZMod.finEquiv p).toEquiv).sum_comp,
    Fintype.sum_prod_type]
  simp only [Equiv.prodCongr_apply, Prod.map, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    finite_residue_val]

theorem sum_point_forms (p M : ℕ) [NeZero p] (G : ℤ → ℤ → Weight M 3) :
    (∑ U : Point p, G (U.1.val : ℤ) (U.2.val : ℤ)) =
      ∑ r : Fin p, ∑ t : Fin p, G ((r : ℕ) : ℤ) ((t : ℕ) : ℤ) := by
  rw [← (Equiv.prodCongr (ZMod.finEquiv p).toEquiv (ZMod.finEquiv p).toEquiv).sum_comp,
    Fintype.sum_prod_type]
  simp only [Equiv.prodCongr_apply, Prod.map, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    finite_residue_val]

/-! ### Correlations with `p`-divisible labels -/

open TorsionCorrelationRows (Rows) in
/-- A slope correlation at `p`-divisible labels lies in the upper space. -/
theorem fibre3_mem_of_div (p ell : ℕ) (hp : 0 < p) (h3 : 3 ≤ ell) (hl : 0 < ell)
    (hM : 0 < p * ell) (a b c d σ : ℤ) (ha : (p : ℤ) ∣ a) (hb : (p : ℤ) ∣ b) (hc : (p : ℤ) ∣ c)
    (hd : (p : ℤ) ∣ d) :
    fibre3 p ell hM a b c d σ ∈ upperGood p ell hl hM := by
  have : NeZero (p * ell) := ⟨hM.ne'⟩
  obtain ⟨L, _, K, hK, hS⟩ := corr3_rows p hp ell h3 (-σ) (a, b) (c, d)
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
  set rowsForm : Weight (p * ell) 3 := (L.map fun T => T.1 • crossForm (p * ell) hM
    (T.2.a * a + T.2.b * c) (T.2.a * b + T.2.b * d) (T.2.c * a + T.2.d * c)
    (T.2.c * b + T.2.d * d)).sum with hrows
  have hrows_mem : rowsForm ∈ upperGood p ell hl hM := by
    rw [hrows]
    have hall : ∀ L' : List (ℂ × Rows),
        (L'.map fun T => T.1 • crossForm (p * ell) hM
          (T.2.a * a + T.2.b * c) (T.2.a * b + T.2.b * d) (T.2.c * a + T.2.d * c)
          (T.2.c * b + T.2.d * d)).sum ∈ upperGood p ell hl hM := by
      intro L'
      induction L' with
      | nil => exact Submodule.zero_mem _
      | cons T L' ih =>
        rw [List.map_cons, List.sum_cons]
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ih
        exact cross_mem_upper hp hl hM
          (dvd_add (dvd_mul_of_dvd_right ha _) (dvd_mul_of_dvd_right hc _))
          (dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_right hd _))
          (dvd_add (dvd_mul_of_dvd_right ha _) (dvd_mul_of_dvd_right hc _))
          (dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_right hd _))
    exact hall L
  have hfib : ∀ τ, fibre3 p ell hM a b c d σ τ = corr3 p ell (-σ) (a, b) (c, d) τ := by
    intro τ
    unfold fibre3 corr3
    simp only [_root_.sum_apply, crossForm_apply]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
    congr 2 <;> ring
  set G : Weight (p * ell) 3 := fibre3 p ell hM a b c d σ - rowsForm with hG
  have hGv : ∀ τ, G τ = corr3 p ell (-σ) (a, b) (c, d) τ - rowSum3 (p * ell) (a, b) (c, d) L τ := by
    intro τ
    rw [hG, _root_.sub_apply, hfib, hrows, hrowv]
  obtain ⟨hK0, E, hE, hEv⟩ := hS
  have h3M : 3 ≤ p * ell := by nlinarith
  have h3K : 3 ≤ K := h3M.trans (Nat.le_of_dvd hK0 hK)
  have hres : AllWeightSeriesTrace.restrictionK (p * ell) K 3 hK G = E := by
    apply _root_.ModularForm.ext
    intro τ
    rw [AllWeightSeriesTrace.restrictionK_apply, hGv, hEv]
  have hmemK : AllWeightSeriesTrace.restrictionK (p * ell) K 3 hK G ∈
      AllWeightSeriesTrace.seriesSpanK K h3K 3 le_rfl := by
    rw [hres, ← classSeriesSpan_eq_seriesSpanK K h3K]
    exact hE
  obtain ⟨g, hg, hge⟩ := AllWeightSeriesTrace.invariant_seriesK_descent K (p * ell) h3M hK0 hK 3
    le_rfl (AllWeightSeriesTrace.restrictionK (p * ell) K 3 hK G) hmemK
    (fun γ hγ => G.slash_action_eq' γ hγ)
  have hgG : g = G := AllWeightSeriesTrace.restrictionK_injective (p * ell) K 3 hK hge
  have hGmem : G ∈ upperGood p ell hl hM := by
    apply classSeries_le_upper hl hM
    rw [classSeriesSpan_eq_seriesSpanK (p * ell) h3M, ← hgG]
    exact hg
  have hsplit : fibre3 p ell hM a b c d σ = G + rowsForm := by rw [hG]; abel
  rw [hsplit]
  exact Submodule.add_mem _ hGmem hrows_mem

/-! ### The orbit sums -/

variable (p N : ℕ) [Fact p.Prime]

theorem val_mul_dvd (s x : ZMod p) :
    (p : ℤ) ∣ ((s * x).val : ℤ) - (s.val : ℤ) * (x.val : ℤ) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [ZMod.val_mul, Int.natCast_mod]
  push_cast
  exact (Int.mod_modEq _ _).symm.dvd

/-- Rank zero. -/
theorem rank_zero_mem (h3 : 3 ≤ N) (hM : 0 < p * N) (A B : Point N) :
    crossPoint (p * N) hM (splitPoint p N A 0) (splitPoint p N B 0) ∈
      upperGood p N (by omega) hM := by
  rw [crossPoint_split]
  simp only [Prod.fst_zero, Prod.snd_zero, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero]
  exact cross_mem_upper (Fact.out : p.Prime).pos (by omega) hM (dvd_mul_right _ _)
    (dvd_mul_right _ _) (dvd_mul_right _ _) (dvd_mul_right _ _)

/-- The full sum over `U` with `T = 0`. -/
theorem first_zero_full (h3 : 3 ≤ N) (hM : 0 < p * N) (A B : Point N) :
    (∑ U : Point p, crossPoint (p * N) hM (splitPoint p N A 0) (splitPoint p N B U)) =
      (p : ℂ) • crossForm (p * N) hM ((p : ℤ) * A.1.val) ((p : ℤ) * A.2.val)
        ((p : ℤ) * ((p : ℤ) * B.1.val)) ((p : ℤ) * ((p : ℤ) * B.2.val)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hN : 0 < N := by omega
  have : NeZero p := ⟨hp.ne'⟩
  have : NeZero N := ⟨hN.ne'⟩
  simp_rw [crossPoint_split]
  simp only [Prod.fst_zero, Prod.snd_zero, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero]
  rw [sum_point_forms p (p * N) (fun u v => crossForm (p * N) hM ((p : ℤ) * A.1.val)
    ((p : ℤ) * A.2.val) ((p : ℤ) * B.1.val + (N : ℤ) * u) ((p : ℤ) * B.2.val + (N : ℤ) * v))]
  apply DFunLike.ext
  intro τ
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, crossForm_apply]
  simp_rw [← Finset.mul_sum]
  rw [lam_sum (n := p) (N := N) hp hN, TorsionMuDistributionNat.xValue_scale hp N,
    lambdaValue_scale hp N hN]
  ring

theorem first_zero_mem (h3 : 3 ≤ N) (hM : 0 < p * N) (A B : Point N) :
    (∑ U : {U : Point p // U ≠ 0},
      crossPoint (p * N) hM (splitPoint p N A 0) (splitPoint p N B U.val)) ∈
      upperGood p N (by omega) hM := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsum := Fintype.sum_eq_add_sum_subtype_ne
    (fun U : Point p => crossPoint (p * N) hM (splitPoint p N A 0) (splitPoint p N B U)) 0
  rw [first_zero_full p N h3 hM] at hsum
  have he : (∑ U : {U : Point p // U ≠ 0},
      crossPoint (p * N) hM (splitPoint p N A 0) (splitPoint p N B U.val)) =
      (p : ℂ) • crossForm (p * N) hM ((p : ℤ) * A.1.val) ((p : ℤ) * A.2.val)
        ((p : ℤ) * ((p : ℤ) * B.1.val)) ((p : ℤ) * ((p : ℤ) * B.2.val)) -
      crossPoint (p * N) hM (splitPoint p N A 0) (splitPoint p N B 0) := by
    rw [hsum]; abel
  rw [he]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (cross_mem_upper hp (by omega) hM
    (dvd_mul_right _ _) (dvd_mul_right _ _) (dvd_mul_right _ _) (dvd_mul_right _ _)))
    (rank_zero_mem p N h3 hM A B)

/-- The full slope-`s` sum. -/
theorem slope_full_eq (hM : 0 < p * N) (s : ZMod p) (A B : Point N) :
    (∑ T : Point p, crossPoint (p * N) hM (splitPoint p N A T)
        (splitPoint p N B (CoprimeProductTrace.scale s T))) =
      fibre3 p N hM ((p : ℤ) * A.1.val) ((p : ℤ) * A.2.val) ((p : ℤ) * B.1.val)
        ((p : ℤ) * B.2.val) (s.val : ℤ) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hterm : ∀ T : Point p, crossPoint (p * N) hM (splitPoint p N A T)
      (splitPoint p N B (CoprimeProductTrace.scale s T)) =
      crossForm (p * N) hM ((p : ℤ) * A.1.val + (N : ℤ) * (T.1.val : ℤ))
        ((p : ℤ) * A.2.val + (N : ℤ) * (T.2.val : ℤ))
        ((p : ℤ) * B.1.val + (N : ℤ) * ((s.val : ℤ) * (T.1.val : ℤ)))
        ((p : ℤ) * B.2.val + (N : ℤ) * ((s.val : ℤ) * (T.2.val : ℤ))) := by
    intro T
    rw [crossPoint_split]
    apply crossForm_congr (U := (_, _)) (V := (_, _)) (U' := (_, _)) (V' := (_, _)) hM
    · exact ⟨by simp, by simp⟩
    · have h1 := val_mul_dvd p s T.1
      have h2 := val_mul_dvd p s T.2
      refine ⟨?_, ?_⟩
      · change ((p * N : ℕ) : ℤ) ∣ ((p : ℤ) * B.1.val + (N : ℤ) * ((s * T.1).val : ℤ)) -
          ((p : ℤ) * B.1.val + (N : ℤ) * ((s.val : ℤ) * (T.1.val : ℤ)))
        rw [show ((p : ℤ) * B.1.val + (N : ℤ) * ((s * T.1).val : ℤ)) -
          ((p : ℤ) * B.1.val + (N : ℤ) * ((s.val : ℤ) * (T.1.val : ℤ))) =
          (N : ℤ) * (((s * T.1).val : ℤ) - (s.val : ℤ) * (T.1.val : ℤ)) by ring]
        push_cast
        rw [mul_comm (p : ℤ)]
        exact mul_dvd_mul_left _ h1
      · change ((p * N : ℕ) : ℤ) ∣ ((p : ℤ) * B.2.val + (N : ℤ) * ((s * T.2).val : ℤ)) -
          ((p : ℤ) * B.2.val + (N : ℤ) * ((s.val : ℤ) * (T.2.val : ℤ)))
        rw [show ((p : ℤ) * B.2.val + (N : ℤ) * ((s * T.2).val : ℤ)) -
          ((p : ℤ) * B.2.val + (N : ℤ) * ((s.val : ℤ) * (T.2.val : ℤ))) =
          (N : ℤ) * (((s * T.2).val : ℤ) - (s.val : ℤ) * (T.2.val : ℤ)) by ring]
        push_cast
        rw [mul_comm (p : ℤ)]
        exact mul_dvd_mul_left _ h2
  simp_rw [hterm]
  rw [sum_point_forms p (p * N) (fun u v => crossForm (p * N) hM ((p : ℤ) * A.1.val + (N : ℤ) * u)
    ((p : ℤ) * A.2.val + (N : ℤ) * v) ((p : ℤ) * B.1.val + (N : ℤ) * ((s.val : ℤ) * u))
    ((p : ℤ) * B.2.val + (N : ℤ) * ((s.val : ℤ) * v)))]
  rfl

/-- The rank-one orbit sum. -/
def rankOneSum (hM : 0 < p * N) (s : ZMod p) (A B : Point N) : Weight (p * N) 3 :=
  ∑ T : {T : Point p // T ≠ 0}, crossPoint (p * N) hM (splitPoint p N A T.val)
    (splitPoint p N B (CoprimeProductTrace.scale s T.val))

theorem rankOneSum_mem (h3 : 3 ≤ N) (hM : 0 < p * N) (s : ZMod p) (A B : Point N) :
    rankOneSum p N hM s A B ∈ upperGood p N (by omega) hM := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsum := Fintype.sum_eq_add_sum_subtype_ne
    (fun T : Point p => crossPoint (p * N) hM (splitPoint p N A T)
      (splitPoint p N B (CoprimeProductTrace.scale s T))) 0
  have hs0 : CoprimeProductTrace.scale s (0 : Point p) = 0 := by
    simp [CoprimeProductTrace.scale]
  rw [hs0, slope_full_eq p N hM s A B] at hsum
  have he : rankOneSum p N hM s A B = fibre3 p N hM ((p : ℤ) * A.1.val) ((p : ℤ) * A.2.val)
      ((p : ℤ) * B.1.val) ((p : ℤ) * B.2.val) (s.val : ℤ) -
      crossPoint (p * N) hM (splitPoint p N A 0) (splitPoint p N B 0) := by
    rw [rankOneSum, hsum]; abel
  rw [he]
  exact Submodule.sub_mem _ (fibre3_mem_of_div p N hp h3 (by omega) hM _ _ _ _ _
    (dvd_mul_right _ _) (dvd_mul_right _ _) (dvd_mul_right _ _) (dvd_mul_right _ _))
    (rank_zero_mem p N h3 hM A B)

/-! ### Rank two: Fourier reduction of the second factor -/

/-- The `x`-value at a split label. -/
def splitX (τ : ℍ) (A : Point N) (T : Point p) : ℂ := xPoint (p * N) τ (splitPoint p N A T)

omit [Fact p.Prime] in
theorem crossPoint_split_apply (hM : 0 < p * N) (A B : Point N) (T U : Point p) (τ : ℍ) :
    crossPoint (p * N) hM (splitPoint p N A T) (splitPoint p N B U) τ =
      splitX p N τ A T * CoprimeProductTrace.splitLambda p N τ B U := by
  rw [crossPoint_apply]
  rfl

theorem det_orbit_value [NeZero N] (hcop : Nat.Coprime p N) (τ : ℍ) (d : ZMod p) (A B : Point N) :
    (∑ D : DeterminantPairs p d, splitX p N τ A D.1.val *
        CoprimeProductTrace.splitLambda p N τ B D.2.val) =
      -(1 / (N : ℂ)) * ∑ C : Point N, pairing N (CoprimeProductTrace.scale (p : ZMod N) C) B *
        ∑ s : ZMod p, phase p (-(N : ZMod p) * d * s) *
          ∑ T : {T : Point p // T ≠ 0}, splitX p N τ A T.val *
            CoprimeProductTrace.splitLambda p N τ C (CoprimeProductTrace.scale s T.val) := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have he : (N : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime N p).mpr hcop.symm).ne_zero
  have hfirst : (∑ D : DeterminantPairs p d, splitX p N τ A D.1.val *
      CoprimeProductTrace.splitLambda p N τ B D.2.val) = -(1 / ((p * N : ℕ) : ℂ)) *
      ∑ C : Point N, pairing N (CoprimeProductTrace.scale (p : ZMod N) C) B *
        ∑ D : DeterminantPairs p d, splitX p N τ A D.1.val *
          ∑ V : Point p, CoprimeProductTrace.splitLambda p N τ C V *
            pairing p (CoprimeProductTrace.scale (N : ZMod p) V) D.2.val := by
    simp_rw [split_lambda_fourier p N hcop τ B, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro C _
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro V _
    ring
  have hpair (C : Point N) :
      (∑ D : DeterminantPairs p d, splitX p N τ A D.1.val *
        ∑ V : Point p, CoprimeProductTrace.splitLambda p N τ C V *
          pairing p (CoprimeProductTrace.scale (N : ZMod p) V) D.2.val) =
      ∑ s : ZMod p, (p : ℂ) * phase p (-(N : ZMod p) * d * s) *
        ∑ T : {T : Point p // T ≠ 0}, splitX p N τ A T.val *
          CoprimeProductTrace.splitLambda p N τ C (CoprimeProductTrace.scale s T.val) := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum]
    exact determinant_pair_reduction p (N : ZMod p) he d (splitX p N τ A)
      (CoprimeProductTrace.splitLambda p N τ C)
  rw [hfirst]
  simp_rw [hpair, mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro s _
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

/-- The rank-two orbit sum. -/
def rankTwoSum (hM : 0 < p * N) (d : ZMod p) (A B : Point N) : Weight (p * N) 3 :=
  ∑ D : DeterminantPairs p d, crossPoint (p * N) hM (splitPoint p N A D.1.val)
    (splitPoint p N B D.2.val)

theorem rankTwoSum_eq [NeZero N] (hcop : Nat.Coprime p N) (hM : 0 < p * N) (d : ZMod p)
    (A B : Point N) :
    rankTwoSum p N hM d A B = -(1 / (N : ℂ)) • ∑ C : Point N,
      pairing N (CoprimeProductTrace.scale (p : ZMod N) C) B •
        ∑ s : ZMod p, phase p (-(N : ZMod p) * d * s) • rankOneSum p N hM s A C := by
  apply DFunLike.ext
  intro τ
  simp only [rankTwoSum, rankOneSum, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    crossPoint_split_apply]
  exact det_orbit_value p N hcop τ d A B

theorem rankTwoSum_mem [NeZero N] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N) (hM : 0 < p * N)
    (d : ZMod p) (A B : Point N) :
    rankTwoSum p N hM d A B ∈ upperGood p N (by omega) hM := by
  rw [rankTwoSum_eq p N hcop hM d A B]
  apply Submodule.smul_mem
  refine Submodule.sum_mem _ fun C _ => Submodule.smul_mem _ _ ?_
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (rankOneSum_mem p N h3 hM s A C)

/-! ### Orbit averaging in each rank -/

theorem trace_rank_zero [NeZero N] (h3 : 3 ≤ N) (hM : 0 < p * N) (A B : Point N) :
    normalizedTrace3 N (p * N) hM
        (crossPoint (p * N) hM (splitPoint p N A 0) (splitPoint p N B 0)) ∈
      target p N (by omega) hM :=
  trace_upperGood _ hM (rank_zero_mem p N h3 hM A B)

theorem trace_first_zero [NeZero N] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N) (hM : 0 < p * N)
    (A B : Point N) (U0 : Point p) (hU0 : U0 ≠ 0) :
    normalizedTrace3 N (p * N) hM
        (crossPoint (p * N) hM (splitPoint p N A 0) (splitPoint p N B U0)) ∈
      target p N (by omega) hM := by
  classical
  apply trace_mem_of_orbit (⟨U0, hU0⟩ : {U : Point p // U ≠ 0}) hM _
    (fun U => crossPoint (p * N) hM (splitPoint p N A 0) (splitPoint p N B U.val))
  · exact trace_upperGood _ hM (first_zero_mem p N h3 hM A B)
  · intro U
    obtain ⟨G, hG⟩ := DivisionEisensteinLowerClosure.exists_SL2_nonzero_row_move
      U0.1 U0.2 U.val.1 U.val.2 (nonzero_components U0 hU0) (nonzero_components U.val U.property)
    have h0 : ![(0 : Point p).1, (0 : Point p).2] ᵥ* G.1 = ![(0 : Point p).1, (0 : Point p).2] := by
      ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    obtain ⟨γ, hγ, hP, hQ⟩ := exists_Gamma_split_pair_move p N hcop A B 0 U0 0 U.val G h0 hG
    have hc := trace_crossPoint_action N (p * N) hM (splitPoint p N A 0) (splitPoint p N B U0) γ hγ
    rw [hP, hQ] at hc
    exact hc

theorem trace_rank_one [NeZero N] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N) (hM : 0 < p * N)
    (A B : Point N) (T0 : Point p) (hT0 : T0 ≠ 0) (s : ZMod p) :
    normalizedTrace3 N (p * N) hM (crossPoint (p * N) hM (splitPoint p N A T0)
        (splitPoint p N B (CoprimeProductTrace.scale s T0))) ∈ target p N (by omega) hM := by
  classical
  apply trace_mem_of_orbit (⟨T0, hT0⟩ : {T : Point p // T ≠ 0}) hM _
    (fun T => crossPoint (p * N) hM (splitPoint p N A T.val)
      (splitPoint p N B (CoprimeProductTrace.scale s T.val)))
  · exact trace_upperGood _ hM (rankOneSum_mem p N h3 hM s A B)
  · intro T
    obtain ⟨G, hG⟩ := DivisionEisensteinLowerClosure.exists_SL2_nonzero_row_move
      T0.1 T0.2 T.val.1 T.val.2 (nonzero_components T0 hT0) (nonzero_components T.val T.property)
    have hs : ![(CoprimeProductTrace.scale s T0).1, (CoprimeProductTrace.scale s T0).2] ᵥ* G.1 =
        ![(CoprimeProductTrace.scale s T.val).1, (CoprimeProductTrace.scale s T.val).2] := by
      have hv (P : Point p) : ![(CoprimeProductTrace.scale s P).1, (CoprimeProductTrace.scale s P).2] =
          s • (![P.1, P.2] : Fin 2 → ZMod p) := by
        ext i; fin_cases i <;> rfl
      rw [hv, hv, Matrix.smul_vecMul, hG]
    obtain ⟨γ, hγ, hP, hQ⟩ := exists_Gamma_split_pair_move p N hcop A B
      T0 (CoprimeProductTrace.scale s T0) T.val (CoprimeProductTrace.scale s T.val) G hG hs
    rw [← hP, ← hQ]
    exact trace_crossPoint_action N (p * N) hM _ _ γ hγ

theorem trace_rank_two [NeZero N] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N) (hM : 0 < p * N)
    (A B : Point N) (T0 U0 : Point p) (d : ZMod p) (hd : d ≠ 0) (hTU : det T0 U0 = d) :
    normalizedTrace3 N (p * N) hM
        (crossPoint (p * N) hM (splitPoint p N A T0) (splitPoint p N B U0)) ∈
      target p N (by omega) hM := by
  classical
  have hT0 : T0 ≠ 0 := by
    intro hz
    rw [hz] at hTU
    have hz0 : det (0 : Point p) U0 = 0 := by simp [det]
    exact hd (hTU.symm.trans hz0)
  apply trace_mem_of_orbit (⟨⟨T0, hT0⟩, ⟨U0, hTU⟩⟩ : DeterminantPairs p d) hM _
    (fun D => crossPoint (p * N) hM (splitPoint p N A D.1.val) (splitPoint p N B D.2.val))
  · exact trace_upperGood _ hM (rankTwoSum_mem p N h3 hcop hM d A B)
  · intro D
    obtain ⟨G, hG0, hG1⟩ := exists_SL2_determinant_pair_move T0 U0 D.1.val D.2.val d hd hTU
      D.2.property
    obtain ⟨γ, hγ, hP, hQ⟩ := exists_Gamma_split_pair_move p N hcop A B T0 U0 D.1.val D.2.val G
      hG0 hG1
    rw [← hP, ← hQ]
    exact trace_crossPoint_action N (p * N) hM _ _ γ hγ

/-! ### Assembly -/

theorem trace_split_mem [NeZero N] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N) (hM : 0 < p * N)
    (A B : Point N) (T U : Point p) :
    normalizedTrace3 N (p * N) hM
        (crossPoint (p * N) hM (splitPoint p N A T) (splitPoint p N B U)) ∈
      target p N (by omega) hM := by
  by_cases hT : T = 0
  · subst hT
    by_cases hU : U = 0
    · subst hU
      exact trace_rank_zero p N h3 hM A B
    · exact trace_first_zero p N h3 hcop hM A B U hU
  · by_cases hd : det T U = 0
    · have hu := (determinant_kernel T hT U).mp hd
      generalize coordinate T U = s at hu
      rw [hu]
      exact trace_rank_one p N h3 hcop hM A B T hT s
    · exact trace_rank_two p N h3 hcop hM A B T U (det T U) hd rfl

/-- **Coprime-prime mixed trace**, target form: for `p` prime coprime to `ℓ ≥ 3`, all integer
labels. -/
theorem trace_cross_coprime_target (h3 : 3 ≤ N) (hcop : Nat.Coprime p N) (a b c d : ℤ) :
    normalizedTrace3 N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (crossForm (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) a b c d) ∈
      target p N (by omega) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : NeZero N := ⟨by omega⟩
  set hM := Nat.mul_pos (Fact.out : p.Prime).pos (show 0 < N by omega)
  rw [← crossPoint_label (p * N) hM a b c d]
  obtain ⟨⟨A, T⟩, hP⟩ := (splitPointEquiv p N hcop).surjective (label (p * N) a b)
  obtain ⟨⟨B, U⟩, hQ⟩ := (splitPointEquiv p N hcop).surjective (label (p * N) c d)
  rw [← hP, ← hQ]
  exact trace_split_mem p N h3 hcop hM A B T U

/-- **Coprime-prime mixed trace**: lower mixed forms plus lower class series. -/
theorem trace_cross_coprime_lower (h3 : 3 ≤ N) (hcop : Nat.Coprime p N) (a b c d : ℤ) :
    normalizedTrace3 N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (crossForm (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) a b c d) ∈
      lowerMixedSpan N (by omega) ⊔ classSeriesSpan N (by omega) :=
  target_le p N h3 _ (trace_cross_coprime_target p N h3 hcop a b c d)

/-- **Coprime-prime mixed trace**: in the degree-three product span. -/
theorem trace_cross_coprime_mem (h3 : 3 ≤ N) (hcop : Nat.Coprime p N) (a b c d : ℤ) :
    normalizedTrace3 N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
        (crossForm (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) a b c d) ∈
      degreeThreeProductSpan N (by omega) :=
  target_le_degreeThree p N h3 _ (trace_cross_coprime_target p N h3 hcop a b c d)

end ZInQ.Contrib.HeckePrimeRationality.MixedCoprimeTrace
