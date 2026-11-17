import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionWeierstrassData
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaG2Identity
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable

/-!
# Actual weight-two Eisenstein row sums and Weierstrass division values

The weight-two level-one series is the actual symmetric-row `G2`.
The lattice differences are absolutely summable; individual inverse-square
lattice sums are not rearranged as absolutely summable two-dimensional sums.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open Complex EisensteinSeries Filter
open scoped Topology Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.EisensteinWeightTwo

open ZInQ.Contrib.HeckePrimeRationality

lemma eisSummand_two (τ : _root_.UpperHalfPlane) (m n : _root_.Int) :
    _root_.EisensteinSeries.eisSummand 2 ![m, n] τ =
      1 / ((m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2 := by
  simp [EisensteinSeries.eisSummand, zpow_ofNat]

/-- The valid one-dimensional weight-two row expansion. -/
theorem e2Summand_pos_q (τ : _root_.UpperHalfPlane) (m : _root_.Nat) :
    _root_.EisensteinSeries.e2Summand ((m + 1 : ℕ) : ℤ) τ =
      (-4 * (Real.pi : ℂ) ^ 2) * ∑' n : ℕ+,
        (n : ℂ) * cexp (2 * (Real.pi : ℂ) * I * (τ : ℂ)) ^ ((m + 1) * (n : ℕ)) := by
  let t : ℍ := ⟨((m + 1 : ℕ) : ℂ) * (τ : ℂ), by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by positivity) τ.im_pos⟩
  have h := EisensteinSeries.qExpansion_identity_pnat (k := 1) (by norm_num) t
  have hc : (-2 * (Real.pi : ℂ) * I) ^ (1 + 1) / (1 : ℕ).factorial =
      -4 * (Real.pi : ℂ) ^ 2 := by
    norm_num [mul_pow, I_sq]
  have he : cexp (2 * (Real.pi : ℂ) * I * (t : ℂ)) =
      cexp (2 * (Real.pi : ℂ) * I * (τ : ℂ)) ^ (m + 1) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [t]
    push_cast
    ring
  rw [hc, he] at h
  simpa only [EisensteinSeries.e2Summand, eisSummand_two, t, UpperHalfPlane.coe_mk,
    Int.cast_natCast, pow_one, ← pow_mul] using h

set_option maxHeartbeats 1200000 in
/-- The outer rows are ordinarily summable; this is proved from a convergent q double sum. -/
theorem summable_e2Rows (τ : _root_.UpperHalfPlane) :
    Summable (fun m : ℤ => _root_.EisensteinSeries.e2Summand m τ) := by
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hp : Summable (fun m : ℕ+ => ∑' n : ℕ+, (n : ℂ) *
      cexp (2 * (Real.pi : ℂ) * I * (τ : ℂ)) ^ ((m : ℕ) * (n : ℕ))) := by
    simpa only [pow_one] using (summable_prod_mul_pow 1 hq).prod
  have hs : Summable (fun m : ℕ => ∑' n : ℕ+, (n : ℂ) *
      cexp (2 * (Real.pi : ℂ) * I * (τ : ℂ)) ^ ((m + 1) * (n : ℕ))) :=
    (summable_pnat_iff_summable_succ (f := fun m : ℕ => ∑' n : ℕ+, (n : ℂ) *
      cexp (2 * (Real.pi : ℂ) * I * (τ : ℂ)) ^ (m * (n : ℕ)))).mp hp
  have hpos : Summable (fun m : ℕ => EisensteinSeries.e2Summand ((m + 1 : ℕ) : ℤ) τ) := by
    simpa only [e2Summand_pos_q] using hs.mul_left (-4 * (Real.pi : ℂ) ^ 2)
  have hnat : Summable (fun m : ℕ => EisensteinSeries.e2Summand (m : ℤ) τ) :=
    (summable_nat_add_iff 1 (f := fun m : ℕ => EisensteinSeries.e2Summand (m : ℤ) τ)).mp hpos
  exact Summable.of_nat_of_neg hnat (hnat.congr fun m => (EisensteinSeries.e2Summand_even τ (m : ℤ)).symm)

/-- The actual symmetric definition of `G2` agrees with ordinary summation of its rows. -/
theorem G2_eq_tsum_rows (τ : _root_.UpperHalfPlane) :
    _root_.EisensteinSeries.G2 τ = ∑' m : ℤ, _root_.EisensteinSeries.e2Summand m τ := by
  exact tsum_eq_of_summable_unconditional (L := SummationFilter.symmetricIcc ℤ) (summable_e2Rows τ)

/-- Coordinates on the actual lattice, with the row coordinate first. -/
def gridEquiv (τ : _root_.UpperHalfPlane) : ℤ × ℤ ≃ (ThetaWeierstrass.periodPair τ).lattice :=
  (Equiv.prodComm ℤ ℤ).trans (ThetaWeierstrass.periodPair τ).latticeEquivProd.toEquiv.symm

lemma gridEquiv_coe (τ : _root_.UpperHalfPlane) (p : ℤ × ℤ) :
    (gridEquiv τ p : ℂ) = (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ) := by
  change ((ThetaWeierstrass.periodPair τ).latticeEquivProd.symm (p.2, p.1) : ℂ) = _
  rw [PeriodPair.latticeEquiv_symm_apply]
  simp only [ThetaWeierstrass.periodPair, mul_one]
  ring

/-- An actual inverse-square lattice difference with its summable counterterm. -/
def latticeDifference (τ : _root_.UpperHalfPlane) (z : _root_.Complex) (p : ℤ × ℤ) : ℂ :=
  1 / (z + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) ^ 2 -
    1 / ((p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) ^ 2

/-- Reindexing the actual absolutely convergent Weierstrass sum. -/
theorem hasSum_latticeDifference (τ : _root_.UpperHalfPlane) (z : _root_.Complex) :
    HasSum (latticeDifference τ z) ((ThetaWeierstrass.periodPair τ).weierstrassP z) := by
  have h := (ThetaWeierstrass.periodPair τ).hasSum_weierstrassP (-z)
  rw [PeriodPair.weierstrassP_neg] at h
  have hg := (gridEquiv τ).hasSum_iff.mpr h
  refine hg.congr_fun ?_
  intro p
  simp only [Function.comp_apply, gridEquiv_coe, latticeDifference]
  rw [show -z - ((p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) =
      -(z + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) by ring, neg_sq]

theorem summable_shifted_row (τ : _root_.UpperHalfPlane) (z : _root_.Complex) (m : _root_.Int) :
    Summable (fun n : ℤ => 1 / (z + (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2) := by
  have hd := (hasSum_latticeDifference τ z).summable.prod_factor m
  have hb : Summable (fun n : ℤ => 1 / ((m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2) := by
    simpa only [eisSummand_two] using EisensteinSeries.e2Summand_summable m τ
  exact (hd.add hb).congr fun n => by simp [latticeDifference]

lemma shifted_row_eq (τ : _root_.UpperHalfPlane) (z : _root_.Complex) (m : _root_.Int) :
    (∑' n : ℤ, 1 / (z + (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2) =
      (∑' n : ℤ, latticeDifference τ z (m, n)) + EisensteinSeries.e2Summand m τ := by
  have hd := (hasSum_latticeDifference τ z).summable.prod_factor m
  have hb : Summable (fun n : ℤ => 1 / ((m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2) := by
    simpa only [eisSummand_two] using EisensteinSeries.e2Summand_summable m τ
  rw [EisensteinSeries.e2Summand]
  simp only [eisSummand_two]
  rw [← hd.tsum_add hb]
  exact tsum_congr fun n => by simp [latticeDifference]

/-- Summability of the shifted rows, without falsely asserting summability of the raw lattice sum. -/
theorem summable_shifted_rows (τ : _root_.UpperHalfPlane) (z : _root_.Complex) :
    Summable (fun m : ℤ => ∑' n : ℤ, 1 / (z + (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2) := by
  have hd := (hasSum_latticeDifference τ z).summable.prod
  exact (hd.add (summable_e2Rows τ)).congr fun m => (shifted_row_eq τ z m).symm

/-- The iterated row sum of the actual shifted inverse squares is `℘(z) + G2(τ)`. -/
theorem hasSum_shifted_rows (τ : _root_.UpperHalfPlane) (z : _root_.Complex) :
    HasSum (fun m : ℤ => ∑' n : ℤ, 1 / (z + (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2)
      ((ThetaWeierstrass.periodPair τ).weierstrassP z + EisensteinSeries.G2 τ) := by
  have hd := hasSum_latticeDifference τ z
  have hdp : HasSum (fun m : ℤ => ∑' n : ℤ, latticeDifference τ z (m, n))
      ((ThetaWeierstrass.periodPair τ).weierstrassP z) := by
    apply hd.summable.prod.hasSum_iff.mpr
    rw [← hd.summable.tsum_prod, hd.tsum_eq]
  have hb : HasSum (fun m : ℤ => EisensteinSeries.e2Summand m τ) (EisensteinSeries.G2 τ) := by
    apply (summable_e2Rows τ).hasSum_iff.mpr
    exact (G2_eq_tsum_rows τ).symm
  exact (hdp.add hb).congr_fun fun m => shifted_row_eq τ z m

/-- No shifted denominator vanishes away from the actual lattice. -/
theorem shifted_denominator_ne_zero (τ : _root_.UpperHalfPlane) (z : _root_.Complex)
    (hz : z ∉ (ThetaWeierstrass.periodPair τ).lattice) (m n : _root_.Int) :
    z + (m : ℂ) * (τ : ℂ) + (n : ℂ) ≠ 0 := by
  intro h
  apply hz
  rw [ThetaWeierstrass.mem_periodPair_lattice_iff]
  refine ⟨-n, -m, ?_⟩
  push_cast
  linear_combination h

/-- Classical off-lattice convergence and nonzero denominators are both proved. -/
theorem off_lattice_row_convergence (τ : _root_.UpperHalfPlane) (z : _root_.Complex)
    (hz : z ∉ (ThetaWeierstrass.periodPair τ).lattice) :
    (∀ m n : ℤ, z + (m : ℂ) * (τ : ℂ) + (n : ℂ) ≠ 0) ∧
      HasSum (fun m : ℤ => ∑' n : ℤ, 1 / (z + (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2)
        ((ThetaWeierstrass.periodPair τ).weierstrassP z + EisensteinSeries.G2 τ) :=
  ⟨shifted_denominator_ne_zero τ z hz, hasSum_shifted_rows τ z⟩

/-- The classical off-lattice statement for the actual Weierstrass and weight-two Eisenstein functions. -/
theorem weierstrassP_add_G2_eq_rowSum (τ : _root_.UpperHalfPlane) (z : _root_.Complex)
    (hz : z ∉ (ThetaWeierstrass.periodPair τ).lattice) :
    (ThetaWeierstrass.periodPair τ).weierstrassP z + EisensteinSeries.G2 τ =
      ∑' m : ℤ, ∑' n : ℤ, 1 / (z + (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2 := by
  exact (off_lattice_row_convergence τ z hz).2.tsum_eq.symm

/-! ## Translated congruence classes and principal lifts -/

/-- The actual inverse-square summand on a translated congruence class. -/
def congruenceTerm (N : _root_.Nat) (a b : _root_.Int) (τ : _root_.UpperHalfPlane)
    (p : ℤ × ℤ) : ℂ :=
  EisensteinSeries.eisSummand 2 ![a + N * p.1, b + N * p.2] τ

/-- A degree-zero congruence-class difference, defined independently by lattice summands. -/
def congruenceDifference (N : _root_.Nat) (a b : _root_.Int) (τ : _root_.UpperHalfPlane)
    (p : ℤ × ℤ) : ℂ :=
  congruenceTerm N a b τ p - congruenceTerm N 0 0 τ p

lemma torsion_shifted_term (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) (m n : _root_.Int) :
    1 / (CompletedTheta.torsionPoint N a b τ + (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2 =
      (N : ℂ) ^ 2 * congruenceTerm N a b τ (m, n) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have heq : CompletedTheta.torsionPoint N a b τ + (m : ℂ) * (τ : ℂ) + (n : ℂ) =
      ((((a + N * m : ℤ) : ℂ) * (τ : ℂ) + ((b + N * n : ℤ) : ℂ)) / (N : ℂ)) := by
    unfold CompletedTheta.torsionPoint
    push_cast
    field_simp
    ring
  rw [heq, congruenceTerm, eisSummand_two, div_pow, one_div, inv_div]
  ring

lemma torsion_latticeDifference (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) (p : ℤ × ℤ) :
    latticeDifference τ (CompletedTheta.torsionPoint N a b τ) p =
      (N : ℂ) ^ 2 * congruenceDifference N a b τ p := by
  have h0 := torsion_shifted_term N hN 0 0 τ p.1 p.2
  simp only [CompletedTheta.torsionPoint, Int.cast_zero, zero_mul, add_zero, zero_div,
    zero_add] at h0
  rw [latticeDifference, torsion_shifted_term N hN a b τ, h0, congruenceDifference]
  ring

/-- The weight-two congruence difference is genuinely absolutely summable on the whole grid. -/
theorem hasSum_congruenceDifference (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) :
    HasSum (congruenceDifference N a b τ)
      ((ThetaWeierstrass.periodPair τ).weierstrassP (CompletedTheta.torsionPoint N a b τ) /
        (N : ℂ) ^ 2) := by
  have hNc : (N : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')
  refine ((hasSum_latticeDifference τ (CompletedTheta.torsionPoint N a b τ)).div_const
    ((N : ℂ) ^ 2)).congr_fun ?_
  intro p
  rw [torsion_latticeDifference N hN a b τ]
  exact (mul_div_cancel_left₀ _ hNc).symm

/-- An independently defined, convergent weight-two lattice-series family. -/
def divisionEisenstein (N : _root_.Nat) (a b : _root_.Int) (τ : _root_.UpperHalfPlane) : ℂ :=
  (N : ℂ) ^ 2 * ∑' p : ℤ × ℤ, congruenceDifference N a b τ p

theorem divisionEisenstein_eq_weierstrassP (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) :
    divisionEisenstein N a b τ =
      (ThetaWeierstrass.periodPair τ).weierstrassP (CompletedTheta.torsionPoint N a b τ) := by
  have hNc : (N : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')
  rw [divisionEisenstein, (hasSum_congruenceDifference N hN a b τ).tsum_eq]
  exact mul_div_cancel₀ _ hNc

theorem torsionPoint_notMem_lattice (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    CompletedTheta.torsionPoint N a b τ ∉ (ThetaWeierstrass.periodPair τ).lattice := by
  intro h
  exact CompletedTheta.H_torsion_ne_zero N hN τ a b hg
    ((ThetaWeierstrass.H_zero_iff_mem_lattice τ _).mpr h)

/-- Identification with the actual supplied torsion value, not a redefinition of it. -/
theorem xValue_eq_divisionEisenstein (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    TorsionWeierstrassData.xValue N a b τ = divisionEisenstein N a b τ := by
  rw [TorsionWeierstrassData.xValue_of_good N a b τ hg,
    divisionEisenstein_eq_weierstrassP N hN]

theorem summable_congruence_row (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) (m : _root_.Int) :
    Summable (fun n : ℤ => congruenceTerm N a b τ (m, n)) := by
  have hNc : (N : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')
  refine ((summable_shifted_row τ (CompletedTheta.torsionPoint N a b τ) m).div_const
    ((N : ℂ) ^ 2)).congr ?_
  intro n
  rw [torsion_shifted_term N hN a b τ]
  exact mul_div_cancel_left₀ _ hNc

theorem summable_congruence_rows (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) :
    Summable (fun m : ℤ => ∑' n : ℤ, congruenceTerm N a b τ (m, n)) := by
  have hNc : (N : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')
  refine ((summable_shifted_rows τ (CompletedTheta.torsionPoint N a b τ)).div_const
    ((N : ℂ) ^ 2)).congr ?_
  intro m
  simp only [torsion_shifted_term N hN a b τ, tsum_mul_left]
  exact mul_div_cancel_left₀ _ hNc

/-- The exact torsion congruence-class row identity for the actual weight-two summand. -/
theorem xValue_add_G2_eq_congruence_rows (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    TorsionWeierstrassData.xValue N a b τ + EisensteinSeries.G2 τ =
      (N : ℂ) ^ 2 * ∑' m : ℤ, ∑' n : ℤ,
        EisensteinSeries.eisSummand 2 ![a + N * m, b + N * n] τ := by
  rw [TorsionWeierstrassData.xValue_of_good N a b τ hg,
    weierstrassP_add_G2_eq_rowSum τ _ (torsionPoint_notMem_lattice N hN a b τ hg)]
  simp only [torsion_shifted_term N hN a b τ, tsum_mul_left, congruenceTerm]

/-- The principal lift of `N(Pα) - N(P0)` gives an actual absolutely convergent weight-two series. -/
def principalLiftTerm (N : _root_.Nat) (a b : _root_.Int) (τ : _root_.UpperHalfPlane)
    (p : ℤ × ℤ) : ℂ :=
  (N + 1 : ℂ) / (CompletedTheta.torsionPoint N a b τ + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) ^ 2 -
    1 / ((N + 1 : ℂ) * CompletedTheta.torsionPoint N a b τ +
      (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) ^ 2 -
    (N : ℂ) / ((p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) ^ 2

lemma principalLiftTerm_eq (N : _root_.Nat) (a b : _root_.Int) (τ : _root_.UpperHalfPlane)
    (p : ℤ × ℤ) :
    principalLiftTerm N a b τ p =
      (N + 1 : ℂ) * latticeDifference τ (CompletedTheta.torsionPoint N a b τ) p -
        latticeDifference τ ((N + 1 : ℂ) * CompletedTheta.torsionPoint N a b τ) p := by
  unfold principalLiftTerm latticeDifference
  ring

lemma torsionPoint_mul_level (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) :
    (N + 1 : ℂ) * CompletedTheta.torsionPoint N a b τ =
      CompletedTheta.torsionPoint N a b τ + (a : ℂ) * (τ : ℂ) + (b : ℂ) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold CompletedTheta.torsionPoint
  field_simp
  ring

theorem hasSum_principalLiftTerm (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) :
    HasSum (principalLiftTerm N a b τ)
      ((N : ℂ) * (ThetaWeierstrass.periodPair τ).weierstrassP (CompletedTheta.torsionPoint N a b τ)) := by
  have h := ((hasSum_latticeDifference τ (CompletedTheta.torsionPoint N a b τ)).mul_left
    (N + 1 : ℂ)).sub (hasSum_latticeDifference τ ((N + 1 : ℂ) * CompletedTheta.torsionPoint N a b τ))
  have hl : (a : ℂ) * (τ : ℂ) + (b : ℂ) ∈ (ThetaWeierstrass.periodPair τ).lattice := by
    rw [ThetaWeierstrass.mem_periodPair_lattice_iff]
    exact ⟨b, a, by ring⟩
  rw [torsionPoint_mul_level N hN a b τ,
    show CompletedTheta.torsionPoint N a b τ + (a : ℂ) * (τ : ℂ) + (b : ℂ) =
      CompletedTheta.torsionPoint N a b τ + ((a : ℂ) * (τ : ℂ) + (b : ℂ)) by ring,
    (ThetaWeierstrass.periodPair τ).weierstrassP_add_coe _ ⟨_, hl⟩] at h
  have hvalue : (N + 1 : ℂ) * (ThetaWeierstrass.periodPair τ).weierstrassP
      (CompletedTheta.torsionPoint N a b τ) -
      (ThetaWeierstrass.periodPair τ).weierstrassP (CompletedTheta.torsionPoint N a b τ) =
      (N : ℂ) * (ThetaWeierstrass.periodPair τ).weierstrassP (CompletedTheta.torsionPoint N a b τ) := by ring
  rw [hvalue] at h
  refine h.congr_fun fun p => ?_
  simpa only [torsionPoint_mul_level N hN a b τ,
    show CompletedTheta.torsionPoint N a b τ + (a : ℂ) * (τ : ℂ) + (b : ℂ) =
      CompletedTheta.torsionPoint N a b τ + ((a : ℂ) * (τ : ℂ) + (b : ℂ)) by ring]
    using principalLiftTerm_eq N a b τ p

/-- The prescribed actual x-value is a principal-divisor Eisenstein lattice sum divided by N. -/
theorem xValue_eq_principalLift_sum (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    TorsionWeierstrassData.xValue N a b τ =
      (∑' p : ℤ × ℤ, principalLiftTerm N a b τ p) / (N : ℂ) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [(hasSum_principalLiftTerm N hN a b τ).tsum_eq,
    TorsionWeierstrassData.xValue_of_good N a b τ hg]
  exact (mul_div_cancel_left₀ _ hNc).symm

/-! ## Finite degree-zero weights and the weight-two modular covariance -/

/-- Finite zero-total-weight combinations are absolute two-dimensional Eisenstein sums. -/
theorem hasSum_weighted_congruence (N : _root_.Nat) (hN : 0 < N)
    {ι : Type*} [Fintype ι] (a b : ι → ℤ) (c : ι → ℂ) (τ : _root_.UpperHalfPlane)
    (hc : ∑ i, c i = 0) :
    HasSum (fun p : ℤ × ℤ => ∑ i, c i * congruenceTerm N (a i) (b i) τ p)
      ((∑ i, c i * (ThetaWeierstrass.periodPair τ).weierstrassP
        (CompletedTheta.torsionPoint N (a i) (b i) τ)) / (N : ℂ) ^ 2) := by
  classical
  have h := hasSum_sum (s := Finset.univ) (fun i _ =>
    (hasSum_congruenceDifference N hN (a i) (b i) τ).mul_left (c i))
  have hv : (∑ i, c i * ((ThetaWeierstrass.periodPair τ).weierstrassP
      (CompletedTheta.torsionPoint N (a i) (b i) τ) / (N : ℂ) ^ 2)) =
      (∑ i, c i * (ThetaWeierstrass.periodPair τ).weierstrassP
        (CompletedTheta.torsionPoint N (a i) (b i) τ)) / (N : ℂ) ^ 2 := by
    simp only [mul_div_assoc, Finset.sum_div]
  rw [hv] at h
  refine h.congr_fun ?_
  intro p
  simp only [congruenceDifference, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hc, zero_mul, sub_zero]

/-- Literal finite-weight identification with the common actual x-values. -/
theorem weighted_xValue_eq_congruence_sum (N : _root_.Nat) (hN : 0 < N)
    {ι : Type*} [Fintype ι] (a b : ι → ℤ) (c : ι → ℂ) (τ : _root_.UpperHalfPlane)
    (hc : ∑ i, c i = 0)
    (hg : ∀ i, ¬ ((N : ℤ) ∣ a i ∧ (N : ℤ) ∣ b i)) :
    (∑ i, c i * TorsionWeierstrassData.xValue N (a i) (b i) τ) =
      (N : ℂ) ^ 2 * ∑' p : ℤ × ℤ, ∑ i,
        c i * EisensteinSeries.eisSummand 2 ![a i + N * p.1, b i + N * p.2] τ := by
  have hNc : (N : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')
  rw [show (fun p : ℤ × ℤ => ∑ i, c i * EisensteinSeries.eisSummand 2
      ![a i + N * p.1, b i + N * p.2] τ) =
      (fun p => ∑ i, c i * congruenceTerm N (a i) (b i) τ p) by rfl,
    (hasSum_weighted_congruence N hN a b c τ hc).tsum_eq]
  simp only [TorsionWeierstrassData.xValue_of_good N _ _ τ (hg _)]
  exact (mul_div_cancel₀ _ hNc).symm

open Matrix CongruenceSubgroup ModularForm
open scoped Modular MatrixGroups

set_option backward.isDefEq.respectTransparency.types false in
/-- Integral right multiplication on the entire index grid, with its actual inverse. -/
def vecMulEquiv (γ : SL(2, ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun v := v ᵥ* γ.1
  invFun v := v ᵥ* (γ⁻¹).1
  left_inv v := by
    dsimp only
    simp_rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  right_inv v := by
    dsimp only
    simp_rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

/-- The same actual congruence-class difference on the matrix-compatible grid. -/
def vectorDifference (N : _root_.Nat) (a : Fin 2 → ℤ) (τ : _root_.UpperHalfPlane)
    (v : Fin 2 → ℤ) : ℂ :=
  EisensteinSeries.eisSummand 2 (a + (N : ℤ) • v) τ -
    EisensteinSeries.eisSummand 2 ((N : ℤ) • v) τ

lemma vectorDifference_eq (N : _root_.Nat) (a : Fin 2 → ℤ) (τ : _root_.UpperHalfPlane)
    (v : Fin 2 → ℤ) :
    vectorDifference N a τ v = congruenceDifference N (a 0) (a 1) τ (v 0, v 1) := by
  simp [vectorDifference, congruenceDifference, congruenceTerm, EisensteinSeries.eisSummand]

theorem hasSum_vectorDifference (N : _root_.Nat) (hN : 0 < N) (a : Fin 2 → ℤ)
    (τ : _root_.UpperHalfPlane) :
    HasSum (vectorDifference N a τ)
      ((ThetaWeierstrass.periodPair τ).weierstrassP
        (CompletedTheta.torsionPoint N (a 0) (a 1) τ) / (N : ℂ) ^ 2) := by
  have h := (finTwoArrowEquiv ℤ).hasSum_iff.mpr
    (hasSum_congruenceDifference N hN (a 0) (a 1) τ)
  exact h.congr_fun fun v => vectorDifference_eq N a τ v

lemma divisionEisenstein_vector_sum (N : _root_.Nat) (a : Fin 2 → ℤ)
    (τ : _root_.UpperHalfPlane) :
    divisionEisenstein N (a 0) (a 1) τ =
      (N : ℂ) ^ 2 * ∑' v : Fin 2 → ℤ, vectorDifference N a τ v := by
  unfold divisionEisenstein
  rw [← (finTwoArrowEquiv ℤ).tsum_eq]
  congr 1
  exact tsum_congr fun v => (vectorDifference_eq N a τ v).symm

/-- The genuine denominator in the modular transformation law. -/
def slDenom (γ : SL(2, ℤ)) (τ : _root_.UpperHalfPlane) : ℂ :=
  UpperHalfPlane.denom
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)) (τ : ℂ)

lemma vectorDifference_SL2 (N : _root_.Nat) (a v : Fin 2 → ℤ) (γ : SL(2, ℤ))
    (τ : _root_.UpperHalfPlane) :
    vectorDifference N a (γ • τ) v = (slDenom γ τ) ^ 2 *
      vectorDifference N (a ᵥ* γ.1) τ (vecMulEquiv γ v) := by
  rw [vectorDifference, EisensteinSeries.eisSummand_SL2_apply,
    EisensteinSeries.eisSummand_SL2_apply, Matrix.add_vecMul, Matrix.smul_vecMul]
  simp only [slDenom, vectorDifference, vecMulEquiv, Equiv.coe_fn_mk, zpow_ofNat]
  ring

/-- Weight-two covariance is proved by an absolutely summable integral matrix reindexing. -/
theorem divisionEisenstein_SL2_apply (N : _root_.Nat) (hN : 0 < N) (a : Fin 2 → ℤ)
    (γ : SL(2, ℤ)) (τ : _root_.UpperHalfPlane) :
    divisionEisenstein N (a 0) (a 1) (γ • τ) = (slDenom γ τ) ^ 2 *
      divisionEisenstein N ((a ᵥ* γ.1) 0) ((a ᵥ* γ.1) 1) τ := by
  have hs := (hasSum_vectorDifference N hN (a ᵥ* γ.1) τ).summable
  have hreindex := ((vecMulEquiv γ).hasSum_iff.mpr hs.hasSum).tsum_eq
  simp only [Function.comp_apply] at hreindex
  rw [divisionEisenstein_vector_sum, divisionEisenstein_vector_sum]
  simp only [vectorDifference_SL2, tsum_mul_left]
  rw [hreindex]
  ring

/-- The independently defined lattice-series family has the actual weight-two slash covariance. -/
theorem divisionEisenstein_slash (N : _root_.Nat) (hN : 0 < N) (a : Fin 2 → ℤ)
    (γ : SL(2, ℤ)) :
    (fun τ : ℍ => divisionEisenstein N (a 0) (a 1) τ) ∣[(2 : ℤ)] γ =
      (fun τ : ℍ => divisionEisenstein N ((a ᵥ* γ.1) 0) ((a ᵥ* γ.1) 1) τ) := by
  funext τ
  rw [ModularForm.SL_slash_apply, divisionEisenstein_SL2_apply N hN a γ τ]
  have hd : slDenom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  simp only [slDenom, _root_.zpow_neg, _root_.zpow_ofNat]
  field_simp

lemma torsionPoint_add_level (N : _root_.Nat) (hN : 0 < N) (a b m n : _root_.Int)
    (τ : _root_.UpperHalfPlane) :
    CompletedTheta.torsionPoint N (a + N * m) (b + N * n) τ =
      CompletedTheta.torsionPoint N a b τ + ((m : ℂ) * (τ : ℂ) + (n : ℂ)) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold CompletedTheta.torsionPoint
  push_cast
  field_simp
  ring

/-- The series depends only on the actual congruence class of its torsion label. -/
theorem divisionEisenstein_add_level (N : _root_.Nat) (hN : 0 < N) (a b m n : _root_.Int)
    (τ : _root_.UpperHalfPlane) :
    divisionEisenstein N (a + N * m) (b + N * n) τ = divisionEisenstein N a b τ := by
  rw [divisionEisenstein_eq_weierstrassP N hN, divisionEisenstein_eq_weierstrassP N hN,
    torsionPoint_add_level N hN]
  have hl : (m : ℂ) * (τ : ℂ) + (n : ℂ) ∈ (ThetaWeierstrass.periodPair τ).lattice := by
    rw [ThetaWeierstrass.mem_periodPair_lattice_iff]
    exact ⟨n, m, by ring⟩
  exact (ThetaWeierstrass.periodPair τ).weierstrassP_add_coe _ ⟨_, hl⟩

lemma label_intCast_Gamma (N : _root_.Nat) (a : Fin 2 → ℤ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (i : Fin 2) :
    (((a ᵥ* γ.1) i : ℤ) : ZMod N) = (a i : ZMod N) := by
  have hg := CongruenceSubgroup.Gamma_mem'.mp hγ
  have hm : γ.1.map (Int.castRingHom (ZMod N)) = (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod N) => g.1) hg
    simpa only [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_one] using! h
  have h := RingHom.map_vecMul (Int.castRingHom (ZMod N)) γ.1 a i
  rw [hm, Matrix.vecMul_one] at h
  exact h

/-- Principal-congruence invariance of the actual, independently defined lattice-series family. -/
theorem divisionEisenstein_Gamma_label (N : _root_.Nat) (hN : 0 < N) (a : Fin 2 → ℤ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : _root_.UpperHalfPlane) :
    divisionEisenstein N ((a ᵥ* γ.1) 0) ((a ᵥ* γ.1) 1) τ =
      divisionEisenstein N (a 0) (a 1) τ := by
  have hd (i : Fin 2) : (N : ℤ) ∣ (a ᵥ* γ.1) i - a i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    simp only [Int.cast_sub, label_intCast_Gamma N a γ hγ, sub_self]
  obtain ⟨m, hm⟩ := hd 0
  obtain ⟨n, hn⟩ := hd 1
  have h0 : (a ᵥ* γ.1) 0 = a 0 + N * m := by linarith
  have h1 : (a ᵥ* γ.1) 1 = a 1 + N * n := by linarith
  rw [h0, h1]
  exact divisionEisenstein_add_level N hN (a 0) (a 1) m n τ

/-- Weight-two slash invariance; holomorphy and cusp bounds are separate analytic properties. -/
def divisionEisensteinSIF (N : _root_.Nat) (hN : 0 < N) (a : Fin 2 → ℤ) :
    SlashInvariantForm (CongruenceSubgroup.Gamma N) 2 where
  toFun τ := divisionEisenstein N (a 0) (a 1) τ
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ CongruenceSubgroup.Gamma N), rfl⟩ := hA
    have h := (divisionEisenstein_slash N hN a A).trans
      (funext (divisionEisenstein_Gamma_label N hN a A hA))
    rw [ModularForm.SL_slash] at h
    simpa only [Matrix.SpecialLinearGroup.mapGL, MonoidHom.comp_apply] using! h

/-- The actual shifted row sum is the negative derivative of the actual completed theta ratio. -/
theorem shifted_rowSum_eq_neg_theta_logDerivative (τ : _root_.UpperHalfPlane) (z : _root_.Complex)
    (hz : z ∉ (ThetaWeierstrass.periodPair τ).lattice) :
    (∑' m : ℤ, ∑' n : ℤ, 1 / (z + (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2) =
      -(deriv (fun w : ℂ => deriv (CompletedTheta.H τ) w / CompletedTheta.H τ w) z) := by
  rw [← weierstrassP_add_G2_eq_rowSum τ z hz,
    ThetaWeierstrass.weierstrassP_eq_neg_deriv_logDerivative τ z hz,
    ThetaG2.finitePart_eq_neg_G2]
  ring

/-! ## Holomorphy of the independent weight-two lattice-series family -/

open scoped Manifold

/-- Actual theta derivative series along any real affine upper-half-plane coordinate. -/
theorem differentiableAt_th_affine (k : ℕ) (r s : ℝ) {t : ℂ} (ht : 0 < t.im) :
    DifferentiableAt ℂ (fun u : ℂ => ThetaG2.th k ((r : ℂ) * u + (s : ℂ)) u) t := by
  let T0 : ℝ := t.im / 2
  let T1 : ℝ := t.im + 1
  let U : Set ℂ := {u | T0 < u.im ∧ u.im < T1}
  have hT : 0 < T0 := by dsimp [T0]; linarith
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have htU : t ∈ U := by constructor <;> dsimp [T0, T1] <;> linarith
  have hsum := (summable_pow_mul_jacobiTheta₂_term_bound (|r| * T1) hT k).mul_left
    ((2 * Real.pi) ^ k)
  have hd : DifferentiableOn ℂ (fun u : ℂ => ∑' n : ℤ,
      (2 * (Real.pi : ℂ) * I * n) ^ k * jacobiTheta₂_term n ((r : ℂ) * u + (s : ℂ)) u) U := by
    refine differentiableOn_tsum_of_summable_norm hsum ?_ hU ?_
    · intro n
      refine Differentiable.differentiableOn ?_
      unfold jacobiTheta₂_term
      fun_prop
    · intro n u hu
      have hbound : |((r : ℂ) * u + (s : ℂ)).im| ≤ |r| * T1 := by
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero, abs_mul, abs_of_pos (lt_trans hT hu.1)]
        exact mul_le_mul_of_nonneg_left hu.2.le (abs_nonneg r)
      exact ThetaG2.norm_term_coeff_le k hT hbound hu.1.le n
  exact hd.differentiableAt (hU.mem_nhds htU)

lemma H_logDerivative_eq_th (τ : _root_.UpperHalfPlane) (z : ℂ) (hz : CompletedTheta.H τ z ≠ 0) :
    deriv (CompletedTheta.H τ) z / CompletedTheta.H τ z =
      (Real.pi : ℂ) * I + ThetaG2.th 1 (z + ((τ : ℂ) + 1) / 2) τ /
        ThetaG2.th 0 (z + ((τ : ℂ) + 1) / 2) τ := by
  have hθ : jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ ≠ 0 := by
    exact (mul_ne_zero_iff.mp hz).2
  rw [CompletedTheta.deriv_H, ThetaG2.th_one, ThetaG2.th_zero]
  unfold CompletedTheta.Hder CompletedTheta.H
  have he := Complex.exp_ne_zero ((Real.pi : ℂ) * I * z)
  generalize jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ = A at hθ ⊢
  generalize jacobiTheta₂' (z + ((τ : ℂ) + 1) / 2) τ = B
  generalize cexp ((Real.pi : ℂ) * I * z) = E at he ⊢
  field_simp [hθ, he]

/-- Exact normalized row identity in the actual first and second theta derivative series. -/
theorem rowSum_eq_theta_quotients (τ : _root_.UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (ThetaWeierstrass.periodPair τ).lattice) :
    (∑' m : ℤ, ∑' n : ℤ, 1 / (z + (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2) =
      (ThetaG2.th 1 (z + ((τ : ℂ) + 1) / 2) τ /
        ThetaG2.th 0 (z + ((τ : ℂ) + 1) / 2) τ) ^ 2 -
      ThetaG2.th 2 (z + ((τ : ℂ) + 1) / 2) τ /
        ThetaG2.th 0 (z + ((τ : ℂ) + 1) / 2) τ := by
  have hH := ThetaWeierstrass.H_ne_zero_of_notMem τ hz
  have hθ : ThetaG2.th 0 (z + ((τ : ℂ) + 1) / 2) τ ≠ 0 := by
    rw [ThetaG2.th_zero]
    exact (mul_ne_zero_iff.mp hH).2
  have heq : (fun w : ℂ => deriv (CompletedTheta.H τ) w / CompletedTheta.H τ w) =ᶠ[𝓝 z]
      (fun w => (Real.pi : ℂ) * I + ThetaG2.th 1 (w + ((τ : ℂ) + 1) / 2) τ /
        ThetaG2.th 0 (w + ((τ : ℂ) + 1) / 2) τ) := by
    filter_upwards [(CompletedTheta.differentiable_H τ z).continuousAt.eventually_ne hH] with w hw
    exact H_logDerivative_eq_th τ w hw
  have h0 := (ThetaG2.hasDerivAt_th 0 τ.im_pos (z + ((τ : ℂ) + 1) / 2)).comp_add_const z
    (((τ : ℂ) + 1) / 2)
  have h1 := (ThetaG2.hasDerivAt_th 1 τ.im_pos (z + ((τ : ℂ) + 1) / 2)).comp_add_const z
    (((τ : ℂ) + 1) / 2)
  have hd := ((h1.div h0 hθ).const_add ((Real.pi : ℂ) * I)).deriv
  simp only [Pi.div_apply, Nat.reduceAdd] at hd
  rw [shifted_rowSum_eq_neg_theta_logDerivative τ z hz, heq.deriv_eq, hd]
  field_simp [hθ]
  ring

lemma torsion_affine_shift (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : _root_.UpperHalfPlane) :
    CompletedTheta.torsionPoint N a b τ + ((τ : ℂ) + 1) / 2 =
      (((a : ℝ) / N + 1 / 2 : ℝ) : ℂ) * (τ : ℂ) + (((b : ℝ) / N + 1 / 2 : ℝ) : ℂ) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold CompletedTheta.torsionPoint
  push_cast
  field_simp
  ring

lemma divisionEisenstein_zero_of_bad (N : ℕ) (hN : 0 < N) (a b : ℤ)
    (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) (τ : _root_.UpperHalfPlane) :
    divisionEisenstein N a b τ = 0 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨m, hm⟩ := hb.1
  obtain ⟨n, hn⟩ := hb.2
  have heq : CompletedTheta.torsionPoint N a b τ = (m : ℂ) * (τ : ℂ) + (n : ℂ) := by
    unfold CompletedTheta.torsionPoint
    rw [hm, hn]
    push_cast
    field_simp
  have hl : CompletedTheta.torsionPoint N a b τ ∈ (ThetaWeierstrass.periodPair τ).lattice := by
    rw [ThetaWeierstrass.mem_periodPair_lattice_iff]
    exact ⟨n, m, heq.trans (by ring)⟩
  rw [divisionEisenstein_eq_weierstrassP N hN]
  exact (ThetaWeierstrass.periodPair τ).weierstrassP_coe ⟨_, hl⟩

/-- Holomorphy follows for the actual independently defined weight-two difference series. -/
theorem divisionEisenstein_mdiff (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    MDiff (fun τ : ℍ => divisionEisenstein N a b τ) := by
  classical
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · have heq : (fun τ : ℍ => divisionEisenstein N a b τ) = fun _ => (0 : ℂ) :=
      funext (divisionEisenstein_zero_of_bad N hN a b hg)
    rw [heq]
    exact UpperHalfPlane.mdifferentiable_iff.mpr (differentiableOn_const (0 : ℂ))
  · have hG : MDiff EisensteinSeries.G2 := by
      rw [ThetaG2.G2_eq_smul_E2]
      exact MDifferentiable.const_smul _ E2_mdifferentiable
    have hGc := UpperHalfPlane.mdifferentiable_iff.mp hG
    let r : ℝ := (a : ℝ) / N + 1 / 2
    let s : ℝ := (b : ℝ) / N + 1 / 2
    have hd : DifferentiableOn ℂ (fun t : ℂ =>
        (ThetaG2.th 1 ((r : ℂ) * t + (s : ℂ)) t /
          ThetaG2.th 0 ((r : ℂ) * t + (s : ℂ)) t) ^ 2 -
        ThetaG2.th 2 ((r : ℂ) * t + (s : ℂ)) t /
          ThetaG2.th 0 ((r : ℂ) * t + (s : ℂ)) t -
        EisensteinSeries.G2 (UpperHalfPlane.ofComplex t)) {t | 0 < t.im} := by
      intro t ht
      have hne : ThetaG2.th 0 ((r : ℂ) * t + (s : ℂ)) t ≠ 0 := by
        have hH := CompletedTheta.H_torsion_ne_zero N hN (⟨t, ht⟩ : ℍ) a b hg
        have hθ := (mul_ne_zero_iff.mp hH).2
        rw [← torsion_affine_shift N hN a b (⟨t, ht⟩ : ℍ), ThetaG2.th_zero]
        exact hθ
      have h0 := differentiableAt_th_affine 0 r s ht
      have h1 := differentiableAt_th_affine 1 r s ht
      have h2 := differentiableAt_th_affine 2 r s ht
      have hGd := hGc.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds ht)
      exact (((h1.div h0 hne).pow 2).sub (h2.div h0 hne)).sub hGd |>.differentiableWithinAt
    apply UpperHalfPlane.mdifferentiable_iff.mpr
    apply hd.congr
    intro t ht
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos ht]
    have hz := torsionPoint_notMem_lattice N hN a b (⟨t, ht⟩ : ℍ) hg
    have h := weierstrassP_add_G2_eq_rowSum (⟨t, ht⟩ : ℍ) _ hz
    rw [rowSum_eq_theta_quotients (⟨t, ht⟩ : ℍ) _ hz, torsion_affine_shift N hN a b,
      ← divisionEisenstein_eq_weierstrassP N hN] at h
    dsimp only [r, s]
    linear_combination h

end ZInQ.Contrib.HeckePrimeRationality.EisensteinWeightTwo
