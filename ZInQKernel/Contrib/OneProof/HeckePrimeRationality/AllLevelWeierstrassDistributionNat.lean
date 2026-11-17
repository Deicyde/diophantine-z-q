import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionWeierstrassData
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDistributionNat
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelUnipotentAverage

/-!
# Distribution of Weierstrass torsion values in every positive degree

For the lattice `ℤ + ℤ τ` let `℘` be Mathlib's Weierstrass function and let
`xValue N a b τ` be `℘((a τ + b)/N)` when `(a, b)` is not divisible by `N` and `0` otherwise.
For all positive `n, N` and all integers `a, b`:
`Σ_{r,s < n} xValue (nN) (a + N r) (b + N s) τ = n² · xValue N a b τ`.

Proof.
* Generic identity. Where all factors of the degree-`n` multiplication identity of the completed
  theta function `H` are nonzero, the logarithmic-derivative identity
  `Σ_p H'/H(x + c_p) = K + n H'/H(n x)` holds on a neighbourhood; differentiating it and using
  `℘ = -(H'/H)' + c` gives `Σ_p ℘(z + c_p) = n² ℘(n z)` off the lattice (`weierstrassP_sum`),
  where `c_p = (r τ + s)/n`.
* Admissible image: specialize at `z = (a τ + b)/(nN)`.
* Inadmissible image: subtracting the double pole `1/z²` on both sides and letting `z → 0`
  (the finite part of `℘` at `0` is `0`) gives `Σ_{p ≠ 0} ℘(c_p) = 0`. The values themselves need
  not vanish; only their sum does. Periodicity in the labels then covers every inadmissible
  image, where the right-hand side is `0` by the zero convention.

No distribution identity is assumed; the inputs are the proved multiplication identity, the
proved theta–Weierstrass comparison and Mathlib's lattice sum.
-/

noncomputable section

open Complex Filter Topology
open scoped Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.WeierstrassDistributionNat

open CompletedTheta TorsionDistributionNat ThetaWeierstrass TorsionWeierstrassData

/-- The logarithmic derivative of `H`. -/
def G (τ : ℍ) (w : ℂ) : ℂ := deriv (H τ) w / H τ w

theorem differentiableAt_G (τ : ℍ) {w : ℂ} (hw : H τ w ≠ 0) : DifferentiableAt ℂ (G τ) w :=
  (analyticAt_logDerivative (differentiable_H τ) hw).differentiableAt

theorem notMem_iff_H_ne_zero (τ : ℍ) (w : ℂ) : w ∉ (periodPair τ).lattice ↔ H τ w ≠ 0 :=
  (H_zero_iff_mem_lattice τ w).not.symm

/-- The logarithmic-derivative identity on a neighbourhood. -/
theorem logDeriv_eventually (n : ℕ) (hn : 0 < n) (τ : ℍ) {z : ℂ}
    (hz : ∀ p, H τ (z + cn τ n p) ≠ 0) (hnz : H τ ((n : ℂ) * z) ≠ 0) :
    ∀ᶠ x in 𝓝 z, ∑ p, G τ (x + cn τ n p) = K n + (n : ℂ) * G τ ((n : ℂ) * x) := by
  have hc : ∀ p, ∀ᶠ x in 𝓝 z, H τ (x + cn τ n p) ≠ 0 := fun p =>
    ((differentiable_H τ).continuous.comp (continuous_id.add continuous_const)).continuousAt
      |>.eventually_ne (hz p)
  have hcn : ∀ᶠ x in 𝓝 z, H τ ((n : ℂ) * x) ≠ 0 :=
    ((differentiable_H τ).continuous.comp (continuous_const.mul continuous_id)).continuousAt
      |>.eventually_ne hnz
  filter_upwards [Filter.eventually_all.mpr hc, hcn] with x hx hnx
  have h := logDeriv_sum n hn τ x hx hnx
  simp only [← deriv_H] at h
  exact h

/-- Differentiated identity: `Σ_p (H'/H)'(z + c_p) = n² (H'/H)'(n z)`. -/
theorem logDeriv_deriv_sum (n : ℕ) (hn : 0 < n) (τ : ℍ) {z : ℂ}
    (hz : ∀ p, H τ (z + cn τ n p) ≠ 0) (hnz : H τ ((n : ℂ) * z) ≠ 0) :
    ∑ p, deriv (G τ) (z + cn τ n p) = (n : ℂ) ^ 2 * deriv (G τ) ((n : ℂ) * z) := by
  have hL : HasDerivAt (fun x => ∑ p, G τ (x + cn τ n p)) (∑ p, deriv (G τ) (z + cn τ n p)) z :=
    HasDerivAt.fun_sum fun p _ =>
      ((differentiableAt_G τ (hz p)).hasDerivAt).comp_add_const z (cn τ n p)
  have hR0 : HasDerivAt (fun x => G τ ((n : ℂ) * x)) (deriv (G τ) ((n : ℂ) * z) * (n : ℂ)) z := by
    have h := ((differentiableAt_G τ hnz).hasDerivAt).comp z
      ((hasDerivAt_id' z).const_mul (n : ℂ))
    exact h.congr_deriv (by ring)
  have hR : HasDerivAt (fun x => K n + (n : ℂ) * G τ ((n : ℂ) * x))
      ((n : ℂ) * (deriv (G τ) ((n : ℂ) * z) * (n : ℂ))) z :=
    (hR0.const_mul (n : ℂ)).const_add (K n)
  have hL' := hR.congr_of_eventuallyEq (logDeriv_eventually n hn τ hz hnz)
  rw [hL.unique hL']
  ring

/-- **Generic distribution of `℘`**: `Σ_p ℘(z + c_p) = n² ℘(n z)` off the lattice. -/
theorem weierstrassP_sum (n : ℕ) (hn : 0 < n) (τ : ℍ) {z : ℂ}
    (hz : ∀ p, z + cn τ n p ∉ (periodPair τ).lattice)
    (hnz : (n : ℂ) * z ∉ (periodPair τ).lattice) :
    ∑ p, (periodPair τ).weierstrassP (z + cn τ n p) =
      (n : ℂ) ^ 2 * (periodPair τ).weierstrassP ((n : ℂ) * z) := by
  have hz' : ∀ p, H τ (z + cn τ n p) ≠ 0 := fun p => (notMem_iff_H_ne_zero τ _).mp (hz p)
  have hnz' : H τ ((n : ℂ) * z) ≠ 0 := (notMem_iff_H_ne_zero τ _).mp hnz
  have hW : ∀ w, w ∉ (periodPair τ).lattice →
      (periodPair τ).weierstrassP w = -deriv (G τ) w + finitePart τ := fun w hw =>
    weierstrassP_eq_neg_deriv_logDerivative τ w hw
  rw [Finset.sum_congr rfl fun p _ => hW _ (hz p), hW _ hnz, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, logDeriv_deriv_sum n hn τ hz' hnz', Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-! ### Admissible images -/

theorem x_distribution_good (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (a b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    ∑ r : Fin n, ∑ s : Fin n, xValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      (n : ℂ) ^ 2 * xValue N a b τ := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set t := torsionPoint N a b τ with ht
  set u := t / n with hu
  have hnu : (n : ℂ) * u = t := by rw [hu]; field_simp
  have hpre : ∀ p : Fin n × Fin n, torsionPoint (n * N) (a + N * ((p.1 : ℕ) : ℤ))
      (b + N * ((p.2 : ℕ) : ℤ)) τ = u + cn τ n p := fun p =>
    torsionPoint_preimage hn hN a b τ p.1 p.2
  have hz : ∀ p : Fin n × Fin n, u + cn τ n p ∉ (periodPair τ).lattice := by
    intro p
    rw [notMem_iff_H_ne_zero, ← hpre p]
    exact H_torsion_ne_zero (n * N) (Nat.mul_pos hn hN) τ _ _ (good_preimage hg p.1 p.2)
  have hnz : (n : ℂ) * u ∉ (periodPair τ).lattice := by
    rw [hnu, notMem_iff_H_ne_zero]
    exact H_torsion_ne_zero N hN τ a b hg
  rw [← Fintype.sum_prod_type' (fun (r s : Fin n) =>
    xValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ)]
  rw [Finset.sum_congr rfl fun p _ => by
    rw [xValue_of_good _ _ _ τ (good_preimage hg p.1 p.2), hpre p]]
  rw [weierstrassP_sum n hn τ hz hnz, hnu, xValue_of_good N a b τ hg]

/-! ### The vanishing sum over nonzero `n`-torsion -/

/-- The zero index. -/
def p0 (n : ℕ) (hn : 0 < n) : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩)

theorem cn_p0 (n : ℕ) (hn : 0 < n) (τ : ℍ) : cn τ n (p0 n hn) = 0 := by
  simp [cn, p0]

theorem cn_notMem (n : ℕ) (hn : 0 < n) (τ : ℍ) {p : Fin n × Fin n} (hp : p ≠ p0 n hn) :
    cn τ n p ∉ (periodPair τ).lattice := by
  rw [mem_periodPair_lattice_iff]
  rintro ⟨m, k, hmk⟩
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : ((p.1 : ℕ) : ℂ) * τ + ((p.2 : ℕ) : ℂ) = (n : ℂ) * ((m : ℂ) + (k : ℂ) * τ) := by
    unfold cn at hmk
    rw [← hmk]; field_simp
  have him := congrArg Complex.im heq
  have hre := congrArg Complex.re heq
  simp at him hre
  have h1 : ((p.1 : ℕ) : ℝ) = n * k := by
    have h' : (((p.1 : ℕ) : ℝ) - n * k) * τ.im = 0 := by linear_combination him
    rcases mul_eq_zero.mp h' with h | h
    · linarith
    · exact absurd h τ.im_ne_zero
  have hr0 : (p.1 : ℕ) = 0 := by
    have hlt : ((p.1 : ℕ) : ℝ) < n := by exact_mod_cast p.1.isLt
    have hk : (k : ℝ) = 0 := by
      rcases lt_trichotomy (k : ℝ) 0 with h | h | h
      · nlinarith [(Nat.cast_nonneg (p.1 : ℕ) : (0 : ℝ) ≤ _)]
      · exact h
      · have hk1 : (1 : ℝ) ≤ k := by
          have : (0 : ℤ) < k := by exact_mod_cast h
          exact_mod_cast this
        nlinarith
    rw [hk, mul_zero] at h1
    exact_mod_cast h1
  have hs : ((p.2 : ℕ) : ℝ) = n * m := by
    linear_combination hre - τ.re * h1
  have hs0 : (p.2 : ℕ) = 0 := by
    have hlt : ((p.2 : ℕ) : ℝ) < n := by exact_mod_cast p.2.isLt
    have hm : (m : ℝ) = 0 := by
      rcases lt_trichotomy (m : ℝ) 0 with h | h | h
      · nlinarith [(Nat.cast_nonneg (p.2 : ℕ) : (0 : ℝ) ≤ _)]
      · exact h
      · have hm1 : (1 : ℝ) ≤ m := by
          have : (0 : ℤ) < m := by exact_mod_cast h
          exact_mod_cast this
        nlinarith
    rw [hm, mul_zero] at hs
    exact_mod_cast hs
  apply hp
  exact Prod.ext (Fin.ext hr0) (Fin.ext hs0)

/-- **Sum over nonzero `n`-torsion**: `Σ_{p ≠ 0} ℘((r τ + s)/n) = 0`. -/
theorem weierstrassP_sum_nonzero (n : ℕ) (hn : 0 < n) (τ : ℍ) :
    ∑ p ∈ Finset.univ.erase (p0 n hn), (periodPair τ).weierstrassP (cn τ n p) = 0 := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set L := periodPair τ
  set S := Finset.univ.erase (p0 n hn)
  have hU : ((L.lattice : Set ℂ) \ {(0 : ℂ)})ᶜ ∈ 𝓝 (0 : ℂ) := L.compl_lattice_sdiff_singleton_mem_nhds 0
  have hnear : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (∀ p, z + cn τ n p ∉ L.lattice) ∧ (n : ℂ) * z ∉ L.lattice ∧ z ≠ 0 := by
    have hz0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0 := self_mem_nhdsWithin
    have hzU : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ((L.lattice : Set ℂ) \ {(0 : ℂ)})ᶜ :=
      nhdsWithin_le_nhds hU
    have hnU : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (n : ℂ) * z ∈ ((L.lattice : Set ℂ) \ {(0 : ℂ)})ᶜ := by
      have ht : Tendsto (fun z : ℂ => (n : ℂ) * z) (𝓝 0) (𝓝 0) :=
        (continuous_const.mul continuous_id : Continuous fun z : ℂ => (n : ℂ) * z).tendsto' 0 0 (mul_zero _)
      exact nhdsWithin_le_nhds (ht.eventually_mem hU)
    have hp : ∀ p, p ≠ p0 n hn → ∀ᶠ z in 𝓝[≠] (0 : ℂ), z + cn τ n p ∉ L.lattice := by
      intro p hp
      have hopen : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
      have ht : Tendsto (fun z : ℂ => z + cn τ n p) (𝓝 0) (𝓝 (cn τ n p)) :=
        (continuous_id.add continuous_const : Continuous fun z : ℂ => z + cn τ n p).tendsto' 0 _ (zero_add _)
      exact nhdsWithin_le_nhds (ht.eventually_mem (hopen.mem_nhds (cn_notMem n hn τ hp)))
    have hall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ p, p ≠ p0 n hn → z + cn τ n p ∉ L.lattice :=
      Filter.eventually_all.mpr fun p => by
        by_cases h : p = p0 n hn
        · exact Filter.Eventually.of_forall fun z h' => absurd h h'
        · exact (hp p h).mono fun z hz _ => hz
    filter_upwards [hz0, hzU, hnU, hall] with z hz0 hzU hnU hall
    have hnz0 : (n : ℂ) * z ≠ 0 := mul_ne_zero hn' hz0
    refine ⟨fun p => ?_, fun h => hnU ⟨h, hnz0⟩, hz0⟩
    by_cases h : p = p0 n hn
    · rw [h, cn_p0, add_zero]; exact fun hm => hzU ⟨hm, hz0⟩
    · exact hall p h
  have hident : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ∑ p ∈ S, L.weierstrassP (z + cn τ n p) =
        (n : ℂ) ^ 2 * (L.weierstrassP ((n : ℂ) * z) - 1 / ((n : ℂ) * z) ^ 2) -
          (L.weierstrassP z - 1 / z ^ 2) := by
    filter_upwards [hnear] with z ⟨hz, hnz, hz0⟩
    have h := weierstrassP_sum n hn τ hz hnz
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (p0 n hn)), cn_p0, add_zero] at h
    have e : (n : ℂ) ^ 2 * (1 / ((n : ℂ) * z) ^ 2) = 1 / z ^ 2 := by field_simp
    linear_combination h + e
  have hlimL : Tendsto (fun z => ∑ p ∈ S, L.weierstrassP (z + cn τ n p)) (𝓝[≠] (0 : ℂ))
      (𝓝 (∑ p ∈ S, L.weierstrassP (cn τ n p))) := by
    refine tendsto_finsetSum _ fun p hp => ?_
    have hpne : p ≠ p0 n hn := Finset.ne_of_mem_erase hp
    have hopen : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
    have hd : DifferentiableAt ℂ L.weierstrassP (cn τ n p) :=
      (L.differentiableOn_weierstrassP _ (cn_notMem n hn τ hpne)).differentiableAt
        (hopen.mem_nhds (cn_notMem n hn τ hpne))
    have ht : Tendsto (fun z : ℂ => z + cn τ n p) (𝓝 0) (𝓝 (cn τ n p)) :=
      (continuous_id.add continuous_const : Continuous fun z : ℂ => z + cn τ n p).tendsto' 0 _ (zero_add _)
    exact (hd.continuousAt.tendsto.comp ht).mono_left nhdsWithin_le_nhds
  have hlimR : Tendsto (fun z => (n : ℂ) ^ 2 * (L.weierstrassP ((n : ℂ) * z) -
      1 / ((n : ℂ) * z) ^ 2) - (L.weierstrassP z - 1 / z ^ 2)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((n : ℂ) ^ 2 * 0 - 0)) := by
    have hf := weierstrassP_finitePart_zero τ
    have hmul : Tendsto (fun z : ℂ => (n : ℂ) * z) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun z : ℂ => (n : ℂ) * z) (𝓝 0) (𝓝 0) :=
          (continuous_const.mul continuous_id : Continuous fun z : ℂ => (n : ℂ) * z).tendsto' 0 0 (mul_zero _)
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact mul_ne_zero hn' hz
    exact ((hf.comp hmul).const_mul _).sub hf
  have hlimR' := hlimR.congr' (hident.mono fun z hz => hz.symm)
  have := tendsto_nhds_unique hlimL hlimR'
  rw [this]; ring

/-! ### Label periodicity and the inadmissible images -/

theorem xValue_shift {M : ℕ} (hM : 0 < M) (A B m k : ℤ) (τ : ℍ) :
    xValue M (A + M * m) (B + M * k) τ = xValue M A B τ := by
  by_cases hg : (M : ℤ) ∣ A ∧ (M : ℤ) ∣ B
  · have hg' : (M : ℤ) ∣ A + M * m ∧ (M : ℤ) ∣ B + M * k :=
      ⟨dvd_add hg.1 (dvd_mul_right _ _), dvd_add hg.2 (dvd_mul_right _ _)⟩
    simp only [xValue, hg, hg', and_self, ite_true]
  · have hg' : ¬ ((M : ℤ) ∣ A + M * m ∧ (M : ℤ) ∣ B + M * k) :=
      (AllLevelForms.good_shift (N := M) (a := A) (b := B) m k).mpr hg
    rw [xValue_of_good _ _ _ τ hg, xValue_of_good _ _ _ τ hg']
    have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
    have hmem : ((k : ℂ) + (m : ℂ) * τ) ∈ (periodPair τ).lattice :=
      (mem_periodPair_lattice_iff τ _).mpr ⟨k, m, rfl⟩
    have e : torsionPoint M (A + M * m) (B + M * k) τ =
        torsionPoint M A B τ + ((⟨(k : ℂ) + (m : ℂ) * τ, hmem⟩ : (periodPair τ).lattice) : ℂ) := by
      simp only [torsionPoint]
      push_cast
      field_simp
      ring
    rw [e, PeriodPair.weierstrassP_add_coe]

theorem x_sum_bad (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (a' b' : ℤ) :
    ∑ r : Fin n, ∑ s : Fin n,
      xValue (n * N) (N * a' + N * ((r : ℕ) : ℤ)) (N * b' + N * ((s : ℕ) : ℤ)) τ = 0 := by
  have hnN : 0 < n * N := Nat.mul_pos hn hN
  set g : ℤ → ℤ → ℂ := fun x y => xValue (n * N) (N * x) (N * y) τ with hgdef
  have hperx : ∀ x y : ℤ, g (x + n) y = g x y := by
    intro x y
    simp only [hgdef]
    rw [show (N : ℤ) * (x + n) = N * x + ((n * N : ℕ) : ℤ) * 1 by push_cast; ring]
    conv_lhs => rw [show (N : ℤ) * y = N * y + ((n * N : ℕ) : ℤ) * 0 by ring]
    rw [xValue_shift hnN]
  have hpery : ∀ x y : ℤ, g x (y + n) = g x y := by
    intro x y
    simp only [hgdef]
    rw [show (N : ℤ) * (y + n) = N * y + ((n * N : ℕ) : ℤ) * 1 by push_cast; ring]
    conv_lhs => rw [show (N : ℤ) * x = N * x + ((n * N : ℕ) : ℤ) * 0 by ring]
    rw [xValue_shift hnN]
  have hterm : ∀ r s : Fin n,
      xValue (n * N) (N * a' + N * ((r : ℕ) : ℤ)) (N * b' + N * ((s : ℕ) : ℤ)) τ =
        g (((r : ℕ) : ℤ) + a') (((s : ℕ) : ℤ) + b') := by
    intro r s
    simp only [hgdef]
    rw [show (N : ℤ) * a' + N * ((r : ℕ) : ℤ) = N * (((r : ℕ) : ℤ) + a') by ring,
      show (N : ℤ) * b' + N * ((s : ℕ) : ℤ) = N * (((s : ℕ) : ℤ) + b') by ring]
  simp_rw [hterm]
  have hinner : ∀ x : ℤ, ∑ s : Fin n, g x (((s : ℕ) : ℤ) + b') = ∑ s : Fin n, g x ((s : ℕ) : ℤ) := by
    intro x
    rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => g x ((s : ℤ) + b')) n,
      Fin.sum_univ_eq_sum_range (fun s : ℕ => g x (s : ℤ)) n]
    exact AllLevelAverage.sum_range_shift (N := n) (g x) (hpery x) b'
  simp_rw [hinner]
  set Gs : ℤ → ℂ := fun x => ∑ s : Fin n, g x ((s : ℕ) : ℤ) with hGs
  have hGper : ∀ x, Gs (x + n) = Gs x := fun x => by simp only [hGs, hperx]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => Gs ((r : ℤ) + a')) n,
    AllLevelAverage.sum_range_shift (N := n) Gs hGper a',
    ← Fin.sum_univ_eq_sum_range (fun r : ℕ => Gs (r : ℤ)) n]
  simp only [hGs]
  rw [← Fintype.sum_prod_type' (fun (r s : Fin n) => g ((r : ℕ) : ℤ) ((s : ℕ) : ℤ)),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (p0 n hn))]
  have h0 : g (((p0 n hn).1 : ℕ) : ℤ) (((p0 n hn).2 : ℕ) : ℤ) = 0 := by
    simp only [hgdef, p0, Nat.cast_zero, mul_zero]
    exact xValue_zero _ τ
  rw [h0, zero_add, ← weierstrassP_sum_nonzero n hn τ]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpne : p ≠ p0 n hn := Finset.ne_of_mem_erase hp
  have hgood : ¬ (((n * N : ℕ) : ℤ) ∣ N * ((p.1 : ℕ) : ℤ) ∧
      ((n * N : ℕ) : ℤ) ∣ N * ((p.2 : ℕ) : ℤ)) := by
    rintro ⟨h1, h2⟩
    apply hpne
    have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    have d1 : (n : ℤ) ∣ ((p.1 : ℕ) : ℤ) := by
      obtain ⟨c, hc⟩ := h1
      exact ⟨c, by apply mul_left_cancel₀ hNz; rw [hc]; push_cast; ring⟩
    have d2 : (n : ℤ) ∣ ((p.2 : ℕ) : ℤ) := by
      obtain ⟨c, hc⟩ := h2
      exact ⟨c, by apply mul_left_cancel₀ hNz; rw [hc]; push_cast; ring⟩
    have e1 : (p.1 : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt (by exact_mod_cast d1) p.1.isLt
    have e2 : (p.2 : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt (by exact_mod_cast d2) p.2.isLt
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  simp only [hgdef]
  rw [xValue_of_good _ _ _ τ hgood]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [torsionPoint, cn]
  push_cast
  field_simp

/-- **Distribution of Weierstrass torsion values in degree `n`, for all integer labels.** -/
theorem x_distribution_nat (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (a b : ℤ) :
    ∑ r : Fin n, ∑ s : Fin n, xValue (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      (n : ℂ) ^ 2 * xValue N a b τ := by
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hg
    have hx : xValue N (N * a') (N * b') τ = 0 := by
      simp [xValue]
    rw [hx, mul_zero]
    exact x_sum_bad n N hn hN τ a' b'
  · exact x_distribution_good n N hn hN τ a b hg

end ZInQ.Contrib.HeckePrimeRationality.WeierstrassDistributionNat
