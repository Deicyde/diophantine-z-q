import ZInQKernel.Contrib.OneProof.X0ModuliUsed
import ZInQKernel.Contrib.GZTheta.TripleProduct
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville

/-!
# theta-wp8: `X0EtaRoute.ThetaWeierstrass8` proved

Task theta-wp8 (2026-11-15). Report: `docs/research/theta-wp8.md`; scratch and log: `scratch/theta-wp8/`.

**Main result** `ThetaWP8.thetaWeierstrass8 : X0EtaRoute.ThetaWeierstrass8`: for `w ∈ ℍ`, with Mathlib's
`jacobiTheta₂` and `℘ = ℘_{⟨1, w⟩}` (`PeriodPair.weierstrassP`),
`θ(0; w) / (e^{πiw/4} θ(w/2; w)) = 1 − 2(℘(1/2) − ℘(1/2 + w/8))/(℘(3w/8) − ℘(1/2 + w/8))`.
Consequences: `ThetaWP8.xEtaWeierstrass : X0EtaRoute.XEtaWeierstrass`, and Theorem 1.1 without the top hypothesis
`hX` and without any replacement for it (`ThetaWP8.frozenTarget_noHX`, `ThetaWP8.tyzThm35ReadingA_noHX`).

Proof (no new hypotheses; Mathlib, gz-theta's triple product `ZInQ.GZTheta.jacobiTheta₂_eq_jtpP`):
* **A.** `s(z) = θ(z + (1+w)/2; w)` has exact quasi-periods `1`, `w`, vanishes exactly on `ℤ + ℤw`
  (`sF_ne_zero`, `sF_lat`, from the triple product), and its zeros are simple (`sF_simple`: `s = (1 − e(−z))·G`).
* **B.** Removable singularities (`reg h x = lim_{y→x, y≠x} h y`) and boundedness of continuous doubly periodic
  functions (`isBounded_range_of_periodic`).
* **C.** For `c, 2c ∉ ℤ + ℤw`, `h(u) = (℘(u) − ℘(c)) s(u)²/(s(u − c) s(u + c))` is exactly doubly periodic and has
  an analytic representative at every point (pole of `℘` against the double zero of `s²`; simple zeros of
  `s(u ∓ c)` against the zeros of `℘(u) − ℘(c)`), nonzero at `0`; by Liouville it is a nonzero constant
  (`hF_const`). This is the classical `℘(u) − ℘(v) = −σ(u−v)σ(u+v)/(σ(u)²σ(v)²)` up to the constant, which cancels.
* **D.** The ratio becomes a quotient of six theta values; quasi-periodicity, the triple product at base
  `Q = e^{πiw/8}`, Euler's identity `∏(1 − x^{2n+1})∏(1 + x^{n+1}) = 1` and the series split
  `θ₄(w/4) = θ₃(w) − θ₂(w)` give `θ₂ θ(w/4) θ₃ θ₄(w/4) = 2 θ(1/2 + 3w/8)² θ(1/2 + w/8)²` (`prod_identity`), which is the
  identity (`core`).

No `sorry`, no `axiom`.
-/

open Complex Filter
open scoped Real Topology

noncomputable section

namespace ThetaWP8

open ZInQ.GZTheta

variable {w : ℂ}

/-- `s(z) = θ(z + (1+w)/2; w)`; its zeros are exactly `ℤ + ℤw`. -/
def sF (w z : ℂ) : ℂ := jacobiTheta₂ (z + (1 + w) / 2) w

theorem sF_add_one (z : ℂ) : sF w (z + 1) = sF w z := by
  unfold sF; rw [show z + 1 + (1 + w) / 2 = z + (1 + w) / 2 + 1 by ring, jacobiTheta₂_add_left]

theorem sF_add_w (z : ℂ) : sF w (z + w) = cexp (-π * I * (2 * w + 2 * z + 1)) * sF w z := by
  unfold sF
  rw [show z + w + (1 + w) / 2 = z + (1 + w) / 2 + w by ring, jacobiTheta₂_add_left']
  congr 2; ring

theorem differentiable_sF (hw : 0 < w.im) : Differentiable ℂ (sF w) := by
  intro z
  exact (differentiableAt_jacobiTheta₂_fst _ hw).comp z (by fun_prop)

/-- `eJ ((1+w)/2) = -q`. -/
theorem eJ_half_add (w : ℂ) : eJ ((1 + w) / 2) = -qJ w := by
  unfold eJ qJ
  rw [show 2 * (π : ℂ) * I * ((1 + w) / 2) = π * I + π * I * w by ring, Complex.exp_add,
    Complex.exp_pi_mul_I]; ring

/-- `B((1+w)/2) = A`. -/
theorem jtpB_half_add (w : ℂ) : jtpB w ((1 + w) / 2) = jtpA w := by
  unfold jtpB jtpA
  refine tprod_congr fun n => ?_
  rw [eJ_half_add]; ring

/-- `s(y) = (1 − e(−y)) · G(y)`, `G(y) = A · B(y + (1+w)/2) · B(−y + (1+w)/2)`. -/
def gF (w y : ℂ) : ℂ := jtpA w * jtpB w (y + (1 + w) / 2) * jtpB w (-y + (1 + w) / 2)

theorem sF_eq_factor (hw : 0 < w.im) (y : ℂ) : sF w y = (1 - eJ (-y)) * gF w y := by
  unfold sF gF
  rw [jacobiTheta₂_eq_jtpP hw]
  unfold jtpP
  have h := jtpB_neg_sub_tau hw (y + (1 - w) / 2)
  rw [show y + (1 - w) / 2 + w = y + (1 + w) / 2 by ring] at h
  rw [h]
  have e1 : (qJ w)⁻¹ * eJ (-(y + (1 - w) / 2)) = -eJ (-y) := by
    have : eJ (-(y + (1 - w) / 2)) = eJ (-y) * eJ (-((1 + w) / 2)) * eJ w := by
      rw [← eJ_add, ← eJ_add]; congr 1; ring
    rw [this, eJ_neg ((1 + w) / 2), eJ_half_add, eJ_tau w]
    have := qJ_ne_zero w
    field_simp
  have e2 : jtpB w (-(y + (1 - w) / 2)) = jtpB w (-y + (1 + w) / 2) := by
    rw [← jtpB_add_one w (-(y + (1 - w) / 2))]; congr 1; ring
  rw [e1, e2]; ring

theorem gF_zero (w : ℂ) : gF w 0 = jtpA w ^ 3 := by
  unfold gF; simp only [zero_add, neg_zero, jtpB_half_add]; ring

theorem differentiable_gF (hw : 0 < w.im) : Differentiable ℂ (gF w) := by
  unfold gF
  have h := differentiable_jtpB hw
  exact ((differentiable_const _).mul (h.comp (by fun_prop))).mul (h.comp (by fun_prop))

theorem sF_zero (hw : 0 < w.im) : sF w 0 = 0 := by
  rw [sF_eq_factor hw]; simp [eJ]

theorem hasDerivAt_sF_zero (hw : 0 < w.im) :
    HasDerivAt (sF w) (2 * π * I * jtpA w ^ 3) 0 := by
  have h1 : HasDerivAt (fun y : ℂ => 1 - eJ (-y)) (2 * π * I) 0 := by
    have : HasDerivAt (fun y : ℂ => cexp (2 * π * I * (-y))) (cexp (2 * π * I * (-0)) * (2 * π * I * (-1))) 0 :=
      (((hasDerivAt_id (0 : ℂ)).neg).const_mul (2 * π * I)).cexp |>.congr_deriv (by simp)
    have h2 := this.const_sub 1
    unfold eJ
    convert h2 using 1; simp
  have h3 := h1.mul ((differentiable_gF hw) 0).hasDerivAt
  have e : sF w = (fun y => (1 - eJ (-y)) * gF w y) := funext (sF_eq_factor hw)
  rw [e]
  convert h3 using 1
  simp [eJ, gF_zero]

theorem deriv_sF_zero_ne (hw : 0 < w.im) : deriv (sF w) 0 ≠ 0 := by
  rw [(hasDerivAt_sF_zero hw).deriv]
  have := jtpA_ne_zero hw
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [this, hpi, I_ne_zero]

/-! ### Zeros -/

theorem jtpB_ne_zero_of (hw : 0 < w.im) {x : ℂ} (hx : ∀ n : ℕ, 1 + qJ w ^ (2 * n + 1) * eJ x ≠ 0) :
    jtpB w x ≠ 0 :=
  tprod_one_add_ne_zero_of_summable hx (summable_jtpB_term hw x)

theorem qJ_pow_odd (w : ℂ) (n : ℕ) : qJ w ^ (2 * n + 1) = eJ ((2 * n + 1) * w / 2) := by
  unfold qJ eJ; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem eJ_eq_one_iff (x : ℂ) : eJ x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold eJ
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    apply mul_left_cancel₀ hpi
    rw [hm]; ring
  · rintro ⟨m, rfl⟩; exact ⟨m, by ring⟩

/-- `1 + q^{2n+1} e(x) = 0` forces `x + (2n+1)w/2 − 1/2 ∈ ℤ`. -/
theorem factor_zero {x : ℂ} {n : ℕ} (h : 1 + qJ w ^ (2 * n + 1) * eJ x = 0) :
    ∃ m : ℤ, x = m - (2 * n + 1) * w / 2 + 1 / 2 := by
  rw [qJ_pow_odd] at h
  have h1 : eJ (x + (2 * n + 1) * w / 2 - 1 / 2) = 1 := by
    have : eJ (x + (2 * n + 1) * w / 2 - 1 / 2) = -(eJ ((2 * n + 1) * w / 2) * eJ x) := by
      rw [sub_eq_add_neg, eJ_add, eJ_add, eJ_neg, show (1 / 2 : ℂ) = 1 / 2 from rfl]
      have : eJ (1 / 2) = -1 := eJ_half
      rw [this]; ring
    rw [this]; linear_combination -h
  obtain ⟨m, hm⟩ := (eJ_eq_one_iff _).1 h1
  exact ⟨m, by linear_combination hm⟩

/-- The lattice `ℤ + ℤw` as a predicate. -/
def InLat (w z : ℂ) : Prop := ∃ m n : ℤ, z = m + n * w

theorem sF_ne_zero (hw : 0 < w.im) {y : ℂ} (hy : ¬ InLat w y) : sF w y ≠ 0 := by
  unfold sF
  rw [jacobiTheta₂_eq_jtpP hw]
  unfold jtpP
  refine mul_ne_zero (mul_ne_zero (jtpA_ne_zero hw) ?_) ?_
  · refine jtpB_ne_zero_of hw fun n hn => hy ?_
    obtain ⟨m, hm⟩ := factor_zero hn
    exact ⟨m, -(n + 1), by push_cast; linear_combination hm⟩
  · refine jtpB_ne_zero_of hw fun n hn => hy ?_
    obtain ⟨m, hm⟩ := factor_zero hn
    exact ⟨-m - 1, n, by push_cast; linear_combination -hm⟩

/-! ### Quasi-periodicity along the lattice and simple zeros -/

theorem sF_add_int (z : ℂ) (m : ℤ) : sF w (z + m) = sF w z := by
  induction m using Int.induction_on generalizing z with
  | zero => simp
  | succ k ih =>
    rw [show z + ((k + 1 : ℤ) : ℂ) = (z + k) + 1 by push_cast; ring, sF_add_one]; exact_mod_cast ih z
  | pred k ih =>
    rw [← sF_add_one (z + ((-(k : ℤ) - 1 : ℤ) : ℂ)),
      show z + ((-(k : ℤ) - 1 : ℤ) : ℂ) + 1 = z + ((-(k : ℤ)) : ℤ) by push_cast; ring, ih]

/-- `s(z + p) = e^{a + bz} s(z)`. -/
def QP (w p : ℂ) : Prop := ∃ a b : ℂ, ∀ z, sF w (z + p) = cexp (a + b * z) * sF w z

theorem qp_add_w {p : ℂ} (h : QP w p) : QP w (p + w) := by
  obtain ⟨a, b, h⟩ := h
  refine ⟨a + b * w + (-π * I * (2 * w + 1)), b + (-π * I * 2), fun z => ?_⟩
  rw [show z + (p + w) = (z + w) + p by ring, h, sF_add_w, ← mul_assoc, ← Complex.exp_add]
  congr 2; ring

theorem qp_sub_w {p : ℂ} (h : QP w p) : QP w (p - w) := by
  obtain ⟨a, b, h⟩ := h
  refine ⟨a - b * w - (-π * I * (2 * w + 2 * (-w) + 1)), b - (-π * I * 2), fun z => ?_⟩
  have h' := sF_add_w (w := w) (z - w)
  rw [sub_add_cancel] at h'
  have hz : sF w (z - w) = cexp (-(-π * I * (2 * w + 2 * (z - w) + 1))) * sF w z := by
    rw [h', ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  rw [show z + (p - w) = (z - w) + p by ring, h, hz, ← mul_assoc, ← Complex.exp_add]
  congr 2; ring

theorem sF_add_lat (m n : ℤ) : QP w (m + n * w) := by
  induction n using Int.induction_on with
  | zero => exact ⟨0, 0, fun z => by simp [sF_add_int]⟩
  | succ k ih =>
    have := qp_add_w ih
    rwa [show (m : ℂ) + (k : ℤ) * w + w = m + ((k + 1 : ℤ) : ℂ) * w by push_cast; ring] at this
  | pred k ih =>
    have := qp_sub_w ih
    rwa [show (m : ℂ) + ((-(k : ℤ)) : ℤ) * w - w = m + ((-(k : ℤ) - 1 : ℤ) : ℂ) * w by
      push_cast; ring] at this

theorem sF_lat (hw : 0 < w.im) {l : ℂ} (hl : InLat w l) : sF w l = 0 := by
  obtain ⟨m, n, rfl⟩ := hl
  obtain ⟨a, b, h⟩ := sF_add_lat (w := w) m n
  have := h 0
  rw [zero_add] at this
  rw [this, sF_zero hw, mul_zero]

/-- Simple zero at every lattice point: `s(z) = (z − l) g(z)` with `g` entire, `g(l) ≠ 0`. -/
theorem sF_simple (hw : 0 < w.im) {l : ℂ} (hl : InLat w l) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g l ≠ 0 ∧ ∀ z, sF w z = (z - l) * g z := by
  obtain ⟨m, n, rfl⟩ := hl
  obtain ⟨a, b, h⟩ := sF_add_lat (w := w) m n
  set l := (m : ℂ) + n * w
  have hd0 : Differentiable ℂ (dslope (sF w) 0) := by
    have := (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) (f := sF w)
      Filter.univ_mem).2 (differentiable_sF hw).differentiableOn
    exact fun z => (this z (Set.mem_univ z)).differentiableAt Filter.univ_mem
  refine ⟨fun z => cexp (a + b * (z - l)) * dslope (sF w) 0 (z - l), ?_, ?_, ?_⟩
  · exact ((by fun_prop : Differentiable ℂ fun z => cexp (a + b * (z - l)))).mul
      (hd0.comp (by fun_prop))
  · simp only [sub_self, dslope_same]
    exact mul_ne_zero (Complex.exp_ne_zero _) (deriv_sF_zero_ne hw)
  · intro z
    have e := h (z - l)
    rw [sub_add_cancel] at e
    rw [e]
    have hs := sub_smul_dslope (sF w) 0 (z - l)
    rw [sF_zero hw, sub_zero, sub_zero, smul_eq_mul] at hs
    rw [← hs]; ring

/-! ## Part B. Removable singularities and Liouville for doubly periodic functions -/

section Liouville

/-- The regularization `H(x) = lim_{y → x, y ≠ x} h(y)`. -/
def reg (h : ℂ → ℂ) (x : ℂ) : ℂ := limUnder (𝓝[≠] x) h

/-- If `h` agrees near `x` (punctured) with a function analytic at `x`, the regularization agrees
with it on a neighbourhood of `x`. -/
theorem reg_eventuallyEq {h g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (hhg : h =ᶠ[𝓝[≠] x] g) :
    reg h =ᶠ[𝓝 x] g := by
  have h1 : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, z ≠ x → h z = g z :=
    (eventually_nhdsWithin_iff.1 hhg).eventually_nhds
  have h2 : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ g y := hg.eventually_analyticAt
  filter_upwards [h1, h2] with y hy hgy
  unfold reg
  apply Tendsto.limUnder_eq
  by_cases hyx : y = x
  · subst hyx
    exact (hgy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (hhg.mono fun z hz => hz.symm)
  · have hev : h =ᶠ[𝓝 y] g := by
      filter_upwards [hy, isOpen_ne.mem_nhds hyx] with z hz hzx using hz hzx
    exact (hgy.continuousAt.tendsto.congr' hev.symm).mono_left nhdsWithin_le_nhds

theorem reg_analyticAt {h g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (hhg : h =ᶠ[𝓝[≠] x] g) :
    AnalyticAt ℂ (reg h) x :=
  hg.congr (reg_eventuallyEq hg hhg).symm

theorem reg_eq {h g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (hhg : h =ᶠ[𝓝[≠] x] g) :
    reg h x = g x :=
  (reg_eventuallyEq hg hhg).eq_of_nhds

theorem reg_eq_self {h : ℂ → ℂ} {x : ℂ} (hh : AnalyticAt ℂ h x) : reg h x = h x :=
  reg_eq hh (Eventually.of_forall fun _ => rfl)

theorem reg_add_period {h : ℂ → ℂ} {p : ℂ} (hp : ∀ u, h (u + p) = h u) (x : ℂ) :
    reg h (x + p) = reg h x := by
  unfold reg
  have e : 𝓝[≠] (x + p) = Filter.map (fun u => u + p) (𝓝[≠] x) := by
    simp
  rw [e]
  have : h ∘ (fun u => u + p) = h := funext hp
  simp only [limUnder, Filter.map_map, this]

/-- A continuous function with periods `1` and `w` (`Im w > 0`) is bounded. -/
theorem isBounded_range_of_periodic {F : ℂ → ℂ} {w : ℂ} (hw : 0 < w.im) (hF : Continuous F)
    (h1 : ∀ u, F (u + 1) = F u) (hw' : ∀ u, F (u + w) = F u) : Bornology.IsBounded (Set.range F) := by
  set P : ℝ × ℝ → ℂ := fun st => (st.1 : ℂ) + st.2 * w
  have hP : Continuous P := by fun_prop
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hb : Bornology.IsBounded (F '' (P '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))) :=
    ((hK.image hP).image hF).isBounded
  refine hb.subset ?_
  rintro _ ⟨z, rfl⟩
  have hp1 : Function.Periodic F 1 := h1
  have hpw : Function.Periodic F w := hw'
  set n : ℤ := ⌊z.im / w.im⌋
  set z1 : ℂ := z - n * w
  set t : ℝ := z1.im / w.im
  set m : ℤ := ⌊z1.re - t * w.re⌋
  set z2 : ℂ := z1 - m
  have ht : t = z.im / w.im - n := by
    simp only [t, z1, sub_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero]
    field_simp
  have ht0 : 0 ≤ t := by rw [ht]; linarith [Int.floor_le (z.im / w.im)]
  have ht1 : t ≤ 1 := by rw [ht]; linarith [Int.lt_floor_add_one (z.im / w.im)]
  set s : ℝ := z1.re - t * w.re - m
  have hs0 : 0 ≤ s := by simp only [s]; linarith [Int.floor_le (z1.re - t * w.re)]
  have hs1 : s ≤ 1 := by simp only [s]; linarith [Int.lt_floor_add_one (z1.re - t * w.re)]
  have hz2 : z2 = P (s, t) := by
    apply Complex.ext
    · simp only [z2, P, s, sub_re, intCast_re, add_re, ofReal_re, mul_re, ofReal_im, zero_mul,
        sub_zero]
      ring
    · simp only [z2, P, sub_im, intCast_im, sub_zero, add_im, ofReal_im, mul_im, ofReal_re,
        zero_mul, add_zero, zero_add, t]
      field_simp
  have hFz : F z = F z2 := by
    simp only [z2, z1]
    have e1 := (hp1.int_mul m).sub_eq (z - n * w)
    have e2 := (hpw.int_mul n).sub_eq z
    rw [mul_one] at e1
    rw [e1, e2]
  refine ⟨P (s, t), ⟨(s, t), ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩, rfl⟩, ?_⟩
  rw [hFz, hz2]

end Liouville

/-! ## Part C. The elliptic function `h(u) = (℘(u) − ℘(c)) s(u)² / (s(u − c) s(u + c))` is constant -/

section WP

variable (L : PeriodPair) {w : ℂ}

theorem inLat_add {a b : ℂ} (ha : InLat w a) (hb : InLat w b) : InLat w (a + b) := by
  obtain ⟨m, n, rfl⟩ := ha; obtain ⟨m', n', rfl⟩ := hb
  exact ⟨m + m', n + n', by push_cast; ring⟩

theorem inLat_neg {a : ℂ} (ha : InLat w a) : InLat w (-a) := by
  obtain ⟨m, n, rfl⟩ := ha
  exact ⟨-m, -n, by push_cast; ring⟩

theorem inLat_sub {a b : ℂ} (ha : InLat w a) (hb : InLat w b) : InLat w (a - b) := by
  rw [sub_eq_add_neg]; exact inLat_add ha (inLat_neg hb)

theorem inLat_zero : InLat w 0 := ⟨0, 0, by simp⟩

variable {L}

theorem mem_lattice_iff (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) {x : ℂ} : x ∈ L.lattice ↔ InLat w x := by
  rw [PeriodPair.mem_lattice, h1, h2]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩

theorem wp_add_lat (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) (u : ℂ) {l : ℂ} (hl : InLat w l) :
    L.weierstrassP (u + l) = L.weierstrassP u :=
  L.weierstrassP_add_coe u ⟨l, (mem_lattice_iff h1 h2).2 hl⟩

variable (L w) in
/-- `h(u) = (℘(u) − ℘(c)) s(u)² / (s(u − c) s(u + c))`. -/
def hF (c u : ℂ) : ℂ :=
  (L.weierstrassP u - L.weierstrassP c) * sF w u ^ 2 / (sF w (u - c) * sF w (u + c))

theorem hF_add_one (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) (c u : ℂ) : hF L w c (u + 1) = hF L w c u := by
  unfold hF
  rw [wp_add_lat h1 h2 u ⟨1, 0, by simp⟩, sF_add_one,
    show u + 1 - c = (u - c) + 1 by ring, sF_add_one, show u + 1 + c = (u + c) + 1 by ring, sF_add_one]

theorem hF_add_w (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) (c u : ℂ) : hF L w c (u + w) = hF L w c u := by
  unfold hF
  rw [wp_add_lat h1 h2 u ⟨0, 1, by simp⟩, sF_add_w,
    show u + w - c = (u - c) + w by ring, sF_add_w, show u + w + c = (u + c) + w by ring, sF_add_w]
  set E := cexp (-π * I * (2 * w + 2 * u + 1))
  set E1 := cexp (-π * I * (2 * w + 2 * (u - c) + 1))
  set E2 := cexp (-π * I * (2 * w + 2 * (u + c) + 1))
  have hE : E1 * E2 = E ^ 2 := by
    simp only [E, E1, E2]
    rw [← Complex.exp_add, sq, ← Complex.exp_add]; congr 1; ring
  have hE0 : E1 * E2 ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  rw [show (E * sF w u) ^ 2 = (E1 * E2) * sF w u ^ 2 by rw [hE]; ring]
  rw [show (L.weierstrassP u - L.weierstrassP c) * ((E1 * E2) * sF w u ^ 2) /
      (E1 * sF w (u - c) * (E2 * sF w (u + c))) =
      (E1 * E2) * ((L.weierstrassP u - L.weierstrassP c) * sF w u ^ 2) /
      ((E1 * E2) * (sF w (u - c) * sF w (u + c))) by ring]
  exact mul_div_mul_left _ _ hE0

theorem analyticAt_wp (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) {x : ℂ} (hx : ¬ InLat w x) :
    AnalyticAt ℂ L.weierstrassP x :=
  L.analyticOnNhd_weierstrassP x (by rw [Set.mem_compl_iff, SetLike.mem_coe, mem_lattice_iff h1 h2]; exact hx)

theorem analyticAt_dslope_wp (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) {x : ℂ} (hx : ¬ InLat w x) :
    AnalyticAt ℂ (dslope L.weierstrassP x) x := by
  have hU : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 x :=
    L.isClosed_lattice.isOpen_compl.mem_nhds
      (by rw [Set.mem_compl_iff, SetLike.mem_coe, mem_lattice_iff h1 h2]; exact hx)
  exact ((Complex.differentiableOn_dslope hU).2 L.differentiableOn_weierstrassP).analyticAt hU

theorem analyticAt_sF (hw : 0 < w.im) (x : ℂ) : AnalyticAt ℂ (sF w) x :=
  (differentiable_sF hw).analyticAt x

/-- Local analytic representatives of `h` at every point; nonvanishing at `0`. -/
theorem hF_local (hw : 0 < w.im) (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) {c : ℂ} (hc : ¬ InLat w c)
    (h2c : ¬ InLat w (2 * c)) (x : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ hF L w c =ᶠ[𝓝[≠] x] g ∧ (x = 0 → g x ≠ 0) := by
  have hs := analyticAt_sF hw
  by_cases hx : InLat w x
  · -- a pole of `℘`, a double zero of `s²`
    obtain ⟨gx, hgx, hgx0, hsx⟩ := sF_simple hw hx
    have hxc : ¬ InLat w (x - c) := fun h => hc (by
      have := inLat_sub hx h; rwa [sub_sub_cancel] at this)
    have hxc' : ¬ InLat w (x + c) := fun h => hc (by
      have := inLat_sub h hx; rwa [add_sub_cancel_left] at this)
    have hD : sF w (x - c) * sF w (x + c) ≠ 0 := mul_ne_zero (sF_ne_zero hw hxc) (sF_ne_zero hw hxc')
    refine ⟨fun u => ((L.weierstrassPExcept x u - 1 / x ^ 2 - L.weierstrassP c) * (u - x) ^ 2 + 1) *
      gx u ^ 2 / (sF w (u - c) * sF w (u + c)), ?_, ?_, ?_⟩
    · refine AnalyticAt.div ?_ ((hs _).comp (by fun_prop) |>.mul ((hs _).comp (by fun_prop))) hD
      have : AnalyticAt ℂ (L.weierstrassPExcept x) x := L.analyticAt_weierstrassPExcept x
      have hg : AnalyticAt ℂ gx x := hgx.analyticAt x
      fun_prop
    · filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ x)
      have hux : u - x ≠ 0 := sub_ne_zero.2 hu
      have e := L.weierstrassPExcept_add ⟨x, (mem_lattice_iff h1 h2).2 hx⟩ u
      simp only at e
      unfold hF
      rw [← e, hsx u]
      congr 1
      field_simp
      ring
    · intro _
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_add, one_mul]
      exact div_ne_zero (pow_ne_zero _ hgx0) hD
  by_cases hx1 : InLat w (x - c)
  · obtain ⟨g', hg', hg'0, hsg'⟩ := sF_simple hw hx1
    have hxc' : ¬ InLat w (x + c) := fun h => h2c (by
      have := inLat_sub h hx1; rwa [show x + c - (x - c) = 2 * c by ring] at this)
    have hwx : L.weierstrassP x = L.weierstrassP c := by
      have := wp_add_lat h1 h2 c hx1; rwa [add_sub_cancel] at this
    refine ⟨fun u => dslope L.weierstrassP x u * sF w u ^ 2 / (g' (u - c) * sF w (u + c)), ?_, ?_, ?_⟩
    · refine AnalyticAt.div ?_ ?_ (mul_ne_zero (by simpa using hg'0) (sF_ne_zero hw hxc'))
      · have := analyticAt_dslope_wp h1 h2 hx
        have := hs x
        fun_prop
      · exact ((hg'.analyticAt _).comp (by fun_prop)).mul ((hs _).comp (by fun_prop))
    · filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ x)
      have hux : u - x ≠ 0 := sub_ne_zero.2 hu
      have hd := sub_smul_dslope L.weierstrassP x u
      rw [smul_eq_mul, hwx] at hd
      unfold hF
      rw [← hd, hsg' (u - c), show u - c - (x - c) = u - x by ring]
      rw [show (u - x) * dslope L.weierstrassP x u * sF w u ^ 2 =
          (u - x) * (dslope L.weierstrassP x u * sF w u ^ 2) by ring,
        show (u - x) * g' (u - c) * sF w (u + c) = (u - x) * (g' (u - c) * sF w (u + c)) by ring]
      exact mul_div_mul_left _ _ hux
    · intro h0; exact absurd (h0 ▸ inLat_zero) hx
  by_cases hx2 : InLat w (x + c)
  · obtain ⟨g', hg', hg'0, hsg'⟩ := sF_simple hw hx2
    have hxc : ¬ InLat w (x - c) := fun h => h2c (by
      have := inLat_sub hx2 h; rwa [show x + c - (x - c) = 2 * c by ring] at this)
    have hwx : L.weierstrassP x = L.weierstrassP c := by
      have := wp_add_lat h1 h2 (-c) hx2
      rw [show -c + (x + c) = x by ring, L.weierstrassP_neg] at this
      exact this
    refine ⟨fun u => dslope L.weierstrassP x u * sF w u ^ 2 / (sF w (u - c) * g' (u + c)), ?_, ?_, ?_⟩
    · refine AnalyticAt.div ?_ ?_ (mul_ne_zero (sF_ne_zero hw hxc) (by simpa using hg'0))
      · have := analyticAt_dslope_wp h1 h2 hx
        have := hs x
        fun_prop
      · exact ((hs _).comp (by fun_prop)).mul ((hg'.analyticAt _).comp (by fun_prop))
    · filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ x)
      have hux : u - x ≠ 0 := sub_ne_zero.2 hu
      have hd := sub_smul_dslope L.weierstrassP x u
      rw [smul_eq_mul, hwx] at hd
      unfold hF
      rw [← hd, hsg' (u + c), show u + c - (x + c) = u - x by ring]
      rw [show (u - x) * dslope L.weierstrassP x u * sF w u ^ 2 =
          (u - x) * (dslope L.weierstrassP x u * sF w u ^ 2) by ring,
        show sF w (u - c) * ((u - x) * g' (u + c)) = (u - x) * (sF w (u - c) * g' (u + c)) by ring]
      exact mul_div_mul_left _ _ hux
    · intro h0; exact absurd (h0 ▸ inLat_zero) hx
  · refine ⟨hF L w c, ?_, Eventually.of_forall fun _ => rfl, fun h0 => absurd (h0 ▸ inLat_zero) hx⟩
    unfold hF
    refine AnalyticAt.div ?_ ((hs _).comp (by fun_prop) |>.mul ((hs _).comp (by fun_prop)))
      (mul_ne_zero (sF_ne_zero hw hx1) (sF_ne_zero hw hx2))
    have := analyticAt_wp h1 h2 hx
    have := hs x
    fun_prop

/-- **`h` is a nonzero constant** off its singular set. -/
theorem hF_const (hw : 0 < w.im) (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) {c : ℂ} (hc : ¬ InLat w c)
    (h2c : ¬ InLat w (2 * c)) :
    ∃ K : ℂ, K ≠ 0 ∧ ∀ u, ¬ InLat w u → ¬ InLat w (u - c) → ¬ InLat w (u + c) → hF L w c u = K := by
  choose g hga hgh hg0 using hF_local hw h1 h2 hc h2c
  set H := reg (hF L w c)
  have hHa : ∀ x, AnalyticAt ℂ H x := fun x => reg_analyticAt (hga x) (hgh x)
  have hHd : Differentiable ℂ H := fun x => (hHa x).differentiableAt
  have hb := isBounded_range_of_periodic hw hHd.continuous
    (reg_add_period (hF_add_one h1 h2 c)) (reg_add_period (hF_add_w h1 h2 c))
  refine ⟨H 0, ?_, fun u hu hu1 hu2 => ?_⟩
  · show reg (hF L w c) 0 ≠ 0
    rw [reg_eq (hga 0) (hgh 0)]; exact hg0 0 rfl
  · rw [← hHd.apply_eq_apply_of_bounded hb u 0]
    symm
    apply reg_eq_self
    have hs := analyticAt_sF hw
    unfold hF
    refine AnalyticAt.div ?_ ((hs _).comp (by fun_prop) |>.mul ((hs _).comp (by fun_prop)))
      (mul_ne_zero (sF_ne_zero hw hu1) (sF_ne_zero hw hu2))
    have := analyticAt_wp h1 h2 hu
    have := hs u
    fun_prop

end WP

/-! ## Part D. The theta-constant identity (triple product, Euler, an even/odd series split) -/

section Products

/-- `Q = e^{πiw/8}`. -/
def Qw (w : ℂ) : ℂ := cexp (π * I * w / 8)

theorem Qw_ne_zero (w : ℂ) : Qw w ≠ 0 := Complex.exp_ne_zero _

theorem norm_Qw_lt_one (hw : 0 < w.im) : ‖Qw w‖ < 1 := by
  unfold Qw
  rw [Complex.norm_exp]
  have : (π * I * w / 8).re = -(π * w.im / 8) := by
    simp [Complex.mul_re]; ring
  rw [this]
  have := Real.pi_pos
  have : 0 < π * w.im / 8 := by positivity
  calc rexp (-(π * w.im / 8)) < rexp 0 := Real.exp_lt_exp.2 (by linarith)
    _ = 1 := Real.exp_zero

theorem Qw_pow (w : ℂ) (k : ℕ) : Qw w ^ k = cexp (k * (π * I * w / 8)) := by
  unfold Qw; rw [← Complex.exp_nat_mul]

theorem qJ_eq (w : ℂ) : qJ w = Qw w ^ 8 := by
  rw [Qw_pow, qJ]; congr 1; push_cast; ring

theorem qJ_quarter (w : ℂ) : qJ (w / 4) = Qw w ^ 2 := by
  rw [Qw_pow, qJ]; congr 1; push_cast; ring

theorem gp_shift {Q c d : ℂ} {k m m' : ℕ} (h : c * Q ^ m = d * Q ^ m') : gp Q c k m = gp Q d k m' := by
  unfold gp
  refine tprod_congr fun n => ?_
  rw [pow_add, pow_add, ← mul_assoc, ← mul_assoc, mul_right_comm c, mul_right_comm d, h]

theorem gp_split {Q : ℂ} (hQ : ‖Q‖ < 1) (c : ℂ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    gp Q c k m = (1 + c * Q ^ m) * gp Q c k (k + m) := by
  unfold gp
  have hm1 : Multipliable (fun n : ℕ => 1 + c * Q ^ (k * (n + 1) + m)) :=
    (multipliable_geom_lin hQ c k (k + m) hk).congr fun n => by ring_nf
  rw [tprod_eq_zero_mul' (f := fun n : ℕ => 1 + c * Q ^ (k * n + m)) hm1]
  simp only [mul_zero, zero_add]
  congr 1
  exact tprod_congr fun n => by ring_nf

theorem gp_pm {Q : ℂ} (hQ : ‖Q‖ < 1) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    gp Q 1 k m * gp Q (-1) k m = gp Q (-1) (2 * k) (2 * m) := by
  rw [gp_mul_gp hQ _ _ _ _ hk]
  unfold gp
  exact tprod_congr fun n => by ring

theorem gp_ne_zero {Q : ℂ} (hQ : ‖Q‖ < 1) (c : ℂ) {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (hc : ‖c‖ ≤ 1) : gp Q c k m ≠ 0 := by
  refine tprod_one_add_ne_zero_of_summable (fun n => one_add_ne_zero_of_norm_lt ?_)
    (summable_geom_lin hQ c k m hk)
  rw [norm_mul, norm_pow]
  calc ‖c‖ * ‖Q‖ ^ (k * n + m) ≤ 1 * ‖Q‖ ^ (k * n + m) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ < 1 := by rw [one_mul]; exact pow_lt_one₀ (norm_nonneg _) hQ (by positivity)

/-- **Euler's identity** `∏(1 − x^{2n+1}) ∏(1 + x^{n+1}) = 1`, `x = Q^{16}`. -/
theorem euler16 {Q : ℂ} (hQ : ‖Q‖ < 1) : gp Q (-1) 32 16 * gp Q 1 16 16 = 1 := by
  have h1 := gp_pm hQ (k := 16) (by norm_num) 16
  have h2 := gp_even_mul_odd hQ (-1) 16 16 (by norm_num)
  have h0 := gp_ne_zero hQ (-1) (k := 32) (m := 32) (by norm_num) (by norm_num) (by simp)
  norm_num at h1 h2
  apply mul_right_cancel₀ h0
  linear_combination h1 + gp Q 1 16 16 * h2

/-- Triple product at base `Q`. -/
theorem theta_gp (hw : 0 < w.im) (z : ℂ) :
    jacobiTheta₂ z w = gp (Qw w) (-1) 16 16 * gp (Qw w) (eJ z) 16 8 * gp (Qw w) (eJ (-z)) 16 8 := by
  rw [jacobiTheta₂_eq_jtpP hw]
  unfold jtpP
  rw [jtpA_eq_gp, jtpB_eq_gp, jtpB_eq_gp, qJ_eq, gp_pow, gp_pow, gp_pow]

theorem eJ_lin (a : ℂ) (k : ℕ) : eJ (a + k * w / 8) = eJ a * Qw w ^ (2 * k) := by
  rw [eJ_add, Qw_pow]; unfold eJ; congr 2; push_cast; ring

/-- `θ₄(w/4) = θ₃(w) − θ₂(w)` (split the series into even and odd indices). -/
theorem theta4_quarter (hw : 0 < w.im) :
    jacobiTheta₂ (1 / 2) (w / 4) = jacobiTheta₂ 0 w - cexp (π * I * w / 4) * jacobiTheta₂ (w / 2) w := by
  have hw4 : 0 < (w / 4).im := by simp; linarith
  set F : ℤ → ℂ := fun m => jacobiTheta₂_term m (1 / 2) (w / 4)
  let e : ℤ ⊕ ℤ → ℤ := Sum.elim (fun n => 2 * n) (fun n => 2 * n + 1)
  have he : Function.Bijective e := by
    constructor
    · rintro (a | a) (b | b) h <;> simp [e] at h ⊢ <;> omega
    · intro m
      obtain ⟨k, hk | hk⟩ := Int.even_or_odd' m
      · exact ⟨Sum.inl k, by simp [e, hk]⟩
      · exact ⟨Sum.inr k, by simp [e, hk]⟩
  have hF := hasSum_jacobiTheta₂_term (1 / 2) hw4
  have hS : HasSum (F ∘ e) (jacobiTheta₂ 0 w + -cexp (π * I * w / 4) * jacobiTheta₂ (w / 2) w) := by
    apply HasSum.sum
    · refine (hasSum_jacobiTheta₂_term 0 hw).congr_fun fun n => ?_
      simp only [Function.comp_apply, F, e, Sum.elim_inl, jacobiTheta₂_term]
      rw [show 2 * π * I * ((2 * n : ℤ) : ℂ) * (1 / 2) + π * I * ((2 * n : ℤ) : ℂ) ^ 2 * (w / 4) =
        (2 * π * I * n * 0 + π * I * n ^ 2 * w) + n * (2 * π * I) by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    · refine ((hasSum_jacobiTheta₂_term (w / 2) hw).mul_left (-cexp (π * I * w / 4))).congr_fun
        fun n => ?_
      simp only [Function.comp_apply, F, e, Sum.elim_inr, jacobiTheta₂_term]
      rw [show 2 * π * I * ((2 * n + 1 : ℤ) : ℂ) * (1 / 2) + π * I * ((2 * n + 1 : ℤ) : ℂ) ^ 2 * (w / 4) =
        (π * I + π * I * w / 4 + (2 * π * I * n * (w / 2) + π * I * n ^ 2 * w)) + n * (2 * π * I) by
          push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
        Complex.exp_add, Complex.exp_pi_mul_I]
      ring
  have hS' := (Equiv.hasSum_iff (Equiv.ofBijective e he)).2 hF
  rw [neg_mul, ← sub_eq_add_neg] at hS
  exact hF.unique ((Equiv.hasSum_iff (Equiv.ofBijective e he)).1 hS)

end Products

section Values

variable (hw : 0 < w.im)
include hw

omit hw in
theorem gp_c_eq {k m m' : ℕ} {c d : ℂ} (h : c * Qw w ^ m = d * Qw w ^ m') :
    gp (Qw w) c k m = gp (Qw w) d k m' := gp_shift h

include hw

theorem val_t0 : jacobiTheta₂ 0 w = gp (Qw w) (-1) 16 16 * gp (Qw w) 1 16 8 ^ 2 := by
  rw [theta_gp hw, neg_zero]; simp [eJ, sq, mul_assoc]

theorem val_t4 : jacobiTheta₂ (w / 4) w =
    gp (Qw w) (-1) 16 16 * gp (Qw w) 1 16 12 * gp (Qw w) 1 16 4 := by
  have hQ := Qw_ne_zero w
  have e1 : eJ (w / 4) = Qw w ^ 4 := by
    have := eJ_lin (w := w) 0 2; rw [show (0 : ℂ) + (2 : ℕ) * w / 8 = w / 4 by push_cast; ring] at this
    rw [this]; simp [eJ]
  rw [theta_gp hw, eJ_neg, e1, gp_c_eq (c := Qw w ^ 4) (m := 8) (m' := 12) (d := 1) (by ring),
    gp_c_eq (c := (Qw w ^ 4)⁻¹) (m := 8) (m' := 4) (d := 1) (by field_simp)]

theorem val_u (k : ℕ) (hk : k ≤ 3) : jacobiTheta₂ (1 / 2 + k * w / 8) w =
    gp (Qw w) (-1) 16 16 * gp (Qw w) (-1) 16 (8 + 2 * k) * gp (Qw w) (-1) 16 (8 - 2 * k) := by
  have hQ := Qw_ne_zero w
  have e1 : eJ (1 / 2 + k * w / 8) = -Qw w ^ (2 * k) := by rw [eJ_lin, eJ_half]; ring
  rw [theta_gp hw, eJ_neg, e1, gp_c_eq (c := -Qw w ^ (2 * k)) (m := 8) (m' := 8 + 2 * k) (d := -1)
    (by ring), gp_c_eq (c := (-Qw w ^ (2 * k))⁻¹) (m := 8) (m' := 8 - 2 * k) (d := -1) ?_]
  have : Qw w ^ 8 = Qw w ^ (2 * k) * Qw w ^ (8 - 2 * k) := by rw [← pow_add]; congr 1; omega
  rw [this]; field_simp

theorem val_t2 : jacobiTheta₂ (w / 2) w = 2 * gp (Qw w) (-1) 16 16 * gp (Qw w) 1 16 16 ^ 2 := by
  have hQ := Qw_ne_zero w
  have e1 : eJ (w / 2) = Qw w ^ 8 := by
    have := eJ_lin (w := w) 0 4; rw [show (0 : ℂ) + (4 : ℕ) * w / 8 = w / 2 by push_cast; ring] at this
    rw [this]; simp [eJ]
  rw [theta_gp hw, eJ_neg, e1, gp_c_eq (c := Qw w ^ 8) (m := 8) (m' := 16) (d := 1) (by ring),
    gp_c_eq (c := (Qw w ^ 8)⁻¹) (m := 8) (m' := 0) (d := 1) (by field_simp), gp_split (norm_Qw_lt_one hw) 1 (by norm_num) 0]
  norm_num; ring

theorem val_f4 : jacobiTheta₂ (1 / 2) (w / 4) =
    (gp (Qw w) (-1) 16 4 * gp (Qw w) (-1) 16 12 * gp (Qw w) (-1) 16 8 * gp (Qw w) (-1) 16 16) *
    (gp (Qw w) (-1) 16 2 * gp (Qw w) (-1) 16 10 * gp (Qw w) (-1) 16 6 * gp (Qw w) (-1) 16 14) ^ 2 := by
  have hQ := norm_Qw_lt_one hw
  have hw4 : 0 < (w / 4).im := by simp; linarith
  rw [jacobiTheta₂_eq_jtpP hw4]
  unfold jtpP
  have eh : eJ (-(1 / 2)) = -1 := by rw [eJ_neg, eJ_half]; norm_num
  rw [jtpA_eq_gp, jtpB_eq_gp, jtpB_eq_gp, eJ_half, eh, qJ_quarter, gp_pow, gp_pow]
  have a1 := gp_even_mul_odd hQ (-1) 4 4 (by norm_num)
  have a2 := gp_even_mul_odd hQ (-1) 8 4 (by norm_num)
  have a3 := gp_even_mul_odd hQ (-1) 8 8 (by norm_num)
  have b1 := gp_even_mul_odd hQ (-1) 4 2 (by norm_num)
  have b2 := gp_even_mul_odd hQ (-1) 8 2 (by norm_num)
  have b3 := gp_even_mul_odd hQ (-1) 8 6 (by norm_num)
  norm_num at a1 a2 a3 b1 b2 b3 ⊢
  rw [← a1, ← a2, ← a3, ← b1, ← b2, ← b3]
  ring

/-- **The product identity** `θ₂ · θ(w/4) · θ₃ · θ₄(w/4) = 2 θ(1/2 + 3w/8)² θ(1/2 + w/8)²`. -/
theorem prod_identity :
    jacobiTheta₂ (w / 2) w * jacobiTheta₂ (w / 4) w * jacobiTheta₂ 0 w * jacobiTheta₂ (1 / 2) (w / 4) =
      2 * jacobiTheta₂ (1 / 2 + (3 : ℕ) * w / 8) w ^ 2 * jacobiTheta₂ (1 / 2 + (1 : ℕ) * w / 8) w ^ 2 := by
  have hQ := norm_Qw_lt_one hw
  rw [val_t2 hw, val_t4 hw, val_t0 hw, val_f4 hw, val_u hw 3 (by norm_num), val_u hw 1 (by norm_num)]
  norm_num
  have r1 := gp_pm hQ (k := 16) (by norm_num) 4
  have r2 := gp_pm hQ (k := 16) (by norm_num) 12
  have r3 := gp_pm hQ (k := 16) (by norm_num) 8
  have r4 := gp_even_mul_odd hQ (-1) 16 8 (by norm_num)
  have r5 := euler16 hQ
  norm_num at r1 r2 r3 r4
  set A := gp (Qw w) (-1) 16 16
  set P16 := gp (Qw w) 1 16 16
  set P12 := gp (Qw w) 1 16 12
  set P8 := gp (Qw w) 1 16 8
  set P4 := gp (Qw w) 1 16 4
  set M4 := gp (Qw w) (-1) 16 4
  set M8 := gp (Qw w) (-1) 16 8
  set M12 := gp (Qw w) (-1) 16 12
  set g8 := gp (Qw w) (-1) 32 8
  set g16 := gp (Qw w) (-1) 32 16
  set g24 := gp (Qw w) (-1) 32 24
  set M := gp (Qw w) (-1) 16 2 * gp (Qw w) (-1) 16 10 * gp (Qw w) (-1) 16 6 * gp (Qw w) (-1) 16 14
  -- bracket `P16² P12 P4 P8² M4 M12 M8 = 1`
  have hb : P16 ^ 2 * (P12 * M12) * (P4 * M4) * P8 ^ 2 * M8 = 1 := by
    rw [r1, r2, mul_assoc (P16 ^ 2), mul_comm g24 g8, r4]
    linear_combination (P16 * g16 + 1) * r5 + P16 ^ 2 * (P8 * M8 + g16) * r3
  linear_combination 2 * A ^ 4 * M ^ 2 * hb

end Values

/-! ## Part E. Assembly -/

section Assembly

theorem notInt_div (p : ℤ) (d : ℕ) (hd0 : 0 < d) (hd : ¬ (d : ℤ) ∣ p) :
    ∀ n : ℤ, (n : ℝ) ≠ (p : ℝ) / d := by
  intro n h
  have h1 : ((n * d : ℤ) : ℝ) = p := by
    push_cast; rw [h]; field_simp
  have h2 : n * d = p := by exact_mod_cast h1
  exact hd ⟨n, by rw [← h2]; ring⟩

theorem not_inLat (hw : 0 < w.im) {z : ℂ} (x y : ℝ) (hz : z = x + y * w)
    (h : (∀ m : ℤ, (m : ℝ) ≠ x) ∨ (∀ n : ℤ, (n : ℝ) ≠ y)) : ¬ InLat w z := by
  rintro ⟨m, n, hmn⟩
  rw [hz] at hmn
  have him := congrArg Complex.im hmn
  have hre := congrArg Complex.re hmn
  simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add, intCast_im,
    intCast_re] at him
  have hy : y = n := by
    have : (y - n) * w.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact absurd h' hw.ne'
  subst hy
  simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero, intCast_re, intCast_im] at hre
  have hx : x = m := by linarith
  rcases h with h | h
  · exact h m hx.symm
  · exact h n rfl

theorem exp_mul_Q_eq {X : ℂ} (k : ℕ) (n : ℤ) (hX : X + k * (π * I * w / 8) = n * (2 * π * I)) :
    cexp X * Qw w ^ k = 1 := by
  rw [Qw_pow, ← Complex.exp_add, hX, Complex.exp_int_mul_two_pi_mul_I]

theorem exp_mul_Q_eq_neg {X : ℂ} (k : ℕ) (n : ℤ)
    (hX : X + k * (π * I * w / 8) = π * I + n * (2 * π * I)) : cexp X * Qw w ^ k = -1 := by
  rw [Qw_pow, ← Complex.exp_add, hX, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_pi_mul_I]; ring

theorem aux_eq (X S D : ℂ) (hS : S ≠ 0) (hD : D ≠ 0) : X = X * S ^ 2 / D * D / S ^ 2 := by
  field_simp

theorem theta_add_two (y : ℂ) : jacobiTheta₂ (y + 2) w = jacobiTheta₂ y w := by
  rw [show y + 2 = y + 1 + 1 by ring, jacobiTheta₂_add_left, jacobiTheta₂_add_left]

/-- **Core theorem** (any period pair `(1, w)`, `Im w > 0`). -/
theorem core (L : PeriodPair) (hw : 0 < w.im) (h1 : L.ω₁ = 1) (h2 : L.ω₂ = w) :
    jacobiTheta₂ 0 w / (cexp (π * I * w / 4) * jacobiTheta₂ (w / 2) w) =
      1 - 2 * ((L.weierstrassP (1 / 2) - L.weierstrassP (1 / 2 + w / 8)) /
        (L.weierstrassP (3 * w / 8) - L.weierstrassP (1 / 2 + w / 8))) := by
  set c : ℂ := 1 / 2 + w / 8 with hcdef
  have n2 := notInt_div 1 2 (by norm_num) (by norm_num)
  have n4 := notInt_div 1 4 (by norm_num) (by norm_num)
  have n8 := notInt_div 1 8 (by norm_num) (by norm_num)
  have nm8 := notInt_div (-1) 8 (by norm_num) (by norm_num)
  have n38 := notInt_div 3 8 (by norm_num) (by norm_num)
  push_cast at n2 n4 n8 nm8 n38
  have hc : ¬ InLat w c := not_inLat hw (1 / 2) (1 / 8) (by push_cast; ring) (Or.inl n2)
  have h2c : ¬ InLat w (2 * c) := not_inLat hw 1 (1 / 4) (by push_cast; ring) (Or.inr n4)
  obtain ⟨K, hK0, hK⟩ := hF_const hw h1 h2 hc h2c
  have ha0 : ¬ InLat w (1 / 2) := not_inLat hw (1 / 2) 0 (by push_cast; ring) (Or.inl n2)
  have ha1 : ¬ InLat w (1 / 2 - c) := not_inLat hw 0 (-1 / 8) (by push_cast; ring) (Or.inr nm8)
  have ha2 : ¬ InLat w (1 / 2 + c) := not_inLat hw 1 (1 / 8) (by push_cast; ring) (Or.inr n8)
  have hb0 : ¬ InLat w (3 * w / 8) := not_inLat hw 0 (3 / 8) (by push_cast; ring) (Or.inr n38)
  have hb1 : ¬ InLat w (3 * w / 8 - c) := not_inLat hw (-1 / 2) (1 / 4) (by push_cast; ring) (Or.inr n4)
  have hb2 : ¬ InLat w (3 * w / 8 + c) := not_inLat hw (1 / 2) (1 / 2) (by push_cast; ring) (Or.inr n2)
  have ha := hK _ ha0 ha1 ha2
  have hb := hK _ hb0 hb1 hb2
  unfold hF at ha hb
  have sa0 := sF_ne_zero hw ha0
  have sa1 := sF_ne_zero hw ha1
  have sa2 := sF_ne_zero hw ha2
  have sb0 := sF_ne_zero hw hb0
  have sb1 := sF_ne_zero hw hb1
  have sb2 := sF_ne_zero hw hb2
  -- `℘(u) − ℘(c) = K · s(u − c) s(u + c) / s(u)²`
  have hA : L.weierstrassP (1 / 2) - L.weierstrassP c =
      K * (sF w (1 / 2 - c) * sF w (1 / 2 + c)) / sF w (1 / 2) ^ 2 := by
    rw [← ha]; exact aux_eq _ _ _ sa0 (mul_ne_zero sa1 sa2)
  have hB : L.weierstrassP (3 * w / 8) - L.weierstrassP c =
      K * (sF w (3 * w / 8 - c) * sF w (3 * w / 8 + c)) / sF w (3 * w / 8) ^ 2 := by
    rw [← hb]; exact aux_eq _ _ _ sb0 (mul_ne_zero sb1 sb2)
  rw [hA, hB]
  have hP := prod_identity hw
  have hf4 := theta4_quarter hw
  rw [hf4] at hP
  -- the six theta values
  set Q := Qw w
  have hQ : Q ≠ 0 := Qw_ne_zero w
  set u3 := jacobiTheta₂ (1 / 2 + (3 : ℕ) * w / 8) w
  set u1 := jacobiTheta₂ (1 / 2 + (1 : ℕ) * w / 8) w
  set t0 := jacobiTheta₂ 0 w
  set t2 := jacobiTheta₂ (w / 2) w
  set t4 := jacobiTheta₂ (w / 4) w
  have e1 : sF w (1 / 2 - c) = u3 := by unfold sF; congr 1; push_cast; ring
  have e2 : sF w (1 / 2 + c) = -(Q ^ 2)⁻¹ * u3 := by
    unfold sF
    have q := jacobiTheta₂_add_left' (-(1 / 2 + (3 : ℕ) * w / 8) + 2) w
    rw [theta_add_two, jacobiTheta₂_neg_left] at q
    have hE := exp_mul_Q_eq_neg (w := w) (X := -π * I * (w + 2 * (-(1 / 2 + (3 : ℕ) * w / 8) + 2))) 2 (-2)
      (by push_cast; ring)
    rw [show 1 / 2 + c + (1 + w) / 2 = -(1 / 2 + (3 : ℕ) * w / 8) + 2 + w by push_cast; ring, q]
    rw [show cexp (-π * I * (w + 2 * (-(1 / 2 + (3 : ℕ) * w / 8) + 2))) = -(Q ^ 2)⁻¹ by
      rw [eq_div_of_mul_eq (pow_ne_zero _ hQ) hE]; ring]
  have e3 : sF w (1 / 2) = t2 := by
    unfold sF; rw [show (1 / 2 : ℂ) + (1 + w) / 2 = w / 2 + 1 by ring, jacobiTheta₂_add_left]
  have e4 : sF w (3 * w / 8) = -(Q ^ 6)⁻¹ * u1 := by
    unfold sF
    have q := jacobiTheta₂_add_left' (-(1 / 2 + (1 : ℕ) * w / 8) + 1) w
    rw [jacobiTheta₂_add_left, jacobiTheta₂_neg_left] at q
    have hE := exp_mul_Q_eq_neg (w := w) (X := -π * I * (w + 2 * (-(1 / 2 + (1 : ℕ) * w / 8) + 1))) 6 (-1)
      (by push_cast; ring)
    rw [show 3 * w / 8 + (1 + w) / 2 = -(1 / 2 + (1 : ℕ) * w / 8) + 1 + w by push_cast; ring, q]
    rw [show cexp (-π * I * (w + 2 * (-(1 / 2 + (1 : ℕ) * w / 8) + 1))) = -(Q ^ 6)⁻¹ by
      rw [eq_div_of_mul_eq (pow_ne_zero _ hQ) hE]; ring]
  have e5 : sF w (3 * w / 8 - c) = (Q ^ 4)⁻¹ * t4 := by
    unfold sF
    have q := jacobiTheta₂_add_left' (-(w / 4)) w
    rw [jacobiTheta₂_neg_left] at q
    have hE := exp_mul_Q_eq (w := w) (X := -π * I * (w + 2 * -(w / 4))) 4 0 (by push_cast; ring)
    rw [show 3 * w / 8 - c + (1 + w) / 2 = -(w / 4) + w by ring, q]
    rw [show cexp (-π * I * (w + 2 * -(w / 4))) = (Q ^ 4)⁻¹ by
      rw [eq_div_of_mul_eq (pow_ne_zero _ hQ) hE]; ring]
  have e6 : sF w (3 * w / 8 + c) = (Q ^ 8)⁻¹ * t0 := by
    unfold sF
    have q := jacobiTheta₂_add_left' (0 + 1) w
    rw [jacobiTheta₂_add_left] at q
    have hE := exp_mul_Q_eq (w := w) (X := -π * I * (w + 2 * (0 + 1))) 8 (-1) (by push_cast; ring)
    rw [show 3 * w / 8 + c + (1 + w) / 2 = 0 + 1 + w by ring, q]
    rw [show cexp (-π * I * (w + 2 * (0 + 1))) = (Q ^ 8)⁻¹ by
      rw [eq_div_of_mul_eq (pow_ne_zero _ hQ) hE]; ring]
  have hQ2 : cexp (π * I * w / 4) = Q ^ 2 := by
    rw [Qw_pow]; congr 1; push_cast; ring
  have ht0 : t0 ≠ 0 := by intro h; apply sb2; rw [e6, h, mul_zero]
  have ht4 : t4 ≠ 0 := by intro h; apply sb1; rw [e5, h, mul_zero]
  have hu1 : u1 ≠ 0 := by intro h; apply sb0; rw [e4, h, mul_zero]
  have ht2 : t2 ≠ 0 := by rw [← e3]; exact sa0
  rw [e1, e2, e3, e4, e5, e6, hQ2]
  rw [hQ2] at hP
  field_simp
  linear_combination hP

end Assembly

end ThetaWP8

/-! ## The contribution -/

namespace ThetaWP8

/-- **`X0EtaRoute.ThetaWeierstrass8` (glue GLUE THETA-WP-8 of hx-used), proved.** -/
theorem thetaWeierstrass8 : X0EtaRoute.ThetaWeierstrass8 := by
  intro w
  exact core (T5Glue.pp w) w.im_pos rfl rfl

/-- `X0EtaRoute.XEtaWeierstrass` (x0-32's eta quotient as a `℘`-ratio), proved. -/
theorem xEtaWeierstrass : X0EtaRoute.XEtaWeierstrass :=
  X0EtaRoute.xEtaWeierstrass_of_theta thetaWeierstrass8

open ZInQ.Contrib.TYZDecomp in
/-- **TYZ reading A with neither `hX` nor a replacement**: from the three `𝓛`-leaves, the printed main theorem
of CM `hCM` and TYZ Theorem 3.3. -/
theorem tyzThm35ReadingA_noHX (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2)
    (hCM : T5Glue.ShimuraMainCM) (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33) :
    ZInQ.Literature.TYZThm35ReadingA :=
  X0ModuliUsed.tyzThm35ReadingA_of_theta h11 h29 hCM thetaWeierstrass8 h33

/-- **Theorem 1.1 without the top hypothesis `hX`**: the binders of `ZInQ.OneProof.frozenTarget` (base
`43513d87`) minus `hX`. It is `X0ModuliUsed.frozenTarget_of_theta` with `hT := thetaWeierstrass8`. -/
theorem frozenTarget_noHX
    (r : HDec.HSyn.OpenResearchLeaves22) (t : HDec.HSyn.OpenTextbookLeaves11) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : ZInQ.Contrib.TYZDecomp.TYZThm11Integral) (h29 : ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hFH : ZInQ.GZFH.FriedbergHoffsteinB_FE) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  X0ModuliUsed.frozenTarget_of_theta r t l g h11 h29 hCM thetaWeierstrass8 h33 hFH hL3

end ThetaWP8
