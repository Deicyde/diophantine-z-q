import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint

/-! Analytic normalization of short Weierstrass coordinates, using only a pole condition on x. -/

namespace HDec.CMBranch.CMjBridges

open Filter Set
open scoped Topology PeriodPair

/-- A germ of an analytic numerator for a pole of order two, with nonzero leading term.
The equality is only on the punctured neighbourhood, so values assigned at the pole
carry no information. -/
def HasDoublePoleAtZero (f : ℂ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ F 0 ≠ 0 ∧
    (fun z => z ^ 2 * f z) =ᶠ[𝓝[≠] 0] F

/-- To certify a double pole, it suffices to clear it by the square of an
analytic local parameter with nonzero derivative. This applies to evaluations
of regular sections in a chart at the identity. -/
theorem hasDoublePoleAtZero_of_localParameter {f t v : ℂ → ℂ}
    (ht : AnalyticAt ℂ t 0) (ht0 : t 0 = 0) (ht' : deriv t 0 ≠ 0)
    (hv : AnalyticAt ℂ v 0) (hv0 : v 0 ≠ 0)
    (he : (fun z => t z ^ 2 * f z) =ᶠ[𝓝[≠] 0] v) :
    HasDoublePoleAtZero f := by
  have hg : AnalyticAt ℂ (dslope t 0) 0 := by
    obtain ⟨p, hp⟩ := ht
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hg0 : dslope t 0 0 ≠ 0 := by simpa using ht'
  refine ⟨fun z => v z / dslope t 0 z ^ 2, hv.div (hg.pow 2) (pow_ne_zero 2 hg0),
    div_ne_zero hv0 (pow_ne_zero 2 hg0), ?_⟩
  filter_upwards [he, (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds]
    with z hz hne
  have hz' : z * dslope t 0 z = t z := by
    simpa [smul_eq_mul, ht0] using sub_smul_dslope t 0 z
  apply (eq_div_iff (pow_ne_zero 2 hne)).mpr
  rw [← hz, ← hz', mul_pow]
  ring

private theorem affine_weierstrassP_of_even (P : PeriodPair) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f P.latticeᶜ)
    (hper : ∀ l : P.lattice, Function.Periodic f l)
    (heven : ∀ z, f (-z) = f z) (hpole : HasDoublePoleAtZero f) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z ∉ P.lattice, f z = a * ℘[P] z + b := by
  classical
  obtain ⟨F, hF, hF0, heq⟩ := hpole
  let E : ℂ → ℂ := fun z => (F z + F (-z)) / 2
  have hneg : AnalyticAt ℂ (fun z : ℂ => F (-z)) 0 :=
    hF.fun_comp_of_eq (analyticAt_id.neg) (neg_zero : -(0 : ℂ) = 0)
  have hE : AnalyticAt ℂ E 0 := (hF.add hneg).div_const (c := 2)
  have hE0 : E 0 = F 0 := by dsimp [E]; rw [neg_zero]; ring
  have hneg₀ : Tendsto (fun z : ℂ => -z) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [neg_zero] using
        (continuous_neg.continuousAt (x := (0 : ℂ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using neg_ne_zero.mpr (show z ≠ 0 from hz)
  have heqE : (fun z => z ^ 2 * f z) =ᶠ[𝓝[≠] 0] E := by
    filter_upwards [heq, hneg₀.eventually heq] with z hz hz'
    have hfold : (-z) ^ 2 * f (-z) = z ^ 2 * f z := by rw [heven]; ring
    change (-z) ^ 2 * f (-z) = F (-z) at hz'
    dsimp [E]
    rw [← hz, ← hz', hfold]
    ring
  have hEvenE (z : ℂ) : E (-z) = E z := by dsimp [E]; rw [neg_neg, add_comm]
  have hD : deriv E 0 = 0 := by
    have hd := hE.differentiableAt.hasDerivAt
    have hc := hd.comp_of_eq (0 : ℂ) (hasDerivAt_neg (0 : ℂ)) (neg_zero : -(0 : ℂ) = 0).symm
    have hfun : (E ∘ fun z : ℂ => -z) = E := funext hEvenE
    rw [hfun, mul_neg_one] at hc
    exact CharZero.eq_neg_self_iff.mp (hd.unique hc)
  obtain ⟨G, hG, hTaylor⟩ := hE.exists_eventuallyEq_sum_add_pow_mul 2
  have hTaylor' : ∀ᶠ z in 𝓝 (0 : ℂ), E z = F 0 + z ^ 2 * G z := by
    filter_upwards [hTaylor] with z hz
    simpa [Finset.sum_range_succ, hE0, hD, smul_eq_mul] using hz
  let H : ℂ → ℂ := fun z => G z - F 0 * ℘[P - (0 : ℂ)] z
  have hH : AnalyticAt ℂ H 0 := hG.sub
    (analyticAt_const.fun_mul (P.analyticAt_weierstrassPExcept 0))
  have hmatch : (fun z => f z - F 0 * ℘[P] z) =ᶠ[𝓝[≠] 0] H := by
    filter_upwards [heqE, hTaylor'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hz ht (hn : z ≠ 0)
    have hwp : ℘[P - (0 : ℂ)] z + 1 / z ^ 2 = ℘[P] z := by
      simpa using P.weierstrassPExcept_add (0 : P.lattice) z
    change z ^ 2 * f z = E z at hz
    rw [ht] at hz
    dsimp [H]
    rw [← hwp]
    field_simp
    linear_combination hz
  let g : ℂ → ℂ := fun z => if z ∈ P.lattice then H 0 else f z - F 0 * ℘[P] z
  have hgper (l : P.lattice) (z : ℂ) : g (z + l) = g z := by
    have hm : z + l ∈ P.lattice ↔ z ∈ P.lattice :=
      P.lattice.toAddSubgroup.add_mem_cancel_right l.property
    simp only [g, hm, hper l z, P.weierstrassP_add_coe]
  have hg0 : AnalyticAt ℂ g 0 := by
    apply hH.congr
    have hnear := P.compl_lattice_sdiff_singleton_mem_nhds 0
    have hpunct : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z - F 0 * ℘[P] z = H z := by
      simpa only [Filter.EventuallyEq, eventually_nhdsWithin_iff, mem_compl_iff,
        mem_singleton_iff] using hmatch
    filter_upwards [hnear, hpunct] with z hz hh
    by_cases h : z = 0
    · subst z
      simp [g]
    · have hzl : z ∉ P.lattice := fun hl => hz ⟨hl, h⟩
      simpa only [g, ite_eq_right hzl] using (hh h).symm
  have hg : Differentiable ℂ g := by
    intro z
    by_cases hz : z ∈ P.lattice
    · have htrans : g = fun w : ℂ => g (w - z) := by
        funext w
        simpa using hgper ⟨z, hz⟩ (w - z)
      have han : AnalyticAt ℂ (fun w : ℂ => g (w - z)) z := by
        have h := hg0
        rw [← sub_self z] at h
        exact h.fun_comp (f := fun w : ℂ => w - z) (by fun_prop)
      exact (htrans ▸ han : AnalyticAt ℂ g z).differentiableAt
    · have han : AnalyticAt ℂ (fun w => f w - F 0 * ℘[P] w) z :=
        (hf z hz).sub (analyticAt_const.fun_mul (P.analyticOnNhd_weierstrassP z hz))
      apply (han.congr ?_).differentiableAt
      filter_upwards [P.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      exact (ite_eq_right (show w ∉ P.lattice from hw)).symm
  have hbounded : Bornology.IsBounded (range g) :=
    (IsZLattice.isCompact_range_of_periodic P.lattice g hg.continuous
      (fun z w hw => hgper ⟨w, hw⟩ z)).isBounded
  refine ⟨F 0, H 0, hF0, fun z hz => ?_⟩
  have h := hg.apply_eq_apply_of_bounded hbounded z 0
  simp only [g, ite_eq_right hz, Submodule.zero_mem, ite_true] at h
  linear_combination h

private theorem exists_value_weierstrassP (P : PeriodPair) (x : ℂ) :
    ∃ z ∉ P.lattice, ℘[P] z = x := by
  let h := P.discriminant_ne_zero
  let W := P.weierstrassCurve
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq
    (x ^ 3 + W.a₄ * x + W.a₆) (by decide : 0 < 2)
  have he : W.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simpa [W] using hy
  have hn := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    h.weierstrassCurve_Δ_ne_zero).mp he
  obtain ⟨z, hz⟩ := (P.isUniformization_toPoint h).2.1 (.some x y hn)
  have hout : z ∉ P.lattice := by
    intro hm
    rw [P.toPoint_of_mem h hm] at hz
    exact WeierstrassCurve.Affine.Point.some_ne_zero hn hz.symm
  rw [P.toPoint_of_notMem h hout] at hz
  exact ⟨z, hout, (WeierstrassCurve.Affine.Point.some.inj hz).1⟩

open Polynomial in
/-- An even elliptic function with a double pole and a holomorphic partner off the
lattice on a nonsingular short cubic are the standard lattice coordinates, up to
a single scale. No assumption on the pole part of the partner is needed. -/
theorem shortCubic_coordinates_of_doublePole (P : PeriodPair) {x y : ℂ → ℂ} {a b : ℂ}
    (hx : AnalyticOnNhd ℂ x P.latticeᶜ) (hy : AnalyticOnNhd ℂ y P.latticeᶜ)
    (hper : ∀ l : P.lattice, Function.Periodic x l) (heven : ∀ z, x (-z) = x z)
    (hpole : HasDoublePoleAtZero x)
    (hEq : ∀ z ∉ P.lattice, y z ^ 2 = x z ^ 3 + a * x z + b)
    (hsimple : ∀ r : ℂ, r ^ 3 + a * r + b = 0 → 3 * r ^ 2 + a ≠ 0) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ z ∉ P.lattice,
      x z = u ^ 2 * ℘[P] z ∧ y z = u ^ 3 * (℘'[P] z / 2) := by
  classical
  obtain ⟨c, d, hc, hxd⟩ := affine_weierstrassP_of_even P hx hper heven hpole
  let F : ℂ[X] := X ^ 3 +
    (C (3 * d / c) * X ^ 2 + C ((3 * d ^ 2 + a) / c ^ 2) * X + C ((d ^ 3 + a * d + b) / c ^ 3))
  let G : ℂ[X] := X ^ 3 + (C 0 * X ^ 2 + C (-P.g₂ / 4) * X + C (-P.g₃ / 4))
  have hFm : F.Monic := monic_X_pow_add degree_quadratic_lt
  have hGm : G.Monic := monic_X_pow_add degree_quadratic_lt
  have hFd : F.natDegree = 3 := by
    apply natDegree_eq_of_degree_eq_some
    unfold F
    rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow]
    exact degree_quadratic_lt
  have hGd : G.natDegree = 3 := by
    apply natDegree_eq_of_degree_eq_some
    unfold G
    rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow]
    exact degree_quadratic_lt
  have hFe (r : ℂ) : c ^ 3 * F.eval r = (c * r + d) ^ 3 + a * (c * r + d) + b := by
    simp only [F, eval_add, eval_pow, eval_X, eval_mul, eval_C]
    field_simp
    ring
  have hFder (r : ℂ) : c ^ 2 * F.derivative.eval r = 3 * (c * r + d) ^ 2 + a := by
    simp only [F, derivative_add, derivative_mul, derivative_X_pow, derivative_X, derivative_C,
      zero_mul, zero_add, mul_one, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero,
      show 3 - 1 = (2 : ℕ) by decide, show 2 - 1 = (1 : ℕ) by decide, pow_one]
    field_simp
    ring
  have hFsimple (r : ℂ) (hr : F.IsRoot r) : ¬ F.derivative.IsRoot r := by
    intro hder
    exact hsimple (c * r + d)
      (by simpa only [IsRoot.def.mp hr, mul_zero] using (hFe r).symm)
      (by simpa only [IsRoot.def.mp hder, mul_zero] using (hFder r).symm)
  have hGe (z : ℂ) (hz : z ∉ P.lattice) :
      G.eval (℘[P] z) = (℘'[P] z / 2) ^ 2 := by
    simp only [G, eval_add, eval_pow, eval_X, eval_mul, eval_C, zero_mul, zero_add]
    linear_combination -(P.derivWeierstrassP_sq z hz) / 4
  have hFEq : ∀ z ∉ P.lattice, y z ^ 2 = c ^ 3 * F.eval (℘[P] z) := by
    intro z hz
    rw [hFe, ← hxd z hz, hEq z hz]
  have hroot (r : ℂ) (hr : F.IsRoot r) : G.IsRoot r := by
    obtain ⟨z, hz, hzval⟩ := exists_value_weierstrassP P r
    have hyz : y z = 0 := by
      have h := hFEq z hz
      rw [hzval, IsRoot.def.mp hr, mul_zero] at h
      by_contra hy'
      exact pow_ne_zero 2 hy' h
    have hwp := (P.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
    rw [P.deriv_weierstrassP] at hwp
    have h₁ := (hy z hz).differentiableAt.hasDerivAt.pow 2
    have h₂ := ((F.hasDerivAt (℘[P] z)).comp z hwp).const_mul (c ^ 3)
    have heq : (fun w => y w ^ 2) =ᶠ[𝓝 z] (fun w => c ^ 3 * F.eval (℘[P] w)) := by
      filter_upwards [P.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      exact hFEq w hw
    have hzder := (h₁.congr_of_eventuallyEq heq.symm).unique h₂
    simp only [hyz, show 2 - 1 = (1 : ℕ) by decide, pow_one, mul_zero, zero_mul, hzval] at hzder
    have hwpz : ℘'[P] z = 0 := by
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hzder.symm).resolve_left (pow_ne_zero 3 hc))).resolve_left
        (fun h => hFsimple r hr (IsRoot.def.mpr h))
    exact IsRoot.def.mpr (by simpa [hzval, hwpz] using hGe z hz)
  have hFG : F = G := by
    symm
    apply eq_of_monic_of_dvd_of_natDegree_le hFm hGm _ (by rw [hFd, hGd])
    apply (IsAlgClosed.splits F).dvd_of_roots_le_roots hFm.ne_zero
    rw [Multiset.le_iff_count]
    intro r
    simp only [count_roots]
    by_cases hr : F.IsRoot r
    · have hFle : F.rootMultiplicity r ≤ 1 := by
        apply le_of_not_gt
        exact fun hrm => hFsimple r hr
          ((one_lt_rootMultiplicity_iff_isRoot hFm.ne_zero).mp hrm).2
      exact hFle.trans (Nat.one_le_iff_ne_zero.mpr
        (fun h => hGm.ne_zero (rootMultiplicity_eq_zero_iff.mp h (hroot r hr))))
    · rw [rootMultiplicity_eq_zero hr]
      exact Nat.zero_le _
  have hd : d = 0 := by
    have h := congrArg (fun p : ℂ[X] => p.coeff 2) hFG
    have h' : 3 * d / c = 0 := by simpa [F, G, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
      coeff_C] using h
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp h').resolve_right hc)).resolve_left (by norm_num)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq c (by decide : 0 < 2)
  have hu0 : u ≠ 0 := fun h => hc (by simpa [h] using hu.symm)
  let q : ℂ → ℂ := fun z => u ^ 3 * (℘'[P] z / 2)
  have hq : AnalyticOnNhd ℂ q P.latticeᶜ := fun z hz =>
    analyticAt_const.fun_mul ((P.analyticOnNhd_derivWeierstrassP z hz).div_const (c := 2))
  have hsquares : ∀ z ∉ P.lattice, y z ^ 2 = q z ^ 2 := by
    intro z hz
    rw [hFEq z hz, hFG, hGe z hz, ← hu]
    dsimp [q]
    ring
  have hsign : Set.EqOn y q P.latticeᶜ ∨ Set.EqOn y (fun z => -q z) P.latticeᶜ := by
    by_cases h : Set.EqOn y q P.latticeᶜ
    · exact Or.inl h
    · right
      simp only [Set.EqOn, not_forall] at h
      push Not at h
      obtain ⟨z, hz, hn⟩ := h
      have hconn : IsPreconnected (P.latticeᶜ : Set ℂ) :=
        (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
          (countable_of_Lindelof_of_discrete (X := P.lattice))).2
      apply hy.eqOn_of_preconnected_of_eventuallyEq (fun w hw => (hq w hw).neg) hconn hz
      have hop := (hy z hz).continuousAt.sub (hq z hz).continuousAt
      filter_upwards [P.isClosed_lattice.isOpen_compl.mem_nhds hz,
        hop.eventually_ne (sub_ne_zero.mpr hn)] with w hw hne
      exact (sq_eq_sq_iff_eq_or_eq_neg.mp (hsquares w hw)).resolve_left
        (fun h => hne (sub_eq_zero.mpr h))
  rcases hsign with h | h
  · refine ⟨u, hu0, fun z hz => ⟨?_, h hz⟩⟩
    rw [hxd z hz, hd, add_zero, hu]
  · refine ⟨-u, neg_ne_zero.mpr hu0, fun z hz => ⟨?_, ?_⟩⟩
    · rw [hxd z hz, hd, add_zero, neg_sq, hu]
    · rw [h hz]
      dsimp [q]
      ring

#print axioms hasDoublePoleAtZero_of_localParameter
#print axioms affine_weierstrassP_of_even
#print axioms exists_value_weierstrassP
#print axioms shortCubic_coordinates_of_doublePole

end HDec.CMBranch.CMjBridges
