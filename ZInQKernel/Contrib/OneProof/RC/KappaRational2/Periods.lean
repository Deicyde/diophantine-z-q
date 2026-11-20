import ZInQKernel.Contrib.RC53Assist.NewformPeriods.Transport
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.EichlerIntegral.Transformation
import ZInQKernel.RouteK.Rank.LFunctionCd
import Mathlib.NumberTheory.ModularForms.NormTrace

/-! Compare two admissible scales without rechoosing the normalization
of tex 1825–1828. The period comparison is proved here. -/

noncomputable section

open Filter Topology UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup ConjAct
open ModularForm
open scoped MatrixGroups ModularForm Manifold Pointwise
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.RC53Assist.NewformPeriods

namespace ZInQ.Manuscript.RC.KappaRational2

private theorem primitive_tendsto_translate {N : ℕ} [NeZero N]
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (δ : SL(2, ℤ)) :
    ∃ c : ℂ, Tendsto (fun τ : ℍ => eichlerPotential f (δ • τ)) atImInfty (𝓝 c) := by
  let Γ := (Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  let Γ' := toConjAct (mapGL ℝ δ)⁻¹ • Γ
  have : Γ'.IsArithmetic := by
    simpa [Γ', ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv, map_mapGL]
      using Subgroup.IsArithmetic.conj Γ (mapGL ℚ δ)⁻¹
  let g := CuspForm.translate f (mapGL ℝ δ)
  have hg : ⇑g = ⇑f ∣[(2 : ℤ)] δ := by
    rw [CuspForm.coe_translate, SL_slash, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
  let A : ℂ := (-2 * Real.pi * Complex.I) *
    TauCeti.cuspIntegral g (mapGL ℚ δ⁻¹ • OnePoint.infty) OnePoint.infty
  have hform (τ : ℍ) : eichlerPotential f (δ • τ) =
      TauCeti.eichlerIntegral Γ'.strictWidthInfty 1 g τ - A := by
    have he := TauCeti.CuspFormClass.eichlerIntegral_slash_apply
      (n := 0) (by norm_num : (2 : ℤ) = (0 : ℕ) + 2)
      f (by norm_num : (0 : ℝ) < 1) (TauCeti.one_mem_strictPeriods_Gamma0_map N)
      g Γ'.strictWidthInfty_pos Γ'.strictWidthInfty_mem_strictPeriods δ hg τ
    simpa [eichlerPotential, A, SL_slash_apply] using he
  have hz : IsZeroAtImInfty (TauCeti.eichlerIntegral Γ'.strictWidthInfty 1 g) :=
    TauCeti.isZeroAtImInfty_eichlerIntegral Γ'.strictWidthInfty_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex g Γ'.strictWidthInfty_mem_strictPeriods)
      (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g) 0
  refine ⟨-A, ?_⟩
  simp only [hform]
  simpa only [zero_sub] using
    (show Tendsto _ atImInfty (𝓝 (0 : ℂ)) from hz).sub (tendsto_const_nhds (x := A))

/-- The periods of a nonzero cusp form cannot all become integers after
multiplication by a nonzero complex constant. -/
theorem no_integral_period_scaling {N : ℕ} [NeZero N]
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (hf : f ≠ 0)
    {a : ℂ} (ha : a ≠ 0)
    (hint : ∀ γ ∈ Gamma0 N, ∀ τ : ℍ,
      ∃ n : ℤ, a * (eichlerPotential f (γ • τ) - eichlerPotential f τ) = n) : False := by
  let A : ℂ := 2 * Real.pi * Complex.I * a
  have hA : A ≠ 0 := by simp [A, ha, Real.pi_ne_zero]
  let F : ℍ → ℂ := fun τ => Complex.exp (A * eichlerPotential f τ)
  have hFd : MDiff F := by
    have hExp : MDiff Complex.exp := mdifferentiable_iff_differentiable.mpr
      Complex.differentiable_exp
    exact hExp.comp ((mdifferentiable_eichlerPotential f).const_smul A)
  let g : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 0 := {
    toFun := F
    slash_action_eq' := by
      rintro _ ⟨γ, hγ, rfl⟩
      rw [← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← SL_slash]
      funext τ
      simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]
      obtain ⟨n, hn⟩ := hint γ hγ τ
      have h : A * eichlerPotential f (γ • τ) =
          A * eichlerPotential f τ + n * (2 * Real.pi * Complex.I) := by
        dsimp only [A]
        linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hn
      simp only [F, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    holo' := hFd
    bdd_at_cusps' := by
      intro c hc
      have hc' := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
      obtain ⟨δ, hδ⟩ := isCusp_SL2Z_iff'.mp hc'
      refine (OnePoint.isBoundedAt_iff_exists_SL2Z hc').mpr ⟨δ, hδ.symm, ?_⟩
      obtain ⟨z, hz⟩ := primitive_tendsto_translate f δ
      have h : Tendsto (fun τ : ℍ => F (δ • τ)) atImInfty (𝓝 (Complex.exp (A * z))) :=
        Complex.continuous_exp.continuousAt.tendsto.comp ((tendsto_const_nhds (x := A)).mul hz)
      have hb : IsBoundedAtImInfty (fun τ : ℍ => F (δ • τ)) :=
        Asymptotics.isBigO_const_of_tendsto h (one_ne_zero : (1 : ℝ) ≠ 0)
      simpa only [SL_slash_def, neg_zero, zpow_zero, mul_one] using hb }
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero g
  have hc' : ∀ τ : ℍ, F τ = c := fun τ => congrFun hc τ
  apply hf
  ext τ
  have hm := UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_eichlerPotential f)
  have hτ : (0 : ℝ) < (τ : ℂ).im := τ.im_pos
  have hd := (hm _ hτ).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hτ)
  have hdF := (hd.hasDerivAt.const_mul A).cexp
  have hcF : (fun z : ℂ => Complex.exp (A * (eichlerPotential f ∘ ofComplex) z)) =
      fun _ => c := funext fun z => hc' (ofComplex z)
  rw [hcF] at hdF
  have hh := hdF.unique (hasDerivAt_const (τ : ℂ) c)
  have hzero : deriv (eichlerPotential f ∘ ofComplex) (τ : ℂ) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (Complex.exp_ne_zero _))).resolve_left hA
  have hff := congrFun (normalizedDeriv_eichlerPotential f) τ
  simpa [Derivative.normalizedDerivOfComplex, hzero] using hff.symm

/-- The integral subgroup generated by the scaled periods of the primitive. -/
def periodSubmodule (N : ℕ) (f : ℍ → ℂ) (r : ℂ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {z | ∃ γ ∈ Gamma0 N, ∃ τ : ℍ,
    z = r * (eichlerPotential f (γ • τ) - eichlerPotential f τ)}

private theorem lattice_submodule_alternatives (Lat : PeriodPair) (P : Submodule ℤ ℂ)
    (hPL : P ≤ Lat.lattice) :
    (∃ d : ℤ, d ≠ 0 ∧ ∀ w ∈ Lat.lattice, (d : ℂ) * w ∈ P) ∨
      (∃ a : ℂ, a ≠ 0 ∧ ∀ w ∈ P, ∃ n : ℤ, a * w = n) := by
  by_cases h : ∃ (u v : ℂ) (a b c e : ℤ), u ∈ P ∧ v ∈ P ∧
      (a : ℂ) * Lat.ω₁ + b * Lat.ω₂ = u ∧ (c : ℂ) * Lat.ω₁ + e * Lat.ω₂ = v ∧
      a * e - b * c ≠ 0
  · obtain ⟨u, v, a, b, c, e, hu, hv, hu', hv', hdet⟩ := h
    have h₁ : ((a * e - b * c : ℤ) : ℂ) * Lat.ω₁ ∈ P := by
      have H := P.sub_mem (P.smul_mem e hu) (P.smul_mem b hv)
      rw [zsmul_eq_mul, zsmul_eq_mul, ← hu', ← hv'] at H
      convert H using 1
      push_cast
      ring
    have h₂ : ((a * e - b * c : ℤ) : ℂ) * Lat.ω₂ ∈ P := by
      have H := P.sub_mem (P.smul_mem a hv) (P.smul_mem c hu)
      rw [zsmul_eq_mul, zsmul_eq_mul, ← hu', ← hv'] at H
      convert H using 1
      push_cast
      ring
    refine Or.inl ⟨_, hdet, fun w hw => ?_⟩
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hw
    have H := P.add_mem (P.smul_mem m h₁) (P.smul_mem n h₂)
    simp only [zsmul_eq_mul] at H
    convert H using 1
    push_cast
    ring
  · right
    by_cases hP : ∃ u ∈ P, u ≠ (0 : ℂ)
    · obtain ⟨u, hu, hu0⟩ := hP
      obtain ⟨a, b, hu'⟩ := PeriodPair.mem_lattice.mp (hPL hu)
      have hprop (w : ℂ) (hw : w ∈ P) (c e : ℤ)
          (hw' : (c : ℂ) * Lat.ω₁ + e * Lat.ω₂ = w) :
          (a : ℂ) * e = (b : ℂ) * c := by
        have hh : a * e - b * c = 0 := by
          by_contra hh
          exact h ⟨u, w, a, b, c, e, hu, hw, hu', hw', hh⟩
        exact_mod_cast (sub_eq_zero.mp hh)
      by_cases ha : a = 0
      · have hb : b ≠ 0 := by rintro rfl; simp [ha] at hu'; exact hu0 hu'.symm
        refine ⟨(b : ℂ) / u, div_ne_zero (by exact_mod_cast hb) hu0, fun w hw => ?_⟩
        obtain ⟨c, e, hw'⟩ := PeriodPair.mem_lattice.mp (hPL hw)
        refine ⟨e, ?_⟩
        have H := hprop w hw c e hw'
        have heq : (b : ℂ) * w = (e : ℂ) * u := by
          rw [← hu', ← hw']
          linear_combination -Lat.ω₁ * H
        rw [div_mul_eq_mul_div, heq, mul_div_cancel_right₀ _ hu0]
      · refine ⟨(a : ℂ) / u, div_ne_zero (by exact_mod_cast ha) hu0, fun w hw => ?_⟩
        obtain ⟨c, e, hw'⟩ := PeriodPair.mem_lattice.mp (hPL hw)
        refine ⟨c, ?_⟩
        have heq : (a : ℂ) * w = (c : ℂ) * u := by
          rw [← hu', ← hw']
          linear_combination Lat.ω₂ * hprop w hw c e hw'
        rw [div_mul_eq_mul_div, heq, mul_div_cancel_right₀ _ hu0]
    · push Not at hP
      exact ⟨1, one_ne_zero, fun w hw => ⟨0, by simp [hP w hw]⟩⟩

/-- The scaled periods contain a nonzero integer multiple of the full
Weierstrass lattice. Equivalently their subgroup has finite index there. -/
theorem scaled_periods_clear_lattice {N : ℕ} [NeZero N]
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (hf : f ≠ 0)
    {Lat : PeriodPair} {r : ℂ} (hr : IsParamScale N f Lat r) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ w ∈ Lat.lattice, (d : ℂ) * w ∈ periodSubmodule N f r := by
  have hP : periodSubmodule N f r ≤ Lat.lattice :=
    Submodule.span_le.mpr (by rintro _ ⟨γ, hγ, τ, rfl⟩; exact hr.2 γ hγ τ)
  refine (lattice_submodule_alternatives Lat _ hP).resolve_right ?_
  rintro ⟨a, ha, hint⟩
  refine no_integral_period_scaling f hf (mul_ne_zero ha hr.1) (fun γ hγ τ => ?_)
  rw [mul_assoc]
  exact hint _ (Submodule.subset_span ⟨γ, hγ, τ, rfl⟩)

/-- A reference rational scale for the same normalized form and lattice
forces rationality of the original scale, by the non-CM multiplier condition. -/
theorem rational_of_reference_scale {N : ℕ} [NeZero N]
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (hf : f ≠ 0)
    {Lat : PeriodPair} (hNC : IsNonCMLattice Lat) {κ : ℂ} (hκ : IsParamScale N f Lat κ)
    (href : ∃ r : ℚ, IsParamScale N f Lat (r : ℂ)) :
    ∃ c : ℚ, (c : ℂ) = κ := by
  obtain ⟨r, hr⟩ := href
  obtain ⟨d, hd, hP⟩ := scaled_periods_clear_lattice f hf hr
  let a : ℂ := κ / (r : ℂ)
  let m : ℂ →ₗ[ℤ] ℂ := (LinearMap.mulLeft ℂ a).restrictScalars ℤ
  have hmap : periodSubmodule N f (r : ℂ) ≤ Lat.lattice.comap m := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, hγ, τ, rfl⟩
    change a * ((r : ℂ) * _) ∈ Lat.lattice
    rw [← mul_assoc, div_mul_cancel₀ κ hr.1]
    exact hκ.2 γ hγ τ
  obtain ⟨n, hn⟩ := hNC (a * (d : ℂ)) (fun w hw => by
    rw [mul_assoc]
    exact hmap (hP w hw))
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  refine ⟨(n : ℚ) * r / (d : ℚ), ?_⟩
  push_cast
  dsimp [a] at hn
  field_simp [hr.1] at hn
  apply (div_eq_iff hdC).mpr
  linear_combination -hn

/-- The reference-scale comparison for the normalized elliptic Fourier coefficients. -/
theorem rational_of_matching_coeffs (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hNC : IsNonCMLattice Lat) {κ : ℂ} (hκ : IsParamScale N f Lat κ)
    (href : ∃ r : ℚ, IsParamScale N f Lat (r : ℂ)) :
    ∃ c : ℚ, (c : ℂ) = κ := by
  apply rational_of_reference_scale f _ hNC hκ href
  intro hz
  have h := hf 1 one_pos
  rw [hz] at h
  simp [FunLike.coe_zero, qExpansion_zero,
    (ZInQ.Literature.isMultiplicative_LFunction E).map_one] at h

end ZInQ.Manuscript.RC.KappaRational2
