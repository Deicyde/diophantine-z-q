import ZInQKernel.Contrib.OneProof.RC.AppE.Phase

/-!
# Appendix E: the weight-`3/2` spaces are vector spaces, and the full-space comparison

Lane RC8's genuine definitions `IsHalfIntegralWeightCuspForm`, `hiwCoeff`, `heckeT3`,
`IsInWaldspurgerEigenspace` (`RC/PrintsAnalytic/Waldspurger.lean`). This file proves the
linear algebra that Appendix E uses on them (tex 8029–8039, 8104–8110):

* `hiwForm_periodic` — a form has period `1` (`T ∈ Γ₀(N)`, `θ(z+1) = θ(z)`;
  no nonvanishing of `θ` is used);
* `hiwForm_analyticAt` — its `q`-expansion function is analytic
  at `q = 0` (Mathlib's `analyticAt_cuspFunction_zero`), so the Fourier coefficients are linear:
  `hiwCoeff_add`, `hiwCoeff_smul`, `hiwCoeff_sum`;
* `hiwForm_add`, `hiwForm_smul`, `hiwForm_sum`, and `eigen_add`, `eigen_smul`, `eigen_sum` for
  `IsInWaldspurgerEigenspace` — the full good-Hecke eigenspace `V` is a complex vector space
  ("Keep all old multiplicities", tex 7947);
* `proportional_of_waldspurgerCor2` — **the full-space comparison** (tex 8029–8039): for `f₁, f₂`
  in one eigenspace, `a_{f₁}(D) a_{f₂}(D₀) = a_{f₂}(D) a_{f₁}(D₀)`, from Waldspurger's Corollaire 2
  (lane RC8's PRINT) at `f₁`, `f₂` and `f₁ + f₂`, given `L(E^{(σD₀)}, 1) ≠ 0`. This is the
  manuscript's "proportional coefficient functionals" with the scalar common to every vector;
  the proof replaces the polynomial-ring domain argument by the identity
  `A (x₁y₂ − x₂y₁)² = Σ cᵢ (Cor. 2 at fᵢ)` (provenance (c): same conclusion, shorter route).

Everything here is PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppE

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsAnalytic UpperHalfPlane
  CongruenceSubgroup Filter Function
open scoped MatrixGroups Manifold

/-! ## Period `1` and analyticity at the cusp `∞` -/

theorem T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ Gamma0 N := by
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem T_zpow_neg_one_mem_Gamma0 (N : ℕ) : ModularGroup.T ^ (-1 : ℤ) ∈ Gamma0 N :=
  zpow_mem (T_mem_Gamma0 N) _

theorem thetaFun_vadd_one (z : ℍ) : thetaFun ((1 : ℝ) +ᵥ z) = thetaFun z := by
  unfold thetaFun
  rw [coe_vadd]
  have : (2 : ℂ) * (((1 : ℝ) : ℂ) + (z : ℂ)) = 2 + 2 * (z : ℂ) := by push_cast; ring
  rw [this, jacobiTheta_two_add]

/-- **A half-integral weight form has period `1`** (PROVED): `T = (1 1; 0 1) ∈ Γ₀(N)` has
`d = 1` and `j(T, z) = θ(z+1)/θ(z)`, which is `1` where `θ(z) ≠ 0`; where `θ(z) = 0`, the
transformation laws at `T` and `T⁻¹` give `g(z+1) = 0 = g(z)` (for `k > 0`). -/
theorem hiwForm_periodic {k N : ℕ} {χ : DirichletCharacter ℂ N}
    {g : ℍ → ℂ} (hg : IsHalfIntegralWeightCuspForm k N χ g) (z : ℍ) :
    g ((1 : ℝ) +ᵥ z) = g z := by
  have hT := hg.2.1 ModularGroup.T (T_mem_Gamma0 N) z
  have hT11 : ((ModularGroup.T 1 1 : ℤ) : ZMod N) = 1 := by simp [ModularGroup.T]
  rw [hT11, map_one, one_mul, modular_T_smul] at hT
  unfold thetaMultiplier at hT
  rw [modular_T_smul, thetaFun_vadd_one] at hT
  by_cases hθ : thetaFun z = 0
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hT
    · -- both sides vanish
      have h1 : g ((1 : ℝ) +ᵥ z) = 0 := by
        rw [hT, hθ, div_zero, zero_pow hk.ne', zero_mul]
      have hTi := hg.2.1 (ModularGroup.T ^ (-1 : ℤ)) (T_zpow_neg_one_mem_Gamma0 N)
        ((1 : ℝ) +ᵥ z)
      have hTi11 : (((ModularGroup.T ^ (-1 : ℤ)) 1 1 : ℤ) : ZMod N) = 1 := by
        rw [ModularGroup.coe_T_zpow]
        simp
      have hback : ModularGroup.T ^ (-1 : ℤ) • ((1 : ℝ) +ᵥ z) = z := by
        rw [modular_T_zpow_smul, vadd_vadd]
        push_cast
        simp
      rw [hTi11, map_one, one_mul, hback] at hTi
      unfold thetaMultiplier at hTi
      rw [hback, hθ, zero_div, zero_pow hk.ne', zero_mul] at hTi
      rw [h1, hTi]
  · rw [div_self hθ, one_pow, one_mul] at hT
    exact hT

theorem hiwForm_periodic_comp {k N : ℕ} {χ : DirichletCharacter ℂ N}
    {g : ℍ → ℂ} (hg : IsHalfIntegralWeightCuspForm k N χ g) :
    Periodic (g ∘ ofComplex) (1 : ℝ) :=
  UpperHalfPlane.periodic_comp_ofComplex (hiwForm_periodic hg)

/-- A cusp form tends to `0` at `i∞` (PROVED: the cusp condition at `α = 1`). -/
theorem hiwForm_isZeroAtImInfty {k N : ℕ} {χ : DirichletCharacter ℂ N}
    {g : ℍ → ℂ} (hg : IsHalfIntegralWeightCuspForm k N χ g) : IsZeroAtImInfty g := by
  have h := hg.2.2 1
  simp only [one_smul] at h
  have h' : Tendsto (fun z : ℍ => ‖g z‖) atImInfty (nhds 0) := by
    refine h.congr fun z => ?_
    simp
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h'

theorem hiwForm_mdiff {k N : ℕ} {χ : DirichletCharacter ℂ N}
    {g : ℍ → ℂ} (hg : IsHalfIntegralWeightCuspForm k N χ g) : MDiff g :=
  UpperHalfPlane.mdifferentiable_iff.mpr hg.1

/-- The `q`-expansion function of a half-integral weight cusp form is analytic at `q = 0`
(PROVED, Mathlib's `analyticAt_cuspFunction_zero`). -/
theorem hiwForm_analyticAt {k N : ℕ}
    {χ : DirichletCharacter ℂ N} {g : ℍ → ℂ} (hg : IsHalfIntegralWeightCuspForm k N χ g) :
    AnalyticAt ℂ (cuspFunction 1 g) 0 :=
  analyticAt_cuspFunction_zero one_pos (hiwForm_periodic_comp hg) (hiwForm_mdiff hg)
    (hiwForm_isZeroAtImInfty hg).boundedAtFilter

/-! ## The spaces are vector spaces; the coefficients are linear -/

theorem hiwForm_add {k N : ℕ} {χ : DirichletCharacter ℂ N}
    {f g : ℍ → ℂ} (hf : IsHalfIntegralWeightCuspForm k N χ f)
    (hg : IsHalfIntegralWeightCuspForm k N χ g) : IsHalfIntegralWeightCuspForm k N χ (f + g) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hf.1.add hg.1
  · intro γ hγ z
    simp only [Pi.add_apply, hf.2.1 γ hγ z, hg.2.1 γ hγ z]
    ring
  · intro α
    have h := (hf.2.2 α).add (hg.2.2 α)
    rw [add_zero] at h
    refine squeeze_zero (fun z => by positivity) (fun z => ?_) h
    simp only [Pi.add_apply]
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)

theorem hiwForm_smul {k N : ℕ} {χ : DirichletCharacter ℂ N}
    {g : ℍ → ℂ} (c : ℂ) (hg : IsHalfIntegralWeightCuspForm k N χ g) :
    IsHalfIntegralWeightCuspForm k N χ (c • g) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hg.1.const_smul c
  · intro γ hγ z
    simp only [Pi.smul_apply, smul_eq_mul, hg.2.1 γ hγ z]
    ring
  · intro α
    have h := (hg.2.2 α).const_mul ‖c‖
    rw [mul_zero] at h
    refine h.congr fun z => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    ring

theorem hiwForm_zero (k N : ℕ) (χ : DirichletCharacter ℂ N) :
    IsHalfIntegralWeightCuspForm k N χ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (differentiableOn_const (0 : ℂ))
  · intro γ _ z
    simp
  · intro α
    simp

theorem hiwForm_sum {k N : ℕ} {χ : DirichletCharacter ℂ N} {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, IsHalfIntegralWeightCuspForm k N χ (f i)) :
    IsHalfIntegralWeightCuspForm k N χ (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hiwForm_zero k N χ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hiwForm_add (hiwForm_smul (c a) (hf a (Finset.mem_insert_self a s)))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem hiwCoeff_add {k N : ℕ} {χ χ' : DirichletCharacter ℂ N} {f g : ℍ → ℂ}
    (hf : IsHalfIntegralWeightCuspForm k N χ f) (hg : IsHalfIntegralWeightCuspForm k N χ' g)
    (n : ℕ) : hiwCoeff (f + g) n = hiwCoeff f n + hiwCoeff g n := by
  unfold hiwCoeff
  rw [qExpansion_add (hiwForm_analyticAt hf) (hiwForm_analyticAt hg), map_add]

theorem hiwCoeff_smul {k N : ℕ} {χ : DirichletCharacter ℂ N} {g : ℍ → ℂ}
    (hg : IsHalfIntegralWeightCuspForm k N χ g) (c : ℂ) (n : ℕ) :
    hiwCoeff (c • g) n = c * hiwCoeff g n := by
  unfold hiwCoeff
  rw [qExpansion_smul (hiwForm_analyticAt hg), PowerSeries.coeff_smul, smul_eq_mul]

theorem hiwCoeff_zero (n : ℕ) : hiwCoeff 0 n = 0 := by
  unfold hiwCoeff
  rw [qExpansion_zero, map_zero]

theorem hiwCoeff_sum {k N : ℕ} {χ : DirichletCharacter ℂ N} {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, IsHalfIntegralWeightCuspForm k N χ (f i)) (n : ℕ) :
    hiwCoeff (∑ i ∈ s, c i • f i) n = ∑ i ∈ s, c i * hiwCoeff (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hiwCoeff_zero]
  | insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, IsHalfIntegralWeightCuspForm k N χ (f i) :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      hiwCoeff_add (hiwForm_smul (c a) hfa) (hiwForm_sum s c f hfs),
      hiwCoeff_smul hfa, ih hfs]

/-- `heckeT3` is additive in the coefficient sequence (PROVED). -/
theorem heckeT3_add (N : ℕ) (χ : DirichletCharacter ℂ N) (p : ℕ) (a b : ℕ → ℂ) (n : ℕ) :
    heckeT3 N χ p (a + b) n = heckeT3 N χ p a n + heckeT3 N χ p b n := by
  unfold heckeT3
  split_ifs <;> simp only [Pi.add_apply] <;> ring

/-- `heckeT3` is homogeneous in the coefficient sequence (PROVED). -/
theorem heckeT3_smul (N : ℕ) (χ : DirichletCharacter ℂ N) (p : ℕ) (c : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    heckeT3 N χ p (fun m => c * a m) n = c * heckeT3 N χ p a n := by
  unfold heckeT3
  split_ifs <;> ring

theorem eigen_add {E : WeierstrassCurve ℚ} {N : ℕ}
    {ψ η : DirichletCharacter ℂ N} {f g : ℍ → ℂ} (hf : IsInWaldspurgerEigenspace E N ψ η f)
    (hg : IsInWaldspurgerEigenspace E N ψ η g) : IsInWaldspurgerEigenspace E N ψ η (f + g) := by
  refine ⟨hiwForm_add hf.1 hg.1, fun p hp hpN n => ?_⟩
  have hc : hiwCoeff (f + g) = hiwCoeff f + hiwCoeff g :=
    funext fun m => hiwCoeff_add hf.1 hg.1 m
  rw [hc, heckeT3_add, hf.2 p hp hpN n, hg.2 p hp hpN n, Pi.add_apply]
  ring

theorem eigen_smul {E : WeierstrassCurve ℚ} {N : ℕ}
    {ψ η : DirichletCharacter ℂ N} {g : ℍ → ℂ} (c : ℂ) (hg : IsInWaldspurgerEigenspace E N ψ η g) :
    IsInWaldspurgerEigenspace E N ψ η (c • g) := by
  refine ⟨hiwForm_smul c hg.1, fun p hp hpN n => ?_⟩
  have hc : hiwCoeff (c • g) = fun m => c * hiwCoeff g m :=
    funext fun m => hiwCoeff_smul hg.1 c m
  rw [hc, heckeT3_smul, hg.2 p hp hpN n]
  ring

theorem eigen_sum {E : WeierstrassCurve ℚ} {N : ℕ}
    {ψ η : DirichletCharacter ℂ N} {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, IsInWaldspurgerEigenspace E N ψ η (f i)) :
    IsInWaldspurgerEigenspace E N ψ η (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using hiwForm_zero 3 N ψ, fun p _ _ n => ?_⟩
    simp only [Finset.sum_empty]
    have : hiwCoeff (0 : ℍ → ℂ) = fun _ => 0 := funext hiwCoeff_zero
    rw [this]
    unfold heckeT3
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact eigen_add (eigen_smul (c a) (hf a (Finset.mem_insert_self a s)))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-! ## The full-space comparison (tex 8029–8039) -/

/-- **Proportional coefficient functionals on the whole eigenspace** (tex 8029–8039 and
8104–8110; PROVED from lane RC8's PRINT `WaldspurgerCor2`). Let `f₁, f₂` lie in the full
good-Hecke eigenspace of `E` and `η = ψχ_{−σ}` at a level `N` (`4 ∣ N`), and let `D₀, D` be
positive squarefree, prime to `N`, in one unit squareclass at every prime of `N`, with
`L(E^{(σD₀)}, 1) ≠ 0` (for an entire continuation `F₀`; `F` continues `L(E^{(σD)}, s)`). Then
`a_{f₁}(D) a_{f₂}(D₀) = a_{f₂}(D) a_{f₁}(D₀)`. Corollaire 2 at `f₁`, `f₂` and `f₁ + f₂` gives
`yᵢ² B = xᵢ² A` (`xᵢ = a_{fᵢ}(D)`, `yᵢ = a_{fᵢ}(D₀)`, `A = F₀(1)√D₀ ≠ 0`), and
`A (x₁y₂ − x₂y₁)²` is a linear combination of these three identities. -/
theorem proportional_of_waldspurgerCor2 (hW : WaldspurgerCor2) {E : WeierstrassCurve ℚ}
    (hE : E.IsElliptic) {N : ℕ} (hN : 4 ∣ N) (ψ η : DirichletCharacter ℂ N) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    {f₁ f₂ : ℍ → ℂ} (h₁ : IsInWaldspurgerEigenspace E N ψ η f₁)
    (h₂ : IsInWaldspurgerEigenspace E N ψ η f₂) {D₀ D : ℕ}
    (hD₀ : 0 < D₀) (hD : 0 < D) (hsq₀ : Squarefree D₀) (hsq : Squarefree D)
    (hc₀ : D₀.Coprime N) (hc : D.Coprime N) (hcl : SameUnitClassesAtLevel N D D₀)
    {F₀ F : ℂ → ℂ} (hF₀ : IsLContinuation (qtwist E ((σ * D₀ : ℤ) : ℚ)) F₀)
    (hF : IsLContinuation (qtwist E ((σ * D : ℤ) : ℚ)) F) (hF₀1 : F₀ 1 ≠ 0) :
    hiwCoeff f₁ D * hiwCoeff f₂ D₀ = hiwCoeff f₂ D * hiwCoeff f₁ D₀ := by
  have hW1 := hW E hE N hN ψ η σ hσ hψη f₁ h₁ D₀ D hD₀ hD hsq₀ hsq hc₀ hc hcl F₀ F hF₀ hF
  have hW2 := hW E hE N hN ψ η σ hσ hψη f₂ h₂ D₀ D hD₀ hD hsq₀ hsq hc₀ hc hcl F₀ F hF₀ hF
  have hW3 := hW E hE N hN ψ η σ hσ hψη (f₁ + f₂) (eigen_add h₁ h₂) D₀ D hD₀ hD hsq₀ hsq hc₀ hc hcl
    F₀ F hF₀ hF
  rw [hiwCoeff_add h₁.1 h₂.1, hiwCoeff_add h₁.1 h₂.1] at hW3
  have hA : F₀ 1 * (Real.sqrt D₀ : ℂ) ≠ 0 := by
    refine mul_ne_zero hF₀1 ?_
    have : 0 < Real.sqrt (D₀ : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hD₀)
    exact_mod_cast this.ne'
  have key : F₀ 1 * (Real.sqrt D₀ : ℂ) *
      (hiwCoeff f₁ D * hiwCoeff f₂ D₀ - hiwCoeff f₂ D * hiwCoeff f₁ D₀) ^ 2 = 0 := by
    linear_combination
      -(hiwCoeff f₂ D₀ ^ 2 + hiwCoeff f₁ D₀ * hiwCoeff f₂ D₀) * hW1 -
      (hiwCoeff f₁ D₀ ^ 2 + hiwCoeff f₁ D₀ * hiwCoeff f₂ D₀) * hW2 +
      (hiwCoeff f₁ D₀ * hiwCoeff f₂ D₀) * hW3
  have := (mul_eq_zero.mp key).resolve_left hA
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

end ZInQ.Manuscript.RC.AppE
