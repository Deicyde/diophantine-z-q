import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.FunctionField
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Classification
import Mathlib.NumberTheory.ModularForms.NormTrace

/-! A proof of the printed form of P1, `ℂ(X₀(N)) = ℂ(j, j_N)`, from the complex cusp
classification of the base (`ModFnClassify.complexCuspClassification`: the `q`-expansion
at `i∞` of a `Γ₀(N)`-invariant meromorphic function on `ℍ`, meromorphic at every cusp, lies in
the field generated over `ℂ` by the expansions of `j` and `j_N`).

Steps. A meromorphic function `g` on `X₀(N)` has, at each cusp `σ(∞)`, a meromorphic germ in
the strict local parameter: `g ∘ σ` is periodic with the strict width (it is a weight-zero
slash-invariant form for the conjugate group), holomorphic for large `Im τ`, and of moderate
growth. At `i∞` this gives its expansion `s`. The classification puts `s` in
`ℂ(j, j_N)`, so `s · Q(j, j_N) = P(j, j_N)` for complex polynomials `P`, `Q` with
`Q(j, j_N) ≠ 0`. Comparing convergent expansions, `g · Q(j, j_N) = P(j, j_N)` near `i∞`, and
since the upper half-plane is connected this holds on every punctured germ. -/

noncomputable section

open Filter UpperHalfPlane ModularCurve ShimuraPointDict Complex
open scoped Topology TensorProduct MatrixGroups ModularForm

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open X0Model ModFnField ModFnClassify

variable (N : ℕ) [NeZero N]

/-- A meromorphic function on `X₀(N)` as a weight-zero slash-invariant form for `Γ₀(N)`. -/
def x0SlashForm {g : ℂ → ℂ} (hg : IsX0Function N g) :
    SlashInvariantForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 0 where
  toFun τ := g τ
  slash_action_eq' γ hγ := by
    obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
    funext τ
    change ((fun τ : ℍ => g τ) ∣[(0 : ℤ)] γ₀) τ = g τ
    rw [ModularForm.SL_slash_apply, zpow_neg, zpow_zero, inv_one, mul_one]
    exact hg.invariant γ₀ hγ₀ τ

/-- The translate of `g` by `σ` is periodic with the strict width at `σ(∞)`. -/
theorem periodic_translate {g : ℂ → ℂ} (hg : IsX0Function N g) (σ : SL(2, ℤ)) :
    Function.Periodic ((fun τ : ℍ => g (σ • τ : ℍ)) ∘ ofComplex)
      (translatedLevel N σ).strictWidthInfty := by
  let Γ' := translatedLevel N σ
  have : Γ'.IsArithmetic := by
    simpa [Γ', translatedLevel, ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv,
      Matrix.SpecialLinearGroup.map_mapGL]
      using Subgroup.IsArithmetic.conj
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
        (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹
  have h := SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate (x0SlashForm N hg) (Matrix.SpecialLinearGroup.mapGL ℝ σ))
    Γ'.strictWidthInfty_mem_strictPeriods
  have he : ⇑(SlashInvariantForm.translate (x0SlashForm N hg)
      (Matrix.SpecialLinearGroup.mapGL ℝ σ)) = fun τ : ℍ => g (σ • τ : ℍ) := by
    funext τ
    rw [SlashInvariantForm.coe_translate]
    change ((fun τ : ℍ => g τ) ∣[(0 : ℤ)] σ) τ = g (σ • τ : ℍ)
    rw [ModularForm.SL_slash_apply, zpow_neg, zpow_zero, inv_one, mul_one]
  rw [he] at h
  exact h

theorem translatedLevel_width_pos (σ : SL(2, ℤ)) : 0 < (translatedLevel N σ).strictWidthInfty := by
  let Γ' := translatedLevel N σ
  have : Γ'.IsArithmetic := by
    simpa [Γ', translatedLevel, ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv,
      Matrix.SpecialLinearGroup.map_mapGL]
      using Subgroup.IsArithmetic.conj
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
        (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹
  exact Γ'.strictWidthInfty_pos

/-- At every cusp, `g` has a meromorphic germ in the strict local parameter. -/
theorem cuspGerm_translate {g : ℂ → ℂ} (hg : IsX0Function N g) (σ : SL(2, ℤ)) :
    CuspGerm (translatedLevel N σ).strictWidthInfty (fun τ : ℍ => g (σ • τ : ℍ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hw := translatedLevel_width_pos N σ
  apply cuspGerm_of_periodic_growth hw (periodic_translate N hg σ) (hg.cusp_holomorphic σ)
  exact cuspGrowth_changeWidth hN hw (hg.cusp_growth σ)

/-- The expansion of `g` at `i∞`. -/
theorem exists_realizes {g : ℂ → ℂ} (hg : IsX0Function N g) :
    ∃ s : LaurentSeries ℂ, Realizes s (fun τ : ℍ => g τ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  have hper : Function.Periodic ((fun τ : ℍ => g τ) ∘ ofComplex) 1 :=
    UpperHalfPlane.periodic_comp_ofComplex fun τ => by
      rw [← UpperHalfPlane.modular_T_smul]
      exact hg.invariant _ hT τ
  have hdiff : ∀ᶠ z : ℂ in comap Complex.im atTop,
      DifferentiableAt ℂ ((fun τ : ℍ => g τ) ∘ ofComplex) z := by
    have h := hg.cusp_holomorphic 1
    simp only [one_smul] at h
    exact h
  have hgrowth : CuspGrowth (N : ℝ) (fun τ : ℍ => g τ) := by
    have h := hg.cusp_growth 1
    simp only [one_smul] at h
    exact h
  exact cuspGerm_realizes
    (cuspGerm_of_periodic_growth one_pos hper hdiff (cuspGrowth_changeWidth hN one_pos hgrowth))

/-- The analytic function `τ ↦ P(j(τ), j_N(τ))`. -/
def polyFun (P : MvPolynomial (Fin 2) ℂ) (z : ℂ) : ℂ :=
  MvPolynomial.eval ![jFunction z, jNFunction N z] P

/-- The Laurent series `P(j, j_N)`. -/
def polySeries (P : MvPolynomial (Fin 2) ℂ) : LaurentSeries ℂ :=
  MvPolynomial.aeval ![jqModC ℂ, jqNModC ℂ N] P

theorem realizes_poly (P : MvPolynomial (Fin 2) ℂ) :
    Realizes (polySeries N P) (fun τ : ℍ => polyFun N P τ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [polySeries, polyFun, MvPolynomial.aeval_C, MvPolynomial.eval_C]
    exact Realizes.const c
  | add p q hp hq =>
    simp only [polySeries, polyFun, map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [polySeries, polyFun, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    refine hp.mul ?_
    fin_cases i
    · exact realizes_j
    · exact realizes_jN N

theorem analyticOnNhd_polyFun (P : MvPolynomial (Fin 2) ℂ) :
    AnalyticOnNhd ℂ (polyFun N P) {z : ℂ | 0 < z.im} := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro z _
    unfold polyFun
    simp only [MvPolynomial.eval_C]
    exact analyticAt_const
  | add p q hp hq =>
    intro z hz
    unfold polyFun
    simp only [map_add]
    exact (hp z hz).add (hq z hz)
  | mul_X p i hp =>
    intro z hz
    unfold polyFun
    simp only [map_mul, MvPolynomial.eval_X]
    refine (hp z hz).mul ?_
    fin_cases i
    · exact analyticOn_j z hz
    · exact analyticOn_jN N z hz

theorem meromorphicIncl_polyGerm (τ : ℍ) (P : MvPolynomial (Fin 2) ℂ) :
    meromorphicIncl (τ : ℂ) (polyGerm N τ P) = (polyFun N P : PuncturedGerm (τ : ℂ)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    unfold polyFun
    simp only [polyGerm, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
    rfl
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]
    unfold polyFun
    simp only [map_add]
    rfl
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    unfold polyFun
    simp only [map_mul, MvPolynomial.eval_X]
    rw [show (fun z => MvPolynomial.eval ![jFunction z, jNFunction N z] p *
        ![jFunction z, jNFunction N z] i) =
        (fun z => MvPolynomial.eval ![jFunction z, jNFunction N z] p) *
          (fun z => ![jFunction z, jNFunction N z] i) from rfl, Germ.coe_mul]
    congr 1
    simp only [polyGerm, MvPolynomial.eval₂Hom_X']
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, jGerm, jField, fieldGerm_j]
      exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => by simp [jFunction])
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        jNGerm, jNField]
      rw [fieldGerm_jN]
      rfl

/-- **P1, printed form, proved.** `ℂ(X₀(N)) = ℂ(j, j_N)`, from the complex cusp
classification of the base. -/
theorem dsFunctionFieldX0_proof : DSFunctionFieldX0 := by
  intro N _ g hg
  obtain ⟨s, hs⟩ := exists_realizes N hg
  have hsT : ∃ T : ℝ, ∀ τ : ℍ, T < τ.im →
      HasSum (fun m : ℤ => s.coeff m * Function.Periodic.qParam 1 τ ^ m) (g τ) := by
    obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hs
    exact ⟨A, fun τ hτ => hA τ hτ.le⟩
  have hmem := complexCuspClassification N g s hg.meromorphicOn hg.invariant
    (fun σ => cuspGerm_translate N hg σ) hsT
  have hrange : ({jqModC ℂ, jqNModC ℂ N} : Set (LaurentSeries ℂ)) =
      Set.range ![jqModC ℂ, jqNModC ℂ N] := by
    ext x
    simp [or_comm]
  rw [modularFunctionFieldC, hrange, IntermediateField.mem_adjoin_range_iff] at hmem
  obtain ⟨r, q, hrq⟩ := hmem
  -- polynomials with `s · Q = P` and `Q ≠ 0`
  obtain ⟨P, Q, hQ, hsPQ⟩ : ∃ P Q : MvPolynomial (Fin 2) ℂ, polySeries N Q ≠ 0 ∧
      s * polySeries N Q = polySeries N P := by
    by_cases hq : polySeries N q = 0
    · refine ⟨0, 1, by simp [polySeries], ?_⟩
      have : s = 0 := by rw [hrq]; change _ / polySeries N q = 0; rw [hq, div_zero]
      simp [this, polySeries]
    · refine ⟨r, q, hq, ?_⟩
      rw [hrq]
      exact div_mul_cancel₀ _ hq
  refine ⟨P, Q, fun τ => ⟨?_, ?_⟩⟩
  · -- `Q(j, j_N)` has nonzero germ everywhere
    intro h0
    apply hQ
    have hz : (polyFun N Q : PuncturedGerm (τ : ℂ)) = 0 := by
      rw [← meromorphicIncl_polyGerm, h0, map_zero]
    have hev : polyFun N Q =ᶠ[𝓝 (τ : ℂ)] 0 :=
      ((analyticOnNhd_polyFun N Q τ τ.im_pos).frequently_zero_iff_eventually_zero).mp
        ((Germ.coe_eq.mp hz).frequently)
    have hall := (analyticOnNhd_polyFun N Q).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_im_gt 0).isPreconnected τ.im_pos hev
    have hR : Realizes (polySeries N Q) (fun _ : ℍ => (0 : ℂ)) := by
      have h := realizes_poly N Q
      unfold Realizes at h ⊢
      filter_upwards [h] with σ hσ
      have h0 := hall σ.im_pos
      simp only [Pi.zero_apply] at h0
      rwa [h0] at hσ
    have h0' : Realizes (0 : LaurentSeries ℂ) (fun _ : ℍ => (0 : ℂ)) := by
      simpa using Realizes.const (0 : ℂ)
    exact hR.eq_of_eventuallyEq h0' EventuallyEq.rfl
  · -- `g · Q(j, j_N) = P(j, j_N)` on every punctured germ
    rw [meromorphicIncl_polyGerm, meromorphicIncl_polyGerm]
    have hR1 : Realizes (polySeries N P) (fun τ : ℍ => g τ * polyFun N Q τ) := by
      rw [← hsPQ]; exact hs.mul (realizes_poly N Q)
    have hR2 := realizes_poly N P
    obtain ⟨A, hA⟩ := (atImInfty_mem _).mp (hR1.and hR2)
    let F : ℂ → ℂ := fun z => g z * polyFun N Q z - polyFun N P z
    have hFm : MeromorphicOn F {z : ℂ | 0 < z.im} := fun z hz =>
      ((hg.meromorphicOn z hz).mul (analyticOnNhd_polyFun N Q z hz).meromorphicAt).sub
        (analyticOnNhd_polyFun N P z hz).meromorphicAt
    let z₀ : ℂ := ((max A 0 + 1 : ℝ) : ℂ) * Complex.I
    have hz₀ : 0 < z₀.im := by simp [z₀]; positivity
    have hF0 : F =ᶠ[𝓝 z₀] 0 := by
      have hopen : IsOpen {z : ℂ | max A 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds (show max A 0 < z₀.im by simp [z₀])] with z hz
      have hzpos : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz
      obtain ⟨h1, h2⟩ := hA ⟨z, hzpos⟩ (le_trans (le_max_left _ _) hz.le)
      have := h1.unique h2
      simp only [F, Pi.zero_apply]
      change g z * polyFun N Q z - polyFun N P z = 0
      rw [sub_eq_zero]
      exact this
    have htop : meromorphicOrderAt F z₀ = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr (hF0.filter_mono nhdsWithin_le_nhds)
    have hconn : IsConnected {z : ℂ | 0 < z.im} :=
      ⟨⟨Complex.I, by simp⟩, (convex_halfSpace_im_gt 0).isPreconnected⟩
    have hallTop : meromorphicOrderAt F (τ : ℂ) = ⊤ := by
      by_contra hne
      have := (hFm.exists_meromorphicOrderAt_ne_top_iff_forall hconn).mp
        ⟨⟨τ, τ.im_pos⟩, hne⟩ ⟨z₀, hz₀⟩
      exact this htop
    have hFev := meromorphicOrderAt_eq_top_iff.mp hallTop
    rw [← Germ.coe_mul]
    exact Germ.coe_eq.mpr (hFev.mono fun z hz => sub_eq_zero.mp hz)

/-- **P1, Lean reading, proved.** -/
theorem p1_proof : P1 N := p1_of_dsFunctionFieldX0 N dsFunctionFieldX0_proof

end ZInQ.Manuscript.RC.CuspFormDifferentials
