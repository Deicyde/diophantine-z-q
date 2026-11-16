import ZInQKernel.Contrib.OneProof.GAGAChart

open scoped Topology
open Filter Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace SGA1Fix

variable {n : ℕ}

/-- The polynomial function `(y, τ) ↦ p(y; τ)` of `p ∈ ℂ[y₁, …, yₙ][τ]`. -/
def pfun (p : (MvPolynomial (Fin n) ℂ)[X]) (q : (Fin n → ℂ) × ℂ) : ℂ :=
  (p.map (MvPolynomial.eval q.1)).eval q.2

theorem pfun_eq_sum (p : (MvPolynomial (Fin n) ℂ)[X]) (q : (Fin n → ℂ) × ℂ) :
    pfun p q = ∑ i ∈ Finset.range (p.natDegree + 1),
      MvPolynomial.eval q.1 (p.coeff i) * q.2 ^ i := by
  unfold pfun
  rw [eval_eq_sum_range' (lt_of_le_of_lt natDegree_map_le (Nat.lt_succ_self _))]
  simp [coeff_map]

theorem analyticAt_pfun (p : (MvPolynomial (Fin n) ℂ)[X]) (q : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (pfun p) q := by
  have : pfun p = fun q : (Fin n → ℂ) × ℂ => ∑ i ∈ Finset.range (p.natDegree + 1),
      MvPolynomial.eval q.1 (p.coeff i) * q.2 ^ i := funext (pfun_eq_sum p)
  rw [this]
  refine Finset.analyticAt_fun_sum (𝕜 := ℂ) (f := fun i (q : (Fin n → ℂ) × ℂ) => MvPolynomial.eval q.1 (p.coeff i) * q.2 ^ i) _ fun i _ => ?_
  refine AnalyticAt.mul ?_ ((analyticAt_snd (𝕜 := ℂ) (E := Fin n → ℂ) (F := ℂ) (p := q)).pow i)
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (A := ℂ) (B := ℂ)
    (f := fun q : (Fin n → ℂ) × ℂ => q.1) (z := q)
    (fun j => ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)).analyticAt q) (p.coeff i)
  simpa [MvPolynomial.coe_aeval_eq_eval] using h

theorem ev_aeval {S : Type*} [CommRing S] [Algebra (MvPolynomial (Fin n) ℂ) S] (ψ : S →+* ℂ)
    (y : Fin n → ℂ) (hψ : ψ.comp (algebraMap (MvPolynomial (Fin n) ℂ) S) = MvPolynomial.eval y)
    (x : S) (p : (MvPolynomial (Fin n) ℂ)[X]) :
    ψ (aeval x p) = pfun p (y, ψ x) := by
  rw [aeval_def, hom_eval₂, hψ, pfun, eval_map]

theorem hasDerivAt_pfun_snd (p : (MvPolynomial (Fin n) ℂ)[X]) (y : Fin n → ℂ) (τ : ℂ) :
    HasDerivAt (fun t => pfun p (y, t)) (pfun (derivative p) (y, τ)) τ := by
  simp only [pfun]
  rw [← derivative_map]
  exact (p.map _).hasDerivAt τ

/-- **Holomorphic implicit functions for a standard étale algebra.** Let `S` be standard étale over
`ℂ[y₁, …, yₙ]` with generator `x`, and let `ev z : S → ℂ` be ring maps, parametrized by `z ∈ Z`,
lying over the points `y z ∈ ℂⁿ` near `z₀`. If `y` and `z ↦ ev z x` are continuous at `z₀`, then
every `a ∈ S` satisfies `ev z a = h (y z)` near `z₀` for a function `h` analytic at `y z₀`. -/
theorem exists_analytic_of_standardEtale {S : Type*} [CommRing S]
    [Algebra (MvPolynomial (Fin n) ℂ) S] (P : StandardEtalePresentation (MvPolynomial (Fin n) ℂ) S)
    {Z : Type*} [TopologicalSpace Z] (z₀ : Z) (ev : Z → S →+* ℂ) (y : Z → Fin n → ℂ)
    (hR : ∀ᶠ z in 𝓝 z₀, (ev z).comp (algebraMap (MvPolynomial (Fin n) ℂ) S) =
      MvPolynomial.eval (y z))
    (hy : ContinuousAt y z₀) (hx : ContinuousAt (fun z => ev z P.x) z₀) (a : S) :
    ∃ h : (Fin n → ℂ) → ℂ, AnalyticAt ℂ h (y z₀) ∧ ∀ᶠ z in 𝓝 z₀, ev z a = h (y z) := by
  set τ₀ := ev z₀ P.x with hτ₀
  set y₀ := y z₀ with hy₀
  have hR₀ := hR.self_of_nhds
  set Φ : (Fin n → ℂ) × ℂ → (Fin n → ℂ) × ℂ := fun q => (q.1, pfun P.f q) with hΦ
  have hFa : AnalyticAt ℂ (pfun P.f) (y₀, τ₀) := analyticAt_pfun _ _
  have hΦa : AnalyticAt ℂ Φ (y₀, τ₀) := analyticAt_fst.prod hFa
  set D := fderiv ℂ (pfun P.f) (y₀, τ₀) with hDdef
  have hD : HasFDerivAt (pfun P.f) D (y₀, τ₀) := hFa.differentiableAt.hasFDerivAt
  have hc : D (0, 1) = pfun (derivative P.f) (y₀, τ₀) := by
    have h1 : HasDerivAt (fun t : ℂ => ((y₀, t) : (Fin n → ℂ) × ℂ)) ((0 : Fin n → ℂ), (1 : ℂ)) τ₀ :=
      (hasDerivAt_const τ₀ y₀).prodMk (hasDerivAt_id τ₀)
    have h2 := hD.comp_hasDerivAt τ₀ h1
    exact h2.unique (hasDerivAt_pfun_snd _ _ _)
  have hc0 : D (0, 1) ≠ 0 := by
    rw [hc, ← ev_aeval (ev z₀) y₀ hR₀]
    exact (P.hasMap.isUnit_derivative_f.map (ev z₀)).ne_zero
  set c := D (0, 1) with hcdef
  have hDsplit : ∀ u t, D (u, t) = D (u, 0) + t * c := by
    intro u t
    have : ((u, t) : (Fin n → ℂ) × ℂ) = (u, 0) + t • ((0 : Fin n → ℂ), (1 : ℂ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  set L0 : ((Fin n → ℂ) × ℂ) →L[ℂ] ((Fin n → ℂ) × ℂ) :=
    (ContinuousLinearMap.fst ℂ _ _).prod D with hL0
  set Linv : ((Fin n → ℂ) × ℂ) →L[ℂ] ((Fin n → ℂ) × ℂ) :=
    (ContinuousLinearMap.fst ℂ _ _).prod (c⁻¹ • (ContinuousLinearMap.snd ℂ _ _ -
      D.comp ((ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ).comp (ContinuousLinearMap.fst ℂ _ _))))
    with hLinv
  have hl : Function.LeftInverse Linv L0 := by
    rintro ⟨u, t⟩
    simp only [hL0, hLinv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inl_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [hDsplit u t]
    ext
    · rfl
    · simp only
      field_simp
      ring
  have hr : Function.RightInverse Linv L0 := by
    rintro ⟨u, w⟩
    simp only [hL0, hLinv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inl_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [hDsplit u]
    ext
    · rfl
    · simp only
      field_simp
      ring
  set Le : ((Fin n → ℂ) × ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ) :=
    ContinuousLinearEquiv.equivOfInverse L0 Linv hl hr with hLe
  have hΦd : HasFDerivAt Φ L0 (y₀, τ₀) := hasFDerivAt_fst.prodMk hD
  have hstrict : HasStrictFDerivAt Φ (Le : ((Fin n → ℂ) × ℂ) →L[ℂ] ((Fin n → ℂ) × ℂ)) (y₀, τ₀) := by
    have := hΦa.hasStrictFDerivAt
    rw [hΦd.fderiv] at this
    exact this
  set e := hstrict.toOpenPartialHomeomorph Φ with he
  have hsrc : (y₀, τ₀) ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hsymm : AnalyticAt ℂ e.symm (e (y₀, τ₀)) :=
    e.analyticAt_symm' (i := Le) hsrc (by simpa [he] using hΦa) (by simp [he, hΦd.fderiv, hLe])
  have hΦ₀ : Φ (y₀, τ₀) = (y₀, 0) := by
    simp only [hΦ, Prod.mk.injEq, true_and]
    rw [← ev_aeval (ev z₀) y₀ hR₀, P.hasMap.1, map_zero]
  have hecoe : ∀ q, e q = Φ q := fun q => rfl
  have he₀ : e.symm (y₀, 0) = (y₀, τ₀) := by
    rw [← hΦ₀, ← hecoe]; exact e.left_inv hsrc
  -- the root `ev z x` is `e.symm (y z, 0)` near `z₀`
  have hT : Tendsto (fun z => (y z, ev z P.x)) (𝓝 z₀) (𝓝 (y₀, τ₀)) := hy.prodMk_nhds hx
  have key : ∀ᶠ z in 𝓝 z₀, e.symm (y z, 0) = (y z, ev z P.x) := by
    filter_upwards [hR, hT.eventually (e.open_source.mem_nhds hsrc)] with z hz hzs
    have : Φ (y z, ev z P.x) = (y z, 0) := by
      simp only [hΦ, Prod.mk.injEq, true_and]
      rw [← ev_aeval (ev z) (y z) hz, P.hasMap.1, map_zero]
    rw [← this, ← hecoe]; exact e.left_inv hzs
  obtain ⟨p, m, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x a
  set j : (Fin n → ℂ) → (Fin n → ℂ) × ℂ := fun y' => (y', (e.symm (y', 0)).2) with hj
  refine ⟨fun y' => pfun p (j y') / pfun P.g (j y') ^ m, ?_, ?_⟩
  · have hin : AnalyticAt ℂ (fun y' : Fin n → ℂ => ((y', (0 : ℂ)) : (Fin n → ℂ) × ℂ)) y₀ :=
      analyticAt_id.prod analyticAt_const
    have hsymm' : AnalyticAt ℂ e.symm ((fun y' : Fin n → ℂ => ((y', (0 : ℂ)) : (Fin n → ℂ) × ℂ)) y₀) := by
      have : e (y₀, τ₀) = (y₀, 0) := by rw [hecoe, hΦ₀]
      rw [this] at hsymm
      exact hsymm
    have h1 := AnalyticAt.comp (g := e.symm)
      (f := fun y' : Fin n → ℂ => ((y', (0 : ℂ)) : (Fin n → ℂ) × ℂ)) hsymm' hin
    have h2 := AnalyticAt.comp (g := fun q : (Fin n → ℂ) × ℂ => q.2)
      (f := fun y' : Fin n → ℂ => e.symm (y', (0 : ℂ))) analyticAt_snd h1
    have hjA : AnalyticAt ℂ j y₀ := analyticAt_id.prod h2
    have hj₀ : j y₀ = (y₀, τ₀) := by simp only [hj, he₀]
    refine AnalyticAt.div ((analyticAt_pfun p _).comp hjA) (((analyticAt_pfun P.g _).comp hjA).pow m) ?_
    simp only [hj₀]
    refine pow_ne_zero _ ?_
    rw [← ev_aeval (ev z₀) y₀ hR₀]
    exact (P.hasMap.2.map (ev z₀)).ne_zero
  · filter_upwards [hR, key] with z hz hk
    have hjz : j (y z) = (y z, ev z P.x) := by simp only [hj, hk]
    simp only [hjz]
    have hp' := congrArg (ev z) hp
    rw [map_mul, map_pow, ev_aeval (ev z) (y z) hz, ev_aeval (ev z) (y z) hz] at hp'
    have hne : pfun P.g (y z, ev z P.x) ≠ 0 := by
      rw [← ev_aeval (ev z) (y z) hz]
      exact (P.hasMap.2.map (ev z)).ne_zero
    rw [eq_div_iff (pow_ne_zero _ hne)]
    exact hp'

end SGA1Fix
