import ZInQKernel.Contrib.OneProof.GAGAChart

/-!
# sga1-fix: `uniformizationLeafAll` and `gagaMorphism` from printed leaves

Three leaves of sga1-etale (`SmoothComplexManifoldEtale.lean`) and gaga-chart (`GAGAChart.lean`) are
restated in the form their sources print, and both textbook fields are rebuilt on them.

1. **`SGA1_XII_3_3a`** (SGA 1, Exp. XII, Remarque 3.3(a): if `f` is étale, `f^an` is a local
   isomorphism), topological part only: for `U ⊆ X` affine and `U → 𝔸ⁿ_ℂ` étale, `Q ↦ (fᵢ(Q))` is a
   homeomorphism from a neighbourhood of each `P ∈ U(ℂ)` onto an open subset of `ℂⁿ`. sga1-etale's
   second half (every regular function is near `P` an analytic function of the `fᵢ`) is **proved**
   here from the étaleness alone (`regular_half`): `Γ(X, U)` is standard étale over `ℂ[x]` on a basic
   open `D(s) ∋ P` (Mathlib's `Algebra.IsEtaleAt.exists_isStandardEtale`, Stacks 00UE) and the
   generator of a standard étale algebra is a holomorphic implicit function of `x`
   (`exists_analytic_of_standardEtale`, Mathlib's analytic inverse function theorem). So
   `SGA1_XII_3_3a → SGA1Etale.SGA1_XII_3_1_Etale` (`sga1_XII_3_1_Etale_of_3_3a`).
2. **`SGA1_XII_2_4`** (SGA 1, Exp. XII, Prop. 2.4, "only if"): `X` locally of finite type over `ℂ`
   and preconnected gives `X^an` preconnected. `ConnectedPreconnectedAn` follows
   (`connectedPreconnectedAn_of_2_4`).
3. **`SGA1_XII_4_4`** (GAGA for morphisms, abelian varieties): every morphism of analytic spaces
   `A^an → B^an` is `f^an`. Stated with no atlas: `IsAnMorphism` (continuous for the analytic
   topologies, pulls back holomorphic functions) over `AnFunAt`, the structure sheaf of `X^an`
   (near `P`, `H ∘ (g₁, …, g_k)` with `gⱼ` regular and `H` holomorphic). Proved: in every `IsAnStr`
   atlas the holomorphic functions are exactly `AnFunAt` (`contMDiffAt_iff_anFunAt`) and the
   holomorphic maps are exactly the `IsAnMorphism`s (`contMDiff_iff_isAnMorphism`); `AnFunAt` is the
   pullback of `𝒪_{ℂⁿ}` along étale coordinates (`anFunAt_iff_etale`); sga1-etale's étale atlas
   satisfies `IsAnStr` (`isAnStr_of_3_3a`); hence `GAGAChart ↔ SGA1_XII_4_4`
   (`gagaChart_iff_printed`).

Main theorems: `SGA1Printed.uniformizationLeafAll_of_printed` and
`SGA1Printed.gagaMorphism_of_printed`. Report: `docs/research/sga1-fix.md`.
-/

open scoped Topology Manifold ContDiff
open Filter Polynomial Set CategoryTheory AlgebraicGeometry

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

noncomputable section

namespace SGA1Printed

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
  rw [aeval_def, hom_eval₂, hψ, pfun, Polynomial.eval_map]

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
      FunLike.coe_smul, FunLike.coe_sub, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply,
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
      FunLike.coe_smul, FunLike.coe_sub, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply,
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


/-! ## The regular-functions half, from étaleness -/

open UnifPrinted UnifTopology SGA1Etale

variable {X : Over (Spec (CommRingCat.of ℂ))}

/-- Regular functions are continuous at the points of `U(ℂ)` for the analytic topology. -/
theorem continuousAt_xevalAt_an [LocallyOfFiniteType X.hom] (U : X.left.Opens) (g : Γ(X.left, U))
    {P : CPt X} (hP : XPtIn X P U) :
    @ContinuousAt _ _ (analyticTopology X) _ (XevalAt X U g) P := by
  letI := analyticTopology X
  have h := GAGAAn.continuousOn_xevalAt U g
  rw [classicalTopology_eq_analyticTopology] at h
  exact h.continuousAt ((isOpen_ptIn_an U).mem_nhds hP)

/-- **The regular-functions half of SGA 1 XII 3.3(a), proved.** Let `X` be locally of finite type
over `ℂ`, `U ⊆ X` affine and `f : Fin n → Γ(X, U)` with `ℂ[x₁, …, xₙ] → Γ(X, U)` étale. Then every
regular function `g` on `U` is, near each `P ∈ U(ℂ)`, an analytic function of `f₁, …, fₙ`.
Proof: `Γ(X, U)` is standard étale over `ℂ[x]` on a basic open `D(s) ∋ P` (Mathlib's
`Algebra.IsEtaleAt.exists_isStandardEtale`, Stacks 00UE), and the generator of the standard étale
algebra is an analytic function of `f` near `P` by the holomorphic implicit function theorem
(`exists_analytic_of_standardEtale`). -/
theorem regular_half [LocallyOfFiniteType X.hom] {U : X.left.Opens} {n : ℕ}
    (f : Fin n → Γ(X.left, U)) (hf : (MvPolynomial.eval₂Hom (algC X U) f).Etale)
    (P : CPt X) (hP : XPtIn X P U) (g : Γ(X.left, U)) :
    ∃ h : (Fin n → ℂ) → ℂ, AnalyticAt ℂ h (fun i => XevalAt X U (f i) P) ∧
      ∀ᶠ Q in @nhds _ (analyticTopology X) P,
        XevalAt X U g Q = h (fun i => XevalAt X U (f i) Q) := by
  letI := analyticTopology X
  letI : Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, U) :=
    (MvPolynomial.eval₂Hom (algC X U) f).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(X.left, U) := hf
  set 𝔭 := RingHom.ker (evP P U hP)
  haveI : 𝔭.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s, hs, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := MvPolynomial (Fin n) ℂ) 𝔭
  have hsP : evP P U hP s ≠ 0 := fun h => hs (RingHom.mem_ker.mpr h)
  have Pr := hst.nonempty_standardEtalePresentation.some
  set D := X.left.basicOpen s
  have hDopen : IsOpen {Q : CPt X | XPtIn X Q D} := isOpen_ptIn_an D
  have hPD : XPtIn X P D := (xPtIn_basicOpen_iff P hP s).mpr hsP
  have hDU : ∀ Q, XPtIn X Q D → XPtIn X Q U := fun Q hQ => xPtIn_mono (X.left.basicOpen_le s) hQ
  have hDs : ∀ Q (hQ : XPtIn X Q D), evP Q U (hDU Q hQ) s ≠ 0 := fun Q hQ =>
    (xPtIn_basicOpen_iff Q (hDU Q hQ) s).mp hQ
  classical
  let ev : CPt X → Localization.Away s →+* ℂ := fun Q =>
    if hQ : XPtIn X Q D then IsLocalization.Away.lift s (g := evP Q U (hDU Q hQ)) (Ne.isUnit (hDs Q hQ))
    else IsLocalization.Away.lift s (g := evP P U hP) (Ne.isUnit hsP)
  have hev : ∀ Q (hQ : XPtIn X Q D) (a : Γ(X.left, U)),
      ev Q (algebraMap _ (Localization.Away s) a) = evP Q U (hDU Q hQ) a := by
    intro Q hQ a
    simp only [ev, hQ, ↓reduceDIte]
    exact IsLocalization.Away.lift_eq s _ a
  set y : CPt X → Fin n → ℂ := fun Q i => XevalAt X U (f i) Q with hy
  have hDnhds : {Q : CPt X | XPtIn X Q D} ∈ 𝓝 P := hDopen.mem_nhds hPD
  have hR : ∀ᶠ Q in 𝓝 P, (ev Q).comp (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.Away s)) =
      MvPolynomial.eval (y Q) := by
    filter_upwards [hDnhds] with Q hQ
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ)
        Γ(X.left, U) (Localization.Away s), hev Q hQ]
      change evP Q U _ (MvPolynomial.eval₂ (algC X U) f (MvPolynomial.C c)) = _
      rw [evP_eval₂]
      simp
    · intro i
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ)
        Γ(X.left, U) (Localization.Away s), hev Q hQ]
      change evP Q U _ (MvPolynomial.eval₂ (algC X U) f (MvPolynomial.X i)) = _
      rw [evP_eval₂]
      simp [hy, xevalAt_eq_evP (hDU Q hQ)]
  have hyc : ContinuousAt y P := continuousAt_pi.mpr fun i => continuousAt_xevalAt_an U (f i) hP
  have hxc : ContinuousAt (fun Q => ev Q Pr.x) P := by
    obtain ⟨⟨c, ⟨_, k, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers s) Pr.x
    have hcont : ContinuousAt (fun Q => XevalAt X U c Q / XevalAt X U s Q ^ k) P := by
      refine (continuousAt_xevalAt_an U c hP).div ((continuousAt_xevalAt_an U s hP).pow k) ?_
      rw [xevalAt_eq_evP hP]; exact pow_ne_zero _ hsP
    refine hcont.congr ?_
    filter_upwards [hDnhds] with Q hQ
    have h1 := congrArg (ev Q) hc
    simp only [map_mul, map_pow, hev Q hQ] at h1
    rw [xevalAt_eq_evP (hDU Q hQ), xevalAt_eq_evP (hDU Q hQ), div_eq_iff (pow_ne_zero _ (hDs Q hQ))]
    exact h1.symm
  obtain ⟨h, hh, hev'⟩ := exists_analytic_of_standardEtale Pr P ev y hR hyc hxc
    (algebraMap _ (Localization.Away s) g)
  refine ⟨h, hh, ?_⟩
  filter_upwards [hev', hDnhds] with Q hQ hQD
  rw [xevalAt_eq_evP (hDU Q hQD), ← hev Q hQD]
  exact hQ

/-! ## The restated leaves -/

/-- **LEAF (printed form, special case and consequence): SGA 1, Exp. XII, Remarque 3.3(a)**
(Grothendieck et al., *Revêtements étales et groupe fondamental*, LNM 224, Springer 1971, p. 325 per
the 11-16 review; not read for this statement, locator UNVERIFIED): for a morphism `f` of `ℂ`-schemes
locally of finite type, if `f` is étale then `f^an` is a local isomorphism (of analytic spaces).
Stated for `f : U → 𝔸ⁿ_ℂ` given by `f₁, …, fₙ ∈ Γ(X, U)` (the ring map `ℂ[x₁, …, xₙ] → Γ(X, U)`,
`xᵢ ↦ fᵢ`, is Mathlib's `RingHom.Etale`), `U` an affine open of a `ℂ`-scheme `X` locally of finite
type, and only for the underlying map of topological spaces: the underlying space of `U^an` is the
open subset `U(ℂ)` of `X(ℂ)` with the analytic topology (`analyticTopology`, SGA 1 XII 1.1), that of
`(𝔸ⁿ)^an` is `ℂⁿ`, and `f^an` is `Q ↦ (fᵢ(Q))`; a local isomorphism of ringed spaces is in particular
a local homeomorphism: every `P ∈ U(ℂ)` has an open neighbourhood mapped homeomorphically onto an
open subset of `ℂⁿ`. The structure-sheaf part is not assumed: for regular functions it is proved
(`regular_half`). -/
def SGA1_XII_3_3a : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), LocallyOfFiniteType X.hom →
    ∀ (U : X.left.Opens), IsAffineOpen U → ∀ (n : ℕ) (f : Fin n → Γ(X.left, U)),
      (MvPolynomial.eval₂Hom (algC X U) f).Etale →
      letI := analyticTopology X
      ∀ P : CPt X, XPtIn X P U →
        ∃ e : OpenPartialHomeomorph (CPt X) (Fin n → ℂ), P ∈ e.source ∧
          e.source ⊆ {Q | XPtIn X Q U} ∧ ∀ Q ∈ e.source, e Q = fun i => XevalAt X U (f i) Q

/-- sga1-etale's leaf (both halves) from the topological leaf and the proved regular half. -/
theorem sga1_XII_3_1_Etale_of_3_3a (hL : SGA1_XII_3_3a) : SGA1Etale.SGA1_XII_3_1_Etale := by
  intro X hX U hU n f hf P hP
  haveI := hX
  exact ⟨hL X hX U hU n f hf P hP, fun g => regular_half f hf P hP g⟩

/-- **LEAF (printed form): SGA 1, Exp. XII, Prop. 2.4, "only if"** (LNM 224, 1971; locator per the
11-16 review, UNVERIFIED): for `X` locally of finite type over `ℂ`, if `X` is connected then `X^an`
is connected. "Connected" as Mathlib's `PreconnectedSpace` on both sides (Bourbaki's *connexe*; the
empty case is trivial under either convention, since `X = ∅` gives `X(ℂ) = ∅`), the underlying space
of `X^an` being `X(ℂ)` with `analyticTopology` (SGA 1 XII 1.1). -/
def SGA1_XII_2_4 : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), LocallyOfFiniteType X.hom → PreconnectedSpace X.left →
    @PreconnectedSpace (CPt X) (analyticTopology X)

/-- sga1-etale's `ConnectedPreconnectedAn` (`X` proper and irreducible) from `SGA1_XII_2_4`. -/
theorem connectedPreconnectedAn_of_2_4 (h : SGA1_XII_2_4) : SGA1Etale.ConnectedPreconnectedAn :=
  fun X hP hI => by haveI := hI; exact h X hP.toLocallyOfFiniteType inferInstance

/-- **Main theorem 1: `UniformizationLeafAll` from printed leaves**: Mumford's theorem
(`MumfordComplexTorus`), SGA 1 XII 3.3(a) (topological part), GAGA's compactness (`ProperCompactAn`)
and SGA 1 XII 2.4, through sga1-etale's `uniformizationLeafAll_of_etale`. -/
theorem uniformizationLeafAll_of_printed (hM : MumfordComplexTorus) (hL : SGA1_XII_3_3a)
    (hPC : ProperCompactAn) (hC : SGA1_XII_2_4) :
    BPAnalytic.Uniformization.UniformizationLeafAll :=
  SGA1Etale.uniformizationLeafAll_of_etale hM (sga1_XII_3_1_Etale_of_3_3a hL) hPC
    (connectedPreconnectedAn_of_2_4 hC)

/-! ## The structure sheaf of `X^an` and morphisms of analytic spaces -/

open PkgI3 (AbVar)

/-- **Holomorphic functions on `X^an` near `P`**: `F` agrees near `P` (analytic topology) with
`H ∘ (g₁, …, g_k)` for regular functions `gⱼ` on an open `U ∋ P` and `H` holomorphic at `(gⱼ(P))`.
These are the sections of the structure sheaf of `X^an` (SGA 1 XII 1.1) when `X^an` is reduced, as
functions on `X(ℂ)`: for `U ↪ 𝔸^k` affine, `U^an` is the analytic subspace of `ℂ^k` cut out by the
equations of `U`, so its sections are locally restrictions of holomorphic functions of the
coordinates; and `H ∘ g` is the pullback of `H` along `g^an : U^an → ℂ^k`. For `X` smooth this is
also the pullback of `𝒪_{ℂⁿ}` along étale coordinates (`anFunAt_iff_etale`), and the holomorphic
functions of any `IsAnStr` atlas (`contMDiffAt_iff_anFunAt`). -/
def AnFunAt (X : Over (Spec (CommRingCat.of ℂ))) (F : CPt X → ℂ) (P : CPt X) : Prop :=
  ∃ (U : X.left.Opens) (k : ℕ) (g : Fin k → Γ(X.left, U)) (H : (Fin k → ℂ) → ℂ),
    XPtIn X P U ∧ AnalyticAt ℂ H (fun i => XevalAt X U (g i) P) ∧
    ∀ᶠ Q in @nhds _ (analyticTopology X) P, F Q = H (fun i => XevalAt X U (g i) Q)

/-- `F` is a section of the structure sheaf of `X^an` on `W`. -/
def AnFunOn (X : Over (Spec (CommRingCat.of ℂ))) (W : Set (CPt X)) (F : CPt X → ℂ) : Prop :=
  ∀ P ∈ W, AnFunAt X F P

/-- **Morphisms of analytic spaces `X^an → Y^an`** (for `X^an`, `Y^an` reduced): maps continuous for
the analytic topologies that pull back holomorphic functions (`AnFunOn`) on every open to holomorphic
functions. A morphism of reduced complex spaces is determined by its underlying map, and a continuous
map is one exactly when it pulls back holomorphic functions (`F^♯ s = s ∘ F`). For smooth `X`, `Y`
these are the holomorphic maps of any `IsAnStr` atlases (`contMDiff_iff_isAnMorphism`). -/
def IsAnMorphism (X Y : Over (Spec (CommRingCat.of ℂ))) (F : CPt X → CPt Y) : Prop :=
  @Continuous _ _ (analyticTopology X) (analyticTopology Y) F ∧
  ∀ (W : Set (CPt Y)) (s : CPt Y → ℂ), @IsOpen _ (analyticTopology Y) W → AnFunOn Y W s →
    AnFunOn X (F ⁻¹' W) (s ∘ F)

/-- **LEAF (printed form, special case): GAGA for morphisms, for complex abelian varieties.** SGA 1
(LNM 224, 1971), Exp. XII, Thm. 4.4 and its corollary on morphisms: for `X` proper over `ℂ` and `Y`
locally of finite type, `Hom(X, Y) → Hom(X^an, Y^an)` is bijective; Serre, *Géométrie algébrique et
géométrie analytique*, Ann. Inst. Fourier 6 (1956), for projective varieties (abelian varieties are
projective). Locators UNVERIFIED. Special case `X = A`, `Y = B` abelian varieties (reduced, so a
morphism `A^an → B^an` is an `IsAnMorphism`), surjectivity only: every morphism of analytic spaces
`F : A^an → B^an` is `f^an`, i.e. `F P = P ≫ f` on `ℂ`-points, for a morphism of `ℂ`-schemes
`f : A → B`. -/
def SGA1_XII_4_4 : Prop :=
  ∀ (A B : AbVar ℂ) (F : CPt A.X → CPt B.X), IsAnMorphism A.X B.X F →
    ∃ f : A.X ⟶ B.X, ∀ P, F P = P ≫ f

section Str

attribute [local instance] analyticTopology

variable {Y : Over (Spec (CommRingCat.of ℂ))}

/-- A function holomorphic on `X^an` is holomorphic in any `IsAnStr` atlas. -/
theorem contMDiffAt_of_anFunAt [LocallyOfFiniteType X.hom] {m : ℕ}
    [ChartedSpace (Fin m → ℂ) (CPt X)] (hX : GAGAAn.IsAnStr X m) {F : CPt X → ℂ} {P : CPt X}
    (hF : AnFunAt X F P) : ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, ℂ) ω F P := by
  obtain ⟨U, k, g, H, hPU, hH, hev⟩ := hF
  have hG : ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin k → ℂ) ω (fun Q i => XevalAt X U (g i) Q) P :=
    contMDiffAt_pi_module_iff.mpr fun i =>
      (hX.2.1 U (g i) P hPU).contMDiffAt ((isOpen_ptIn_an U).mem_nhds hPU)
  have hH' : ContMDiffAt 𝓘(ℂ, Fin k → ℂ) 𝓘(ℂ, ℂ) ω H (fun i => XevalAt X U (g i) P) :=
    hH.contDiffAt.contMDiffAt
  exact (hH'.comp P hG).congr_of_eventuallyEq hev

/-- A function holomorphic in an `IsAnStr` atlas is holomorphic on `X^an`. -/
theorem anFunAt_of_contMDiffAt {m : ℕ}
    [ChartedSpace (Fin m → ℂ) (CPt X)] (hX : GAGAAn.IsAnStr X m) {F : CPt X → ℂ} {P : CPt X}
    (hF : ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, ℂ) ω F P) : AnFunAt X F P := by
  obtain ⟨hMan, -, hcoords⟩ := hX
  have := hMan
  obtain ⟨U, f, hPU, hloc⟩ := hcoords P
  have hLP : hloc.localInverse (fun i => XevalAt X U (f i) P) = P :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hinv := hloc.contMDiffAt_localInverse
  have hFL : ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, ℂ) ω (F ∘ hloc.localInverse)
      (fun i => XevalAt X U (f i) P) := by
    refine ContMDiffAt.comp _ ?_ hinv
    rw [hLP]; exact hF
  refine ⟨U, m, f, F ∘ hloc.localInverse, hPU, hFL.contDiffAt.analyticAt, ?_⟩
  filter_upwards [hloc.localInverse_eventuallyEq_left] with Q hQ
  exact (congrArg F hQ).symm

/-- **`IsAnStr` atlases carry exactly the holomorphic functions of `X^an`.** -/
theorem contMDiffAt_iff_anFunAt [LocallyOfFiniteType X.hom] {m : ℕ}
    [ChartedSpace (Fin m → ℂ) (CPt X)] (hX : GAGAAn.IsAnStr X m) (F : CPt X → ℂ) (P : CPt X) :
    ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, ℂ) ω F P ↔ AnFunAt X F P :=
  ⟨anFunAt_of_contMDiffAt hX, contMDiffAt_of_anFunAt hX⟩

/-- Regular functions are holomorphic on `X^an`. -/
theorem anFunOn_xevalAt (U : X.left.Opens) (g : Γ(X.left, U)) :
    AnFunOn X {Q | XPtIn X Q U} (XevalAt X U g) := fun _ hQ =>
  ⟨U, 1, fun _ => g, fun v => v 0, hQ,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _,
    Eventually.of_forall fun _ => rfl⟩

/-- A holomorphic map in `IsAnStr` atlases is a morphism of analytic spaces. -/
theorem isAnMorphism_of_contMDiff [LocallyOfFiniteType Y.hom] {n m : ℕ}
    [ChartedSpace (Fin n → ℂ) (CPt X)] [ChartedSpace (Fin m → ℂ) (CPt Y)]
    (hX : GAGAAn.IsAnStr X n) (hY : GAGAAn.IsAnStr Y m) {F : CPt X → CPt Y}
    (hF : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω F) : IsAnMorphism X Y F := by
  refine ⟨hF.continuous, fun W s hW hs P hP => ?_⟩
  have h1 := contMDiffAt_of_anFunAt hY (hs (F P) hP)
  exact anFunAt_of_contMDiffAt hX (h1.comp P (hF P))

/-- A morphism of analytic spaces is holomorphic in `IsAnStr` atlases. -/
theorem contMDiff_of_isAnMorphism [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {n m : ℕ} [ChartedSpace (Fin n → ℂ) (CPt X)] [ChartedSpace (Fin m → ℂ) (CPt Y)]
    (hX : GAGAAn.IsAnStr X n) (hY : GAGAAn.IsAnStr Y m) {F : CPt X → CPt Y}
    (hF : IsAnMorphism X Y F) : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω F := by
  intro P
  refine GAGAAn.contMDiffAt_of_regular hY F P hF.1.continuousAt fun U g hU => ?_
  exact contMDiffAt_of_anFunAt hX (hF.2 _ _ (isOpen_ptIn_an U) (anFunOn_xevalAt U g) P hU)

/-- **Holomorphic maps in `IsAnStr` atlases are exactly the morphisms of analytic spaces.** -/
theorem contMDiff_iff_isAnMorphism [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {n m : ℕ} [ChartedSpace (Fin n → ℂ) (CPt X)] [ChartedSpace (Fin m → ℂ) (CPt Y)]
    (hX : GAGAAn.IsAnStr X n) (hY : GAGAAn.IsAnStr Y m) (F : CPt X → CPt Y) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω F ↔ IsAnMorphism X Y F :=
  ⟨isAnMorphism_of_contMDiff hX hY, contMDiff_of_isAnMorphism hX hY⟩

/-- **Holomorphic functions of `X^an` are the pullbacks of holomorphic functions along étale
coordinates** (`X` smooth): the structure sheaf of `X^an` near `P` is the pullback of `𝒪_{ℂⁿ}` along
`f^an`, as the local isomorphism of SGA 1 XII 3.3(a) says. -/
theorem anFunAt_iff_etale (hL : SGA1_XII_3_3a) [Smooth X.hom] (F : CPt X → ℂ) (P : CPt X) :
    AnFunAt X F P ↔ ∃ (U : X.left.Opens) (_ : IsAffineOpen U) (n : ℕ) (f : Fin n → Γ(X.left, U)),
      (MvPolynomial.eval₂Hom (algC X U) f).Etale ∧ XPtIn X P U ∧
      ∃ h : (Fin n → ℂ) → ℂ, AnalyticAt ℂ h (cf f P) ∧ ∀ᶠ Q in 𝓝 P, F Q = h (cf f Q) := by
  constructor
  · rintro ⟨U, k, g, H, hPU, hH, hev⟩
    obtain ⟨V, hV, hxV, n, f, hf⟩ := exists_etale_chart (X := X) (P.left.base default)
    have hPV : XPtIn X P V := (xPtIn_iff _ _).mpr hxV
    have hrep := fun j => regFun_local (sga1_XII_3_1_Etale_of_3_3a hL) hV f hf (g j) hPV hPU
    choose h hh hevh using hrep
    refine ⟨V, hV, n, f, hf, hPV, fun v => H (fun j => h j v), ?_, ?_⟩
    · have he : (fun j => h j (cf f P)) = fun j => XevalAt X U (g j) P :=
        funext fun j => ((hevh j).self_of_nhds).symm
      refine AnalyticAt.comp (g := H) (f := fun v => fun j => h j v) ?_ (AnalyticAt.pi hh)
      rw [he]; exact hH
    · filter_upwards [hev, eventually_all.mpr hevh] with _ hQ hQ'
      rw [hQ]
      exact congrArg H (funext fun j => hQ' j)
  · rintro ⟨U, -, n, f, -, hPU, h, hh, hev⟩
    exact ⟨U, n, f, h, hPU, hh, hev⟩

end Str

/-- sga1-etale's atlas of étale charts satisfies `IsAnStr`, from the restated leaf. -/
theorem isAnStr_of_3_3a (hL : SGA1_XII_3_3a) (X : Over (Spec (CommRingCat.of ℂ)))
    [Smooth X.hom] [IsProper X.hom] [IrreducibleSpace X.left] :
    letI := analyticTopology X
    ∃ (n : ℕ) (_ : ChartedSpace (Fin n → ℂ) (CPt X)), GAGAAn.IsAnStr X n :=
  GAGAAn.isAnStr_of_etale (sga1_XII_3_1_Etale_of_3_3a hL) X

/-- The atlas-free GAGA leaf gives gaga-chart's chart form. -/
theorem gagaChart_of_printed (h : SGA1_XII_4_4) : GAGAAn.GAGAChart := by
  intro A B n m cA cB hA hB F hF
  exact h A B F (isAnMorphism_of_contMDiff hA hB hF)

/-- Conversely, the chart form gives the atlas-free form (atlases from the restated étale leaf). -/
theorem printed_of_gagaChart (hG : GAGAAn.GAGAChart) (hL : SGA1_XII_3_3a) : SGA1_XII_4_4 := by
  intro A B F hF
  letI := analyticTopology A.X
  letI := analyticTopology B.X
  obtain ⟨n, cA, hA⟩ := isAnStr_of_3_3a hL A.X
  obtain ⟨m, cB, hB⟩ := isAnStr_of_3_3a hL B.X
  exact hG A B n m cA cB hA hB F (contMDiff_of_isAnMorphism hA hB hF)

theorem gagaChart_iff_printed (hL : SGA1_XII_3_3a) : GAGAAn.GAGAChart ↔ SGA1_XII_4_4 :=
  ⟨fun h => printed_of_gagaChart h hL, gagaChart_of_printed⟩

/-- **Main theorem 2: `GAGAMorphism` from printed leaves**: those of main theorem 1 and GAGA for
morphisms of abelian varieties (`SGA1_XII_4_4`), through gaga-chart's `gagaMorphism_of_gagaChart`. -/
theorem gagaMorphism_of_printed (hM : MumfordComplexTorus) (hL : SGA1_XII_3_3a)
    (hPC : ProperCompactAn) (hC : SGA1_XII_2_4) (hG : SGA1_XII_4_4) :
    ZInQ.HomLattice.GAGAMorphism :=
  GAGAAn.gagaMorphism_of_gagaChart (uniformizationLeafAll_of_printed hM hL hPC hC)
    (gagaChart_of_printed hG)


end SGA1Printed
