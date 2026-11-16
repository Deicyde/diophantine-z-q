import ZInQKernel.Contrib.OneProof.UniformizationTopology

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace SGA1Etale

open UnifPrinted UnifTopology

variable {X : Over (Spec (CommRingCat.of ℂ))}

/-- Restriction to a basic open commutes with the coordinate ring map. -/
theorem eval₂Hom_res {U : X.left.Opens} (s : Γ(X.left, U)) {n : ℕ} (f : Fin n → Γ(X.left, U)) :
    MvPolynomial.eval₂Hom (algC X (X.left.basicOpen s)) (fun i => res (X.left.basicOpen_le s) (f i)) =
      (X.left.presheaf.map (homOfLE (X.left.basicOpen_le s)).op).hom.comp
        (MvPolynomial.eval₂Hom (algC X U) f) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.coe_comp, Function.comp_apply]
    simp only [algC]
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]
  · intro i
    simp [res]

/-- Étale coordinates restrict to basic opens. -/
theorem etale_res {U : X.left.Opens} (hU : IsAffineOpen U) (s : Γ(X.left, U)) {n : ℕ}
    (f : Fin n → Γ(X.left, U)) (hf : (MvPolynomial.eval₂Hom (algC X U) f).Etale) :
    (MvPolynomial.eval₂Hom (algC X (X.left.basicOpen s))
      (fun i => res (X.left.basicOpen_le s) (f i))).Etale := by
  rw [eval₂Hom_res]
  refine RingHom.Etale.stableUnderComposition _ _ hf ?_
  let _ := (X.left.presheaf.map (homOfLE (X.left.basicOpen_le s)).op).hom.toAlgebra
  have := hU.isLocalization_basicOpen s
  exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway s)

/-- **Smooth implies locally étale over affine space** (Mathlib's
`Smooth.exists_isStandardSmooth` and `RingHom.IsStandardSmooth.exists_etale_mvPolynomial`). -/
theorem exists_etale_chart [Smooth X.hom] (x : X.left) :
    ∃ (U : X.left.Opens), IsAffineOpen U ∧ x ∈ U ∧ ∃ (n : ℕ) (f : Fin n → Γ(X.left, U)),
      (MvPolynomial.eval₂Hom (algC X U) f).Etale := by
  obtain ⟨U', hU', V, hV, hxV, e, hst⟩ := Smooth.exists_isStandardSmooth X.hom x
  obtain rfl : U' = ⊤ := eq_top_iff.mpr fun y _ => by
    rw [Subsingleton.elim y (X.hom.base x)]; exact e hxV
  obtain ⟨n, g, hgC, hg⟩ := hst.exists_etale_mvPolynomial
  refine ⟨V, hV, hxV, n, fun i => g (MvPolynomial.X i), ?_⟩
  have heq : MvPolynomial.eval₂Hom (algC X V) (fun i => g (MvPolynomial.X i)) =
      g.comp (MvPolynomial.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.coe_comp,
        Function.comp_apply, MvPolynomial.map_C]
      rw [← RingHom.comp_apply g MvPolynomial.C, hgC]
      rfl
    · intro i
      simp
  rw [heq]
  refine RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective ?_) hg
  exact (MvPolynomial.mapEquiv (Fin n)
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv).bijective

/-- **A nonempty open of a `ℂ`-scheme locally of finite type has a `ℂ`-point** (Hilbert's
Nullstellensatz, Mathlib's `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`). -/
theorem exists_cPt_of_mem [LocallyOfFiniteType X.hom] {V : X.left.Opens} {x : X.left}
    (hx : x ∈ V) : ∃ P : CPt X, XPtIn X P V := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType X.hom (inferInstance)
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by rw [Scheme.Hom.preimage_top]; exact le_top)
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := by
    intro y
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom y, ?_⟩
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ (Scheme.ΓSpecIso _).inv).hom y = y
    rw [Iso.hom_inv_id]; rfl
  have hft' : (algC X W).FiniteType :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ hsurj)
  letI := (algC X W).toAlgebra
  obtain ⟨k, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft'
  set f : Fin k → Γ(X.left, W) := fun i => φ (MvPolynomial.X i) with hfdef
  have hgen : Generates W f := by
    intro y
    obtain ⟨p, hp⟩ := hφ y
    refine ⟨p, ?_⟩
    rw [← hp]
    conv_rhs => rw [MvPolynomial.aeval_unique φ]
    rfl
  have hnt : Nontrivial Γ(X.left, W) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h10 : X.left.basicOpen (1 : Γ(X.left, W)) = X.left.basicOpen (0 : Γ(X.left, W)) := by
      rw [Subsingleton.elim (1 : Γ(X.left, W)) 0]
    rw [Scheme.basicOpen_one, Scheme.basicOpen_zero] at h10
    have : x ∈ (⊥ : X.left.Opens) := h10 ▸ hxW
    exact this
  set I := RingHom.ker (MvPolynomial.eval₂Hom (algC X W) f)
  have hI : I ≠ ⊤ := RingHom.ker_ne_top _
  obtain ⟨w, hw⟩ : (MvPolynomial.zeroLocus ℂ I).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h2 := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) I
    rw [h, MvPolynomial.vanishingIdeal_empty] at h2
    exact hI (Ideal.radical_eq_top.mp h2.symm)
  have hwz : w ∈ zeroLocus f := fun p hp => by
    have := hw p (RingHom.mem_ker.mpr hp)
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  rw [← range_coord hW f hgen] at hwz
  obtain ⟨P, -⟩ := hwz
  exact ⟨P.1, xPtIn_mono hWV P.2⟩

/-! ## The leaf -/

/-- **LEAF (SGA 1, Exp. XII, Prop. 3.1, étale clause, with the analytic space of XII 1.1).**
Let `X` be a `ℂ`-scheme locally of finite type, `U ⊆ X` an affine open and `f₁, …, fₙ ∈ Γ(X, U)`
such that `U → 𝔸ⁿ_ℂ` (the ring map `ℂ[x₁, …, xₙ] → Γ(X, U)`, `xᵢ ↦ fᵢ`) is étale. Then the analytic
map `U^an → ℂⁿ` is étale, i.e. a local isomorphism of analytic spaces: near each `P ∈ U(ℂ)`,
(1) `Q ↦ (fᵢ(Q))ᵢ` is a homeomorphism from an open neighbourhood of `P` in `X(ℂ)` (analytic
topology) onto an open subset of `ℂⁿ`, and (2) every regular function on `U` is, near `P`, a
holomorphic function of `f₁, …, fₙ`. SGA 1 (Grothendieck, *Revêtements étales et groupe
fondamental*, LNM 224, 1971), Exp. XII, §1 (construction of `X^an`, 1.1) and Prop. 3.1
(`f` étale iff `f^an` étale), with "étale" for analytic spaces meaning local isomorphism; locators
UNVERIFIED. `analyticTopology X` is the topology of `X^an` (unif-topology). -/
def SGA1_XII_3_1_Etale : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), LocallyOfFiniteType X.hom →
    ∀ (U : X.left.Opens), IsAffineOpen U → ∀ (n : ℕ) (f : Fin n → Γ(X.left, U)),
      (MvPolynomial.eval₂Hom (algC X U) f).Etale →
      letI := analyticTopology X
      ∀ P : CPt X, XPtIn X P U →
        (∃ e : OpenPartialHomeomorph (CPt X) (Fin n → ℂ), P ∈ e.source ∧
            e.source ⊆ {Q | XPtIn X Q U} ∧ ∀ Q ∈ e.source, e Q = fun i => XevalAt X U (f i) Q) ∧
        (∀ g : Γ(X.left, U), ∃ h : (Fin n → ℂ) → ℂ,
            AnalyticAt ℂ h (fun i => XevalAt X U (f i) P) ∧
            ∀ᶠ Q in 𝓝 P, XevalAt X U g Q = h (fun i => XevalAt X U (f i) Q))

/-! ## Glue: local holomorphic representation -/

attribute [local instance] analyticTopology

/-- The coordinate map `X(ℂ) → ℂⁿ` of `f : Fin n → Γ(X, U)` (zero outside `U(ℂ)`). -/
def cf {U : X.left.Opens} {n : ℕ} (f : Fin n → Γ(X.left, U)) (Q : CPt X) : Fin n → ℂ :=
  fun i => XevalAt X U (f i) Q

theorem isOpen_ptIn_an [LocallyOfFiniteType X.hom] (W : X.left.Opens) :
    IsOpen[analyticTopology X] {Q | XPtIn X Q W} := by
  rw [← classicalTopology_eq_analyticTopology]; exact isOpen_ptIn W

theorem xPtIn_inf {P : CPt X} {U W : X.left.Opens} (hU : XPtIn X P U) (hW : XPtIn X P W) :
    XPtIn X P (U ⊓ W) := fun x hx => ⟨hU hx, hW hx⟩

/-- Every regular function on any open `W` is, near each point of `U(ℂ) ∩ W(ℂ)`, a holomorphic
function of étale coordinates on `U` (the leaf on a basic open `D(s) ⊆ U ∩ W`). -/
theorem regFun_local (hL : SGA1_XII_3_1_Etale) [LocallyOfFiniteType X.hom] {U : X.left.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (f : Fin n → Γ(X.left, U))
    (hf : (MvPolynomial.eval₂Hom (algC X U) f).Etale) {W : X.left.Opens} (g : Γ(X.left, W))
    {R : CPt X} (hRU : XPtIn X R U) (hRW : XPtIn X R W) :
    ∃ h : (Fin n → ℂ) → ℂ, AnalyticAt ℂ h (cf f R) ∧
      ∀ᶠ Q in @nhds _ (analyticTopology X) R, XevalAt X W g Q = h (cf f Q) := by
  letI := analyticTopology X
  have hx : R.left.base default ∈ U ⊓ W := (xPtIn_iff _ _).mp (xPtIn_inf hRU hRW)
  obtain ⟨s, hsle, hxs⟩ := hU.exists_basicOpen_le (V := U ⊓ W) ⟨_, hx⟩ ((xPtIn_iff _ _).mp hRU)
  have hRD : XPtIn X R (X.left.basicOpen s) := (xPtIn_iff _ _).mpr hxs
  have hDW : X.left.basicOpen s ≤ W := hsle.trans inf_le_right
  obtain ⟨-, h2⟩ := hL X inferInstance _ (hU.basicOpen s) n _ (etale_res hU s f hf) R hRD
  obtain ⟨h, hh, hev⟩ := h2 (res hDW g)
  have hcf : ∀ Q, XPtIn X Q (X.left.basicOpen s) →
      (fun i => XevalAt X _ (res (X.left.basicOpen_le s) (f i)) Q) = cf f Q :=
    fun Q hQ => funext fun i => xevalAt_res _ _ hQ
  refine ⟨h, (hcf R hRD) ▸ hh, ?_⟩
  filter_upwards [hev, (isOpen_ptIn_an _).mem_nhds hRD] with Q hQ hQD
  rw [← xevalAt_res hDW g hQD, hQ, hcf Q hQD]

/-- In an étale chart `e`, a regular function is holomorphic: `g ∘ e⁻¹` agrees near `w` with a
function analytic at `w`. -/
theorem chart_rep (hL : SGA1_XII_3_1_Etale) [LocallyOfFiniteType X.hom] {U : X.left.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (f : Fin n → Γ(X.left, U))
    (hf : (MvPolynomial.eval₂Hom (algC X U) f).Etale)
    (e : OpenPartialHomeomorph (CPt X) (Fin n → ℂ))
    (hsrc : e.source ⊆ {Q | XPtIn X Q U}) (heq : ∀ Q ∈ e.source, e Q = cf f Q)
    {W : X.left.Opens} (g : Γ(X.left, W)) {w : Fin n → ℂ} (hw : w ∈ e.target)
    (hW : XPtIn X (e.symm w) W) :
    ∃ h : (Fin n → ℂ) → ℂ, AnalyticAt ℂ h w ∧
      ∀ᶠ w' in 𝓝 w, XevalAt X W g (e.symm w') = h w' := by
  have hR := e.map_target hw
  obtain ⟨h, hh, hev⟩ := regFun_local hL hU f hf g (hsrc hR) hW
  have hw' : cf f (e.symm w) = w := by rw [← heq _ hR, e.right_inv hw]
  refine ⟨h, hw' ▸ hh, ?_⟩
  have ht : Tendsto e.symm (𝓝 w) (𝓝 (e.symm w)) := e.continuousAt_symm hw
  filter_upwards [ht.eventually hev, e.open_target.mem_nhds hw] with w' h1 h2
  rw [h1, ← heq _ (e.map_target h2), e.right_inv h2]

/-- Vector-valued version of `chart_rep`. -/
theorem chart_rep_pi (hL : SGA1_XII_3_1_Etale) [LocallyOfFiniteType X.hom] {U : X.left.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (f : Fin n → Γ(X.left, U))
    (hf : (MvPolynomial.eval₂Hom (algC X U) f).Etale)
    (e : OpenPartialHomeomorph (CPt X) (Fin n → ℂ))
    (hsrc : e.source ⊆ {Q | XPtIn X Q U}) (heq : ∀ Q ∈ e.source, e Q = cf f Q)
    {W : X.left.Opens} {m : ℕ} (g : Fin m → Γ(X.left, W)) {w : Fin n → ℂ} (hw : w ∈ e.target)
    (hW : XPtIn X (e.symm w) W) :
    ∃ H : (Fin n → ℂ) → (Fin m → ℂ), AnalyticAt ℂ H w ∧
      ∀ᶠ w' in 𝓝 w, cf g (e.symm w') = H w' := by
  have := fun j => chart_rep hL hU f hf e hsrc heq (g j) hw hW
  choose h hh hev using this
  refine ⟨fun w' j => h j w', AnalyticAt.pi hh, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hev] with w' hw'
  exact funext hw'

/-- Two maps between `ℂⁿ` and `ℂᵐ`, differentiable and inverse to each other near a point, force
`n = m`. -/
theorem eq_of_local_inverse {n m : ℕ} {H : (Fin n → ℂ) → (Fin m → ℂ)}
    {H' : (Fin m → ℂ) → (Fin n → ℂ)} {a : Fin n → ℂ} {b : Fin m → ℂ} (hab : H a = b)
    (hba : H' b = a) (hH : DifferentiableAt ℂ H a) (hH' : DifferentiableAt ℂ H' b)
    (h1 : ∀ᶠ w in 𝓝 a, H' (H w) = w) (h2 : ∀ᶠ w in 𝓝 b, H (H' w) = w) : n = m := by
  have e1 : (fderiv ℂ H' b).comp (fderiv ℂ H a) = ContinuousLinearMap.id ℂ _ := by
    have hc : fderiv ℂ (H' ∘ H) a = (fderiv ℂ H' b).comp (fderiv ℂ H a) := by
      rw [fderiv_comp a (hab ▸ hH') hH, hab]
    rw [← hc, (show (H' ∘ H) =ᶠ[𝓝 a] id from h1).fderiv_eq, fderiv_id]
  have e2 : (fderiv ℂ H a).comp (fderiv ℂ H' b) = ContinuousLinearMap.id ℂ _ := by
    have hc : fderiv ℂ (H ∘ H') b = (fderiv ℂ H a).comp (fderiv ℂ H' b) := by
      rw [fderiv_comp b (hba ▸ hH) hH', hba]
    rw [← hc, (show (H ∘ H') =ᶠ[𝓝 b] id from h2).fderiv_eq, fderiv_id]
  let L : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ) :=
    LinearEquiv.ofLinearMap (fderiv ℂ H a).toLinearMap (fderiv ℂ H' b).toLinearMap
      (LinearMap.ext fun v => by
        simpa using congrArg (fun T : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) => T v) e2)
      (LinearMap.ext fun v => by
        simpa using congrArg (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => T v) e1)
  simpa using L.finrank_eq

/-- **Dimension is well defined**: two étale charts at a common `ℂ`-point have the same `n`. -/
theorem dim_eq (hL : SGA1_XII_3_1_Etale) [LocallyOfFiniteType X.hom] {U U' : X.left.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') {n m : ℕ} (f : Fin n → Γ(X.left, U))
    (f' : Fin m → Γ(X.left, U')) (hf : (MvPolynomial.eval₂Hom (algC X U) f).Etale)
    (hf' : (MvPolynomial.eval₂Hom (algC X U') f').Etale) {R : CPt X} (hRU : XPtIn X R U)
    (hRU' : XPtIn X R U') : n = m := by
  obtain ⟨⟨e, hRe, hsrc, heq⟩, -⟩ := hL X inferInstance U hU n f hf R hRU
  obtain ⟨⟨e', hRe', hsrc', heq'⟩, -⟩ := hL X inferInstance U' hU' m f' hf' R hRU'
  replace heq : ∀ Q ∈ e.source, e Q = cf f Q := heq
  replace heq' : ∀ Q ∈ e'.source, e' Q = cf f' Q := heq'
  have ha : e R ∈ e.target := e.map_source hRe
  have hb : e' R ∈ e'.target := e'.map_source hRe'
  obtain ⟨H, hH, hevH⟩ := chart_rep_pi hL hU f hf e hsrc heq f' ha (by rw [e.left_inv hRe]; exact hRU')
  obtain ⟨H', hH', hevH'⟩ :=
    chart_rep_pi hL hU' f' hf' e' hsrc' heq' f hb (by rw [e'.left_inv hRe']; exact hRU)
  have hab : H (e R) = e' R := by
    rw [← hevH.self_of_nhds, e.left_inv hRe, heq' R hRe']
  have hba : H' (e' R) = e R := by
    rw [← hevH'.self_of_nhds, e'.left_inv hRe', heq R hRe]
  have hHt : Tendsto H (𝓝 (e R)) (𝓝 (e' R)) := hab ▸ hH.continuousAt.tendsto
  have hH't : Tendsto H' (𝓝 (e' R)) (𝓝 (e R)) := hba ▸ hH'.continuousAt.tendsto
  have hQ : ∀ᶠ w in 𝓝 (e R), e.symm w ∈ e'.source :=
    (e.continuousAt_symm ha).preimage_mem_nhds (by rw [e.left_inv hRe]; exact e'.open_source.mem_nhds hRe')
  have hQ' : ∀ᶠ w in 𝓝 (e' R), e'.symm w ∈ e.source :=
    (e'.continuousAt_symm hb).preimage_mem_nhds (by rw [e'.left_inv hRe']; exact e.open_source.mem_nhds hRe)
  have h1 : ∀ᶠ w in 𝓝 (e R), H' (H w) = w := by
    filter_upwards [hHt.eventually hevH', hevH, hQ, e.open_target.mem_nhds ha] with w h1 h2 h3 h4
    rw [← h1, ← h2, ← heq' _ h3, e'.left_inv h3, ← heq _ (e.map_target h4), e.right_inv h4]
  have h2 : ∀ᶠ w in 𝓝 (e' R), H (H' w) = w := by
    filter_upwards [hH't.eventually hevH, hevH', hQ', e'.open_target.mem_nhds hb] with w h1 h2 h3 h4
    rw [← h1, ← h2, ← heq _ h3, e.left_inv h3, ← heq' _ (e'.map_target h4), e'.right_inv h4]
  exact eq_of_local_inverse hab hba hH.differentiableAt hH'.differentiableAt h1 h2

/-- An étale chart of dimension `n`, with the local homeomorphism given by the leaf. -/
structure EChart (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ) where
  U : X.left.Opens
  hU : IsAffineOpen U
  f : Fin n → Γ(X.left, U)
  hf : (MvPolynomial.eval₂Hom (algC X U) f).Etale
  e : OpenPartialHomeomorph (CPt X) (Fin n → ℂ)
  hsrc : e.source ⊆ {Q | XPtIn X Q U}
  heq : ∀ Q ∈ e.source, e Q = cf f Q

/-- For `X` smooth and irreducible, there is one `n` with an `n`-dimensional étale chart at every
`ℂ`-point. -/
theorem exists_echart (hL : SGA1_XII_3_1_Etale) [Smooth X.hom] [IrreducibleSpace X.left] :
    ∃ n : ℕ, ∀ P : CPt X, ∃ c : EChart X n, P ∈ c.e.source := by
  have hch : ∀ P : CPt X, ∃ U : X.left.Opens, IsAffineOpen U ∧ XPtIn X P U ∧
      ∃ (n : ℕ) (f : Fin n → Γ(X.left, U)), (MvPolynomial.eval₂Hom (algC X U) f).Etale :=
    fun P => by
      obtain ⟨U, hU, hx, n, f, hf⟩ := exists_etale_chart (X := X) (P.left.base default)
      exact ⟨U, hU, (xPtIn_iff _ _).mpr hx, n, f, hf⟩
  have hdim : ∃ n : ℕ, ∀ P : CPt X, ∃ U : X.left.Opens, IsAffineOpen U ∧ XPtIn X P U ∧
      ∃ f : Fin n → Γ(X.left, U), (MvPolynomial.eval₂Hom (algC X U) f).Etale := by
    by_cases hne : Nonempty (CPt X)
    · obtain ⟨P₀⟩ := hne
      obtain ⟨U₀, hU₀, hP₀, n, f₀, hf₀⟩ := hch P₀
      refine ⟨n, fun P => ?_⟩
      obtain ⟨U, hU, hP, m, f, hf⟩ := hch P
      obtain ⟨x, hx, hx₀⟩ := nonempty_preirreducible_inter U.2 U₀.2
        ⟨_, (xPtIn_iff _ _).mp hP⟩ ⟨_, (xPtIn_iff _ _).mp hP₀⟩
      obtain ⟨R, hR⟩ := exists_cPt_of_mem (X := X) (V := U ⊓ U₀) ⟨hx, hx₀⟩
      have := dim_eq hL hU hU₀ f f₀ hf hf₀ (xPtIn_mono inf_le_left hR) (xPtIn_mono inf_le_right hR)
      subst this
      exact ⟨U, hU, hP, f, hf⟩
    · exact ⟨0, fun P => (hne ⟨P⟩).elim⟩
  obtain ⟨n, hn⟩ := hdim
  refine ⟨n, fun P => ?_⟩
  obtain ⟨U, hU, hP, f, hf⟩ := hn P
  obtain ⟨⟨e, hPe, hsrc, heq⟩, -⟩ := hL X inferInstance U hU n f hf P hP
  exact ⟨⟨U, hU, f, hf, e, hsrc, heq⟩, hPe⟩

/-- The charted space structure on `X(ℂ)` given by a choice of étale charts. -/
def chartedSpaceOf {n : ℕ} (ch : CPt X → EChart X n) (hch : ∀ P, P ∈ (ch P).e.source) :
    ChartedSpace (Fin n → ℂ) (CPt X) where
  atlas := Set.range fun P => (ch P).e
  chartAt P := (ch P).e
  mem_chart_source := hch
  chart_mem_atlas P := ⟨P, rfl⟩

theorem isManifold_of (hL : SGA1_XII_3_1_Etale) [LocallyOfFiniteType X.hom] {n : ℕ}
    (ch : CPt X → EChart X n) (hch : ∀ P, P ∈ (ch P).e.source) :
    @IsManifold _ _ _ _ _ _ _ 𝓘(ℂ, Fin n → ℂ) ω (CPt X) _ (chartedSpaceOf ch hch) := by
  letI := chartedSpaceOf ch hch
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨P, rfl⟩ ⟨P', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
    inter_univ, Function.id_comp, Function.comp_id]
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  have hw' : w ∈ (ch P).e.target ∧ (ch P).e.symm w ∈ (ch P').e.source := by
    simpa [OpenPartialHomeomorph.trans_source] using hw
  obtain ⟨H, hH, hev⟩ := chart_rep_pi hL (ch P).hU (ch P).f (ch P).hf (ch P).e (ch P).hsrc
    (ch P).heq (ch P').f hw'.1 ((ch P').hsrc hw'.2)
  refine hH.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hev, ((ch P).e.symm ≫ₕ (ch P').e).open_source.mem_nhds hw] with w' h1 h2
  have h2' : (ch P).e.symm w' ∈ (ch P').e.source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, mem_inter_iff,
      mem_preimage] at h2
    exact h2.2
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  rw [(ch P').heq _ h2', h1]

end SGA1Etale
