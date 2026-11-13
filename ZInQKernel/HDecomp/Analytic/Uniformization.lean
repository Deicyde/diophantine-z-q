import ZInQKernel.HDecomp.Analytic.Hom
import ZInQKernel.HDecomp.Objects

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from
`scratch/bp-analytic/Torus.lean`, §10.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

noncomputable section

/-! ## §10. LEAF: the analytic uniformization of a complex abelian variety (node AN3 / N14)

`UniformizationLeaf A` is AN3 of docs/research/bp-faltings.md (= N14 of bp-qmmoduli.md) in
"coordinate form": it needs **no analytification**. It quantifies over

* the group `A(ℂ)` of `ℂ`-points of the project's `AbVar` (copied from
  `ZInQKernel/HDecomp/Objects.lean`), a commutative group by Mathlib;
* regular functions `f ∈ Γ(U, 𝒪_A)` on Zariski opens `U`, evaluated at `ℂ`-points;
* the complex torus `ℂ^g ⧸ Λ` of §1-§3;
* analyticity of functions on open subsets of `ℂ^g`.

`IsUniformization A Λ φ` says that the group isomorphism `φ : ℂ^g ⧸ Λ ≃ A(ℂ)` is analytic for the
analytic structure of `A(ℂ)`:
(i) every regular function pulls back to a holomorphic function on an open set;
(ii) at every point some `g` regular functions pull back to a local biholomorphism;
(iii) `φ⁻¹` is continuous for the topology defined by regular functions (the analytic topology of
`A(ℂ)`, which on an affine open is the subspace topology of `ℂ^n`).
The leaf is a consequence of Mumford, *Abelian varieties*, §1 (a compact connected complex Lie
group is a torus) applied to `A^an` (Mumford §4; Serre, GAGA §2; SGA 1 XII §1, 2.4, 3.1, 3.2);
locators UNVERIFIED. It is not
stronger than the published statement. -/

namespace BPAnalytic.Uniformization

open CategoryTheory AlgebraicGeometry Limits MonObj

universe u

/-! `AbVar`, `AbVar.ptObj`, `AbVar.Pt` (copied in the draft from `Objects.lean`) are
`PkgI3`'s, from `ZInQKernel.HDecomp.Objects`. -/
open PkgI3 (AbVar)

example (A : AbVar ℂ) : CommGroup (A.Pt ℂ) := inferInstance

variable (A : AbVar ℂ)

/-- The `ℂ`-point `P` lies in the Zariski open `U`. -/
def PtIn (P : A.Pt ℂ) (U : A.X.left.Opens) : Prop := ⊤ ≤ P.left ⁻¹ᵁ U

open Classical in
/-- The value `f(P) ∈ ℂ` of a regular function `f ∈ Γ(U, 𝒪_A)` at a `ℂ`-point `P ∈ U`
(`0` if `P ∉ U`; only used on `U`). -/
def evalAt (U : A.X.left.Opens) (f : Γ(A.X.left, U)) (P : A.Pt ℂ) : ℂ :=
  if h : PtIn A P U then
    ((P.left.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom f
  else 0

/-- The group isomorphism `φ : ℂ^g ⧸ Λ ≃ A(ℂ)` is an isomorphism of complex Lie groups. -/
structure IsUniformization {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (φ : Torus Λ ≃+ Additive (A.Pt ℂ)) : Prop where
  /-- (i) regular functions are holomorphic on open sets -/
  holo : ∀ (U : A.X.left.Opens) (f : Γ(A.X.left, U)),
    IsOpen {v : Fin g → ℂ | PtIn A (Additive.toMul (φ (proj Λ v))) U} ∧
    AnalyticOnNhd ℂ (fun v => evalAt A U f (Additive.toMul (φ (proj Λ v))))
      {v | PtIn A (Additive.toMul (φ (proj Λ v))) U}
  /-- (ii) at every point, `g` regular functions give local holomorphic coordinates -/
  coords : ∀ v₀ : Fin g → ℂ, ∃ (U : A.X.left.Opens) (f : Fin g → Γ(A.X.left, U))
    (e : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)),
    PtIn A (Additive.toMul (φ (proj Λ v₀))) U ∧
    HasFDerivAt (fun v i => evalAt A U (f i) (Additive.toMul (φ (proj Λ v))))
      (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀
  /-- (iii) `φ⁻¹` is continuous for the topology defined by regular functions -/
  open_map : ∀ v₀ : Fin g → ℂ, ∀ N ∈ 𝓝 (proj Λ v₀), ∃ (U : A.X.left.Opens) (k : ℕ)
    (f : Fin k → Γ(A.X.left, U)) (ε : ℝ), 0 < ε ∧
    PtIn A (Additive.toMul (φ (proj Λ v₀))) U ∧
    ∀ P : A.Pt ℂ, PtIn A P U →
      (∀ i, ‖evalAt A U (f i) P - evalAt A U (f i) (Additive.toMul (φ (proj Λ v₀)))‖ < ε) →
      ∃ q ∈ N, Additive.toMul (φ q) = P

/-- **LEAF (AN3, coordinate form).** Analytic uniformization of a complex abelian variety:
`A(ℂ) ≅ ℂ^g ⧸ Λ` as complex Lie groups, with `Λ` a full lattice. -/
def UniformizationLeaf : Prop :=
  ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
    (φ : Torus Λ ≃+ Additive (A.Pt ℂ)), IsUniformization A Λ φ

/-- The leaf for every complex abelian variety. -/
def UniformizationLeafAll : Prop := ∀ A : AbVar ℂ, UniformizationLeaf A

/-! ### Glue: the uniformization is unique up to a linear map of lattices -/

variable {A}

/-- **Uniqueness (continuity).** For two uniformizations of the same `A`, the comparison map
`φ'⁻¹ ∘ φ : ℂ^g ⧸ Λ → ℂ^{g'} ⧸ Λ'` is continuous. -/
theorem IsUniformization.continuous_comparison {g g' : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Λ' : Submodule ℤ (Fin g' → ℂ)} {φ : Torus Λ ≃+ Additive (A.Pt ℂ)}
    {φ' : Torus Λ' ≃+ Additive (A.Pt ℂ)} (hφ : IsUniformization A Λ φ)
    (hφ' : IsUniformization A Λ' φ') : Continuous (φ.trans φ'.symm) := by
  rw [(QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous_iff,
    continuous_iff_continuousAt]
  intro v₀
  set w₀ := ((φ.trans φ'.symm) (proj Λ v₀)).out
  have hw₀ : proj Λ' w₀ = (φ.trans φ'.symm) (proj Λ v₀) := QuotientAddGroup.out_eq' _
  have hφw : φ' (proj Λ' w₀) = φ (proj Λ v₀) := by
    rw [hw₀, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [ContinuousAt, Filter.tendsto_def]
  intro N' hN'
  rw [Function.comp_apply, ← hw₀] at hN'
  obtain ⟨U, k, f, ε, hε, hU0, hsep⟩ := hφ'.open_map w₀ N' hN'
  rw [hφw] at hU0 hsep
  have hopen : ∀ᶠ v in 𝓝 v₀, PtIn A (Additive.toMul (φ (proj Λ v))) U :=
    (hφ.holo U 0).1.mem_nhds hU0
  have hall : ∀ᶠ v in 𝓝 v₀, ∀ i, dist (evalAt A U (f i) (Additive.toMul (φ (proj Λ v))))
      (evalAt A U (f i) (Additive.toMul (φ (proj Λ v₀)))) < ε := by
    rw [Filter.eventually_all]
    intro i
    exact (((hφ.holo U (f i)).2 v₀ hU0).continuousAt).eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [hopen, hall] with v hv hvi
  obtain ⟨q, hqN, hq⟩ := hsep _ hv (fun i => by simpa [dist_eq_norm] using hvi i)
  have hq' : φ' q = φ (proj Λ v) := Additive.toMul.injective hq
  have : (φ.trans φ'.symm) (proj Λ v) = q := by
    rw [AddEquiv.trans_apply, ← hq', AddEquiv.symm_apply_apply]
  show (φ.trans φ'.symm) (proj Λ v) ∈ N'
  rw [this]; exact hqN

/-- **Uniqueness of the uniformization up to a linear map.** Two uniformizations of the same `A`
differ by an `ℝ`-linear map carrying `Λ` into `Λ'` (and, symmetrically, back): the period lattice
of `A` is well defined up to isomorphism. -/
theorem IsUniformization.exists_realLinear {g g' : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Λ' : Submodule ℤ (Fin g' → ℂ)} [DiscreteTopology Λ] [DiscreteTopology Λ'] {φ : Torus Λ ≃+
        Additive (A.Pt ℂ)}
    {φ' : Torus Λ' ≃+ Additive (A.Pt ℂ)} (hφ : IsUniformization A Λ φ)
    (hφ' : IsUniformization A Λ' φ') :
    ∃ T : (Fin g → ℂ) →L[ℝ] (Fin g' → ℂ), (∀ v ∈ Λ, T v ∈ Λ') ∧
      ∀ v, φ' (proj Λ' (T v)) = φ (proj Λ v) := by
  obtain ⟨T, hTΛ, hT⟩ := exists_realLinear_lift Λ Λ' (φ.trans φ'.symm).toAddMonoidHom
    (hφ.continuous_comparison hφ')
  refine ⟨T, hTΛ, fun v => ?_⟩
  rw [← hT v]
  simp

/-! ### Glue: endomorphisms act on the period lattice by linear maps -/

variable (A) in
/-- Post-composition with an endomorphism `α` of the group scheme, on `ℂ`-points. -/
def ptMap (α : A.X ⟶ A.X) [IsMonHom α] : Additive (A.Pt ℂ) →+ Additive (A.Pt ℂ) where
  toFun P := Additive.ofMul (Additive.toMul P ≫ α)
  map_zero' := by
    change Additive.ofMul ((1 : A.Pt ℂ) ≫ α) = Additive.ofMul 1
    simp [MonObj.one_comp]
  map_add' P Q := by
    change Additive.ofMul ((Additive.toMul P * Additive.toMul Q) ≫ α) =
      Additive.ofMul (Additive.toMul P ≫ α * Additive.toMul Q ≫ α)
    simp [MonObj.mul_comp]

variable (A) in
/-- Regular functions composed with `α` are regular: `f(α ∘ P) = (α^* f)(P)`. -/
theorem evalAt_comp (α : A.X ⟶ A.X) (U : A.X.left.Opens) (f : Γ(A.X.left, U)) (P : A.Pt ℂ) :
    evalAt A U f (P ≫ α) = evalAt A (α.left ⁻¹ᵁ U) (α.left.app U f) P := by
  have hiff : PtIn A (P ≫ α) U ↔ PtIn A P (α.left ⁻¹ᵁ U) := Iff.rfl
  unfold evalAt
  by_cases h : PtIn A P (α.left ⁻¹ᵁ U)
  · simp only [hiff.mpr h, h, ↓reduceDIte]
    simp [Over.comp_left, Scheme.Hom.comp_appLE]
    rfl
  · simp only [mt hiff.mp h, h, ↓reduceDIte]

/-- **Endomorphisms act continuously on the torus.** For a uniformization `φ` and an
endomorphism `α` of `A`, the transported map `φ⁻¹ ∘ α ∘ φ` is continuous. -/
theorem IsUniformization.continuous_endo {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {φ : Torus Λ ≃+ Additive (A.Pt ℂ)} (hφ : IsUniformization A Λ φ) (α : A.X ⟶ A.X)
    [IsMonHom α] :
    Continuous ((φ.symm.toAddMonoidHom.comp (ptMap A α)).comp φ.toAddMonoidHom) := by
  set ψ := (φ.symm.toAddMonoidHom.comp (ptMap A α)).comp φ.toAddMonoidHom
  have hψ : ∀ x, φ (ψ x) = ptMap A α (φ x) := fun x => by simp [ψ]
  rw [(QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous_iff,
    continuous_iff_continuousAt]
  intro v₀
  set w₀ := (ψ (proj Λ v₀)).out
  have hw₀ : proj Λ w₀ = ψ (proj Λ v₀) := QuotientAddGroup.out_eq' _
  have hφw : Additive.toMul (φ (proj Λ w₀)) = Additive.toMul (φ (proj Λ v₀)) ≫ α := by
    rw [hw₀, hψ]; rfl
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  rw [Function.comp_apply, ← hw₀] at hN
  obtain ⟨U, k, f, ε, hε, hU0, hsep⟩ := hφ.open_map w₀ N hN
  rw [hφw] at hU0 hsep
  have hopen : ∀ᶠ v in 𝓝 v₀, PtIn A (Additive.toMul (φ (proj Λ v))) (α.left ⁻¹ᵁ U) :=
    (hφ.holo (α.left ⁻¹ᵁ U) 0).1.mem_nhds hU0
  have hall : ∀ᶠ v in 𝓝 v₀, ∀ i,
      dist (evalAt A (α.left ⁻¹ᵁ U) (α.left.app U (f i)) (Additive.toMul (φ (proj Λ v))))
        (evalAt A (α.left ⁻¹ᵁ U) (α.left.app U (f i)) (Additive.toMul (φ (proj Λ v₀)))) < ε := by
    rw [Filter.eventually_all]
    intro i
    exact (((hφ.holo (α.left ⁻¹ᵁ U) (α.left.app U (f i))).2 v₀ hU0).continuousAt).eventually
      (Metric.ball_mem_nhds _ hε)
  filter_upwards [hopen, hall] with v hv hvi
  obtain ⟨q, hqN, hq⟩ := hsep (Additive.toMul (φ (proj Λ v)) ≫ α) hv (fun i => by
    rw [evalAt_comp, evalAt_comp]
    simpa [dist_eq_norm] using hvi i)
  have hq' : φ q = φ (ψ (proj Λ v)) := by
    rw [hψ]; exact Additive.toMul.injective hq
  show ψ (proj Λ v) ∈ N
  rw [← φ.injective hq']; exact hqN

/-- **Endomorphisms of `A` act on `ℂ^g` by `ℝ`-linear maps preserving the period lattice**
(the rational representation; `ℂ`-linearity needs the holomorphy clause (ii), node T2 in its
holomorphic form). -/
theorem IsUniformization.exists_realLinear_endo {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    [DiscreteTopology Λ] {φ : Torus Λ ≃+ Additive (A.Pt ℂ)} (hφ : IsUniformization A Λ φ)
    (α : A.X ⟶ A.X) [IsMonHom α] :
    ∃ T : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ), (∀ v ∈ Λ, T v ∈ Λ) ∧
      ∀ v, Additive.toMul (φ (proj Λ (T v))) = Additive.toMul (φ (proj Λ v)) ≫ α := by
  obtain ⟨T, hTΛ, hT⟩ := exists_realLinear_lift Λ Λ _ (hφ.continuous_endo α)
  refine ⟨T, hTΛ, fun v => ?_⟩
  rw [← hT v]
  simp [ptMap]

/-- **Endomorphisms of `A` act on `ℂ^g` by `ℂ`-linear maps preserving the period lattice.**
The real lift of `exists_realLinear_endo` is holomorphic: in the coordinates of clause (ii) it is
`(local inverse of F) ∘ G` with `F, G` given by regular functions (clause (i)). This is the analytic
representation `End(A) → M_g(ℂ)` used by R1an and T11. -/
theorem IsUniformization.exists_complexLinear_endo {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    [DiscreteTopology Λ] {φ : Torus Λ ≃+ Additive (A.Pt ℂ)} (hφ : IsUniformization A Λ φ)
    (α : A.X ⟶ A.X) [IsMonHom α] :
    ∃ T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ), (∀ v ∈ Λ, T v ∈ Λ) ∧
      ∀ v, Additive.toMul (φ (proj Λ (T v))) = Additive.toMul (φ (proj Λ v)) ≫ α := by
  obtain ⟨T, hTΛ, hT⟩ := hφ.exists_realLinear_endo α
  -- coordinates at `T 0`
  obtain ⟨U, f, e, hU, hF⟩ := hφ.coords (T 0)
  set F : (Fin g → ℂ) → (Fin g → ℂ) :=
    fun v i => evalAt A U (f i) (Additive.toMul (φ (proj Λ v))) with hFdef
  set G : (Fin g → ℂ) → (Fin g → ℂ) := fun v i =>
    evalAt A (α.left ⁻¹ᵁ U) (α.left.app U (f i)) (Additive.toMul (φ (proj Λ v))) with hGdef
  have hFT : ∀ v, F (T v) = G v := by
    intro v; funext i
    simp only [hFdef, hGdef, hT v, evalAt_comp]
  have hFan : AnalyticAt ℂ F (T 0) :=
    AnalyticAt.pi fun i => (hφ.holo U (f i)).2 (T 0) hU
  have hU0 : PtIn A (Additive.toMul (φ (proj Λ 0))) (α.left ⁻¹ᵁ U) := by
    have : PtIn A (Additive.toMul (φ (proj Λ (T 0)))) U := hU
    rwa [hT 0] at this
  have hGan : AnalyticAt ℂ G 0 :=
    AnalyticAt.pi fun i => (hφ.holo (α.left ⁻¹ᵁ U) (α.left.app U (f i))).2 0 hU0
  have hstrict : HasStrictFDerivAt F (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (T 0) := by
    have h := hFan.hasStrictFDerivAt
    rwa [hF.fderiv] at h
  -- `T = (local inverse of F) ∘ G` near `0`
  have hev : ∀ᶠ v in 𝓝 (0 : Fin g → ℂ), hstrict.localInverse F e (T 0) (G v) = T v := by
    have hcont : Filter.Tendsto (T : (Fin g → ℂ) → (Fin g → ℂ)) (𝓝 0) (𝓝 (T 0)) :=
      T.continuous.tendsto 0
    filter_upwards [hcont.eventually hstrict.eventually_left_inverse] with v hv
    rw [← hFT v]; exact hv
  have hdiffL : DifferentiableAt ℂ (hstrict.localInverse F e (T 0)) (G 0) := by
    have h := hstrict.to_localInverse.differentiableAt
    rwa [hFT 0] at h
  have hTdiff : DifferentiableAt ℂ (T : (Fin g → ℂ) → (Fin g → ℂ)) 0 :=
    (hdiffL.comp 0 hGan.differentiableAt).congr_of_eventuallyEq
      (hev.mono fun v hv => hv.symm)
  set D := fderiv ℂ (T : (Fin g → ℂ) → (Fin g → ℂ)) 0
  have hD : (D.restrictScalars ℝ : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ)) = T :=
    (hTdiff.hasFDerivAt.restrictScalars ℝ).unique T.hasFDerivAt
  have hDT : ∀ v, D v = T v := fun v => congrArg (fun L : (Fin g → ℂ) →L[ℝ] _ => L v) hD
  exact ⟨D, fun v hv => by rw [hDT]; exact hTΛ v hv, fun v => by rw [hDT]; exact hT v⟩

/-- **Uniqueness of the uniformization up to a `ℂ`-linear map**: two uniformizations of the same
`A` differ by a `ℂ`-linear map carrying `Λ` into `Λ'`. With the symmetric statement this makes the
period lattice of `A`, and every quantity computed from it (the Faltings metric, the period matrix
up to `GL`), independent of the choice of `(Λ, φ)`. -/
theorem IsUniformization.exists_complexLinear {g g' : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Λ' : Submodule ℤ (Fin g' → ℂ)} [DiscreteTopology Λ] [DiscreteTopology Λ']
    {φ : Torus Λ ≃+ Additive (A.Pt ℂ)} {φ' : Torus Λ' ≃+ Additive (A.Pt ℂ)}
    (hφ : IsUniformization A Λ φ) (hφ' : IsUniformization A Λ' φ') :
    ∃ T : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), (∀ v ∈ Λ, T v ∈ Λ') ∧
      ∀ v, φ' (proj Λ' (T v)) = φ (proj Λ v) := by
  obtain ⟨T, hTΛ, hT⟩ := hφ.exists_realLinear hφ'
  obtain ⟨U, f, e, hU, hF⟩ := hφ'.coords (T 0)
  set F : (Fin g' → ℂ) → (Fin g' → ℂ) :=
    fun v i => evalAt A U (f i) (Additive.toMul (φ' (proj Λ' v))) with hFdef
  set G : (Fin g → ℂ) → (Fin g' → ℂ) :=
    fun v i => evalAt A U (f i) (Additive.toMul (φ (proj Λ v))) with hGdef
  have hFT : ∀ v, F (T v) = G v := by
    intro v; funext i
    simp only [hFdef, hGdef, hT v]
  have hFan : AnalyticAt ℂ F (T 0) :=
    AnalyticAt.pi fun i => (hφ'.holo U (f i)).2 (T 0) hU
  have hU0 : PtIn A (Additive.toMul (φ (proj Λ 0))) U := by
    have : PtIn A (Additive.toMul (φ' (proj Λ' (T 0)))) U := hU
    rwa [hT 0] at this
  have hGan : AnalyticAt ℂ G 0 :=
    AnalyticAt.pi fun i => (hφ.holo U (f i)).2 0 hU0
  have hstrict : HasStrictFDerivAt F (e : (Fin g' → ℂ) →L[ℂ] (Fin g' → ℂ)) (T 0) := by
    have h := hFan.hasStrictFDerivAt
    rwa [hF.fderiv] at h
  have hev : ∀ᶠ v in 𝓝 (0 : Fin g → ℂ), hstrict.localInverse F e (T 0) (G v) = T v := by
    have hcont : Filter.Tendsto (T : (Fin g → ℂ) → (Fin g' → ℂ)) (𝓝 0) (𝓝 (T 0)) :=
      T.continuous.tendsto 0
    filter_upwards [hcont.eventually hstrict.eventually_left_inverse] with v hv
    rw [← hFT v]; exact hv
  have hdiffL : DifferentiableAt ℂ (hstrict.localInverse F e (T 0)) (G 0) := by
    have h := hstrict.to_localInverse.differentiableAt
    rwa [hFT 0] at h
  have hTdiff : DifferentiableAt ℂ (T : (Fin g → ℂ) → (Fin g' → ℂ)) 0 :=
    (hdiffL.comp 0 hGan.differentiableAt).congr_of_eventuallyEq
      (hev.mono fun v hv => hv.symm)
  set D := fderiv ℂ (T : (Fin g → ℂ) → (Fin g' → ℂ)) 0
  have hD : (D.restrictScalars ℝ : (Fin g → ℂ) →L[ℝ] (Fin g' → ℂ)) = T :=
    (hTdiff.hasFDerivAt.restrictScalars ℝ).unique T.hasFDerivAt
  have hDT : ∀ v, D v = T v := fun v => congrArg (fun L : (Fin g → ℂ) →L[ℝ] _ => L v) hD
  exact ⟨D, fun v hv => by rw [hDT]; exact hTΛ v hv, fun v => by rw [hDT]; exact hT v⟩

/-! ### Glue: the period lattice is well defined up to isomorphism -/

/-- Lifts are unique: two continuous `ℝ`-linear maps inducing the same map of tori are equal. -/
theorem eq_of_proj_eq {g g' : ℕ} {Λ' : Submodule ℤ (Fin g' → ℂ)} [DiscreteTopology Λ']
    (T T' : (Fin g → ℂ) →L[ℝ] (Fin g' → ℂ)) (h : ∀ v, proj Λ' (T v) = proj Λ' (T' v)) :
    T = T' := by
  have hmem : ∀ v, T v - T' v ∈ Λ' := fun v => (proj_eq_iff Λ').mp (h v)
  ext v : 1
  have hconst := PreconnectedSpace.constant (inferInstance : PreconnectedSpace (Fin g → ℂ))
    (f := fun v => (⟨_, hmem v⟩ : Λ')) ((T.continuous.sub T'.continuous).subtype_mk _)
    (x := v) (y := 0)
  have := congrArg Subtype.val hconst
  simp only [map_zero, sub_zero] at this
  exact sub_eq_zero.mp this

/-- **The period lattice of `A` is well defined up to isomorphism**: two uniformizations differ
by a `ℂ`-linear isomorphism `T` with `T(Λ) = Λ'`. -/
theorem IsUniformization.exists_equiv {g g' : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Λ' : Submodule ℤ (Fin g' → ℂ)} [DiscreteTopology Λ] [DiscreteTopology Λ']
    {φ : Torus Λ ≃+ Additive (A.Pt ℂ)} {φ' : Torus Λ' ≃+ Additive (A.Pt ℂ)}
    (hφ : IsUniformization A Λ φ) (hφ' : IsUniformization A Λ' φ') :
    ∃ T : (Fin g → ℂ) ≃L[ℂ] (Fin g' → ℂ),
      Λ.map (T.toLinearEquiv.toLinearMap.restrictScalars ℤ) = Λ' ∧
      ∀ v, φ' (proj Λ' (T v)) = φ (proj Λ v) := by
  obtain ⟨T, hTΛ, hT⟩ := hφ.exists_complexLinear hφ'
  obtain ⟨T', hT'Λ, hT'⟩ := hφ'.exists_complexLinear hφ
  have h1 : ∀ v, T' (T v) = v := by
    have := eq_of_proj_eq (Λ' := Λ) ((T'.comp T).restrictScalars ℝ)
      (ContinuousLinearMap.id ℝ _) (fun v => by
        apply φ.injective
        simp [hT', hT])
    intro v; exact congrArg (fun L : (Fin g → ℂ) →L[ℝ] _ => L v) this
  have h2 : ∀ w, T (T' w) = w := by
    have := eq_of_proj_eq (Λ' := Λ') ((T.comp T').restrictScalars ℝ)
      (ContinuousLinearMap.id ℝ _) (fun w => by
        apply φ'.injective
        simp [hT', hT])
    intro w; exact congrArg (fun L : (Fin g' → ℂ) →L[ℝ] _ => L w) this
  refine ⟨ContinuousLinearEquiv.equivOfInverse T T' h1 h2, ?_, fun v => hT v⟩
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hTΛ v hv
  · intro w hw
    exact ⟨T' w, hT'Λ w hw, h2 w⟩

/-- **The dimension is well defined**: all uniformizations of `A` have the same `g`. -/
theorem IsUniformization.dim_eq {g g' : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Λ' : Submodule ℤ (Fin g' → ℂ)} [DiscreteTopology Λ] [DiscreteTopology Λ']
    {φ : Torus Λ ≃+ Additive (A.Pt ℂ)} {φ' : Torus Λ' ≃+ Additive (A.Pt ℂ)}
    (hφ : IsUniformization A Λ φ) (hφ' : IsUniformization A Λ' φ') : g = g' := by
  obtain ⟨T, -, -⟩ := hφ.exists_equiv hφ'
  have := T.toLinearEquiv.finrank_eq
  simpa using this

/-! ### Glue: the analytic representation `End(A) → End_ℂ(ℂ^g)` -/

section AnalyticRep

variable {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
  {φ : Torus Λ ≃+ Additive (A.Pt ℂ)}

/-- The analytic representation of an endomorphism `α` of `A`: the unique `ℂ`-linear map of
`ℂ^g` lifting `φ⁻¹ ∘ α ∘ φ` (`exists_complexLinear_endo`). -/
noncomputable def analyticRep (hφ : IsUniformization A Λ φ) (α : A.X ⟶ A.X) [IsMonHom α] :
    (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
  (hφ.exists_complexLinear_endo α).choose

theorem analyticRep_mem (hφ : IsUniformization A Λ φ) (α : A.X ⟶ A.X) [IsMonHom α]
    {v : Fin g → ℂ} (hv : v ∈ Λ) : analyticRep hφ α v ∈ Λ :=
  (hφ.exists_complexLinear_endo α).choose_spec.1 v hv

theorem analyticRep_spec (hφ : IsUniformization A Λ φ) (α : A.X ⟶ A.X) [IsMonHom α]
    (v : Fin g → ℂ) :
    Additive.toMul (φ (proj Λ (analyticRep hφ α v))) = Additive.toMul (φ (proj Λ v)) ≫ α :=
  (hφ.exists_complexLinear_endo α).choose_spec.2 v

/-- Characterization: any continuous `ℝ`-linear lift of `α` is `analyticRep α`. -/
theorem analyticRep_unique (hφ : IsUniformization A Λ φ) (α : A.X ⟶ A.X) [IsMonHom α]
    (T : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ))
    (hT : ∀ v, Additive.toMul (φ (proj Λ (T v))) = Additive.toMul (φ (proj Λ v)) ≫ α) :
    (analyticRep hφ α).restrictScalars ℝ = T :=
  eq_of_proj_eq _ _ fun v => φ.injective (Additive.toMul.injective (by
    rw [ContinuousLinearMap.coe_restrictScalars', analyticRep_spec, hT]))

/-- `ρ(𝟙) = id`. -/
theorem analyticRep_id (hφ : IsUniformization A Λ φ) :
    analyticRep hφ (𝟙 A.X) = ContinuousLinearMap.id ℂ _ := by
  have := analyticRep_unique hφ (𝟙 A.X) (ContinuousLinearMap.id ℝ _) (fun v => by simp)
  ext v : 1
  exact congrArg (fun L : (Fin g → ℂ) →L[ℝ] _ => L v) this

/-- `ρ(β ≫ α) = ρ(α) ∘ ρ(β)` (composition of endomorphisms). -/
theorem analyticRep_comp (hφ : IsUniformization A Λ φ) (α β : A.X ⟶ A.X) [IsMonHom α]
    [IsMonHom β] :
    analyticRep hφ (β ≫ α) = (analyticRep hφ α).comp (analyticRep hφ β) := by
  have := analyticRep_unique hφ (β ≫ α)
    (((analyticRep hφ α).comp (analyticRep hφ β)).restrictScalars ℝ) (fun v => by
      simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_comp,
        Function.comp_apply]
      rw [analyticRep_spec, analyticRep_spec, Category.assoc])
  ext v : 1
  exact congrArg (fun L : (Fin g → ℂ) →L[ℝ] _ => L v) this

/-- The pointwise product of two endomorphisms of the commutative group scheme `A` is again an
endomorphism (as in `Objects.lean`, `PkgI3.AbVar.homGroup`). -/
instance isMonHom_mul (α β : A.X ⟶ A.X) [IsMonHom α] [IsMonHom β] : IsMonHom (α * β) := by
  change IsMonHom (CartesianMonoidalCategory.lift α β ≫ μ[A.X])
  infer_instance

/-- `ρ(α + β) = ρ(α) + ρ(β)`, the sum in the group `Hom(A, A)` being the pointwise product of
morphisms into the commutative group scheme `A`. -/
theorem analyticRep_mul (hφ : IsUniformization A Λ φ) (α β : A.X ⟶ A.X) [IsMonHom α]
    [IsMonHom β] :
    analyticRep hφ (α * β) = analyticRep hφ α + analyticRep hφ β := by
  have := analyticRep_unique hφ (α * β)
    ((analyticRep hφ α + analyticRep hφ β).restrictScalars ℝ) (fun v => by
      simp only [ContinuousLinearMap.coe_restrictScalars', add_apply]
      rw [show proj Λ (analyticRep hφ α v + analyticRep hφ β v) =
          proj Λ (analyticRep hφ α v) + proj Λ (analyticRep hφ β v) from rfl, map_add, toMul_add,
        analyticRep_spec, analyticRep_spec, MonObj.comp_mul])
  ext v : 1
  exact congrArg (fun L : (Fin g → ℂ) →L[ℝ] _ => L v) this

end AnalyticRep

/-! ### Glue: torsion points (for T12) -/

/-- On the torus, `n • [v] = 0 ↔ n • v ∈ Λ`: the `n`-torsion of `E ⧸ Λ` is `(1/n)Λ ⧸ Λ`. -/
theorem nsmul_proj_eq_zero_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Λ : Submodule ℤ E) (n : ℕ) (v : E) : n • proj Λ v = 0 ↔ n • v ∈ Λ := by
  rw [proj, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  rfl

/-- **Torsion points of `A(ℂ)`**: `P^n = 1` iff `P = φ([v])` with `n • v ∈ Λ`. Hence
`A(ℂ)[n] ≅ (1/n)Λ ⧸ Λ ≅ Λ ⧸ nΛ`, and `T_ℓ A ≅ Λ ⊗ ℤ_ℓ` (T12's comparison, glue). -/
theorem torsion_iff {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} (φ : Torus Λ ≃+ Additive (A.Pt ℂ))
    (n : ℕ) (P : A.Pt ℂ) :
    P ^ n = 1 ↔ ∃ v : Fin g → ℂ, n • v ∈ Λ ∧ Additive.toMul (φ (proj Λ v)) = P := by
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective (φ.symm (Additive.ofMul P))
  have hP : Additive.toMul (φ (proj Λ v)) = P := by
    simp only [proj, hv, AddEquiv.apply_symm_apply, toMul_ofMul]
  constructor
  · intro h
    refine ⟨v, (nsmul_proj_eq_zero_iff Λ n v).mp ?_, hP⟩
    apply φ.injective
    rw [map_nsmul, map_zero]
    apply Additive.toMul.injective
    rw [toMul_nsmul, hP, h]
    rfl
  · rintro ⟨w, hw, rfl⟩
    rw [← toMul_nsmul, ← map_nsmul, (nsmul_proj_eq_zero_iff Λ n w).mpr hw, map_zero]
    rfl

end BPAnalytic.Uniformization
