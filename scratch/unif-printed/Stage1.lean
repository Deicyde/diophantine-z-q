import ZInQKernel.HDecomp.Analytic.Uniformization

/-! # unif-printed, stage 1: the coordinate form from Mumford §1 and an analytic Lie group structure

`UniformizationLeafAll` (kernel, `ZInQKernel/HDecomp/Analytic/Uniformization.lean`) from
* `MumfordComplexTorus` (Mumford §1, printed form, over Mathlib's complex Lie groups), and
* `AbVarAnalyticLieGroup` (the analytic structure of `A(ℂ)`: a compact connected complex Lie group whose
  holomorphic structure is the one given by regular functions). -/

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj

set_option linter.unusedSectionVars false

noncomputable section

namespace UnifPrinted

open BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

/-- **Mumford, *Abelian varieties*, §1 (printed form).** A compact connected complex Lie group `X` of
dimension `g` is a complex torus: there are a lattice `Λ ⊂ ℂ^g` and a biholomorphic group isomorphism
`ℂ^g ⧸ Λ ≃ X`. (Mumford, *Abelian varieties*, 2nd ed. (1974), §1, Theorem on p. 1-2; Birkenhake–Lange,
*Complex abelian varieties*, 2nd ed., §1.1; locators UNVERIFIED.) Stated over Mathlib's complex
analytic manifolds (`IsManifold 𝓘(ℂ, ℂ^g) ω`) and Lie groups (`LieGroup 𝓘(ℂ, ℂ^g) ω`); the torus is
bp-analytic's `Torus Λ` with its analytic structure (`ZInQKernel/HDecomp/Analytic/Torus.lean`). -/
def MumfordComplexTorus : Prop :=
  ∀ (g : ℕ) (X : Type) [TopologicalSpace X] [ChartedSpace (Fin g → ℂ) X] [Group X],
    IsManifold 𝓘(ℂ, Fin g → ℂ) ω X → LieGroup 𝓘(ℂ, Fin g → ℂ) ω X → T2Space X →
    CompactSpace X → ConnectedSpace X →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin g → ℂ), 𝓘(ℂ, Fin g → ℂ)⟯ X), ∀ a b, e (a + b) = e a * e b

/-- The analytic structure on `A(ℂ)` (a topology and a complex atlas) is the one given by regular
functions: (1) `U(ℂ)` is open for every Zariski open `U`; (2) regular functions are holomorphic on
`U(ℂ)`; (3) at every point, `g` regular functions are local holomorphic coordinates; (4) the topology
is the one defined by regular functions. -/
structure IsAnalyticStr (A : AbVar ℂ) (g : ℕ) [TopologicalSpace (A.Pt ℂ)]
    [ChartedSpace (Fin g → ℂ) (A.Pt ℂ)] : Prop where
  isOpen_ptIn : ∀ U : A.X.left.Opens, IsOpen {P | PtIn A P U}
  holo : ∀ (U : A.X.left.Opens) (f : Γ(A.X.left, U)),
    ContMDiffOn 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ) ω (evalAt A U f) {P | PtIn A P U}
  coords : ∀ P : A.Pt ℂ, ∃ (U : A.X.left.Opens) (f : Fin g → Γ(A.X.left, U)), PtIn A P U ∧
    IsLocalDiffeomorphAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω (fun Q i => evalAt A U (f i) Q) P
  nhds : ∀ (P₀ : A.Pt ℂ), ∀ N ∈ 𝓝 P₀, ∃ (U : A.X.left.Opens) (k : ℕ) (f : Fin k → Γ(A.X.left, U))
    (ε : ℝ), 0 < ε ∧ PtIn A P₀ U ∧ ∀ P : A.Pt ℂ, PtIn A P U →
      (∀ i, ‖evalAt A U (f i) P - evalAt A U (f i) P₀‖ < ε) → P ∈ N

/-- **(composite; reduced in stage 2)** `A(ℂ)`, with its analytic structure, is a compact connected
complex Lie group. -/
def AbVarAnalyticLieGroup : Prop :=
  ∀ A : AbVar ℂ, ∃ (g : ℕ) (_ : TopologicalSpace (A.Pt ℂ)) (_ : ChartedSpace (Fin g → ℂ) (A.Pt ℂ)),
    IsManifold 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ) ∧ LieGroup 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ) ∧
    T2Space (A.Pt ℂ) ∧ CompactSpace (A.Pt ℂ) ∧ ConnectedSpace (A.Pt ℂ) ∧ IsAnalyticStr A g

section Torus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Λ : Submodule ℤ E)
  [DiscreteTopology Λ]

/-- The chart `chartOf Λ v`, inverted: a partial diffeomorphism `E → E ⧸ Λ` agreeing with `proj`. -/
def projPartialDiffeo (v : E) : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) E (Torus Λ) ω where
  toPartialEquiv := (chartOf Λ v).symm.toPartialEquiv
  open_source := (chartOf Λ v).open_target
  open_target := (chartOf Λ v).open_source
  contMDiffOn_toFun := by
    refine (contMDiff_proj Λ).contMDiffOn.congr fun z _ => ?_
    exact chartOf_symm_apply Λ v z
  contMDiffOn_invFun := by
    have hmem : chartOf Λ v ∈ atlas E (Torus Λ) := ⟨v, rfl⟩
    exact contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hmem)

/-- **The projection `E → E ⧸ Λ` is a local biholomorphism.** -/
theorem isLocalDiffeomorphAt_proj (v : E) :
    IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (proj Λ) v :=
  ⟨projPartialDiffeo Λ v, self_mem_chartOf_target Λ v, fun z _ => (chartOf_symm_apply Λ v z).symm⟩

end Torus

/-- **Stage 1 (proved).** The coordinate form `UniformizationLeaf A` from Mumford §1 and an analytic
Lie group structure on `A(ℂ)` given by regular functions. -/
theorem uniformizationLeaf_of_lieGroup (hM : MumfordComplexTorus) (A : AbVar ℂ) (g : ℕ)
    [TopologicalSpace (A.Pt ℂ)] [ChartedSpace (Fin g → ℂ) (A.Pt ℂ)]
    (hMan : IsManifold 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ)) (hLie : LieGroup 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ))
    (hT2 : T2Space (A.Pt ℂ)) (hC : CompactSpace (A.Pt ℂ)) (hK : ConnectedSpace (A.Pt ℂ))
    (hS : IsAnalyticStr A g) : UniformizationLeaf A := by
  obtain ⟨Λ, hd, hz, e, he⟩ := hM g (A.Pt ℂ) hMan hLie hT2 hC hK
  let φ : Torus Λ ≃+ Additive (A.Pt ℂ) :=
    { toFun := fun q => Additive.ofMul (e q)
      invFun := fun P => e.symm (Additive.toMul P)
      left_inv := fun q => by simp
      right_inv := fun P => by simp
      map_add' := fun a b => by simp only [he]; rfl }
  have hφ : ∀ q, Additive.toMul (φ q) = e q := fun q => rfl
  have hcont : Continuous (fun v : Fin g → ℂ => e (proj Λ v)) :=
    e.continuous.comp (isLocalHomeomorph_proj Λ).continuous
  refine ⟨g, Λ, hd, hz, φ, ⟨fun U f => ?_, fun v₀ => ?_, fun v₀ N hN => ?_⟩⟩
  · -- (i) regular functions are holomorphic
    simp only [hφ]
    have hopen : IsOpen {v : Fin g → ℂ | PtIn A (e (proj Λ v)) U} :=
      (hS.isOpen_ptIn U).preimage hcont
    refine ⟨hopen, ?_⟩
    have h1 : ContMDiffOn 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ) ω (fun v => evalAt A U f (e (proj Λ v)))
        {v : Fin g → ℂ | PtIn A (e (proj Λ v)) U} :=
      (hS.holo U f).comp (e.contMDiff.comp (contMDiff_proj Λ)).contMDiffOn (fun v hv => hv)
    have h2 := (contMDiffOn_iff_contDiffOn.mp h1).analyticOn
    exact hopen.analyticOn_iff_analyticOnNhd.mp h2
  · -- (ii) local coordinates
    obtain ⟨U, f, hU, hloc⟩ := hS.coords (e (proj Λ v₀))
    have hep : IsLocalDiffeomorphAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω
        (fun v => e (proj Λ v)) v₀ :=
      (isLocalDiffeomorphAt_proj Λ v₀).comp (K := 𝓘(ℂ, Fin g → ℂ)) (P := A.Pt ℂ)
        (e.isLocalDiffeomorph (proj Λ v₀))
    have hF := hep.comp (K := 𝓘(ℂ, Fin g → ℂ)) (P := Fin g → ℂ) hloc
    obtain ⟨L, hL⟩ := hF.isInvertible_mfderiv (by simp)
    let L' : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := L
    have hL' : (L' : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) =
        mfderiv 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ)
          ((fun Q i => evalAt A U (f i) Q) ∘ fun v => e (proj Λ v)) v₀ := hL
    refine ⟨U, f, L', by simpa [hφ] using hU, ?_⟩
    have hd' := (hF.mdifferentiableAt (by simp)).hasMFDerivAt
    rw [hasMFDerivAt_iff_hasFDerivAt] at hd'
    rw [hL']
    exact hd'
  · -- (iii) `φ⁻¹` is continuous for the topology of regular functions
    have hN' : e '' N ∈ 𝓝 (e (proj Λ v₀)) := e.toHomeomorph.isOpenMap.image_mem_nhds hN
    obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := hS.nhds _ _ hN'
    refine ⟨U, k, f, ε, hε, by simpa [hφ] using hU, fun P hP hPi => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hsep P hP (by simpa [hφ] using hPi)
    exact ⟨q, hq, rfl⟩

/-- **Stage 1 (proved).** `UniformizationLeafAll` from `MumfordComplexTorus` and
`AbVarAnalyticLieGroup`. -/
theorem uniformizationLeafAll_of_lieGroup (hM : MumfordComplexTorus) (hA : AbVarAnalyticLieGroup) :
    UniformizationLeafAll := by
  intro A
  obtain ⟨g, t, cs, hMan, hLie, hT2, hC, hK, hS⟩ := hA A
  exact uniformizationLeaf_of_lieGroup hM A g hMan hLie hT2 hC hK hS

end UnifPrinted
