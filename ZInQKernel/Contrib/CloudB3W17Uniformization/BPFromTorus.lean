import ZInQKernel.Contrib.HDecomp.Analytic.Uniformization

/-!
# Pointwise analytic torus witness gives BP's exact coordinate uniformization

This is a pointwise adapter, not a new literature leaf or a claim that H103 is
closed. All hypotheses concern genuine Mathlib manifolds, regular sections of
`A`, and an actual torus diffeomorphism. The final assembly must supply them.

Attribution: adapted from host task `unif-printed`,
`ZInQKernel/Contrib/OneProof/UniformizationPrinted.lean`, Stage 1 lines 95–163
at commit `dbf043a4eb8d977b1d4bf0b03010f915b70bcfb8` (the report credits
`scratch/unif-printed/Stage1.lean`). That module is not on the accepted base,
so this new adapter reuses its pointwise proof logic explicitly rather than
silently importing or copying an unmerged host module. Differences: there is
no `MumfordComplexTorus` premise, no purpose-built analytic structure bundle,
and no four-leaf reduction. A torus witness and its concrete regular-function
properties are inputs directly. The actual torus supplier can fill the witness.
-/

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj

namespace CloudB3W17Uniformization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

section TorusProjection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ]

/-- The inverted BP quotient chart, as an analytic partial diffeomorphism. -/
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

/-- The existing BP torus projection is an analytic local diffeomorphism. -/
theorem isLocalDiffeomorphAt_proj (v : E) :
    IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (proj Λ) v :=
  ⟨projPartialDiffeo Λ v, self_mem_chartOf_target Λ v,
    fun z _ => (chartOf_symm_apply Λ v z).symm⟩
end TorusProjection

/-- An actual analytic torus presentation, compatible with regular sections and their
neighbourhood basis, gives the exact BP uniformization of this abelian variety. -/
theorem uniformizationLeaf_of_torus (A : AbVar ℂ) (g : ℕ)
    [TopologicalSpace (A.Pt ℂ)] [ChartedSpace (Fin g → ℂ) (A.Pt ℂ)]
    [IsManifold 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ)]
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin g → ℂ), 𝓘(ℂ, Fin g → ℂ)⟯ A.Pt ℂ)
    (he : ∀ a b, e (a + b) = e a * e b)
    (hopen : ∀ U : A.X.left.Opens, IsOpen {P | PtIn A P U})
    (hholo : ∀ (U : A.X.left.Opens) (f : Γ(A.X.left, U)),
      ContMDiffOn 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ) ω (evalAt A U f) {P | PtIn A P U})
    (hcoords : ∀ P : A.Pt ℂ, ∃ (U : A.X.left.Opens) (f : Fin g → Γ(A.X.left, U)),
      PtIn A P U ∧ IsLocalDiffeomorphAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω
        (fun Q i => evalAt A U (f i) Q) P)
    (hnhds : ∀ (P₀ : A.Pt ℂ), ∀ N ∈ 𝓝 P₀,
      ∃ (U : A.X.left.Opens) (k : ℕ) (f : Fin k → Γ(A.X.left, U)) (ε : ℝ),
        0 < ε ∧ PtIn A P₀ U ∧ ∀ P : A.Pt ℂ, PtIn A P U →
          (∀ i, ‖evalAt A U (f i) P - evalAt A U (f i) P₀‖ < ε) → P ∈ N) :
    UniformizationLeaf A := by
  let φ : Torus Λ ≃+ Additive (A.Pt ℂ) :=
    { toFun := fun q => Additive.ofMul (e q)
      invFun := fun P => e.symm (Additive.toMul P)
      left_inv := fun q => by simp
      right_inv := fun P => by simp
      map_add' := fun a b => by simp only [he]; rfl }
  have hφ : ∀ q, Additive.toMul (φ q) = e q := fun q => rfl
  have hcont : Continuous (fun v : Fin g → ℂ => e (proj Λ v)) :=
    e.continuous.comp (isLocalHomeomorph_proj Λ).continuous
  refine ⟨g, Λ, inferInstance, inferInstance, φ,
    ⟨fun U f => ?_, fun v₀ => ?_, fun v₀ N hN => ?_⟩⟩
  · simp only [hφ]
    have ho : IsOpen {v : Fin g → ℂ | PtIn A (e (proj Λ v)) U} :=
      (hopen U).preimage hcont
    refine ⟨ho, ?_⟩
    have h1 : ContMDiffOn 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ) ω
        (fun v => evalAt A U f (e (proj Λ v))) {v | PtIn A (e (proj Λ v)) U} :=
      (hholo U f).comp (e.contMDiff.comp (contMDiff_proj Λ)).contMDiffOn (fun _ hv => hv)
    exact ho.analyticOn_iff_analyticOnNhd.mp (contMDiffOn_iff_contDiffOn.mp h1).analyticOn
  · obtain ⟨U, f, hU, hloc⟩ := hcoords (e (proj Λ v₀))
    have hep : IsLocalDiffeomorphAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω
        (fun v => e (proj Λ v)) v₀ :=
      (isLocalDiffeomorphAt_proj Λ v₀).comp (K := 𝓘(ℂ, Fin g → ℂ)) (P := A.Pt ℂ)
        (e.isLocalDiffeomorph (proj Λ v₀))
    have hF := hep.comp (K := 𝓘(ℂ, Fin g → ℂ)) (P := Fin g → ℂ) hloc
    obtain ⟨L, hL⟩ := hF.isInvertible_mfderiv (by simp)
    refine ⟨U, f, L, by simpa only [hφ] using hU, ?_⟩
    have hd := (hF.mdifferentiableAt (by simp)).hasMFDerivAt
    rw [hasMFDerivAt_iff_hasFDerivAt] at hd
    rw [hL]
    exact hd
  · have hN' : e '' N ∈ 𝓝 (e (proj Λ v₀)) := e.toHomeomorph.isOpenMap.image_mem_nhds hN
    obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := hnhds _ _ hN'
    refine ⟨U, k, f, ε, hε, by simpa only [hφ] using hU, fun P hP hPi => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hsep P hP (by simpa only [hφ] using hPi)
    exact ⟨q, hq, rfl⟩

end

end CloudB3W17Uniformization
