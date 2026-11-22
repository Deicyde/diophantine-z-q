/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 Step-2 producer item for C3: (B2.b) `ContractedPresentationTrivial` (C3
`Step2B2/Plan.lean` 09cbbfbe, statement used verbatim through the import), PROVED natively.
SOURCE ONLY, UNCOMPILED. Native HELD. Universe u, default options.

The point `p` of `ℙ^d_K` lies in a standard chart `D₊(Xⱼ)`; the contraction hypothesis puts all
of `C` into `i⁻¹ toProj⁻¹ D₊(Xⱼ)`, where the frame field makes `σⱼ` a free generator; the
pulled-back section is then a free generator of `i^*L` on every open of `C` (batch-2 adapted FLT
`FramePullback.main`), so the frame map `𝒪_C → i^*L` is an isomorphism.
Truth: TRUE (no hypothesis on `C`; `L` invertibility is not even needed).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.Plan
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.PresentationBasics

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.ContractedTrivial

open PresentationBasics

/-- A global section that frames every open makes the frame map an isomorphism. -/
theorem isIso_frameHom {Z : Scheme.{u}} (N : Z.Modules) (s : Γ(N, ⊤))
    (hs : ∀ W : Z.Opens, Function.Bijective fun g : Γ(Z, W) => g • resTop N W s) :
    IsIso (FramePullback.frameHom N s) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  change IsIso ((FramePullback.frameHom N s).app W)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hs W

/-- **(B2.b) proved.** -/
theorem contractedPresentationTrivial :
    ZInQ.Contrib.CloudR2NOS.Step2B2.ContractedPresentationTrivial.{u} := by
  intro K _ X fX L _ d 𝔓 C i p hp
  -- the image point lies in a standard chart
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨j, hj⟩ := PresChart.exists_mem_basicOpen_X K d (p.base pt)
  -- all of `C` maps into `toProj⁻¹ D₊(Xⱼ)`
  have hC : ∀ c : C, i.base c ∈ 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K) (MvPolynomial.X j) := by
    intro c
    have h1 := congrArg (fun φ => φ.base c) hp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1
    rw [Subsingleton.elim (fX.base (i.base c)) pt] at h1
    show 𝔓.toProj.base (i.base c) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K) (MvPolynomial.X j)
    rw [h1]
    exact hj
  have htop : ∀ W : C.Opens, W ≤ i ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K) (MvPolynomial.X j)) :=
    fun W c _ => hC c
  -- the pulled-back `σⱼ` frames `i^* L` on every open of `C`
  let τ : Γ((Scheme.Modules.pullback i).obj L, ⊤) :=
    show Γ((Scheme.Modules.pullback i).obj L, ⊤) from FramePullback.eta i L ⊤ (𝔓.σ j)
  have hτ : ∀ W : C.Opens, Function.Bijective fun g : Γ(C, W) =>
      g • resTop ((Scheme.Modules.pullback i).obj L) W τ := fun W =>
    FramePullback.main i L (𝔓.σ j) (fun V hV => 𝔓.frame j V hV) W (htop W)
  haveI := isIso_frameHom ((Scheme.Modules.pullback i).obj L) τ hτ
  exact ⟨(asIso (FramePullback.frameHom ((Scheme.Modules.pullback i).obj L) τ)).symm⟩

end ZInQ.Contrib.CloudR2NOS.ClosedSection.ContractedTrivial
