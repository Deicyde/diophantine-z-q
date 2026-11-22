import ZInQKernel.Contrib.CloudB3W17Uniformization.BPFromTorus
import ZInQKernel.Contrib.CloudB3W17LocalExp.UnconditionalTorus

/-!
# Exact BP uniformization from the analytic regular-function structure of abelian points

The torus presentation in this adapter is proved, not an open premise:
`CloudB3W17LocalExp.exists_torus_diffeo` combines the constructed analytic
exponential with its IFT/surjectivity/full-lattice quotient theorem. Only the
concrete scheme-point analytic dictionary remains to be supplied by the native
analytic geometry donor. This is an intermediate theorem, not an H103 closure.
-/

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry MonObj

namespace CloudB3W17Uniformization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

/-- The proved complex torus theorem supplies the witness in the pointwise BP adapter. -/
theorem uniformizationLeaf_of_analyticPoints (A : AbVar ℂ) (g : ℕ)
    [TopologicalSpace (A.Pt ℂ)] [ChartedSpace (Fin g → ℂ) (A.Pt ℂ)]
    [LieGroup 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ)] [CompactSpace (A.Pt ℂ)]
    [ConnectedSpace (A.Pt ℂ)]
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
  obtain ⟨Λ, hd, hz, e, he⟩ :=
    CloudB3W17LocalExp.exists_torus_diffeo (E := Fin g → ℂ) (G := A.Pt ℂ)
  exact uniformizationLeaf_of_torus A g Λ e he hopen hholo hcoords hnhds

end CloudB3W17Uniformization
