import ZInQKernel.Contrib.CloudB3W17GAGA.CanonicalOriginalPoints
import ZInQKernel.Contrib.CloudB3W17Hodge.CptManifold
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytic.ParametricCircleIntegral

/-!
# Actual Oka scalar sections in genuine canonical regular charts

Only manifold differentiability of the original-point map is needed.  The
finite-dimensional scalar Cauchy theorem upgrades every regular-coordinate
pullback in a genuine source chart, and the resulting function is bundled in
Oka's actual ring of holomorphic functions.  No H103, target uniformization,
GAGA statement, algebraic map or invented compatibility premise is imported.
This is a local scalar interface, not yet a global analytic-space morphism.
-/

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry TopologicalSpace
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (cEvalAt)
open ZInQ.Contrib.CloudB3W17GAGA

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

section Chart

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin d → ℂ) M]

/-- The genuine chart domain where the inverse chart lies in the specified open. -/
def chartPullbackOpen
    (e : PartialDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M (Fin d → ℂ) ω)
    (s : Set M) (hs : IsOpen s) : Opens (Fin d → ℂ) :=
  ⟨e.target ∩ e.symm ⁻¹' s,
    e.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage e.open_target hs⟩

/-- Scalar holomorphy in a genuine analytic chart follows already from MDifferentiableOn. -/
theorem analyticAt_chart_pullback
    (e : PartialDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M (Fin d → ℂ) ω)
    {f : M → ℂ} {s : Set M} (hs : IsOpen s)
    (hf : MDifferentiableOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) f s)
    {z : Fin d → ℂ} (hz : z ∈ chartPullbackOpen e s hs) :
    AnalyticAt ℂ (fun w => f (e.symm w)) z := by
  have hd : MDifferentiableOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ)
      (fun w => f (e.symm w)) (chartPullbackOpen e s hs) :=
    hf.comp ((e.symm.mdifferentiableOn (by simp)).mono inter_subset_left)
      (fun _ hw => hw.2)
  exact analyticAt_of_differentiableOn (chartPullbackOpen e s hs).isOpen hd.differentiableOn hz

/-- An actual scalar chart pullback, as an element of Oka's genuine holomorphic ring. -/
def chartScalarSection
    (e : PartialDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M (Fin d → ℂ) ω)
    (f : M → ℂ) (s : Set M) (hs : IsOpen s)
    (hf : MDifferentiableOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) f s) :
    OkaRing (chartPullbackOpen e s hs) :=
  OkaRing.mk (fun w => f (e.symm w.1))
    (okaAnalytic_restrict (fun _ hw => analyticAt_chart_pullback e hs hf hw))

@[simp]
theorem chartScalarSection_eval
    (e : PartialDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M (Fin d → ℂ) ω)
    (f : M → ℂ) (s : Set M) (hs : IsOpen s)
    (hf : MDifferentiableOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) f s)
    (w : chartPullbackOpen e s hs) :
    OkaRing.evalHom w.2 (chartScalarSection e f s hs hf) = f (e.symm w.1) := rfl

end Chart

local instance cptsIntegral (A : AbVar ℂ) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

local instance cptsTopology (A : AbVar ℂ) : TopologicalSpace (APts A) :=
  CloudB3W17Hodge.classicalTopology A.X

local instance cptsChartedSpace (A : AbVar ℂ) (n : ℕ) [SmoothOfRelativeDimension n A.X.hom] :
    ChartedSpace (Fin n → ℂ) (APts A) := CloudB3W17Hodge.chartedSpace A.X n

local instance cptsManifold (A : AbVar ℂ) (n : ℕ) [SmoothOfRelativeDimension n A.X.hom] :
    IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A) := CloudB3W17Hodge.isManifold_cpt A.X n

/-- The open source domain of a regular section composed with the actual original-point F. -/
def regularPullbackOpen (A B : AbVar ℂ) (F : APts A → APts B)
    (hF : MDifferentiable 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) F) (U : B.X.left.Opens) : Opens (APts A) :=
  ⟨F ⁻¹' pointDom B U, (canonical_isOpen_pointDom B U).preimage hF.continuous⟩

/-- Regular-section pullbacks along the proved canonical map are scalar MDifferentiableOn. -/
theorem mdifferentiableOn_regular_pullback (A B : AbVar ℂ) (F : APts A → APts B)
    (hF : MDifferentiable 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) F)
    (U : B.X.left.Opens) (s : Γ(B.X.left, U)) :
    MDifferentiableOn 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ) 𝓘(ℂ, ℂ)
      (fun P => cEvalAt (F P) U s) (regularPullbackOpen A B F hF U) :=
  ((canonical_cpts_holo B _ U s).mdifferentiableOn (by simp)).comp hF.mdifferentiableOn
    (fun _ hP => hP)

/-- Every genuine regular pullback has an actual Oka section in a canonical regular source chart.
The chart and its regular coordinates are obtained internally from the unchanged Hodge atlas. -/
theorem exists_canonical_oka_section (A B : AbVar ℂ) (F : APts A → APts B)
    (hF : MDifferentiable 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
      𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) F)
    (U : B.X.left.Opens) (s : Γ(B.X.left, U))
    (P : APts A) (hP : F P ∈ pointDom B U) :
    ∃ (V : A.X.left.Opens) (a : Fin (TopologicalSpace.dim A.X.left) → Γ(A.X.left, V))
      (e : PartialDiffeomorph 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
        𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
        (APts A) (Fin (TopologicalSpace.dim A.X.left) → ℂ) ω)
      (W : Opens (Fin (TopologicalSpace.dim A.X.left) → ℂ)) (t : OkaRing W),
      P ∈ pointDom A V ∧ P ∈ e.source ∧
      EqOn (fun Q i => cEvalAt Q V (a i)) e e.source ∧ e P ∈ W ∧
      ∀ w : W, e.symm w.1 ∈ regularPullbackOpen A B F hF U ∧
        OkaRing.evalHom w.2 t = cEvalAt (F (e.symm w.1)) U s := by
  obtain ⟨V, a, hPV, e, heP, heq⟩ :=
    canonical_cpts_coords A (TopologicalSpace.dim A.X.left) P
  let S := regularPullbackOpen A B F hF U
  let W := chartPullbackOpen e S S.isOpen
  let t := chartScalarSection e (fun Q => cEvalAt (F Q) U s) S S.isOpen
    (mdifferentiableOn_regular_pullback A B F hF U s)
  refine ⟨V, a, e, W, t, hPV, heP, heq, ?_, fun w => ⟨w.2.2, rfl⟩⟩
  refine ⟨e.map_source heP, ?_⟩
  change F (e.symm (e P)) ∈ pointDom B U
  exact (congrArg (fun Q => F Q ∈ pointDom B U) (e.left_inv heP)).mpr hP

end ZInQ.Contrib.CloudB3W17bOkaComparison
