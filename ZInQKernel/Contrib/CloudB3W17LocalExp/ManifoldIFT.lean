import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.RCLike.Basic

/-!
# Analytic inverse function theorem: vector-space source, manifold target

Mathlib (pin `56a0058`) has the inverse function theorem for maps between normed spaces
(`ContDiffAt.toOpenPartialHomeomorph`, `ContDiffAt.to_localInverse`) and the forward direction for
manifolds (`IsLocalDiffeomorphAt.isInvertible_mfderiv`), but not the converse for manifolds. This file
proves the case needed by complex uniformization: the source is a normed space over `ℝ` or `ℂ` with its self model, the target an analytic manifold.

```lean
theorem isLocalDiffeomorphAt_of_hasMFDerivAt (hf : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) ω f a)
    (hd : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, F) f a (e : E →L[𝕜] F)) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, F) ω f a
```

Proof: in the chart `c` at `f a`, `ψ = c ∘ f` is analytic at `a` with invertible derivative
`(mfderiv c (f a)) ∘ e` (the chart's differential is invertible because a chart of an analytic manifold
is a partial diffeomorphism). Mathlib's inverse function theorem gives a partial homeomorphism around
`a` whose inverse is analytic at `ψ a`; restricting to the open set where `ψ`, its inverse and `f` are
well behaved turns it into a `PartialDiffeomorph`, and composing with the chart's inverse gives one for
`f`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set

noncomputable section

namespace CloudB3W17LocalExp

variable {𝕜 : Type*} [RCLike 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(𝕜, F) ω M]

/-- A chart of an analytic manifold, as a partial diffeomorphism. -/
def chartPartialDiffeo (x : M) : PartialDiffeomorph 𝓘(𝕜, F) 𝓘(𝕜, F) M F ω where
  toPartialEquiv := (chartAt F x).toPartialEquiv
  open_source := (chartAt F x).open_source
  open_target := (chartAt F x).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

/-- A chart is a local diffeomorphism at every point of its source. -/
theorem isLocalDiffeomorphAt_chart {x y : M} (hy : y ∈ (chartAt F x).source) :
    IsLocalDiffeomorphAt 𝓘(𝕜, F) 𝓘(𝕜, F) ω (chartAt F x) y :=
  ⟨chartPartialDiffeo x, hy, fun _ _ => rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [CompleteSpace F]

/-- **Analytic inverse function theorem, vector-space source and manifold target.** An analytic map
`f : E → M` whose differential at `a` is a continuous linear equivalence is an analytic local
diffeomorphism at `a`. -/
theorem isLocalDiffeomorphAt_of_hasMFDerivAt {f : E → M} {a : E} {e : E ≃L[𝕜] F}
    (hf : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) ω f a)
    (hd : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, F) f a (e : E →L[𝕜] F)) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, F) ω f a := by
  have hω0 : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hωinf : (ω : WithTop ℕ∞) ≠ ∞ := by simp
  set c := chartAt F (f a) with hc
  have hca : f a ∈ c.source := mem_chart_source F (f a)
  -- the chart is analytic with invertible differential at `f a`
  have hcsm : ContMDiffAt 𝓘(𝕜, F) 𝓘(𝕜, F) ω (c : M → F) (f a) :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hca)
  have hclocal : IsLocalDiffeomorphAt 𝓘(𝕜, F) 𝓘(𝕜, F) ω (c : M → F) (f a) :=
    isLocalDiffeomorphAt_chart hca
  set Dc := hclocal.mfderivToContinuousLinearEquiv hω0 with hDcdef
  have hDc : (Dc : TangentSpace 𝓘(𝕜, F) (f a) →L[𝕜] TangentSpace 𝓘(𝕜, F) (c (f a)))
      = mfderiv 𝓘(𝕜, F) 𝓘(𝕜, F) (c : M → F) (f a) :=
    hclocal.mfderivToContinuousLinearEquiv_coe hω0
  -- `ψ = c ∘ f` is analytic at `a`
  have hψsm : ContDiffAt 𝕜 ω ((c : M → F) ∘ f) a :=
    contMDiffAt_iff_contDiffAt.mp (hcsm.comp a hf)
  -- and has invertible derivative there
  have hcmd : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜, F) (c : M → F) (f a) := hcsm.mdifferentiableAt hω0
  have hcomp : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, F) ((c : M → F) ∘ f) a
      ((mfderiv 𝓘(𝕜, F) 𝓘(𝕜, F) (c : M → F) (f a)).comp (e : E →L[𝕜] F)) :=
    hcmd.hasMFDerivAt.comp a hd
  set A : E ≃L[𝕜] F := e.trans Dc with hA
  have hAcoe : (A : E →L[𝕜] F)
      = (mfderiv 𝓘(𝕜, F) 𝓘(𝕜, F) (c : M → F) (f a)).comp (e : E →L[𝕜] F) := by
    rw [hA, ← hDc]; rfl
  have hψd : HasFDerivAt ((c : M → F) ∘ f) (A : E →L[𝕜] F) a := by
    rw [hAcoe]
    exact hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  -- Mathlib's inverse function theorem in the model space
  set h := hψsm.toOpenPartialHomeomorph ((c : M → F) ∘ f) hψd hω0 with hh
  have hcoe : ⇑h = (c : M → F) ∘ f := hψsm.toOpenPartialHomeomorph_coe hψd hω0
  have hasrc : a ∈ h.source := hψsm.mem_toOpenPartialHomeomorph_source hψd hω0
  have hinv : ContDiffAt 𝕜 ω (hψsm.localInverse hψd hω0) (((c : M → F) ∘ f) a) :=
    hψsm.to_localInverse hψd hω0
  have hinvcoe : hψsm.localInverse hψd hω0 = ⇑h.symm := rfl
  -- open sets where everything is analytic and `f` lands in the chart
  obtain ⟨V₁, hV₁sub, hV₁open, haV₁⟩ := mem_nhds_iff.mp (hψsm.eventually hωinf)
  obtain ⟨W₁, hW₁sub, hW₁open, hW₁mem⟩ := mem_nhds_iff.mp (hinv.eventually hωinf)
  obtain ⟨V₂, hV₂sub, hV₂open, haV₂⟩ :=
    mem_nhds_iff.mp (hf.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hca))
  set s : Set E := (V₁ ∩ V₂) ∩ (h.source ∩ h ⁻¹' W₁) with hs
  have hsopen : IsOpen s :=
    (hV₁open.inter hV₂open).inter
      (h.continuousOn.isOpen_inter_preimage h.open_source hW₁open)
  have has : a ∈ s := ⟨⟨haV₁, haV₂⟩, hasrc, by rw [hcoe]; exact hW₁mem⟩
  -- the restricted partial diffeomorphism of the model space
  have hsymm_mem : ∀ y ∈ h.target ∩ h.symm ⁻¹' s, y ∈ W₁ := by
    rintro y ⟨hy, hys⟩
    have : h (h.symm y) = y := h.right_inv hy
    have hmem : h (h.symm y) ∈ W₁ := hys.2.2
    rwa [this] at hmem
  let Pψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F ω :=
    { toPartialEquiv := h.toPartialEquiv.restr s
      open_source := h.open_source.inter hsopen
      open_target := h.continuousOn_symm.isOpen_inter_preimage h.open_target hsopen
      contMDiffOn_toFun := by
        rw [show ((h.toPartialEquiv.restr s).toFun) = ⇑h from rfl, contMDiffOn_iff_contDiffOn,
          hcoe]
        intro x hx
        have hx' : ContDiffAt 𝕜 ω ((c : M → F) ∘ f) x := hV₁sub hx.2.1.1
        exact hx'.contDiffWithinAt
      contMDiffOn_invFun := by
        rw [show ((h.toPartialEquiv.restr s).invFun) = ⇑h.symm from rfl, contMDiffOn_iff_contDiffOn,
          ← hinvcoe]
        intro y hy
        have hy' : ContDiffAt 𝕜 ω (hψsm.localInverse hψd hω0) y := hW₁sub (hsymm_mem y hy)
        exact hy'.contDiffWithinAt }
  -- compose with the inverse chart
  refine ⟨Pψ.trans (chartPartialDiffeo (f a)).symm, ⟨⟨hasrc, has⟩, ?_⟩, ?_⟩
  · show h a ∈ (chartPartialDiffeo (f a)).symm.source
    rw [hcoe]
    exact c.map_source hca
  · rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    show f x = (chartAt F (f a)).symm (h x)
    rw [hcoe]
    exact (c.left_inv (hV₂sub hx2.1.2)).symm

end CloudB3W17LocalExp
