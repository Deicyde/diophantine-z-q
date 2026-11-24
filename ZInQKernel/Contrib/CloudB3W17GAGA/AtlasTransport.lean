module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Cω fidelity of the choice-based transported atlas

A homeomorphism, and its inverse, are Cω for the atlas produced by
`Homeomorph.chartedSpace`. The proof uses the existing choice-based
`localInverseAt`; it replaces neither that atlas nor any point topology.
No manifold hypothesis is needed on either carrier for these two comparisons.
This minimal Mathlib-only supplier is shared by W17's H103 and H105 routes.
-/

open scoped Manifold ContDiff Topology
open Set Filter Topology

set_option autoImplicit false

public section

noncomputable section

namespace ZInQ.Contrib.CloudB3W17GAGA

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace E Y]

/-- A homeomorphism is Cω for the existing atlas transported from its target. -/
theorem contMDiff_homeomorph_transported (e : X ≃ₜ Y) :
    letI : ChartedSpace E X := Homeomorph.chartedSpace e.symm
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω e := by
  let : ChartedSpace E X := Homeomorph.chartedSpace e.symm
  change ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω e
  intro x
  rw [contMDiffAt_iff]
  refine ⟨e.continuous.continuousAt, ?_⟩
  let g : X → Y := e.symm.surjective.hasRightInverse.choose
  let l := e.symm.isLocalHomeomorph.localInverseAt (g x)
  let c := chartAt E (g x)
  have hg : e.symm (g x) = x := e.symm.surjective.hasRightInverse.choose_spec x
  have hge : g x = e x := by
    apply e.symm.injective
    rw [hg, e.symm_apply_apply]
  have hcx : chartAt E x = l.trans c := rfl
  have hl : (l.symm : Y → X) = e.symm := e.symm.isLocalHomeomorph.localInverseAt_symm (g x)
  have hlx : l x = g x := by
    calc
      l x = l (e.symm (g x)) := congrArg l hg.symm
      _ = g x := e.symm.isLocalHomeomorph.localInverseAt_apply_self
  have hcy : g x ∈ c.source := mem_chart_source E (g x)
  have hbase : (chartAt E x) x = c (g x) := by
    rw [hcx, OpenPartialHomeomorph.trans_apply, hlx]
  have heq : ((chartAt E (e x)) ∘ e ∘ (chartAt E x).symm) =ᶠ[𝓝 (c (g x))] id := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hcy)] with z hz
    rw [hcx, OpenPartialHomeomorph.coe_trans_symm, hl]
    change (chartAt E (e x)) (e (e.symm (c.symm z))) = z
    rw [e.apply_symm_apply, ← hge]
    exact c.right_inv hz
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id, hbase]
  exact (contDiffAt_id.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The inverse homeomorphism is Cω in the same existing transported atlas. -/
theorem contMDiff_homeomorph_symm_transported (e : X ≃ₜ Y) :
    letI : ChartedSpace E X := Homeomorph.chartedSpace e.symm
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω e.symm := by
  let : ChartedSpace E X := Homeomorph.chartedSpace e.symm
  change ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω e.symm
  intro y
  rw [contMDiffAt_iff]
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  let x := e.symm y
  let g : X → Y := e.symm.surjective.hasRightInverse.choose
  let l := e.symm.isLocalHomeomorph.localInverseAt (g x)
  let c := chartAt E y
  have hg : e.symm (g x) = x := e.symm.surjective.hasRightInverse.choose_spec x
  have hge : g x = y := by
    apply e.symm.injective
    exact hg
  have hcx : chartAt E x = l.trans (chartAt E (g x)) := rfl
  have hl : (l.symm : Y → X) = e.symm := e.symm.isLocalHomeomorph.localInverseAt_symm (g x)
  have hx : x ∈ l.source := by
    rw [← hg]
    exact e.symm.isLocalHomeomorph.apply_self_mem_localInverseAt_source
  have hcy : y ∈ c.source := mem_chart_source E y
  have hc : Tendsto (fun z => e.symm (c.symm z)) (𝓝 (c y)) (𝓝 x) :=
    e.symm.continuous.continuousAt.tendsto.comp (c.tendsto_symm hcy)
  have heq : ((chartAt E x) ∘ e.symm ∘ c.symm) =ᶠ[𝓝 (c y)] id := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hcy),
      hc.eventually (l.open_source.mem_nhds hx)] with z hz hzl
    have hle : l (e.symm (c.symm z)) = c.symm z := by
      apply e.symm.injective
      have h := l.left_inv hzl
      rwa [hl] at h
    simp only [Function.comp_apply, id_eq]
    rw [hcx, OpenPartialHomeomorph.trans_apply, hle, hge]
    exact c.right_inv hz
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id]
  exact (contDiffAt_id.congr_of_eventuallyEq heq).contDiffWithinAt

end ZInQ.Contrib.CloudB3W17GAGA
