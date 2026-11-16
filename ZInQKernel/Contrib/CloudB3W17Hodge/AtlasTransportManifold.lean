/-
Original work of the Z-in-Q kernel (cloud batch 3, W17, task hodge-author). Not copied from
HodgeConjecture; see `CloudB3W17Hodge/NOTICE` and `CloudB3W17Hodge/LICENSE` for the provenance of
the vendored port under `CloudB3W17Hodge/Port/`.

# A manifold structure transported along a homeomorphism

`Homeomorph.chartedSpace` gives the source of a homeomorphism `e : X ≃ₜ Y` a `ChartedSpace E X`
by pushing forward the atlas of `Y`. This file proves that this transported atlas is a `C^n`
manifold atlas whenever `Y` is a `C^n` manifold, which Mathlib does not record at
`56a005855ea17e0b0958f73ec801ae140b0a1679`: there is no `HasGroupoid` or `IsManifold` transfer
along a local homeomorphism anywhere in the library.

The obstacle is that `Homeomorph.chartedSpace` is built from
`IsLocalHomeomorph.chartedSpaceOfRightInverse`, whose charts are
`(localInverseAt (g x)).trans (chartAt E (g x))` for a choice-based right inverse `g` and a
choice-based local inverse `localInverseAt`. Neither choice is accessible.

It does not need to be. `e.symm` is a *global* homeomorphism, so any of its local inverses is
pinned: on the source of `localInverseAt y` it must agree with `e` itself
(`localInverseAt_eq`, from `localInverseAt_symm` and injectivity of `e.symm`). With that, a
transition of the transported atlas,

  `((lₐ ≫ₕ cₐ).symm ≫ₕ (l_b ≫ₕ c_b))`,

is shown to agree on its source with the transition `cₐ.symm ≫ₕ c_b` of the atlas of `Y`, whose
`ContDiffOn` is exactly `HasGroupoid.compatible` for `Y`. The middle factor `l_b ∘ e.symm`
cancels pointwise, the choice functions never have to be identified, and the atlas is left
unchanged.

This is the last ingredient for the analytic-manifold structure on the complex points of a
smooth complex scheme in the kernel's own presentation; `Bridge.lean` supplies the carrier,
topology and chart transport, and `AtlasManifold.isManifold_cpt` below assembles the manifold
instance on `CPt X`.

## Main results

* `CloudB3W17Hodge.localInverseAt_eq`: a local inverse of a global homeomorphism agrees with it;
* `CloudB3W17Hodge.isManifold_homeomorph_transported`: the generic transport, Mathlib-only;
* `CloudB3W17Hodge.isManifold_cpt`: `IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CPt X)` for the kernel's
  carrier and classical topology, for `X` smooth of relative dimension `n` over `ℂ`.
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

public section

open scoped Manifold ContDiff Topology
open Set Filter

namespace CloudB3W17Hodge

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace E Y]

/-- **A local inverse of a global homeomorphism is that homeomorphism.** On the source of
`e.symm.isLocalHomeomorph.localInverseAt y`, the choice-based local inverse agrees with `e`. -/
theorem localInverseAt_eq (e : X ≃ₜ Y) (y : Y) {x : X}
    (hx : x ∈ (e.symm.isLocalHomeomorph.localInverseAt y).source) :
    (e.symm.isLocalHomeomorph.localInverseAt y) x = e x := by
  have h1 := (e.symm.isLocalHomeomorph.localInverseAt y).left_inv hx
  rw [e.symm.isLocalHomeomorph.localInverseAt_symm y] at h1
  exact e.symm.injective (by rw [h1, e.symm_apply_apply])

/-- **The atlas transported along a homeomorphism is a `C^n` manifold atlas.** If `Y` is a `C^n`
manifold modelled on `E` and `e : X ≃ₜ Y`, then `X` with the atlas `Homeomorph.chartedSpace e.symm`
is a `C^n` manifold. The atlas is the one Mathlib builds; it is not replaced. -/
theorem isManifold_homeomorph_transported (n : ℕ∞ω) [IsManifold 𝓘(𝕜, E) n Y] (e : X ≃ₜ Y) :
    letI : ChartedSpace E X := Homeomorph.chartedSpace e.symm
    IsManifold 𝓘(𝕜, E) n X := by
  let _ : ChartedSpace E X := Homeomorph.chartedSpace e.symm
  apply isManifold_of_contDiffOn
  intro c₁ c₂ h₁ h₂
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  set g := e.symm.surjective.hasRightInverse.choose with hg
  set la := e.symm.isLocalHomeomorph.localInverseAt (g a) with hla
  set lb := e.symm.isLocalHomeomorph.localInverseAt (g b) with hlb
  set ca := chartAt E (g a) with hca
  set cb := chartAt E (g b) with hcb
  have hcompat := HasGroupoid.compatible (G := contDiffGroupoid n 𝓘(𝕜, E))
    (chart_mem_atlas E (g a)) (chart_mem_atlas E (g b))
  have hcd : ContDiffOn 𝕜 n ⇑(ca.symm ≫ₕ cb) (ca.symm ≫ₕ cb).source := by
    have h := hcompat.1
    simpa [contDiffPregroupoid, OpenPartialHomeomorph.trans_source] using h
  have hpt : ∀ z ∈ ((la ≫ₕ ca).symm ≫ₕ (lb ≫ₕ cb)).source,
      z ∈ (ca.symm ≫ₕ cb).source ∧
        ((la ≫ₕ ca).symm ≫ₕ (lb ≫ₕ cb)) z = (ca.symm ≫ₕ cb) z := by
    intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    obtain ⟨hzA, hzB⟩ := hz
    rw [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_target] at hzA
    obtain ⟨hzca, hzla⟩ := hzA
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hzB
    obtain ⟨hzB1, hzB2⟩ := hzB
    have hw : ((la ≫ₕ ca).symm) z = e.symm (ca.symm z) := by
      rw [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
        e.symm.isLocalHomeomorph.localInverseAt_symm (g a)]
    rw [hw] at hzB1 hzB2
    rw [Set.mem_preimage] at hzB2
    have hlbw : lb (e.symm (ca.symm z)) = ca.symm z := by
      rw [localInverseAt_eq e (g b) hzB1, e.apply_symm_apply]
    rw [hlbw] at hzB2
    constructor
    · rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      exact ⟨hzca, hzB2⟩
    · rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hw,
        OpenPartialHomeomorph.coe_trans, Function.comp_apply, hlbw,
        OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ]
  exact (hcd.mono fun z hz => (hpt z hz).1).congr fun z hz => (hpt z hz).2

end

end CloudB3W17Hodge
