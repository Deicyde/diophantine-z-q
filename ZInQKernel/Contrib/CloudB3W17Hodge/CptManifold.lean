/-
Original work of the Z-in-Q kernel (cloud batch 3, W17, task hodge-author). Not copied from
HodgeConjecture; see `CloudB3W17Hodge/NOTICE` and `CloudB3W17Hodge/LICENSE` for the provenance of
the vendored port under `CloudB3W17Hodge/Port/`.

# The complex points of a smooth complex scheme are an analytic manifold, on the kernel's carrier

`Bridge.lean` identifies the kernel's `ℂ`-points `CPt X` with their classical topology with the
ported `AlgebraicGeometry.Point ℂ X` with its analytic topology (`cptHomeomorph`), and transports
the ported atlas to `CPt X` (`chartedSpace`). `AtlasTransportManifold.lean` shows that an atlas
transported along a homeomorphism is a `C^n` manifold atlas.

Combining them gives the analytic manifold structure on `X(ℂ)` in the kernel's own presentation:

  `isManifold_cpt : IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CPt X)`

for `X` smooth of relative dimension `n` over `ℂ`, with `CPt X` carrying `classicalTopology X` and
`chartedSpace X n`. Together with `CloudB3W17Hodge.exists_smoothOfRelativeDimension`
(`RelativeDimension.lean`), which produces the relative dimension from `Smooth` and
`IrreducibleSpace` alone, this is the manifold content of the textbook leaf
`SmoothComplexManifold` / `SmoothComplexManifoldAn` on the kernel's carrier.

The atlas is the one `Bridge.chartedSpace` already fixed; nothing here redefines it, so the
`Cω` comparison results of `CloudB3W17GAGA` (`contMDiff_cptHomeomorph`, `cptDiffeomorph`) apply
verbatim to the same structure.

## Main results

* `CloudB3W17Hodge.isManifold_cpt`;
* `CloudB3W17Hodge.exists_chartedSpace_isManifold_of_smooth`: the `∃ n` form, at the leaf's own
  hypotheses `Smooth X.hom` and `IrreducibleSpace X.left`.
-/
import ZInQKernel.Contrib.CloudB3W17Hodge.AtlasTransportManifold
import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge
import ZInQKernel.Contrib.CloudB3W17Hodge.RelativeDimension

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Manifold ContDiff

namespace CloudB3W17Hodge

noncomputable section

attribute [local instance] CloudB3W17Hodge.classicalTopology

variable (X : Over (Spec ↧ℂ))

/-- **The complex points of a smooth complex scheme form an analytic manifold**, on the kernel's
carrier `CPt X` with its classical topology and the atlas of `Bridge.chartedSpace`. -/
theorem isManifold_cpt (n : ℕ) [SmoothOfRelativeDimension n X.hom] :
    letI : ChartedSpace (Fin n → ℂ) (CPt X) := chartedSpace X n
    IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CPt X) :=
  isManifold_homeomorph_transported ω (cptHomeomorph X)

/-- **The leaf's manifold clause, at the leaf's own hypotheses.** For `X` smooth and irreducible
over `ℂ`, there is an `n` for which `X(ℂ)`, with its classical topology, is charted on `Fin n → ℂ`
and is an analytic manifold. The relative dimension comes from
`CloudB3W17Hodge.exists_smoothOfRelativeDimension`, which needs no reducedness hypothesis. -/
theorem exists_chartedSpace_isManifold_of_smooth
    [Smooth X.hom] [IrreducibleSpace X.left] :
    ∃ (n : ℕ) (cs : ChartedSpace (Fin n → ℂ) (CPt X)),
      @IsManifold ℂ _ (Fin n → ℂ) _ _ (Fin n → ℂ) _ 𝓘(ℂ, Fin n → ℂ) ω (CPt X) _ cs := by
  obtain ⟨n, hn⟩ := exists_smoothOfRelativeDimension X.hom
  exact ⟨n, chartedSpace X n, isManifold_cpt X n⟩

end

end CloudB3W17Hodge
