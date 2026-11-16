/-
Original work of the Z-in-Q kernel (cloud batch 3, W17, task hodge-author). Not copied from
HodgeConjecture. It builds on the vendored port under `CloudB3W17Hodge/Port/`, whose provenance
and licence are recorded in `CloudB3W17Hodge/NOTICE` and `CloudB3W17Hodge/LICENSE`.

# Relative dimension of a smooth irreducible complex scheme, without reducedness

The vendored port derives a single relative dimension for a smooth complex scheme from
`IsIntegral X` (`AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension`), and identifies it
with `dim X` (`AlgebraicGeometry.SmoothOfRelativeDimension.of_isIntegral`).

The textbook leaf this contribution targets hypothesises `IrreducibleSpace X.left`, not
`IsIntegral X.left`, and `IsIntegral = IrreducibleSpace + IsReduced`. At Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` there is no route from `Smooth` to `IsReduced`: the
available statement is
`AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`, and nothing
supplies `GeometricallyReduced` from `Smooth` (there is no smooth-implies-regular in Mathlib at
this revision). `Flat X.hom`, `IsReduced (Spec ↧ℂ)` and `IsLocallyNoetherian (Spec ↧ℂ)` are all
available, so that single link is the whole obstruction.

It is not needed. In the port, `IsIntegral` enters the chart-independence argument
(`isStandardSmoothOfRelativeDimension_eq`) only through `IrreducibleSpace.isIrreducible_univ`, to
produce a point common to two nonempty affine charts; reducedness is never used. This file
re-derives the chain under `IrreducibleSpace` alone, rebuilding the port's one `private` step
(`isStandardSmoothOfRelativeDimension_le`) from its public lemmas
`orderKrullDim_eq_of_isStandardSmoothOfRelativeDimension`,
`isStandardSmoothOfRelativeDimension_appLE_basicOpen` and `orderKrullDim_mono`. No ported file is
modified.

## Main results

* `CloudB3W17Hodge.isStandardSmoothOfRelativeDimension_le`: the port's private step, rebuilt.
* `CloudB3W17Hodge.isStandardSmoothOfRelativeDimension_eq`: chart-independence from
  `IrreducibleSpace`.
* `CloudB3W17Hodge.exists_smoothOfRelativeDimension`: a smooth irreducible complex scheme is
  smooth of a single relative dimension.
-/
module

public import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
public import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates

public section

open CategoryTheory AlgebraicGeometry

namespace CloudB3W17Hodge

variable {X : Scheme} (f : X ⟶ Spec ↧ℂ)

/-- Comparison of the relative dimensions of two standard-smooth affine charts sharing a point.
This is the port's `private isStandardSmoothOfRelativeDimension_le`, rebuilt from its public
lemmas so that no ported file has to be modified. -/
lemma isStandardSmoothOfRelativeDimension_le {U V : X.Opens} {n m : ℕ}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) [Nonempty V]
    (hn : (f.appLE ⊤ U (by simp)).hom.IsStandardSmoothOfRelativeDimension n)
    (hm : (f.appLE ⊤ V (by simp)).hom.IsStandardSmoothOfRelativeDimension m)
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) : n ≤ m := by
  obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le (V := V) ⟨x, hxV⟩ hxU
  have hne : Nonempty (X.basicOpen g) := ⟨⟨x, hxg⟩⟩
  have hZ : Order.krullDim (X.basicOpen g) = n :=
    AlgebraicGeometry.orderKrullDim_eq_of_isStandardSmoothOfRelativeDimension f (hU.basicOpen g)
      (AlgebraicGeometry.isStandardSmoothOfRelativeDimension_appLE_basicOpen f hU g hn)
  have hVdim : Order.krullDim V = m :=
    AlgebraicGeometry.orderKrullDim_eq_of_isStandardSmoothOfRelativeDimension f hV hm
  have := AlgebraicGeometry.orderKrullDim_mono (X := X) hgV
  rw [hZ, hVdim] at this
  exact_mod_cast this

/-- **Chart-independence needs only irreducibility.** On an irreducible scheme the relative
dimension of a standard-smooth affine chart does not depend on the chart. The port proves this
from `IsIntegral`; reducedness plays no part. -/
lemma isStandardSmoothOfRelativeDimension_eq [IrreducibleSpace X] {U V : X.Opens} {n m : ℕ}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) [Nonempty U] [Nonempty V]
    (hn : (f.appLE ⊤ U (by simp)).hom.IsStandardSmoothOfRelativeDimension n)
    (hm : (f.appLE ⊤ V (by simp)).hom.IsStandardSmoothOfRelativeDimension m) : n = m := by
  obtain ⟨z, hzU, hzV⟩ : ((U : Set X) ∩ (V : Set X)).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U›
    obtain ⟨y⟩ := ‹Nonempty V›
    obtain ⟨z, -, hz⟩ := (IrreducibleSpace.isIrreducible_univ X).2 (U : Set X) (V : Set X) U.2 V.2
      ⟨x.1, trivial, x.2⟩ ⟨y.1, trivial, y.2⟩
    exact ⟨z, hz⟩
  exact le_antisymm
    (isStandardSmoothOfRelativeDimension_le f hU hV hn hm hzU hzV)
    (isStandardSmoothOfRelativeDimension_le f hV hU hm hn hzV hzU)

/-- **A smooth irreducible complex scheme is smooth of a single relative dimension.** This is the
port's `Smooth.exists_smoothOfRelativeDimension` with `IsIntegral` weakened to `IrreducibleSpace`,
which is exactly the hypothesis the textbook leaf supplies. -/
lemma exists_smoothOfRelativeDimension [IrreducibleSpace X] [Smooth f] :
    ∃ n : ℕ, SmoothOfRelativeDimension n f := by
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨V₀, hV₀, hx₀, hs₀⟩ := AlgebraicGeometry.Smooth.exists_affine_isStandardSmooth f x₀
  have hne₀ : Nonempty V₀ := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨n, hn⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs₀
  refine ⟨n, ⟨fun x ↦ ?_⟩⟩
  obtain ⟨V, hV, hxV, hs⟩ := AlgebraicGeometry.Smooth.exists_affine_isStandardSmooth f x
  have hne : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨m, hm⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs
  refine ⟨⊤, isAffineOpen_top _, V, hV, hxV, by simp, ?_⟩
  rwa [isStandardSmoothOfRelativeDimension_eq f hV₀ hV hn hm]

end CloudB3W17Hodge
