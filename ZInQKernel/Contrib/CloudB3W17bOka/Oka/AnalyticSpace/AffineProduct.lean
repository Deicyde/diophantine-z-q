/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.HolomorphicMapGeneral

/-!
# `ℂ^0` is terminal and `ℂ^(n+m)` is the product of `ℂ^n` and `ℂ^m`

`Oka/AnalyticSpace/HolomorphicMapGeneral.lean` gives, for **every** complex analytic space `Z`, a
bijection `Hom(Z, ℂ^m) ≃ Γ(Z, 𝒪_Z)^m` whose forward map is
`ComplexAnalytic.AnalyticSpace.coordPullback` and which is natural in `Z` by
`ComplexAnalytic.AnalyticSpace.coordPullback_comp`. This file reads two limits off it.

Splitting a tuple of `n + m` sections into a tuple of `n` and a tuple of `m` is `Fin.addCases`,
and it is a bijection natural in `Z`; a tuple of `0` sections is unique. So `ℂ^(n+m)` represents
`Z ↦ Hom(Z, ℂ^n) × Hom(Z, ℂ^m)` and `ℂ^0` represents the point. **Nothing analytic is used
below** — every argument here is `Fin.addCases`, the bijection, and its naturality
`ComplexAnalytic.AnalyticSpace.coordPullback_comp`, and the analysis is all spent in the file this
one imports.

## What the arithmetic looks like on coordinates

The `j`-th coordinate of `ℂ^n` pulls back along the first projection to the `Fin.castAdd`-th
coordinate of `ℂ^(n+m)`, and the `j`-th of `ℂ^m` along the second to the `Fin.natAdd`-th. Those
two equations are what every proof about the binary product runs on, and both are one rewrite off
`ComplexAnalytic.AnalyticSpace.coordPullback_symm_homComplexAffineSpaceEquivGeneral`. The terminal
object uses neither: `ComplexAnalytic.AnalyticSpace.isTerminalComplexAffineSpaceZero` never names
a coordinate, there being none to name.

## Main results

- `ComplexAnalytic.AnalyticSpace.affineProdFst` and
  `ComplexAnalytic.AnalyticSpace.affineProdSnd`: **the two coordinate projections**
  `ℂ^(n+m) ⟶ ℂ^n` and `ℂ^(n+m) ⟶ ℂ^m`.
- `ComplexAnalytic.AnalyticSpace.affineProdLift`: **the morphism into `ℂ^(n+m)` assembled from a
  morphism into `ℂ^n` and one into `ℂ^m`**, with
  `ComplexAnalytic.AnalyticSpace.affineProdLift_fst` and
  `ComplexAnalytic.AnalyticSpace.affineProdLift_snd` the two triangles and
  `ComplexAnalytic.AnalyticSpace.hom_ext_affineProd` its uniqueness.
- `ComplexAnalytic.AnalyticSpace.isLimitBinaryFanAffineProd`: **`ℂ^(n+m)` with those two
  projections is the binary product of `ℂ^n` and `ℂ^m`**, and
  `ComplexAnalytic.AnalyticSpace.hasBinaryProduct_complexAffineSpace` is the instance, so
  `ℂ^n ⨯ ℂ^m` is usable notation.
- `ComplexAnalytic.AnalyticSpace.isTerminalComplexAffineSpaceZero`: **`ℂ^0` is a terminal object
  of `ComplexAnalytic.AnalyticSpace`**, and
  `ComplexAnalytic.AnalyticSpace.hasTerminal_analyticSpace` is the instance.

## What is not here

* **`CategoryTheory.Limits.HasBinaryProducts ComplexAnalytic.AnalyticSpace`.** What lands here is
  the product at a *pair of affine spaces* and nothing wider. At `3d45b0c`, which is this file's
  base, `#synth CategoryTheory.Limits.HasBinaryProducts ComplexAnalytic.AnalyticSpace` fails, and
  it still fails with this file in the import closure — **both elaborated rather than grepped**,
  and the second is the one worth recording, since
  `ComplexAnalytic.AnalyticSpace.hasBinaryProduct_complexAffineSpace` below could be mistaken for
  it. **Nothing below gives the product of two arbitrary analytic spaces.**
* **The fibre product, over anything.** Neither statement here is over a base, and neither bears
  on `CategoryTheory.Limits.HasPullbacks`. The route from a binary product to a fibre product is
  an equaliser, and nothing below builds one or prices one.
* **The product of two local models.** A local model is cut out inside an open subset of some
  `ℂ^n`, and the ambient space of a product of two of them is the product supplied here; the
  cutting out is not done below, and it is a separate obligation.
* **Any description of the underlying map of `ComplexAnalytic.AnalyticSpace.affineProdFst` as a
  map of points.** The projections are defined by their coordinate pullbacks and are characterised
  by them; the base map is not computed below, and no statement here needs it.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic.AnalyticSpace

/-! ### The two coordinate projections -/

variable (n m : ℕ)

/-- **The first projection `ℂ^(n+m) ⟶ ℂ^n`**, the morphism whose `j`-th coordinate pullback is the
`Fin.castAdd`-th coordinate function of `ℂ^(n+m)`.

Defined through the inverse of `ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquivGeneral`
rather than by a formula on points: that equivalence is `Equiv.ofBijective`, so this is a choice
term, and `ComplexAnalytic.AnalyticSpace.coordPullback_affineProdFst` below is what a caller
should use instead of unfolding it. -/
noncomputable def affineProdFst :
    AnalyticSpace.complexAffineSpace.{u} (n + m) ⟶ AnalyticSpace.complexAffineSpace.{u} n :=
  (homComplexAffineSpaceEquivGeneral.{u} (AnalyticSpace.complexAffineSpace.{u} (n + m)) n).symm
    fun j ↦ coord (ULift.up (Fin.castAdd m j.down))

/-- **The second projection `ℂ^(n+m) ⟶ ℂ^m`**, the morphism whose `j`-th coordinate pullback is
the `Fin.natAdd`-th coordinate function of `ℂ^(n+m)`. -/
noncomputable def affineProdSnd :
    AnalyticSpace.complexAffineSpace.{u} (n + m) ⟶ AnalyticSpace.complexAffineSpace.{u} m :=
  (homComplexAffineSpaceEquivGeneral.{u} (AnalyticSpace.complexAffineSpace.{u} (n + m)) m).symm
    fun j ↦ coord (ULift.up (Fin.natAdd n j.down))

set_option backward.isDefEq.respectTransparency false in
/-- **The first projection pulls the `j`-th coordinate of `ℂ^n` back to the `Fin.castAdd`-th
coordinate of `ℂ^(n+m)`.** -/
@[simp]
theorem coordPullback_affineProdFst (j : ULift.{u} (Fin n)) :
    AnalyticSpace.coordPullback (affineProdFst.{u} n m) j =
      coord (ULift.up (Fin.castAdd m j.down)) := by
  unfold affineProdFst
  rw [coordPullback_symm_homComplexAffineSpaceEquivGeneral]

set_option backward.isDefEq.respectTransparency false in
/-- **The second projection pulls the `j`-th coordinate of `ℂ^m` back to the `Fin.natAdd`-th
coordinate of `ℂ^(n+m)`.** -/
@[simp]
theorem coordPullback_affineProdSnd (j : ULift.{u} (Fin m)) :
    AnalyticSpace.coordPullback (affineProdSnd.{u} n m) j =
      coord (ULift.up (Fin.natAdd n j.down)) := by
  unfold affineProdSnd
  rw [coordPullback_symm_homComplexAffineSpaceEquivGeneral]

/-! ### The pair of a morphism to `ℂ^n` and a morphism to `ℂ^m` -/

variable {n m}

/-- **The morphism into `ℂ^(n+m)` assembled from a morphism into `ℂ^n` and one into `ℂ^m`.**

Its tuple of coordinate pullbacks is `Fin.addCases` of the two given tuples, which is where the
two morphisms are combined; `ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquivGeneral`
turns that tuple back into a morphism. **`Oka/AnalyticSpace/HolomorphicMapGeneral.lean` describes
this operation in the section of its module docstring on why `ℂ^m` is not built as a product, and
says that file does not take it**; the order is not an accident, since this definition consumes
that file's bijection and so the bijection cannot have been proved from it. -/
noncomputable def affineProdLift {Z : AnalyticSpace.{u}}
    (f : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n)
    (g : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m) :
    Z ⟶ AnalyticSpace.complexAffineSpace.{u} (n + m) :=
  (homComplexAffineSpaceEquivGeneral.{u} Z (n + m)).symm fun j ↦
    Fin.addCases (fun a ↦ AnalyticSpace.coordPullback f (ULift.up a))
      (fun b ↦ AnalyticSpace.coordPullback g (ULift.up b)) j.down

/-- **The coordinate pullbacks of `ComplexAnalytic.AnalyticSpace.affineProdLift` are the tuple it
was built from**, with no choice term left in the statement. -/
@[simp]
theorem coordPullback_affineProdLift {Z : AnalyticSpace.{u}}
    (f : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n)
    (g : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m) (j : ULift.{u} (Fin (n + m))) :
    AnalyticSpace.coordPullback (affineProdLift.{u} f g) j =
      Fin.addCases (fun a ↦ AnalyticSpace.coordPullback f (ULift.up a))
        (fun b ↦ AnalyticSpace.coordPullback g (ULift.up b)) j.down := by
  unfold affineProdLift
  rw [coordPullback_symm_homComplexAffineSpaceEquivGeneral]

/-- **The pair followed by the first projection is the first morphism.**

Three steps, and each is named: `ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace`
reduces the equation of morphisms to an equation of coordinate pullbacks,
`ComplexAnalytic.AnalyticSpace.coordPullback_comp` turns the pullback along a composite into a
pullback of a pullback, and `Fin.addCases_left` evaluates the tuple at a `Fin.castAdd` index. -/
theorem affineProdLift_fst {Z : AnalyticSpace.{u}}
    (f : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n)
    (g : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m) :
    affineProdLift.{u} f g ≫ affineProdFst.{u} n m = f := by
  refine AnalyticSpace.hom_ext_complexAffineSpace _ _ fun j ↦ ?_
  have h := AnalyticSpace.coordPullback_comp (affineProdLift.{u} f g) (affineProdFst.{u} n m) j
  rw [coordPullback_affineProdFst] at h
  have hj : AnalyticSpace.coordPullback (affineProdLift.{u} f g)
      (ULift.up (Fin.castAdd m j.down)) = AnalyticSpace.coordPullback f j := by
    rw [coordPullback_affineProdLift]
    simp
  exact h.trans hj

/-- **The pair followed by the second projection is the second morphism**, by the argument
`ComplexAnalytic.AnalyticSpace.affineProdLift_fst` gives with `Fin.addCases_right` in place of
`Fin.addCases_left`. -/
theorem affineProdLift_snd {Z : AnalyticSpace.{u}}
    (f : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n)
    (g : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m) :
    affineProdLift.{u} f g ≫ affineProdSnd.{u} n m = g := by
  refine AnalyticSpace.hom_ext_complexAffineSpace _ _ fun j ↦ ?_
  have h := AnalyticSpace.coordPullback_comp (affineProdLift.{u} f g) (affineProdSnd.{u} n m) j
  rw [coordPullback_affineProdSnd] at h
  have hj : AnalyticSpace.coordPullback (affineProdLift.{u} f g)
      (ULift.up (Fin.natAdd n j.down)) = AnalyticSpace.coordPullback g j := by
    rw [coordPullback_affineProdLift]
    simp
  exact h.trans hj

/-- **A morphism into `ℂ^(n+m)` is determined by its two projections.**

`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` asks for the pullbacks of the `n + m`
coordinates to agree, and `Fin.addCases` splits that obligation into the two the hypotheses
supply: a coordinate of `ℂ^(n+m)` is the pullback of a coordinate of `ℂ^n` along the first
projection or of one of `ℂ^m` along the second, which is
`ComplexAnalytic.AnalyticSpace.coordPullback_affineProdFst` and
`ComplexAnalytic.AnalyticSpace.coordPullback_affineProdSnd` read backwards. -/
theorem hom_ext_affineProd {Z : AnalyticSpace.{u}}
    (φ ψ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} (n + m))
    (h₁ : φ ≫ affineProdFst.{u} n m = ψ ≫ affineProdFst.{u} n m)
    (h₂ : φ ≫ affineProdSnd.{u} n m = ψ ≫ affineProdSnd.{u} n m) :
    φ = ψ := by
  refine AnalyticSpace.hom_ext_complexAffineSpace _ _ fun j ↦ ?_
  obtain ⟨j⟩ := j
  induction j using Fin.addCases with
  | left a =>
    have e : ∀ χ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} (n + m),
        (LocallyRingedSpace.Γ.map χ.toLRSHom.op).hom (coord (ULift.up (Fin.castAdd m a))) =
          AnalyticSpace.coordPullback (χ ≫ affineProdFst.{u} n m) (ULift.up a) := fun χ ↦ by
      rw [AnalyticSpace.coordPullback_comp, coordPullback_affineProdFst]
    rw [e φ, e ψ, h₁]
  | right b =>
    have e : ∀ χ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} (n + m),
        (LocallyRingedSpace.Γ.map χ.toLRSHom.op).hom (coord (ULift.up (Fin.natAdd n b))) =
          AnalyticSpace.coordPullback (χ ≫ affineProdSnd.{u} n m) (ULift.up b) := fun χ ↦ by
      rw [AnalyticSpace.coordPullback_comp, coordPullback_affineProdSnd]
    rw [e φ, e ψ, h₂]

/-! ### `ℂ^(n+m)` is the binary product -/

variable (n m)

/-- **`ℂ^(n+m)` with its two coordinate projections, as a binary fan** over `ℂ^n` and `ℂ^m`. -/
noncomputable def binaryFanAffineProd :
    BinaryFan (AnalyticSpace.complexAffineSpace.{u} n) (AnalyticSpace.complexAffineSpace.{u} m) :=
  BinaryFan.mk (affineProdFst.{u} n m) (affineProdSnd.{u} n m)

/-- **`ℂ^(n+m)` is the product of `ℂ^n` and `ℂ^m` in `ComplexAnalytic.AnalyticSpace`.**

The lift is `ComplexAnalytic.AnalyticSpace.affineProdLift` at the cone's two legs, the two
triangles are `ComplexAnalytic.AnalyticSpace.affineProdLift_fst` and
`ComplexAnalytic.AnalyticSpace.affineProdLift_snd`, and uniqueness is
`ComplexAnalytic.AnalyticSpace.hom_ext_affineProd`, which asks exactly what
`CategoryTheory.Limits.BinaryFan.isLimitMk` supplies. -/
noncomputable def isLimitBinaryFanAffineProd : IsLimit (binaryFanAffineProd.{u} n m) :=
  BinaryFan.isLimitMk (fun s ↦ affineProdLift.{u} s.fst s.snd)
    (fun s ↦ affineProdLift_fst.{u} s.fst s.snd) (fun s ↦ affineProdLift_snd.{u} s.fst s.snd)
    fun _ _ h₁ h₂ ↦ hom_ext_affineProd.{u} _ _ (by rw [h₁, affineProdLift_fst])
      (by rw [h₂, affineProdLift_snd])

/-- **The binary product of two complex affine spaces exists**, so `ℂ^n ⨯ ℂ^m` is usable notation.

`CategoryTheory.Limits.HasBinaryProduct` is `Prop`-valued, so this instance loses the
identification of the product with `ℂ^(n+m)`;
`ComplexAnalytic.AnalyticSpace.isLimitBinaryFanAffineProd` is what keeps it and is what a caller
who wants the coordinates should use. -/
instance hasBinaryProduct_complexAffineSpace :
    HasBinaryProduct (AnalyticSpace.complexAffineSpace.{u} n)
      (AnalyticSpace.complexAffineSpace.{u} m) :=
  ⟨⟨⟨_, isLimitBinaryFanAffineProd.{u} n m⟩⟩⟩

/-! ### `ℂ^0` is terminal -/

/-- **`ℂ^0` is a terminal object of `ComplexAnalytic.AnalyticSpace`.**

`ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquivGeneral` at `m = 0` is a bijection from
`Hom(Z, ℂ^0)` to the functions out of `ULift (Fin 0)`, of which there is one; both halves of
`CategoryTheory.Limits.IsTerminal.ofUniqueHom` are therefore `Fin.elim0`, the existence half
through the inverse of the bijection and the uniqueness half through its injectivity.

**This is the empty product** and shares its argument with
`ComplexAnalytic.AnalyticSpace.isLimitBinaryFanAffineProd`: in both, splitting the coordinates of
the target is what makes the universal property a statement about tuples of sections. -/
noncomputable def isTerminalComplexAffineSpaceZero :
    IsTerminal (AnalyticSpace.complexAffineSpace.{u} 0) :=
  IsTerminal.ofUniqueHom
    (fun Z ↦ (homComplexAffineSpaceEquivGeneral.{u} Z 0).symm fun j ↦ j.down.elim0)
    fun Z _ ↦ (homComplexAffineSpaceEquivGeneral.{u} Z 0).injective
      (funext fun j ↦ j.down.elim0)

/-- **`ComplexAnalytic.AnalyticSpace` has a terminal object**, witnessed by `ℂ^0`.

`CategoryTheory.Limits.HasTerminal` is `Prop`-valued and so records only that a terminal object
exists; `ComplexAnalytic.AnalyticSpace.isTerminalComplexAffineSpaceZero` is what says which one it
is, and a caller who needs `⊤_ ComplexAnalytic.AnalyticSpace` to *be* `ℂ^0` should use that. -/
instance hasTerminal_analyticSpace : HasTerminal AnalyticSpace.{u} :=
  isTerminalComplexAffineSpaceZero.{u}.hasTerminal

end ComplexAnalytic.AnalyticSpace
