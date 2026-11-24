# Invariant differentials of group schemes

This directory proves `ZInQ.Contrib.RC53Assist.AbelianCurve.InvariantDifferentialTrivialization`
(`AbelianCurve/DifferentialLine.lean`), the only remaining input of S2a, and records the
resulting S2a statements without hypotheses. Nothing is assumed: there is no printed input,
no `sorry`, and no new axiom. Every declaration depends only on `propext`, `Classical.choice`
and `Quot.sound`.

## Literature

J. S. Milne, *Abelian varieties*, version 2.00 (March 16, 2008), Chapter IV, Proposition 6.4,
printed page 152 (page 158 of <https://www.jmilne.org/math/CourseNotes/AV.pdf>, 1291594 bytes,
SHA-256 `f5ca4e63e5092a4b102daad1470e4cbed5fe8f82115e3a28c8881e3f67f6aaef`; manuscript bibitem
`milne-av`). Verbatim:

> PROPOSITION 6.4. Let V be a smooth algebraic variety of dimension g over a field k.
> (a) The sheaf of differentials Ω¹_{V/k} on V is a locally free sheaf of O_V-modules of rank g.
> (b) If V is a group variety, then Ω¹ is free.

The printed proof refers to Springer, *Linear Algebraic Groups*, 3.2–3.3. The proof here is
the scheme-theoretic shearing argument instead, which also covers non-affine groups.

## Main results

All in namespace `ZInQ.Contrib.RC53Assist.GroupDifferentials`.

* `invariantDifferentialTrivialization : AbelianCurve.InvariantDifferentialTrivialization`
  (`Trivialization.lean`). The quasi-compactness hypothesis of that proposition is not used.
* `nonempty_relativeDifferentials_iso_unit_of_grpObj`: over any field, a group scheme smooth of
  relative dimension one has `Ω ≅ 𝒪`.
* `exists_free_iso_relativeDifferentials_of_grpObj`: over any field, the differential sheaf of
  any group scheme is free (Milne IV.6.4(b) as printed, without smoothness).
* `nonempty_relativeDifferentials_iso_free_of_grpObj` (`HigherDimension.lean`): over any field,
  a group scheme smooth of relative dimension `d` has `Ω ≅ 𝒪^d`.
* `differentialsComparison` (`Comparison.lean`): the reduction's sheaf `differentialSheaf`
  (sheafified presheaf differentials over the presheaf inverse image) is isomorphic to the
  vendored Stacks-project sheaf representing derivations over the sheaf inverse image.
* `abVar_projectiveWeierstrassModel_unconditional` and its siblings (`S2a.lean`): pointed
  scheme-level S2a for `PkgI3.AbVar`, `PkgI2.IsAbelianVariety`, `PkgI2.IsAbelianScheme` and a
  bare proper smooth geometrically integral group curve, with no remaining hypothesis.
* `NonVacuity.lean`: the multiplicative group `Spec ℚ[T, T⁻¹]` satisfies all hypotheses of
  `InvariantDifferentialTrivialization`, and the theorems are applied to it.

## Proof

1. Translation invariance. For a group scheme `π : G ⟶ S` with identity `e`,
   `Ω_{G/S} ≅ π^* e^* Ω_{G/S}`: the shearing automorphism `(g, h) ↦ (g h, h)` of `G ×_S G`
   identifies `μ^* Ω` and `pr₁^* Ω` with `Ω_{(G ×_S G)/G}` by base change of differentials
   (Stacks Project, Lemma 29.33.10, Tag 01V0), and one pulls back along `g ↦ (e(π g), g)`.
   This is proved in the vendored AxiomMath/Stacks code
   (`ZInQKernel/Contrib/CloudB3W16Cartier/GroupDifferentials.lean`) for the sheaf
   construction of `Ω`, and transported along `differentialsComparison`.
2. Comparison of the two constructions of `Ω` (`Comparison.lean`). Both represent derivations
   into sheaves of modules. A derivation into a sheaf of modules that kills the presheaf
   inverse image also kills the sheaf inverse image: read as the ring map
   `a ↦ (a, D a)` into the square-zero extension, its composite with the sheaf structure map
   is determined by its adjunct, which is determined by the values on `f^♯ a`.
3. The fibre at the identity. Smoothness of relative dimension `d` gives a neighbourhood of
   every point on which `Ω` is free of rank `d` (standard-smooth charts; vendored
   Jacobian-Challenge code for `d = 1`, `HigherDimension.lean` for general `d`). A point
   `Spec k ⟶ G` factors through such a neighbourhood, so `e^* Ω` is free, and pullback
   preserves free sheaves.
4. A smooth integral group curve over the rationals is smooth of relative dimension one
   (`AbelianCurve.smooth_relativeDimension_one`).

## Files

* `Comparison.lean`: the two constructions of `Ω_{X/S}` agree.
* `Trivialization.lean`: translation invariance, triviality at the identity, the target.
* `HigherDimension.lean`: the rank-`d` version.
* `S2a.lean`: S2a statements without remaining hypotheses.
* `NonVacuity.lean`: the multiplicative group as a witness.

## Build

From the repository root:

```text
lake build +ZInQKernel.Contrib.RC53Assist.GroupDifferentials.S2a \
  +ZInQKernel.Contrib.RC53Assist.GroupDifferentials.HigherDimension \
  +ZInQKernel.Contrib.RC53Assist.GroupDifferentials.NonVacuity
```

The vendored Jacobian-Challenge and AxiomMath/Stacks modules imported here had no object files
in the integration build; building these targets compiles them. No existing source file is
changed.
