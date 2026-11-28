# One-dimensional abelian varieties and Weierstrass models

## Scope and exact object definitions

S2a in `ZInQKernel/Contrib/CloudB3RC53/ModularWeil/DifferentialLine.lean`, lines 16–20,
is a prose reading translation, not an existing Lean declaration. Its statement that the
abelian-variety objects are absent is superseded by the actual objects in the tree.

* `PkgI3.AbVar`, in `ZInQKernel/HDecomp/Objects.lean`, lines 162–181, is a group object `X`
  over the spectrum of a field with proper, smooth and geometrically integral structure
  morphism. `dim A` is `topologicalKrullDim A.X.left`.
* `PkgI2.IsAbelianVariety`, Objects, lines 794–797, places the same three conditions on an
  object of `Grp (Over (Spec k))`.
* `PkgI2.IsAbelianScheme`, Objects, lines 801–804, uses properness, smoothness and geometrically
  connected fibres. `SchemeBridge.lean` derives geometric integrality using the proved
  `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`; it does not assume that the two
  geometric predicates are definitionally interchangeable.

## Proved without printed inputs

1. The actual generic stalk of a one-dimensional integral finite-type scheme is an algebraic
   function field of one variable. This means finite over a rational function subfield, not
   a claim that it is purely rational.
2. Geometric integrality makes the rational constants exact in that function field. Extension
   of constants to any field leaves a domain.
3. A smooth integral rational scheme of dimension one is smooth of relative dimension one;
   its local rings are regular, its closed-point local rings are discrete valuation rings,
   and every local ring is a valuation ring.
4. The identity is an actual rational section and a closed point. Its residue field is the
   rational field. Its local ring constructs a normalized place of degree one; the place's
   valuation ring is exactly the image of that local ring in the generic stalk.
5. Global regular functions on a proper geometrically integral scheme are constants. Thus the
   global sections of a trivial line sheaf have ground-field dimension one. This proves the
   rank-one case of Milne IV.6.6 used here.
6. A generic-point map from an integral scheme with valuation local rings to a proper scheme
   extends over the whole source by the valuative criterion. A specified function-field
   isomorphism between two such proper rational schemes extends in both directions to a
   rational scheme isomorphism, inducing that same field map.
7. All local rings of a nonsingular projective Weierstrass model are valuation rings. Off
   infinity its affine chart is a Dedekind domain; at infinity the existing projective-model
   identification supplies the discrete valuation ring.
8. A comparison based on the identity's pole-order-two first coordinate sends the actual
   identity point to the actual point at infinity.

These results include the complete function-field and identity-place parts of S2a, and the
scheme comparison needed after a Weierstrass function-field model has been obtained.

## Conditional S2a conclusion

The main results are `abelian_projectiveWeierstrassModel`,
`abVar_projectiveWeierstrassModel`, `groupAbVar_projectiveWeierstrassModel`, and
`abelianScheme_projectiveWeierstrassModel`, in namespace
`ZInQ.Contrib.RC53Assist.AbelianCurve`.

After exactly the two inputs below, every actual one-dimensional rational abelian variety
has a nonsingular Weierstrass equation and an isomorphism to its actual projective model
**over the rational numbers**, sending the identity to infinity. The pullback of rational
functions is the field identification produced by the proved Riemann–Roch construction.

The equation is obtained through the proved
`ZInQ.Contrib.RC53Assist.InvariantDifferential.s2b_rational`. The stronger coordinate result
uses `exists_weierstrassModel_of_genus_eq_one` at the constructed identity place, so the
coordinate functions have their sole poles there, of orders two and three. The scheme's
function field is the existing `IsogenyScheme.projFunctionFieldEquiv`, not an assumed model
identification.

## Mathematical inputs of these reductions (both now proved)

### `InvariantDifferentialTrivialization`

For a smooth integral group curve of finite type over the rational numbers, the **actual**
relative Kähler differential sheaf is a trivial line sheaf. Finite type is represented by
smoothness and explicit quasi-compactness. The sheaf is defined by the same sheafification
as `Scheme.Hom.relativeDifferentials` in the vendored Jacobian library.

**Cited source:** Milne, *Abelian varieties*, version 2.00, March 16, 2008,
**Chapter IV, Proposition 6.4(a)–(b), printed p. 152**. It states that the differential sheaf of
 a smooth variety of dimension `g` is locally free of rank `g`, and is free for a group variety.
The manuscript's bibliography contains this exact notes edition as **`milne-av`**, at
`diophantine_zq.tex`, lines 11024–11026. This is **not** Chapter I, Theorem 6.4 or Proposition 6.6,
which concern projectivity and ample divisors. Chapter IV, Proposition 6.6, also on p. 152,
is the global-sections assertion whose rank-one case is proved here.

The cited notes were read directly from <https://www.jmilne.org/math/CourseNotes/AV.pdf>.

### `RegularDifferentialComparison`

For every smooth proper geometrically integral rational curve, the global sections of its
actual differential sheaf are ground-field-linearly equivalent to
`TauCeti.weilDifferentialFiltration (0 : TauCeti.Divisor ℚ X.functionField)`.
The mathematical comparison is the residue pairing on repartitions. The input asks only
for the resulting linear equivalence, a consequence of the canonical comparison, not an
arbitrary assertion that the genus equals one.

**Cited source for rational and regular curve differentials:** Silverman, manuscript
bibitem **`silverman`**, *The Arithmetic of Elliptic Curves*, second edition,
Chapter II, §§4–5. **Not cited in the manuscript:** Stichtenoth, *Algebraic Function Fields and
Codes*, second edition, §I.5, Definition 1.5.1 and Remark 1.5.12, for the particular
Weil-repartition representation used by Tau Ceti. The Stichtenoth locator is taken from the
vendored library's references; it is not claimed to have been checked against a page image
of that book.

Neither input asserts an elliptic function field, a Weierstrass model, or a scheme
isomorphism. Both are definitions of propositions used as hypotheses, **not axioms**.
Both are now proved, by `ZInQ.Contrib.RC53Assist.GroupDifferentials.invariantDifferentialTrivialization`
(`ZInQKernel/Contrib/RC53Assist/GroupDifferentials/Trivialization.lean`) and
`ZInQ.Contrib.RC53Assist.AbelianCurveInputs.LocalFacts.regularDifferentialComparison`
(`ZInQKernel/Contrib/RC53Assist/AbelianCurveInputs/LocalFacts.lean`);
`ZInQKernel/Contrib/RC53Assist/GroupDifferentials/S2a.lean` states the genus-one assertion and the
full S2a conclusion without hypotheses.
No extra normal-model, projective-model, rational-place, or birational-extension input remains
in these reductions.

## Files

* `FunctionField.lean`: dimension, one-variable function fields, exact constants.
* `IdentityPlace.lean`: the actual identity section, residue field, and normalized local place.
* `SmoothCurve.lean`: relative dimension, regular/DVR/valuation local rings, rational place.
* `DifferentialLine.lean`: the actual differential sheaf, constant global functions, trivial-line
  dimension, the two precise inputs, and the genus-one reduction.
* `WeierstrassReduction.lean`: the proved S2b and its identity-based coordinate construction.
* `BirationalComparison.lean`: the proved extension and faithful scheme comparison.
* `ProjectiveComparison.lean`: the actual proper projective model, its valuation local rings,
  and the pointed scheme-level reduction.
* `ObjectBridge.lean`: specialization to `PkgI3.AbVar` and `PkgI2.IsAbelianVariety`.
* `SchemeBridge.lean`: specialization to the actual `PkgI2.IsAbelianScheme` definition.

Exact declaration signatures and the compiler's axiom output accompany this directory.

## Read-only verification

The two supplied head modules `InvariantDifferential/WeierstrassModel.lean` and
`IsogenyScheme/ProjectiveModel.lean` have no object files in the existing build tree.
`HDecomp/Objects.lean` and several geometric-integrality dependencies also lack them.
Accordingly verification checks their source proofs together with these new files, without
building dependencies or writing object files.

`Scratch/ObjectsContext.lean` reproduces the exact three object definitions and dimension
used from Objects, with no fields added or removed. `Scratch/Assemble.py` makes each source's
scope explicit and resolves the imported Tau Ceti files' intended `Ideal` opens as
`_root_.Ideal`, because the combined import context also contains `TauCeti.Ideal`. It does
not change their mathematical statements or proof steps. Existing source files are untouched.

Reproduction from the repository root:

```text
python3 ZInQKernel/Contrib/RC53Assist/AbelianCurve/Scratch/GenerateAudit.py ZInQKernel/Contrib/RC53Assist/AbelianCurve/Scratch/ReviewAudit.lean
lake env lean ZInQKernel/Contrib/RC53Assist/AbelianCurve/Scratch/ReviewAudit.lean
```

Use the specified six-thread, CPU-affinity and niceness settings for the compiler invocation.
The source generator refuses to overwrite an existing source check. The scratch check emits
exact types and axiom dependencies; the nine contribution sources contain no checking or
printing commands.

No existing file was edited, no object file was produced, and no repository history operation
or dependency update was performed.
