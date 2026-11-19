# Equal-dimensional surjective homomorphisms of abelian varieties are finite

**Proved (VERIFIED in Lean).** `ShimuraSteps.sameDimSurjectiveFinite` has exactly the
existing type `ShimuraSteps.SameDimSurjectiveFinite`. Thus
`ShimuraSteps.shimuraThm1Af_of_printed'` derives the existing quotient row from the
printed-form statement and the composite Jacobian Hecke relations. The finiteness
proof adds no hypothesis. The source is
[`SameDimFinite.lean`](../../ZInQKernel/Contrib/OneProof/SameDimFinite.lean).

The proof uses dimension equals transcendence degree
(`ZInQ.Contrib.Dim.topologicalKrullDim_eq_trdeg_functionField`). A surjection
maps generic point to generic point. The induced extension of function fields
has transcendence degree zero by additivity (Mathlib `trdeg_add_eq`), and is
essentially of finite type, so it is finite. Thus the source generic point is
quasi-finite. Its singleton in the generic fibre is closed and dense, so it
is the only point there. The generic fibre is proper and locally of finite type;
its singleton underlying space makes it quasi-finite, hence finite.

Over the algebraic closure of the source function field, the generic fibre through
the canonical point is still finite by base change. Its rational points inject
into the algebra maps out of a finite algebra. The geometric kernel over
`AlgebraicClosure k` injects into those points by extending scalars and translating
by the canonical point. This uses the existing `AbVarBC.extPt_injective`.
`PicDict.finiteOfFiniteKerPts` then gives the conclusion: it translates fibres on
geometric points, obtains quasi-finiteness everywhere from the closed points
and the Jacobson property, and uses proper plus quasi-finite implies finite.
This route needs only the generic fibre and no general theorem on dimension of fibres.

## Lean statements

VERIFIED. The two exported theorems in namespace `ShimuraSteps` are:

```lean
theorem sameDimSurjectiveFinite : SameDimSurjectiveFinite
theorem shimuraThm1Af_of_printed' :
    ShimuraThm1AsPrinted → ShimuraHeckeRelations → R16Thm1b.ShimuraThm1Af
```

Here `SameDimSurjectiveFinite` quantifies over `A B : PkgI3.AbVar ℚ` and
`f : PkgI3.AbVar.Hom A B` and says
`A.dim = B.dim → Surjective f.hom.left → IsFinite f.hom.left`.

The private theorems have the following statements. In the scheme lemmas
`k` and `L` are fields in `Type`, and `X` and `Y` are schemes in universe zero.

| Theorem | Statement |
| --- | --- |
| `genericPoint_map` | A surjection between integral schemes maps the source generic point to the target generic point. |
| `fromSpecStalk_generic_comp` | For integral `X` over `Spec k`, the canonical morphism `Spec k(X) ⟶ X` composed with the structure map is induced by the structural algebra map `k → k(X)`. |
| `functionField_essFiniteType` | With the same structural algebra, the function field of an integral scheme locally of finite type over `k` is essentially of finite type over `k`. |
| `quasiFiniteAt_generic_of_sameDim` | For equal-dimensional integral schemes locally of finite type over `k`, a surjective morphism over `k` which is locally of finite type is quasi-finite at the source generic point. |
| `subsingleton_genericFiber` | A surjective, locally finite type morphism of integral schemes, quasi-finite at the source generic point, has a subsingleton generic fibre. |
| `finite_genericFiber` | A proper surjection of integral schemes, quasi-finite at the source generic point, has finite generic fibre over the target generic residue field. |
| `finite_geometricGenericFiber` | If a morphism into an integral scheme has finite generic fibre, its pullback along an `L`-point with generic image is finite over `Spec L`. |
| `finite_sections` | A finite scheme over `Spec L` has finitely many sections over `Spec L`. |
| `finite_kerPts_of_sameDim` | A surjective homomorphism of equal-dimensional abelian varieties over `k` has finitely many kernel points over `AlgebraicClosure k`. |

## Fold status

VERIFIED. The stock `#discharges` command matches the two-input theorem against
the exact type of the `shimuraThm1Af` row. The scratch harness checks this one type;
it does not validate the full assembly. See
[`Discharges-output.txt`](../../scratch/samedim-finite/Discharges-output.txt)
and [`Axioms-output.txt`](../../scratch/samedim-finite/Axioms-output.txt).
The proof and all its new helpers use only `propext`, `Classical.choice` and `Quot.sound`.

| Criterion | Before | Proposed after | Actual after |
| --- | --- | --- | --- |
| strict | 5 LEAF / 24 GLUE | 6 LEAF / 24 GLUE | 5 LEAF / 24 GLUE |
| strictest | 5 LEAF / 24 GLUE | 6 LEAF / 24 GLUE | 5 LEAF / 24 GLUE |

The [spec](../../scratch/samedim-finite/autofold.json) and
[`--dry-run` output](../../scratch/samedim-finite/autofold-dryrun.txt)
replace the quotient row with `ShimuraThm1AsPrinted` (published, flag
`AI page read pp. 525-527`) and `ShimuraHeckeRelations` (consequence, on-the-spot
GLUE). The guard accepts the proposal. No fold was performed.

## Known issues

- The prior recorded AI page read flags a misprint on Shimura p. 526, before
  clause (iv): the conjugate eigenvalue multiplies the conjugate form. That
  sentence is outside the quotient clauses used here. See
  [the source audit](shimura-steps.md#known-issues).
- The Euler-factor identity in the citation is total over embeddings. This
  contribution concerns the quotient and its uniqueness and does not verify
  the manuscript's identification of a particular Tate constituent.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict | Check |
| --- | --- | --- |
| L770–771 | OK | The Shimura citation supplies the quotient construction, per the recorded AI page read of pp. 525–527. |
| L770–773, uniqueness | gap filled | The manuscript omits uniqueness. The formal quotient row needs a projection-compatible isomorphism; the induced surjection is finite by this contribution, so the existing connected-kernel criterion completes that comparison. This is on-the-spot glue (provenance (c)). |
| L771–773 | unverified | The embedding-specific identification is outside this proof; these lines only invoke the total Euler-factor identity. |
| L11053–11057 | OK | The bibliography identifies Shimura's paper, Theorem 1 and the DOI. |
