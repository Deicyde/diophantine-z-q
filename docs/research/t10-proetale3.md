# T10 pro-étale comparison, third continuation

**VERIFIED — the degree-one limit comparison is proved.** The original residue
reductions give an additive isomorphism from the row’s integral pro-étale
H¹ to the compatible families of finite **pro-étale** H¹ classes.
Every such family has a unique integral lift. The theorem takes no auxiliary
epimorphism, Mittag-Leffler or finite generation hypothesis. This is the first
comparison, before passing from the small pro-étale site to the big étale site.

**VERIFIED — the finite lift sheaves are representable.** The lift sheaf of
each finite pro-étale degree-one class on the geometric scheme is represented
by a finite étale surjection. Its pullback to itself is split, and the class is
zero exactly when the cover has a section. The identification with
`T10Milne86.FiniteH1` remains open. The T10 row stays GLUE; delta **0**
(strict H count: **4 LEAF, 18 GLUE**).

**Known issue, UNVERIFIED against the cited sources.**
`diophantine_zq.tex:10967–10972` cites the 2008 notes’ Part I, Theorem 12.1(a)
alone for Galois equivariance. The earlier local audit points separately to
Remark 12.5. The 1986 print locator and the printed scope of naturality still
need verification. There is no established mathematical error. The equivariant
square is for the *same* Milne family as the printed comparison; independently
chosen isomorphisms do not give that square.

## What is checked

The following files are in `ZInQKernel/Contrib/OneProof/T10Proetale/`.
Names below are in `ZInQ.Manuscript.T10Proetale`.

| File | Declarations and what they prove |
|---|---|
| `AffineWeaklyEtaleLimits.lean` | `flat_of_filteredCocones` lifts a finite equational criterion for flatness to one filtered stage, with the base ring allowed to move. `flat_of_affineLimits` transfers this to morphisms between affine limits. `weaklyEtale_of_affineLimit` applies flatness also to the diagonal. `surjective_of_affineLimit` uses nonempty inverse limits of affine fibres. `affineDiagramLimit` chooses an affine limit of an affine diagram. `affineSequenceLimitCover` gives an affine weakly étale surjection to the first term of a tower of such covers. |
| `AffineLocalLifts.lean` | `proUnderlying` is the scheme forgetful functor. `proSingletonCover` checks the singleton sieve of a weakly étale quasi-compact surjection. `affineCover_lift_of_compactSpace` refines a sieve on which a section lifts to a single affine weakly étale surjection: use a finite affine refinement and glue on the disjoint union. `affineCover_lift` is the affine case. |
| `CountableLocalLifts.lean` | `countable_affineCover_lifts` chooses successive affine lifts and pulls all of them back to their common inverse limit. `proProduct_epi` proves that the countable product of epimorphisms of abelian sheaves on the actual small pro-étale site is epi. |
| `IntegralTower.lean` | `residueQuotientProduct_epi` specializes that result to the actual injective-presentation quotients. `proFiniteH1Limit` is the additive group of compatible finite classes. `proReduction_existsUnique` removes the previous comparison’s last assumption using the quotient-product epi and the existing surjectivity of the degree-zero difference operator. `proReductionEquiv` is the additive identification, and `proReductionEquiv_apply` proves that it is given by the original reductions. |
| `MapDescentDatum.lean` | `mapDescentDatum` extends an overlap datum through a pullback-preserving functor using the image of its universal overlap map. `mapDescentDatum_transport_image` verifies agreement on the original site’s points. |
| `FiniteTorsorDescent.lean` | `splitProjection_finite` and `splitProjection_etale` check the split model. `liftSheafRepresentableOnSlice` packages the pointwise splitting as a representation, `liftSheaf_affineCover` obtains a single affine cover with a lift, and `liftSheafDescentDatum` constructs the canonical overlap datum. `liftSheaf_finiteEtaleDescent` descends this datum in schemes. `liftSheaf_finiteEtaleRepresentable` verifies representation on the slice by subcanonicity and the sheaf condition. `liftSheaf_globalRepresentable` gives the whole-site result. `proFiniteH1_representable` identifies the actual classes furnished by quotient sections and detects the zero class. `liftSheaf_selfPullbackSplits` splits the cover on the slice over itself. |

The site-level product argument does not rely on the finite H¹ groups
being finite or on replacing the row’s sheaf by an abstract group tower.
There are no new assumptions at the row. The private `LiftStep` is the data of
one local affine lift used to define the recursion; it is constructed from
`affineCover_lift` and contains no assertion about products or cohomology.

The representability theorem uses the existing hypotheses `CompactSpace X`
and `IsSeparated g` for the map to an affine base. In the row the geometric
abelian variety is proper over the spectrum of the algebraic closure.
`RepresentableBy` in the splitting theorem refers to the actual lift
presheaf and is provided by the preceding representability result.

## Remaining comparison

- **VERIFIED:** the base had split models on auxiliary pro-étale covers. The
  descent proof produces a finite étale cover *of the original scheme*
  representing the lift sheaf. It checks invariance for that sheaf’s canonical
  overlap datum. The vendored inputs are
  `Jacobian/AlgebraicGeometry/Descent/{Affine,AffineLocal,Gluing}.lean`,
  `Jacobian/AlgebraicGeometry/Morphisms/FlatDescent.lean` and
  `Jacobian/CategoryTheory/Comma/Over/DescentRepresentable.lean` under
  `ZInQKernel/Contrib/CloudW07JacobiansCurves/`.
- **Smallest remaining comparison:** identify the finite derived degree-one
  groups by assigning the same ℤ/ℓⁿ-torsor to the pro-étale lift sheaf and the
  big étale Ext class. For a Čech proof, the missing interface is to send a
  finite étale trivializing cover and its coefficient-valued one-cocycle to
  the class in `T10Milne86.FiniteH1`, identify equality of classes with changes
  of trivialization on common refinements, and prove that every big étale class
  is obtained. The sheafified constant coefficient on the big site and the
  continuous finite coefficient on the small site must give the same sections
  on the covers and overlaps. The comparison must preserve addition and
  residue maps and identify the scalar actions.
- **SPECULATIVE, implementation size:** the remaining finite comparison is
  library work on the two Ext and torsor interfaces. A common Čech
  construction needs the degree-one Ext–Čech comparison, its compatibility
  with refinements and coefficients, and identifications of the two free
  sections sources. Mathlib’s `Sites/NonabelianCohomology/H1.lean` defines
  the cocycle quotient for a chosen family; it does not identify these two
  derived groups with it.
- The scheme square in `Transport.lean` is unchanged. After the finite
  comparison, check transport along `1 × Spec(σ⁻¹)` against pullback along
  `1 × Spec(σ)` and check the semilinear square for the same Milne family.
  The draft `Milne86Thm15_1a` supplies naturality over the original field.
  The semilinear square was not attempted. There is no new print, provider,
  or discharge.

## Manuscript check

| `diophantine_zq.tex` lines | Verdict | Check |
|---|---|---|
| 10954–10965 | unverified | The manuscript passes from finite coefficients through the algebraic/analytic comparison to the integral limit, then inverts ℓ. The new result verifies the extra integral-to-finite-pro-étale dictionary required by the Lean row. It does not verify the algebraic/analytic comparison. |
| 10967–10972 | unverified | The finite comparison and the semilinear square for the same family must still be checked as needed below. The cited source and the separate equivariance locator remain unaudited against the originals. |
| 10973–10978 | OK | The manuscript uses the equivariant comparison downstream to read the Tate-module Galois action on geometric H¹; the Lean consumer `T10_linIso_of_tateDuality` remains conditional on the unchanged row. |
| 11024–11026 | OK | The bibliography identifies the cited notes. This verifies what the manuscript cites, not that the stated locator supplies equivariance. |
