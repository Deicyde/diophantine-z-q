# Shimura's quotient and rational intertwining

**Scoped result.** The rational equation is proved equivalent to `HeckeCompat`,
including independence of the denominator. The scheme-theoretic sum of the
annihilator images exists as an abelian subvariety. The printed universal
property identifies any supplied genuine quotient by that sum, and a connected
scheme kernel implies the printed factorization test. The general quotient
construction and the reverse implication for arbitrary surjections are scoped
stops.

## Clause comparisons

| Clause | Lean status |
|---|---|
| `HeckeCompat ν t x` | Proved equivalent to `ν ∘ t = x ∘ ν` in `ℚ ⊗[ℤ] Hom(J,A)`, with composition extended from integral homomorphisms. The same equivalence holds for every positive denominator for `x`. |
| `PrintQuotient ξ f ν` | The genuine sum `C → J` of the specified scheme-theoretic images is constructed. Given a genuine quotient `q : J → Q` by that sum, proved both ways that the clause holds exactly when there is an abelian variety isomorphism `a : Q → A` with `a ∘ q = ν`. Existence of `q` is still open. |
| `KerConnected ν` | Proved that the scheme-theoretic kernel being connected implies this test, and that a genuine quotient by an abelian subvariety has connected scheme kernel. The converse for a surjective `ν` remains open. |

The image sum is characterized as the least closed subgroup scheme through
which every endomorphism in the family factors. The proof takes a maximal
irreducible closed range among abelian subvarieties contained in every common
closed subgroup. The last term of a longest chain is maximal by finite Krull
dimension. The image of addition with any further summand is another candidate
and contains the chosen range, so maximality forces equality. Lifts from
reduced schemes through closed immersions upgrade the range containments to
factorizations of schemes, including when the testing subgroup is nonreduced.

For the kernel implication, any factorization tested by `KerConnected` induces
a surjection of scheme-theoretic kernels by base change. The isogeny's kernel
is therefore connected and finite. Cartier smoothness makes it reduced, so
its rational identity section is an isomorphism. The isogeny is then a
monomorphism and, by faithful flatness, an effective epimorphism; hence it is
an isomorphism.

## Lean statements

All names below are in `ShimuraSteps.Quotient`. Here `ι` denotes
`hom0Inclusion` and `comp0 u v` denotes `v ∘ u`.

| Theorem | Statement |
|---|---|
| `comp0_tmul` | `comp0 (r ⊗ f) (s ⊗ g) = (r * s) ⊗ (g ∘ f)`. |
| `hom0Inclusion_injective` | `ι : Hom(J,A) → Hom⁰(J,A)` is injective, by `hom_nsmul_eq_zero`. |
| `hom0_exists_positive_denominator` | Every `v : Hom⁰(J,A)` has `m > 0` and integral `u` with `m • v = ι u`. |
| `hom0_nsmul_cancel` | `m • v = m • w` in `Hom⁰(J,A)` with `m > 0` implies `v = w`. |
| `cleared_hecke_iff` | Given `m > 0` and `m • x = ι e`, the equation `m • (ν ∘ t) = e ∘ ν` is equivalent to `ι (ν ∘ t) = comp0 (ι ν) x`. |
| `heckeCompat_iff_rational` | `HeckeCompat ν t x ↔ ι (ν ∘ t) = comp0 (ι ν) x`. |
| `unit_closed` | The unit section of a separated group scheme over ℚ is a closed immersion. |
| `kernelInclusion_closed` | The inclusion of the scheme-theoretic kernel of an abelian variety homomorphism over ℚ is a closed immersion. |
| `kills_iff_kills_imageSum` | If `i : C → J` represents the sum of the images of `I`, then `Kills I v ↔ v ∘ i = 0`. |
| `printQuotient_iff_iso` | For the sum of the saturated annihilator images and a genuine quotient `q : J → Q`, `PrintQuotient ξ f ν ↔ ∃ a : Hom(Q,A), IsIso a ∧ a ∘ q = ν`. |
| `schemeKernelConnected_of_isAbVarQuotient` | A genuine quotient by an abelian subvariety has connected scheme-theoretic kernel. |
| `unit_isIso_of_finite_connected` | The unit section of the connected scheme-theoretic kernel of a finite homomorphism is an isomorphism. |
| `kerConnected_of_schemeKernelConnected` | If `J ×_A Spec ℚ` along the unit is connected, then `KerConnected ν`. |
| `factors_of_range_subset` | A morphism from a reduced scheme factors through any closed subscheme containing its point range. |
| `range_le_of_factor` | Factorization through a morphism implies containment in its point range. |
| `range_eq_of_surj_factor` | Precomposing with a surjection preserves the point range. |
| `imageSum_exists` | For every set `I ⊆ End(J)` there is an abelian subvariety representing its scheme-theoretic image sum. |
| `exists_printQuotient_of_abVarQuotientBySubvarietyExists` | The named quotient existence Prop implies existence of a genuine quotient by the printed image sum satisfying both `PrintQuotient` and `KerConnected`. |

## Known issues

- VERIFIED (existing AI page read, recorded in
  [the earlier source audit](r16-thm1b.md#known-issues-exact-locations)): on p. 526 the sentence
  before clause (iv) has the original form where the conjugate eigenform should
  occur on the right. This does not affect the quotient or intertwining clauses.
  The print was not reread for this task. No new error in the manuscript was found.
- VERIFIED (Lean): the comment in
  `ZInQKernel/Contrib/OneProof/R16Thm1.lean` calling the integral form weaker is
  misleading. For this Hom space the forms are equivalent.
- `KerConnected ν` is used together with surjectivity in the printed clause.
  Without surjectivity the factorization test holds vacuously whenever `ν` is
  not surjective. That test alone cannot characterize a connected kernel:
  for example, take `E → E × E` given by `P ↦ ([2]P, 0)` on
  `E : y² = x³ − x` over ℚ. Its kernel is finite étale and has distinct rational
  points `0` and `(0,0)`. This example is a mathematical scope check (VERIFIED by direct calculation), with no new Lean declaration.

## Quotient sizing

**VERIFIED (source).** `ZInQKernel/Contrib/AVB1/Poincare.lean` and
`ZInQKernel/Contrib/CloudR2Poincare/FinalUnconditional.lean` supply a complement
`g : D → J` such that addition `s : C × D → J` is finite and surjective.
The complement statement in the tree does not assert that `g` is a closed
immersion. `ZInQKernel/Contrib/OneProof/MilneQuasiInverse/Flatness.lean` and
`ZInQKernel/Contrib/OneProof/MilneQuasiInverse/Descent.lean` give flatness
of isogenies and effective epimorphisms for fpqc maps in the slice.
`ZInQKernel/Contrib/CloudR2Poincare/L3/KernelIdentity.lean` constructs the actual identity component
of a kernel in characteristic zero as an abelian variety (`covAbVar`, `covHom`).

**VERIFIED (source).** The generic scheme quotient provider
`Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation` gives a finite
flat scheme quotient, its kernel-pair square and its coequalizer. It requires
an actual equivalence relation with an affine open containing each orbit.
The existing abelian-variety packaging in `ZInQKernel/Contrib/CloudR2Poincare/L4/QuotientExists.lean` and
`ZInQKernel/Contrib/CloudR2Poincare/L4/B3.lean` uses the finite stabilizer of a line bundle. In particular
`StabilizerAbVarQuotientExists_proof` takes a very ample line bundle and the
seesaw input in its interface; it does not accept an arbitrary finite subgroup.

**SPECULATIVE implementation size; mathematical plan.** This is several pieces
of new scheme glue, comparable to several modules of the existing quotient implementation (the
five L4 modules for existence, scheme conversion, descent, geometry and
packaging total 595 lines, before the new complement descent). The general
construction is a scoped stop.

1. Form the finite closed subgroup `H = D ×_J C → D` as a scheme pullback.
   It is isomorphic to the scheme-theoretic kernel of `s` by
   `(d,c) ↦ (−c,d)`, even without monicity of `g`. Generalize the translation
   relation and the group and properness descent in L4 from a stabilizer to
   this arbitrary finite subgroup; use the generic scheme provider to obtain
   the abelian variety `Q = D/H`.
2. The homomorphism `C × D → D/H` kills the kernel of `s`.
   Descend it along the finite faithfully flat map `s` to `q : J → Q`.
   Descend the kernel square too: its pullback along `s` is `C × H`,
   which is also the pullback of the closed immersion `C → J`.
   Establish surjectivity and the universal property: a map killing `C`
   restricts to a map on `D` killing `H`, factors through `D/H`, and
   agrees after precomposition by the epimorphism `s`.
3. For the missing reverse direction of the kernel criterion, start with
   surjective `ν`. Use `covHom ν.hom` for `(ker ν)⁰ → J` and factor
   `ν` through the resulting quotient. The induced map to `A` is an
   isogeny: its kernel over an algebraic closure is the finite group of
   components of `ker ν`. The additional Lean obligation is that this
   induced map is finite (e.g. prove the kernel comparison and use the
   finite-kernel criterion, or prove the corresponding dimension equality and
   use `ZInQKernel/Contrib/OneProof/SameDimFinite.lean`). Then `KerConnected` forces it to be an
   isomorphism. This step and the general construction are unproved here.

The faithful stopping statement is `AbVarQuotientBySubvarietyExists`: for
every closed immersion of abelian varieties `i : C ↪ J` over ℚ, there exist
an abelian variety `Q` and a surjective homomorphism `q : J → Q` such that
the square with `C → Spec ℚ` and the unit of `Q` is a pullback, and every
homomorphism out of `J` killing `i` factors uniquely through `q`.
The abelian-variety structure of `C` supplies connectedness. This Prop is
an on-the-spot (c) proof target. It is a definition only, with no new axiom or
literature row.

## Verification

VERIFIED with Lean 4.35.0 and Mathlib v4.35.0: all three new
`ZInQKernel/Contrib/OneProof/ShimuraQuotient*.lean` modules compile using
`lake env lean`. The three standalone audit files in
`scratch/shimura-quotient/` print the axioms of all 18 new theorems and the
named existence Prop. Every result uses only `propext`, `Classical.choice`
and `Quot.sound`.

## Manuscript check

Line numbers refer to `diophantine_zq.tex`. The only manuscript input to this
work is the reference to Shimura's construction; the recorded source for its
quotient clauses is the existing AI page read of pp. 525–527.

| TeX lines | Verdict | Check |
|---|---|---|
| L770–771, quotient construction | OK | The recorded read of Shimura 1973, Theorem 1, identifies the constructed variety as the quotient by the sum of the images of the integral elements of the rational annihilator. |
| L770–771, intertwining in that construction | gap filled | The Lean integral test and rational intertwining on the genuine Hom tensor product have now been proved equivalent. |
| L771–773, application of the Euler identity to a Tate constituent | unverified | Out of scope here. The prior read distinguishes the total identity from the assertion about a specific constituent. |
| L11053–11057 | OK | The bibliography gives Shimura's article, Theorem 1 and DOI, matching the citation at L771 and the recorded read. |
