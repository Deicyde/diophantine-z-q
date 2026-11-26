# Abelian variety quotients over ℚ

**VERIFIED (Lean).** `abVarQuotientBySubvarietyExists` proves that every abelian
subvariety `C ↪ J` over ℚ has a genuine quotient `J → J/C`. The theorem
certifies a surjection, the scheme-theoretic kernel square, and the universal
property among abelian variety homomorphisms. The proof uses a Poincaré
complement. Both directions of the comparison with `PrintQuotient` are now
unconditional. For a surjective homomorphism, both directions of the comparison
between `KerConnected` and the connectedness of its scheme kernel are proved.

## Construction

1. The existing `StabilizerAbVarQuotientExists_proof` takes a very ample line
   bundle and a seesaw input. It provides an abelian variety quotient for the
   resulting finite stabilizer, with a finite flat quotient map, its
   translation kernel pair, and dimension equality. The new theorem accepts
   any group scheme with a closed inclusion in an abelian variety and finite
   structure map over ℚ. Cartier smoothness supplies flatness. Its proof
   uses the same finite locally free equivalence relation theorem, projective
   affine-open coverage, and group and geometry descent. It certifies the
   kernel square with the subgroup itself and unique factorization of
   homomorphisms killing it.
2. Poincaré reducibility gives a homomorphism `g : B → J` for which addition
   `s : C × B → J` is an isogeny. The supplied Lean theorem need not assert
   that `g` is a closed immersion. The finite subgroup of `B` used here is
   `B ×_J C`: its first projection is a closed immersion, and negating the
   `C` coordinate identifies it with the scheme kernel of `s`. The map
   `C × B → B/(B ×_J C)` kills that kernel and descends along the finite
   faithfully flat `s`. On any test scheme mapping into the kernel of the
   descended map, pull back the cover `s`; the complement coordinate then
   lifts to `B ×_J C`. Addition therefore factors through `C` on the cover.
   The lift descends by effective epimorphy and is unique by monicity.
   Restriction to the complement proves surjectivity and the quotient's
   universal property.
3. Apply this construction to the existing scheme-theoretic sum of the
   saturated annihilator images. The commuting isomorphism with any map that
   satisfies `PrintQuotient` follows from the existing uniqueness comparison.
4. For a surjection `ν`, quotient by `(ker ν)⁰` and write the residual map as
   `ψ`. The map from `ker ν` to `ker ψ` is a proper surjection, and the
   inverse image of the residual unit is the open identity component.
   Thus the residual unit has open range. Its inclusion is an open immersion
   because the residual kernel is reduced in characteristic zero. The
   diagonal of `ψ` is a base change of that unit along the difference map on
   the kernel pair; hence `ψ` is formally unramified. Local finite type and
   properness then make `ψ` finite. The printed test makes the resulting
   isogeny an isomorphism, identifying `ker ν` with the connected subvariety.

These are proofs of glue (on-the-spot, provenance (c)). There is no new
literature row or change to the printed statements.

## Lean statements

All names are in `ShimuraSteps.Quotient`. Private lemmas are included for the
axiom audit.

| Declaration | Statement |
|---|---|
| `target_pair_mono` | The translation action and second projection on `G × B` are jointly monic for a monic subgroup inclusion. |
| `target_properties` | Translation has finite, flat and locally finitely presented underlying morphism when `G` is finite flat over ℚ. |
| `finiteSchemeQuotient` | The translation relation has a finite flat surjection in the slice with that relation as its kernel pair. |
| `exists_operations` | Multiplication and inversion descend along this surjection. |
| `separated_quotient` | The quotient scheme is separated over ℚ. |
| `translation_kernel` | A homomorphism with the translation kernel pair has the indicated subgroup as its scheme kernel. |
| `finiteSubgroupQuotient_exists` | For any finite closed subgroup scheme `j : G ↪ B` there exist `Q` and `q : B → Q` satisfying `IsFiniteSubgroupQuotient j q`: an isogeny with kernel `G` and unique factorization for homomorphisms killing `G`. |
| `intersection_isPullback` | The addition kernel, with its first coordinate negated, is the pullback of `i : C → J` and `g : B → J`. |
| `factor_of_effectiveEpi` | A factorization through a monomorphism descends along an effective epimorphism. |
| `descended_kernel` | If `q` descends the complement's finite quotient and kills `i`, then `i` is its scheme kernel. |
| `abVarQuotientBySubvarietyExists` | The existing `AbVarQuotientBySubvarietyExists` Prop holds. |
| `exists_genuineQuotient_printQuotient_iff_iso` | There exist a genuine image sum and its genuine quotient map `q`; for every `ν : J → A`, `PrintQuotient ξ f ν` iff there is an isomorphism of abelian varieties `a : Q → A` with `a ∘ q = ν`. |
| `componentModel_kernel` | The kernel scheme used by the identity component construction represents the kernel in the slice. |
| `openImmersion_of_closed_and_open_range` | A closed immersion into a reduced scheme with open point range is an open immersion. |
| `residual_unit_open` | Factoring through the quotient by the identity component gives a residual kernel with an open unit section. |
| `finite_of_open_kernel_unit` | A homomorphism with an open unit section of its kernel is finite. |
| `schemeKernelConnected_of_kerConnected` | Surjectivity of `ν` and `KerConnected ν` imply `SchemeKernelConnected ν`. |
| `kerConnected_iff_schemeKernelConnected` | For surjective `ν`, `KerConnected ν ↔ SchemeKernelConnected ν`. |

## Known issues

- VERIFIED (prior source audit): the sentence immediately before clause (iv)
  of Shimura 1973, p. 526, omits the conjugation on the form on the
  right-hand side; see the [recorded audit](r16-thm1b.md#known-issues-exact-locations).
  It does not affect the quotient or connected-kernel clauses checked here.
  The article was not reread for this task. No new manuscript or source error
  was found.
- VERIFIED (Lean statement): the printed surjectivity clause is needed for
  the reverse kernel comparison. Without it the factorization test is
  vacuous for a nonsurjective map, as discussed in
  [the preceding report](shimura-quotient.md#known-issues).

## Manuscript check

Line numbers are from `diophantine_zq.tex`. The check of the cited article
uses the prior source audit.

| TeX lines | Verdict | Check |
|---|---|---|
| L770–771, Shimura's quotient construction | gap filled | Lean now constructs the actual quotient by the sum of the saturated annihilator images and proves the two geometric clause comparisons, including the printed surjectivity condition for the reverse kernel direction. The manuscript invokes the construction by citation. |
| L771–773, Euler-factor identity and constituent | unverified | Identifying a specific Tate constituent from the Euler-factor identity is outside the quotient and kernel comparisons. |
| L11053–11057 | OK | The title, journal, year, theorem citation and DOI match the recorded audit. |

## Verification

VERIFIED (Lean 4.35.0 / Mathlib v4.35.0). Each of the four
`ZInQKernel/Contrib/OneProof/AbVarQuotient*.lean` modules was checked with
`lake env lean`. The four independent audit files under
`scratch/abvar-quotient/` run `#print axioms` on the 18 new theorems,
including the private helpers. Every theorem uses only `propext`,
`Classical.choice` and `Quot.sound`. No existing Lean files were edited.
