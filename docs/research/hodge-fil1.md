# The Hodge number in the degree-one Scholze row

**Scoped stop.** On `dcc3d7723`, no proved input or current headline field supplies the symmetry that fixes the two Hodge–Tate multiplicities of the Tate module of an arbitrary abelian variety over a finite extension of `ℚ_p`. The missing statement is `HodgeFil1.TatePolarizationSymmetry`: for the same `A` and `F` as the Scholze row, `V_p(A)` admits a nondegenerate bilinear form with cyclotomic multiplier. The Hodge-number clause stays in the row, including for surfaces. No new leaf or fold is proposed on this base.

**Known source issue (VERIFIED from the manuscript).** The Hodge numbers at L10996 are stated without a citation. This is an omitted justification, not a known false claim. The scope of the Scholze comparison used at L10954–10965 is different from the Hodge-number calculation. The manuscript cites the 2016 corrigendum explicitly; the existing locator audit (`docs/research/locators.md`, R10) records that it repairs the period-site definitions and preserves the comparison. No new mathematical error was found in the checked steps. The Scholze locators are UNVERIFIED in this task; no source reading is requested.

## Audit

The full [candidate table](../../scratch/hodge-fil1/audit.md) records the declaration, source location, status on this base and whether it consumes clause 3. The distinctions that determine the result are:

| Route | Result |
|---|---|
| (a) Polarization symmetry | T10 identifies cohomology with the dual of the Tate module; T5 gives rank `2g`. The Tate-module pairing assembler still requires a symmetric isogeny to a dual with a perfect compatible Weil pairing. The old supplier uses Picard representability and Picard-zero properness, which the live headline no longer assumes. |
| (b) Hodge–Tate multiplicities | `DeRhamScholze.TT.deRhamHodgeTate01_proof` gives weights in the appropriate range with two unknown multiplicities. The existing `hodgeTate01_dims` fixes the multiplicities only after being given the dimension of `Fil¹`. No independent tangent-space Hodge–Tate comparison on these objects was found. |
| (c) Other inputs | The old cyclotomic determinant proof also uses the pairing. The live determinant argument concerns a specific global character. The comparison row does not supply an algebraic de Rham space or the filtered comparison to one, so a theorem about invariant differential forms alone would not settle this Lean goal. |

`frozenTarget` on this base uses `OpenResearchLeaves65`, `OpenTextbookLeaves18` and `OpenAddedLeaves28` (`ZInQKernel/OneProof/Main.lean:203–211`); `TailZ87.lean:73,75` gives the exact Scholze and T10 fields. The unchanged local de Rham Tate-module field adds no constraint on the relative sizes of the filtration steps. The generic dimension count gives `a + b = 2g`; one needs a separate constraint such as `a = b`. For abstract de Rham representations this constraint does not follow from filtration range and total rank: a sum of trivial representations has only a degree-zero jump.

The missing Prop has no de Rham or Hodge input. It asks only for a pairing on the rational module, with formula `B(σx, σy) = χₚ(σ) B(x,y)`; the form supplies `V_p(A) ≃ V_p(A)^∨(1)`. No positivity, alternation, integral perfection or representability of an entire Picard functor occurs in this statement. Providing it is a geometric task. The existing Picard construction would need both of its missing inputs. A possible route avoiding full Picard representability is to use the native finite stabilizer quotient and descended normalized family from the Poincaré proof. That code supplies the quotient isogeny and separation of geometric points by their Picard classes. It still needs a construction of bilinear pairings on the quotient's `p^n`-torsion against `A[p^n]`, with nondegeneracy, Galois equivariance and compatibility in `n`, before taking the inverse limit and rationalizing. The older proofs of those properties are tied to the represented Picard object. This is a prospective reuse route (SPECULATIVE); reducing the two Picard inputs by that route is outside this scoped stop.

## Conditional Lean statements

All declarations are in `ZInQKernel/Contrib/OneProof/HodgeFil1.lean`. `ScholzeH1AbVarDR` retains clauses 1 and 2 with the original quantifiers. `TatePolarizationSymmetry` is only a definition documenting the blocker; it is neither assumed by the headline nor registered as a provider.

| Theorem in namespace `HodgeFil1` | Statement |
|---|---|
| `finrank_filD_dual_of_pairing` | For a representation `V` of rank `2g` with a nondegenerate cyclotomic pairing, if `V^∨` is de Rham with range `[0,1]`, its `Fil¹` has `ℚ_p`-rank `[F:ℚ_p] * g`. |
| `finrank_fil1_of_dR_of_pairing` | The same equality for the row's étale `H¹` at each `A/F` of dimension `g`, from clauses 1 and 2, T10 and `TatePolarizationSymmetry`. |
| `fil1_of_dR` | `ScholzeH1AbVarDR → T10_TateDuality → TatePolarizationSymmetry → ScholzeH1AbVar`. |
| `fil1_surf_of_dR` | The same inputs give `ScholzeH1AbSurf`, by applying the pointwise proof at dimension 2. |

The pointwise proof moves the two input clauses along `milneE`. The generic proof obtains the two unknown multiplicities from `deRhamHodgeTate01_proof`, applies `eq_of_pairing` to make them equal, and uses the total rank to identify each with `g`. The two bounds of `finrank_fil1_bounds` then give equality: `Fil² = 0` gives the upper bound by the degree-one Hodge–Tate space, while the bound from degree zero gives the lower bound after subtracting `[F:ℚ_p] * g` from the rank of `D_dR`. Finally `map_filD` transfers the answer back to étale cohomology. This use of the pairing is on-the-spot glue (provenance (c)); it adds no row.

## Count and proposed row

No row changes now. The conditional [autofold preview](../../scratch/hodge-fil1/autofold-dryrun.txt) gives strict **5 LEAF / 26 GLUE → 5 / 26** on 31 H rows and strictest **5 / 26 → 5 / 26**. The spec has an intentionally absent polarization provider; its successful `--dry-run` verifies the shape and count only. Do not run it as a fold.

Proposed kinds entry after the blocker is proved: `added | scholzeH1AbVarDR | consequence | pending review: GLUE; removes the Fil¹ dimension clause (L10996 for surfaces) | GLUE | GLUE`. Source: the Scholze comparison cited at L10954–10965, with the cited corrigendum. Once the pairing is proved, the all-dimension Lean calculation will remove reliance on the uncited assertion in the row, while leaving the manuscript text and its bibliography as they are.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict |
|---|---|
| L10939–10951 | **OK** — the statement concerns a surface and two copies of a restricted representation. The conditional proof addresses its degree-one Hodge number, and does not need the splitting of `r`. |
| L10954–10965 | **unverified** — the application and citations were checked in the manuscript; the published comparison and its algebraic–analytic bridges were not reread. De Rhamness and the two filtration bounds are taken as clauses 1 and 2. |
| L10967–10972 | **OK** — the direction and dual in the manuscript match the existing equivariant T10 input and the proved rational transport. |
| L10973–10994 | **unverified** — closure, coefficient extension and descent for `r` are beyond the calculation at `F`; those literature steps were not rechecked. |
| L10996 | **OK** — the Hodge numbers `2,2` are the intended surface calculation, but the text leaves it uncited. The conditional Lean argument proves the corresponding statement for `D_dR` once Tate-module symmetry is supplied; the open source issue survives on the current base. |
| L10997 | **gap filled** — the implication from the filtration to the Hodge–Tate multiplicities uses the proved comparison in degrees 0 and 1 and linear duality, with the manuscript's Tate-twist sign. The multiplicity value itself remains conditional as above. |
| L10998–11000 | **unverified** — the descent and coefficient-embedding conclusion for the two summands is not used in the new proof. |
