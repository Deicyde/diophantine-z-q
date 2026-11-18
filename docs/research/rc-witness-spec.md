# Appendix F: specialization of the fixed witness

**Proved at the fixed witness.** `actualWitness` in `Specialize.lean` constructs the
stage evaluations and proves both `WitnessSpecialization` and
`WitnessValuation` (Appendix F (O.2)). Its inputs are the global exact witness
from the twist comparison, its division tower, the existing actual stage
sequence, the squared Tate action, the selected datum and prepared condition,
and the fixed integral row and its cocycle value. It assumes no compatibility
of geometric or ring class reductions. The stage interface and the valuation
statement are unchanged.

The finite identity is
`ev i Dw dat (L • genusPoint dat) = finiteRow b (Mθ i) (proj (Mθ i) (c_Q(g_i * g_i)))`
in `ZMod (2 ^ Mθ i)`. The place is the witness of `IsFrobAt` for
`selectedFrobenius q i`; the same place is used for reduction of the scaled
genus point, the division point and the torsion. The finite map uses arithmetic
Frobenius, so the difference is `F²R - R` with its original sign and no
unit factor. The integer representative is taken only after this equality.

The rational point and square root in `ExactWitness` are the output of
`RC/Stages/ExactGenus.lean` (`exact_twist_of_genusPoint`), with an embedding
of the witness field into the algebraic closure. That comparison precedes all
stage choices. The calculation uses the manuscript's Kummer map and existing
stage construction. The common localization and finite residue enclosure,
coordinate naturality, and use of principal ideal reciprocity to deduce
quadratic ring class residue descent are on-the-spot (c) details.

## Declarations and interfaces

Paths in the tables are relative to
`ZInQKernel/Contrib/OneProof/RC/WitnessSpec/`. Here `p` is the stage prime,
`v` its absolute place, `H` the conductor-one ring class field, and `n = 2^M`.

| File and declaration | Statement and use |
| --- | --- |
| `Residue.lean`: `ofIsFrobAt`, `frob_on_integers`, `charP` | Retain the prime witnessing `IsFrobAt g p`; reduction of `g(x)` for an algebraic integer is `red(x)^p); the quotient has characteristic `p`. These fix the residue model and Frobenius in the stage map. |
| `Residue.lean`: `isAlgClosed_residue`, `residueAlgebra`, `isAlgebraic_residue`, `exists_commonFiniteResidue` | The quotient is algebraically closed and algebraic over its canonical `ZMod p` subfield; every finite set of its elements is contained in one finite subfield. This allows a common finite field for the coordinates of the witness, division point and finite torsion. |
| `Residue.lean`: `split_root_residue` | A root fixed by `g`, with square `D` prime to `p`, reduces to a nonzero root fixed by the `p`-power map. Supplies the split scalar. |
| `Residue.lean`: `integersMap`, `restrictPrime`, `restrictPrime_under`, `residueMap`, `residueMap_mk` | For `e : L →ₐ[ℚ] Qbar`, embed its integers, contract the selected prime (still over `(p)`), and map its residue quotient to the common field by reducing the image of each integer. These are the same-place maps. |
| `Residue.lean`: `restrict_frobenius`, `residueMap_pow_sq` | If `e ∘ σ = g ∘ e`, the induced automorphism is arithmetic Frobenius at the contraction. If the contracted quotient has order `p²`, every image coordinate satisfies `x^(p²) = x`. |
| `Valuation.lean`: `restrictHeightOne`, `localRing`, `localRingIntAlgebra`, `localRingLocalization` | The contracted prime is nonzero in a finite number field; localize the absolute integers at the selected prime with its canonical algebra and localization structure. |
| `Valuation.lean`: `localRingMap`, `coe_localRingMap`, `valuationRing` | The local ring at a contraction maps to the absolute localization by the given field embedding. The absolute localization is a valuation subring: any element or its inverse lies in the local ring of a finite field of definition. |
| `LocalFrobenius.lean`: `integerFrob_at`, `integerFrob_compl`, `localFrob`, `coe_localFrob` | The restriction of `g` to the integers is arithmetic Frobenius, preserves the prime complement, and extends to the local ring with underlying field action `g`. |
| `LocalFrobenius.lean`: `localResidueEquiv`, `localFrob_residue`, `localValuationEquiv`, `valuation_frob_le_one_iff`, `valuation_frob_residue` | The residue of the local ring is the absolute quotient and its induced action is the `p`-power. Transport through the canonical equivalence with the valuation subring: `v(gx) ≤ 1 ↔ v(x) ≤ 1`, and `red(gx) = red(x)^p` on integral elements. These supply point equivariance. |
| `Restriction.lean`: `rationalPrimeBelow_restrict`, `localRingMap_isLocal`, `finiteValuationEquiv`, `valuationRingMap`, `valuationRingMap_isLocal`, `coe_valuationRingMap` | The rational prime below the contraction is `p`; the map of localizations reflects units. Identify the finite localization with the valuation ring and embed it as a local map into the absolute valuation ring. The map on underlying elements is `e`. |
| `Restriction.lean`: `valuation_le_one_restrict`, `valuationResidueMap`, `valuationResidueMap_residue`, `finiteValuationResidueEquiv` | `v(e x) ≤ 1 ↔ v_L(x) ≤ 1`; the induced residue embedding sends `red_L(x)` to `red(e x)). The finite valuation residue field is the quotient by the contracted prime. Supplies reduction compatibility and the residue count. |
| `RingClass.lean`: `conductor_one_eq`, `conductorOne_inertiaDeg_of_inert`, `conductorOne_residue_card` | The conductor-one conductor is the unit ideal. A quadratic prime `(p)` has trivial Picard class and every ring class prime above it has relative residue degree one. If the base prime has residue degree two, the upstairs residue cardinality is `p²`. |
| `Inert.lean`: `inertPrime_of_legendre` | For a quadratic field, at `p ∤ disc K` with negative Legendre sign, the contracted prime is `(p)` and its residue degree is two. A degree-one residue field would contain a nonzero discriminant root, contradicting that sign. |
| `RingClassPlace.lean`: `restrictPrime_liesOver`, `ringClassResidue_card` | The contractions of one absolute prime to the two rings of integers lie over one another. The conductor-one quotient at this exact ring class place has `p²` elements under the inert sign. |
| `PointReduction.lean`: `reductionToModel`, `reductionToModel_some`, `reductionToModel_pole`, `fp_frob_apply` | Retype good reduction using a specified common prime-field equation. Integral affine coordinates reduce coordinatewise; a pole in `x) gives infinity. Arithmetic Frobenius on coordinates is the `p`-power. |
| `PointReduction.lean`: `reductionToModel_frobenius`, `reductionToModel_natural`, `quadraticResiduePoints` | Good reduction intertwines the decomposition element and Frobenius, commutes with a compatible valued field embedding, and sends points over a subfield of order `p²` into `FixedSq F`. Supplies both geometric stage reductions. |
| `CurveAtPlace.lean`: `integralEquation_baseChange`, `integralEquation_isIntegral`, `integralEquation`, `integralEquation_elliptic`, `integralEquation_residue` | An integral equation `C` has the expected base changes and valuation-ring equation. If `p ∤ Δ(C)`, its model is elliptic and its residue is obtained by base change of `C mod p`. |
| `CurveAtPlace.lean`: `valuationResidueEquiv`, `valuationResidue_charP`, `valuationResidue_algebra`, `valuationResidue_algClosed`, `curveReduction`, `curveReduction_frobenius` | Transport residue field, characteristic, prime-field algebra and algebraic closure to the valuation API. This gives the actual point reduction and `red(gP) = F(red(P))` at the chosen place. |
| `FiniteReduction.lean`: `finiteResidue_charP`, `finiteResidue_algebra`, `residueEmbedding`, `finiteReduction`, `finiteReduction_agrees` | The finite residue has characteristic `p` with its canonical prime-field algebra. The reduction at the contracted prime agrees with absolute reduction after the embedding over `ZMod p`. |
| `FiniteReduction.lean`: `ringClassReduction`, `ringClassReduction_agrees` | The actual conductor-one point map into `FixedSq F` agrees, after forgetting the fixed-point condition, with absolute reduction. Supplies the datum reduction input of the stage map. |
| `SplitRoot.lean`: `split_root_over_primeField` | Positive Legendre sign makes the reduction of the specified root the image of a nonzero root in `ZMod p`; use the sign determined by this place. |
| `Evaluation.lean`: `torsionMap`, `torsionMap_bijective`, `frob_sq_on_reduced_torsion` | Restrict reduction to `n`-torsion; injectivity and matching cardinalities give a bijection. Equivariance transports trivial square action to residue torsion. |
| `Evaluation.lean`: `stageMap`, `stageMap_apply_division` | Compose `r : E(H) →+ FixedSq F`, the finite Kummer map, inverse torsion specialization and the fixed row. If `nR=Q` and `r(P)=red(Q)`, its value on `P` is the row on `g²R - R`. Supplies the exact finite equality. |
| `Witness.lean`: `LocalStage`, `DatumReductions`, `stageKummer` | Package equivariant reduction, squared torsion action, torsion bijectivity and division surjectivity. Assemble the actual formula for supplied reductions; unused entries of the total `StageKummer` interface are zero. |
| `Witness.lean`: `witnessSpecialization_of_reductions`, `witnessValuation_of_reductions` | If the two reductions agree on `L • genusPoint dat` and `Q` at each stage, the finite identity is `WitnessSpecialization`. The fixed integral row with value `2^(a+1)` at `σ²` gives `WitnessValuation` via the existing `witnessValuation_withStages`. |

| `Torsion.lean`: `curveReduction_eq_zero_of_nsmul`, `curveReduction_torsion_bijective` | For `p ∤ n`, the kernel of absolute reduction contains no nonzero `n`-torsion. Descend the two coordinates to a finite field of definition and apply the finite-prime integrality proof. In odd characteristic the two geometric `2^M`-torsion groups have the same cardinality, so specialization is bijective. |
| `TwistMatch.lean`: `rationalGeomPoint`, `rationalGeomPoint_fixed`, `map_twistEmb_eq_geomTwist` | Embed a rational point in the geometric group; all absolute Galois elements fix it. For the specified embedding of the datum field, the embedded rational twist of a point equals its geometric twist with exactly the image of the datum's root. Supplies equality of the unreduced points. |
| `TwistAtPlace.lean`: `twistVC_at_place`, `twist_unit_valuation`, `twist_unit_residue`, `twistVC_reduction_equation` | The geometric change lifts to a change over the valuation ring, which reduces to the base change of a variable change over `ZMod p`. Scaling by its unit preserves valuations and reduces as multiplication by the residue unit to the same power. The changed integral equation reduces to the changed residue equation. |
| `ActualLocal.lean`: `torsionMap_equiv`, `reduced_elliptic`, `two_ne_zero_residue`, `localStage`, `localStage_red` | An additive equivalence gives a bijection of level torsion. The residue curve is elliptic and 2 is nonzero at an odd prime. Compose the exact geometric twist with absolute reduction and use Frobenius equivariance, torsion bijectivity and divisibility of the residue geometric group to realize `LocalStage`; its reduction is exactly that composite. |
| `Specialize.lean`: `witnessReductions`, `witnessReductions_at_witness`, `ExactWitness` | Supply the chosen datum's ring class reduction at each stage and extend by zero outside it. Package the global embedding, square root, rational point, and its equality with the multiplied genus point before reduction. |
| `Specialize.lean`: `goodAt_disc_unit`, `not_dvd_of_legendre_ne_zero`, `choose_local_at_witness` | Good reduction for the rational equation implies `p ∤ Δ(C)`; a nonzero Legendre sign implies `p ∤ D`. At the selected place the ring class evaluation of the multiple and the split reduction of the rational point coincide, so the `DatumReductions` match is proved. |
| `Specialize.lean`: `actualWitness` | For the exact global witness, actual stage sequence and fixed cocycle row, there exists one unchanged `StageKummer` with both `WitnessSpecialization` and `WitnessValuation` for the original `lamOf` and `withStages`. |

## Scope remaining

Nothing remains for the stated witness identity or its valuation. A
geometric formula on other entries of the total interface would require
`∀ i D dat` in the intended domain, a chosen same-place residue map for
`E(H_dat)` into the fixed group used at stage `i`, and the assertion that
`ev i D dat` is the row composed with Kummer applied to that map. Only the
selected `D = Dw` and `dat` are needed here. At other conductors or primes
where the residue is not quadratic, the fixed-group claim would require
different arithmetic hypotheses. No claim about those entries, theta forms,
or (O.7) follows from this witness construction.

## Known issues

- No mathematical error was found in the scoped manuscript lines. In tex
  8379–8388 Frobenius is over `F_p`; in tex 8440–8446 the symbol is reused
  for Frobenius over `F_{p²}`. Thus the latter is the square of the former.
- The geometric reduction here applies to the fixed witness on the chosen
  stages. Zero entries outside the witness in a total `StageKummer` do not
  furnish a theta or evaluation formula there.
- No new printed-form leaves were added. The good-reduction torsion input
  is from the vendored Tau Ceti proof. The source number reported there,
  Silverman AEC VII.3.1(b), was not independently checked against the book
  (UNVERIFIED). No known defect in that proof or in the conductor-one
  reciprocity input was identified.

## Manuscript check

- Tex 8293–8306 — OK: the global point used below is the exact multiplied witness obtained by the rational-twist comparison.
- Tex 8308–8310 — OK: the given tower provides the selected division point and the exact finite component of the global cocycle.
- Tex 8340–8357 — OK: use the fixed split twist, the fixed row and its one nonzero square-cocycle value; no precision-dependent rescaling.
- Tex 8358–8376 — OK: use the earlier joint-field stage construction and the same place exhibiting its chosen representative.
- Tex 8377–8391 — OK: use the earlier `κ_M(P)=F²R−R` with unchanged arithmetic Frobenius convention and exact finite row.
- Tex 8392 — gap filled: the common valuation, equivariance, and the prime-to-`p` torsion specialization give the exact cocycle calculation on the selected division point.
- Tex 8393–8394 — gap filled: the same root specializes to a nonzero root over the prime field; the twist used on torsion and on the embedded rational witness has the same scalar.
- Tex 8394–8398 — gap filled: at conductor one the negative sign gives a principal inert prime; the contracted ring class residue is quadratic and reduction agrees at the selected absolute place.
- Tex 8399–8405 — OK: stages, precision growth and fixed valuation offset are the existing construction.
- Tex 8439–8453 — OK: the quadratic fixed group and the square-Frobenius Kummer formula use the same normalization.

All new Lean files were checked individually with `lean -j1` in the Lake
environment against the imported stage artifacts. Their `#print axioms`
outputs contain only `propext`, `Classical.choice`, and `Quot.sound`.
