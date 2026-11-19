# Appendix F: the geometry at the detector's place

**Result and scope.** The divisor identities of the specialized modular
parametrization give the Hecke and affine Atkin–Lehner identities of
`PM.Geometry`. Rationality of the base cusp gives Frobenius equivariance;
the comparison of the right uniformizer with Frobenius is made on the same
supersingular locus. At the selected absolute place, good reduction gives
an additive equivalence on geometric `2^M`-torsion. The global integral
detector row, reduced modulo `2^M` and transported by that equivalence,
gives `PM.Evaluation` with its fixed row and trivial Frobenius square.
The two theta constructors then use the same `P_M`.

The formalization stops at the point and divisor interfaces of the modular
special fibre. To instantiate them one needs a good model of `X₀(N)` and
its Jacobian and correspondences, the extension of the elliptic quotient,
and the comparisons of their specializations. The supplied interfaces ask
only for coarse points, a divisor class map, the specialized quotient and
the identities on the relevant divisor classes. They do not replace
construction of the modular curve or reduction of its correspondences.
For the Heegner contribution the remaining geometric input is the
pointwise reduction of the CM points in the reference orientation and
commutation with the extended parametrization, at the very same place.
With these inputs the proof supplies the reference tuple congruence in
`Visibility.ComparisonCore` for each matched datum. The rest of (O.7)
still uses the orientation, weight and theta data of its existing interface.

## Statements and consumers

All new declarations are in `ZInQ.Manuscript.RC.PMGeometry`.
Write `F` for arithmetic Frobenius over the prime field and `n = 2^M`.

| Declaration | Statement and consumer |
| --- | --- |
| `center` | The additive map `D ↦ D - deg(D)[∞]` to degree-zero divisors; used to define the based Abel–Jacobi input. |
| `GeometricInput.onDivisor`, `specialize` | The quotient of the divisor class after centering, evaluated on `[x]` for specialization; supplies `Geometry.specialize`. |
| `GeometricInput.specialize_infinity` | `specialize infinity = 0`; the base case for `Geometry.hecke` and `Geometry.specialize_frob`. |
| `GeometricInput.hecke` | For good `p` and every actual line index, the sum of specialized neighbour values with multiplicity is `a_p • specialize z`; supplies `Geometry.hecke`. |
| `GeometricInput.cusp`, `atkin_affine` | The cusp term is `specialize (W_p infinity)`; after the right Atkin–Lehner operation the value is `w_p • specialize z + cusp p`; supplies `Geometry.cusp` and `Geometry.atkin_affine`. |
| `GeometricInput.frobSS`, `specialize_frob` | Restrict arithmetic Frobenius to the supersingular locus; the specialized value at that Frobenius is `fixedFrob F (specialize x)`; supplies `Geometry.frobSS` and `Geometry.specialize_frob`. |
| `GeometricInput.frobSS_involutive` | Frobenius squared is the identity on the coarse pairs, so replacing it by its inverse leaves the class operation unchanged. |
| `GeometricInput.uniformizer_spec` | The class equivalence takes the right uniformizer to `frobSS`; supplies `Geometry.uniformizer_spec`. |
| `GeometricInput.geometry` | Builds `PM.Geometry` from the above and the named adelic outputs. |
| `rowOnOriginal`, `rowOnOriginal_fixed` | Transport the detector row to the original Tate module by the inverse geometric twist equivalence. If the detector fixes the splitting root, the transported row is fixed by the same element, by `Stages.geomTwist_equivariant`. |
| `reducedEquation_elliptic` | If the prime does not divide the integral discriminant, the reduced equation over the prime field is elliptic. This gives the curve instance for `PM.lam`. |
| `goodIntegralEquation` | The actual stage's `GoodAt` condition implies the integral discriminant is a unit; proves the good-reduction premise for `evaluationOfStage`. |
| `torsionSpecialization`, `torsionSpecialization_frob` | Reduction restricts to an additive equivalence on geometric `n`-torsion, intertwining the selected absolute Galois element and `F`; these supply the transport in `ofTateRow`. |
| `proj_onto` (private) | Every finite-level Tate vector lifts to the Tate module; used for finite row invariance and the square action. |
| `finiteRow_fixed` | If `g` and `σ` agree on the torsion field at level `M` and `b ∘ ρ(σ) = b`, then `finiteRow b M` is invariant under `g`; gives `Evaluation.row_fixed` after transport. |
| `square_trivial_at` | With the same finite-level agreement and `ρ(σ²) = 1`, `F²` fixes geometric residue `n`-torsion; supplies `Evaluation.square_trivial`. |
| `evaluationAt`, `evaluationOfStage` | Supply `PM.Evaluation` using `ofTateRow`, oddness, the square action and the fixed row. The latter constructor gets oddness and agreement from the actual stage and uses the same `selectedFrobenius` place as the witness. |
| `stageMap_eq_lam_comp` | The existing untwisted `WitnessSpec.stageMap` on a supplied datum reduction `r` equals `(PM.lam evaluation).comp r`; identifies the stage evaluation where this local formula is used. |
| `conjugate`, `datumReduction` | Use the actual `galPt` action and the conductor-one ring class reduction of `WitnessSpec` at the selected place; their codomain in the reduction square is `FixedSq F`. |
| `InputsAtDatum.point_reduction` | The specialized value at `z_{t₀,c}` equals the same-place reduction of `σ_c(y)`. |
| `InputsAtDatum.lift_at_conjugate` | Every integral lift of `P_M` at `z_{t₀,c}` agrees modulo `n` with the finite stage value of `L • σ_c(y)`; supplies the pointwise premise of `Visibility.lamOf_reduction`. |
| `lamOf_reduction_at` | The weighted reference-tuple sum of those lifts equals `lamOf` modulo `2^M 𝒪`, given the existing Artin character match and equality of the stage map with the constructed evaluation at the selected entry. Supplies `ComparisonCore.reduction`. |
| `appFStage`, `visibilityStage` | Partially apply the existing constructors to the derived geometry and actual-place detector, retaining the original theta, frame, Schwartz and lift inputs. |

The specialization proof reuses `WitnessSpec.curveReduction_torsion_bijective`
and `curveReduction_frobenius`. The injectivity part of the former descends any
point in the kernel to a finite field of definition and uses prime-to-residue-
characteristic torsion injectivity there; the equal cardinalities then give
surjectivity on the geometric torsion. The proof of `finiteRow_fixed` uses
surjectivity of finite Tate projection and equality of the actions on the
finite torsion field. It does not require that the chosen Frobenius lift and
the detector element agree on the entire Tate module.

## Named inputs and provenance

`InputsAtDatum` includes `GeometricInput` and its two dependent
Heegner comparison fields. The point and Jacobian models are inputs in
the scope of the stop rule.

| Input | Manuscript and provenance |
| --- | --- |
| `Adelic.ram` | 8462–8463, PRINT: existing `AppF.VoightMainThm1461` instance for the chosen algebra. The print is existential; the record takes its ramification output. |
| `Adelic.eichler`, `LineIndex`, `Adelic.atkin`, `atkin_involutive`, `uniformizer` | 8464–8468, 8481–8490, 9040–9042, 9067–9071, 9331–9358, ELLIOT: hypotheses from the adelic task and the existing ideal interfaces. |
| `Point`, `ss`, `classes` | 8465–8474, PRINT: Jetchev–Kane §§1.1–1.2 and 2.5 as cited (locators UNVERIFIED in this run), in the coarse quadratic-residue model. `classes` is the named statement of the geometric part of that print, after supplying the adelic identification. |
| `T`, `W`, `frobenius`, `frobenius_sq`, `frobenius_ss`, `hecke_compare`, `atkin_compare`, `frobenius_compare` | 8469–8479, 8483–8490, 9331–9358: the good geometric correspondences and arithmetic Frobenius, and their agreement with the adelic operations. The operator comparisons are ELLIOT's use of the model; they are not a separate print. |
| `infinity`, `T_infinity`, `frobenius_infinity` | 8476–8487, 9347–9355, ELLIOT: the rational base cusp, its good Hecke divisor, and its Frobenius fixedness. |
| `J`, `divisorClass`, `quotient` | 8476–8481, ELLIOT: the specialization of the Abel–Jacobi divisor class and elliptic quotient at good reduction. |
| `hecke_quotient`, `atkinSign`, `atkinSign_eq`, `atkin_quotient`, `frobenius_quotient` | 8481–8489, 9334–9339, 9347–9355, ELLIOT: the quotient relations restricted to the degree-zero classes used in the proof. No affine point identity is assumed. |
| `reduceCM`, `cm_class` | 9265–9279, existing Cornut–Jetchev input as used in `Visibility.Models`: geometric reduction on the reference sign and level orientations, using Thm. 3.1, Cor. 3.2 and §§4.9–4.10 as cited. The pointwise identification is kept as a named comparison; the abstract bijection alone does not give it. No new Cornut–Jetchev print is introduced. |
| `pi_commutes` | 8476–8479, 9283–9291, ELLIOT: the extension of the parametrization commutes with the actual reduction on the CM conjugates. |
| `DatumPlace`, good reduction, global row and its Galois data | 8340–8343, 8360–8393, 9205–9209, 9265–9272, 9288–9290, ELLIOT: the chosen absolute place, a ring class embedding at that place, inertness of the prime, and the finite-level agreement, square and row of the global detector. The actual stage gives oddness and a unit discriminant; the datum gives its quadratic degree, and the negative Legendre sign gives the discriminant unit. No residue-level detector condition is assumed. |

The local group and divisor calculations not written explicitly in the
manuscript are on-the-spot (c). No new external result besides the named
Jetchev–Kane input is used as a leaf; the existing Voight and Cornut–Jetchev
statements retain their scope.

## Known issues

- The prior source audit (A052 in
  `docs/theorem-application-audit/INVENTORY.md`) reports that
  Jetchev–Kane has `N > 1` and prime-to-`ℓ₀` level, without a squarefree
  assumption. Its scope does not, by itself, certify the manuscript's
  wording “every `N` prime to `ℓ₀`” at `N = 1`; no level-one
  application of that citation is made here. The audit separates the
  class-set identification from the later theta and orientation arguments.
- The manuscript switches its symbol `F`: tex 8379–8388 uses the
  prime-field action, while tex 8440–8446 uses quadratic-field Frobenius.
  Here `curveFrob` is the prime-field action throughout, and the Kummer
  map uses `F²-1`.
- The witness's total `StageKummer` was constructed to have the local
  formula only at its chosen datum. The Heegner theorem requires the map
  equality only at the entry it evaluates. A family covering further
  admissible data needs their actual ring class embeddings, same-place
  reductions and geometric comparison. The untwisted detector row is
  the one on `T₂E` after the manuscript's split twist identification.

## Manuscript check

- 8340–8343 — OK: the split geometric twist carries the fixed detector row to the original curve.
- 8359–8377 — OK: the chosen Frobenius agrees on the finite torsion field, which suffices for the reduced square action.
- 8378–8393 — gap filled: the existing reduction bijection and Frobenius compatibility identify the global row and the one on the geometric special fibre.
- 8394–8398 — OK: the twist and fixed-witness specialization are the earlier `WitnessSpec` result; the witness construction is not repeated here.
- 8440–8456 — OK: quadratic Frobenius is the square of the prime-field action, and `bC=b` descends to the finite row.
- 8457–8459 — OK: the already proved fixed-witness equality evaluates the compatible division point at the chosen place.
- 8462–8464 — unverified: reuse the existing Voight print and the adelic outputs; no fresh source check or Eichler construction.
- 8465–8474 — unverified: Jetchev–Kane is used in the stated coarse supersingular model, with citation scope as above.
- 8476–8481 — unverified: the good modular model, specialized elliptic quotient, and correspondence extensions are named inputs.
- 8481–8487 — gap filled: apply the quotient to the Hecke difference divisor and annihilate `(p+1)[∞]`.
- 8487–8489 — gap filled: restoring the shifted base term gives the affine identity; the existing PM lemma applies it after multiplication kills the cusp.
- 8489–8492 — gap filled: restrict Frobenius to the supersingular locus, use its comparison with the right uniformizer, and apply the fixed row.
- 8493 — OK: both theta interfaces accept the same function via residue classes and integral lifts.
- 9195–9264 — unverified: the Heegner comparison uses the existing reference-orbit input, retaining one sign and the chosen level orientations.
- 9265–9279 — unverified: reduction of the actual enhanced CM point to the reference class is the pointwise input to the proof.
- 9280–9291 — gap filled: same-place point reduction, multiplication by `L` and additive evaluation yield the pointwise premise and then the finite sum congruence.
- 9331–9339 — OK: PM's existing lift lemma uses the derived affine relation after the specified `L` kills the cusp; the norm-character factor is separate.
- 9343–9358 — OK: the right uniformizer has eigenvalue `+1` on the detector; this adds no norm or Schwartz sign.

## Validation

All four files compiled with `lake env lean --threads=1` using the local
dependency cache and sequential rebuilds of missing imports. All 27
`#print axioms` checks report only `propext`, `Classical.choice` and
`Quot.sound`. No `sorry`, new axiom or main-module import.

A failed transition between verification queues briefly allowed two Lean
processes from this task to overlap. This violated the one-process rule.
The old queue was stopped, and the final checks above ran sequentially in
a single locked queue. A shell quoting error while drafting the handoff
later invoked Lean without a file or resource precheck; it printed usage
and compiled nothing.
