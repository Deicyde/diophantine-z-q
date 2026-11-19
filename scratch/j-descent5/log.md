# CM period descent results log

## Sizing before any build

- **VERIFIED (source):** `JDescent3FunctionField.lean` attaches the actual generic stalk, the rational identity place matching its stalk, and all positive pole-space dimensions and exact poles conditional on genus one. Tau Ceti's `RiemannRoch/Basic.lean` and `Place/Basic.lean` give order tests for pole spaces, strict valuation inequalities, and uniformizers. Its `EllipticCurve/Affine/FunctionField/Genus.lean` computes those spaces for an existing Weierstrass equation, so it cannot construct the equation here. The new algebra is distinct-order independence, a relation at order six, coordinate changes, and the exclusion of a simple pole via order one. This looks like a self-contained function-field proof.
- **VERIFIED (source):** The vendor `AlgebraicCurve.exists_place_range_stalk_eq` attaches a valuation subring to each closed point. Mathlib's generic-stalk construction embeds sections on nonempty opens into the function field. Sections need a local-to-global gluing lemma, and a place attached to a closed point other than the identity must be shown distinct from the identity place. Inversion requires transporting stalk orders or obtaining evenness directly from the analytic double pole and cubic. These are separate from the cubic relation.
- **VERIFIED (source):** `JDescent.lean` recovers an algebraic modular invariant from the matched short coefficients; `JDescent2Analytic.lean` identifies the lattice coordinates from a nonsingular cubic, an even abscissa and an exact double pole, and `hasDoublePoleAtZero_of_localParameter` handles the analytic identity with a numerator and local parameter. The same-period holomorphy and openness clauses are in `HDecomp/LeafPush2/R22.lean`; the stronger `HDecomp/Analytic/Uniformization.lean` supplies a coordinate derivative for a different witness. `IsPeriodAt` does not assume a derivative for its witness.
- **SPECULATIVE (size):** Realize a parameter and a unit numerator as sections on a neighborhood of the identity. Their value and unit identities are algebraic; showing a nonzero derivative needs actual first-order information on the given period map, or a proof that an analytic parameter evaluation on it is locally injective. That comparison can be isolated without invoking a general comparison of algebraic and analytic meromorphic functions.

## Cubic

- **VERIFIED (Lean):** `abVar_shortCubic_of_genusOne` constructs the normalized short equation in the actual generic stalk, with pole orders −2 and −3 and no other poles. Distinct-order independence makes six monomials a basis of the sixth pole space. A zero cubic coefficient would place the square of the ordinate in the fifth pole space. The singular case is excluded by a quotient with sole pole of order one.
- **VERIFIED (Lean):** `JDescent5Cubic.lean` compiled under `lake env lean`; all five theorem checks report only the standard three axioms.

## Sections

- **VERIFIED (Lean):** `abVar_shortSections_of_genusOne` realizes the normalized coordinates as regular sections on the complement of the identity. The proof uses the injectivity of the correspondence from closed points to stalk images in the generic field. The sections on a cover agree in the generic stalk and therefore glue; the cubic equation also lifts by injectivity there.
- **VERIFIED (Lean):** `JDescent5Sections.lean` compiled under `lake env lean`; all six theorem checks report only the standard three axioms.

## Pole-space action of an involution

- **VERIFIED (Lean):** `shortCubic_parity_of_place_involution` proves that any ground-field involution preserving the marked place fixes the short abscissa and sends the ordinate to itself or its negative. The proof expands the transformed coordinates in pole spaces of dimensions two and three. The involution forces both leading coefficients to square to one, while the cubic relates their cube and square. This fixes the abscissa coefficient and makes its translation zero.
- **VERIFIED (Lean):** Both theorem checks in `JDescent5Parity.lean` list only the three standard axioms.

## Scheme inversion, local parameter, and period evaluation

- **VERIFIED (Lean):** Scheme inversion induces an involutive automorphism of the actual generic stalk preserving the identity place. The abscissa is fixed as a rational function and as a section on the punctured scheme, and evaluates to an even function of the specified period.
- **VERIFIED (Lean):** The order-two abscissa has a parameter and unit numerator on one algebraic neighborhood of the identity. On this neighborhood, regular sections evaluate holomorphically along the specified period. The parameter vanishes and the numerator is nonzero at zero. Off the lattice and sufficiently near zero the section identity evaluates to the parameter identity for an exact double pole.
- **VERIFIED (Lean):** The analytic double-pole conclusion and the row proof compile with the parameter evaluation's nonzero derivative as the sole extra comparison beyond genus and Fowler. This formulation uses exactly the period witness in the input.
- **VERIFIED (source):** `Contrib/MulEtale/Direct/PowerAtIdentity.lean` additionally computes multiplication by two on the actual dual-number tangent arrows. This could bypass a general analytification comparison by comparing the first nonzero analytic term under doubling.

## Doubling on the identity parameter

- **VERIFIED (Lean):** `abVar_double_parameter_mod_square` proves `[2]^*t = 2t + t²g` in the actual identity stalk for every order-one parameter. The rational identity splits the residue map, valuation order one gives the generator of its kernel, and the resulting normalized residue derivation is represented by the existing dual-number tangent arrow. Applying the proved multiplication formula to that arrow gives the congruence. All five theorem checks in `JDescent5Doubling.lean` give only the standard three axioms.

## Sign of the ordinate

- **VERIFIED (Lean):** The pole-degree formula at the rational identity gives degree two over the field generated by the abscissa and degree three over the field generated by the ordinate. Since the degree over their joint field divides both, the coordinates generate the actual generic stalk.
- **VERIFIED (Lean):** The period point of coordinate `1/3` is different from its inverse. Equality on the generic stalk would force scheme inversion to be the identity by separateness. Hence the ordinate's positive sign is excluded. `abVarInv_sections_of_genusOne` gives invariance of the abscissa and negation of the ordinate as identities of sections. All six theorem checks in `JDescent5Odd.lean` give only the standard three axioms.

## Exact analytic double pole and assembly

- **VERIFIED (Lean):** The congruence for doubling lifts to an identity of sections on an open about the identity. Along the specified period it is `f(2z) = 2f(z) + f(z)^2 g(z)` near zero. The analytic germ `f` cannot vanish locally because `f²x=u` on a punctured neighborhood with `u(0) ≠ 0`. If `f(z)=z^n v(z)` with `v(0) ≠ 0`, cancel `z^n` off zero and pass to the limit; the resulting `2^n = 2` gives `n=1`. There is no remaining derivative premise.
- **VERIFIED (Lean):** `cmPeriodShortCoordinatesDoublePole_of_genusOne` and `cmjDegree_of_print_of_genusOne` compile under `lake env lean`. The hypotheses of the latter are exactly `AbVarFunctionFieldGenusOne` and `CMjDegreePrint`. Both final theorem checks list only the three standard axioms.

## Verification

- **VERIFIED (Lean):** All nine new modules and the row-only `#discharges` check compiled. Every new theorem has a `#print axioms` invocation. The consolidated audit checks 52 declarations and contains only `propext`, `Classical.choice` and `Quot.sound`.
- **VERIFIED (Lean):** `#discharges` matches `cmjDegree` and reports exactly the expected genus and print hypotheses for the new reduction.
- **VERIFIED (dry run):** The preview carries forward the existing Fowler statement and has a placeholder only for the genus proof. The excerpt records the pinned base; the command did not apply a fold.
