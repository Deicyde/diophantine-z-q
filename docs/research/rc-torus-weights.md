# Torus weights at the actual (O.7) stage

**The constructor for `DatumAt.weights` is pointwise.** Given the
adelic realization of the actual orientation fibers and the local
readings below, `datumWeights` supplies all fields of
`TorusWeights s.visibility A`. It takes the full odd filter on the
chosen stage. It uses the embedding of the square root from the
supplied `IntegralSupport.basis`, and evaluates the descended ideal
character on the class of the same finite idele used to move the frame.
It uses the existing trivial descent for `D = 1`. No point values or
coefficient sums enter the proof.

For a tuple `t` and class `c`, equality with the rationally translated
right ideal gives the chosen frame
`diag(q) * (embed(a_c) * z_t) * r` by `Adelic.fromAdelic_translate_iff`. A vector in the corresponding
orbit is `q x₀ q⁻¹`. Its local coordinates in that frame are
`r_p⁻¹ (z_{t,p}⁻¹ x₀ z_{t,p}) r_p`. Rational factors disappear from the
norm character, and the torus factor disappears from the Schwartz
argument by centralization. The norm multiplier is the character of
`r`; the Schwartz multiplier is the inverse of that same character.
The norm base is a sign. The base Schwartz value is nonzero because
its transported value on the identity-class support orbit is nonzero;
each local factor of the base product therefore has two-power order.

The local reduced norm calculation, the product over unramified
primes, and transport through the chosen representatives and orbit
quotient are on-the-spot (c). No new print or leaf is used.

## Statements and consumers

All names are in `ZInQ.Manuscript.RC.TorusWeights`.
In the table `C` is the norm factor data, `W` the local Schwartz
data, `T` the adelic presentation, and `J` the ideal reading.

| Declaration | Statement and field supplied |
| --- | --- |
| `localNrd` | Bundles the scalar of `x * star x` as a multiplicative map from local quaternion units to p-adic units. Used in `norm_transport` and `schwartz_transport`. |
| `NormFactors.onIntegralNorm` | If all reduced-norm valuations of `z` are the prime exponents of a nonzero natural `n`, and the reduced norm is 1 at primes of `h_*`, then `↑(C.character z) = chiD hstar n` in `ℤ`. Supplies the arithmetic for `character` and `norm_transport`. |
| `descent_of_filter` | For `[F:ℚ] = 2` and `discr F = D*h_*` on the odd filter, `(1 < D → NormCharacterDescent F hstar) → NormCharacterDescent F hstar`. Supplies `character` at the identity parameter `D = 1` as well as the supplied case `D > 1`. |
| `NormFactors.rightProduct` | For an everywhere integral right unit `r`, its character equals the product of its local norm characters on `W.primes`. This is used in `schwartz_transport`. |
| `SchwartzFactors.eval_order` | A nonzero Schwartz product in any frame satisfies `∃ j : ℕ, W.eval z x ^ (2 ^ j : ℕ) = 1`. Supplies `schwartz_order`. |
| `sign_square` | For `v : ℤˣ`, the square of its image in the coefficient ring is one. Supplies `norm_order`. |
| `frame_transport` | If `a` centralizes the local images of `x`, the coordinates of `q x q⁻¹` in `diag(q) * (a*z) * r` are the `r_p⁻¹` conjugates of the coordinates of `x` in `z`. Used in `schwartz_transport`. |
| `torus_character` | For every `c`, `↑(C.character (T.embedIdeles (T.idele c))) = ↑(hχ.choose (J.pic c))` in `ℤ`. Supplies `character` and its appearance in `norm_transport`. |
| `orbit_transport` | For every `t,c` there is one `r : Adelic.integralUnits _` with `χN = C(z_t) C(embed(a_c)) C(r)` and `f = W.eval z_t x₀ * C(r)⁻¹` at the chosen orbit representative. Supplies `transport` and both transport equations. |
| `actualWeights`, `datumWeights` | Construct `O7Actual.TorusWeights s.visibility A` with the two base values just displayed and the descended `character`. The second constructor uses the field and basis of the very `IntegralSupport` that fixes the class-group type of `DatumAt.weights`. |

## Remaining hypotheses

These are the exact inputs to the constructor. Each is a smaller
obligation than the stage's two transport identities with their base
orders and class character.

| Input and owner | Exact obligation and manuscript step |
| --- | --- |
| Odd filter and field datum; ELLIOT input at the stage caller | `OddFilter N s.ell D (-(s.weights.m : ℤ))`: `D > 0`, `Squarefree D`, `D.natAbs.Coprime hstar.natAbs`, `legendreSym s.ell D = 1`, `D*hstar` odd fundamental, and `Nonvanishing.SplitsIn (D*hstar) p` for every prime dividing `2*N`. The field datum has `discr F = D*hstar` (tex 9105–9108, 9121–9134, 9201–9208). These restrict the arithmetic index and say nothing about weights. |
| `IntegralSupport`, including `QuadraticBasis`; orbit, character, and theta join lanes | Supply the existing support datum for the same actual stage. The constructor projects the field, integer basis and class group; the support bridge is supplied upstream (tex 9123–9134). The basis provides the degree two and the root mapped by the rational embedding; neither gives a representation change for weights. |
| `NormCharacterDescent F hstar` for `1 < D`; character lane | The existing ideal-theoretic descent on conductor-one Picard classes (tex 9180–9194). The sibling proved this on its branch. The assumption contains no adelic or stage weights. |
| `A` and `TorusParametrization s D Q A`; Picard-fiber lane | Use the report's `∀ t, ClassGroup (𝓞 F) ≃ {P : OrbitSet s.visibility (actualIndex s D) // A.orientation P = t}` as `A.fiber`. For that very equivalence, give `ι`, the map of finite ideles into the quaternion finite units, `z_t`, and one finite idele `a_c` of class `c`. The embedded ideles centralize `ι(√d)) locally. The image of `(t,c)` is the orbit represented by `(a_c z_t, ι(√d))`: there is a `q` such that the chosen right ideal is the `q`-translate of `Adelic.fromAdelic (embed(a_c) * z_t)` and the vector `q x₀ q⁻¹` is supported with quotient class the orbit component of `A.param (t,c)` (tex 9150–9174). This is an orbit and representative comparison with no character evaluations; constructing the restricted-product realization and the two quotient maps is substantial upstream work. |
| `TorusIdealRead T`; Picard-fiber lane plus local reduced-norm dictionary | For each `c`, a nonzero integral ideal `J_c` of norm prime to `s.weights.m`, the equality `toFractionalIdeal (a_c) = FractionalIdeal.mk0 J_c`, and the conductor-one comparison `(conductorOrder F 1).picClass J_c = pic c` for a multiplicative equivalence `pic`. The precise remaining local norm statements are `Padic.valuation (localNrd p (embed(a_c))_p) = (Ideal.absNorm J_c).factorization p` at every rational prime and `localNrd p (embed(a_c))_p = 1` at primes dividing `s.weights.m`. These are valuation and normalization facts, not character equalities (tex 9161–9166, 9178–9194). Grouping the local field factors and identifying the reduced norm with the local field norm is the substantive part; once those maps exist, the equalities are local ideal-norm calculations. |
| `NormFactors`; theta join / finite norm character | The finite character of the adelic reduced norm as a homomorphism to `ℤˣ`, its local factors on `ℚ_pˣ`, triviality on the rational diagonal, value `chiD hstar p ^ v` at unramified (p) for `v ≥ 0`, valuation zero of the norm of a local order unit, and the local product formula in `NormFactors.product` (tex 8571–8578, 8601–8603, 8612–8614, 9178–9192). These are raw norm facts. The constructor proves the evaluation on the torus from them and the separate norm dictionary. The global character packaging is a separate small to medium interface. |
| `SchwartzFactors` and `StageRead`; theta join | Give a finite set of Schwartz factors containing the primes of `h_*`, with local covariance by the inverse local norm character and two-power order of each nonzero local value. Then give the exact readings of `PMLocal.χN` and `PMLocal.f` at `Adelic.classRepresentative z`, the second on nonzero support at the actual index (tex 8495–8578, 8601–8604, 9121–9134, 9321–9327). The local rules and the chosen representative readings involve no torus, Picard class, base phase, or common transport. The reading is a small interface once the local factors have been joined. |

## Verification

`Norm.lean` and `Actual.lean` passed separate, sequential
`lake env lean --threads=1` runs. The inline `#print axioms` checks
cover all eight new theorems and the three listed definitions.
`sign_square` uses only `propext` and `Classical.choice`; the other
ten checks report `propext`, `Classical.choice`, and `Quot.sound`.
Neither file adds an axiom or an unfinished proof.

## Known issues

- As the orbit report notes, the comment on
  `Visibility.ThetaStage.χN` overstates descent to the adelic double
  quotient. The bare norm character can change at a ramified
  character prime. Tex 8571–8578 and 8612–8614 assert representative
  independence of the combined summand; the construction uses that
  convention and keeps the individual chosen-frame values.
- An integral ideal prime to `h_*` only forces valuation zero at those
  primes. It does not fix the unit coordinates of an arbitrary
  representing idele. Normalize the finite idele to be 1 at all
  places above `h_*` (which preserves its ideal); the exact
  reduced-norm condition used here is `TorusIdealRead.ramified_one`.
- The Cornut–Jetchev reduction at tex 9195–9295 is outside this
  pointwise weight constructor and no printed locator for it is used.

## Manuscript check

- 8495–8566 — unverified for the stage join: local factors, supports, and fixed character values are handed in; this proof uses their per-prime order and covariance.
- 8571–8578 — gap filled: derive the right adelic multiplier from the product of the local norm factors and the inverse local covariance.
- 8601–8604, 8612–8614 — OK: with the chosen representative readings, rational diagonal invariance and the common right unit give the two separate changes.
- 9105–9108, 9121–9134 — OK: the exact filter includes positivity, squarefreeness, coprimality, the detecting symbol, odd fundamental discriminant, and splitting at every prime of `2N`. Nonzero support and the matching basis are upstream.
- 9150–9170 — unverified here: the actual finite idele embedding, orientation fiber equivalences, and compatibility of the orbit and ideal descriptions are supplied by the sibling.
- 9171–9180 — gap filled: torus centralization gives the unchanged raw Schwartz argument; the right ideal comparison gives the precise right unit that appears in both factors.
- 9181–9194 — gap filled conditional on the valuation and normalization dictionary: the prime factors give the norm symbol on the same integral ideal, and its image is the descended character. The `D = 1` descent is proved in the existing tree.
- 9195–9295 — unverified here: source reduction, sign fiber, same-place specialization and the point-value sum belong to the reference reduction.
- 9297–9305 — OK: the existing support action gives equality of the Schwartz values on the rational unit orbit, so the result applies to its chosen vector.
- 9321–9327 — gap filled: the base Schwartz value is nonzero by the supported orbit; multiplication preserves the local two-power orders, and the norm sign has square one.
