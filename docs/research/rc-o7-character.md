# (O.7): conductor-one norm descent and integral basis

Both inputs of `rc-o7-actual` are discharged on the odd filter, including
the previously open case `D > 1`. The Picard character has values in
`ℤˣ` and agrees with the requested norm symbol on **every** integral
ideal of norm prime to `h_*`. The actual stage also receives
`IntegralSupport.basis`, `disc_neg`, and `disc_mod_eight`. No new print
is used.

The proof follows route (a). Put `d = D h_*` and
`θ = (1 + √d)/2`. The tree's `exists_sq_eq_discr` gives the root in
the supplied field. The lift from the rational quadratic algebra is
an equivalence by injectivity and dimension two. The element `θ`
satisfies `θ² − θ − (d−1)/4 = 0`. The rational change from `(1, √d)`
to `(1, θ)` has determinant `1/2`, so the existing calculation of
`disc(1, √d) = 4d` gives `disc(1, θ) = d`. In the integral basis
of the field the two columns have integer coordinates; their
determinant squares to one. They therefore span the ring of integers
over the integers. This uses the supplied **field** discriminant
equality; no separate squarefreeness premise is needed.

For `α = i + jθ` the quadratic norm formula gives
`4 absNorm((α)) = (2i+j)² − d j²`. Reducing modulo `|h_*|` and using
that the norm is prime to `h_*` gives Jacobi symbol one: the right side
is a unit square and the symbol of four is one at the odd modulus.
The existing ray class maps move every conductor-one Picard class to an
integral representative coprime to the modulus `(|h_*|)`. The
principal kernel of `picClass` then gives equality of the Jacobi sign
on any two eligible representatives of the same class, by
multiplying each by an eligible representative of the inverse class.
This is the principal kernel argument of
`ZInQKernel/Contrib/OneProof/RC/Gz34Instance/Character.lean` at conductor one. The square-one
Jacobi values are made into integer units at the start, so no complex
character or change of codomain is needed. The basis index argument
and elementary alternative to the manuscript's reciprocity proof,
including the moving and descent steps, are on-the-spot (c).

## Formal statements

All declarations below are in `ZInQ.Manuscript.RC.O7Character`.
Write `deg F` for `Module.finrank ℚ F`.

| Declaration | Statement and input discharged |
| --- | --- |
| `quadraticBasis` | For `deg F = 2`, `discr F = D * -m`, `D * -m < 0` and `(D * -m) % 4 = 1`, constructs `QuadraticBasis F (D * -m)`. Discharges the integral basis input to `halfIntegral_iff_optimal` and the basis used for stabilizers and orbit parametrization. |
| `normCharacterDescent` | For `deg F = 2`, `discr F = D * hstar`, `D * hstar < 0` and `(D * hstar) % 8 = 1`, proves `NormCharacterDescent F hstar`. Discharges the named ELLIOT descent input at `D > 1`; the statement also applies at `D = 1`. |
| `stageIntegralArithmetic` | Given `s : StageAt O N M hN m`, `deg F = 2`, `discr F = D * -m`, `D * -m < 0` and `(D * -m) % 8 = 1`, supplies the basis at the stage's actual weight parameter and the two discriminant facts in `StageIntegralArithmetic s D F`. Discharges those three fields of `IntegralSupport`, using `s.m_eq`. |

The private construction `quadraticBasisOfDiscr` uses the general
parameter `d`. The private theorems are `half_discr` (discriminant of the half basis),
`spans_of_discr` (an integral pair with the field discriminant spans),
`principal_norm_formula`, `chiD_principal`, and `exists_picClass_coprime`
(the five assertions described above).

## Remaining hypotheses and ownership

There is no residual genus or integral-basis proof hypothesis, and no
replacement ELLIOT or GLUE leaf. The exact arithmetic inputs at a call
site are `deg F = 2`, `discr F = D * hstar`, `D * hstar < 0`, and
`(D * hstar) % 8 = 1` (or `% 4 = 1` for the basis alone).
The actual filter and field datum supply these (stage selection and
its caller in `rc-o7-orbits`). Degree and discriminant identify the
field; negativity and the residue condition are scalar facts about
the datum. They contain no assertion about ideals, representatives,
characters or their values. This is the sense in which the required
input is strictly weaker in scope than descent; it is not a claim
that bare `NormCharacterDescent F hstar` implies a choice of field
discriminant. Positivity and squarefreeness of `D` and coprimality with
`h_*` are filter conditions, and are redundant once these inputs are
known.

The separate `IntegralSupport.half` condition remains with
`rc-theta-join`: it just requires membership of the half generator in
the class left order for each supported vector. It has no Picard
character quantifier. The comparison still needs the independent
orbit/weight inputs (`rc-o7-orbits`), the existing
`Voight1467VToIII` rational embedding GLUE, and the reference reduction/stage join
(`rc-o7-orbits` and `rc-stage-selector`). That join still has to supply
`hχF` of `lamOf_reduction_at`: for each reference-fiber index `c`, its
coefficient `χF c` is the cast of the selected datum's
`chiSign dat.χ ((ringClassArtinEquiv (conductorOrder dat.K 1)).symm (e c))`.
This is a pointwise identification of two existing characters along
the given parametrization; it does not require constructing a new
global character. These are separate interfaces of the host comparison,
not hypotheses of either discharge.

## Verification

`Basis.lean`, `Character.lean`, and `Stage.lean` each passed
`lake env lean`, sequentially. The separate
`scratch/rc-o7-character/Axioms.lean` run printed the following
dependencies. There are no other axioms or unproved declarations in
the new files.

| Declarations | `#print axioms` result |
| --- | --- |
| `quadraticBasis`, `normCharacterDescent`, `StageIntegralArithmetic`, `stageIntegralArithmetic` | `propext`, `Classical.choice`, `Quot.sound` |
| `half_discr`, `spans_of_discr`, `quadraticBasisOfDiscr`, `principal_norm_formula`, `chiD_principal`, `exists_picClass_coprime` | `propext`, `Classical.choice`, `Quot.sound` |

## Known issues

No new manuscript or source error was found in the steps audited
below. The Voight implication remains GLUE and its published wording
is UNVERIFIED here, as in `docs/research/rc-o7-actual.md`. The host
report also records the Jetchev–Kane level-one scope issue; neither
source is used by this proof.

## Manuscript check

- 2404–2410, 8209–8212 — OK: the selected negative partner and the odd filter give the discriminant datum used here; its stipulated splitting at two is used in the form `d ≡ 1 mod 8`.
- 8213–8217 — gap filled: the elementary norm weight in (O.1) is independent of the choice of eligible representative by `normCharacterDescent`.
- 8261–8266 — unverified: this work does not identify the character's fixed field or the rational character components of the point.
- 9105–9108, 9121–9123 — OK: the proof takes the quadratic field with the indicated negative discriminant and the residue condition at two; inertness at the detecting prime is unnecessary here.
- 9123–9131 — gap filled: `quadraticBasis` proves the maximal order is generated by the half generator, as used by the existing optimality criterion.
- 9171–9182 — OK: the norm-symbol factor on an eligible integral torus ideal represents the character in (O.1); adelic transport and the other weight factor stay with the orbit work.
- 9183–9189 — gap filled for descent: the principal norm congruence replaces the biquadratic discriminant and reciprocity argument; no fixed-field identification is asserted here.
- 9189–9193 — OK: the existing self case handles the trivial character, and the moving argument and integer-unit codomain give eligible representatives and sign invariance under inversion.
