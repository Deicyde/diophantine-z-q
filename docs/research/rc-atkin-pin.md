# The newform sign in (O.7)

**Scoped stop.** The sign is the integer unit attached to the actual
newform at the exact divisor `p ^ N.factorization p`. There is a proof of
the signed translation of the scaled Eichler integral in `ℂ` and in the
period quotient. The complex chart proof gives the signed translation
of `CST.phiAn` and transfers it to the fixed rational parametrization
on interior complex points. To finish (a) over the rational model,
construct the rational Atkin–Lehner
involution inducing this chart action and descend the identity, based
at the rational cusp at infinity. The special-fibre passage (b) is
isolated from that work; the Lean implication from (a) and (b) has
the exact type of the pointwise Atkin field.

## Known issues

- Inherited citation scope: the two Milne references at tex 1784 do not
  establish the normalized-newform claim or the Hecke identity at
  tex 1788. See
  `ZInQKernel/Contrib/OneProof/RC/PrintsAnalytic/Milne.lean`.
  The bridge here uses the existing strong modularity input and the
  least-level theorem, rather than those citations.
- The prior O.7 source audit records a level-one scope issue for the
  Jetchev–Kane result used at tex 8468–8474. This task retains the
  `PMAdelic.JetchevKane` input. Primary locators for the inherited scope
  issues were not independently checked.
- The equality at the normalized cusp and identification of the
  moduli involution with the constructed rational model are separate
  from the eigenrelation. An equality of analytic functions on the
  interior alone has no Lean rule that identifies these maps over
  `ℚ`. No new printed leaf is introduced. Atkin–Lehner (1970) is
  used through the existing Lean eigenrelation, not as a citation for
  the descended parametrization formula.

## Statements

Declarations are in `ZInQ.Manuscript.RC.AtkinPin`.

| Module and declaration | Statement and use |
| --- | --- |
| `Sign.signUnit_cast` | For every exact divisor `Q`, the integer underlying `signUnit f hχ hQ` casts to `f.atkinLehnerSign hχ hQ`. |
| `Sign.wNew_cast` | The same assertion for the total `wNew f hχ p`, using `Q = p ^ N.factorization p`; the off-support exact divisor is 1. |
| `Assembly.consumerNewform` | Given the existing `PrintsAnalytic.ModularNewform`, returns `F : ConsumerNewform I` with `F.form.χ = 1` and `F.form.toCuspFormGamma0 F.trivial = I.f`. `ConsumerNewform.signs` is `wNew F.form F.trivial`. |
| `Assembly.stageLevel_eq` | `StageKummer.level ℓ = newformLevel (Ecurve ℓ)` through `EcurveZ_baseChange`, so the exponent uses the stage level. |
| `Assembly.oddStagedOfPinnedParamValues` | Builds the odd staged instance on `SelectorTotal.withParamIndices a` using `SelectorTotal.pointInputs` and `AtkinSign.oddStagedActual` with `w := F.signs`. The special-fibre input is `SpecialFibreAtSigns … F.signs`; its projected sign agrees by definition. |
| `Analytic.slash_eq_signUnit_smul` | The ordinary weight-two slash by `atkinGL hQ` acts on the very same newform by the complex cast of `signUnit`. The normalizing power at weight two is zero. |
| `Analytic.hasDerivAt_eichlerPotential` (private) | The derivative of `eichlerPotential f ∘ ofComplex` is `2πif` on the upper half-plane. |
| `Analytic.scaled_eichler_transform`, `periodClass_transform` | For `ζ = κ · eichlerPotential f` and every interior basepoint `t`, `ζ(W_Q τ) = ε_Q ζ(τ) + ζ(W_Q t) − ε_Q ζ(t)`. The first theorem is in `ℂ`; the second applies the quotient homomorphism and uses integer scalar multiplication. |
| `Uniformization.cast_point_some` (private), `weierPt_add` | A cast between equal Weierstrass equations preserves affine coordinates. For `IsLatticeOf E Lat`, the exact coordinate map `CST.weierPt E Lat` preserves addition. The change from its short Weierstrass model has scale 1. |
| `Generic.atkinGL_chart_congr`, `atkinGL_sq_chart` (private) | The matrix respects the chart orbit relation; its square acts as an element of `Γ₀(N)` because the intervening scalar acts trivially. |
| `Generic.atkinInterior_apply`, `atkinInterior_involutive` | The involution on `Set.range X.complexPoint` sends the chart point of `τ` to that of `W_Q τ` and squares to the identity. It specializes to `X0Branch.model`. |
| `Generic.phiAn_transform` | The same signed translation as for `ζ`, now with `CST.phiAn` in the group of complex points of the genuine elliptic curve. |
| `Generic.projectiveValue_transform_chart`, `actualParametrization_transform_chart` | Transfer the formula through the chart identity of the rational morphism. The second theorem uses the proved join to obtain the dominant morphism on `X0Branch.model` at the fixed scale, including the same `phiAn` comparison. |
| `Generic.RationalAtkin`, `BasedAtkinOnPoints` | The exact unresolved rational-model statements: a rational scheme involution with the proved chart action, and the based identity on field-valued points for that involution and the fixed morphism. These are interface definitions. |
| `Generic.translatedAtkinOnPoints` | From the based identity, `π(W_Q x) = [ε_Q]π(x) + c_Q` on field-valued points with the base change of `c_Q = π(W_Q b) − [ε_Q]π(b) ∈ E(ℚ)`. The theorem `translatedAtkinAtInfinity` uses the actual rational `infinityPoint` and the normalization `π(b)=0` to replace this by `π(W_Q ∞)`. |
| `Specialization.atkin_quotient_of_specialization`, `pinned_atkin_quotient_of_specialization` | Apply additive reduction to the based identity and substitute the two comparisons in `BasedSpecialization`. The pinned version uses `(wNew f hχ p : ℤ)` at the exact divisor `p ^ N.factorization p`, with no sign-agreement binder. |

The remaining `ha` is exactly the following divisibility for every
admissible `(i, D)`, with the row from `AtkinSign.actualRowFamily` and
`O = Coefficients hN (H 0) F.signs`:

```text
(2 : O) ^ W.Mθ i ∣
  row.weights.phase row.reference * (W.aθ i D : O) -
    Visibility.thetaCoeff (actualFamily … F.signs … i).visibility ((m : ℤ) * D)
```

This keeps one sign function in `O7Assemble.actualStage`, its
`levelRoots_parity` instance of (O.3), the special-fibre quotient, and the
coefficient reading. There is still a comparison to supply for the
fixed integer representative `W.aθ`; the newform does not by itself
identify that representative.

## The exact specialization input

Write `P = projectiveValue ∘ π` on field-valued points. At
`p^e ∥ N`, use the same `W_Q` with `Q = p^e` as in (a). For
each `x ∈ X.ss`, choose a common characteristic-zero coefficient
field at the good place, a lift `y` of `x`, and the base change
`a` of the rational cusp `b` specializing to `infinity`. The
geometric comparison must use the actual additive elliptic
reduction `red` in both of these equalities:

```text
red (P y - P a) =
  quotient (divisorClass (center infinity (of x)))
red (P (W_Q y) - P (W_Q a)) =
  quotient (divisorClass (center infinity (of (X.W p x) - of (X.W p infinity))))
```

In particular the second comparison needs the compatibility of the
algebraic involution with the coarse `X.W p` at both the lift and
the cusp. This is weaker than proving specialization of the
Jacobian action on every divisor, and does not require particular
CM lifts. The condition contains no eigenvalue. Applying `red`
to `P (W_Q y) - P (W_Q a) = [ε_Q](P y - P a)` and using additivity
proves exactly the field required by `SpecialFibreAtSigns`, before
the multiplier or detector. No integral model is built here.

## Remaining inputs

| Input | Reduction or reason it remains |
| --- | --- |
| Shared `PrintsAnalytic.ModularNewform` | Breuil–Conrad–Diamond–Taylor, *On the modularity of elliptic curves over ℚ: wild 3-adic exercises*, 2001, Theorem A and Introduction condition (2), existing composite input. For the move to the normalized newform at the conductor, see Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires de Hilbert*, 1986, local conductor theorem (number **UNVERIFIED**). The comparison to the actual cusp form at the least level is proved in the tree. |
| The fixed scale has a rational representative, and lattice data for `E` | These are inputs of the existing at-scale join. The rational pullback scalar follows from comparing rational differentials for the rational modular map normalized at infinity; a citation for the construction is Shimura, *On the factors of the jacobian variety of a modular function field*, 1973, Theorem 1, locator **UNVERIFIED**. A theorem constructing another map or scale does not prove rationality of an independently supplied `κ`. |
| `RationalAtkin (X0Branch.model N) hQ` | Classical rational moduli operation: replace `(A, C_Q ⊕ C_{N/Q})` by the quotient by `C_Q`, with level subgroup given by the dual kernel and the image of the complementary subgroup. Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*, 1973, cyclic isogeny moduli and their compactification, theorem number **UNVERIFIED**. The missing GLUE is its realization on the normalization used here, with the specified chart. A function-field route is to pull back both (j) and (j_N), compare their rational expansions, then extend the field automorphism by properness and the valuative argument for smooth curves. This is a model comparison rather than a new eigenvalue theorem. |
| Descend the chart formula to `BasedAtkinOnPoints`, with `b` the cusp and `π(b)=0` | Algebraic GLUE (c): compare the maps on the generic point using a faithful complex chart and the projective elliptic group law, then use separatedness. Constancy of `π∘W_Q − [ε_Q]π` identifies its value by evaluation at the existing `X0Model.cusp`. The base value requires comparing the fixed morphism with the rational formal arc at that cusp; `ParamJoin.Cusps` gives analytic period limits. The classical identity is tex 2943–2946. Atkin–Lehner, *Hecke operators on Γ₀(m)*, 1970, eigenrelation locator **UNVERIFIED**, supplies the modular-form step already proved in Lean; it does not identify the constructed projective maps. |
| `BasedSpecialization`, good Hecke/Frobenius comparison, and per-row `hπ` | Good reduction and moduli correspondences: Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*, 1973, theorem number **UNVERIFIED**. Extension to the elliptic target uses its Néron mapping property; Bosch–Lütkebohmert–Raynaud, *Néron Models*, 1990, §1.2, locator **UNVERIFIED**. The coarse identification and actual Artin-place compatibility are separate GLUE for the good-reduction work. |
| `hCusp` | Manin–Drinfeld, as cited via Elkik, *Le théorème de modularité de Wiles*, 1996, p. 59 Theorem, locator **UNVERIFIED**. It needs the based cusp dictionary and the agreed multiplier; owned by the cusp work. |
| `hCM`, source `CMFieldOfDefinition`, and coarse ideal-class comparison | The inherited `SelectorTotal` and `AtkinSign` inputs. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, 1971, Ch. 6 theorem number **UNVERIFIED** (field of definition); Jetchev–Kane, *Equidistribution of Heegner points and ternary quadratic forms*, 2011, manuscript citation to §§1.1–1.2 and 2.5; journal locator **UNVERIFIED** (coarse comparison, scope issue above). The Artin and orientation dictionaries are additional model comparisons. |
| Remaining stage arithmetic, (L), witness, central normalization, selector support and `ha` | Inherited separately in `rc-selector-total.md` and `rc-atkin-sign.md`. Choice of stage data and the exact reading of the integer in `ha` are interface data; no single refereed theorem fixes an independently supplied representative. |

## Manuscript check

| Tex and step | Verdict |
| --- | --- |
| 1779–1783: use modularity and the actual curve form. | OK |
| 1784 and 1788: cite Milne for the rational newform and good Hecke action. | error — inherited citation scope above |
| 1785–1787, 1825–1828: fix the based map and reuse the period scale. | OK — fixed-scale join used on the interior |
| 2937–2942: the cuspidal subgroup is finite and a fixed multiplier kills its image. | unverified — retained in the cusp work |
| 2943–2946: Atkin–Lehner acts by the eigenvalue up to the based translation. | gap filled on the interior complex chart (c); rational-model descent remains |
| 8468–8474: identify the supersingular pairs with ideal classes. | error — inherited level-one citation scope above |
| 8476–8479: extend and specialize at the good prime. | unverified — isolated in `BasedSpecialization` |
| 8487–8489: subtract the two translated values, using the same eigenvalue. | gap filled — the based identity specializes given the two comparisons (c) |
| 8505–8507: use the Atkin–Lehner sign in the parity of the local character. | gap filled — supply the newform unit to the existing parity constructor (c) |
| 9331–9341: the normalizer reads the same sign on the weight and on the parametrization. | gap filled for the sign pin (c); coarse reduction and cusp annihilation remain |
| 9372–9398: compare at the fixed precision and phase. | unverified — exactly the remaining `ha` reading |

All six modules passed `lake build` with a single Lean process in the
60 GB scope. The 22 theorem and definition audits report only
`propext`, `Classical.choice`, and `Quot.sound`.
