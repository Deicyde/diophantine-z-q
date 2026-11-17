# Actual checks for the prime-Hecke proof attempt

Base: `27657ffb10fd6706595d384eb412cfe5d091427d`.
Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Commands actually run

With `LEAN_NUM_THREADS=2` and the pinned toolchain:

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.NegOne:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.SmallLevels:olean
lake --no-cache env lean HeckeProofAudit.lean
```

All final commands exited 0. Pinned Mathlib compiled artifacts came from its
cache; the project/Tau Ceti contribution dependencies were built locally.
This is not claimed as an independent cold replay of every imported kernel
constant or as a full-project verification.

The local audit imports `SmallLevels` and prints axioms for all 12 public
contribution theorems, then checks the two main partial exports' types.
To reproduce that audit, save this as `HeckeProofAudit.lean` at the checkout
root and run the last command above:

```lean
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.SmallLevels

#print axioms ZInQ.Contrib.HeckePrimeRationality.rational_coeff_off_prime_multiples
#print axioms ZInQ.Contrib.HeckePrimeRationality.diamond_prime_eq_self_of_unit_eq_one
#print axioms ZInQ.Contrib.HeckePrimeRationality.rational_hecke_of_unit_eq_one
#print axioms ZInQ.Contrib.HeckePrimeRationality.rational_hecke_of_prime_eq_one
#print axioms ZInQ.Contrib.HeckePrimeRationality.rational_hecke_level_one
#print axioms ZInQ.Contrib.HeckePrimeRationality.rational_diamond_coeff_of_unit_eq_neg_one
#print axioms ZInQ.Contrib.HeckePrimeRationality.rational_hecke_of_unit_eq_neg_one
#print axioms ZInQ.Contrib.HeckePrimeRationality.rational_hecke_of_prime_eq_neg_one
#print axioms ZInQ.Contrib.HeckePrimeRationality.rational_hecke_of_prime_sign_class
#print axioms ZInQ.Contrib.HeckePrimeRationality.units_sign_of_small_level
#print axioms ZInQ.Contrib.HeckePrimeRationality.rational_hecke_of_units_sign
#print axioms ZInQ.Contrib.HeckePrimeRationality.rational_hecke_small_levels

#check ZInQ.Contrib.HeckePrimeRationality.rational_hecke_small_levels
#check ZInQ.Contrib.HeckePrimeRationality.rational_hecke_of_prime_sign_class
```

Every reported transitive closure is exactly within
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` was reported.
The four private concrete unit decisions are covered transitively through
the public small-level classification theorem.

## Failed attempts retained in the verification record

- The first identity-class module compiled without a proof repair.
- The first `NegOne` build failed at the scalar-coercion rewrite. Adding
  `FunLike.coe_smul` exposes the scalar action on the underlying function
  before `ModularForm.qExpansion_smul`; no statement changed.
- The first `SmallLevels` build failed because a kernel decision in the
  variable-dependent context retained free variables. Four closed private
  concrete decisions were moved before the variable block and then applied
  after substituting N. No `native_decide` or kernel bypass was used.

Deprecation and unused-section-variable warnings remain. No warning was
presented as an error or hidden by changing a theorem's mathematical scope.

## Final checked source hashes

- `HeckePrimeRationality.lean`:
  `f472b89258b1514e4ea81d2b163181f9513a6d7ce140604afc5a8ae708a7940f`
- `HeckePrimeRationality/NegOne.lean`:
  `3d3b6c733206693af5374ed035fa73b96e4f2fb8425caeae91570a71fff32ff6`
- `HeckePrimeRationality/SmallLevels.lean`:
  `dc241ba4964409ad7209aee2155a485410c0bede7aace3c285943c9d577f5218`

## Independent review and remaining proof obligation

A separate mathematical source reviewer checked the exact operator,
coefficient map, casts, residue conditions, all-level off-multiple fragment,
negative-identity action and final closed finite-check context. That source
review is not an independent native replay certificate.

The full `CoeffRational.HeckePrimeIntegralToRational` definition is unchanged
and **not proved by this contribution**. The remaining argument must establish
rationality of the actual non-sign diamond coefficients on integral-input
forms without assuming the general diamond/Hecke preservation leaf circularly.
No hypothesis has been removed from the final single-proof assembly. No PR,
merge or project-completion claim is made.

## Current analytic checkpoint: 51 public declarations

Three further exact proof modules have now been compiled and independently
source-reviewed. The earlier 12 theorem bodies and hashes above are unchanged.
The full all-level rationality leaf is still open.

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RealCoefficients:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveNonvanishing:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.SharpLevelFiveBound:olean
```

The final parent build and combined 51-declaration axiom audit exited 0.
The audit enumerates every public theorem/lemma in the six proof modules and
prints its transitive axioms: all remain within the standard trio, with no
`sorryAx`. It also proves literal examples using root-qualified Mathlib types
and the actual theta function, so wrapper aliases cannot weaken the two targets.
The exact audit script and output are retained in the verification packet.

- `RealCoefficients.lean`: 5363 bytes,
  `635ee91a2e5f4a029e11ee031b8c3c9961675bd72f532dd733389ed453a910f9`.
  Five public theorems prove all-level conjugation commutation and real
  coefficient preservation, not rationality. A beta reduction was needed
  before the q-expansion rewrite; the statements were unchanged.
- `ThetaFiveNonvanishing.lean`: 19355 bytes,
  `01f91286f5ffc718277553c8a199d188b92fab2e5cd697cfb3a9400d9e07ba3e`.
  Twenty-three public theorem declarations, including the exact global
  5-torsion nonvanishing target, with no product/zero-set assumption.
- `SharpLevelFiveBound.lean`: 7720 bytes,
  `af8523a8748fe1f8b2a69d75b90ff5ecd298ff3f904bb220af562440ccf93d58`.
  Eleven public lemma/theorem declarations, including truncation injectivity
  through the weight at level five. No basis/dimension/rationality premise.

For concise independent target checks, use:

```lean
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveNonvanishing
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.SharpLevelFiveBound

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped UpperHalfPlane MatrixGroups

example (tau : UpperHalfPlane) (a b : Int) (h : ¬ (5 ∣ a ∧ 5 ∣ b)) :
    _root_.jacobiTheta₂
      (((a : Complex) * (tau : Complex) + (b : Complex)) / 5 + ((tau : Complex) + 1) / 2)
      (tau : Complex) ≠ 0 :=
  ZInQ.Contrib.HeckePrimeRationality.ThetaFive.jacobiTheta₂_fiveTorsion_ne_zero tau a b h

example (k : Int) (hk : 0 ≤ k)
    (f : _root_.ModularForm
      ((CongruenceSubgroup.Gamma1 5).map (Matrix.SpecialLinearGroup.mapGL Real)) k)
    (h : ∀ n : Nat, n ≤ k.toNat → (_root_.UpperHalfPlane.qExpansion 1 f).coeff n = 0) :
    f = 0 :=
  CoeffRational.SharpLevelFiveBound.eq_zero_of_coeff_eq_zero k hk f h

#print axioms ZInQ.Contrib.HeckePrimeRationality.ThetaFive.jacobiTheta₂_fiveTorsion_ne_zero
#print axioms CoeffRational.SharpLevelFiveBound.eq_zero_of_coeff_eq_zero
```

The plain-file module-system warnings remain; they are warnings, not errors.
No source header/body was churned merely to suppress them. Ordinary compiler
checking and separate source review are not a cold native replay certificate.
These earlier helpers did not supply the weight-one forms or their coefficient
descent. The later checkpoint below constructs those and proves the level-five
contract. The all-level hypothesis in the final single-proof assembly remains
undischarged.

## Closed level-five endpoint

The actual weight-one forms, coefficient arithmetic, fifth cyclotomic field,
normalized rational generators and power-basis action are now proved. The
conditional algebraic helper is bound to those concrete proof objects in
`LevelFive.lean`; no generator, basis, Galois or rationality premise survives.

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.LevelFive:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.LowLevels:olean
lake --no-cache env lean LevelFiveEndpointAudit.lean
```

All final commands exited 0. The endpoint audit checks this literal original
contract specialized at N = 5, using root-qualified types and operators:

```lean
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.LevelFive

example (k : Int) (p : Nat)
    (g : _root_.CuspForm
      ((_root_.CongruenceSubgroup.Gamma1 5).map (_root_.Matrix.SpecialLinearGroup.mapGL Real)) k)
    (hk : 2 ≤ k) (hp : p.Prime) (hgood : ¬ p ∣ 5)
    (hg : ∀ m : Nat, ∃ z : Int,
      (_root_.UpperHalfPlane.qExpansion 1 g).coeff m = (z : Complex)) :
    ∀ m : Nat, ∃ q : Rat,
      (_root_.UpperHalfPlane.qExpansion 1
        (_root_.HeckeRing.GL2.heckeSlashGamma1CuspFormEnd k
          (_root_.HeckeRing.GL2.diagCosetGamma1 5 p) g)).coeff m = (q : Complex) :=
  ZInQ.Contrib.HeckePrimeRationality.LevelFive.integral_input_hecke_rational k p g hk hp hgood hg

#print axioms ZInQ.Contrib.HeckePrimeRationality.LevelFive.integral_input_hecke_rational
```

The full endpoint axiom closure is `[propext, Classical.choice, Quot.sound]`.
The complete supporting module audits also remain within this standard trio;
no `sorryAx` was reported. Separate source review checked the actual generator
construction, Galois-fixed coefficient argument, integer diamond matrix and
all endpoint binders, not merely the conditional helper.

Current additional source hashes:

- `ThetaFiveTorsionDefinitions.lean`:
  `1cc7d8168ba13be52660e079dc081f6f33a292e151a2410a0d5fe17b6d4fbbeb`
- `ThetaFiveTorsionForms.lean`:
  `fd20716f2e20c5f718d43a9f6e429bb3e050d998421faa30d05b79b685ffbef7`
- `ThetaFiveTorsionCoefficients.lean`:
  `75726aa34563f24de2e08891e0c7312cbbc2367e4b2f64af247fb1d895479396`
- `ThetaFiveCyclotomicField.lean`:
  `f9b19d85085aa6af6349e10bb61847ac4d2ab8a218c1aa201d0a37c069204d17`
- `ThetaFivePowerBasis.lean`:
  `10e6c156f24423a961dfb3d8b8b1ae1972272e7de70e155b8b5f6c44a06f7a0c`
- `ThetaFiveNormalizedGenerators.lean`:
  `29316c9702ce801a311425f0ff8ef1d97a29eb7ffd7f943df64138e283e897f8`
- `ThetaFiveRationalGenerators.lean`:
  `740ffccaa69477bf8f76b08f12ab4129199b52eee77254bfa130eabea1de6b0e`
- `ThetaFiveDiamondFromBasis.lean`:
  `cb2c8c5f731cd9aba66a6675a97f871b0012511dd7f6b6fe86c3f6deee6c2531`
- `LevelFive.lean`:
  `047bfbcabaffece34a8e73eae1e56c2067af35370cafa5deed2f0a07f7b2e45e`
- `LowLevels.lean`:
  `944886d247918369dd1c45369c512a7a32af71b452299484e4095684e80b2ceb`

The earlier six proof modules and their reported hashes are unchanged.
Compiler repairs in the new normalized-generator module supplied the correct
field-denominator nonzero facts, exact polynomial multipliers, and an explicit
Gamma0 membership proof; no target statement was weakened. Failed attempts
are retained in the private verification record.

`LowLevels.lean` combines the level-five theorem with the earlier sign cases
and exposes only the extra bound N ≤ 6. It does not discharge any level N ≥ 7.
The original all-level target, final assembly and other global obligations
remain unchanged. No PR, merge, landing or full Z-in-Q claim is made.

## Arbitrary-level foundation checkpoint

The new mathematical source covers actual positive-level theta functions,
actual principal and Gamma-one forms, coefficient arithmetic for all integer
labels, exact period conversion, the explicit invariant projector, all-row
field-coordinate descent, finite-family conjugation and homogeneous torsion
products. The zero-label module proves counterexamples to naive raw
all-torsion distribution; it does not prove trace closure.

All 33 mathematical modules were co-imported successfully. The complete audit
prints transitive axioms for all 465 named public proof/instance declarations
and eight actual constructions: the old torsion form and normalized A/B,
the arbitrary-level Gamma-one and principal forms, average, linear average,
and product form. All 473 records contain at most `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` is present. The earlier
N ≤ 6 original-contract source and hashes remain unchanged.

The reusable audit is `HeckePrimeRationality/Audit.lean`. Its literal checks
use the actual functions and root-qualified types. Commands include:

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionProducts:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTraceTwoZeroConvention:olean
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/Audit.lean
```

Component audits additionally check the literal infinite-row linear system,
actual coefficient-coordinate equality, arbitrary integer labels, exact
period-N versus period-one index N·m, actual averaging formula and projection,
and finite-family coefficient-conjugate form. Every final component build and
audit exited 0. Raw type printing confirms that the generic automorphism is
an actual `AlgEquiv Rat K K`; its notation does not introduce an extension
hypothesis. The generic rational-fixedness lemma proves rational implies
fixed, not the converse without Galois/fixed-field data.

Every new module received separate complete mathematical source review. That
review is not an independent cold imported-proof replay. Warm pinned inputs
are still used. The partial sources are not a full-project verification or
a proof of any unrestricted principal spanning theorem.

The following new source hashes identify the exact verified editions:

- `AllLevelTorsionDefinitions.lean`:
  `850b9acd85deab1b3aca2175649ce4268715973a27fdc4fe49b9549f5789a8ff`
- `AllLevelThetaNonvanishing.lean`:
  `51a28fb390750a289b95f116bfd7617a199ebb8b7521b56c838ae0ae2a496338`
- `AllLevelTorsionCoefficients.lean`:
  `22ae0a2347052f1df7237157dffc9005d224b15126a81866c49ace17f37b8bec`
- `AllLevelTorsionForms.lean`:
  `06523780031c9971e7126adddcdf66af7b0820fcca62fbb99138ccd77f9340e4`
- `AllLevelPrincipalForms.lean`:
  `682f23c519b6b9bd134c9e6d18a70824698774bdd81dbf8ab892cf2ae1d6ef93`
- `FiniteLinearDescent.lean`:
  `ce13a992c5950ddb649c56fc883018c5445cfc8e92e0770520fcb00ad5642c8f`
- `AllLevelTorsionData.lean`:
  `9cb39f2ea08a4d2b374a7d56400dde19e2ce80990c1b42813562affd9646f647`
- `AllLevelPrincipalCoefficients.lean`:
  `cd17a0dd46cc0c47255d9901eb844245e11884e635382d1aae680ee14af26573`
- `CoefficientCoordinates.lean`:
  `42722aa5e6278d5e7300fb8553ed1442aee1fb133e62a3c876cb17d0d83d3c77`
- `AllLevelPeriodConversion.lean`:
  `dcfdac8e6990c1924e109c2074362791e9e24dd935a9ba481df0c49f93ade257`
- `AllLevelIntegerRows.lean`:
  `7a063160a08f90a8741eee073fbd261a547417f5d20a5d09386b3245faddef7f`
- `AllLevelUnipotentAverage.lean`:
  `76aafc214c3ff4da0d5d87042c796813fc58cced3b22c0122501f9a383246c11`
- `AllLevelAverageLinear.lean`:
  `7f63cc299ca14cee113128eb20d26d75d02937e734705d7f919bb935d203d65b`
- `CoefficientConjugation.lean`:
  `9737eabc1442a84fdaf716a060d5e1d3af7c390c0cdde12ee891919bc3eaafad`
- `AllLevelTorsionProductBase.lean`:
  `c695ab7d264f3fcf4750a023252c8f9123667bc96163540b4a8202cc329059b0`
- `AllLevelTorsionProducts.lean`:
  `9c96307eb838cfc69b4c0b56b259e3e8be69a73300bb87a6761b21675c0226da`
- `AllLevelTraceTwoZeroConvention.lean`:
  `a169f851c4f31e38760cb863e8bb6a7b459b01cbbc6a44f15a0237feae684810`

The full original all-level leaf is still open. Its missing producer is
principal Eisenstein-product spanning bound to the actual theta family,
with concrete invariant-space descent. No explicit spanning or conjugate
family input of a generic helper has been removed by assertion. No global
premise in the final assembly has changed.

## Completed-theta extension: current 34-module audit

`AllLevelCompletedTheta.lean` additionally constructs the actual entire odd
theta H, its derivative Hder, joint holomorphy on the positive-imaginary
parameter domain, quasi-periods, oddness, and the exact Good-torsion
logarithmic-derivative expression. The global zero set, simple zeros,
multiplication, distribution and Eisenstein spanning are not supplied by
this module.

Source: 159 lines, 7241 bytes, SHA256
`821acb910d89b27902a119aa2e3132b1444b20f76be161ea2f5f7cb32d561b15`.

The parent build and literal actual derivative/torsion-formula audit exited 0.
The complete `Audit.lean` now co-imports all 34 mathematical source modules
and audits all 479 public proofs/instances plus the earlier eight actual
constructions and H/Hder. All 489 records remain within the standard trio;
no `sorryAx` is present. The full source review checked the exact derivative,
positive-imaginary domain, quasi-period signs, and the absorbed 1/2 term.

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelCompletedTheta:olean
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/Audit.lean
```

Exact audit source SHA256:
`cc330b4f00a57098f6d2cdf7f884ca1ccd3211cbeba8dc7224204ec52c6aeee0`.

The previous 33 mathematical source editions are unchanged. Current results
remain ordinary pinned compilation and separate complete source review with
warm imports, not independent cold replay or original all-level completion.
The unconditional original Hecke contract is still proved here only for
N ≤ 6, with its level bound visible.

## Analytic-producer and exact-reduction checkpoint: 49 modules

The next additive checkpoint preserves every previously published mathematical
source. It adds the actual global theta zero set and simple origin zero,
all-positive-degree multiplication, the two-division raw and zero-extended
distribution identities, the actual Weierstrass normalization, and direct
completed-theta Frobenius–Stickelberger addition.

The actual finite-product diamond descent and guarded prime-Hecke consequence
are also proved, with their representation hypothesis explicit.
`UnrestrictedReduction.lean` binds this to the exact original
`CoeffRational.HeckePrimeIntegralToRational`, including arbitrary integer
weights and all levels, **conditional on the unproved
`PrincipalProductSpanning` property**. Naming and auditing this predicate's
definition do not prove it; no original assembly hypothesis is discharged.

All 49 mathematical modules co-import successfully. `AnalyticAudit.lean`
audits every one of their 660 named public proofs/instances and 40 selected
definitions. All 700 records have at most `propext`, `Classical.choice`,
`Quot.sound`, with no `sorryAx`. Definition audits include auxiliary
predicates; they are code-binding checks, not proofs that those predicates
hold. The earlier 34-module `Audit.lean` and its history are retained.

Each added module was compiled at the pinned toolchain and received complete
independent source review. Component literal checks preserve the actual
Jacobi-theta functions, actual Mathlib `PeriodPair.weierstrassP`, actual
cusp forms/operators, and the original unrestricted leaf's quantifiers.
The only repairs to two parent audit scripts corrected a namespace and
literal-expression whitespace; mathematical sources were unchanged. The
new cusp-form helper's initial rewrite was specialized to its unit and
coefficient before applying the same coercion lemma; its hypotheses and
conclusion were unchanged. Earlier failed logs are retained.

To reproduce the complete added checkpoint audit:

```sh
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/AnalyticAudit.lean
```

Exact audit source SHA256:
`70b06cc03699d77889678ea4e867e6987b8ab815a0f026b24bd642b13d73d7d3`.

Exact added mathematical source editions:

- `KnownFieldCoefficientCoordinates.lean`:
  `d17f5248ef1b4c70ed0055079706771d712975359770f326d1bb645317b78f10`
- `DiamondProductFrames.lean`:
  `7f025477b81e6a6472e19e6bee0f77207f245a68ee5f74d0aa6620b8e03ae618`
- `AllLevelDiamondFromProducts.lean`:
  `3ddd3ca49008b242c180ed87f6e18d73b8872fd18afdaad0b96a016e95c25911`
- `AllLevelThetaZeroSet.lean`:
  `09f41030a9e671fcb479ba2a2f80f1c8ad8a1dbcaedd0b9b016b83a0f7f672bf`
- `QuasiThetaMultiplicationTwo.lean`:
  `d20fc400beaf610513db7516298f517dace95ddb391e7ee7ec1c97b472117f12`
- `AllLevelThetaMultiplicationTwo.lean`:
  `ac3e99876bd469e406b1897322fe99857f20dede45d53c3840171d3c962350bb`
- `AllLevelHeckeFromProducts.lean`:
  `f8aea7a17252666b23386673b75092728b2566bfb9048e9ea5238b7f2d384ecb`
- `UnrestrictedReduction.lean`:
  `db378bbe0b442ff377f432331940831072336d022c72e88c530a24b693411970`
- `AllLevelTorsionDistributionTwo.lean`:
  `770cc9de53281f47d75c30d1c90d18a1ffdd0f32902063dfac8d7952e145a98c`
- `AllLevelTorsionDistributionTwoRegular.lean`:
  `6d1a963081030febb9c89e6a95e780328943559ee1d48f4fa89c64f1a9873a18`
- `AllLevelThetaWeierstrass.lean`:
  `9798fdb2a87a96686c221e3b22934ce4bc6811e1c80d58b082c616cb02d7c903`
- `QuasiThetaMultiplicationNat.lean`:
  `f9effec81c2aa027bb28d6aca00731341319d8500bb952c8ad5a079ac28b1427`
- `AllLevelThetaMultiplicationNat.lean`:
  `07129e1ab95051af3e53d26004605b5c3754bbc1db2bd7a03fc811dc4574505d`
- `AllLevelThetaAdditionLocal.lean`:
  `974b5d49790a5dde33c8965e7b2a8b98192b6caed657694e21c88ae27b735ab1`
- `AllLevelThetaAddition.lean`:
  `bafc6b7fc7615821fd70938c2a4d8753ee535c681ff0fedd537560ca7989b901`

This checkpoint still does not prove principal Eisenstein-product spanning,
full torsion Fourier duality, the genuine Eisenstein identification of the
quadratic defect, low-weight trace closure, or the unrestricted Hecke leaf.
Warm imports and separate source review are not an independent cold replay
or full-project acceptance. N ≤ 6 remains the unconditional original-contract
extent; the all-level result is a conditional reduction, not completion.

## Actual distribution, Fourier and quadratic checkpoint: 56 modules

Seven further modules provide the actual torsion Fourier kernel and global
comparison, general-degree raw and zero-extended distribution, a shared
actual Weierstrass torsion-value convention, all-degree x-distribution, and
the concrete torsion quadratic-addition relation. All previously published
49 mathematical source editions and both historical audits are preserved.

The full `WeightTwoAudit.lean` co-imports all 56 mathematical modules. It
checks all 769 named public proofs/instances and 56 selected definitions or
constructions. All 825 records contain at most `propext`, `Classical.choice`,
`Quot.sound`, with no `sorryAx`. A definition audit is not proof of the defined
predicate or its mathematical identification: `PrincipalProductSpanning`
remains explicitly unproved, and the quadratic value's Eisenstein membership
is not established by defining it.

Every new mathematical module was compiled and independently source-reviewed
in full. Literal component audits check:

- actual zero-extended Fourier duality for every positive N and every integer
  label, with factor −1/N and pairing exponent `br−as`;
- raw distribution at admissible images and zero-extended distribution at
  arbitrary images, for every positive degree and level;
- actual Mathlib Weierstrass x-distribution at every integer label, with n²
  scaling and the zero convention; and the vanishing sum over nonzero
  n-torsion, without any individual-value vanishing claim;
- actual torsion Frobenius–Stickelberger and the equivalent quadratic-addition
  relation at three admissible labels. The first-coordinate completions and
  the proven identical finite-part constants are explicitly connected.

The Fourier proof uses a genuine derivative-defined removable quotient and
an independently proved common entire numerator. Residues cancel at every
candidate pole through finite character orthogonality; constancy and its
zero value are proved, not assumed. It contains no conditional infinite-sum
interchange or Fourier-defined torsion family.

The x-distribution differentiates on a common zero-free neighborhood. Its
bad-image case comes from cancellation of the actual Weierstrass double
poles and normalized finite parts, not from treating an even function as
odd. The quadratic relation is an algebraic restatement of the genuine
analytic addition theorem; it does not assert that the resulting defect is
Eisenstein. All three admissibility hypotheses are essential and visible.

Commands at the same pinned toolchain include:

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionFourierComparison:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDistributionNatRegular:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelWeierstrassDistributionNat:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticAddition:olean
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/WeightTwoAudit.lean
```

All final builds and audits exited 0. Exact complete audit SHA256:
`d0762aaf5623b43286295935ae57eb1b91584395defb132d6b30d94b8b0106a0`.

Exact new source editions:

- `AllLevelTorsionFourierKernel.lean`:
  `469560fbd136fd4de025b5e5f5d5e4347d63ff49a45d1dbb49a9d8c881e50ba0`
- `AllLevelTorsionFourierComparison.lean`:
  `eaa8729e3b4a621491f2c35e86a5e2955df6adc098bdc304be22ba9c393b0a1f`
- `AllLevelTorsionDistributionNat.lean`:
  `e91830e4baa8affdd41c43abb02c8164575cab021bef8e4b8746fac0785fb92d`
- `AllLevelTorsionDistributionNatRegular.lean`:
  `c7219a6e35b250eb96cc47e5bca6e08d525c135950cd114fdcd937b9346d8ced`
- `TorsionWeierstrassData.lean`:
  `4561ad592f0f466df3e610d0dde8aa0383fdc0478463b2e073e42091e1ea30de`
- `AllLevelWeierstrassDistributionNat.lean`:
  `fc4fef9595b749b0701c68692f1f6dfd144eaaf31836dff1a69af6cd839de3ec`
- `TorsionQuadraticAddition.lean`:
  `6f3587fe8511d9be8a58a12230f36bd975befb8ddcd4f8001947eab84cfaba06`

The concrete values are functions of the actual completed theta and
Weierstrass constructions with explicit zero conventions. Naming the
quadratic value μ does not itself identify it with a genuine Eisenstein
series. The μ/x Fourier identities, that Eisenstein identification,
low-weight trace closure and principal product spanning remain unproved
in this checkpoint. Thus the original unrestricted Hecke leaf remains OPEN;
N ≤ 6 remains the unconditional original-contract extent. No original
hypothesis, dependency pin, assembly or public proof history is altered.

These are ordinary pinned compilations with disclosed warm imports and
complete independent source reviews, not independent cold replay of every
imported proof or a full-project acceptance certificate.

## Actual theta constant and complete label cases: 59 modules

The new two-file identity proves that the actual theta finite-part constant
is exactly `−EisensteinSeries.G2 τ`, with no caller-supplied identification,
triple-product, holomorphy, boundedness or vanishing premise. The first file
proves its S/T transformation and invariance of `finitePart + G2`. The second
justifies termwise higher theta derivatives and holomorphy on open parameter
strips, proves a genuine large-height lower bound on the denominator, and
constructs an actual level-one weight-two modular form with every field
proved. Mathlib's exact weight-two rank-zero theorem then makes that form
zero. The third-derivative expression is also bound explicitly to actual
Jacobi-theta functions in the parent literal audit.

This is an identification of the single constant, not proof that torsion
quadratic values belong to an Eisenstein space. It does not prove the μ/x
Fourier identities, trace closure or principal spanning.

A separate new module states every label case of the actual quadratic
defect. The all-Good branch uses the previously proved addition identity;
zero-class branches retain the true negative-square terms. Expressing
those squares as `x + 2μ` uses the existing definition of μ, not new analytic
or Eisenstein content. The zero/opposite-label cases are checked literally.
The first rejected source edition needed retained divisibility witnesses and
a definitional scalar equality; only that unproved edition was repaired,
with all theorem statements unchanged. Published mathematical source was
not rewritten.

The complete `ThetaConstantAudit.lean` co-imports all 59 mathematical source
modules. It audits all 817 named public proofs/instances and 66 selected
definitions or constructions: all 883 records use at most `propext`,
`Classical.choice`, `Quot.sound`, and no `sorryAx`. Definition audits remain
code-binding checks, not proofs of the defined spanning predicate.
The older three audit editions and all 56 previous mathematical source
editions are preserved byte-for-byte.

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaG2Identity:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticCases:olean
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/ThetaConstantAudit.lean
```

All final parent builds, full declaration audits and literal contracts
exited 0. Complete independent source reviews read all 657 lines of the
G2 pair and all 112 lines of the final case module, plus their exact
load-bearing callees. These are ordinary pinned compilations and source
reviews with warm imports, not independent cold replay.

Exact new source editions:

- `AllLevelThetaG2.lean`:
  `17c9dcfc32bb9c7551e8815e1b98e2fd01010688bc4dbaaaa105a30e239df69e`
- `AllLevelThetaG2Identity.lean`:
  `8d213342f55728db64438d50e0e5158386bf8ee0ce2e7caad8850b7910836a1d`
- `TorsionQuadraticCases.lean`:
  `6ebe9dea13a5f04b3594817e0060fe7112977820009a08312cb1a1eeee5b4522`

Exact complete audit SHA256:
`40b6c6630885df39e7d9706522a92c86957c588ba0880814f78a813477983dc7`.

`PrincipalProductSpanning` and the original unrestricted Hecke leaf remain
OPEN. No original global hypothesis, pin or assembly has changed; the
unconditional original-contract extent remains nonzero N ≤ 6.
