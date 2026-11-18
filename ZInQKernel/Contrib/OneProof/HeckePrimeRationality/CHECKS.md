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

## Actual Fourier, Eisenstein and correlation checkpoint: 71 modules

Twelve additive mathematical modules preserve every earlier 59-module
source edition and all four historical audits. They prove:

- the actual μ/x Fourier dualities for every positive level and all integer
  labels, with factors −1 and −1/N² and pairing `br−as`;
- all-degree μ distribution with factor 1 and the frozen zero convention,
  through a genuine enumeration of the surviving divisible frequencies;
- actual principal-level x, λ and μ modular forms of weights 2, 1 and 2,
  with every field proved for all positive N, including N=1 and N=2;
- independently defined weight-two congruence-difference and principal-lift
  Eisenstein lattice series, with absolute differences, ordinarily summable
  rows, exact WP/G2 normalization, actual modular-form fields and equality
  to x-values at every label;
- explicit quadratic generator inclusion of actual x- and μ-forms in the
  complex span of genuine Good degree-two principal torsion products at
  the same level, under the visible N ≥ 3 guard;
- actual finite-correlation recurrence and its zero-slope base, a genuine
  embedded torsion-kernel enumeration, representative independence,
  injective ambient enlargement, constructed larger-level preimages, slope
  reduction and a terminating Euclidean expansion retaining every defect.

Parent builds, complete new-declaration audits and literal contracts all
exited 0. Literal checks use actual data, root-qualified modular-form groups,
actual lattice summands and the precise factors and level guards. Separate
complete source reviews checked all added source and load-bearing callees.
These are ordinary pinned compilations with warm imports, not independent
cold replay of every imported constant or full-project acceptance.

`FourierCorrelationAudit.lean` co-imports all 71 mathematical modules and
checks all 1001 named public proof/instance declarations and 108 selected
definitions, constructions or type aliases. All 1109 records have at most
`propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. A definition
or span audit does not prove that the defined predicate holds or that the
span is the entire modular-form space.

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionMuFourierFinite:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionWeierstrassForms:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelEisensteinWeightTwoBounds:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionMuDistributionNat:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticGeneratorSpan:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationEnlarge:olean
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/FourierCorrelationAudit.lean
```

Exact new mathematical source editions:

- `AllLevelTorsionCorrelation.lean`:
  `8ad203b3d75f6701616e40f44b6470800d41b78b1ab1ed1e0ce88e8b40586c64`
- `AllLevelTorsionMuFourierKernel.lean`:
  `f95c400fb1b2dc5127d3af20a0ee3ec79bda0c79fd9640a1ad445b6e4466bf53`
- `AllLevelTorsionMuFourierLaurent.lean`:
  `6a2d43b59d1204e3e77c952e2058acdae1b2c5b159552ac541ee9815ab4afd03`
- `AllLevelTorsionMuFourier.lean`:
  `b13a747f2e81097308f438907504295544e048478a5b798b4f6951117d839fcf`
- `AllLevelTorsionMuFourierFinite.lean`:
  `848c32ac0322257bb48f3a14c1a4f59e2057d2143d813f7ec2409598b175ba83`
- `TorsionWeierstrassForms.lean`:
  `c47ed79aa9bc5e96077aa3a6c7a3fc210a81c1abe43bac6860f4dc0194abd00c`
- `AllLevelEisensteinWeightTwo.lean`:
  `640ce251ed8fe73955903e54d1ce7422c905ccd235d9f8c518f60095e71faa63`
- `AllLevelEisensteinWeightTwoBounds.lean`:
  `badc7fe02c7cb47a7e0acf694de5636859f41632e7dcba1cdb63d6fe717e876a`
- `AllLevelTorsionMuDistributionNat.lean`:
  `9a46bd20019b6f2434ccb0c942ac0e06ca02b32a596b2cbab858c2f0085b2fac`
- `TorsionQuadraticGenerators.lean`:
  `3c210441bae49c36d1d40be7b5049fe915d89303b3c847f44712c2fda8bd53b7`
- `TorsionQuadraticGeneratorSpan.lean`:
  `451ab574d54634ce508ea1a128ccdd21869f642747b07d493ec970ef0e727ddd`
- `AllLevelTorsionCorrelationEnlarge.lean`:
  `b2db13e4aa570a6f5601cc609fd9ee9c14e59a4f56fa9d5cc689b4e03e8b7719`

Exact complete audit SHA256:
`e8b54bc9ca3e5659d2215c812a68f68841d7e1fa98b86677afeb67f79a1644bb`.

The x/Eisenstein identification is in the convergent series sense; it is not
Petersson-subspace membership, trace closure or whole-space spanning. The
same-level quadratic generator formula excludes N=2. The enlarged Euclidean
expansion records multiplicatively growing ambient levels and leaves every
D-correction explicit; original-level integer row constraints, label descent
and correction identification are not supplied by that expansion.

The μ/defect bindings to the independent series span, Eisenstein level
descent, original-level product-row constraints, low-weight trace closure and
principal spanning remain separate proof obligations. No original assembly
hypothesis has been discharged. The unrestricted Hecke leaf and full Z-in-Q
theorem remain unproved, and the unconditional original extent remains N ≤ 6.

## Actual all-label series-span and correlation binding: 73 modules

Two further mathematical modules preserve all 71 earlier mathematical
editions and five historical audits. `divisionSpan` is defined from the
range of the independently convergent series-defined `divisionEisensteinMF`,
not from x, μ, D or the entire modular-form space. Explicit form equalities
prove that actual x and μ belong to that span; λ² enters by `x + 2μ`.

The actual quadratic-defect form is built from three genuine λ products.
All label cases are proved: bad left/right/sum retain negative squares;
the three-μ expression is reached only with three Good classes. Every case
then has proved series-span membership, including the explicit N=1 zero form.

The square of the common scale κ=−2πi is proved nonzero. Dividing the actual
quadratic form by κ² gives exactly raw `TorsionCorrelation.D` on canonical
ambient labels. The finite defect sums and factor-1/s correction are genuine
modular forms in the same ambient-level series span. The correlation
recurrence retains `0 < M,n,s`, `n ∣ M`, `s ∣ M` and `s • B′ = B` unchanged.
No defect is silently discarded and no lower-level descent is assumed.

Both ordinary parent builds, all 37 new-declaration audits and literal
actual μ/D membership, raw-defect equality and degenerate-case contracts
exited 0. Complete independent source review read all 355 lines and the
exact previously reviewed callees. `SeriesMembershipAudit.lean` co-imports
all 73 modules and audits 1029 named public proofs/instances plus 117 selected
definitions, constructions or type aliases: all 1146 records have at most
`propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelDivisionSeriesCorrelation:olean
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/SeriesMembershipAudit.lean
```

Exact added source editions:

- `AllLevelDivisionSeriesMembership.lean`:
  `c442dff7675d35a6c7d4e194d147b7bbb576b3b54ed68eb1ad3a945f6500983e`
- `AllLevelDivisionSeriesCorrelation.lean`:
  `761194aea33475e279be2e873f90f371d0590a01665ea07f482da49b3f84eebd`

Exact complete audit SHA256:
`697133d58830ffae8aff784d03cd4b118b99563a08e9b925459c62f3f37aa80b`.

This is membership in a specific independently convergent series span, not
identification with a classical Petersson-Eisenstein subspace, level descent,
trace closure or a `⊤` statement about all modular forms. The remaining
original-level product-row constraints, level maps/trace closure and full
principal spanning are not proved here. The unrestricted original Hecke
leaf, its assembly hypothesis and full Z-in-Q remain unchanged and unproved;
N ≤ 6 remains the unconditional original-contract extent. Warm imported
proof closures and complete source review are not a cold replay certificate.

## Original-level rows and upward level maps: 78 modules

Five additive mathematical modules preserve all earlier 73 source editions
and six complete audits. The actual row producer gives finite original-M
products with integer determinant ±n, both congruences modulo n and
uncollected coefficients ±n. Both h-factors pull back by exact signed integer
quotients. The error is an explicit finite list of actual D-correction
records, never defined as C minus the product sum. Each record has a positive
level and genuine divisibility data. Its level divides (n−1)!M; for M=nℓ
that common bound is n!ℓ. Individual correction levels need not equal it.
The literal slope is natural, with n>0, M>0 and n∣M.

The level-map modules prove actual linear restriction along N∣M, injectivity,
exact series-generator images at labels (M/N)a, upward inclusion, composition
and finite weighted sums. Factorial inclusions are proved. The normalized
trace uses the actual finite relative index with nonvanishing proved, not a
normalization assumption. It is a left inverse on upward images and descends
scaled-generator combinations. The finite quotient orbit proves preservation
of the upper series span after restriction, not arbitrary lower-span closure.

All five parent mathematical builds and every final literal/axiom audit
exited 0. Complete source review covered all 388 row lines and all 395 level,
trace, orbit and factorial lines, with exact callees and the primary-paper
comparison. The earlier 385-line level-map total was a counting slip.
No mathematical source was edited to repair it.

`RowsAndLevelMapsAudit.lean` co-imports all 78 mathematical modules. It audits
1078 named public source proofs/instances, 138 selected source definitions,
structures or type aliases, and one additional ordinary capture of the
derived row decision instance: all 1217 records use at most `propext`,
`Classical.choice`, `Quot.sound`, with no `sorryAx`. The new five-file source
inventory is 49 proof bodies and 21 definitions/structures/aliases; the
derived instance is audited separately, not counted as 50 new public proofs.
The unsupported private `#print prefix` name probe was retained as a failed
diagnostic; it did not affect any mathematical build or source. No evaluation
or custom loader was used.

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationRows:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinTraceOrbit:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinFactorialLevels:olean
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/RowsAndLevelMapsAudit.lean
```

Exact added source editions:

- `AllLevelTorsionCorrelationRows.lean`:
  `c38e80db728977e24ddaffd9a6b1ab074afc750f7321d14ad1e5e278d99ab05f`
- `DivisionEisensteinLevelMaps.lean`:
  `60436850b64543e1daea72d8f5ec7fc5de4a4ea3b0995bb6ffcab1dcf0523ed9`
- `DivisionEisensteinFactorialLevels.lean`:
  `ec5dfde1a8818a65f2e455f23c94d417cdb00d03472121b3da8a9177052798be`
- `DivisionEisensteinTracePartial.lean`:
  `0c1d34073f3d6d3588301d6dfcb59428ed08a99b4f6cbe2a0188f41bc48e8b1f`
- `DivisionEisensteinTraceOrbit.lean`:
  `5f6f6f8a3d9bee62281f75e4ce211a997428e033780ed246fa8241196b691ef8`

Exact complete audit SHA256:
`9c463f89a05283580df062a104aa815dacd5057a398da0238b1ab62083cb8a26`.

Still separate: assembling the described finite corrections into one actual
series-span form at the canonical factorial level, signed-slope extension,
and arbitrary lower-level series-generator trace closure. Upward injectivity
and upper-span preservation do not establish that missing downward lemma.
No whole-space spanning or Petersson-subspace identification is claimed.
`PrincipalProductSpanning`, the unrestricted original Hecke leaf and the full
Z-in-Q theorem remain unproved by this work. The original-contract extent
remains nonzero N ≤ 6; no assembly hypothesis, pin or published proof edition
has been changed. These are pinned warm-import compilations and source
reviews, not a full cold/native acceptance certificate.

## Actual weight-three derivative, kernel and generators: 81 modules

Three additive mathematical sources preserve all previous 78 mathematical
editions and seven complete audits. y is the actual Mathlib Weierstrass
derivative at the actual torsion point, with a proved bad-class zero value,
not a Fourier-defined replacement. Its shifted inverse-cube lattice sum is
absolutely convergent, and the congruence-class equality has the exact factor
−2N³. Every reindexing is therefore applied to a convergent weight-three sum.

The actual kernel unit has ordinary analytic logarithmic jets. Differentiation
of a zero-free neighbourhood gives E‴(0)=N²(A+y), where A=λ³−3λx. The finite
character comparison is differentiated only after an ordinary germ equality;
it yields F(A+y)=−(3/N)y. The zero row follows from actual oddness and finite
reindexing, without assigning a residue to the zero kernel. Finite inversion
uses F²=N² id, giving y=(3N F(A)−N⁴A)/(N⁴−9). The denominator is proved nonzero
for every positive integer N, and negative labels use nonnegative Euclidean
remainders before conversion to naturals.

The actual yForm is a weight-three modular form on Γ(N), with evaluation to
Mathlib WP′ for all positive levels and integer labels. Bad labels and N=1
give the genuine zero form. For N≥3, actual multiplication and span induction
put yForm in the span of genuine Good degree-three principal torsion products
at the same level. The scale is absorbed over complex scalars only; no
coefficient-field rationality or whole-space spanning follows.

All three parent source builds, all 59 new-declaration audits and literal
actual derivative/series/third jet/negative and zero labels/generator checks
exited 0. Complete independent source review read every one of the 930 added
lines and the exact load-bearing callees. `WeightThreeAudit.lean` co-imports
all 81 mathematical modules: 1129 named public source proofs/instances,
146 selected definitions/structures/aliases and one derived row-instance
capture, all 1276 records within `propext`, `Classical.choice`, `Quot.sound`,
with no `sorryAx`.

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionWeightThreeForms:olean
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/WeightThreeAudit.lean
```

Exact added source editions:

- `AllLevelTorsionWeightThree.lean`:
  `73915c752499ff7ad8f5123bbaa47f6dddf6b480b516c7f0c4aca5634ba5c456`
- `AllLevelTorsionWeightThreeFourier.lean`:
  `3bbcb8f603ec51a73fb28ab2a7503b845894338a22709a0b67d56dea2d80729b`
- `AllLevelTorsionWeightThreeForms.lean`:
  `74dd4e08cac2220e7eddf453213a7248b3a58aa8a2f1ee12eee78461550fb063`

Exact complete audit SHA256:
`f401b6597749b7fa4e75d6e07397da10a2bb42aca8a834d722832ae8c2838563`.

This is same-level generator inclusion, not a span of the entire weight-three
space, a Petersson-subspace identification, trace closure or principal product
spanning. The canonical correction-form binding, signed-slope extension,
general lower-level trace closure and full principal spanning remain separate
obligations. No pending result is assumed. The original Hecke leaf remains
unproved beyond the visible N≤6 extent; its assembly/pins and full Z-in-Q
obligations are unchanged. These are ordinary compilations and complete source
reviews with warm imports, not independent cold replay or native acceptance.

## Signed canonical correction: 83-module stage

Two new sources assemble the actual finite D-corrections into a single
weight-two modular form at L=(n−1)!M and prove its independent series-span
membership. The correction is a weighted list sum of actual defect forms
restricted upward from their positive levels, not C minus products. The
pair/vector generator spans agree by a proved full-range identity. Every
integer slope is handled by nonnegative integer residues before `toNat`;
rows and correction are chosen before the universal quantifier over τ.
At M=nℓ the form has exactly level n!ℓ. The determinant ±n, signed row
congruences and uncollected coefficients ±n remain explicit.

Both parent source builds, all 23 proof and six definition audits, and literal
actual group/row/correction/negative-slope contracts exited 0. Complete source
review covered all 302 lines and exact raw-defect/series/restriction callees.
`CorrelationSignedAudit.lean` retains the 83-module stage: 1152 named public
source proofs/instances, 152 selected definitions/structures/aliases and one
derived-instance capture, 1305 standard-axiom records without `sorryAx`.

- `AllLevelTorsionCorrelationModular.lean`:
  `c8b26fc64510caa09a830b854248da8e7026f1919d90eefef62dee8069cfbbe8`
- `AllLevelTorsionCorrelationSigned.lean`:
  `cd46ead95cbbc500f621dd0885e70d04bd6509c23a80769be57e208893ccf202`
- `CorrelationSignedAudit.lean`:
  `03b90dd6ec2427a866cc553bcf76480f67c0994518044db8b799cd219a75d161`

## General lower-series-span trace closure: 92-module stage

Nine additional sources prove the previously missing lower-span trace lemma
for every positive N∣M and arbitrary integer upper label, not just scaled
labels or upper-span preservation. The trace remains the actual normalized
modular-form trace, and the span is still generated by independently
convergent series-defined forms.

Normality and genuine quotient permutations make trace constant on actual
principal-group label orbits. In a repeated-prime extension, explicit
trace-zero matrices reach every point of the complete fiber; a real integral
special-linear lift uses p∣N to justify N²≡0 modulo pN. The coprime-prime
case uses actual nonzero field-row motions, strong approximation and CRT.
The one p-zero fiber point is uniquely produced. Complete-fiber distribution
then gives the exact p² and p²−1 formulas with proved nonzero divisors.
No orbit, multiplicity or trace preservation is assumed.

Induction constructs actual lower series-span forms at successive prime
levels. Only after lower membership is proved does injectivity identify that
form with the trace. This proves all-member trace closure and actual
invariant lower-series descent, but not trace closure of all principal
products or whole modular-form spanning.

All nine parent source builds, all 41 proof/one definition audits and final
literal arbitrary-generator/all-member/invariant-descent contracts exited 0.
The first private literal audit lacked the slash-notation scope; it was
repaired without any mathematical-source change, and its failed log remains.
The complete independent source review read all 893 lines and exact matrix,
quotient, distribution, field and modular-form callees. Its level-one hash
was recomputed and corrected in the review receipt; all nine source hashes
were independently verified before parent compilation.

`LowerTraceAudit.lean` retains the 92-module stage: 1193 named source
proofs/instances, 153 selected definitions/structures/aliases and one
derived-instance capture, 1347 standard-axiom records with no `sorryAx`.

Exact added source editions:

- `DivisionEisensteinLowerClosureOne.lean`:
  `a476b462853055c42a9c41241bea683c665035be77c74b352485dbdfc715ad83`
- `DivisionEisensteinCompleteFibers.lean`:
  `a5baef6acbdba5e543d325cfa9da42c236fff3639eb7e9f6de5014239c3d91ad`
- `DivisionEisensteinPrimeFiberMoves.lean`:
  `6724ebb200f5edf66b022ee89eac6384740f86fe49a3b77be78b810d07167798`
- `DivisionEisensteinTraceInvariance.lean`:
  `2bfad0aced0ed25c1ecf97654b291bb99ab3d18a022d658b886753ed4c620fe7`
- `DivisionEisensteinRepeatedPrimeTrace.lean`:
  `6b803802885a73e765ca8281e270a939576e7cfea5806b415a5769f7c370cb95`
- `DivisionEisensteinCoprimeFiberMoves.lean`:
  `549cb3fbbcd6d840a0df92a6dc739b82ec46ef44ddc1830dabb5155b61b2adbc`
- `DivisionEisensteinAffineZero.lean`:
  `5f67e138a6e64f0f99b232f542e39201eee53e65658cf22bc0c7b32480600926`
- `DivisionEisensteinCoprimePrimeTrace.lean`:
  `dc07b39fc3e85e14401c26cb710ef21fede6713a779437cc619d81565114ec9a`
- `DivisionEisensteinLowerTraceClosure.lean`:
  `f4053b5515b5b66ead9247530b66bf1cae49997e099db04b6ad33d29c9ab8122`
- `LowerTraceAudit.lean`:
  `4e50ca48e40302d4d757feb545667fb6a3a18febf44a7ac151c3bff884e83f53`

## Actual g₂/g₃ invariants and product spans: 95-module stage

Three further sources identify the actual lattice invariants with finite
nonzero-torsion moments. For N≥2, g₂=60Σx²/((N²−1)(N²+6)) and
g₃=(4Σx³−Σy²)/(N²−1), with y=actual WP′. The nonzero-class bijection and
count N²−1 are proved; no cubic assertion at the zero convention is used.
The denominators exclude N=1 before division.

The second differential equation is proved also at zeros of WP′ through
finite meromorphic order and continuity, not pointwise cancellation. The
pole-removed WP coefficient gives B″(0)=g₂/10. Ordinary regularized
distribution is established at and near zero before differentiation. This
supplies the exact N²+6 square-moment factor and covers N=2 critical torsion.

Actual modular forms of weights four/six evaluate to Mathlib g₂/g₃ for N≥2.
For N≥3, genuine tuple concatenation and double span induction put them in
the same-level Good degree-four/six product spans. Normalizations bind
g₂=60G₄ and g₃=140G₆ to actual absolutely convergent inverse-power lattice
sums. These invariants are not quasimodular weight-two G₂.

All three parent source builds, all 50 proof/12 definition audits and actual
invariant/root-group/generator/normalization literal contracts exited 0.
Complete independent source review covered all 684 lines and exact critical
point, pole, distribution, modular-form and product callees.
`TorsionInvariantAudit.lean` co-imports all 95 mathematical sources: 1243
named public source proofs/instances, 165 selected definitions/structures/
aliases and one derived-instance capture, all 1409 records using at most
`propext`, `Classical.choice`, `Quot.sound`, and no `sorryAx`.

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationSigned:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinLowerTraceClosure:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionInvariantNormalizations:olean
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/TorsionInvariantAudit.lean
```

- `AllLevelTorsionInvariants.lean`:
  `0ba9017f2a14f3ea5ba9ba5071ffba838f410e02115abdbe603be6b1af658b83`
- `AllLevelTorsionInvariantForms.lean`:
  `3a6b91e6bb7c4a3d5a25935c1e2ede10b4601a1612f4c825033942c5c076ecb9`
- `AllLevelTorsionInvariantNormalizations.lean`:
  `1abe01250b158287ebe31629b069ec11e04b1f23decef8ce5aaa78634685645c`
- `TorsionInvariantAudit.lean`:
  `cbf9417f9ae1189cdd57572412e488e1a788ff0938cea8a0043ea1f294010d41`

All earlier mathematical source editions and audit histories are preserved.
These results prove particular series-span trace closure and generator
inclusions, not a classical Petersson-space identification, principal-product
trace closure in all relevant weights, or whole principal modular-form
spanning. No pending result is an input. `PrincipalProductSpanning` and the
unrestricted original Hecke leaf remain unproved, and the original
unconditional extent remains nonzero N≤6. The full Z-in-Q theorem, original
assembly premises and pins are unchanged. Warm-import ordinary compilation
and separate source reviews are not independent cold/native acceptance.

## Lower signed correlation product closure: 98-module stage

Three additive sources prove the actual signed correlation of embedded
lower-level A,B to be a genuine weight-two modular form on Γ(ℓ), for every
positive n and ℓ, with every modular-form field supplied. All-label raw
covariance, the complete n-torsion permutation, fixed embedded lower points
and arithmetic common-cusp bounds are proved, not caller hypotheses.

For ℓ≥3, original lower row products and the descended independent-series
correction give actual Good degree-two product-span membership. Both row
factors pull back by the additive level map. The correction is the actual
normalized trace of the previously constructed finite upper error; its
lower series membership is supplied by the proved general trace theorem.
The temporary lower modular difference is used to prove invariance, not to
manufacture error-space membership. No principal-product trace theorem is
assumed or concluded here.

All parent builds, 45 proof/15 definition audits and literal actual lower
correlation/group/product-span contracts exited 0. Complete independent
source review covered all 610 lines and the full lower-series supplier.
`LowerCorrelationAudit.lean` preserves the 98-module stage: 1288 named
source proofs/instances, 180 selected definitions/structures/aliases and one
derived-instance capture, 1469 standard-axiom records without `sorryAx`.
The earlier intermediate c826 source is not claimed to have the same ABI or
bytes as the final 419f edition; published historical sources are unchanged.

- `AllLevelTorsionCorrelationLower.lean`:
  `419f484f440ca564029e1373d60cf2feae94486f1f4674a3fe020f26043209f0`
- `AllLevelTorsionCorrelationLowerProducts.lean`:
  `71cf18bb8148e3380c240d988f8dae492f8415812d8fa56ce4bc729ac4f4a3c9`
- `AllLevelTorsionCorrelationLowerClosure.lean`:
  `6aee6ffd10cf5faa3d7f7bd6e6b3fb23bbab5fcf6e13531e6310ba0b44b9f366`
- `LowerCorrelationAudit.lean`:
  `8e22db087e403a31f763d3762d2060f6361a9dadea23c2abe61fb1b7258f8122`

## Repeated-prime degree-two product trace: 99-module stage

For p prime, p∣ℓ and ℓ≥3, the actual normalized trace of every Good degree-two
principal product from pℓ to ℓ lies in the genuine lower product span. The
trace is Mathlib's actual modular-form trace divided by its nonzero relative
index. No rank/basis, orbit, multiplicity, desired trace preservation or
whole-space spanning assumption appears.

Rank zero scales to an actual lower product. Rank one uses constructed
trace-zero principal-group moves and a genuine finite p² average. The signed
row congruences make both row combinations p-divisible; actual level scaling
pulls them to ℓ. The independently constructed series correction descends
through its proved invariance before the lower trace is taken. Rank two has
an explicit one-parameter move fixing the first row; actual Fourier duality
and a finite geometric sum leave only dependent second rows. All ranks,
nonprimitive rows and p=2 are covered. The coprime-prime case is not a
conclusion of this file.

Parent build, all 36 theorem/seven definition audits and general/p=2 literal
contracts exited 0. Complete source review read all 814 lines and exact
callees. The author's nine selected main-axiom records and a review's initial
30-theorem count are not the complete inventory; the parent enumerates all
36 theorem bodies and seven definitions. `RepeatedPrimeAudit.lean` retains
99 modules and 1512 standard-axiom records: 1324 named source proofs/instances,
187 selected definitions/structures/aliases and one derived-instance capture.

- `RepeatedPrimeProductTrace.lean`:
  `e0827cdf59f576bb494c6f6a9eafb8e00133f74ef717baa9e56344644a05294d`
- `RepeatedPrimeAudit.lean`:
  `fcdac9e216bddffe696822afff5983c69901d1c6a89538a53f8d088922231538`

## All-weight, all-label congruence-grid generator inclusion: 103 modules

Four sources give actual principal congruence-grid inverse-power forms for
N≥3 and every Nat weight k≥3, at every integer label. Their values are
N^k times the actual unrestricted `eisSummand` congruence sum. Every form
belongs to the genuine same-level Good length-k product span. No series is
replaced by a polynomial proxy and no generation or modularity is assumed.

The weighted expression recurrence has scalars only in degree zero. Formal
DX=Y and DY=6X²−g₂/2 are bound to actual ordinary WP derivatives, including
critical Y=0 points. The actual Taylor coefficient gives the exact
(−1)^r/(r+1)! normalization at k=r+2. Good torsion evaluation is off the
actual lattice. Bad even rows are actual G_k, not zero; absolute Euclidean
residue-grid decomposition and finite averaging give the N^k−1 denominator.
All positivity, negative-quotient and zero-row conventions are explicit.
Odd bad rows vanish by actual lattice negation.

This is the unrestricted congruence grid, not an identification with
Mathlib's separate primitive gcd=1 `eisensteinSeriesMF`, a Petersson subspace
or all modular forms. No primitive filter is silently introduced.

All four parent source builds, all 34 proof/nine definition/one inductive-type
audits and actual all-weight/all-label/root-group/bad-even contracts exited 0.
Complete independent source review covered all 603 lines, actual WP/calculus,
absolute summability, grade and product-span callees. `AllWeightEisensteinAudit.lean`
co-imports all 103 mathematical modules: 1358 named public source proofs/instances,
197 selected definitions/structures/aliases/inductive types and one derived
instance capture, all 1556 records within `propext`, `Classical.choice`,
`Quot.sound`, and no `sorryAx`.

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationLowerClosure:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RepeatedPrimeProductTrace:olean
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightPrincipalEisensteinForms:olean
lake --no-cache env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/AllWeightEisensteinAudit.lean
```

- `AllWeightWeierstrassDifferentialExpressions.lean`:
  `a7cd113cc41f073159b3a66cbea173760d6553e9e29ccc89c67def51d3a8b111`
- `AllWeightGoodPrincipalEisenstein.lean`:
  `8681eb3c40d1b0e4ae37cb6712f47d6985bdc99fc6bf6eb8c58a3a75f1ed89d0`
- `AllWeightLatticePrincipalEisenstein.lean`:
  `7ded3bf2f5a1faa51ab4ffaf8df230490e56729cfd501553b7b5be0ba30478f5`
- `AllWeightPrincipalEisensteinForms.lean`:
  `aeada9f1a9be2fd1c2d8f4ebd313e0031ec239ee31a06cfb093d1fdf9ada3988`
- `AllWeightEisensteinAudit.lean`:
  `c6308d58e34e3d00666fb889278c6913e7752d3a418af0117422141664e26846`

The coprime-prime product trace, mixed weight-three trace, primitive-series
binding and full principal modular-form spanning remain separate from this
edition. No pending source is a premise. `PrincipalProductSpanning` and the
unrestricted original Hecke leaf are still unproved; the unconditional extent
remains nonzero N≤6. No original assembly premise, pin or earlier published
proof edition is changed. These are ordinary pinned compilations and complete
source reviews with warm imports, not independent cold/native acceptance or
full Z-in-Q completion.

## Coprime-prime and all-divisible-level degree-two product trace: 120 modules

Fifteen sources close the actual coprime-prime Good principal-product trace,
including the stronger zero-extended all-point raw product and upper-span
endpoints. They prove the genuine CRT split, negative-determinant Fourier
phase, exact −1/N coefficient after affine cancellation, actual lower signed
correlation forms and nonempty orbit averaging. All ranks, nonprimitive lower
labels, zero classes and p=2 are covered. No desired trace/orbit/span premise
is supplied.

Two further sources combine that result with the previously proved repeated-
prime case. For positive N∣M and N≥3, the actual normalized weight-two trace
sends every upper Good degree-two product-span member into the lower product
span. Strong induction retains the explicit intermediate level bound. Actual
invariant descent constructs a lower product-span member before restriction
injectivity identifies it. This is degree two only, not whole-space spanning.

The seventeen new mathematical sources contain 90 proof bodies and 23
selected definitions/type aliases: fifteen coprime files have 81 proofs/23
definitions, and the two binder files have nine proofs/no definitions.
Complete independent source reviews read all 1580 coprime lines and all 224
binder lines with load-bearing callees. The binder review's coprime-source
condition was subsequently satisfied by the complete coprime review; its
historical wording was preserved.

The exact source editions were restored on a fresh worker without changing
any prior mathematical source, dependency pin, original leaf or published
history. The full ordinary rebuild and cumulative audit both exited 0:

```sh
lake --no-cache --no-ansi build +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightEisensteinAudit:olean +ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalProductTrace:olean
lake --no-cache --no-ansi env lean ZInQKernel/Contrib/OneProof/HeckePrimeRationality/AllLevelProductTraceAudit.lean
```

`AllLevelProductTraceAudit.lean` checks all 120 mathematical modules: 1448
named public source proofs/instances, 220 selected definitions/structures/
aliases/inductive types and one derived-row-instance capture. All 1669 records
have at most `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
Its literal coprime-prime/all-divisible-level/invariant-descent/composite-
generator examples retain the actual Mathlib groups, trace and product span.

Exact new cumulative audit SHA256:
`2308a5895bb8890048fafbd270f35d0cda0990bf4cb567ead51b94871869d565`.
This is a new derived audit from the frozen 103-module audit plus the exact
113 new author-inventory entries, not a byte/ABI identity claim for an earlier
unbanked audit. The initial private ASCII-only inventory omitted 18 Unicode
names; the corrected exact-name inventory verifies all 1669 unique entries.
No mathematical source was changed to correct that diagnostic.

Exact new endpoint editions:

- `CoprimePrincipalProductTrace.lean`:
  `0e687b1cdac2f1ceb873163af49b29d5f4e3bfe574b13abcf9e2370d3db7ece9`
- `CoprimePrincipalProductTraceSpan.lean`:
  `a54da5adec9dd04baa84ca1c31e2df95969b61106eb1b6c4050089fa3ca4aaea`
- `PrincipalProductTraceUpperSpan.lean`:
  `99d357f24698e502af9d21ea8a558607ae9f52595c38329a579df30d3fe58d81`
- `AllLevelPrincipalProductTrace.lean`:
  `16de2d561abb0c095deabea7ed7de23f5418d19042ca1ea81bc4bc8d4d94d372`

These are ordinary pinned compilations with warm imported proof artifacts
plus complete independent source reviews, not a cold/native or full-project
acceptance certificate. Mixed weight-three product trace, primitive-series
binding, newform extraction and principal-product spanning are not supplied
by this edition. `PrincipalProductSpanning`, the unrestricted Hecke leaf and
the full Z-in-Q theorem remain unproved; the original unconditional extent
remains nonzero N≤6 and no assembly premise is removed.
