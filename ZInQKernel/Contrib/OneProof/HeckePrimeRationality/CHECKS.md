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
