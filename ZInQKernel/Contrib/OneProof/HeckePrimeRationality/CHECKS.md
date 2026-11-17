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
The weight-one forms and their coefficient descent are not supplied by these
helpers. No assumption in the final single-proof assembly has been discharged.
