# WitnessSpec notation removal

Removed 49 `local notation` commands under
`ZInQKernel/Contrib/OneProof/RC/WitnessSpec/`. The table uses line numbers from
the base revision `f2c6dbc7d2696fa5e73370f18931325de5c51845` and shows the
original right-hand sides. Named notations appearing in those right-hand sides
were expanded transitively. Every statement uses the expansion directly.

| File | Line | Notation | Original expansion | Replacement |
| --- | ---: | --- | --- | --- |
| `ActualLocal.lean` | 31 | `wₚ` | `(ValuationSubring.valuation (valuationRing v))` | Inlined |
| `ActualLocal.lean` | 32 | `kₚ` | `(IsLocalRing.ResidueField (Valuation.valuationSubring wₚ))` | Inlined; also proof-local `let` |
| `ActualLocal.lean` | 33 | `B` | `(WeierstrassCurve.map C (Int.castRingHom (ZMod p)))` | Inlined; also proof-local `let` |
| `ActualLocal.lean` | 34 | `E` | `(WeierstrassCurve.baseChange C ℚ)` | Inlined |
| `CurveAtPlace.lean` | 23 | `R` | `(Valuation.valuationSubring w)` | Inlined |
| `CurveAtPlace.lean` | 24 | `k` | `(ResidueField R)` | Inlined |
| `CurveAtPlace.lean` | 74 | `wₚ` | `(ValuationSubring.valuation (valuationRing v))` | Inlined |
| `CurveAtPlace.lean` | 75 | `Rₚ` | `(Valuation.valuationSubring wₚ)` | Inlined |
| `CurveAtPlace.lean` | 76 | `kₚ` | `(ResidueField Rₚ)` | Inlined |
| `CurveAtPlace.lean` | 110 | `B` | `(WeierstrassCurve.map C (Int.castRingHom (ZMod p)))` | Inlined |
| `Evaluation.lean` | 19 | `Xₙ` | `AddSubgroup.torsionBy X (n : ℤ)` | Inlined |
| `Evaluation.lean` | 20 | `Yₙ` | `AddSubgroup.torsionBy Y (n : ℤ)` | Inlined |
| `FiniteReduction.lean` | 19 | `wₚ` | `(ValuationSubring.valuation (valuationRing v))` | Inlined |
| `FiniteReduction.lean` | 20 | `kₚ` | `(ResidueField (Valuation.valuationSubring wₚ))` | Inlined |
| `FiniteReduction.lean` | 21 | `wL` | `(IsDedekindDomain.HeightOneSpectrum.valuation L (restrictHeightOne v e))` | Inlined |
| `FiniteReduction.lean` | 22 | `kL` | `(ResidueField (Valuation.valuationSubring wL))` | Inlined; also proof-local `let` |
| `FiniteReduction.lean` | 43 | `B` | `(WeierstrassCurve.map C (Int.castRingHom (ZMod p)))` | Inlined |
| `FiniteReduction.lean` | 66 | `H` | `(ringClassField (conductorOrder K 1))` | Inlined |
| `FiniteReduction.lean` | 67 | `kH` | `(ResidueField (Valuation.valuationSubring (IsDedekindDomain.HeightOneSpectrum.valuation H (restrictHeightOne v er))))` | Proof-local `let` |
| `LocalFrobenius.lean` | 15 | `Sₚ` | `(LocalSubring.toSubring (localRing v))` | Inlined |
| `LocalFrobenius.lean` | 79 | `wₚ` | `(ValuationSubring.valuation (valuationRing v))` | Inlined |
| `LocalFrobenius.lean` | 80 | `Rₚ` | `(Valuation.valuationSubring wₚ)` | Inlined |
| `PointReduction.lean` | 25 | `R` | `v.valuationSubring` | Inlined |
| `PointReduction.lean` | 26 | `k` | `ResidueField R` | Inlined |
| `PointReduction.lean` | 27 | `Wℓ` | `WeierstrassCurve.toAffine (E⁄L)` | Inlined |
| `PointReduction.lean` | 28 | `C` | `(integralModel R Wℓ)` | Inlined |
| `PointReduction.lean` | 29 | `Ck` | `(WeierstrassCurve.map C (residue R))` | Inlined |
| `Restriction.lean` | 18 | `u` | `(restrictHeightOne v e)` | Inlined |
| `Restriction.lean` | 19 | `S` | `(valuationSubringAtPrime L u)` | Inlined |
| `Restriction.lean` | 20 | `Sₚ` | `(LocalSubring.toSubring (localRing v))` | Inlined |
| `Restriction.lean` | 21 | `wₚ` | `(ValuationSubring.valuation (valuationRing v))` | Inlined |
| `Restriction.lean` | 22 | `Rₚ` | `(Valuation.valuationSubring wₚ)` | Inlined |
| `Restriction.lean` | 23 | `wL` | `(IsDedekindDomain.HeightOneSpectrum.valuation L u)` | Inlined |
| `Restriction.lean` | 24 | `RL` | `(Valuation.valuationSubring wL)` | Inlined |
| `Specialize.lean` | 26 | `H` | `(ringClassField (CST.conductorOrder dat.K 1))` | Inlined |
| `Specialize.lean` | 84 | `E` | `(WeierstrassCurve.baseChange C ℚ)` | Inlined |
| `Specialize.lean` | 85 | `A` | `(qtwist E (Dw : ℚ))` | Inlined |
| `Specialize.lean` | 86 | `H` | `(ringClassField (CST.conductorOrder dat.K 1))` | Inlined |
| `Torsion.lean` | 21 | `wₚ` | `(ValuationSubring.valuation (valuationRing v))` | Inlined |
| `Torsion.lean` | 22 | `kₚ` | `(IsLocalRing.ResidueField (Valuation.valuationSubring wₚ))` | Inlined; also proof-local `let` |
| `Torsion.lean` | 23 | `B` | `(WeierstrassCurve.map C (Int.castRingHom (ZMod p)))` | Inlined; also proof-local `let` |
| `Torsion.lean` | 24 | `E` | `(WeierstrassCurve.baseChange C ℚ)` | Inlined |
| `Torsion.lean` | 25 | `X` | `(Affine.Point (WeierstrassCurve.toAffine (E⁄Qbar)))` | Inlined |
| `TwistAtPlace.lean` | 20 | `Sₚ` | `(LocalSubring.toSubring (localRing v))` | Inlined |
| `TwistAtPlace.lean` | 21 | `wₚ` | `(ValuationSubring.valuation (valuationRing v))` | Inlined |
| `TwistAtPlace.lean` | 22 | `Rₚ` | `(Valuation.valuationSubring wₚ)` | Inlined; also proof-local `let` |
| `TwistAtPlace.lean` | 23 | `kₚ` | `(ResidueField Rₚ)` | Inlined |
| `Valuation.lean` | 32 | `Z` | `(Subalgebra.toSubring (integralClosure ℤ Qbar))` | Inlined |
| `Valuation.lean` | 37 | `Sₚ` | `(LocalSubring.toSubring (localRing v))` | Inlined |

`diff -u scratch/rc-witness-spec-ln/{check-before,check-after}.txt` exited 0
and produced no output. The files match byte for byte. `Check.lean` checks
75 declarations, including private declarations and instances, plus the
`ExactWitness` constructor and six fields. Both runs use `pp.notation false`
and `pp.explicit true`.

All 11 edited modules compiled with serial `lake env lean -j1` runs.
`RingClassPlace.lean` and `Witness.lean` were rebuilt as dependencies of
edited modules. The 74 existing `#print axioms` reports cover all 41
theorems in the edited files and agree with the baseline. The only axioms
reported were `propext`, `Classical.choice`, and `Quot.sound`.

`git grep` found no remaining `local notation` in WitnessSpec and no
`local infix`, `local macro`, `scoped notation`, or `notation3`
declarations there. Existing scope openings and local instance attributes
are unchanged. The inherited `RC/Stages/ExactGenus.lean` command is outside
this change.
