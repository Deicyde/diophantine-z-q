# coeff-rational log

## 2026-11-16 15:35 start
- Base wip/coeff-field 5bb50efa5; merged origin/main c1e4ed1b8 (commit 2841989dc). Build tree copied (cp -a) from ~/dzq-wt/leaf-fold33b (main + TailZ46).

## Consumer analysis (VERIFIED, read in source)
- `eigenformCoeffFieldFinite` (TailZ45:66) is read once: TailZ45:95 `dsThm965Weak := DSCoeffExt.dsThm965Weak_of_printed n.dsThm965Printed n.eigenformCoeffFieldFinite`.
- `DSThm965Weak` -> `HodgeSplit.DSThm965` (TailZ38:83) -> TailX:198-200: `r13 := eigenformHT_of_kato_ds ... r.dsThm965 ...`, `r14 := r14Det_of_printed r.dsThm965 r.dsThm966` (TailT:1532, through `r14DetWtGe2_of_ds`, TailS:1184, all k >= 2).
- r13 = `PkgI4.EigenformHT`, r14 = `R14Det`/`EigenformRepExists`: universally quantified over (l, iotaC, iotaL, N, k, chi, g). Consumers:
  * TailA:2211 `g12` (via TailD:137 `g8_g12_of_leaves3` and TailK:394 `afterG7_of3`): g is the eigenform produced by `PkgI4.PanBerger` (Pan Thm 1.0.4 + Berger) for r_5; N, k, chi arbitrary (`0 < N`, `1 <= k`). R14 and R13 are applied at this g inside `G12Weight` (TailA:2059; proved by `g12Weight_of_senTwist`, TailB:5496) to show k = 2, and R14 inside `G12Det` (TailA:2078).
  * TailA:3497 `g14` / `iso_R14`: R14 at a weight-2 newform f from g13 (`newform_of_pan`).
- So the chain reads K_f finite for an eigenform g of a priori arbitrary weight k >= 2, level and character, produced existentially by Pan's theorem. Nothing in the tree makes its coefficients rational (the QM abelian surface's newform has [K_f:Q] = 2 typically; an elliptic-curve newform would give dim 1). Narrowing to rational f or fixed (N, k): IMPOSSIBLE.
- R16 (`R16_EichlerShimuraJ1'`, now `R16CoreY`, TailZ45:47) already gives `FiniteDimensional Q (coeffField f)` for weight-2 NEWFORMS, but G12Weight needs R14/R13 at weight k before k = 2 is known, so it cannot supply the weight-k case.

## Lean (VERIFIED, compiled)
- scratch/coeff-rational/HeckePrime.lean compiles; `#print axioms` standard for dsThm965Weak_of_printed_rationalHeckeSpan, dsThm965Weak_of_printed_heckePrime, rationalHeckeSpan_of_diamond.
- ZInQKernel/Contrib/OneProof/CoeffRational.lean (copy scratch/coeff-rational/CoeffRational.lean): `lake build ZInQKernel.Contrib.OneProof.CoeffRational` ok, `lake env lean` on it: no warnings.
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: ok (14101 jobs; only Main rebuilt); frozenTarget standard axioms.
- #discharges (DischargesRun.lean; discharges-output.txt / discharges-full.txt): eigenformCoeffFieldFinite discharged by
  CoeffRational.eigenformCoeffFieldFinite_of_heckePrime still assuming [Gamma1IntegralSpan, HeckePrimeIntegralToRational], and by
  CoeffRational.eigenformCoeffFieldFinite_of_rationalHeckeSpan still assuming [RationalHeckeSpan]; standard axioms. 45 open hypotheses, 6751 theorems checked, 18 discharge one.

## Autofold (VERIFIED)
- scratch/coeff-rational/autofold.json: eigenformCoeffFieldFinite := CoeffRational.eigenformCoeffFieldFinite_of_heckePrime {n}.gamma1IntegralSpan {n}.heckePrimeIntegralToRational (both kind published, flag unread). Dry run: strict 16/21 on 37 -> 18/20 on 38; strictest 16/21 -> 18/20 (GLUE -1).
- FoldCheck.lean (dry-run output minus line 1): compiles; HDec.HSyn.sixContactMin_of_open39 standard axioms.
- autofold-oneleaf.json (rationalHeckeSpan, kind composite): dry run 16/21 -> 16/21 (unchanged).

## Done
- Report docs/research/coeff-rational.md; .fleet/coeff-rational.md.
