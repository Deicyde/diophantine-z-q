# ts-kummer results log

Task: prove or reduce the seven Kummer pieces of scratch/prop-ts-glue/PropTSGlue.lean
(KummerCompositum; KummerAbhyankarFinGlue, KummerOtherBranchFin, KummerVerticalFin;
KummerAbhyankarInfGlue, KummerOtherBranchInf, KummerVerticalInf), the open glue under
`PropTSRed.KummerMeetGlue` via `PropTSGlue.kummerMeetGlue_of_pieces'`.

## Step 0: setup
- Merged origin/wip/prop-ts-glue (clean).
- Truth check of the seven statements (re-derived, model argument, no Lean): all seven true as
  stated (agrees with prop-ts-glue's review). Key point for the Abhyankar pieces: Mathlib's
  `Ideal.ramificationIdx` is the length of `S_q / p S_q`, intrinsic to the local ring, so
  `ramificationIdx_map_eq_ramificationIdx` (localization of the base) and `ramificationIdx_tower`
  (flat towers) apply.
- Plan: (1) prove KummerAbhyankarFinGlue and KummerAbhyankarInfGlue from T2 through one abstract
  core lemma; (2) reduce the other-branch and vertical pieces to a compositum-unramified Prop;
  (3) KummerCompositum.

## Step 1: the two Abhyankar pieces PROVED from T2 (dev file Core.lean), compiled
- `TsKummer.abhyankar_core` (abstract transfer): R0 Dedekind ℚ-algebra with fraction field K,
  L/K finite separable, ι : L → M, A Dedekind with A → M injective, σ : R0 → A integral and
  compatible with ι; π0 generating a nonzero prime, σ π0 = s^n, (s) prime, M = L(s), every prime of
  integralClosure R0 L over (π0) has e ∣ n ⟹ every prime of integralClosure A M over (s) has
  e = 1. Proof: T2 at R_p = (R0)_(π0) (DVR); hypothesis transferred by
  `IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx` (integral closure of R_p is the
  localization, `IsLocalization.integralClosure`); conclusion: integralClosure A M ≃ₐ[R0]
  integralClosure R0 M (same carrier, integrality transitivity), `ramificationIdx_map_algEquiv`
  (new, via `Ideal.ramificationIdx_tower` with an isomorphism), then the flat tower
  R0 → A → integralClosure A M (`Ideal.ramificationIdx_tower`) and e((s)|R0) = n from
  `IsDiscreteValuationRing.length_quotient_pow_maximalIdeal`.
- `TsKummer.kummerAbhyankarFinGlue : KummerAbhyankarFinGlue` (R0 = ℚ[X], σ : X ↦ b + s^n/c,
  π0 = c(X − b)).
- `TsKummer.isFractionRing_infCoord : IsFractionRing InfCoord (RatFunc ℚ)` (via `reflect`), and
  `TsKummer.kummerAbhyankarInfGlue : KummerAbhyankarInfGlue` (R0 = InfCoord, σ : u ↦ s^n/c,
  π0 = c·u).
- Compile (`lake env lean scratch/ts-kummer/Core.lean`, ~25 s): 0 errors; both `#print axioms` =
  [propext, Classical.choice, Quot.sound] (VERIFIED). Statements: verbatim copies of
  KummerShape, rFin, rInf, InfCoord, infAlg, infUnif, KummerAbhyankarFin(Glue),
  KummerAbhyankarInf(Glue) from PropTSGlue.lean (dev copies; final file uses the verbatim prefix).
