# prop-ts (fleet summary)

**Verdict.** I reduced fibre-cover's `PropTS` / `PropTSAll` (Prop. TS, in Beckmann's
specialization-inertia form, for the fibre cover) in Lean to two leaves that are already in the
bundles plus named glue. No new literature leaf is needed.
`PropTSRed.propTSAll_of_bundle_meet` reads:

`PkgI2.AbhyankarDVR (T2) → R1R2fp → KummerMeetGlue → SpecNonMeeting → MobiusGlue (kernel) →
CoverModelOfHecke → PropTSAll`.

There is also a variant with Beckmann 1991 Prop. 4.2 as a leaf (`BeckmannSIT`, stated over
Mathlib's `RatFunc ℚ`, `integralClosure`, localized `Ideal.ramificationIdx` and `padicValRat`):
`propTSAll_of_leaves : BeckmannSIT → R1R2fp → MobiusGlue → CoverModelOfHecke → PropTSAll`.

**Compiles (VERIFIED).** `lake env lean scratch/prop-ts/PropTS.lean` gives 0 errors and 0
warnings. All 24 `#print axioms` lines are `[propext, Classical.choice, Quot.sound]`. The copies
of `PropTS` / `PropTSAll` are identical to fibre-cover's (`check_identical.py`). Proved here:
- the valuation bookkeeping at `0, −16/27, ∞` with indices `4, 2, 6`;
- residue fields are preserved along the kernel's `SameTripleMor`, so only the leaf's own triple
  needs a cover model (this replaces fibre-cover's `CurvePinned` by the kernel's `MobiusGlue`);
- Beckmann (tame form) from `KummerStep + SpecNonMeeting + UnramifiedMono`;
- `UnramifiedMono` as a theorem (subfield of unramified is unramified);
- the non-meeting case of `KummerStep`;
- `FunctionFieldModel` from a scheme statement `NormalizationModel` (residue fields of
  `Spec ψ` and of open immersions);
- `not_propTS_cyclotomic`: `PropTS` fails for `Spec ℚ(ζ₃₃₁)` with the constant map at `p = 331`,
  so it is a genuine constraint on the cover, neither inert nor tautological.

An independent read-only model review found no false or vacuous statement. Its four docstring
fixes are applied.

**What remains (glue, not compiled).**
- `SpecNonMeeting`: purity (t-purity3's `purityGlobalDim2'`) at `(p, X − s₀)` plus étale
  specialization. One building block is proved: `ℤ[X]_m` is regular local of dimension 2
  (`scratch/prop-ts/ZXRegular.lean`).
- `KummerMeet`: the Kummer coordinate `s^n = c(X − b)` or `c/X`, with Abhyankar T2.
- `CoverModelOfHecke(N)`: normalization `π⁻¹(𝔸¹) = Spec B`, the branch data
  (degree ≤ 324, indices 4/6/2), and Lemma NV (`NoVerticalRam`).
- The kernel's `MobiusGlue`.

All locators are UNVERIFIED (no network). Report: `docs/research/prop-ts.md`.
