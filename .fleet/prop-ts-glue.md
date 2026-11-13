# prop-ts-glue (fleet summary)

**Verdict.** The three glue Props under Proposition TS are true as stated. None is false,
vacuous or inert, and none was changed: `SpecNonMeeting`, `KummerMeetGlue` and
`CoverModelOfHecke`, from `scratch/prop-ts/PropTS.lean`. Each is reduced in Lean to smaller
named Props. **`SpecNonMeeting` now follows from the single glue Prop `SNSpecializeUnram`**, the
unramifiedness of the specialized fibre. Report:
`docs/research/prop-ts-glue.md`. Lean: `scratch/prop-ts-glue/PropTSGlue.lean`.

**What compiles** (VERIFIED):
- `lake env lean scratch/prop-ts-glue/PropTSGlue.lean`: 0 errors. All 41 new `#print axioms`
  lines are standard.
- The prefix is prop-ts's file byte for byte, and t-purity3's purity proof is inlined verbatim
  (`check_identical.py`).

**Final composite.** `propTSAll_final'` derives `PropTSAll` from the hypotheses below. No new
literature leaf is needed.
- **Leaves:** T2 and `R1R2fp`.
- **Kernel glue:** `MobiusGlue`.
- **Open glue (13 Props):**
  - `SNSpecializeUnram`;
  - seven Kummer pieces: `KummerCompositum`, plus Abhyankar via T2, other-branch and
    Gauss-valuation pieces, each at a finite point and at `∞`;
  - five Hecke pieces: `HeckeIrreducible`, `HeckeNormalizationIrr`, `HeckeDegree`,
    `HeckeBranch`, `HeckeNoVertRam`.

**Proved here:**
- `SNLocalData`.
- `SNHorizontalTransfer`.
- `SNVertical`.
- `VerticalResidueDegree`, i.e. `Σ e f = n` at the vertical primes, via Mathlib's
  `sum_ramification_inertia_eq_finrank_fiber` and a DVR localization.
- Separability from degree `< p`.
- The finiteness half of `SNSpecialize`.
- The horizontal Gauss-lemma argument.
- All `p`-adic bookkeeping of the Kummer step.
- Purity (inlined from t-purity3).
- The witness form of `CoverModelOfHecke`.

**Review.** An independent read-only reviewer found every open Prop true. The one unverified
input is the `ℚ`-irreducibility of `Y₃`, isolated as `HeckeIrreducible` (SPECULATIVE).

**What remains:**
- `SNSpecializeUnram`: étale over `ℤ[X]_m`, specialized at `X = s₀`, gives a residue field
  unramified at `p`.
- The seven Kummer composita pieces.
- The Hecke curve theory, including Lemma NV.
