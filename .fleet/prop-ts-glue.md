# prop-ts-glue (fleet summary)

**Verdict.**
- **`SpecNonMeeting` is now a Lean theorem** (`PropTSGlue.specNonMeeting`). It is compiled from
  Mathlib alone, with t-purity3's purity proof inlined, and uses the standard axioms only.
- **The other two Props are reduced in Lean to smaller named glue Props:** `KummerMeetGlue` to
  seven, `CoverModelOfHecke` to five.
- None of the three statements is false, vacuous or inert, and none was changed.

Report: `docs/research/prop-ts-glue.md`. Lean: `scratch/prop-ts-glue/PropTSGlue.lean`.

**What compiles** (VERIFIED):
- `lake env lean scratch/prop-ts-glue/PropTSGlue.lean`: 0 errors. All 45 new `#print axioms`
  lines are standard.
- The prefix is prop-ts's file byte for byte, and the t-purity3 copy is verbatim
  (`check_identical.py`).

**Final composite.** `propTSAll_final''` derives `PropTSAll` from the hypotheses below. No new
literature leaf is needed.
- **Leaves:** T2 and `R1R2fp`.
- **Kernel glue:** `MobiusGlue`.
- **Open glue (12 Props):**
  - seven Kummer pieces: `KummerCompositum`, plus Abhyankar via T2, other-branch and
    Gauss-valuation pieces, each at a finite point and at `∞`;
  - five Hecke pieces: `HeckeIrreducible`, `HeckeNormalizationIrr`, `HeckeDegree`,
    `HeckeBranch`, `HeckeNoVertRam`.

**Proved for `SpecNonMeeting`** (prop-ts §4.1, every step):
- `SNLocalData`.
- `SNHorizontalTransfer` and `SNVertical`.
- `VerticalResidueDegree`: `Σ e f = n`, via Mathlib's `sum_ramification_inertia_eq_finrank_fiber`.
- Separability from degree `< p`.
- Purity.
- `SNSpecialize`. Its key steps:
  - `ℤ[X]_m/(dX − a)` is the localization of `ℤ` at `(p)`;
  - the image of the étale cover is formally unramified over `ℤ` and Dedekind, and equals
    `(𝓞_L)_{(p)}`;
  - hence `e = 1`.

**Proved for the other two Props:**
- The `p`-adic bookkeeping of the Kummer step, in both cases.
- `coverModelOfHecke_of_witness`: one triple suffices.

**Review.** An independent read-only reviewer found every open Prop true. The one unverified
input is the `ℚ`-irreducibility of `Y₃`, isolated as `HeckeIrreducible` (SPECULATIVE).

**What remains:**
- The Kummer composita pieces.
- The Hecke curve theory, including Lemma NV.

**Integration.** All new names are in the `PropTSGlue` namespace, and no `ZInQKernel/` file was
edited. To integrate, use `PropTSGlue.specNonMeeting` in place of prop-ts's glue
`SpecNonMeeting`; see report §7.
