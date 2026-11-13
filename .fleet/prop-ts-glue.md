# prop-ts-glue (fleet summary)

**Verdict.** The three glue Props under Proposition TS are true as stated. None is false,
vacuous or inert, and none was changed: `SpecNonMeeting`, `KummerMeetGlue` and
`CoverModelOfHecke`, from `scratch/prop-ts/PropTS.lean`. Each is reduced in Lean to smaller
named Props, and part of the glue is now proved. Report: `docs/research/prop-ts-glue.md`. Lean:
`scratch/prop-ts-glue/PropTSGlue.lean`.

**What compiles** (VERIFIED):
- `lake env lean scratch/prop-ts-glue/PropTSGlue.lean`: 0 errors. All 35 new `#print axioms`
  lines are standard.
- The prefix is prop-ts's file byte for byte, and t-purity3's purity proof is inlined verbatim
  (`check_identical.py`).

**Final composite.** `propTSAll_of_pieces'''` derives `PropTSAll` from the hypotheses below. No
new literature leaf is needed.
- **Leaves:** T2 and `R1R2fp`.
- **Kernel glue:** `MobiusGlue`.
- **Open glue (14 Props):**
  - `VerticalResidueDegree` and `SNSpecialize`, for `SpecNonMeeting`;
  - seven Kummer pieces: `KummerCompositum`, plus Abhyankar via T2, other-branch and
    Gauss-valuation pieces, each at a finite point and at `∞`;
  - five Hecke pieces: `HeckeIrreducible`, `HeckeNormalizationIrr`, `HeckeDegree`,
    `HeckeBranch`, `HeckeNoVertRam`.

**Proved here:**
- `SNLocalData`: the normalization of `ℤ[X]_m` in `E` is normal and finite.
- `SNHorizontalTransfer`: via `S_{Q'} ≅ C_𝔮 ≅ B_Q` and `ramificationIdx_eq_one_iff`.
- `SNVertical`, from `VerticalResidueSeparable`, which in turn follows from
  `VerticalResidueDegree` because degree `< p` implies separable.
- The horizontal case of codimension-one unramifiedness (the Gauss-lemma argument).
- All `p`-adic bookkeeping of the Kummer step, in both cases.
- `PurityGlobalDim2`, from the inlined copy of t-purity3's proof.
- `coverModelOfHecke_of_witness`: one triple suffices.

**Review.** An independent read-only reviewer found every open Prop true. The one unverified
input is the `ℚ`-irreducibility of `Y₃`, now isolated as `HeckeIrreducible` (SPECULATIVE).

**What remains:**
- `VerticalResidueDegree`: `f ≤ n`, via Mathlib's `sum_ramification_inertia_eq_finrank` over
  `ℤ[X]_{(p)}` plus residue-field transport.
- `SNSpecialize`: étale base change to `ℤ_(p)`.
- The Kummer composita.
- The Hecke curve theory, including Lemma NV.
