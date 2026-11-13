# lt-goodred: fleet note

## Verdict

Both targets are **proved**, with no statement changed and no new leaf. The details are in
`docs/research/lt-goodred.md`.

- **`LTGoodRed.goodRedTorsion : HSyn.LinkedTate.GoodRedTorsion`.** It needs no hypothesis: NOS
  (R7a) is the antecedent of the Prop. The proof transports the place `v` along
  `ψ = qEmbRing⁻¹ ∘ τ⁻¹ : K̄ ≃ ℚ̄` and checks the following:
  - `O = ψ^*v ∩ K` is a DVR (neron-lg's classification);
  - `3` and `ℓⁿ` are units of `O` (Bézout);
  - `τσ'τ⁻¹` is an inertia element at `ψ^*v`;
  - NOS (a) ⇒ (b) applies there;
  - the points move along `trPt ∘ bcPt ∘ bcPt`.

  Together with linked-tate's lemmas, G3 on the model now rests on R6, R7a and T5 alone.
- **`LTGoodRed.QM.qmEndRank_of_leaves (I3.M1) (T27) : HSyn.LinkedTate.QMEndRank`.** It uses two
  leaves already in `TextbookLeaves`: I3.M1 (`t6`) and T27 (`t27`). Albert's classification is not
  needed. Also proved:
  - **`rank ≥ 4`**, from `𝒪 ≅ ℤ⁴` and the injective map `endBC² ∘ ι`;
  - **T27's hypotheses**: `B = (2,−3)` is a division algebra (3-adic descent on its norm form),
    `B ↪ End⁰`, and `dim = 2`;
  - **the `M₂(ℚ(√d))` case is excluded**: `End⁰ ↪ M₂(F)` (`ℚ` is flat over `ℤ`), and
    `dim End⁰ > 4` forces `dim ≥ 8` (because `B` is a division algebra) and then a square-zero
    element; `EndDivision` excludes square-zero endomorphisms, because the zero map factors through
    `Spec k`.

## What compiles

All of the following are VERIFIED, with 0 errors, no `sorry`, and standard axioms only.

- **`scratch/lt-goodred/GoodRed.lean`**: 16k lines, 160 s. It contains Leaves.lean L1-14993 and
  only the declarations it needs; `log.md` lists the declarations kept.
- **`integ/`**, against linked-tate's committed files (read only):
  - `HSyn.GluePieces4` = `GluePieces3` without `goodRedTorsion` and `qmEndRank`, so 27 fields
    instead of 29;
  - `HSyn.sixContactMin_of_leaves4 r t gp4 : ZInQ.SixContactMin`.

  This holds both as an olean chain and as one 46k-line flat file (686 s, 233 axiom reports).

## What remains

Of linked-tate's new glue Props, only `LinkedFrob` and `LinkedRam` remain. The other
`GluePieces4` fields are unchanged.
