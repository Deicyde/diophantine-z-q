# inner-twist (2026-11-13)

**Verdict: both Props proved in Lean, no leaf, no new glue, statements unchanged.**

- `G0ModField.InnerTwistCount` (verbatim from scratch/fibre-cover/FibreCover.lean) is proved as
  `G0ModField.innerTwistCount` in `scratch/inner-twist/InnerTwist.lean`. It uses aut-o-finite's
  exact count: `Ad v ∘ t = t ∘ Ad(t⁻¹ v)`, with `W` = conjugation by `1, i, j, ij`.
  `innerTwistCount_sharp` shows that every covering `W` has `≥ 4` elements.
- `G0ModField.UnramifiedConjugates` (verbatim) is proved as `G0ModField.unramifiedConjugates` in
  `scratch/inner-twist/UnramConj.lean`, from Mathlib only, by an inertia argument:
  - `I(Q) ∩ Gal(L/K)` and `I(Q)` have the same order. This uses `card_inertia_eq_ramificationIdxIn`
    and `ramificationIdx_tower`, with `IsGaloisGroup.of_isScalarTower` making `Gal(L/K)` a Galois
    group of `𝓞 L / 𝓞 K`.
  - So `I(Q)` fixes `ℚ(α)`. By conjugating, it fixes every root of `minpoly α`, so `I(Q) = 1`.
- `scratch/inner-twist/FibreCoverIT.lean` assembles aut-o-finite, fibre-cover and both proofs, and
  proves two composites:
  - `fibreCoverExists_of_propTS'` (T5, CurvePinned, PropTS ⊢ FibreCoverExists);
  - `fibreCoverExists_of_propTSAll'` (T5, PropTSAll ⊢ FibreCoverExists).

**What compiles (VERIFIED).** All three files give exit 0 with 0 errors under `lake env lean`.
Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`. The outputs are in
scratch/inner-twist/run_*.txt.

**Finding.** FibreCover.lean does not compile on base f90cf864. pin-apply added two conjuncts to
`R1fpProps`, which breaks `rationalFibre_of_le`. The fix is proof-only and is applied in
FibreCoverIT.lean: `obtain ⟨-, -, -, hnat, -⟩ := h1`. It is the only diff from fibre-cover's body.

**What remains for G2 (not this task).** PropTS on the genuine cover, CurvePinned or PropTSAll,
and the leaf T5. Report: docs/research/inner-twist.md.
