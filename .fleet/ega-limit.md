# ega-limit (fleet summary)

**Verdict: `egaIV_8_10_5_xii` (EGA IV₃ 8.10.5 (xii), `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii`) is proved
outright: the field goes away (−1) and no leaf is added.** `ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof` is
in `ZInQKernel/Contrib/OneProof/EGAIV_8_10_5_xii.lean`. It takes no hypotheses and uses only the axioms propext,
Classical.choice and Quot.sound. The statement is unchanged.

`#discharges` (base 2880fef1): `DISCHARGES [OpenAddedLeaves17.egaIV_8_10_5_xii] by ...egaIV_8_10_5_xii_proof;
still assumes: []`, standard axioms.

Route. The proof uses Chow's lemma only over an affine Noetherian base, which AxiomMath/Stacks has already
proved; it does not need absolute Noetherian approximation:
1. 01ZQ makes the morphism separated at some stage.
2. The base is covered by an affine `Y₀ = ∐ Uₖ`.
3. Chow for `X ×_S Y₀ → Y₀` comes from approximating `Γ(Y₀)` by its finitely generated ℤ-subalgebras, together
   with 01ZM, 01ZQ, Stacks 0200 and Segre (01WD).
4. Stacks 081F given Chow then gives a stage where that morphism is proper.
5. Universal closedness descends along the surjective flat quasi-compact map (Mathlib's fpqc descent).

What compiles (all VERIFIED):
- 73 Stacks files vendored under `ZInQKernel/Contrib/OneProof/EGAProperLimit/` (21k lines; manifest, LICENSE,
  NOTICE).
- The contribution itself, built against `Main` with `+Main +Discharges`.
- `#discharges`.
- A verbatim copy of the statement (`Iff.rfl`).
- The `autofold.json` dry run: strict count 34/11 → 33/11, and the generated `sixContactMin_of_open36` compiles.

Two fixes to the vendored code were needed:
- The upstream lakefile's `maxSynthPendingDepth 3` is now set in each file.
- Four names clashed with CloudW07JacobiansCurves (`ProjectiveSpace`, `isSchemeTheoreticallyDominant_toImage`,
  `HomogeneousLocalization.val_algebraMap`, `HomogeneousLocalization.val_fromZeroRingHom`). They are renamed in the
  vendored copies. These four are likely (SPECULATIVE) the earlier port's "four compatibility failures".

What remains: only the integrator's fold, which this task does not run. Report: `docs/research/ega-limit.md`;
log: `scratch/ega-limit/log.md`.
