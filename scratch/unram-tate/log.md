# unram-tate results log

## UnramifiedSup (scratch/g0-mod-field/ModField.lean L704-706, copied verbatim)
- File: scratch/unram-tate/UnramSup.lean (imports only ZInQKernel.HDecomp.Descent.B2Glue).
- `UnramTate.unramifiedSup : UnramifiedSup` PROVED, no leaf. VERIFIED: `lake env lean` exit 0 (2026-11-13 04:15),
  `#print axioms` = [propext, Classical.choice, Quot.sound]. Only lint warnings (haveI style).
- Proof: inertia element g of Gal(M/Q), M = E ⊔ K, at Q ∋ p; lift s = g.liftNormal Qbar; s.restrictNormal E lies in
  the inertia of Q ∩ 𝓞E (incO = RingOfIntegers.mapRingHom of the inclusion), trivial since
  #I = e = 1 (Mathlib `Ideal.card_inertia_eq_ramificationIdxIn`, `ramificationIdxIn_eq_ramificationIdx`);
  so s fixes E and K, hence E ⊔ K (`IntermediateField.le_iff_le`, fixedField of zpowers s); g = 1; e(Q) = #I(Q) = 1.
- Note: holds for every p : ℕ as stated (p = 0 included; no case split needed).

## TateBridge, piece (iii): matrix units (scratch/unram-tate/QuatUnits.lean)
- `UnramTate.matrixUnits_of_quat`: over a field `E` with `2,3 ≠ 0`, `s² = 2`, operators `I, J` on `V` with
  `I² = 2`, `J² = -3`, `IJ = -JI` give `MatrixUnits2 E V` (glue-descent's structure) whose units commute with every
  operator commuting with `I` and `J`. VERIFIED: compiled, axioms [propext, Classical.choice, Quot.sound] (04:30).
