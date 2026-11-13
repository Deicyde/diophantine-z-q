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

## TateBridge (scratch/g0-mod-field/ModField.lean L1021-1035): reduction (scratch/unram-tate/TateBridge.lean)
- File = ModField.lean L1-1036 verbatim (so `G0ModField.TateBridge` is the statement as written) + section `UnramTate`.
- Proved (no sorry): `opVHom` (ring hom End(A(K̄)) → End_{ℚ̄_ℓ}(ℚ̄_ℓ ⊗ V_ℓ A), from pkg-I3's `Tate.map`), `conjE`,
  `matrixUnits_of_quat` (copy), `iO_sq`, `jO_sq`, `iO_jO` (i² = 2, j² = -3, ij = -ji in 𝒪), `eps_right_one`,
  and `tateBridge_of_pieces : TatePoints → EndBaseChange → ScalarTransfer → TateCont → ResQEmbedding → TateBridge`.
  VERIFIED: `lake env lean` exit 0, axioms [propext, Classical.choice, Quot.sound] (2026-11-13 ~04:55).
- Construction: Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹), c = ε' = n/d (at conjugated arguments), a = 1, β' g = γ(hgh⁻¹),
  matrix units of I = opV(Θ∘ι(i)∘Θ⁻¹), J likewise; continuity: ρ(g₀·resQ σ) = ρ(g₀)·tate σ (rho_map_mul) + open embedding.
- Named glue pieces (all glue, no new leaf): TatePoints, EndBaseChange, ScalarTransfer, TateCont, ResQEmbedding.
- `resQEmbedding : ResQEmbedding` PROVED (continuous `Field.absoluteGaloisGroup.map`, injective via the onto embedding
  of `resQ_comm'`, compact G_{L'} (instance via `Gal(AlgebraicClosure L'/L')`), open range `Fix(L')` by `resQRange`).
- `tateCont_of_tateModuleFree : PkgI3.TateModuleFree → TateCont` PROVED (leaf I3.M0 + RhoCont's
  `continuous_galRep_of_tateModuleFree`; tensor induction; `IsModuleTopology.continuous_of_linearMap`).
  Added import `ZInQKernel.HDecomp.I3Linalg.RhoCont` to the copied header. VERIFIED compiled, standard axioms (~05:00).
- Pitfall (VERIFIED): stating `Continuous fun σ => A.galRep ℓ σ w` with a type ascription times out at whnf
  (1M heartbeats); `have h3 := hρ.comp (Continuous.prodMk_left w)` without ascription is instant.
