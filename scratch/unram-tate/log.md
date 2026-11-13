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
- `scalarTransfer : ScalarTransfer` PROVED (no leaf): γ_ℂ = β/a, ∂γ_ℂ = n/d; γ_ℂ(σ)^r ∈ ℚ with r = orderOf(σ|_{L'})
  (`AlgEquiv.restrictNormalHom`, `restrictNormal_eq_one_iff`), so values integral over ℚ
  (`monic_X_pow_sub_C`); F = ℚ(range γ_ℂ) algebraic (`IntermediateField.isAlgebraic_adjoin`); ψ = `IsAlgClosed.lift`.
- `tateBridge_of_points : TatePoints → EndBaseChange → PkgI3.TateModuleFree → TateBridge` PROVED.
  VERIFIED compiled, axioms [propext, Classical.choice, Quot.sound] (~05:05).
- Remaining for TateBridge: glue TatePoints (points of A_{L'} over \bar{L'} vs A(ℚ̄), Galois-compatible) and glue
  EndBaseChange (ring hom End_K(A) → End_L(A_L)); leaf I3.M0 TateModuleFree (existing, Mumford).
- `endBaseChange : EndBaseChange` PROVED (bp-qmmoduli's `endBC` copied, marked noncomputable).
- `tateBridge_of_tatePoints : TatePoints → PkgI3.TateModuleFree → TateBridge` PROVED. VERIFIED compiled,
  standard axioms (~05:02). Remaining: the single glue Prop `TatePoints`.

## TatePoints, generic parts (scratch/unram-tate/BCPoints.lean, imports only HDecomp.Objects)
- `bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω` (adjunction `Over.mapPullbackAdj`, multiplicative via `Functor.map_mul` +
  `MonObj.comp_mul`; needs `open scoped CategoryTheory.Obj`), `bcPt_galAct` (naturality for σ ∈ Aut_L(Ω),
  `homEquiv_naturality_left_symm`), `trPt` (transport along φ : Ω ≃ₐ[K] Ω₂), `trPt_galAct` (σ ↦ φσφ⁻¹).
  VERIFIED compiled, standard axioms (05:10). Group compatibility of base-change points was NOT done before (h5-glue's
  `ptsBaseChangeEquiv` is a bare bijection).
- `tatePoints : TatePoints` PROVED (BCPoints parts copied into TateBridge.lean): Θ = (trPt φL ∘ bcPt)⁻¹ with
  φ = `IsAlgClosure.equiv L' (AlgebraicClosure L') ℚ̄` restricted to L; h = φ ∘ g (g from `resQ_comm'`, bijective);
  key identity h·resQ σ·h⁻¹ = φσφ⁻¹. Pitfall: `AlgebraicClosure L'` already has `Algebra L _` from `Algebra L L'`
  (do not `letI` another one: SMul diamond).
- `tateBridge_of_tateModuleFree : PkgI3.TateModuleFree → G0ModField.TateBridge` PROVED.
- Final check (05:10): `lake env lean` on UnramSup, QuatUnits, BCPoints, TateBridge: exit 0, 0 errors, no sorry;
  all `#print axioms` = [propext, Classical.choice, Quot.sound]. VERIFIED.
- Added to TateBridge.lean: `unramifiedSup_mf : G0ModField.UnramifiedSup` (UnramSup proof copied), and
  `fieldDescentUnr'`, `modularConstituent_of_ranges_T14'` = g0-mod-field's composites without `hSup`.
  VERIFIED compiled (exit 0, no error, no sorry), standard axioms (05:15).
