# lg-kerwild results log

## Step 0 (09:03-09:15 PST): setup
- Merged origin/wip/local-glue (KerWild, DescentPts, localGlue_of_unramRoots, descentPts_baseChange,
  kerWild_of_g7Data with ι : ℂˣ →* ℚ̄_ℓˣ injective).
- Read (VERIFIED): g14-trace's `G14Bridge.TateBridge35` (scratch/g14-trace/part_bridge.lean l.44-72)
  carries `∃ ιC : ℚ̄ →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = β g` and outputs G7Out with `β' = j_ℓ ∘ βQ`;
  g0-mod-field's `TateBridge` (ModField.lean) has no such clause; g0-assemble2's GLUE field 39
  `LinkedTateLocal` (parts/a85_linked.lean l.2142) has neither the ιC clause nor KerWild.
- G7Data clause 9: `∀ σ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`, `GQL L = L.fixingSubgroup`
  (ZInQKernel/HDecomp/Descent/B3Assembly.lean l.36).
- g0-dim's `G0Dim.pkgI3_dim_baseChange` (scratch/g0-dim/Dim.lean l.341): `(A.baseChange L).dim = A.dim`.
- build.sh: KerWild.lean = LocalGlue.lean body + G14Bridge.lean body + Dim.lean slice + part_kerwild.lean.
- `lake build` of the 24 imported ZInQKernel modules: success.

## Step 1 (09:12-09:14 PST): §1-§4 (part_kerwild.lean) over local-glue + g14-trace's G14Bridge
- First compile: 26 errors, all in the new part (unresolved `GQ`: needed `open GlueDescent.B2Q`;
  one `rw` in `transport_one`). Fixed; second compile exit 0, 0 errors, 14 axiom prints standard.
- Proved (VERIFIED): `kerWild_of_ker`, `transport_one`, `kerWild_of_alg`, `g7Data_ker`
  (`h.2.2.2.2.2.2.2.2.1`), `kerWild_of_g7Data_alg`; defs `TateBridgeK`, `TateBridgeT`,
  `TateBridge35K`; `tateBridge_of_K`, `tateBridgeK_of_T`, `tateBridge35K_of_35`,
  `tateBridgeT_at_of_35`, `tateBridgeK_at_of_35`; `dim_model_of_bc` (g0-dim), `descentPts_of_g7`;
  `localGlue_of_transport`, `localGlue_of_tateBridge35`.
- Defeq checks that went through (VERIFIED by compile): GaloisCopy.G7Out (g0-mod-field's copy) is
  accepted where G0Galois.G7Out (local-data's copy) is expected; `incAlg` vs local-glue's `incAlgL`;
  `numberField_of_fd` (G0ModField) vs `RQ.numberField_of_fd` (Prop instances).

## Step 2 (09:15-09:21 PST): §5 TateBridgeK from I3.M0 (part_tbk.lean, mk_tbk.py)
- Read (VERIFIED): unram-tate proved `TateBridge` from I3.M0 (`tateBridge_of_tateModuleFree`,
  scratch/unram-tate/TateBridge.lean l.1822) with `a' = 1`, `β' g = gam(h g h⁻¹)`,
  `gam = ψ ∘ (β/a)` (`scalarTransfer`, l.1500), but `ScalarTransfer` does not export
  `gam = 1 → β = a`.
- Base switched from G14Bridge.lean to frob-trace's FrobTrace.lean (ModField + unram-tate's
  TateBridge.lean + g14-trace's part_bridge + frob-trace), minus its l.1632-1754 (unram-tate's
  BCPoints block, duplicate of local-glue's bc_block.lean l.11-134; diff identical modulo blank lines).
- New def `UnramTate.ScalarTransferK` (ScalarTransfer + `∀ σ, gam σ = 1 → (β σ : ℂ) = a σ`).
  Proved (VERIFIED, compile exit 0, standard axioms): `scalarTransferK` (unram-tate's proof + one
  bullet: ψ injective), `tateBridgeK_of_piecesK` (unram-tate's `tateBridge_of_pieces` proof + KerWild:
  `g ∈ G_L`, `gam(hgh⁻¹) = 1` ⟹ `β(hgh⁻¹) = a(hgh⁻¹) = 1` ⟹ `hgh⁻¹ ∈ G_{L'}` ⟹ `g ∈ G_{L'}`),
  **`tateBridgeK_of_tateModuleFree : PkgI3.TateModuleFree → TateBridgeK`**,
  `tateBridge35K_of_algFrobRed : TateModuleFree → FrobTrace.AlgFrobRed → TateBridge35K`.

## Step 3 (09:21-09:23 PST): §6 (part_final.lean)
- Proved (VERIFIED): `localGlue_of_kerWild` (G7Out on A_{L'} + KerWild + G7Clauses ⟹ LocalGlue,
  p ≠ ℓ, from R6, I2-Tors, UnramRoots), `exists_localGlue_of_tateBridgeK`,
  `exists_localGlue_of_tateModuleFree`.
- Compile: `lake env lean scratch/lg-kerwild/KerWild.lean` exit 0, 0 errors, no `sorry`, ~60 s;
  21 `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]` (compile.out).
