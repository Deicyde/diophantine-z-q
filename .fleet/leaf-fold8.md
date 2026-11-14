# leaf-fold8 (fleet summary)

**Result.** The single proof now runs on `HDec.HSyn.sixContactMin_of_open8` (`ZInQKernel/OneProof/H/TailZ4.lean`).
- **Fields.** 66 (31 research + 20 textbook + 14 added + 1 glue), down from 69.
- **Strict LEAF/GLUE.** 39/27, was 38/31. Lenient 55/11, was 56/13.
- **TYZ.** `ZInQ.OneProof.frozenTarget` now takes `h33 : TYZSplit.TYZThm33`, TYZ Theorem 3.3 in printed form,
  in place of the composite pinned row T-11.

**What was folded** (each into new modules, verbatim from the source, script-checked):
- **height-split + height-glue** (`TailY`, `TailZ`): `r18`–`r22` and `h5fin` are theorems from height-split's
  eight leaves over the published stable height, plus N1 (from the existing `neronSchemeExtensionExists`) and T35
  (from av-split's leaves). No glue is left on the height side.
- **qm-glue** (`TailZ2`, `TailZ3`): H-87 and H-88 rest on the valence formula, Shimizu's covolume and Lin–Yang's CM
  value.
- **Six cloud-worker Contrib proofs** close `t3Surj`, `t11bExists`, `t24`, `zariskiConnectedness`,
  `egaIV_8_8_2_ii` and `egaIV_17_7_8_ii` outright.
- **tyz-split T-11** is ported (`OneProof/TYZSplit.lean`).

**Not folded.** H-3 (`QMUniformizationC` is a composite by its own docstring, so the count would rise). H-1/H-43
(needs the `CoarseFactor` and `ReciprocityOfFine` glue; no gain). T-5 was left unchanged, as asked.

**What compiles (VERIFIED).**
- `lake build +ZInQKernel.OneProof.Main` exits 0.
- `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
- `DumpCompact`/`cmp_hashes`: of 9953 old constants, 0 were removed and only `frozenTarget` changed. The 878 new
  constants are all in the new modules.
- `Check8`: the closure has 193 116 constants and no `sorryAx`.
- Every new module is under 150 KB.

**What remains.** The 27 strict-GLUE fields: 16 consequences, 10 composites and the glue `QuotientP1Coordinate`.
They are listed in `docs/research/leaf-fold8.md` §2-§3. The most promising next splits:
- `QMUniformizationC` (would let H-3 fold);
- `CoarseFactor` with `ReciprocityOfFine` (H-1/H-43);
- Raynaud's form of Faltings' Lemma 5.

Report: `docs/research/leaf-fold8.md`. Tools and log: `scratch/leaf-fold8/`.
