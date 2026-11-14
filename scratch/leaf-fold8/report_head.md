# leaf-fold8: height, H-87/H-88, six Contrib proofs and TYZ T-11 folded into the single proof; 66 fields, strict GLUE 27 (was 31 of 69)

Task leaf-fold8, 2026-11-14. Base e9240be8 (wip/w58: fork main a6abd709 (w57) with leaf-fold7 inside OneProof,
qm-glue and height-glue). Nothing was merged. New Lean:
- `ZInQKernel/OneProof/H/TailY.lean`, `TailZ.lean`, `TailZ2.lean`, `TailZ3.lean`, `TailZ4.lean`;
- `ZInQKernel/OneProof/TYZSplit.lean`;
- the switch of `ZInQKernel/OneProof/Main.lean`.

Each new module is under 150 KB. Checks and tools are in `scratch/leaf-fold8/` (results log `log.md`, build notes
`BUILD.md`). No existing OneProof module was edited, and neither was any other file under `ZInQKernel/`,
`blueprint/`, or another task's files. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source. There is no network on this host,
so every locator below is the source report's. It is UNVERIFIED unless the audit `locators.md` read it.

## 1. Main result

```lean
theorem ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves8) (t : HDec.HSyn.OpenTextbookLeaves8) (l : HDec.HSyn.OpenAddedLeaves8)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```

The H half goes through the new top of the H assembly:

```lean
theorem HDec.HSyn.sixContactMin_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8)
    (l : OpenAddedLeaves8) (g : OpenGlue7) : ZInQ.SixContactMin
```

(`OneProof/H/TailZ4.lean`). The TYZ half uses tyz-split's derivation
`ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 : TYZThm33 → ∀ ℓ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ`
(`OneProof/TYZSplit.lean`).

The following are **VERIFIED**:
- `lake build +ZInQKernel.OneProof.Main` exits 0.
- `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
- **No existing constant changed.** op-compact's `DumpCompact` (copy in `scratch/leaf-fold8/`) with
  `cmp_hashes.py` compares 9953 OneProof constants before and 10831 after:
  - no constant was removed;
  - the only constant whose type or value hash changed is `ZInQ.OneProof.frozenTarget`, the intended statement
    change;
  - all 878 new constants are in `TailY`–`TailZ4` and `TYZSplit` (`cmp_hashes_out.txt`).
- `Check8.lean` compiles `example : ∀ r t l g, _root_.ZInQ.SixContactMin := sixContactMin_of_open8`. The closure of
  `sixContactMin_of_open8` has 193 116 constants and no `sorryAx`. The six Contrib proofs and
  `tyzThm33Pinned_of_tyzThm33` have standard axioms (`check8_result.txt`).

**Counts.** The forms are the ones leaf-fold7 used, i.e. frontier r3's: *published form*, *consequence of one
theorem* (c), *composite* (comp) and *project glue* (pg).
- The strict count calls only the published forms LEAF; the lenient count also calls consequences LEAF.
- A field keeps the form leaf-fold7 gave it. A new field takes the form its source report gives, except that
  the source's own review overrides it (`faltingsLemma5BC`, §2).
- The table is printed by `mk_fields8.py` (`counts8.md`).

| fold (in this order) | fields | published | c | comp | pg | strict LEAF / GLUE | lenient LEAF / GLUE |
|---|---|---|---|---|---|---|---|
| leaf-fold7 (`sixContactMin_of_open7`) | 69 | 38 | 18 | 12 | 1 | 38 / 31 | 56 / 13 |
| + height-split, height-glue (six height rows) | 71 | 41 | 18 | 11 | 1 | 41 / 30 | 59 / 12 |
| + qm-glue (H-87, H-88) | 72 | 44 | 17 | 10 | 1 | 44 / 28 | 61 / 11 |
| + six cloud-worker Contrib proofs | **66** | **39** | **16** | **10** | **1** | **39 / 27** | **55 / 11** |

**Bundles.**
- `OpenResearchLeaves8`: 31 fields (29 in leaf-fold7).
- `OpenTextbookLeaves8`: 20 fields (23).
- `OpenAddedLeaves8`: 14 fields (16).
- The glue bundle is leaf-fold7's `OpenGlue7`, unchanged: one field, `QuotientP1Coordinate`.

**TYZ side.** The hypothesis `h33` used to be tyz-35's pinned form of TYZ Theorem 3.3, for every `ℓ`. That was the
frontier's GLUE row T-11, a composite. It is now `TYZSplit.TYZThm33`: TYZ Theorem 3.3 in its printed form
(Period7.tex L1299–1311), restricted to `n ≡ 5, 7 (mod 8)` with `𝒫(d)` kept existential. tyz-split counts this as
published form (specialization): the TYZ side goes from 1 GLUE to 1 LEAF among `h11, h29, hS, h33`. `hS` (T-5) is
unchanged, as the task asked.

**Module layout.**
- **Kernel-only modules.** `TailY` and `TailZ` import only kernel modules (`TailZ` imports `TailY`). They hold
  height-glue's `Rows.lean` verbatim, cut in two at a namespace boundary. They could move to
  `ZInQKernel/Contrib/` unchanged.
- **Modules over the chain.** `TailZ2` imports `TailO`; `TailZ3` imports `TailZ2`. They hold qm-glue's
  `HauptGlue.lean` minus its first 2197 lines. Those lines are leafq-check's `Fold.lean`, which is already in
  `TailO` (leaf-fold6 part f10), checked line by line.
- **The bundles.** `TailZ4` imports `TailX`, `TailZ`, `TailZ3` and the six Contrib modules.
- **TYZ.** `OneProof/TYZSplit.lean` imports only `ZInQKernel.Contrib.TYZChain.Main`.
- **Main** imports `TailZ4` and `TYZSplit`. The chain from LPrefix to TailX is untouched.

### 1.1 What changed

Each item below is a field replacement made by compiled theorems. "→" reads "is replaced by".

**height-split and height-glue** (`TailY`, `TailZ` = `scratch/height-glue/Rows.lean` lines 10-3506; `TailZ4`):
- `r18`, `r19`, `r20`, `r21`, `r22`, `h5fin` → height-split's eight leaves over the published stable height
  `IsStableFaltingsHeight`:
  - `semistableReductionThm` (SS1), `semistableNeronBaseChange` (SS2), `semistablePersists` (SS3);
  - `bostLowerBound`, `javanpeykarBound`, `faltingsLemma5BC`, `pazukiCor13Upper`, `gaudronRemondThm14`.
- The derivation is `ZInQ.HeightGlue.heightRows_of_t35` (height-glue): height-split's `heightRows_of` with its
  glue bundle `HeightGlue` proved from T35. It gets two more inputs, both from existing textbook fields:
  - N1 (`ZInQ.H5Neron.NeronModelExists`) is the kernel's `ZInQ.Contrib.NeronC.neronModelExists_of_extension`
    applied to `neronSchemeExtensionExists`;
  - T35 is av-split's `AvSplit.Final.h38` applied to `uniformizationLeafAll` and `mumfordTorsionAlgClosed`.

  So **no new glue enters**. The four glue Props of height-split are proved:
  - `AnalyticUniformizationExists` and `AnalyticUniformizationUnique`;
  - `UniformizationDim`;
  - `MetrizationOfUniformization` (proved with no hypothesis).
- **Transports.**
  - `r19`, `r20`, `r21` and `h5fin` are kernel Props and are filled directly.
  - `r18` and `r22` are the chain's copies, stated over leaf-push2's copy `HDec.ZInQ.LeafPush2.stableFaltingsHeight`
    of the Arakelov layer. That copy is not definitionally the kernel's: `FinExt` and `MetrizedModel` are separate
    structures.
  - `r18_lf8` and `r22_lf8` rewrite with the chain's proved `G0HeightCopies.heightCopiesAgree` (g0-assemble), which
    compares the two infima field by field. `r18_lf8` also converts `IsCurve`/`IsJacobian` field by field, as
    `r18Concrete_of` does in the other direction.
- **Effect.** The vacuity caution of leaf-fold6/7 §2 (R19, R20, R22, `h5fin` stated over the project's infimum
  `stableFaltingsHeight`) no longer applies to any field. The kernel's infimum now appears only in theorems.

**qm-glue** (`TailZ2`, `TailZ3` = `scratch/qm-glue/HauptGlue.lean` lines 2198-end; `TailZ4`):
- `valenceFormulaGammaStar` (H-87, c) → `valenceFormulaCocompactEq` and `shimizuCovolumeO1`, via
  `LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_leaves`.
- `qmHauptmodulBase3` (H-88, comp) → the same two and `igusaCMValue24`, together with Igusa's `ψ₄` and `χ₁₀`
  (existing research fields, through `QMSplit.Theta.thetaModularity_of`), via
  `LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_leaves`.
- The glue `GammaStarFromO1` is proved by qm-glue: `QMglue.gammaStarFromO1_proof`, the index-4 covolume
  transfer.
- `ThetaQuotientValue24` (one number, `j_θ = −16/27` at discriminant `−24`) is replaced by Lin–Yang's published
  Igusa vector at that CM value. qm-glue proves the two equivalent (`thetaQuotientValue24_of_igusa` and its
  converse).

**Cloud-worker Contrib theorems** (`TailZ4`; each proves a field's Prop outright, so the field is **dropped**):

| field | proof | universe / head check |
|---|---|---|
| `t3Surj` (H-76) | `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj_proof.{0}` | field `…NeronMappingAbelianSchemeSurj.{0}`, proof universe-polymorphic, instantiated at 0 |
| `t11bExists` (H-75) | `ZInQ.Contrib.CloudW06PoincareRigidity.T11bExists_proof` | the field is the chain's `HDec.AVB2.T11bExists` (TailM); W06's `T11bExists` has the same text over the kernel's `PkgI3.AbVar`, accepted by unfolding (`t11bExists_lf8`) |
| `t24` (H-33) | `ZInQ.Contrib.CloudW08EigenformTwists.EigenformTwist_proof` | field is the kernel's `PkgI4.EigenformTwist` |
| `zariskiConnectedness` (H-67) | `ZariskiConn.ZariskiConnectedness_proof.{0}` | field `ZariskiConn.ZariskiConnectedness.{0}` |
| `egaIV_8_8_2_ii` (H-64) | `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof` | kernel Prop |
| `egaIV_17_7_8_ii` (H-66) | `ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof` | kernel Prop |

With `t11bExists` proved, T11(b) is proved: `t11b_of_exists5` turns `T11bExists_proof` into the kernel's
`ZInQ.LeafPush2.T11b_Rigidity`. So `qmCentralizerCMC` no longer needs a textbook leaf beside it to give the three
QM rows.

**tyz-split** (`TYZSplit` = `scratch/tyz-split/T11.lean` lines 2-end): `h33` → `TYZSplit.TYZThm33` (see above).

### 1.2 Which constants the fields are (VERIFIED, `Check8.lean`, `check8_result.txt`)

- 24 of the 66 fields have a head constant declared outside `ZInQKernel/OneProof`, i.e. a kernel constant
  (leaf-fold7: 33 of 69).
- The nine kernel fields that went:
  - proved by Contrib: `t3Surj`, `t24`, `zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_17_7_8_ii`;
  - replaced by height-split's leaves: `r19`, `r20`, `r21`, `h5fin`.
- The new fields are declared in the new modules:
  - `ZInQ.HeightSplit.*` (TailY), a root namespace, kernel-only;
  - `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq`, `…ShimizuCovolumeO1` (TailZ2);
  - `…Value24.IgusaCMValue24` (TailZ3).

  The height leaves could move under `ZInQKernel/Contrib/` unchanged.

## 2. Every hypothesis

"Strict kind": LEAF = published form; GLUE (c) = consequence of one theorem; GLUE (comp) = composite;
GLUE (pg) = project glue. The tables are generated from `scratch/leaf-fold8/fields8.tsv` (`mk_fields8.py`, which
starts from leaf-fold7's `fields7.tsv`). Lean types are written as in `TailZ4.lean`, inside `namespace HDec.HSyn`.

**Forms of the new fields (the readings behind the counts).**
- **SS1, SS2, SS3: consequences.** leaf-fold7 §5 already read SS1 and SS2 this way: the global form of SGA 7 IX 3.6
  and the open-subgroup form of IX 3.3. SS3 is IX 3.3 in global form (height-split §7 caveat).
- **`faltingsLemma5BC`: consequence.** height-split calls it an instance of the printed lemma. Its own statement
  review (height-split §8) says Lemma 5 is printed as an identity with a correction term, and that the inequality
  uses Raynaud's bound, so it is a consequence.
- **`javanpeykarBound`: published form (specialization)**, as height-split gives it. Specializations are counted
  this way throughout leaf-fold7. height-split §7 notes that a stricter reader may call it a consequence. Under
  that reading the height fold is neutral on the strict count (−5 + 5) and still lowers the lenient count by 1
  (`h5fin`).
- **`bostLowerBound`, `pazukiCor13Upper` (half), `gaudronRemondThm14`: published form**, with height-split's RISKs:
  Bost's display, and Pazuki's level-2 coordinates (both height-split §8).
- **`valenceFormulaCocompactEq`, `shimizuCovolumeO1`, `igusaCMValue24`: published form**, as qm-split and qm-glue
  give them. `igusaCMValue24` is equivalent to the old glue number.

