# leaf-adopt3: g0-split and wave 25 folded into the H decomposition; no `sorry` left

Status: research note (task leaf-adopt3, 2026-11-13). It continues docs/research/leaf-adopt2.md.
Base: 883c4ddf (wip/integrate-w35c), with origin/wip/g0-split, wip/h5-neron and wip/t10-etale
merged (their scratch directories and notes only; their `.fleet` notes dropped).

Files:
- Edited: `scratch/h-decomposition/Leaves.lean`, `docs/research/h-decomposition.md`.
- New, in `scratch/leaf-adopt3/`:
  - `assemble.py` rebuilds `Leaves.lean` from the base prefix (lines 1-21087 of 883c4ddf) and the
    parts in `parts/`, then runs `header_edits.py` (module docstring) and `apply_repairs.py`
    (12 docstring repairs). `python3 scratch/leaf-adopt3/assemble.py full` reproduces the file.
  - `parts/` holds the tail of the file, one file per section: GlueSSBC, HSyn §0-§2, the ten fold
    fragments `4*_*.lean`, the bundles, the derived theorems, the G0 proof and the trailer.
  - `fold/` holds the fragments as the read-only subagents prepared them (`BRIEF.md`,
    `<task>.lean`, `<task>.notes.md`).
  - `x1transport/T.lean` is the new transport proof, checked standalone.
  - Checks: `stmt_diff.py`, `fold_diff.py` and their outputs; `compile_full.txt`.
  - `doc_edit.py` (the edits of the note), `repairs_report.md`, `log.md`.

No file under `ZInQKernel/`, `blueprint/` or another task's directory was edited.

Marks:
- **VERIFIED**: compiled, counted or read here.
- **STANDARD**: published, with a reference.
- **SPECULATIVE**: an assessment.
- **UNVERIFIED**: a theorem number recalled from memory (no network).

## 0. Main result

**`Leaves.lean` has no `sorry`.** The top-level theorem is

```lean
theorem HSyn.sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces) :
    ZInQ.SixContactMin
```

Its hypotheses are exactly the three bundles. `#print axioms` gives `[propext, Classical.choice,
Quot.sound]`.

So **H follows from 58 literature leaves and 10 named glue Props.** In detail:
- 23 research-level leaves: 21 concrete, while R17 and R1(b) are still `opaque` placeholders.
- 35 textbook leaves, all concrete.
- 10 glue Props, each a `def … : Prop` that the project must still prove.

VERIFIED (final run, 2026-11-13 02:20 PST): `lake env lean scratch/h-decomposition/Leaves.lean`
exits 0 in 452 s (34 024 lines):
- 0 errors and no `declaration uses 'sorry'`;
- 2 `opaque`, no `axiom`;
- 175 `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`, including
  `HSyn.sixContactMin_of_leaves`, `HSyn.glueOutputs_of_leaves` and every wave-25 bridge.

The output is `scratch/leaf-adopt3/compile_full2.txt`. An earlier full run, before the
`X1BelyiOnModel` transport, is `compile_full.txt` (574 s, 174 lines, same result).

| | before (leaf-adopt2) | now |
| --- | --- | --- |
| `sorry` | 1 (`glueOutputs_of_leaves`) | **0** |
| `opaque` | 3 (R1(b), R17, T10) | **2** (R1(b), R17) |
| research leaves | 23 (21 concrete) | 23 (21 concrete) |
| textbook leaves | 33 (32 concrete) | **35 (35 concrete)** |
| glue Props in G0's hypotheses | (one `sorry`) | **10** (`GluePieces`) |

## 1. What was done (all VERIFIED by compilation)

### 1.1 G0: g0-split's proof replaces the `sorry`

I followed g0-split's recipe (its doc §4): `GlueSSBCSec` goes before `HSyn`, and `part_split.lean`
replaces the old tail. Changes against g0-split's text:
- **R18, R22 come from the bundle.** leaf-adopt2 had already made `r.r18`, `r.r22` concrete
  (leaf-push2's statements over `ZInQ.LeafPush2.stableFaltingsHeight`). g0-split's transported
  forms `R18_JavanpeykarConcrete`, `R22_PazukiConcrete` (over def-faltings' height) are now
  derived from them by new proofs, with leaf-adopt2's glue target `HSyn.HeightCopiesAgree` as
  hypothesis:
  - `G0Split.r18Concrete_of` converts the textual copies `LeafModCurves.IsCurve`, `IsJacobian`
    field by field;
  - `G0Split.r22Concrete_of`.

  So `hR18`, `hR22` are no longer hypotheses, and `HeightCopiesAgree` becomes a glue piece.
- **Copies removed.** g0-split's copies of leaf-push2's R22 definitions (`cptObj`, `CPts`,
  `IsUniformization`, `IsSiegel`, `IsPeriodMatrix`, `Char2`, `thetaConst`, `absLogHeight`,
  `pazukiC2`) and of `ffStructMap`, `ffAlgebra`, `javanpeykarBound` are replaced by the
  `ZInQ.LeafPush2` originals. The texts are identical, so statements are unchanged up to the name of
  an identical definition.
- **The pieces are bundled** as `HSyn.GluePieces` (§2).
- **New glue proofs** (§2.3):
  - piece 5 (`HeightAdditivity`) follows from T41, H5 and `ProductModelHeight`;
  - piece 3 (`X1BelyiOnModel`) follows from `BelyiX1` by transport.

### 1.2 Wave 25 folded in

Each fragment sits in its own section between `HSyn` §2 and the bundles. Read-only subagents
prepared each one from the task's files following `fold/BRIEF.md`. I compiled every fragment;
all compiled at the first attempt except e1-sub, whose one error is listed in the table.

| Task | Section | Result in `Leaves.lean` | Bundle / glue effect |
| --- | --- | --- | --- |
| t-skolem-kw | `TSkolemKWSec` | `TSkolemKW.hsyn_t13 : HSyn.SkolemNoether` (also the PkgI6 and GlueDescent forms), `hsyn_t19 : HSyn.BrauerNesbitt`, `hsyn_t18_of_chebotarev : ChebotarevExists → FrobeniusDense`, `KW.KroneckerWeberCyclic` with `kroneckerWeberCyclic_of_hsyn` and C8's use form, `C10.c10_of_chebotarev` | T13, T19 leave the bundle; `t17 : KroneckerWeberCyclic`, `t18 : PkgI6.ChebotarevExists` |
| t-different | `TDifferentSec` | `PkgI6.hilbertDifferentFormula`, `differentBound`, `herbrandQuotient`, `herbrandTransitivity` (types exactly the leaf `def`s) | T22 (both parts) leaves the bundle; T20, T21 local forms proved, global forms stay |
| t30-adelic | `T30Sec` (with the kernel's `GlueI6Rest`, `GlueSqrtLocal`, `GlueSqrtDisj` copied: `Conductor/SqrtChar`, `Sqrt/SqrtLocal`, `Sqrt/Disj`) | `T30.leafSqrtCrit_of_t16a : (∀ p [Fact p.Prime], LocalKroneckerWeber p) → LeafSqrtCrit` | T30 leaves the bundle. G1-adelic is **not copied**: it needs the kernel's `Vigneras/Local.lean` (707 lines) plus `Adelic.lean` (1066), and it changes no field. Its statements are listed in `fold/t30-adelic.notes.md` |
| t10-etale | `T10EtaleSec` | `T10Etale.T10_TateDuality` (Galois-equivariant, over Mathlib's pro-étale `EllAdicCohomology`), `T10_groupIso_of_tateDuality` | `t10` concrete; the `opaque HSyn.T10_TateDuality` is deleted |
| pi0-x6 | `Pi0X6Sec` | `Pi0X6.leafAdopt_r1pi0Props_of_bundle`, `…_of_X6Props` (conclusion exactly `LeafAdopt.R1pi0Props X`, from `R5ptProps`, `R5fpCount`, `R2X6CMExact`, `AGInputs`) | none: R1's clause is kept, as pi0-x6 recommends |
| hodge-lattice | `HodgeLatticeSec` | `HodgeLattice.hodgeLatticeTheorem_of_tangent`, `…_of_abVarFacts` (from `RegularAtOrigin`, `DimAtOrigin`, `DimBaseChange`), `…_of_varieties`, `…_of_abVar` | glue row only. `G0Split.hodgeLatticeTheorem_of_dimBaseChange` takes glue piece 2 as `DimBaseChange` (`dimBaseChange_iff_hodgeLattice`: same statement, binders reordered) |
| h5-neron | `H5NeronSec` | `ZInQ.H5Neron.stableFaltingsHeight_eq_neron_all` (from N1, N2, `NeronModelMinimal`, three glue Props), `stableFaltingsHeight_add_le'`, `heightAdditivity_unfolded` | new leaf T41 = N1; glue piece 5 narrowed to `ProductModelHeight`. **H5 stays a leaf**: no theorem concludes it |
| x1-belyi | `X1BelyiSec` | `X1Belyi.x1ModelExists_of_leaves`, `belyiX1_of_leaves`, `modCurveLeaves_of`, `exists_J1_of_leaves` | new field `x1 : X1Belyi.X1Leaves` (T36-T40) |
| e1-sub | `E1SubSec` (with the kernel's `TateBC` §2, `E1_exists_hom_ne_zero'`, two `GlueI3` wrappers) | `E1Sub.vSurjOfSurjective : FaltingsSemisimple → FaltingsTate → TateModuleFree → VSurjOfSurjective`, `rhoF_subrep_J`, … | glue target `VSurjOfSurjective` proved. One edit: an `rfl` after `rw` in `bcPt.map_one'` had no goal left in this context and was removed |
| c9-rhof | `C9RhofSec` (with the kernel's `RhoCont` §3) | `C9Rhof.rhoF_semisimple`, `rhoF_continuous`, `c9`, `c9_R14`, `c9_r5`, `c10_via_c9`, and the `_hsyn` bundle-form variants | glue row C9 proved |

### 1.3 Bundles (the only statement changes)

`HSyn.TextbookLeaves`, field by field:
- `t10 : T10Etale.T10_TateDuality`, which was an `opaque`.
- `t13`, `t19`, `t22a`, `t22b`, `t30` are removed. They are proved:
  - `HSyn.t13_proved`, `t19_proved`, `t22a_proved`, `t22b_proved`;
  - `TextbookLeaves.leafSqrtCrit` gives T30 from `t16a`.
- **`t17 : TSkolemKW.KW.KroneckerWeberCyclic`** (weaker). No proof in the file used `t17`.
- **`t18 : PkgI6.ChebotarevExists`**. `TextbookLeaves.frobeniusDense` recovers the old field.
  `PkgI6.ChebotarevExists` is the statement of `GlueC10.ChebotarevExists` (t-skolem-kw checked
  the text).
- **New `x1 : X1Belyi.X1Leaves`** bundles T36-T40:

  | Leaf | Statement | Reference |
  | --- | --- | --- |
  | T36 | torsion of elliptic curves | AEC III.6.4(b) |
  | T37 | Néron–Ogg–Shafarevich over `k(T)` | Serre–Tate 1968 |
  | T38 | curves from function fields over `ℚ` | Hartshorne I.6 |
  | T39 | `ℚ` is algebraically closed in `K_N` | Igusa 1959 |
  | T40 | a rational cusp | Tate curve |

  All locators are UNVERIFIED.
- **New `t41 : ZInQ.H5Neron.NeronModelExists`** (Néron models exist, BLR 1.2/1, 1.4/3).

`HSyn.ResearchLeaves`: no field changed. Only the `r19` and `r1r2` docstrings changed
(rv-leaves48 P1, P3).

New theorems give the former fields and the glue targets back (`parts/65_derived.lean`):
- `TextbookLeaves.t10_groupIso`;
- `TextbookLeaves.x1ModelExists`, `TextbookLeaves.belyiX1`;
- `TextbookLeaves.exists_J1`: a `J₁(N)` exists. So `r16`, `t34` are not vacuous for lack of a
  model, which closes rv-leaves48 P2.
- `modCurveLeaves_of_bundles`;
- `t20_local_proved`, `t21_local_proved`.

### 1.4 Docstring and note repairs

`apply_repairs.py` (prepared by a subagent) applies 12 replacements:
- from scratch/rv-leaves48/Repairs.md: P1, P3, P4, P5;
- from docs/research/factcheck-w34b.md: items 1, 3, 4 and the "five fields" nit.

It was tested on copies before use: after stripping comments, the code is byte-identical
(`repairs_report.md`).

In h-decomposition.md the subagent applied P1, P2, P4, P6 and fact-check items 1, 3, 5, 8, 14, 18,
and the line-306 nit.

**The rows the task named.** The task asked for §3 C2/E1 and §5 WP3/WP5/WP13. Those rows are
**not** among factcheck-w34b's items (VERIFIED by grep: the fact-check mentions h-decomposition.md
only in items 5, 14, 28 and one nit). I corrected them anyway, with their real sources:
- G8 (C2), G17 (E1) and WP3: `SemisimpleBaseChange` is proved (glue-ssbc, now in the file).
- WP13: the QM dichotomy locator is Yu 2013 (loc-fix).
- WP5: nothing stale was found (R17 is still `opaque`).

## 2. The glue pieces (`HSyn.GluePieces`, 10 fields)

| # | Field : Prop | Glue step | Status |
| --- | --- | --- | --- |
| 1 | `dimFinite : G0Split.DimFinite` | an abelian variety has finite dimension | open |
| 2 | `dimBaseChange : G0Split.DimBaseChange` | `dim A_L = dim A` | open (it also gives `HodgeLatticeTheorem` with two Props) |
| 4 | `fibreSimple : G0Split.FibreSimple` | G5-G6 on the fibre surface | open |
| 5 | `productModelHeight : ZInQ.H5Neron.ProductModelHeight` | E4 at model level | open; replaces `HeightAdditivity` |
| 6 | `stableHeightBaseChange : G0Split.StableHeightBaseChange` | stable height under base change | open |
| 7 | `productExists : G0Split.ProductExists` | G17, products | open |
| 8 | `reverseIsogeny : G0Split.ReverseIsogeny` | G17, isogeny `J → A × Z` | open |
| 9 | `thetaPoint : G0Split.ThetaPointOfFibre` | G19, F1 on `A` | open |
| 10 | `modularConstituent : G0Split.ModularConstituent` | G2, G4, G7-G16 | open (cores proved) |
| 11 | `heightCopies : HeightCopiesAgree` | the two textual copies of the height agree | open (pure transport) |

Piece 3 (`X1BelyiOnModel`) is proved (§2.3) and is not a field.

### 2.1 Why piece 5 changed

g0-split's `HeightAdditivity` (`h_F(A) + h_F(Z) ≤ h_F(P)` for `P ≅ A × Z`) now follows from:
- T41 (Néron models exist, a textbook theorem);
- H5's `NeronModelMinimal` (`r.h5.2`);
- h5-neron's model-level glue `ProductModelHeight` (`𝒢₁.height + 𝒢₂.height ≤ 𝒢P.height` for a
  product group model).

The bridge is `G0Split.heightAdditivity_of_h5neron`, compiled. `ProductModelHeight` is about
group models and metrized Hodge lines, not about the stable height, so it is a genuine and
smaller glue statement.

### 2.2 Why `HeightCopiesAgree` is a piece

R18 and R22 are stated over leaf-push2's copy of the height. leaf-adopt2 recorded this as a glue
target. The copies duplicate `FinExt`, `HermitianLattice`, `HodgeData`, `GroupModel` and
`MetrizedModel`, so the transport needs equivalences of all of them. It was not attempted
(SPECULATIVE: medium).

### 2.3 New proof: `X1BelyiOnModel` from `BelyiX1`

`G0Split.x1BelyiOnModel_of_belyiX1 : LeafModCurves.BelyiX1 → X1BelyiOnModel` (VERIFIED, standard
axioms). The proof:
- `IsJ1 N J` supplies the curve `X`, `IsJacobian` and `φ : ℚ(X) ≃+* K_N`.
- `isBelyiFunction_map` moves the Belyi property along `φ.symm.toRatAlgEquiv`, using
  `ValuationSubring.comap` and `mem_nonunits_iff_or`.
- `image_mem`: the image of `ℚ(j)` under any ring hom `g` lies in `ℚ(g j)` (`num/denom`,
  `Polynomial.ringHom_ext`, `eq_ratCast`). So `ℚ(t) = g(ℚ(j))` for `t = g(j/1728)`.
- `Algebra.finrank_eq_of_equiv_equiv` then gives `[ℚ(X):ℚ(t)] = [K_N:ℚ(j)] ≤ N²`.
- Positivity comes from `IntermediateField.adjoin.finiteDimensional`.

About 110 lines. It took two compile runs against the prefix olean (`x1transport/`), then
the tail and the final full run.

## 3. Check of the diff (VERIFIED by script, plus reading)

- **Statement diff** (`stmt_diff.py`). It compares every declaration of 883c4ddf's `Leaves.lean`
  (1683, keyed by namespace and name, comments stripped) with the new file; for theorems it compares
  the statement, for definitions the whole text.
  - Changed: only `HSyn.TextbookLeaves`, `HSyn.glueOutputs_of_leaves`,
    `HSyn.sixContactMin_of_leaves`.
  - Removed: only the `opaque HSyn.T10_TateDuality`.
  - Every leaf `def` and every other theorem statement is unchanged.

  The bundle change is exactly §1.3:
  - one placeholder made concrete (T10);
  - five fields removed, each proved;
  - two fields narrowed to weaker statements (T17 to the cyclic case, T18 to Chebotarev's
    existence form); in each case the form the glue uses is proved from the narrower one;
  - two fields added (T36-T40 as one bundle, T41).

  **Nothing is strengthened**: no field became stronger. The new leaves are the published
  statements or consequences of them, per their tasks' reviews, which I did not redo.
- **G0's hypotheses** are exactly `ResearchLeaves`, `TextbookLeaves`, `GluePieces` (read from the
  compiled signature). g0-split's `hR18`, `hR22` and its ten separate hypotheses are gone.
  - `GluePieces` is g0-split's ten pieces, minus piece 3 (proved), with piece 5 replaced by the
    smaller `ProductModelHeight`, plus `HeightCopiesAgree`.
  - Is `ProductModelHeight` stronger than `HeightAdditivity`? As a statement about all group
    models it is not a consequence of `HeightAdditivity`. It is the model-level fact behind it
    (Faltings 1983 §1: `ω` of a product is the direct sum, STANDARD). Reported as a change of
    glue, not of a leaf.
- **Fold diff** (`fold_diff.py`). It compares each task's declarations with the copies in
  `Leaves.lean`. All are identical except four:
  - `TSkolemKW.C10.{brauerNesbittChar0', c10_of_chebotarev}` now refer to `GlueC10`'s originals,
    of which the task had identical copies.
  - `T10Etale.T10_groupIso_of_linIso` concludes `ZInQ.LeafPush2.T10_groupIso`, the identical
    original.
  - `E1Sub.bcPt` lost the `rfl`.
- **Change of meaning in hodge-lattice** (reported by its subagent). The kernel's `ZInQ.DefFaltings`
  has no `AbVar` of its own and uses `PkgI3.AbVar`. `Leaves.lean`'s `ZInQ.DefFaltings` has its
  own copy, and its `HodgeLatticeTheorem` is over it. So hodge-lattice's new Props
  (`RegularAtOrigin`, `DimAtOrigin`, `DimBaseChange`, …) are here over `ZInQ.DefFaltings.AbVar`,
  which carries the same data. h5-neron needed a copy of `AbVar.zero` for that structure
  (`ZInQ.H5Neron.AbVar.zero`).

## 4. What remains

1. **The ten glue pieces** of §2. They are the only Lean work between the leaves and H.
   `ModularConstituent` is the bulk (Glazer's Section 4 on the actual surface).
2. Placeholders: R1(b) and R17. def-ladic-cond's `CarayolR17'` is still not folded.
3. Premises not in G0's hypotheses:
   - Lemma P (rv-qm-polar);
   - AN3 (`AnalyticUniformizationExists`, `…Unique`; `HodgeLatticeTheorem` now reduced);
   - Pazuki's coordinates (R22).
4. Reductions not applied to the bundles:
   - pi0-x6's `R2X6CMExact`, `AGInputs`, if R1's clause is to be derived;
   - h5-neron's N2 and glue, if H5's identity is to be derived;
   - G1-adelic, not copied;
   - the global T20, T21 from the local forms.
5. Unification of the duplicated layers (WP1). This would also discharge `HeightCopiesAgree`.
