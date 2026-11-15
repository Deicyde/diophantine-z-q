# p1-scheme: manual-fold data for `OpenGlue7.quotientP1Coordinate` (HEAD 3782dac8e)

Read-only research; nothing compiled. File:line are at HEAD. Paths relative to the worktree root.

## 0. Summary (key findings)

* `g : OpenGlue7` is read in **exactly one place**: `glue6_of_open7` (TailX.lean:274-275). Every top theorem from
  `sixContactMin_of_open8` to `sixContactMin_of_open25` passes `g` through unchanged.
* L1-L6 **already exist as chain constants** `HDec.MCRGlue.{ProperCurveAF,…,TameInertiaCyclic}` (TailW.lean:337-412).
  They are verbatim mcr-glue (`MCRGlue2.lean.part`) copies. None is a bundle field.
* `CurveBijIso` is **proved, with no hypotheses**: `HDec.HSyn.curveBijIso_lf7 : ModelGlue.CurveBijIso` (TailX.lean:49,
  `:= _root_.CurveSplit.curveBijIso`, TailR.lean:1381). It does not need a field.
* T5 (`ObjBridge.TorsionStructure`) is **derived** from the textbook field `t.mumfordTorsionAlgClosed`. It does not need
  a field.
* `ModelYIrreducible` is **derivable** from the fields `l.deligneComponentsY3PrintedAb` and `r.mumfordRigidityCore`
  (chain below, §5). It does not need a field.
* `CMStabObj` and `ModelYIrreducible` exist **only in scratch**: scratch/mcr-quot/MCRQuot.lean:7648 and :7336, with
  the same text in scratch/gap-triage/MCRQuotNV.lean.
* **Caveat:** the scratch composite `GapTriageMCR.modelCoordinateResidue_final10` (MCRQuotNV.lean:8793) also takes
  `hP : P1SchemeQ`. That statement is not in the list you were given. It is this worktree's task, presumably. So
  either p1-scheme proves `P1SchemeQ`, or `P1SchemeQ` becomes another new field.
* **Caveat:** every mcr-quot composite returns `ModelCoordinateResidue`, never `QuotientP1Coordinate`. To keep
  `OpenGlue7`'s type and leave the downstream chain alone, build `QuotientP1Coordinate` with
  `HDec.MCRGlue.quotientP1Coordinate_of_leaves` (TailW.lean:487), feeding it glue A/B/C made from mcr-quot's
  reductions (§6). The alternative is to reroute to `OpenGlue6.modelCoordinateResidue`.
* **Porting cost:** MCRQuot.lean is MCRGlue.lean (4564 lines) followed by 28 parts. The chain (TailW) contains only
  MCRGlue parts 1-3. The fold therefore needs, in `namespace HDec` after TailW:
  * `MCRGlue4.lean.part` (`CMSectionsDisjoint`, `CoordinateFromSections`, `coordinateNormalization_of`);
  * `MCRGlue5.lean.part` (`hecke_mem_fibreAut`);
  * all of `MCRQuot{1..24,6b,8b}.lean.part`, in the order of scratch/mcr-quot/build.sh.

  `CMSectionsDisjoint` and `hecke_mem_fibreAut` are NOT FOUND in ZInQKernel/.

## 1. Consumers of `quotientP1Coordinate` and `modelCoordinateResidue`

### Definitions

`HDec.MCRGlue.QuotientP1Coordinate`, ZInQKernel/OneProof/H/TailW.lean:202:
```lean
def QuotientP1Coordinate : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∃ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵) (ρ' : ToP1 𝒵.left),
      IsFinite q.left ∧ IsP1Coordinate 𝒵 ρ' ∧ CoordFibres 𝒴 𝒜 (ρ'.comp q.left)
```
`IsP1Coordinate` is defined at TailW.lean:182.

`HDec.MCRGlue.modelCoordinateResidue_of_quotient'`, TailW.lean:679:
```lean
theorem modelCoordinateResidue_of_quotient' (hQ : QuotientP1Coordinate) :
    ModelCoordinateResidue :=
  modelCoordinateResidue_of_quotient hQ specialFibreTranscendence
```
It relies on:
* `modelCoordinateResidue_of_quotient (hQ : QuotientP1Coordinate) (hS : SpecialFibreTranscendence) : ModelCoordinateResidue`
  (TailW.lean:232);
* `specialFibreTranscendence` (TailW.lean:674), which is proved.

`HDec.ModelGlue.ModelCoordinateResidue`, ZInQKernel/OneProof/H/TailL.lean:975 (namespace `HDec.ModelGlue`):
```lean
def ModelCoordinateResidue : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∃ ρ : ToP1 𝒴.left, CoordFibres 𝒴 𝒜 ρ ∧
      ∀ (ξ : 𝒴.left) (_ : IsDomain (𝒴.left.presheaf.stalk ξ)),
        IsDiscreteValuationRing (𝒴.left.presheaf.stalk ξ) →
        IsLocalRing.maximalIdeal (𝒴.left.presheaf.stalk ξ) =
          Ideal.span {(p : 𝒴.left.presheaf.stalk ξ)} →
        ∃ hξ : ξ ∈ ρ.U,
          Transcendental (⊥ : Subfield (IsLocalRing.ResidueField (𝒴.left.presheaf.stalk ξ)))
            (IsLocalRing.residue _ (𝒴.left.presheaf.germ ρ.U ξ hξ ρ.f))
```

### The field and its single reader (TailX.lean, namespace `HDec.HSyn`)

TailX.lean:184-187:
```lean
structure OpenGlue7 : Prop where
  /-- mcr-glue: a finite `q : 𝒴 → 𝒵` over `ℤ_(p)` and an isomorphism `𝒵 ≅ P¹_{ℤ_(p)}` by charts whose composite
  has R2fp's fibre relation (replaces `modelCoordinateResidue`). -/
  quotientP1Coordinate : MCRGlue.QuotientP1Coordinate
```
TailX.lean:274-275, the **only reader of `g.quotientP1Coordinate`**:
```lean
theorem glue6_of_open7 (g : OpenGlue7) : OpenGlue6 where
  modelCoordinateResidue := MCRGlue.modelCoordinateResidue_of_quotient' g.quotientP1Coordinate
```
TailX.lean:280-283:
```lean
theorem sixContactMin_of_open7 (r : OpenResearchLeaves7) (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7)
    (g : OpenGlue7) (h20 : G0Split.R20Lower) : ZInQ.SixContactMin :=
  sixContactMin_of_open6 (researchLeaves5_of_open7 r l) (textbookLeaves6_of_open7 t l) (addedLeaves6_of_open7 r t l)
    (glue6_of_open7 g) h20
```

### Downstream of `modelCoordinateResidue` (TailO.lean)

The field, TailO.lean:2846-2849:
```lean
structure OpenGlue6 : Prop where
  ...
  modelCoordinateResidue : ModelGlue.ModelCoordinateResidue
```
Its only reader, TailO.lean:2910-2913:
```lean
theorem glue4_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6)
    (g : OpenGlue6) : OpenGlue4 where
  heckeVertWitness := heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 (torsionStructure_ofK5 t.t5)
    g.modelCoordinateResidue l.curveBijIso
```
This is used by `sixContactMin_of_open6` (TailO.lean:2922-2925).

* `heckeVertWitness_of_leaves5` is at TailN.lean:38. It calls `ModelGlue.heckeVertWitness_of_curveBijIso`
  (TailL.lean:2425).
* There is an older parallel copy: TailN.lean:206 `modelCoordinateResidue : ModelGlue.ModelCoordinateResidue`, read
  at TailN.lean:257 `g.modelCoordinateResidue l.curveBijIso`. That is the leaf-fold5 generation, not on the current
  path through `glue6_of_open7`.

### Pass-through of `g : OpenGlue7`, open8 to open25

Each line below is `theorem …(g : OpenGlue7)…`. In every case the body passes `g` unchanged:

| file:line | theorem | passes `g` to |
|---|---|---|
| TailZ4.lean:259 | `sixContactMin_of_open8` | `sixContactMin_of_open7 … g (r20Lower_of8 r t hF5)` |
| TailZ9.lean:146 | `_open9` | `_open8` |
| TailZ11.lean:58 | `_open10` | `_open9` |
| TailZ13.lean:69 | `_open11` | `_open10` |
| TailZ15.lean:133 | `_open12` | `_open11` |
| TailZ17.lean:278 | `_open13` | `_open12` |
| TailZ18.lean:1251 | `_open14` | `_open13` |
| TailZ19.lean:1914 | `_open15` | `_open14` |
| TailZ22.lean:336 | `_open16` | `_open15` |
| TailZ23.lean:812 | `_open17` | `_open11`, directly |
| TailZ24.lean:836 | `_open18` | `_open17` |
| TailZ25.lean:136 | `_open19` | `_open18` |
| TailZ26.lean:192 | `_open20` | `_open19` |
| TailZ27.lean:124 | `_open21` | `_open20` |
| TailZ28.lean:123 | `_open22` | `_open21` |
| TailZ29.lean:120 | `_open23` | `_open22` |
| TailZ30.lean:73 | `_open24` | `_open23` |
| TailZ31.lean:69 | `sixContactMin_of_open25` | `_open24` |

The top theorem at TailZ31.lean:69-70:
```lean
theorem sixContactMin_of_open25 (r : OpenResearchLeaves19) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves16) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open24 r t (openAddedLeaves15_of_OpenAddedLeaves16 l) g
```
`ZInQ.OneProof.frozenTarget` (ZInQKernel/OneProof/Main.lean:56-68) takes `(g : HDec.HSyn.OpenGlue7)` (Main.lean:59)
and calls `HDec.HSyn.sixContactMin_of_open25 r t l g`.

### Non-Lean mentions

These need regenerating after the fold:
* docs/one-proof/kinds.tsv:60;
* docs/one-proof/OPEN.md:67,160,296-306;
* docs/one-proof/open-statements.json, claims.tsv, frontier-crosswalk.tsv;
* scratch/contrib-kit/DischargesTest.lean:9 (`t1 (h : HDec.MCRGlue.QuotientP1Coordinate)`, a test fixture).

## 2. Which statements exist as Lean constants

| statement | in ZInQKernel/ (file:line, full name) | scratch only? | bundle field at HEAD? |
|---|---|---|---|
| L1 `ProperCurveAF` | TailW.lean:337 `HDec.MCRGlue.ProperCurveAF` | also MCRGlue/MCRQuot/MCRQuotNV.lean:4044 | no |
| L2 `FiniteQuotientExists` | TailW.lean:350 `HDec.MCRGlue.FiniteQuotientExists` | also scratch :4057 | no |
| L3 `TameQuotientSmooth` | TailW.lean:365 `HDec.MCRGlue.TameQuotientSmooth` | also scratch :4072 | no |
| L4 `SmoothModelOfP1` | TailW.lean:379 `HDec.MCRGlue.SmoothModelOfP1` | also scratch :4086 | no |
| L5 `TameFixedPointsDisjoint` | TailW.lean:393 `HDec.MCRGlue.TameFixedPointsDisjoint` | also scratch :4100 | no |
| L6 `TameInertiaCyclic` | TailW.lean:412 `HDec.MCRGlue.TameInertiaCyclic` | also scratch :4119 | no |
| T5 `ObjBridge.TorsionStructure` | ZInQKernel/HDecomp/Objects.lean:1486 `_root_.ObjBridge.TorsionStructure`, exported as `HDec.ObjBridge.TorsionStructure` (LPrefix.lean:95). Objects.lean:1494 has `theorem torsionStructure_iff : ObjBridge.TorsionStructure ↔ PkgI2.TorsionStructure.{0} := Iff.rfl`. `PkgI2.TorsionStructure` (universe-polymorphic) is at Objects.lean:993. | — | not a field; derived from `t.mumfordTorsionAlgClosed` (TailZ11.lean:19) |
| `CurveBijIso` | TailL.lean:1691 `HDec.ModelGlue.CurveBijIso`; TailR.lean:60 `_root_.ModelGlue.CurveBijIso` (same text) | also scratch :2954 | no; **proved**: `_root_.CurveSplit.curveBijIso` (TailR.lean:1381), `HDec.HSyn.curveBijIso_lf7` (TailX.lean:49) |
| `ModelYIrreducible` | NOT FOUND under this name. Same body as `HDec.PropTSGlue.HeckeIrreducible` (TailG.lean:3919), checked by `rfl` in GlueProbe.lean:25 | MCRQuot.lean:7336, MCRQuotNV.lean:7336 (`MCRQuot.ModelYIrreducible`, top-level) | no; derivable (§5) |
| `CMStabObj` | NOT FOUND | MCRQuot.lean:7648, MCRQuotNV.lean:7648 (`MCRQuot.CMStabObj`) | no |
| (`P1SchemeQ`, not in your list) | NOT FOUND | MCRQuot.lean:8549, MCRQuotNV.lean:8549 (`MCRQuot.P1SchemeQ`) | no |

Bundles at HEAD:
* `OpenResearchLeaves19`: TailZ29.lean:14.
* `OpenTextbookLeaves10`: TailZ11.lean:17, 14 fields, including `mumfordTorsionAlgClosed : _root_.AvSplit.MumfordTorsionAlgClosed` (TailZ11.lean:19).
* `OpenAddedLeaves16`: TailZ31.lean:14, 14 fields.
* `OpenGlue7`: TailX.lean:184, 1 field.

None of the listed statements is a field of any of these. The fields `mumfordRigidityCore` (OpenResearchLeaves19) and
`deligneComponentsY3PrintedAb` (OpenAddedLeaves16) exist and feed `ModelYIrreducible`.

The scratch files are top-level: `MCRGlue`, `ModelGlue`, `MCRQuot`, `PropTSGlue` with no `HDec`. TailW's copies are in
`HDec`. Some dependencies of `CMStabObj` are kernel constants (namespaces not checked):
* `HasCM4`/`HasCM3`/`HasCM24`: HDecomp/QM/Pairs.lean:86-90;
* `M3`, `M3.twist`, `M3.rightMul`: HDecomp/QM/Structures.lean:294, 334, 338;
* `QML3` and `LeafQM.O` were not located.

## 3. Kinds

### mcr-glue.md §3 table (docs/research/mcr-glue.md:117-122), quoted

```
| L1 `ProperCurveAF` | … | Lichtenbaum, Amer. J. Math. 90 (1968), Thm 2.8 (projectivity); EGA II 4.5.4 / Liu, *AGAC*, Prop. 3.3.36 | composite (2 results) |
| L2 `FiniteQuotientExists` | … | SGA 1 Exp. V, Prop. 1.8 (existence), Prop. 1.1 (integral) | leaf (special case) |
| L3 `TameQuotientSmooth` | … | SGA 1 Exp. V (tame base change), Mumford, *Abelian Varieties* §7 Thm 3; normal curves over perfect fields are smooth; EGA IV 17.5.1 | composite (3 results) |
| L4 `SmoothModelOfP1` | … | Liu, *AGAC* §8.3, §10.1 (genus-0 smooth fibre with a section) | STANDARD |
| L5 `TameFixedPointsDisjoint` | … | Edixhoven, Compositio 81 (1992), Prop. 3.4 (smoothness of tame fixed loci), plus "finite étale over a DVR" | leaf consequence |
| L6 `TameInertiaCyclic` | … | Serre, *Local Fields* Ch. IV §2, Cor. 1 of Prop. 7; faithfulness from L5's source | composite (2 results) |
```

### mcr-quot.md (docs/research/mcr-quot.md)

* :38-42: "T5 is the kernel's textbook leaf `ObjBridge.TorsionStructure`." / "`CurveBijIso` is model-glue's textbook
  leaf (it is in the prefix)." / "`ModelYIrreducible` says that `Y` is irreducible over `ℚ`. It is proved from the
  decomposition's existing glue `CoverModelOfHeckeN` together with T5 (`modelYIrreducible_of_coverModelN`)."
* :205: "| (B-P¹) `P1SchemeQ` | … | glue (foundations; Hartshorne II.7.1, EGA II 4.2.4, locators UNVERIFIED) | …"
* :206: "| (C1b-obj) `CMStabObj` | a CM object's class is fixed by some `T = twist α ∘ rightMul u` with `T ∘ T = id` on
  `M3 ℚ̄` and `T ≠ id` | glue (QM with CM; elliptic points of orders 4, 6, 2, Baba–Granath §3.1, locator UNVERIFIED) |"

### gap-triage.md (docs/research/gap-triage.md)

* :30-39, finding 3: "`CoverModelOfHeckeN` and Lemma NV are not needed under the glue field (VERIFIED, compiled in
  GlueProbe) … So mcr-quot's composite needs only L1–L6, T5, `CurveBijIso`, `P1SchemeQ` and `CMStabObj`."
* :79: "| A3 | `P1SchemeQ` from CloudW07, plus the NV-free mcr-quot composite | glue: 2 of mcr-quot's 3 glue Props | T1 | high |"
* :88: "| A12 | `CMStabObj` (glue under `quotientP1Coordinate`) | glue: 1 | T2 | medium-low |"
* :453: planned `theorem GapGlue.cmStabObj_of (hC : HDec.QMSplit.Aut.QMCentralizerCMC) (hT : ObjBridge.TorsionStructure) : MCRQuot.CMStabObj`.
  This is NOT FOUND in Lean; `qmCentralizerCMC` is no longer a field at HEAD.

### leaf-fold9.md:382-394: earlier fold rejected

"(1) mcr-quot … Not taken. Replacing the project glue `QuotientP1Coordinate` (1 strict GLUE) by mcr-quot's inputs
would add: L1 `ProperCurveAF` (composite), L3 `TameQuotientSmooth` (composite) and L6 `TameInertiaCyclic`
(composite); L5 `TameFixedPointsDisjoint` (consequence); L2 `FiniteQuotientExists` (special case) and L4
`SmoothModelOfP1` (STANDARD); the two new glue Props `P1SchemeQ` and `CMStabObj`; and `CoverModelOfHeckeN`. T5 and
`CurveBijIso` are theorems in the chain. That is at least −1 + 6 on the strict count, and −1 + 5 on the lenient count."

(`CoverModelOfHeckeN` has since been replaced by `ModelYIrreducible` from existing fields, per gap-triage.)

### docs/one-proof/kinds.tsv rows

Columns: bundle, field, kind, flag, strict, strictest, source, rated_by, packet, label, tier, flag_class, area_issue.

* :60 `glue	quotientP1Coordinate	project glue		GLUE	GLUE	a finite q : Y -> Z over Z_(p) and Z = P^1_{Z_(p)} by charts with R2fp's fibre relation for the composite: the tame quotient Y/Gamma' = P^1 (SGA 1 Exp. V); no quotient schemes or P^1_{Z_(p)} in Mathlib 4.35	leaf-fold10 table (mcr-glue; folded by leaf-fold7)		wave	T3		elliotglazer/diophantine-z-q#37`
* :40 `textbook	mumfordTorsionAlgClosed	published		LEAF	LEAF	A(k)[n] = (Z/n)^{2g} over k algebraically closed, char k not dividing n: Mumford, Abelian varieties 4, Application 2 (iv) …`
* :15 `research	mumfordRigidityCore	published	locator UNVERIFIED (see the source)	LEAF	LEAF	Mumford, Geometric Invariant Theory, Thm 6.14 and Cor. 6.4 (numbers UNVERIFIED)	route-a-fold …`
* :48 `added	deligneComponentsY3PrintedAb	published	pending reading: depends (medium), whether one display states that the PEL moduli scheme with its uniformization is the canonical model at B = (2,-3|Q), level K3 (Deligne 389 section 5, Milne 2005 section 14)	GLUE	GLUE	Deligne, Sem. Bourbaki 389 (1971) Thm 2.4 and 3; …`

So it is strict GLUE because of the pending reading.

The other kinds.tsv found is scripts/claims/fixtures/kinds.tsv, a test fixture.

### docs/one-proof/OPEN.md:296-298

"### quotientP1Coordinate / * Bundle field `HDec.HSyn.OpenGlue7.quotientP1Coordinate`; kind **project glue**, strict
**GLUE**." It is held by the project (claim link: branch wip/mcr-quot), OPEN.md:67.

## 4. GLUE counts at HEAD, and the definition of strict / strictest

OPEN.md:14-19 (identical block in STATUS.md:23-29):
```
**59 hypotheses of the H part** (in the bundles `OpenAddedLeaves16`, `OpenGlue7`, `OpenResearchLeaves19`, `OpenTextbookLeaves10`), plus 7 hypotheses of the Tian–Yuan–Zhang and Gross–Zagier parts listed at the end.

* **Strict count: 45 published / 14 glue** (the strictest flagged reading; 46/13 without the one strictest-reading flag).
* LEAF means a published, refereed theorem stated over genuine definitions in its printed form, or a consequence
  of it that is never stronger. GLUE is everything else: a consequence of one theorem, a composite of several,
  project glue, or a leaf whose published form is still pending a reading (`kinds.tsv`, column `flag`).
* By kind: composite 4, consequence 7, project glue 1, published 47.
```
So "strict 46/13" is 46 LEAF / 13 GLUE, and "strictest 45/14" is 45 LEAF / 14 GLUE.

I recounted from kinds.tsv. It has 66 rows: 59 H rows (research 30, textbook 14, added 14, glue 1) plus 7
frozenTarget rows. The H rows give strict GLUE 13 and strictest GLUE 14. The one row where the columns differ is
`weilPairingMumford` (added, LEAF/GLUE). `quotientP1Coordinate` is GLUE/GLUE, kind "project glue", and is the only
"project glue" row.

Definitions:
* scripts/one_proof/seed_kinds.py:74-77, the original rule (kinds.tsv is now the source of truth):
  ```python
  def strict(r):
      return 'LEAF' if r['kind'] == 'published' and not r['flag'].startswith('pending') else 'GLUE'
  def strictest(r):
      return 'GLUE' if r['flag'].startswith('strictest') else strict(r)
  ```
  So strict is LEAF only for kind `published` with no `pending…` flag. Kinds `consequence`, `composite` and
  `project glue` are always GLUE. Strictest additionally counts GLUE any row flagged "strictest reading: …".
* render_open.py:151-153 enforces that flag_class `strictest` is set exactly when strict ≠ strictest.
* render_open.py:255-294 computes the headline from the strictest column, with strict in parentheses.
* autofold.py docstring: a fold may not raise either GLUE count (strict or strictest) without `--allow-rise`. A new
  published leaf with no flag gets "unread: new printed leaf…" and counts LEAF. A "pending reading" flag counts GLUE.

Implication, as in leaf-fold9 §5: removing `quotientP1Coordinate` gives −1. Adding the L1-L6 kinds above gives +4
(L1, L3, L6 composite; L5 consequence) to +6 (if L2 "special case" and L4 "STANDARD" also count GLUE). `CMStabObj`
adds +1 (glue). `P1SchemeQ` adds +1 unless proved. T5, `CurveBijIso` and `ModelYIrreducible` add nothing (derived).
So the fold needs `--allow-rise`, or a lead ruling.

Also note autofold puts new leaves "into the bundle of the field they replace", which here is the glue bundle.

## 5. `deligneComponentsY3PrintedAb`, `L_iff_ab`, `mumfordRigidity_of_core`, and `ModelYIrreducible`

**The field.** OpenAddedLeaves16, TailZ31.lean:22-25:
```lean
  /-- shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
  components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
  389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED). -/
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb
```
Its statement, ZInQKernel/OneProof/H/TailZ17.lean:54-55 (namespace `_root_.ShimuraGlue`):
```lean
def DeligneComponentsY3PrintedAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ DelignePi0 Y K3
```
The non-Ab form is TailZ12.lean:1324: `def DeligneComponentsY3Printed : Prop := ∃ (Y …) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ DelignePi0 Y K3`.

**`L_iff_ab` is a naming schema, not a constant.** NOT FOUND as a declaration; it appears only in comments and docs.
route-a-fold.md:51: "Each old field is filled by `(L_iff_ab (mumfordRigidity_of_core r.mumfordRigidityCore)).mpr`
applied to the new field". The instance for this row is TailZ17.lean:99-102 (namespace `_root_.LeafQM.AV.R1UnivRigid`):
```lean
theorem deligneComponentsY3Printed_iff_ab (hR : MumfordRigidity) :
    ShimuraGlue.DeligneComponentsY3Printed ↔ ShimuraGlue.DeligneComponentsY3PrintedAb := by
  unfold ShimuraGlue.DeligneComponentsY3Printed ShimuraGlue.DeligneComponentsY3PrintedAb
  rw [r1fpProps_eq_ab' hR]
```

**`mumfordRigidity_of_core`.** TailZ16.lean:530 (namespace `_root_.LeafQM.AV.R1UnivRigid`):
```lean
theorem mumfordRigidity_of_core (hC : MumfordRigidityCore) : MumfordRigidity := by
```
* `MumfordRigidityCore`: TailZ16.lean:463. `MumfordRigidity`: TailZ16.lean:76.
* `r1fpProps_eq_ab' (hR : MumfordRigidity) : (R1fpProps : …) = R1fpPropsAb`: TailZ16.lean:431.
* The input is the field `mumfordRigidityCore : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidityCore` of OpenResearchLeaves19 (TailZ29.lean).
* The chain uses it at TailZ23.lean:708-709 and 756-758:
  ```lean
  theorem mumfordRigidity_of14 (r : OpenResearchLeaves14) : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidity :=
    _root_.LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core r.mumfordRigidityCore
  …
    deligneComponentsY3Printed :=
      (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsY3Printed_iff_ab (mumfordRigidity_of14 r)).mpr
        l.deligneComponentsY3PrintedAb
  ```
  It is also at TailZ17.lean:216 and 269-271, as `mumfordRigidity_of11`.

**Lemmas on the ModelYIrreducible chain:**
* TailZ12.lean:1346 (namespace `_root_.ShimuraGlue`):
  `theorem deligneComponentsY3_of_printed (h : DeligneComponentsY3Printed) : ShimuraSplit.DeligneComponentsY3`
* TailZ12.lean:1207 (namespace `_root_.ShimuraSplit`):
  `theorem y3Connected_of_deligne (h : DeligneComponentsY3) : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ ConnectedSpace Y.left`
* TailG.lean:8352: `def Y3Connected : Prop := ∃ (Y …) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ ConnectedSpace Y.left`
  (`HDec.TSHecke`; namespace inferred from GlueProbe's usage).
* TailG.lean:8380: `theorem heckeIrreducible_of_connected (hC : Y3Connected) : HeckeIrreducible` (`HDec.TSHecke`).
* TailG.lean:3919 (`HDec.PropTSGlue`):
  ```lean
  def HeckeIrreducible : Prop :=
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π → IrreducibleSpace Y.left
  ```

**GlueProbe.** scratch/gap-triage/GlueProbe.lean:1 imports `ZInQKernel.OneProof.H.TailZ13`; per gap-triage.md:5 it
compiled (exit 0). Lines 17-36:
```lean
namespace GapTriage

/-- `MCRQuot.ModelYIrreducible`, verbatim body. -/
def ModelYIrreducibleCopy : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π → IrreducibleSpace Y.left

/-- The chain's `HeckeIrreducible` is `ModelYIrreducible` (definitional). -/
example : HDec.PropTSGlue.HeckeIrreducible = ModelYIrreducibleCopy := rfl

/-- `ModelYIrreducible` from the bundle field `deligneComponentsY3Printed`: no `CoverModelOfHeckeN`,
no Lemma NV. -/
theorem modelYIrreducible_of_open9 (l : HDec.HSyn.OpenAddedLeaves9) : ModelYIrreducibleCopy :=
  HDec.TSHecke.heckeIrreducible_of_connected
    (_root_.ShimuraSplit.y3Connected_of_deligne
      (_root_.ShimuraGlue.deligneComponentsY3_of_printed l.deligneComponentsY3Printed))

end GapTriage

#print axioms GapTriage.modelYIrreducible_of_open9
```
Lines 38-52 hold the `#check`s of the CloudW07 P¹ toolkit for `P1SchemeQ`: `projectiveLineOver`, `isProper_toSpec`,
`smoothOfRelativeDimension_toSpec`, `chartSpecIso`, `isAffineOpen_chart`, `polyEquivChart`,
`ProjectiveSpace.homOfSections`, `homOfSections_preimage_standardOpen`, `hom_ext`, `instIsProper`, `normalized`,
`normalized_eq_of_mul_eq_one`, `relativeChartCoordinate_mul`, `Scheme.Cover.glueMorphisms`.

**HEAD equivalent (UNCOMPILED sketch, inside `namespace HDec.HSyn`):**
```lean
theorem modelYIrreducible_of_open25 (r : OpenResearchLeaves19) (l : OpenAddedLeaves16) :
    PropTSGlue.HeckeIrreducible :=
  TSHecke.heckeIrreducible_of_connected
    (_root_.ShimuraSplit.y3Connected_of_deligne
      (_root_.ShimuraGlue.deligneComponentsY3_of_printed
        ((_root_.LeafQM.AV.R1UnivRigid.deligneComponentsY3Printed_iff_ab
            (_root_.LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core r.mumfordRigidityCore)).mpr
          l.deligneComponentsY3PrintedAb)))
```

**T5 and `CurveBijIso` in the chain:**
* T5 at HEAD: `ObjBridge.torsionStructure_iff.mpr (torsionStructure_ofK5 (_root_.AvSplit.Final.h25 t.mumfordTorsionAlgClosed))`.
  The pieces:
  * `h25 (hT : AvSplit.MumfordTorsionAlgClosed) : PkgI2.TorsionStructure.{0}` (TailQ.lean:2366);
  * `torsionStructure_ofK5 (h : _root_.PkgI2.TorsionStructure.{0}) : PkgI2.TorsionStructure.{0}` (TailM.lean:419);
  * TailN.lean:42-43 does exactly `(ObjBridge.torsionStructure_iff.mpr hT)`.

  A shorter route is `_root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed` (TailQ.lean:1301;
  used at TailZ23.lean:719), then `torsionStructure_iff.mpr`, which is `Iff.rfl`.
* `CurveBijIso`: `HDec.HSyn.curveBijIso_lf7` (TailX.lean:49).
* `CMStabObj`: NOT FOUND anywhere in ZInQKernel/; not a field and not derived.

**`quotientP1Coordinate_of_leaves`, full signature.** TailW.lean:487-490 (namespace `HDec.MCRGlue`):
```lean
theorem quotientP1Coordinate_of_leaves (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (gA : FibreAutTame) (gB : GenericQuotientP1)
    (gC : CoordinateNormalization) : QuotientP1Coordinate := by
```
* Glue defs: `FibreAutTame` TailW.lean:432, `GenericQuotientP1` :446, `CoordinateNormalization` :469.
* Also `modelCoordinateResidue_of_leaves` (TailW.lean:505, plus `hS : SpecialFibreTranscendence`) and
  `modelCoordinateResidue_of_leaves'` (TailW.lean:684, without hS).
* Neither T5 nor `CurveBijIso` nor `CMStabObj` appears in TailW. Those enter only through mcr-quot's reductions of A/B/C.

## 6. The scratch composite, and how to reach `QuotientP1Coordinate`

scratch/gap-triage/MCRQuotNV.lean:8793 (MCRQuot.lean verbatim through :8719, then this):
```lean
theorem modelCoordinateResidue_final10 (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hYI : ModelYIrreducible) (hP : P1SchemeQ) (hO : CMStabObj) : ModelCoordinateResidue :=
  modelCoordinateResidue_final4 hAF hQE hTS hP1 hFix hCyc hT hC hYI quotientDescendsQ
    (toP1BijIsCoordinateQ_of hC hP) (cMStabInvolution_of hC hYI hO)
```
(namespace `GapTriageMCR`, `open MCRQuot MCRGlue ModelGlue LeafQM LeafQM.AV`)

mcr-quot reductions that give glue A, B, C directly (all MCRQuot.lean, namespace `MCRQuot` unless noted):
* A: `fibreAutTame_of'' (hT) (hC) (hYI) (hF : CurveClosedQbarFinite) : FibreAutTame` (:7434). Takes
  `curveClosedQbarFinite` (:7522, proved). Or use `fibreAutTame_of' hT (fibreAutFixFinite_of' hC hYI)` (:6660, :7594).
* B: `genericQuotientP1_of'' (hA : FibreAutTame) (hT) (hTS) (hC) (hP : P1SchemeQ) : GenericQuotientP1` (:8680).
* C: `MCRGlue.coordinateNormalization_of (h1 : CMSectionsDisjoint) (h2 : CoordinateFromSections) : CoordinateNormalization`
  (:4483, from MCRGlue4.part), with:
  * C1 = `cMSectionsDisjoint_of'' (hA) (hfix : FibreAutFixFinite) (hI : CMStabInvolution) : CMSectionsDisjoint` (:6956);
  * `hI` = `cMStabInvolution_of hC hYI hO` (:7676);
  * `hfix` = `fibreAutFixFinite_of' hC hYI`;
  * C2 = `coordinateFromSections_of'' (hA) (hT) : CoordinateFromSections` (:7299).

So, UNCOMPILED sketch:
```lean
quotientP1Coordinate := MCRGlue.quotientP1Coordinate_of_leaves hAF hQE hTS hP1 hFix hCyc gA
  (genericQuotientP1_of'' gA hT hTS hC hP)
  (coordinateNormalization_of (cMSectionsDisjoint_of'' gA (fibreAutFixFinite_of' hC hYI) (cMStabInvolution_of hC hYI hO))
    (coordinateFromSections_of'' gA hT))
-- where gA := fibreAutTame_of' hT (fibreAutFixFinite_of' hC hYI)
```
This builds an `OpenGlue7` value at the top level from the new bundle plus `r`, `t`, `l`. The chain below
`sixContactMin_of_open25` stays unchanged. `QuotientP1Coordinate` itself is not referenced by any mcr-quot part, so
this assembly is new (not compiled anywhere).
