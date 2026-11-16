# gr14-narrow: Gaudron–Rémond (R19, `gaudronRemondThm14`) narrowed to the forward direction

Task gr14-narrow (re-triage triage2 §1, Task 6). Base: fork main `43513d87` (leaf-fold25).

## Result

**The research field `gaudronRemondThm14` (`HDec.HSyn.OpenResearchLeaves22`, row R19) can be replaced by its first
conjunct, the new leaf `GapGR.GaudronRemondThm14Fwd`.** No field is removed. The second conjunct (an isogeny `B → A`
of degree `≤ κ(A)`) was read on the live path only for the existence of an isogeny `B → A`. That existence is now
proved from the quasi-inverse leaf that the chain already carries (`milneIsogenyQuasiInverse`, via its `K̄`-point
form `isogenyQuasiInverse`) and the chain's proved `MulIsogeny`. The reading risk "is the printed reverse bound
`κ(A)` or `κ(B)`?" therefore drops out of the proof.

The fold is a manual fold (a weaker statement in place of the field, with consumers rerouted). It is given below as
27 exact edits in 20 chain files, and as a script, `scratch/gr14-narrow/apply_fold.py`. FOLD-BUILD-RESULT

Everything below compiles with no `sorry` and only the axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED,
`#print axioms` in `scratch/gr14-narrow/FoldCheck.lean`, output `FoldCheck_out.txt`).

Files:
* `ZInQKernel/Contrib/OneProof/GR14Narrow.lean`: the contributor file. It imports `TailZ35` (the bundle) and `Leaf`.
* `ZInQKernel/Contrib/OneProof/GR14Narrow/Chain.lean`: chain-side helper. It imports only `ZInQKernel.OneProof.H.TailB`,
  so `TailD` can import it without bringing any other module earlier into the chain.
* `ZInQKernel/Contrib/OneProof/GR14Narrow/Leaf.lean`: the leaf. It imports `TailY` and `Chain`, so `TailZ4` can
  import it.

### 1. Theorem statements (verbatim) and axioms

The new LEAF (Leaf.lean):

```lean
/-- **LEAF (R19-GR, forward direction; published form).** Gaudron–Rémond, *Polarisations et isogénies*, Duke Math.
J. 163 (2014), no. 11, Théorème 1.4 (p. 2060; `κ(A)` and `α(g) = 1024g³` defined p. 2058; …) … -/
def GapGR.GaudronRemondThm14Fwd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → IsStableFaltingsHeight A x →
    (∃ φ : A.X ⟶ B.X, ZInQ.DefFaltings.IsIsogeny φ) →
    ∃ φ : A.X ⟶ B.X, ZInQ.DefFaltings.IsIsogeny φ ∧
      (ZInQ.DefFaltings.isogDeg φ : ℝ) ≤ ZInQ.DefFaltings.grKappa g (Module.finrank ℚ K) x
```

Source and why it is never stronger (from its docstring). It is verbatim the first conjunct of the current field
`ZInQ.HeightSplit.GaudronRemondThm14` (TailY L834). That field is the printed Thm 1.4 restated over the kernel's
objects (locators p. 2058/2060 as recorded by the locator audit in the field's docstring; the paper's title and issue
number are from memory, UNVERIFIED). Under either reading of the reverse bound, the forward bound
`deg(A → B) ≤ κ(A)` is the theorem's main assertion.

Proved implications and reroutes:

| theorem (namespace `GapGR`) | statement | file | axioms |
|---|---|---|---|
| `gaudronRemondThm14Fwd_of_field` | `(h : ZInQ.HeightSplit.GaudronRemondThm14) : GaudronRemondThm14Fwd` | Leaf | std 3 |
| `gaudronRemondThm14Fwd_of_open` | `(r : HDec.HSyn.OpenResearchLeaves22) : GaudronRemondThm14Fwd` | GR14Narrow | std 3 |
| `isogenyReverseExists_of_milne` | `(hM : AvSplit.MilneIsogenyQuasiInverse) : HDec.HSyn.G0RevIsog.IsogenyReverseExists` | GR14Narrow | std 3 |
| `isogenyReverseExists_of_open` | `(l : HDec.HSyn.OpenAddedLeaves17) : HDec.HSyn.G0RevIsog.IsogenyReverseExists` | GR14Narrow | std 3 |
| `reverseIsogeny_of_milne` | `(hM : AvSplit.MilneIsogenyQuasiInverse) : HDec.HSyn.G0Split.ReverseIsogeny` | GR14Narrow | std 3 |
| `isogenyReverseExists_of_weil` | `(hMul : HDec.G0FibreSimple.MulIsogeny) (hQ : HDec.WeilPairing.IsogenyQuasiInverse) : HDec.HSyn.G0RevIsog.IsogenyReverseExists` | Chain | std 3 |
| `reverseIsogeny_of_weil` | same hypotheses `: HDec.HSyn.G0Split.ReverseIsogeny` | Chain | std 3 |
| `isogenyReverseExists_of_milne_eq_weil` | `isogenyReverseExists_of_milne hM = isogenyReverseExists_of_weil HDec.HSyn.mulIsogeny_proved (HDec.HSyn.isogenyQuasiInverse_lf7 hM)` (`rfl`) | GR14Narrow | — |
| `R19Fwd` (def) | first conjunct of `ZInQ.DefFaltings.R19_GaudronRemond` (kernel height), verbatim | Chain | — |
| `r19Fwd_of_r19` | `(h : ZInQ.DefFaltings.R19_GaudronRemond) : R19Fwd` | Chain | std 3 |
| `r19Fwd_of_leaves` | `(hGR : GaudronRemondThm14Fwd) (hN1 : ZInQ.H5Neron.NeronModelExists) (hSS1 : SemistableReductionThm) (hSS2 : SemistableNeronBaseChange) : R19Fwd` | Leaf | std 3 |
| `transfer_core_fwd` | `HDec.HSyn.G0Split.transfer_core` (LPrefix L12153) with `(r19 : R19Fwd)` in place of `(r19 : R19_GaudronRemond)`, same other hypotheses and conclusion `GlueAssembly.NonCMOutput Q M a` | Chain | std 3 |
| `isIsogenyMor_of_comp_eq_mul` | `(hMul : HDec.G0FibreSimple.MulIsogeny) [CharZero K] (f : A.X ⟶ B.X) (g : B.X ⟶ A.X) (d : ℕ) (hd : 0 < d) (hfg : f ≫ g = (𝟙 A.X) ^ d) (hgf : g ≫ f = (𝟙 B.X) ^ d) : PkgI3.AbVar.IsIsogenyMor g` | Chain | std 3 |
| `hom_ext_of_points`, `comp_eq_pow_of_isQuasiInverse`, `natCast_hom` | copies of TailP's `AVGlue` lemmas (L589, L639, L629) for the chain's `HDec.WeilPairing` | Chain | std 3 |

`isogenyReverseExists_of_milne` uses only the field and the chain's proved `HDec.HSyn.mulIsogeny_proved` (TailE
L6376). `MulIsogeny` is a hypothesis of the Chain lemmas so that Chain does not import `TailE`. At the fold site
(TailK) it is passed `mulIsogeny_proved`.

### 2. `#discharges` (scratch/gr14-narrow/discharges.txt)

`#discharges: 63 open hypotheses, 1822 theorems checked, 7 discharge one`. All 7 are earlier contributions that Main
imports (GRCountX6, GapSHPair, ElkiesX6Star, R16Split, SGA7PersistsNF, UnipotentForward, MumfordRigidity). **No
`GapGR` theorem discharges a field, as expected.** This is a narrowing: the field is replaced by a weaker statement,
and the conclusion `GaudronRemondThm14Fwd` is not the field's type.

### 3. The manual fold (every consumer at the base `43513d87`)

There is no autofold spec, because the field is replaced by a weaker statement and the old field is not derivable
from the new one. Live consumers come from the probe `scratch/gr14-narrow/Live.lean` (output `Live_out.txt`, VERIFIED).
It walks the 244,312-constant closure of `ZInQ.OneProof.frozenTarget`. Live R19 path:

`OpenResearchLeaves22…8.gaudronRemondThm14` → `heightRowsNo20_of8` (TailZ4 L163, `r19_of_leaves`) →
`OpenResearchLeaves7.r19` → `OpenResearchLeaves5.r19` → `OpenResearchLeaves2.r19` → `ResearchLeaves3.r19`.

From there:
* `glueOutputs_of_leaves3` reads it through `transfer_core`, first conjunct only.
* `reverseIsogeny_of_leaves3` reads it through `isogenyReverseExists_of_r19`, existence only. Its only caller is
  `gluePieces_of_open4`, TailK L308.

Edits (all paths `ZInQKernel/OneProof/H/`; `apply_fold.py` asserts that each old text occurs exactly once):

| # | file:line | old | new |
|---|---|---|---|
| 1 | TailD:2 (after) | — | `import ZInQKernel.Contrib.OneProof.GR14Narrow.Chain` |
| 2 | TailZ4:3 (after) | — | `import ZInQKernel.Contrib.OneProof.GR14Narrow.Leaf` |
| 3 | TailD:76 (`ResearchLeaves3`) | `r19 : ZInQ.DefFaltings.R19_GaudronRemond` | `r19 : _root_.GapGR.R19Fwd` |
| 4 | TailE:6486 (`OpenResearchLeaves2`) | same | same |
| 5 | TailN:93 (`OpenResearchLeaves5`) | same | same |
| 6 | TailX:105 (`OpenResearchLeaves7`) | same | same |
| 7 | TailD:108 (`researchLeaves3_of`, dead, from the old `ResearchLeaves`) | `r19 := r.r19,` | `r19 := _root_.GapGR.r19Fwd_of_r19 r.r19,` |
| 8 | TailD:115-121 | `namespace HSyn.G0RevIsog … reverseIsogeny_of_leaves3 … end HSyn.G0RevIsog` | removed (a comment) |
| 9 | TailD:251 (`glueOutputs_of_leaves3`) | `exact transfer_core r.r19 h20 r.r21 …` | `exact _root_.GapGR.transfer_core_fwd r.r19 h20 r.r21 …` |
| 10 | TailK:308 (`gluePieces_of_open4`) | `reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r3 G0Split.dimFinite` | `reverseIsogeny := _root_.GapGR.reverseIsogeny_of_weil mulIsogeny_proved l.isogenyQuasiInverse` |
| 11 | TailZ4:154 (`heightRowsNo20_of8` type) | `_root_.ZInQ.DefFaltings.R19_GaudronRemond` | `_root_.GapGR.R19Fwd` |
| 12 | TailZ4:163 (`heightRowsNo20_of8` term) | `_root_.ZInQ.HeightSplit.r19_of_leaves r.gaudronRemondThm14 …` | `_root_.GapGR.r19Fwd_of_leaves r.gaudronRemondThm14 …` |
| 13-27 | the field in every bundle generation: TailZ4:102 (OpenResearchLeaves8), Z9:56 (9), Z15:54 (10), Z17:159 (11), Z19:1835 (12), Z22:173 (13), Z23:640 (14), Z25:39 (15), Z26:39 (16), Z27:37 (17), Z28:37 (18), Z29:37 (19), Z33:38 (20), Z34:35 (21), Z35:33 (22) | `gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14` | `gaudronRemondThm14 : _root_.GapGR.GaudronRemondThm14Fwd` |

Notes on the edits:
* Every other mention is unchanged. All 14 copies `gaudronRemondThm14 := ….gaudronRemondThm14` and the four copies
  `r19 := r.r19` (TailX:212, TailN:120, TailE:6587, TailZ4:204) stay well typed. Generations 10-13 are dead and are
  changed only for that reason.
* The old row `R19_GaudronRemond`, the old `ResearchLeaves.r19` (LPrefix L11626), `isogenyReverseExists_of_r19` and
  `reverseIsogeny_of_leaves` (TailA) stay as they are (dead).
* `l.isogenyQuasiInverse` at TailK has type `HDec.WeilPairing.IsogenyQuasiInverse` (TailB L3765). At the top it is
  `isogenyQuasiInverse_lf7 l.milneIsogenyQuasiInverse` (TailX L255), so the reverse existence comes from the field
  `milneIsogenyQuasiInverse`. `isogenyReverseExists_of_milne_eq_weil` records that this is the same statement.
* Suggested docstring for the field (TailZ35:32 and the other generations): "height-split, H-15, gr14-narrow:
  Gaudron–Rémond 2014 Thm 1.4, forward direction (`A → B`, degree ≤ κ(A)) over the published stable height".
* OPEN.md, kinds.tsv and locators need regenerating or a new row for the changed statement (integration lead).

Checks at the base, before the fold (`FoldCheck.lean`, compiled):
* (a) `GapGR.transfer_core_fwd (GapGR.r19Fwd_of_r19 r19) = HDec.HSyn.G0Split.transfer_core r19 := rfl`, so edit 9
  leaves the remaining type unchanged.
* (b) `gluePieces_of_open4_gr14`: `{ gluePieces_of_open4 r t l g hYu with reverseIsogeny := GapGR.reverseIsogeny_of_weil
  mulIsogeny_proved l.isogenyQuasiInverse }`, so edit 10 typechecks in context.
* (c) `heightRowsNo20_of8_gr14`: edits 11-12 with the forward leaf as hypothesis.

FOLD-BUILD-DETAIL

## Method

1. **Live use (probe).** `Live.lean` computes the closure of `frozenTarget` and lists every constant whose type
   mentions R19, `GaudronRemondThm14`, the reverse-isogeny theorems or Milne's leaf, and every constant whose value
   uses one of them. Result as in §3: the second conjunct is consumed only by `isogenyReverseExists_of_r19`
   (`obtain ⟨-, ψ, hψ, -⟩`, the degree discarded). This confirms triage2's agent-H finding.
2. **A quasi-inverse of an isogeny is an isogeny.** Milne's leaf drops "g is an isogeny", so this has to be proved.
   From `f ≫ g = [d]_A` and `g ≫ f = [d]_B` (`d ≥ 1`, characteristic 0):
   * `[d]_B = g ≫ f` is finite (`MulIsogeny`, proved in the chain) and `f` is separated, so `g` is finite
     (`IsFinite.of_comp`);
   * `[d]_A = f ≫ g` is surjective, so `g` is surjective (`Surjective.of_comp`);
   * `g` is a homomorphism because it is a `PkgI3.AbVar.Hom`.

   This is the end of `end0Division_of_homFree` (TailA L1290-1327) with `f` and `g` exchanged.
3. **Where to reroute.** `gluePieces_of_open4` (TailK) is upstream of TailX, where the Milne field lives, and it sees
   only the `K̄`-point form `WeilPairing.IsogenyQuasiInverse`. Threading the Milne field down would take about 6
   generations of signature changes (triage2). Instead, the point equations are turned into morphism equations:
   morphisms of abelian varieties are determined on `K̄`-points (a copy of TailP's `AVGlue.hom_ext_of_points`, with
   the instance `IsReduced A.X.left` supplied by hand, since TailB's closure lacks `import Mathlib`). So the reroute
   is one line at TailK:308, and `MulIsogeny` is passed as `mulIsogeny_proved`, which is already used in the same
   theorem.
4. **Import placement.** `Chain` imports only `TailB`, which is already in TailD's closure, and declares no instances.
   So importing it from TailD changes nothing else in the chain. `Leaf` imports `TailY` and `Chain`, both already
   in TailZ4's closure.
5. **Build note.** In this worktree's copied build, some TYZGenus/Compiler/RouteK oleans were missing or stale, and
   lake rebuilt them (12,997 jobs for Main + Discharges + GR14Narrow). `lean/.lake/build` was copied from the
   pi0-prune worktree (same `lean/` tree, 8094333d).
