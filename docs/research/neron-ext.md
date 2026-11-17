# neron-ext: `neronSchemeExtensionExists` reduced to Néron models over the DVRs of `𝓞_L`

Task neron-ext, 2026-11-16. Base: origin/main 0caafe66 (w80). This was model work with no human review. No existing
file was edited. The deliverables are new files: `ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean`
with four helper modules next to it, and everything under `scratch/neron-ext/`. Results log:
`scratch/neron-ext/log.md`.

Marks used below:
* **VERIFIED**: compiled, or read in a file.
* **STANDARD**: published, with a reference.
* **UNVERIFIED**: a locator recalled from memory (there is no network here).

## 1. Main result

The textbook field `neronSchemeExtensionExists` (`ZInQ.Contrib.NeronC.NeronSchemeExtensionExists`, BLR §1.4
Thm. 3 over `𝓞_L`, existence half) is **proved** from two statements:
* the new leaf **`NeronExt.NeronDVRLocal`**: BLR §1.4 Thm. 3 over the discrete valuation rings `(𝓞_L)_v`;
* the chain's existing leaf **`egaIV_8_10_5_xii`** (EGA IV 8.10.5 (xii), descent of properness). It is already a
  field of `OpenAddedLeaves17`, so nothing is added there.

The new leaf is **not stronger** than the field: the converse is proved too. The open count is unchanged (−1 +1).
The leaf that replaces the field is **local**: it asks for a Néron model over one DVR at a time, not over `𝓞_L`.
All the global geometry is proved glue: spreading out, gluing over a Zariski cover, abelian schemes being Néron
models, and the local nature of the Néron property.

```lean
-- ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean (namespace NeronExt)
theorem extension_of_dvrLocal (hpr : ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii) (hloc : NeronDVRLocal) :
    ZInQ.Contrib.NeronC.NeronSchemeExtensionExists
theorem dvrLocal_of_extension (h : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists) : NeronDVRLocal
```

**The new leaf (exact text, VERIFIED):**

```lean
def NeronDVRLocal : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (v : Ideal (𝓞 L)) [v.IsMaximal] (Rv : Type) [CommRing Rv] [Algebra (𝓞 L) Rv]
    [IsLocalization.AtPrime Rv v] [Algebra Rv L] [IsScalarTower (𝓞 L) Rv L],
    ∃ N : Over (Spec (CommRingCat.of Rv)), CToPrinted.IsNeronModelOver Rv L N ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Rv L)))).obj N ≅
        (A.baseChange L).X)
```

`CToPrinted.IsNeronModelOver` (TailZ19) is BLR §1.2 Def. 1. It asks that `N` be smooth, separated, locally of
finite type and quasi-compact, and that `f ↦ f_L` be bijective for every smooth `R_v`-scheme `Y`.

**Rating: LEAF, published, in printed form.** BLR §1.4 Thm. 3 states that an abelian variety over the fraction
field of a Dedekind scheme has a Néron model. Here the Dedekind scheme is `Spec (𝓞_L)_v`, a discrete valuation ring
(BLR §1.4 Thm. 3 with §1.2 Def. 1; locators UNVERIFIED). Further points:
* The statement is over genuine definitions: `PkgI3.AbVar`, Mathlib's schemes, and the chain's
  `CToPrinted.IsNeronModelOver`.
* It quantifies over every presentation `R_v` of the local ring, so it does not depend on a choice.
* It is the published theorem at a special base, and never stronger: `dvrLocal_of_extension` derives it from the
  field via gt-blr's localization theorem.
* Proposed `kinds.tsv` flag: `locator UNVERIFIED (BLR 1.4 Thm 3 at S = Spec of the DVR (O_L)_v)`.
* A `docs/research/locators.md` row is still needed. I did not edit that shared file. Proposed row: *BLR, Néron
  Models (1990), §1.4 Thm. 3 (existence of Néron models of abelian varieties over a Dedekind base), specialised to
  a DVR; and §1.2 Def. 1.*

**`#discharges`** (VERIFIED, `scratch/neron-ext/Discharges.lean`, output in `scratch/neron-ext/discharges.txt`):

```
DISCHARGES [OpenTextbookLeaves12.neronSchemeExtensionExists] by NeronExt.extension_of_dvrLocal
  still assumes: [ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii, NeronExt.NeronDVRLocal]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 3030 theorems checked, 8 discharge one
```

The other seven lines are discharges by earlier contributions, which are already in the tree.
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for:
* `extension_of_dvrLocal`;
* `dvrLocal_of_extension`;
* `glued`;
* the generated `sixContactMin_of_open36` of the autofold dry run.

**Autofold spec:** `scratch/neron-ext/autofold.json`. It discharges `neronSchemeExtensionExists` with proof
`_root_.NeronExt.extension_of_dvrLocal {l}.egaIV_8_10_5_xii {n}.neronDVRLocal` and adds one leaf
`neronDVRLocal` (kind `published`, with the flag above). Checks:
* `autofold.py --dry-run` reports `strict count: 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11`.
* Its module, with line 1 stripped, compiles (`scratch/neron-ext/AutofoldDry.lean`, VERIFIED).

## 2. Consumers, and why the field cannot be narrowed to abelian schemes

These were found by grep and by closure scans from `ZInQ.OneProof.frozenTarget`. The scans are
`scratch/neron-ext/Reach.lean` → `reach.txt` (partial) and `ReachT41.lean` → `reach-t41.txt` (VERIFIED).

| route | consumers | instance used |
| --- | --- | --- |
| T41 = `H5Neron.NeronModelExists` (`t41_of_extension5`, TailM L387; `neronModelExists_of_extension`, TailZ4 L153/173) | `G0Split.heightAdditivity_of_h5neron`, `H5Neron.stableFaltingsHeight_add_le(')`, `HeightSplit.{r18,r19,r20Lower,r21,r22}_of_*`, `exists_semistable_neron`, `stableFaltingsHeight_ne_{bot,top}`, `stableHeightFinite_of(')`, `TailZ4.heightRowsNo20_of8` | abelian varieties over number fields (the height rows' abelian varieties), and **every** finite extension `L`: the stable height is an infimum over `L` |
| N1 at `L = K` → DVRs (`GapNeron.neronSchemeModelExistsNF`, TailZ26 L174/182) | `raynaudCriterionNF_of14` (r6 at number fields), `ss1_ss3_of14NF` (SS1, SS3) | `A` over a number field `K`, every DVR `O ⊂ K` |
| field passing only | bundles in TailO, TailX, TailZ4, TailZ9, TailZ11, TailZ32, TailZ42 | — |

The test schemes `Y` are arbitrary smooth schemes. The group law (`grpObjOfNeron`) uses `Y = N`, `N×N`, `N×N×N`,
and the uniqueness and localization arguments use further smooth `Y`.

**Verdict (VERIFIED by reading the consumers): no narrowing to a model the tree already has.** Raynaud's criterion
(r6) applies the Néron model to abelian varieties whose reduction is a priori bad: it is how semistable and good
reduction of the QML3 objects is proved. SS1 is the same. The height rows need a Néron model over `𝓞_L` at every
`L`, including places of bad reduction. So "an abelian scheme after base change, or over a localization" is not
enough. Instead the field was reduced to its local content (§1).

## 3. The proof (all glue proved, VERIFIED)

| piece | Lean | content | source of the argument |
| --- | --- | --- | --- |
| N1-g3 (neron-lg): Zariski gluing | `NeronExt.glued` (`NeronExtGlue.lean`) | if every point of `Spec 𝓞_L` has an open neighbourhood `U` with a Néron model of `B` over `U` (`NeronOn L B U`), then `B` has one over `Spec 𝓞_L` | Mathlib's `Scheme.Cover.RelativeGluingData` (Stacks 01LH) over the cover by all good opens. Transition maps are the unique extensions of `id_B`; functoriality and the pullback condition come from Néron uniqueness. Morphisms glue with `glueMorphismsOverOfLocallyDirected` |
| the Néron property is local at the maximal ideals of an open | `neronOn_of_local'` (`NeronExtLocal.lean`) | `X` over `U` smooth, separated, qc with `X ⊗ (𝓞_L)_w` Néron for every maximal `w ∈ U` ⇒ `NeronOn L B U` | gt-blr's `local_pt`/`isNeronModelOver_of_local`, copied with a set `T` of maximal ideals. `𝓞_L` is Jacobson (`isJacobsonRing_int` proved here) |
| N1-ab (BLR §1.2 Prop. 8) | `isNeronModelOver_of_grpObj` (`NeronExtAb.lean`) | a smooth proper `GrpObj` over a DVR is a Néron model | the vendored FLT argument (CloudW03NeronSurj, Apache-2.0). Its two top steps are restated here without the bundle field `connectedFibres`, which no vendored proof reads |
| spreading out | `exists_spread_sep`, `spread_generic` (`NeronExtSpread.lean`) | a smooth separated qc `R_𝔭`-scheme spreads to some `R[1/s]` with the same three properties; a morphism of generic fibres spreads to some `D(s)` | EGA IV 8.8.2 (ii) and 17.7.8 (ii) (`CloudW01Spread`, proved). Separatedness comes from Stacks 01ZP (`CloudW01Spread/StacksFrontier`, proved) applied to the diagonal, with Mathlib's `diagonal_pullback_fst`. Morphisms use Stacks 01ZC (Mathlib) |
| N1-g1 + N1-ab: the good model | `goodModel` | `A_L` has a smooth separated qc model `𝒜` supported on some `D(f)` which is Néron at every `w ∌ f` | `NF.abVarSpreadsOut_of_ega` (8.8.2 and 17.7.8 proved, 8.10.5 (xii) the chain's leaf), then N1-ab over `(𝓞_L)_w` |
| N1-g2 (neron-lg): near a closed point | `near` | a Néron model over `(𝓞_L)_v` gives a Néron model over an open `U ∋ v` | spread the local model to `X` over `D(s)`. Compare `X` with `𝒜` near the generic point: spread both generic isomorphisms; both composites are the identity by uniqueness (`isoNear`). Remove the finitely many other primes of `s₁s₂f` by prime avoidance (`exists_avoid`, from `Ideal.finite_factors`). Then apply the local criterion |
| assembly | `extension_of_dvrLocal` | for each point `x`, `near` at a maximal `v ⊇ x` gives `U ∋ v ∋ x`; then `glued` | — |

Two smaller notes:
* `NeronDVRLocal` is instantiated at `Localization.AtPrime v`, with the algebra `locAlg` (`IsLocalization.lift`
  into `L`).
* `NeronExt.NeronOn L B U` is a Néron model over the open `U`, phrased over `Spec 𝓞_L`: an `𝓞_L`-scheme lying over
  `U`. At `U = ⊤` it is the field's conclusion.

## 4. Files

* `ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean` (444 lines): the contributor file. It imports
  `ZInQKernel.Contrib.NeronC.NeronGroup` (where the statement is defined) and the helpers, and never
  `OneProof.Main`. It contains the leaf, `near`, `goodModel`, `extension_of_dvrLocal` and
  `dvrLocal_of_extension`.
* Helpers next to it: `NeronExtGlue.lean` (534 lines), `NeronExtLocal.lean` (285), `NeronExtAb.lean` (132),
  `NeronExtSpread.lean` (273).
  * They contain no `#eval`, `run_cmd`, syntax or macros, and no global instance on Mathlib classes.
  * The instances they do declare are about this task's own definitions (`res`, `cov`).
  * `isLocalization_bot` is a theorem used locally.
* `lake build ZInQKernel.Contrib.OneProof.NeronSchemeExtensionExists` builds the contributor file and all four
  helpers (VERIFIED).
* `scratch/neron-ext/`:
  * `Glue.lean`, `LocalCrit.lean`, `NeronAb.lean`, `Spread.lean`, `Near.lean`: the drafts, the same content
    as the modules;
  * `Discharges.lean`, `discharges.txt`;
  * `autofold.json`, `AutofoldDry.lean`;
  * `Reach.lean`, `reach.txt`, `ReachT41.lean`, `reach-t41.txt`: the consumer scans;
  * `log.md`.

## 5. Remarks for the integrator

* The fold is count-neutral. It trades the global textbook leaf for a local one. The DVR consumers (r6, SS1, SS3
  through `GapNeron.NeronSchemeModelExistsDVRNF`) could read `NeronDVRLocal` directly: the ValuationSubring form
  follows from it with `CToPrinted.isLocalization_center`. That is a possible later simplification; it is not done
  here.
* What remains open: `NeronDVRLocal` itself. This is BLR's local existence theorem (via Néron smoothening, BLR
  3.1/1, and the construction of chapters 4–6 over strictly henselian DVRs, then descent). A further reduction to
  strictly henselian DVRs plus étale descent was not attempted. Its descent step needs effective descent of
  schemes (BLR 6.1/6.2), which the tree does not have. SPECULATIVE: that is a large project.
* None of the ports already in the tree contains Néron smoothening or the local existence theorem (grep of
  `ZInQKernel/Contrib` for smoothening, VERIFIED). What they do provide, all used here:
  * CloudW03: BLR 1.2/8;
  * CloudW01: spreading out;
  * gt-blr: BLR 1.2/4.
* **Lead for discharging `NeronDVRLocal`.** The Fermat's Last Theorem development (local copy `~/flt-src`, the
  source CloudW03 ported from) states and proves Néron models of abelian varieties over **henselian** DVRs (read
  in the file, VERIFIED):
  `GoodReductionJacobian.RelativeGroupLaw.exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing`.
  * Its hypotheses: `R` a henselian DVR with fraction field `K`, and an abelian variety over `K` given as a
    group law with `AbelianSchemePropertyBundle`.
  * Its conclusion: a commutative group model with `NeronModelPropertyBundle` and a group isomorphism on the
    generic fibre.
  * Its import closure is 577 files (4.7 MB), at Lean v4.33.1 with Mathlib db584cd6 (VERIFIED by an import
    scan).

  `(𝓞_L)_v` is not henselian, so a port would discharge `NeronDVRLocal` only together with descent of the Néron
  model from the henselization `(𝓞_L)_v^h` to `(𝓞_L)_v`. Unlike gt-shpair's base change, this is the existence
  direction. It needs a descent datum from Néron uniqueness and effective descent, which is quasi-projectivity
  territory (BLR §6.1, §6.4; UNVERIFIED). SPECULATIVE: porting the 577 files is a task of the size of flt-cqj
  (661 modules), and the descent step is the real open part.
