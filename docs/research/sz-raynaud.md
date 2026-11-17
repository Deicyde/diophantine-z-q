# sz-raynaud: the two SGA 7 rows on the manuscript's route (diophantine_zq.tex L814-818)

Task sz-raynaud (2026-11-17), base wip/ga-rigidity (f9e83fdb), no other branch merged.

## 1. Result

**Verdict.**

- **Neither row has a counterpart on the manuscript's route at L814-818, and neither can be proved from that route.**
  The rows are `sga7_IX_Cor3_3` (with ga-rigidity's leaf `SGA7_IX_Cor3_3_Def34`) and `sga7_IX_3_5_ForwardGeom`
  (with leaf `SGA7_IX_3_5_ForwardGeom_Def34`).
- **What the route gives in their place is now in Lean.** Its two steps are stated as leaves:
  1. Raynaud's criterion as Silverberg–Zarhin Theorem 3.5 states it (read from the page image on 11-17). This
     gives semistable reduction over `F = L_v(A[3])` directly, with no base change.
  2. The uncited sentence at L817-818, labelled **ELLIOT**: wild inertia acts trivially on `V_ℓ(A)`.

  From these two leaves, L814-818 is proved in Lean, and so is the bundle field `raynaudSemistableSHOr` (SGA 7 IX
  4.7, statement unchanged).
- **Fold.** The fold discharges `raynaudSemistableSHOr` from the new leaf `silverbergZarhinThm35`. That trades a
  LEAF that rests on SGA 7, which the manuscript does not cite, for a LEAF the manuscript cites, read on 11-17. The
  strict dry run gives **12/22 on 34 → 12/22 on 34**, strictest 11/23 → 11/23: the counts are unchanged and the
  fold is accepted without `--allow-rise`.

**The manuscript's two steps** (L814-818, read):

1. "Raynaud's criterion `\cite[Theorem 3.5]{silverbergzarhin}` gives semistable reduction there", for
   `F = L_v(A[3])` (`A[5]` if `p = 3`). Silverberg–Zarhin Thm 3.5 (Ann. Inst. Fourier 45 (1995), p. 406), as read
   from the page image on 11-17 (scratch/sz-raynaud/sz-thm35-reading.md):
   - `X` is an abelian variety over a field `F` with a discrete valuation;
   - `n ≥ 3`, and `n` is not divisible by the residue characteristic;
   - `X_n` is defined over an unramified extension of `F`;
   - then `X` has semistable reduction. Their definition (p. 405): the identity component of the special fibre of
     the Néron model is an extension of an abelian variety by a torus, not necessarily split.

   The manuscript's use (`n = 3`, or `n = 5` at `p = 3`; the torsion rational over `F`) is a direct instance.
2. "Its wild inertia acts trivially on each `V_ℓ(A)` with `ℓ ≠ p`." This sentence has **no citation: ELLIOT.**

**Why each row has no counterpart** (traced in the tree, §3):

- **`sga7_IX_Cor3_3`** (the identity component commutes with base change) feeds only SS2/SS3, that is,
  semistability persists under base change.
  - SS2/SS3 are used to compute Faltings heights on Néron models over a common semistable field
    (`r20_of_leaves'`).
  - At L814-818 the manuscript gets semistability over `F` from the criterion itself, so there is nothing to
    persist.
  - Elsewhere the manuscript uses the stable Faltings height (L598) as a standard notion. It has no
    semistable-persistence step: `grep -i semistab` finds only L740 (de Rham, potentially semistable), L817, L10980
    and the bibliography.
- **`sga7_IX_3_5_ForwardGeom`** (semistable ⇒ `(σ−1)² = 0` on `T_ℓ` for every inertia element) feeds r6
  (`PkgI2.RaynaudCriterionNF`), which is used in two places:
  - **D2** (L814-818). Here the manuscript uses only the weaker ELLIOT sentence, which says nothing about tame
    inertia. So the route gives D2, but not the row.
  - **A6** (`qmModelG3_of`). This is the kernel's own Raynaud route to good reduction. The manuscript instead gets
    good reduction from the proper model and its universal abelian scheme (L529-530).

  The ELLIOT sentence does follow from the row, using one on-the-spot glue statement (wild inertia is pro-`p`):
  `elliot_of_semistableUnipotent`. The converse does not hold.

**Proved in Lean** (`ZInQKernel/Contrib/OneProof/SZRaynaud.lean`, namespace `SZRaynaud`; compiled, §5):

| statement | kind | what it is |
| --- | --- | --- |
| `SilverbergZarhinThm35` | **LEAF** (published; flag "reading 11-17 …") | SZ Thm 3.5 as read. Over any DVR of any field; `m ≥ 3` invertible; `A(K̄)[m]` rational. Conclusion: every Néron model is semistable in SZ's sense (`DictModels.RaynaudOr.IsSemistableResT`: special fibre over `k`, torus not necessarily split) |
| `ElliotWildInertiaTrivial` | **ELLIOT** (consequence; flag "ELLIOT: uncited manuscript sentence (diophantine_zq.tex:817-818) …") | At a finite place of a number field: semistable reduction in SZ's sense ⇒ every wild inertia element acts trivially on `T_ℓ(A)`, for `ℓ` invertible |
| `HasSemistableReductionSZ`, `IsWildInertia` | definitions | `HasSemistableReductionSZ`: a Néron model that is `IsSemistableResT`. `IsWildInertia`: `v_w(σx − x) > v_w(x)` for all `x ≠ 0` (the first ramification group; the valuation-ring form of the kernel's `wildSet`) |
| `isSemistable_of_sz`, `hasSemistableReduction_of_sz` | proved | **The named step from SZ's semistability to the kernel's** (geometric special fibre, split torus): base change `k → k̄`, using Stacks 04KV (`geomConnOfRationalPoint_proof`), via dict-models' `isSemistable_of_resT` |
| `raynaudSemistable_of_sz35` | proved | `SZ35 → ReductSplit.RaynaudSemistable`: the kernel's Raynaud criterion over **every** DVR, with no strict henselization and no `StrictHenselizationPair` |
| `raynaudSemistableSHOr_of_sz35` | proved | `SZ35 → DictModels.RaynaudOr.RaynaudSemistableSHOr`, the bundle field, statement unchanged (left disjunct) |
| `RaynaudWildNF`, `raynaudWildNF_of_leaves` | proved | **L814-818 in Lean**, in r6's objects: if `A[m]` is Galois-fixed (`m ≥ 3` invertible), every wild inertia element fixes `A(K̄)[ℓⁿ]`. Proved from SZ35, ELLIOT, the Néron-model existence field at number fields (as r6's own proof uses), `[m]` étale and Mumford's torsion count |
| `elliot_of_semistableUnipotent` | proved (sanity) | ELLIOT from SGA 7 IX 3.5 (`SemistableUnipotent`, which the ForwardGeom row gives) and the on-the-spot glue `WildPeriodCoprime` (wild inertia is pro-`p`; not proved) |
| `isSemistableDef34_of_sz`, `hasSemistableReductionDef34_of_sz`, `def34_of_sz35` | proved | **GaRigidity:** SZ's output gives Déf. 3.4's "no `𝔾_a`" condition, the hypothesis of ga-rigidity's two Déf. 3.4 rows. Proved by `isSemistable_of_sz` followed by `GaRigidity.SGA7.isSemistableDef34_of_isSemistable` (rigidity for `𝔾_a`, `noGaSubgroup_of_semiAbelian`) |

## 2. The manuscript's text (read)

- **L814-818** (read): at `p`, `F` is `L_v` with `A[3]` adjoined (`A[5]` if `p = 3`), of degree `≤ DG₀` over
  `ℚ_p`. "Raynaud's criterion `\cite[Theorem 3.5]{silverbergzarhin}` gives semistable reduction there" is followed
  by the uncited sentence on wild inertia and `V_ℓ(A)`, `ℓ ≠ p`. L819-821 then use the break bound for the upper
  numbering. VERIFIED (read).
- **Bibliography**, L11077-11080: Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), 403-420. VERIFIED.
- **SGA 7 is cited nowhere in the manuscript**: `grep` for `SGA`, `sga7`, `grothendieck` in diophantine_zq.tex
  finds nothing. Silverberg–Zarhin is cited only at L816. VERIFIED.
- So SGA 7 IX 3.5 (unipotence) and Cor. 3.3 are not on the manuscript's route. Prop. 4.7 reaches it only as the
  proof Silverberg–Zarhin give for Thm 3.5 ("See Proposition 4.7 of [7]").

## 3. Where the rows feed (traced)

scratch/sz-raynaud/log.md has the file:line chain. Summary:

```
sga7_IX_Cor3_3 → sga7_IX_3_3_SHpre → sga7_IX_3_3_SH → semistablePersistsSHcp, sga7_IX_3_3 → SS3 (SemistablePersists)
                → r20_of_leaves' / r20Lower_of_leaves' (Faltings heights over a common semistable field)
sga7_IX_3_5_ForwardGeom → SemistableUnipotent → r6 RaynaudCriterionNF
                → D2: raynaudPlace_of_R6 → torsFix_of_descent → torsFixWildOdd / tateWildKE / localGlue_of_descent
                      (also lt-local's linkedTateLocal through localGlue_at: D2 again)
                → A6: qmModelG3_of (QML3 good reduction, the kernel's Raynaud route; manuscript L529-530 differs)
raynaudSemistableSHOr → raynaudSemistableSH → (with StrictHenselizationPair) RaynaudSemistable → r6, SS1
   (after the fold: silverbergZarhinThm35 → raynaudSemistableSHOr_of_sz35 → raynaudSemistableSHOr, unchanged)
```

In the kernel the ELLIOT sentence is already *proved*, from three inputs: r6's unipotence, the `p`-power period of
wild elements (TailH `wildIter`), and the algebraic core `PkgI2.fixed_of_unipSq_of_iterate`. That proof is the
kernel's own; the manuscript states the sentence without proof.

**Follow-up (not done).** D2 could rest on the manuscript's route in the bundle:
- Re-prove TailH's `raynaudPlace_of_R6`, with conclusion "fixes", from `RaynaudWildNF`.
- This needs a lemma `isWildInertia_of_wild_gen` (the analogue of TailH's `isInertia_of_wild_gen`, for
  `IsWildInertia` on `normVS f₁`).
- `torsFix_of_descent` then loses its unipotence and `wildIter` steps, which removes r6 from D2 and I2.
- r6 is still needed by A6, so no field leaves the bundle until A6 is also rerouted to the manuscript's universal
  abelian scheme (L529-530). So the bundle count would not change; this is why it was not done here.

## 4. Known issues in the sources

1. **Silverberg–Zarhin Thm 3.5: no known issue.** The page was read on 11-17 by the fleet's print reader (host's
   late note, copied into scratch/sz-raynaud/sz-thm35-reading.md). The hypothesis is `n ≥ 3`. The old worry in
   locators R6 ("`> 3`") came from numdam's OCR text layer, which misreads the `≥` sign. So Thm 3.5 covers
   `n = 3`, and the manuscript's use at L814-818 is a direct instance:
   - the torsion is rational over `F`, the trivial case of "defined over an unramified extension";
   - `3` and `5` are prime to `p` in the respective cases.

   The base is any field with a discrete valuation, so the Lean leaf (any DVR) is the print's generality.
   Silverberg–Zarhin's semistability (p. 405) is the residue-field form with a torus that need not be split; the
   leaf concludes exactly that form (`IsSemistableResT`). The step to the kernel's form is `isSemistable_of_sz`
   (Stacks 04KV, proved). The leaf specializes the print in two ways:
   - the unramified extension is taken trivial;
   - "the Néron model" is read as "every Néron model", the standard reading, since Néron models are unique up to
     unique isomorphism.
2. **The ELLIOT sentence (L817-818) is uncited (documented issue, not an error).** The sentence is true and
   standard:
   - Semistable reduction gives `(σ−1)² = 0` on `T_ℓ` for inertia. The sources are SGA 7 IX 3.5 and, per
     locators R6, Silverberg–Zarhin Thm 3.3 (p. 405); the manuscript cites neither.
   - Wild inertia is pro-`p` with `p ≠ ℓ`, and a unipotent element of `p`-power order is trivial.

   `elliot_of_semistableUnipotent` is this argument in Lean, with the pro-`p` input as the on-the-spot glue
   `WildPeriodCoprime`. Suggested repair to the manuscript: cite Silverberg–Zarhin Thm 3.3 (or SGA 7 IX 3.5) and add
   "since wild inertia is pro-`p`".
3. **The ELLIOT leaf reads the sentence globally.** The sentence speaks of the local field `F`. The Lean leaf is at
   a finite place `O` of a number field `K` (the manuscript's setting: `A` over a number field), with "its wild
   inertia" taken as the wild inertia of `w | O` in `Gal(K̄/K)` and semistable reduction taken at `O`. Two standard
   identifications make this the sentence's content:
   - the decomposition group of `w` is the Galois group of the completion;
   - Néron models commute with completion (BLR 7.2/1, the tree's field `blr_7_2_1`).

   The manuscript itself treats `G_F` inside the global Galois group acting on `V_ℓ(A)`. Both identifications are
   in neither the manuscript nor Silverberg–Zarhin; they are documented in the leaf's docstring, and the lead
   decides how the ELLIOT row counts. `T_ℓ` stands in for `V_ℓ`: `T_ℓ ⊆ V_ℓ`, so the leaf is a consequence.

## 5. Lean

- **Contribution:** `ZInQKernel/Contrib/OneProof/SZRaynaud.lean`, with development copy scratch/sz-raynaud/SZR.lean
  (same body).
  - Imports GaRigiditySGA7, RaynaudSemistableOr, NeronDVR, GeomConnOfRationalPoint, MumfordTorsionAlgClosed and
    MulEtale; never `ZInQKernel.OneProof.Main`.
  - GaRigidity.lean and GaRigiditySGA7.lean are unchanged. No other file under ZInQKernel/ was edited.
- **Compile (VERIFIED, 11-17 07:14):** `lake build ZInQKernel.Contrib.OneProof.SZRaynaud ZInQKernel.OneProof.Main
  ZInQKernel.OneProof.Discharges` completed successfully; `ZInQ.OneProof.frozenTarget` depends on the standard
  axioms only.
- **`#discharges`** (scratch/sz-raynaud/Discharges.lean, output scratch/sz-raynaud/discharges-out.txt):
  `DISCHARGES [OpenResearchLeaves42.raynaudSemistableSHOr] by SZRaynaud.raynaudSemistableSHOr_of_sz35`, which still
  assumes `[SZRaynaud.SilverbergZarhinThm35]` and uses the axioms `[propext, Classical.choice, Quot.sound]`.
- **`#print axioms`:** all 11 new theorems use `[propext, Classical.choice, Quot.sound]`, except `pow_smul_tate`,
  which uses `[propext, Quot.sound]`. No `sorry`.
- **Dry-run fold:** the output minus its first line (scratch/sz-raynaud/DryRunFold.lean) compiles, and
  `HDec.HSyn.sixContactMin_of_open61` uses the standard axioms only.
- **Autofold:**
  - Spec: scratch/sz-raynaud/autofold.json, which discharges `raynaudSemistableSHOr` with the leaf
    `silverbergZarhinThm35`.
  - Strict dry run: leaf-fold33b's `autofold.py` and `render_open.py`, copied from d67ea55f6 (and byte-identical at
    origin/wip/leaf-fold33b = 74395dcf0). Output in scratch/sz-raynaud/dryrun.txt: "strict count: 12/22 on 34 →
    12/22 on 34; strictest 11/23 → 11/23"; new generation `OpenResearchLeaves43`, top `sixContactMin_of_open61`.
  - The ELLIOT leaf discharges no field (r6 is still needed by A6), so it is not in the spec. Its kind and flag
    for the lead are in §6.

## 6. Provenance of every new leaf

| leaf | provenance | kind | flag |
| --- | --- | --- | --- |
| `SilverbergZarhinThm35` | (b) cited print, in the manuscript's bibliography (L11077): Thm 3.5 p. 406, semistable p. 405; read 11-17 from the page image | published | `reading 11-17 (the fleet's print reader, page image …): the hypothesis line is n >= 3 …` (LEAF) |
| `ElliotWildInertiaTrivial` | (a) diophantine_zq.tex:817-818, an uncited sentence (ELLIOT) | consequence | `ELLIOT: uncited manuscript sentence (diophantine_zq.tex:817-818); global reading at a finite place of a number field (decomposition group = local Galois group; Néron models commute with completion); T_l for V_l` |
| `WildPeriodCoprime` (glue, used only in the sanity theorem) | (c) on-the-spot: in neither the manuscript nor Silverberg–Zarhin | glue | never LEAF |
