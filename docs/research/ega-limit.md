# ega-limit: EGA IV₃ 8.10.5 (xii) proved

**Result (VERIFIED, compiled).** The open hypothesis `egaIV_8_10_5_xii` of the single proof (bundle field
`HDec.HSyn.OpenAddedLeaves17.egaIV_8_10_5_xii`, type `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii`,
`ZInQKernel/Contrib/SpreadOut/Spread.lean` L49; first bundled in `ZInQKernel/OneProof/H/TailX.lean` L170; LEAF)
is now a theorem:

```lean
theorem ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof : ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
```

in `ZInQKernel/Contrib/OneProof/EGAIV_8_10_5_xii.lean`. It takes no hypotheses and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`. It is built from Mathlib v4.35.0 and AxiomMath/Stacks at
revision c496df0d (Apache-2.0): the 13 modules already vendored in `ZInQKernel/Contrib/CloudW01Spread/`, plus 73
newly vendored in `ZInQKernel/Contrib/OneProof/EGAProperLimit/`. It uses nothing from the bundles. **The field
goes away (−1) and no leaf is added.** The statement is unchanged; it is neither false nor vacuous. It is
EGA IV₃ 8.10.5 (xii) for systems indexed by `Type`-directed preorders in `Scheme.{0}`. Every hypothesis is used:
local finite presentation, quasi-compactness and quasi-separatedness of `Xi`, and qcqs stages with affine
transitions.

`#discharges` output (`scratch/ega-limit/Discharges-output.txt`, base 2880fef1, contribution unfolded):

```
DISCHARGES [OpenAddedLeaves17.egaIV_8_10_5_xii] by ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 4398 theorems checked, 8 discharge one
```

The other seven `DISCHARGES` lines in that run are contributions that were already in the tree.

## 1. Route: no Chow over a non-Noetherian base, no absolute Noetherian approximation

AxiomMath/Stacks proves Stacks 081F in full (`Limits/EventuallyProperOverLimit.lean`), but it does so through
Chow's lemma over a qcqs base. That in turn needs absolute Noetherian approximation (Tag 01ZA, its
`FiniteTypeApproximation`). The file import closure is 1761 files and 513k lines, too much to vendor (VERIFIED by
counting). I found no Chow-free proof: the valuative criterion cannot be moved from a stage to the limit, because
a valuation ring over `D_j` need not factor through `lim D`. The task offered a Nagata fallback, but Nagata is not
in Mathlib or in the vendored libraries. So the proof keeps Chow's lemma but uses it only over an affine
Noetherian base, where Stacks has already proved it. Everything else is glue proved here (`EGAIV_8_10_5_xii.lean`):

1. **Separated at a stage.** Stacks 01ZQ (`exists_isSeparated_baseChange_of_isLimit`, vendored `Diagonal.lean`)
   gives a stage `j₁ → i` where `Z = X_{j₁}` is separated. Properness at the limit is moved along
   `transitionIso`.
2. **Affine cover.** `exists_affine_surjective_flat`: let `p : Y₀ = ∐ Uₖ ⟶ D j₁` be the disjoint union of a finite
   affine open cover. It is affine (Mathlib's instance for finite coproducts), surjective, flat (Mathlib's
   `Sigma.desc` instance) and quasi-compact.
3. **Chow's lemma over an affine base**, `hasChowModification_of_isAffine`: Chow's conclusion
   (`HasChowModification`) for any separated morphism of finite presentation to an affine `T`.
   - `Γ(T)` is the filtered colimit of its finitely generated ℤ-subalgebras; this is CloudW06's
     `AdjoinFinset.isLimitSpecCone`, already in the build.
   - Descend the morphism to a stage by Stacks 01ZM (1) (CloudW01's
     `exists_isPullback_of_finitePresentation_of_essentiallySmall`), then make it separated by 01ZQ.
   - Apply Chow over the Noetherian affine stage `Spec ℤ[s]`: Stacks 0200,
     `hasChowModification_of_hasSegreEmbeddings`, with the Segre embedding 01WD (`exists_segreEmbedding`) for any
     base.
   - Base change back with `HasChowModification.of_isPullback`, through two cartesian squares.
4. **Stacks 081F given Chow.** Apply `exists_isProper_baseChange_of_isLimit_of_hasChowModification`
   (vendored `ProperLimitStage/Basic.lean`) to `f₀ : Z ×_{D j₁} Y₀ ⟶ Y₀` over `D j₁`. At the limit, `f₀` is the base
   change of the proper `Z_∞ ⟶ lim D` (`isPullback_prodSnd`, a pasting of three cartesian squares). This gives a
   stage `j → j₁` where the base change of `f₀` is proper.
5. **Descent.** By `isPullback_prodSnd` again, that base change is the base change of `Z_j ⟶ D j` along the
   surjective, flat, quasi-compact `Y₀ ×_{D j₁} D j ⟶ D j`. Universal closedness descends along such maps (Mathlib
   `FlatDescent.lean`: `DescendsAlong @UniversallyClosed (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`). Separatedness
   and local finite type hold by base change, so `Z_j` is proper. `compIso` then moves this to
   `(Over.pullback (D.map (hj ≫ a₁))).obj Xi`.

## 2. Vendoring, and the earlier port's compatibility failures

The 73 files are the import closure of four upstream modules, minus what CloudW01Spread already has:
`ProperLimitStage/Basic`, `Limits/ChowLemmaNoetherian0200`, `SegreProdIso/Main` and
`Limits/DescendingMorphisms/Diagonal`. That is 21.3k lines, with no `sorry`, `axiom` or `native_decide`, and no
code that runs at build time. `scratch/ega-limit/vendor.py` generates them reproducibly from the read-only local
copy of the upstream repository at the pinned revision. It writes `SOURCE_MANIFEST.json` (the sha256 of each
source), a modification header in every file, and `LICENSE`, which is byte-identical to upstream. `NOTICE.md`
records the port changes. Two kinds of incompatibility had to be fixed, both VERIFIED:

- **`maxSynthPendingDepth = 3`.** The upstream lakefile sets this option for the whole library. Without it,
  `SegreEmbedding/SegreRing.lean` and `Limits/AffineIntoProjective.lean` fail instance synthesis. The fix sets
  the option at the top of each vendored file.
- **Four name clashes with CloudW07JacobiansCurves** (vendored frenzymath/Jacobian-Challenge), found by comparing
  every constant of `Main`'s environment with those of the vendored modules (`DumpMain.lean`, `DumpMine.lean`):
  - `AlgebraicGeometry.ProjectiveSpace` and its subnames: a different definition, indexed by a type of
    coordinates;
  - `Scheme.Hom.isSchemeTheoreticallyDominant_toImage`;
  - `HomogeneousLocalization.val_algebraMap`;
  - `HomogeneousLocalization.val_fromZeroRingHom`.

  The fix renames them in the vendored copies only: `StacksProjectiveSpace`, and the suffix `_stacks` on the other
  three. Import lines are left alone, and nothing in the contribution's statement mentions these names. SPECULATIVE:
  these four clashes are the "four compatibility failures" the earlier Stacks properness port stopped on.

## 3. Checks (all VERIFIED in this worktree; outputs in `scratch/ega-limit/`)

1. `lake build` of the vendored modules: 73 files, about 2 minutes. Logs: `build2.log` (before the renames) and
   `build4.log` (after).
2. Build tree: I copied the build of `~/dzq-wt/pazuki-dict` with reflinks. It is the same base plus one added
   Contrib file, with `Main` already built. Then `lake build +ZInQKernel.OneProof.Main
   +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.EGAIV_8_10_5_xii` succeeded (13,772 jobs; only the
   74 new modules were compiled).
3. `#discharges` with `Main`, `Discharges` and the contribution imported together: the output in the header
   above. The import itself shows that no constant clashes with `Main`.
4. `Statement.lean`: a verbatim copy of the Prop is `Iff.rfl`-equal to the original and is proved by the theorem
   (standard axioms).
5. `autofold.json`: discharges `egaIV_8_10_5_xii` with proof
   `_root_.ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof`, no leaves. `autofold.py --dry-run` reports
   "strict count: 34/11 on 45 -> 33/11 on 44; strictest 34/11 -> 33/11". The generated module, with line 1
   stripped (`FoldDryRun.lean`, `sixContactMin_of_open36` over `OpenAddedLeaves18`), compiles with standard
   axioms. The fold itself was not run: integrator's job.
6. The contribution imports the module that defines the statement (`ZInQKernel.Contrib.SpreadOut.Spread`), never
   `Main`, so folding it creates no import cycle. The file is 15 KB.

## 4. New leaves

None. The proof is self-contained over Mathlib and vendored Apache-2.0 proofs.

## 5. Files

- `ZInQKernel/Contrib/OneProof/EGAIV_8_10_5_xii.lean`: the contribution and its glue.
- `ZInQKernel/Contrib/OneProof/EGAProperLimit/`: 73 vendored files, `LICENSE`, `NOTICE.md`, `SOURCE_MANIFEST.json`.
- `scratch/ega-limit/`:
  - `log.md`: results log;
  - `vendor.py`: generates the vendored tree;
  - `Glue.lean`: the scratch proof;
  - `Statement.lean`, `Discharges.lean` and its output;
  - `DumpMain.lean`, `DumpMine.lean`: the clash scan;
  - `autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean`;
  - build logs.

## 6. What remains

Nothing for this target. Possible reuse:
- `hasChowModification_of_isAffine` (Chow over an affine, possibly non-Noetherian, base);
- `exists_affine_surjective_flat`;
- the descent pattern of step 5.

Any future contribution that vendors the same upstream Stacks files must import these copies rather than vendor its
own, or it will clash.
