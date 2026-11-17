# cm-branch: the CM fibres of the six-contact estimate, routed through the manuscript

Task cm-branch (2026-11-17). Base: `wip/leaf-fold33b` d67ea55f (origin/main is an ancestor; top
`sixContactMin_of_open67`, TailZ74), merged at 09:40 with `origin/wip/leaf-fold33b` be9a6ba4 (top
`HDec.HSyn.sixContactMin_of_open72`, TailZ79). The dry runs were regenerated on the merged base (first built
on open67 with the same result). Line numbers of §2 refer to the first base (TailZ74 still exists). Results log: `scratch/cm-branch/log.md`. Marks: VERIFIED
(compiled, read in the tree or the manuscript), AUDIT-READ (read in the print by the upstream audit,
`docs/reviews/height-replacement/height/AUDIT.md`; this host has no network, a WebFetch to arXiv was
refused), STANDARD (published, exact reference), UNVERIFIED (theorem numbers from memory), SPECULATIVE.

## 1. Result

**The manuscript's CM paragraph (diophantine_zq.tex L581-631, "CM fibers") is formalized in Lean from the
leaves it cites; the case split CM / non-CM (L578-580, merged at L901-905) is a Lean proof; and the
chain's non-CM half is localized to fibres without CM, so the whole H route compiles without NoCM; and a
second dry run also prunes the moduli row's González–Rotger conjunct, taking `gonzalezRotgerThm512X6RCF`
off the route.** VERIFIED: the fold dry run

```lean
theorem HDec.HSyn.sixContactMin_of_open72_cm (r : OpenResearchLeaves53) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) (c : CMBranch.CMInputs) : ZInQ.SixContactMin
```

(`ZInQKernel/Contrib/OneProof/CMBranch/Top.lean`) compiles with only `propext`, `Classical.choice`,
`Quot.sound`. It is the current top `sixContactMin_of_open72` with one extra hypothesis `c` (the CM
inputs below), the chain copied verbatim down to `sixContactMin_of_open4_hf_pz_eb`, and that base replaced
by `sixContactMin_of_open4_cm`. A scan of the transitive constant closure
(`scratch/cm-branch/FieldUse2.lean`, output `fielduse-top.txt`) shows that the new top no longer depends
on NoCM: `G0FibreSimple.FibreComTrivial` (FS5), all of `FS5NoCM` (the `X₆` Kummer fibre, the
optimal-embedding conductor argument, `nocm_on_witness_le`, `elkies_sq`, …), `cmOptimalEmbedding` and
`x6ConicModel` are gone from the closure (89 constants), and nothing was added outside the new files.

**The R5ptProps prune, dry run (VERIFIED).** The files `CMBranch/No5A.lean` … `No5E.lean` (generated,
§6) copy the 1325-constant region of the chain affected by the moduli row's conjunct `R5ptProps` and by the
González–Rotger field types, with `R5ptProps := True` and the González–Rotger fields deleted. Their top

```lean
theorem HDec.HSyn.sixContactMin_of_open72_cm_no5 (r : OpenResearchLeaves53) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) (c : CMBranch.CMInputs) : ZInQ.SixContactMin
```

compiles with standard axioms, and a scan of the fields of the three top bundles that its closure reads
(`scratch/cm-branch/TopFields.lean`, output `topfields.txt`) gives: **read by the current top but not by the
new one: `OpenResearchLeaves53.gonzalezRotgerThm512X6RCF`; read by the new one but not by the current one:
none.** No constant named `…gonzalezRotgerThm512X6…` is left in the closure.

**The target, field by field.**

| top field | status after this task | why |
|---|---|---|
| `gonzalezRotgerThm512X6RCF` | **off the route** in the dry run `sixContactMin_of_open72_cm_no5` (unread: a PruneScan target for the fold) | its only use was the row conjunct `R5ptProps`, which only NoCM read |
| `x6CoarseModuliIdeal` | stays | also produces `X6Props` and the witness of the row (§2); now it also supplies the row's base witness in place of González–Rotger (`gonzalezRotgerX6Ab_of_coarseNoGR_no5`) |
| `elkiesX6StarEveryIdeal` | stays | also produces `π₆` and `R2X6PropsIff` of the row through `babaGranathRationalAb` (§2) |

So NoCM (FS5 and every input it had) and González–Rotger Thm 5.12 leave the route; the two `X₆` fields do
not, because they are not NoCM-only. The manuscript does not use `X₆` for the coordinate either
(L421-434: `Y₃` with the normalizer action and quotient `P¹_j`); re-sourcing that is a separate re-route of
R2.

**The CM inputs** (`CMBranch.CMInputs`): four new leaves and three new glue Props (§4):
`FowlerProp27`, `CMHeight62` (printed, cited by the manuscript), `CMjDegree`, `CMPotentialGood`
(classical, stated but not cited by the manuscript: Known issue 1); glue `CMHomFieldSplit` (matrix units
on A8's Hom-field model), `ReducedCMPeriod` (on-the-spot), `HeightAdditivityUpper`. A8 itself (the field
`L` with `[L:ℚ] ≤ D` over which every geometric endomorphism is defined) is **proved** for every fibre
without NoCM (`CMBranch/A8.lean`, `homFieldModel_of`), so the earlier composite glue `CMFibreSplit` is a
theorem (`cmFibreSplit_of`). Gaudron–Rémond Thm 1.4 and Faltings' Lemma 5
(lower half) are the chain's existing `R19_GaudronRemond` and `R20Lower`.

Files (all new, under `ZInQKernel/Contrib/OneProof/`, no `sorry`, no build-time code; each compiled with
`lake env lean` and built with `lake build`):

| file | content |
|---|---|
| `CMBranch/Arith.lean` (pure Mathlib) | Eq. (6.2)'s summand over Mathlib's `ModularForm.eta` and its expansion, the q-series estimate, the summand bound, `π√|Δ|/12 + 1 ≤ B_cm` |
| `CMBranch.lean` (imports `OneProof.H.LPrefix`) | the leaves and glue, `faltingsHeight_le_bcm`, `cmOutput_of`, `le_heightCcm_of_cmOutput`, `cmBranchOut_of`, `glueOutputs_of_branches`, `sixContactMin_of_branches` |
| `CMBranch/NonCM.lean` | `FibreSimpleNC` without FS5, `nonCMBranch_of` (the chain's `glueOutputs_of_leaves3_hf_pz_eb` restricted), `sixContactMin_of_cmBranch` |
| `CMBranch/Localize.lean` | the localized non-CM chain: `ModularConstituentNC` without FS5 (generated by `scratch/cm-branch/gen/mk_localize.py`) |
| `CMBranch/A8.lean` | A8 for every fibre without NoCM (`homFieldModel_of`), the glue `CMHomFieldSplit`, `cmFibreSplit_of` |
| `CMBranch/Open4.lean` | `sixContactMin_of_open4_cm`: the open4 generation without FS5 |
| `CMBranch/Top.lean` | `CMInputs`, the copied chain with `c` threaded, `sixContactMin_of_open72_cm` (generated by `gen/mk_top.py`) |
| `CMBranch/No5A.lean` … `No5E.lean` | the `R5ptProps`/González–Rotger prune dry run, `sixContactMin_of_open72_cm_no5` (generated by `gen/gen_no5.py`, `no5_edits.py`, `no5_split.py`) |

## 2. What the NoCM fields feed (VERIFIED by reading the chain)

| top field (OpenResearchLeaves48 at open67; OpenResearchLeaves53 at open72) | becomes | consumers |
|---|---|---|
| `gonzalezRotgerThm512X6RCF` | `gonzalezRotgerThm512X6` (`GR512Bridge.gonzalezRotgerThm512X6_of_rcf`, TailZ74 L1259) | `GRX6AbPrint.gonzalezRotgerX6Ab_of_print` (TailZ74 L309) → `gonzalezRotgerX6Ab` |
| `x6CoarseModuliIdeal` | `x6CoarseModuli` (`X6ALIdeal.x6CoarseModuli_of_ideal`, L1169) | `gonzalezRotgerX6Ab_of_print` and `GRX6AbPrint.x6ModuliWitness_of_coarse` (L309, L314) |
| `elkiesX6StarEveryIdeal` | `elkiesX6StarEvery` (L1170) | `ElkiesPrint.elkiesX6StarFunctionField_of_every` (L314) → `elkiesX6StarFunctionField` |

Downstream:

* `gonzalezRotgerX6Ab` → `x6Rows_of_open14_hf_gm_pz_eb` (`gonzalezRotger := …`, EichlerBoundCopy L2948) →
  `LeafAdopt.R1R2fpRepW ∧ X6Kummer.X6ConicModel`. `R1R2fpRepW` (LPrefix L5248) is the moduli row
  `∃ Y Φ X Ψ fY π₆, R1fpProps ∧ R1heckeProps ∧ X6Props ∧ R2X6PropsIff ∧ R1recProps ∧ X6Surj ∧ R5ptProps`;
  `R5ptProps` is González–Rotger Thm 5.12 on points of `X₆`. Also `gonzalezRotgerCountX6Ab` (TailZ27 L105).
* `elkiesX6StarFunctionField` → `elkiesX6StarPrinted` (TailZ36 L102) and `babaGranathRationalAb`
  (TailZ37 L91), which give `R2X6PropsIff` (`π₆ : X₆ → P¹` with the CM values) in the same row, and
  `x6ConicModel`.
* NoCM is `G0FibreSimple.FibreComTrivial` (FS5: `End_𝒪(P.A) = ℤ` at every point over `J(u)`), built in
  `gluePieces_of_open4_hf_pz_eb` (EichlerBoundCopy L2662) from the row's `R5ptProps`, `r.r5count`,
  `x6KummerFibre` (from `l.x6ConicModel`) and `l.cmOptimalEmbedding`. FS5 is consumed by `fibreSimple`
  (G5-G6; then Poincaré in the non-CM transfer, and inside `AfterG7` by `modelG3G6_of_leaves3` and
  `linkedTateLocal_of_leaves3_hf`) and by `KernelFieldExists` (`kernelFieldExists_of_split_hf''`); both
  feed `modularConstituent`.
* The height consumer: `glueOutputs_of_leaves3_hf_pz_eb` (EichlerBoundCopy L2574) always took `Or.inl`
  (`NonCMOutput`) of `GlueAssembly.GlueOutputs`, whose other disjunct `CMOutput h_F(A)` was already there
  with `CMOutput → h_F(A) ≤ C_cm` proved (`GlueAssembly.cm_branch_nat`, HDecomp/Assembly.lean L586).

So what the manuscript's CM branch must deliver in place of NoCM is `GlueAssembly.CMOutput h_F(A)` for
the fibre surface at a CM fibre (with Pazuki's bound and the theta point for the same `A`), and the non-CM
chain must be restricted to fibres without CM. Both are done here.

## 3. Lean steps and the manuscript lines they formalize

| Lean | manuscript | status |
|---|---|---|
| `CMBranch.NoCMAt`, `glueOutputs_of_branches` (case split on `NoCMAt u`) | L578-580 ("We treat these two cases separately"), L901-905 (merge) | proved |
| `homFieldModel_of`: A8's Hom field `L`, `[L:ℚ] ≤ D`, a rational fibre `PK/K ≤ L`, `G_L` fixing all homomorphisms between conjugates | A8 (L520-562), for every fibre | proved (G2 `FibreCoverExists`, `kernelField_of_model_hf`, `a8_field`; no NoCM) |
| `CMHomFieldSplit`: on that model, `E/L` with `End(E_{L̄})` an order `R`; `E² = E × E`; an `L`-isogeny `E² → (PK.A)_L` | L582-586 | GLUE (open) |
| `cmFibreSplit_of`: `CMFibreSplit` (model, `[L:ℚ] ≤ D`, `E`, `E²`, isogeny, CM order) | L520-586 | proved |
| `CMjDegree`: `#Pic(R) ≤ [L:ℚ]` | L586-587 | leaf, uncited in the manuscript (Known issue 1) |
| `FowlerProp27` at `n = D` | L588-593 | leaf, printed form |
| `CMPotentialGood`: an abelian-scheme model over some `L₁ ⊇ L` | L596-597 | leaf, uncited in the manuscript (Known issue 1) |
| "This extension does not change its stable Faltings height" | L597-598 | by construction: `CMHeight62` bounds the stable height of `E/L` by a model over `L₁` |
| `ReducedCMPeriod`: `√3/2 ≤ Im τ_σ ≤ √|Δ|/2` | L598-599 | GLUE, on-the-spot (sketch in §4) |
| `CMHeight62`: `h_F(E) ≤ avg_σ −(1/12) log(|Δ(τ_σ)|(Im τ_σ)⁶)`, `Δ = (2π)¹²η²⁴` | L600-604 | leaf, consequence of the printed formula |
| `summand62_eq_archSummand`: `−(1/12)log(|Δ(τ)| y⁶) = −log 2π + πy/6 − ½log y − 2Σlog|1−qⁿ|` | L600-604 (the displayed expansion) | proved |
| `rho_lt_hundredth`, `neg_tsum_log_le`: `ρ < 1/100`, `−2Σ ≤ 2ρ/(1−ρ)² < 200/9801` | L605-606 | proved |
| `archSummand_le`: `−½ log y < 1/10`, `−log 2π` discarded, summand `≤ πy/6 + 1` | L606-611 | proved |
| `faltingsHeight_le_bcm`, `bcm_of_fowler`: `h_F(E) ≤ π√|Δ|/12 + 1 ≤ D²3^{21000D²} + 1 = B_cm` | L608-612 | proved |
| `R19_GaudronRemond` (reused) over `L`, source `E²`, `g = 2`: `deg ≤ (28²⁵⁶ d max(h_F(E²), log d, 1)²)⁸¹⁹²` (`grKappa_two`) | L614-619 | existing leaf |
| `HeightAdditivityUpper`: `h_F(E²) ≤ 2h_F(E)`; "The maximum is at most `2B_cm`" | L620-621 | GLUE |
| `R20Lower` (reused): Faltings' height variation, lower half | L620-621 | existing (proved in Contrib from the printed lemma) |
| `cmOutput_of`: `CMOutput h_F(A)` | L622-624 | proved |
| `le_heightCcm_of_cmOutput` (via `cm_branch_nat`): `h_F(A) ≤ C_cm`, with `log 28 < 4`, `log d ≤ D`, `log(2B_cm) ≤ 2+2D+42000D²` | L624-628 | proved |
| `cmBranchOut_of`: theta point, Pazuki, `CMOutput` at a CM fibre | L901-905 (CM half); L907-960 unchanged | proved |
| `fibreSimpleNC_of_pieces_hf`: `A` absolutely simple at fibres without CM | L632-634 | proved (no FS5) |
| `Localize.lean`: G4 (`KernelFieldExistsNC`), G3/G5-G6 on G7's model (`ModelG3G6NC`), G8-G16 (`LinkedTateLocalNC`, `LinkedTateDataNC`, `AfterG7NC`), G2-G7 (`fieldDescentUnrNC`), `ModularConstituentNC` | L520-562 and L632-900 at fibres with `End⁰(A_ℚ̄) = B` | proved (the chain's proofs, localized; no FS5) |
| `nonCMBranch_of`, `sixContactMin_of_open4_cm`, `sixContactMin_of_open72_cm` | L632-905 | proved |

## 4. The new leaves and glue, and their rating

| leaf | statement (Lean) | source | printed form? |
|---|---|---|---|
| `FowlerProp27` | for an order `R` of an imaginary quadratic `k` (finite conductor `f`) and `1 ≤ n` with `#Pic(R) ≤ n`: `√|f²d_k| ≤ 2n² exp(21000n²)` | Fowler, Math. Proc. Cambridge Philos. Soc. 180 (2026) 607-641, Prop. 2.7, printed pp. 615-616 (AUDIT-READ) | **yes**, through the standard dictionary `h(Δ) = #Pic(𝒪_Δ)`, `Δ(𝒪_f) = f²d_k` (Cox Thm 7.7, Lemma 7.2, UNVERIFIED numbers); flag "unread here, read by the upstream audit" |
| `CMHeight62` | `E/K` of dimension 1 with an abelian-scheme group model `𝒢` of `E_L` over `𝓞_L` (`IsProper 𝒢.G.hom`) and periods `τ_σ` (`IsPeriodAt`: an analytic uniformization of `E(ℂ)_σ` with lattice `c(ℤ+τℤ)`): `h_F^st(E) ≤ (1/[L:ℚ]) Σ_σ −(1/12)log(|(2π)¹²η(τ_σ)²⁴| Im(τ_σ)⁶)` | Barquero-Sanchez–Cadwallader–Cannon–Genao–Masri, Res. Number Theory 3 (2017) art. 13, §6 Eq. (6.2), pp. 13-14 (AUDIT-READ: original Faltings metric, `Δ = (2π)¹²η²⁴`, the general formula after Silverman Prop. 1.1) | **consequence of the print**: the good-reduction case (finite term `0`), the `≤` half; reading risk: the exact display of (6.2) not read here. It also relies, like R19/R20 and H5, on the tree's `stableFaltingsHeight` (infimum of model heights, metric `(i/2)∫ω∧ω̄`) being Faltings' height; an independent model review checked the sign, the factor `1/12` and the normalization |
| `CMjDegree` | `E/L` of dimension 1 with `End(E_{L̄}) ≅ R` ⇒ `#Pic(R) ≤ [L:ℚ]` | none in the manuscript; Cox, *Primes of the form x²+ny²*, Thm 11.1 (UNVERIFIED number); the upstream audit (FINDINGS.md) sources the degree to Fowler §2.1 | yes, a consequence of `[ℚ(j(E)):ℚ] = h(R)`; Known issue 1 |
| `CMPotentialGood` | `E/L` with CM ⇒ an abelian-scheme group model of `E_{L₁}` for some finite `L₁/L` | none in the manuscript; Serre–Tate 1968 / Silverman AEC VII.5.5 (UNVERIFIED numbers); proved in [cmheight], proof of Thm 1.3, p. 15 (AUDIT-READ) | yes; Known issue 1 |

Glue:

* `CMHomFieldSplit` (the largest): for a fibre context whose object has CM (`End_𝒪(P.A) ≠ ℤ`) and A8's
  Hom-field model `(PK.A)_L`, an elliptic curve `E/L` with `End(E_{L̄})` an order of an imaginary quadratic
  `k`, the product `E²`, and an `L`-isogeny `E² → (PK.A)_L` (matrix units of `End⁰(A) = M₂(k)`,
  L582-586; the upstream audit's paragraph "CM reasoning" spells out the idempotent argument: `e₁₁` gives
  the elliptic image `E`, `e₂₂` another, the off-diagonal units inverse isogenies between them, and the
  corner algebra `e₁₁M₂(k)e₁₁ = k`). Needs images of endomorphisms as abelian varieties and Galois descent
  of the idempotents from `ℚ̄` to `L` (the Hom-field property). `CMFibreSplit` (A8 + this) is proved from
  it (`cmFibreSplit_of`).
* `ReducedCMPeriod` (on-the-spot; L598-599 has no citation): for `E/K` with `End(E_{K̄}) ≅ R` and every
  `σ : K → ℂ` there is a period `τ` of `E` at `σ` with `√3/2 ≤ Im τ ≤ √|Δ_R|/2`. Proof sketch:
  `End(E^σ_ℂ) ≅ End(E_{K̄}) ≅ R` (rigidity), so the period lattice is homothetic to a proper fractional
  `R`-ideal; choose a reduced basis (`|Re τ| ≤ 1/2`, `|τ| ≥ 1`), so `Im τ ≥ √3/2`; `τ` is a root of a
  primitive form `aτ² + bτ + c` of discriminant `Δ_R` with `a ≥ 1`, so `Im τ = √|Δ_R|/(2a) ≤ √|Δ_R|/2`.
* `HeightAdditivityUpper`: `h_F(A × Z) ≤ h_F(A) + h_F(Z)` (the half of additivity the chain did not
  need; the chain's `HeightAdditivity` is `≥`).

## 5. The localization of the non-CM chain (done)

Every use of FS5 and of `FibreSimple` on the chain's path to `ModularConstituent` is at the fibre context
of the statement being proved. `Localize.lean` copies that path with each Prop
`∀ … P, FibreCtx Y Φ π u P → …` replaced by its `NC` version over
`FibreCtxNC := FibreCtx ∧ NoCMAt Y Φ π u`: `conjMapsOnHomFieldNC_of` (FS5 at the fibre becomes
`NoCMAt`), `kernelFieldExistsNC_of_pieces_hf`, `kernelFieldExistsNC_of_split_hf`,
`endDivisionNC_of`, `modelG3G6NC_of(_leaves3)`, `modelEndRank4NC_of_qmEndRank`,
`linkedTateLocalDNC_of_tateBridge35`, `linkedTateLocalNC_of_D`, `linkedTateLocalNC_of_leaves3_hf`,
`linkedTateDataNC_of_local`, `afterG7NC_of3_hf_pz_eb`, `fieldDescentUnrNC`,
`modularConstituentGNC_of_ranges(_T14)`, `modularConstituentNC_of_G`,
`modularConstituentNC_of_field_hf_pz`. The proofs are the originals; only the context is threaded.

## 6. The prune dry run, and the remaining steps

**How the dry run is built** (`scratch/cm-branch/gen/`): `AffectedList.lean` computes, in the closure of
`sixContactMin_of_open72_cm`, every constant that (transitively, through values, types and structure
constructors) mentions `LeafQM.AV.R1R2fp`, `LeafAdopt.R1R2fpRepW`, `LeafQM.AV.R5ptProps`,
`GRDict.GonzalezRotgerThm512X6` or `GR512Bridge.GonzalezRotgerThm512X6RCF` (1325 constants, with their
declaration ranges). `gen_no5.py` replays the scope commands of each of the 28 source modules and copies the
affected declarations verbatim, renaming every copied name `c` to `c_no5` (so name resolution is the
original's), with `R5ptProps` replaced by `R5ptProps_no5 := True` (same arity: every destructuring pattern
still works). `no5_edits.py` makes the hand edits, each marked `-- cm-branch edit`: the producers of
González–Rotger content (`r5ptProps_of_thm512`, `gonzalezRotgerX6Ab_of_witness/_of_coarse/_of_print`,
`r5fp_of_point`, `r5fp_of_rep`, `gonzalezRotgerThm512X6_of_rcf`) are deleted; `R5fp` is dropped from the
`r1r2fpRep_of_split…W` producers; the bundle fields `r5`, `gonzalezRotgerThm512X6(RCF)` and their assignments
are deleted; `gonzalezRotgerX6Ab` is filled by the new `gonzalezRotgerX6Ab_of_coarseNoGR_no5` (the witness of
`x6ModuliWitness_of_coarse`, from `x6CoarseModuli` and `shimuraMainThmIDeligneY3AbU`). `no5_split.py` splits
the result into five files under 130 KB.

**Remaining.**

1. **Fold** (hand-fold, `scratch/cm-branch/autofold.json`): switch `frozenTarget` to the new top with the
   seven `CMInputs` statements as new fields, and drop `gonzalezRotgerThm512X6RCF` (unread). Done in place
   (as pi0-fold did for `R1pi0Props`) rather than by copies, the edits are the ones listed above on the
   original declarations. Afterwards PruneScan should also find the carried-but-unread lower fields
   (`r5count`/`gonzalezRotgerProp56X6`, `cmOptimalEmbedding`, `x6ConicModel` in the older bundles).
2. **Prove the glue** `CMHomFieldSplit`, `ReducedCMPeriod`, `HeightAdditivityUpper`.
3. **Re-source R2** to `Y₃ → P¹_j` (L421-434) to drop the `X₆` fields (separate task).
4. Count: the fold removes one field (`gonzalezRotgerThm512X6RCF`, GLUE pending review in kinds.tsv) and
   adds 3 GLUE and 4 leaves (2 flagged uncited): the GLUE count rises by 3 until step 2, so the autofold would
   need `--allow-rise`. This is the price of following the manuscript, whose CM paragraph rests on more glue
   than the fleet's NoCM.

## 7. Compile log and the fold dry run

All the files compiled (`lake env lean`) and built (`lake build`) on the base with the chain built to
TailZ79 (`scratch/cm-branch/build4.log`; first on TailZ74, `build2.log`). Axioms (`scratch/cm-branch/Axioms.lean`,
`Axioms2.lean`, `FieldUse2.lean`): `propext`, `Classical.choice`, `Quot.sound` for every main theorem,
including `sixContactMin_of_open72_cm` and `sixContactMin_of_open72_cm_no5`. The fold dry runs are `Top.lean` and `No5E.lean` (the autofold script cannot
express a re-route: no field is discharged by these theorems). `#discharges` (with `Main`, `Discharges`,
`CMBranch` and `CMBranch.Top` imported; `scratch/cm-branch/discharges.txt`): "36 open hypotheses, 15863
theorems checked, 19 discharge one", none of them a cm-branch theorem — as expected, since this
contribution re-routes and proves no top field. The top-field scan of §1 is the relevant check.

## 8. Known issues

1. **Uncited classical inputs in the CM paragraph.** L586-587 (`[ℚ(j(E)):ℚ] = h(Δ)`), L596-597
   (potentially good reduction, "since its `j`-invariant is integral") and L598-599 (reduced CM period)
   carry no citation. They are classical and true; here they are the leaves `CMjDegree`, `CMPotentialGood`
   (proposed sources, UNVERIFIED numbers) and the on-the-spot glue `ReducedCMPeriod`. The upstream audit
   attributes the degree to Fowler §2.1 and good reduction to [cmheight] p. 15; neither was read here.
2. **The CM branch needs A8 without NoCM** (resolved). The manuscript's `d = [L:ℚ] ≤ D` for the CM fibre
   is A8's field (L520-562), proved before the case split. The chain's `KernelFieldExists` bundles A8 with
   B1's descent datum, which uses NoCM; A8 alone does not, and `homFieldModel_of` proves it for every
   fibre from the chain's lemmas.
3. **The `X₆` fields are not NoCM-only** (§2): `x6CoarseModuliIdeal` and `elkiesX6StarEveryIdeal` stay;
   R2 would have to be re-sourced to the manuscript's `Y₃ → P¹_j` (L421-434). The manuscript itself never
   uses `X₆ = X₀(6,1)` as a coarse moduli scheme.
4. **Reading risk for (6.2).** Only the audit's reading of Eq. (6.2) is available here; the leaf is the
   inequality the manuscript uses, for good reduction everywhere.
5. No Gross–Zagier or Tian–Yuan–Zhang argument is used. No consumer statement was changed; the new
   `…NC` Props are restrictions of existing ones (each implied by the original, e.g.
   `modularConstituentNC_of`, `fibreSimpleNC_of`).
