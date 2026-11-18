# d2a6-reroute: D2 and A6 off the SGA 7 rows

Task d2a6-reroute, 2026-11-17. Base: wip/lane74b (6b404a20) with `git merge origin/wip/sz-raynaud` (ff8a03ac7, no
conflicts); nothing else merged. Results log: scratch/d2a6-reroute/log.md.

Marks: **VERIFIED** means compiled or read in a named file on this host. **STANDARD** means published, with an exact
reference. **SPECULATIVE** means judgement. Theorem numbers recalled from memory are **UNVERIFIED** (no network).
Model work, no human review.

## 1. Result

**Verdict.**

- **The SGA 7 IX 3.5 row leaves.** `sga7_IX_3_5_ForwardGeom_Def34` is out of the closure of the new top theorem
  `HDec.HSyn.sixContactMin_of_open73`. Standard axioms only; VERIFIED (§5).
- **`ElliotWildInertiaTrivial` discharges a field.** It replaces that row, together with the integral model.
- **D2 is rerouted through `RaynaudWildNF`** (L814-818, sz-raynaud): Raynaud's criterion as printed by Silverberg–Zarhin
  (L816), then the ELLIOT sentence (L817-818).
- **A6 is rerouted to the proper model and its universal abelian scheme** (L529-530). The same goes for a third
  reader of R6 that sz-raynaud did not list, the kernel field's good reduction (L557-558).
  - **The stop rule did not trigger.** A6 needs nothing outside the manuscript except textbook facts, all proved in
    Lean: the valuative criterion, `ℤ_(p) → O`, and rigidity (§3.2).
  - The one statement A6 needs is the manuscript's own L443-477 in sgr-split's form,
    `SGRSplit.ShimuraIntegralModelRep`. It goes back into the bundle as `shimuraIntegralModelRep`
    (consequence, pending reading, GLUE).
- **The SGA 7 Cor. 3.3 row does not leave, and no D2/A6 reroute can remove it.** Its live readers are SS2 and SS3,
  semistable reduction after base change, behind the height rows R18-R22 and `StableHeightFinite`, which are neither
  D2 nor A6 (§4). This confirms sz-raynaud's finding: Cor. 3.3 feeds only the persistence of semistability. The
  lead's target "both SGA 7 rows leave" is reached for IX 3.5 only.
- **The fold also discharges `raynaudSemistableSHOr` (SGA 7 IX 4.7).** It comes from `silverbergZarhinThm35`
  (sz-raynaud's autofold, included because `RaynaudWildNF` needs SZ 3.5 itself), so the fold removes a second SGA 7
  field.

**Count** (this base's docs/one-proof/kinds.tsv, H rows, the script's `counts`):

| | fields | strict LEAF / GLUE | strictest LEAF / GLUE |
|---|---|---|---|
| before (TailZ79, `OpenResearchLeaves53`) | 29 | 5 / 24 | 5 / 24 |
| after (`OpenResearchLeaves54`, BypassFold.lean) | 30 | 5 / 25 | 5 / 25 |
| autofold of `raynaudSemistableSHOr` alone (strict dry run) | 29 | 5 / 24 | 5 / 24 |

What changes (from `gen_bypass.py`'s output):
- **Removed:** `raynaudSemistableSHOr` (LEAF) and `sga7_IX_3_5_ForwardGeom_Def34` (GLUE, consequence pending review).
- **Added:** `silverbergZarhinThm35` (LEAF), `elliotWildInertiaTrivial` (ELLIOT, GLUE) and `shimuraIntegralModelRep`
  (consequence, GLUE).
- **Net:** GLUE rises by one. The strict autofold would refuse this without `--allow-rise`. The lead decides whether
  the trade (a row on SGA 7, which the manuscript never cites, for the manuscript's own two statements) is wanted.

## 2. What the IX 3.5 row fed (traced, VERIFIED)

`scratch/d2a6-reroute/TaintD.lean` and `TaintD2.lean` work on the closure of `sixContactMin_of_open72` (274,299
constants).
- **TaintD** is the declaration-level taint from the IX 3.5 fields. Its output is `taintD-out.txt`: 28 carrier
  bundles and 91 tainted declarations.
- **TaintD2** finds carriers by constructor type and adds `ResearchLeaves3EB`. Its output is `taintD2-out.txt`.

The field travels as follows:
- `sga7_IX_3_5_ForwardGeom_Def34` (TailZ79) → `sga7_IX_3_5_ForwardGeom` (generations 36EBCF … 20GMEB).
- → `semistableUnipotent` (19GMEB … 14GMEB, by `semistableUnipotent_of_forwardGeom`).
- → R6, computed in `raynaudCriterionNF_of14_hf_gm_eb` (Raynaud + IX 3.5 + Néron).
- → R6 is a binder of `sixContactMin_of_open19…17` and the field `r6` of generations 9EB … 2EB.
- → `gluePieces_of_open4_hf_pz_eb` reads `r.r6` three times.

The three readers of R6:

| reader | where | manuscript step | uses of R6 |
|---|---|---|---|
| D2 | Consumers' `linkedTateLocal_of_leaves3_hf` → TailH `LTLocal.linkedTateLocal_of_tateBridge35` → … → `raynaudPlace_of_R6`, `torsFix_of_descent`, `tateWildK_of_R6` | L814-818 (wild inertia of `F = L_v(A[3])`) | `(σ-1)² = 0` on `A[ℓⁿ]`, then the `p`-power period of wild elements |
| A6 | TailI `modelG3G6_of_leaves3` → TailF `qmModelG3_of` → `LeafQM.AV.QML3.goodReduction` | L529-530 (good reduction outside the places over `S`), used at L752-753, L781 | Raynaud's criterion route to good reduction at every `v ∤ 3` |
| kernel field | Consumers' `kernelFieldExists_of_split_hf''` → … → `kernelFieldExists_of_pieces_hf` → TailC `good_of_QML3` → `QML3.goodReduction` | L557-558 ("every conjugate has good reduction" outside `T`) | the same |

The third row is new: sz-raynaud's report names only D2 and A6.

## 3. The reroute (Lean, all compiled, standard axioms)

### 3.1 D2 (`ZInQKernel/Contrib/OneProof/D2WildNF.lean`)

TailH's proofs are kept, with `SZRaynaud.RaynaudWildNF` in place of R6:

- **`isWildInertia_of_wild_gen`**: an element over a wild `σ ∈ G_{ℚ_p}` is wild inertia (`IsWildInertia`) at the
  valuation ring `normVS f`.
- **`RaynaudPlaceFix`** is the manuscript's form: a wild `σ'` that fixes `A[m]` fixes `A[ℓⁿ]`.
  - **`raynaudPlaceFix_of_wildNF`** is TailH's `raynaudPlace_of_R6` over `F = K(A[m])`, with `RaynaudWildNF` in
    place of R6.
  - **`raynaudPlace_of_fix`** and **`raynaudPlace_of_wildNF`** give TailH's weaker `RaynaudPlace`.
- **`torsFix_of_wildNF`** is `torsFix_of_descent` with no unipotence step and no `p`-power period: L817-818 gives the
  fixing directly.
- **The consumers:** `torsFixWild_of_raynaudFix`, `tateWildK_of_wildNF`, `localGlue_of_leaves_wildNF`,
  `torsFixWildOdd_of_wildNF`, `torsFixWildE_of_twist_wildNF`, `tateWildKE_of_wildNF`,
  `localGlue_of_descent_wildNF`.

### 3.2 A6 (`ZInQKernel/Contrib/OneProof/A6IntModel.lean`)

**`D2A6.hasGoodReduction_of_intModel`** takes `ShimuraIntegralModelRep`, an object `PK : QML3 K` (`K ⊇ ℚ`), a
valuation subring `O ⊆ K` and a prime `p > 324` that is not a unit of `O`. It concludes
`PkgI2.HasGoodReduction (toGrp PK.A) O`: an abelian scheme over `O` whose generic fibre is `PK.A` as a group object.
The proof is L529-530 spelled out:

1. **The classifying point.** `PK` becomes a `QMAbScheme` over `Spec K` (sgr-split's `qml3AsQMAb_of`). The integral
   model's universal property, on `Spec K` as a locally noetherian `ℤ_(p)`-scheme, gives `g : Spec K → 𝒴` with
   `PK = g^*𝒜`.
2. **The lift to `O`.** There is a ring map `ℤ_(p) → O`: integers prime to `p` are units of the local ring `O`
   (`isUnit_of_not_dvd`). By the valuative criterion (Mathlib's `IsProper.eq_valuativeCriterion`), `g` extends to
   `ℓ : Spec O → 𝒴`. The square commutes because maps to `Spec ℤ_(p)` are unique.
3. **The abelian scheme.** `ℓ^*𝒜`, with the pulled-back group law, is proper, smooth and geometrically connected,
   since base change preserves each property.
4. **Its generic fibre.** Pasting the two pullback squares, the generic fibre is the pullback of `𝒜` along `j ≫ ℓ = g`,
   hence isomorphic to `PK.A`. The identity goes to the identity (`eta_pullback_fst`, `eta_left_comp`), so the
   isomorphism is a homomorphism by rigidity (`MulRigidity.isMonHom_of_geometricallyIntegral`). This gives an
   isomorphism of group objects (`Grp.mkIso'`).

Then, with the readers adapted:
- **`HDec.LTGoodRed.goodRedTorsionT T`** is generated (gen/gen_goodred.py). It is lt-goodred's `goodRedTorsion` with
  the hypothesis "good reduction where `3` is a unit" replaced by "good reduction where a prime `p ∉ T` is not a unit".
- **`QMModelG3U`** is `QMModelG3` with `T = {3}` replaced by `T324`, the primes `≤ 324`, the manuscript's minimal `S`
  (L383-384). `qmModelG3U_of` proves it from NOS and the integral model.
- **`modelG3G6_of_U`** and **`modelG3G6_of_leavesU`** use `T324 ⊆ T(u)` (`T324_subset_T`, from `mem_S_mul_of_le`).

**Stop-rule check (A6).** Every step above is in the manuscript or is a textbook fact proved in Lean:
- the valuative criterion: Mathlib;
- `ℤ_(p) → O`: elementary;
- rigidity: the kernel's proved `MulRigidity`, Mumford, *Abelian varieties*, §4 Cor. 1, UNVERIFIED locator.

Rigidity is needed only because the kernel's moduli isomorphism (`QMFamFibre`) does not record the group law. In the
manuscript the moduli objects are abelian schemes, so their isomorphisms are group isomorphisms. No on-the-spot leaf
was added, so the rule did not stop the build.

### 3.3 The replacement of R6 (`ZInQKernel/Contrib/OneProof/D2A6Wrap.lean`)

`D2A6.R6U := SZRaynaud.RaynaudWildNF ∧ SGRSplit.ShimuraIntegralModelRep`.

The wrappers have the originals' signatures with `hR6 : R6U`:
- `raynaudPlace_of_R6U`, `tateWildK_of_R6U` and `torsFix_of_R6U` (D2);
- `modelG3G6_of_leaves3U` (A6);
- `good_of_QML3U` (the kernel field). Its `3 ∈ T` argument becomes `T324 ⊆ T`.

### 3.4 The chain (`ZInQKernel/Contrib/OneProof/D2A6Chain.lean`, generated)

`scratch/d2a6-reroute/gen/gen_chain.py` uses piczero-char0's `copylib.py`, extended so that it also replays
`attribute [-instance]`. It copies 102 declarations and 29 structures verbatim, renamed `X ↦ X_u` / `XU`. These are
every declaration reachable from `sixContactMin_of_open72` through declarations that take an R6 hypothesis or a bundle
carrying an IX 3.5 field. The edits:
- `PkgI2.RaynaudCriterionNF` is replaced by `R6U`.
- The three IX 3.5 fields are replaced by one field `r6u : R6U`.
- `raynaudCriterionNF_of14_hf_gm_eb` is replaced by `r.r6u`.
- The five terminal readers are replaced by the wrappers.

The result is `sixContactMin_of_open72_u` on `OpenResearchLeaves53U`, which is `OpenResearchLeaves53` with
`r6u : R6U` in place of `sga7_IX_3_5_ForwardGeom_Def34`. It compiles with no error.

### 3.5 The fold (bypass; scratch/d2a6-reroute/gen/gen_bypass.py → BypassFold.lean)

The generator follows fold-b105's pattern. It is built on TailZ79 and compiled with `lake env lean`.

- **`OpenResearchLeaves54`** has 28 fields:
  - `sga7_IX_3_5_ForwardGeom_Def34` is replaced by `elliotWildInertiaTrivial` and `shimuraIntegralModelRep`;
  - `raynaudSemistableSHOr` is replaced by `silverbergZarhinThm35`.
- **`openResearchLeaves53U_of_OpenResearchLeaves54`** sets
  `r6u := ⟨raynaudWildNF_of_leaves sz elliot (neronSchemeModelExistsNF (neronSchemeExtensionExists_of_dedekind n.neronSchemeExtensionDedekind)), n.shimuraIntegralModelRep⟩`
  and `raynaudSemistableSHOr := raynaudSemistableSHOr_of_sz35 sz`.
- **`sixContactMin_of_open73 r t l := sixContactMin_of_open72_u (…) t l`**.

The integrator's steps:
1. Copy BypassFold.lean to the next `TailZ<j>.lean`.
2. Switch Main to `OpenResearchLeaves54` / `sixContactMin_of_open73`.
3. Replace the two kinds rows by scratch/d2a6-reroute/kinds-rows.tsv and drop their claims rows.

The script writes nothing under ZInQKernel/ or docs/.

## 4. Why Cor. 3.3 stays (VERIFIED, taintD-out.txt section COR33)

`sga7_IX_Cor3_3_Def34` becomes `sga7_IX_3_3_SHpre`, then `sga7_IX_3_3_SH`, then `sga7_IX_3_3` and
`semistablePersistsSHcp`. Its live readers:

- **`ss1_ss3_of14NF_hf_gm_pz_eb`**: SS3, `SemistablePersists`.
- **`researchLeaves9_of_open14_hf_gm_pz_eb`**: SS2, `semistableNeronBaseChange := semistableNeronBaseChange_noSGA3 …
  r.sga7_IX_3_3 …`.

Both feed `heightRowsNo20_of8_hf_eb` (R18 Javanpeykar, R19 Gaudron–Rémond, R21 Bost, R22 Pazuki,
`StableHeightFinite`) and `r20Lower_of8_hf_eb`. These are the literature height bounds over the stable Faltings height,
which the kernel defines through semistable models over a common field. None of them is D2 or A6.

The manuscript treats the stable Faltings height as a standard notion (L598) and has no persistence step. Removing
Cor. 3.3 would mean rerouting the height rows to a definition of the stable height that does not need SGA 7 IX 3.3.
That is outside this task.

## 5. Checks (all VERIFIED on this host)

| check | outcome | file |
|---|---|---|
| `lake build` of TailZ79, SZRaynaud; then D2WildNF, A6IntModel, D2A6Wrap, D2A6Chain; then Main, Discharges | success, 0 errors | (build logs in /tmp, not kept) |
| `lake env lean` D2R.lean, A6U.lean (scratch originals of the Contrib files) | 0 errors, standard axioms | d2r-out.txt, a6u-out.txt |
| `lake env lean` D2A6Chain.lean | 0 errors; `sixContactMin_of_open72_u`: [propext, Classical.choice, Quot.sound] | chain-out1.txt |
| `lake env lean` BypassFold.lean | 0 errors; `sixContactMin_of_open73`: standard | bypass-out.txt |
| closure of `sixContactMin_of_open72_u` (274,179 constants) | absent: `SGA7_IX_3_5_ForwardGeom_Def34`, `SGA7_IX_3_5_ForwardGeom`, both `PkgI2.RaynaudCriterionNF`, `GapNeron.RaynaudCriterionNF`, `QML3.goodReduction`, `raynaudPlace_of_R6`, `torsFix_of_descent`, `modelG3G6_of_leaves3`, `good_of_QML3`, `sorryAx`; present: `RaynaudWildNF`, `ShimuraIntegralModelRep`, `SGA7_IX_Cor3_3_Def34`; control (`open72`): the old ones present | closurecheck-out.txt |
| `#print axioms` of the 28 new theorems (D2 12, A6 10, wrappers 5, chain top 1) | all [propext, Classical.choice, Quot.sound] | discharges-output.txt |
| `#discharges` (base Main + this task's modules) | 30 open hypotheses, 12157 theorems checked, 163 discharge one; 146 of them are projections of the copied structures (noise, Known issues); the genuine line for this fold is `raynaudSemistableSHOr by SZRaynaud.raynaudSemistableSHOr_of_sz35`; the bypass of `sga7_IX_3_5_ForwardGeom_Def34` cannot be expressed as a discharge | discharges-output.txt |
| autofold spec for the outright discharge (`raynaudSemistableSHOr` from `silverbergZarhinThm35`), strict dry run with this base's `scripts/one_proof/autofold.py` (`must_be_glue` at line 202) | strict 5/24 on 29 → 5/24 on 29, strictest 5/24 → 5/24, accepted without `--allow-rise`; the dry-run module compiles, `sixContactMin_of_open73` standard axioms | autofold.json, autofold-dryrun.txt, AutofoldDryRun.lean.txt, autofold-dryrun-compile.txt |

## 6. The new leaves, rated

| field | rating | provenance line |
|---|---|---|
| `silverbergZarhinThm35` (`SZRaynaud.SilverbergZarhinThm35`) | **LEAF** (published; flag "reading 11-17") | (b) cited at diophantine_zq.tex L816: Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.5, p. 406, read from the page image 11-17 (sz-raynaud) |
| `elliotWildInertiaTrivial` (`SZRaynaud.ElliotWildInertiaTrivial`) | **ELLIOT** (kind consequence, counts GLUE) | (a) the uncited sentence at L817-818; true and standard (SGA 7 I Exp. IX Prop. 3.5, UNVERIFIED number, with wild inertia pro-`p`) |
| `shimuraIntegralModelRep` (`SGRSplit.ShimuraIntegralModelRep`) | consequence, **GLUE** (pending reading) | (a)+(b): the manuscript's construction L443-477 from Buzzard, Duke Math. J. 87 (1997), Thm 2.1 and Cor. 2.3 (cited at L444), used at L529-530; sgr-split's literature reading (Kottwitz 1992 §5, Buzzard 1997, Morita 1981) pending; restricted to `p > 324` and polarization-free |

## 7. Manuscript check

One line per manuscript step this work formalizes or relies on.

| tex lines | step | verdict |
|---|---|---|
| L383-384 | `S` contains all primes `≤ 324` | **OK** (used as `T324 ⊆ T(u)`, proved from the kernel's `S_mul`) |
| L443-477 | proper model of `Y₃` over `ℤ[1/30]` from Buzzard Thm 2.1 / Cor. 2.3 at `V_1(5)`, full five-marking, `Isom_𝒪(𝒪/3, A[3])`, free `G_5`-quotient; "represents exactly the full-three moduli problem" | **unverified**: Buzzard 1997 not read (no network); the construction is not formalized and enters as the leaf `shimuraIntegralModelRep`. One reading point: the manuscript's objects carry "its canonical principal polarization", the kernel's are polarization-free; the two functors agree when that polarization is determined by `(A, ι)` (relative Lemma P), which the text asserts but does not prove |
| L529-530 | "The proper model and its universal abelian scheme give good reduction outside the places over `S`" | **gap filled**: the step needs (i) the `K`-point classifying `A` by the fine moduli property; (ii) its extension to `Spec O_v` by the valuative criterion for the proper model, with `ℤ_(p) → O_v`; (iii) the base change of the universal abelian scheme; (iv) the identification of its generic fibre with `A` as a group scheme (fine moduli, rigidity). None is written; all are proved in Lean (`D2A6.hasGoodReduction_of_intModel`). The model is over `ℤ[1/30]`, so the conclusion holds outside `{2,3,5}`, stronger than stated; the kernel uses it outside `S` |
| L557-558 | outside `T` "every conjugate has good reduction" | **OK** given L529-530: each conjugate is again a fibre (an object over `K`); in Lean `good_of_QML3U` at every embedding `K → ℚ̄` |
| L752-753, L781 | `A` has good reduction outside `T ∪ {ℓ}` / at `p ∉ T ∪ {3,5}` | **OK** given L529-530 (`T ⊇ S`); in Lean `qmModelG3U_of` + `modelG3G6_of_U` (`G3Out` at `T324 ⊆ T(u)`) |
| L814-815 | `F = L_v(A[3])` (`A[5]` if `p = 3`) has degree `≤ DG₀` over `ℚ_p` | **OK**: `[F : L_v] ≤ #GL₄(𝔽₃) = 24261120 ≤ G₀`, `#GL₄(𝔽₅) = 116064000000 = G₀` (computed), `[L_v : ℚ_p] ≤ [L : ℚ] ≤ D`; the kernel's `torsFixWildOdd` proves the bound (`card_GL4_three`, `card_GL4_five`) |
| L816-817 | Raynaud's criterion (Silverberg–Zarhin Thm 3.5) gives semistable reduction over `F` | **OK**: `n = 3` (or `5` at `p = 3`) is `≥ 3` and prime to `p`, and the torsion is rational over `F` (sz-raynaud's reading of the print, 11-17) |
| L817-818 | "Its wild inertia acts trivially on each `V_ℓ(A)` with `ℓ ≠ p`" | **gap filled**: no citation. It follows from SGA 7 I Exp. IX Prop. 3.5 (inertia acts on `T_ℓ` with `(σ-1)² = 0` under semistable reduction; number UNVERIFIED) and wild inertia being pro-`p`. Entered as the ELLIOT leaf; sz-raynaud's `elliot_of_semistableUnipotent` derives it from those two facts in Lean. The manuscript also takes it at `F`; the kernel applies it over the number field `K(A[m])` at the place of `embP`, which is equivalent (same inertia groups) |
| L819-821 | the break bound and upper numbering make all ramification groups above `U₀` trivial | **unverified** (not this task's step; D2's consumers downstream are unchanged) |

## 8. Known issues

1. **GLUE rises by one** (5/24 on 29 → 5/25 on 30), because ELLIOT and the integral model count GLUE. The fold
   therefore needs the lead's acceptance; a strict autofold would need `--allow-rise`. The IX 3.5 row it removes was
   itself GLUE (pending review). The 4.7 row it removes was LEAF and is replaced by SZ 3.5 (LEAF).
2. **Cor. 3.3 stays** (§4); the lead's two-row target is not reachable through D2/A6.
3. **`shimuraIntegralModelRep` returns to the bundle** after sgr-fold had removed it (11-15). There its only reader was
   `HeckeVertWitness`, now proved by route NV; here it is A6 and the kernel field. Its pending-reading flag (relative
   Lemma P, level at `3 ∣ D`) carries over unchanged. Its form is restricted to `p > 324`.
4. **`#discharges` noise**: 146 of 163 lines are projections of the copied structures (`…U.field`), as in
   raynaud-narrow and piczero-char0. Each assumes its bundle and discharges nothing.
5. **A large generated copy**: `D2A6Chain.lean`, 4386 lines, 102 declarations and 29 structures.
   - If another fold changes a carrier first, rerun TaintD.lean, TaintD2.lean, gen_chain.py and gen_bypass.py, in
     that order. The generators stop with an error when an edit target is missing.
   - If the lead folds sz-raynaud's autofold first, `raynaudSemistableSHOr` will already be `silverbergZarhinThm35`.
     gen_bypass.py then dies at its check (`OpenResearchLeaves53 lacks raynaudSemistableSHOr`) and needs one line
     changed: map the existing field instead of replacing it.
6. **`ReductSplit.SemistableUnipotent._proof_2`** (an elaborator auxiliary proof term) is still in the closure of
   `open72_u`; the statement `SemistableUnipotent` itself is absent. This is harmless, but the closure check reports
   it.
7. **No PruneScan was run.** After the reroute some textbook or research fields may have lost their last reader
   (e.g. `mulEtaleAbelianScheme`, read by the dropped R6 producer). `neronBaseChangeStrictHenselization` is still read
   by the Cor. 3.3 conversions.
8. The FieldTaint-style script (`Taint79.lean`, from the first run) did not finish in 20 minutes and was killed. The
   declaration-level TaintD/TaintD2 replaced it.

## 9. Files

- **New under `ZInQKernel/Contrib/OneProof/`** (none imports `ZInQKernel.OneProof.Main`): `D2WildNF.lean`,
  `A6IntModel.lean`, `D2A6Wrap.lean`, `D2A6Chain.lean` (generated).
- **`scratch/d2a6-reroute/`:**
  - log.md;
  - drafts D2R.lean, A6U.lean, Wrap.lean;
  - TaintD.lean, TaintD2.lean, ClosureCheck.lean, Discharges.lean and their outputs;
  - gen/ (copylib.py, gen_goodred.py, gen_chain.py, header.lean, gen_bypass.py, copied.txt);
  - BypassFold.lean, kinds-rows.tsv;
  - autofold.json, autofold-dryrun.txt, AutofoldDryRun.lean.txt;
  - Taint.lean, Taint79.lean (the first run's field taint).
