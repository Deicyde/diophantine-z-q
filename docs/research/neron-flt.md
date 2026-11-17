# neron-flt: Néron models over henselian DVRs from the FLT development; `NeronDVRLocal` reduced to descent from `R^sh`

Task neron-flt, 2026-11-16. Base: wip/neron-ext 901a0efd, merged with origin/main c1e4ed1b. This was model work with
no human review. Results log: `scratch/neron-flt/log.md`.

Marks used below:
* **VERIFIED**: compiled, or read in a file.
* **STANDARD**: published, with an exact reference.
* **UNVERIFIED**: a locator recalled from memory (there is no network here).
* **SPECULATIVE**: a judgement not checked.

## 1. Main result

**Target not reached.** `neronSchemeExtensionExists` is not removed without a new leaf. The fold is count-neutral:
`strict count: 16/21 on 37 -> 16/21 on 37` (VERIFIED, autofold dry run).

**What is proved instead (VERIFIED, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`):**
* **Néron models over henselian DVRs.** The bulk of BLR's construction is now a Lean theorem:
  * `NeronFLT.exists_neron_of_henselian`: an abelian variety over the fraction field of any henselian DVR has a
    Néron model;
  * the inputs behind it are BLR Ch. 3–5: smoothening, weak Néron models, the group law, and finite étale descent;
  * the proof is a port of the FLT development's theorem to Lean 4.35: 576 modules, built, with name clashes renamed.
* **neron-ext's leaf `NeronExt.NeronDVRLocal` is reduced to one new leaf**, `NeronFLT.NeronDescentSH`.
  * `NeronDescentSH` is descent of the existence of a Néron model from the strict henselization `R^sh` to `R`
    (BLR §7.2 Thm 1 / §6.5, the "if" half; locator UNVERIFIED).
  * Hence `neronSchemeExtensionExists` follows from this one leaf: `neronSchemeExtensionExists_of_descentSH`.
    EGA IV 8.10.5 (xii) is already proved in the tree (`ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof`).
* **group-law-dvr's leaf follows from the same leaf.** `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDVR` is
  BLR 1.4/3 over every DVR. It lives on branch wip/group-law-dvr; a verbatim copy is proved here:
  `NeronFLT.GLD.neronSchemeExtensionDVR_of_descentSH`. So after integration one leaf `neronDescentSH` replaces both
  `neronSchemeExtensionExists` and `neronSchemeExtensionDVR`.

```lean
-- ZInQKernel/Contrib/OneProof/NeronFLT/Henselian.lean
theorem NeronFLT.exists_neron_of_henselian (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R] (A : PkgI3.AbVar K) :
    ∃ N : Over (Spec (CommRingCat.of R)), CToPrinted.IsNeronModelOver R K N ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj N ≅ A.X)
-- ZInQKernel/Contrib/OneProof/NeronDVRLocalSH.lean
theorem NeronFLT.exists_neron_of_descentSH (R K) … (h : NeronDescentSH) (A : PkgI3.AbVar K) : ∃ N, …  -- any DVR
theorem NeronFLT.neronDVRLocal_of_descentSH (h : NeronDescentSH) : NeronExt.NeronDVRLocal
theorem NeronFLT.neronSchemeExtensionExists_of_descentSH (h : NeronDescentSH) :
    ZInQ.Contrib.NeronC.NeronSchemeExtensionExists
-- ZInQKernel/Contrib/OneProof/NeronSchemeExtensionDVRSH.lean
theorem NeronFLT.GLD.neronSchemeExtensionDVR_of_descentSH (h : NeronDescentSH) : NeronFLT.GLD.NeronSchemeExtensionDVR
```

**The new leaf (exact text, VERIFIED):**

```lean
def NeronDescentSH : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (K₁ : Type) [Field K₁] [Algebra K K₁] (O₁ : ValuationSubring K₁)
    (hO : O₁.comap (algebraMap K K₁) = (ValuationRing.valuation R K).valuationSubring),
    GapSHPair.IsSHSep (ValuationRing.valuation R K).valuationSubring O₁ hO →
    ∀ A : PkgI3.AbVar K,
      (∃ N₁ : Over (Spec (CommRingCat.of O₁)), CToPrinted.IsNeronModelOver O₁ K₁ N₁ ∧
        Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O₁ K₁)))).obj N₁ ≅
          (A.baseChange K₁).X)) →
      ∃ N : Over (Spec (CommRingCat.of R)), CToPrinted.IsNeronModelOver R K N ∧
        Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj N ≅ A.X)
```

**Rating: LEAF, published, in printed form as recalled.** Locator UNVERIFIED; the strict henselization is pinned
by `IsSHSep` as in the chain's leaf `GapSHPair.NeronBaseChangeStrictHenselization`.
* *Printed, as recalled:* BLR, *Néron models* (1990), §7.2 Thm 1 and §6.5. For a DVR `R` with strict henselization
  `R^sh`, a smooth `K`-group scheme of finite type `X_K` has a Néron model over `R` if and only if `X_K ⊗ K^sh` has one
  over `R^sh`.
* The leaf is the "if" direction, specialised to an abelian variety `A`.
* `R ⊆ K` is Mathlib's `(ValuationRing.valuation R K).valuationSubring`. Its elements are exactly the image of `R`
  (`ValuationRing.mem_integer_iff`).
* `IsSHSep O O₁` means: strictly henselian DVR, `K₁/K` separable algebraic, ramification index 1, separable residue
  extension. As gt-shpair recorded, it characterizes `O₁` as `R^sh` up to isomorphism over `R` (EGA IV₄ 18.8.8).
  This is the same pinning, and the same reading risk, as the existing leaf.
* The leaf is over genuine definitions only: Mathlib, `PkgI3.AbVar` and `CToPrinted.IsNeronModelOver` (BLR §1.2
  Def. 1).
* Proposed flag: `locator UNVERIFIED (BLR 7.2 Thm 1 / 6.5: Néron models descend from R^sh to R); R^sh pinned by
  IsSHSep`.
* Proposed `docs/research/locators.md` row (I did not edit that shared file): *BLR, Néron Models (1990), §7.2 Thm. 1
  (base change and descent of Néron models along R → R^sh), with §6.5; the "if" direction for abelian varieties.*

**`#discharges`** (VERIFIED, `scratch/neron-flt/Discharges.lean` → `discharges.txt`):

```
DISCHARGES [OpenTextbookLeaves13.neronSchemeExtensionExists] by NeronFLT.neronSchemeExtensionExists_of_descentSH
  still assumes: [NeronFLT.NeronDescentSH]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves13.neronSchemeExtensionExists] by NeronFLT.extension_of_descentSH
  still assumes: [ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii, NeronFLT.NeronDescentSH]
#discharges: 45 open hypotheses, 13605 theorems checked, 16 discharge one
```

`#print axioms` gives the three standard axioms for:
* `exists_neron_of_henselian`, `exists_neron_of_descentSH`, `neronDVRLocal_of_descentSH`, `extension_of_descentSH`
  and `neronSchemeExtensionExists_of_descentSH`;
* `GLD.neronSchemeExtensionDVR_of_descentSH` (`dvrcheck.txt`).

**Autofold specs:**
* `scratch/neron-flt/autofold.json`: on the current chain, it discharges `neronSchemeExtensionExists` with
  `_root_.NeronFLT.neronSchemeExtensionExists_of_descentSH {n}.neronDescentSH` and adds the leaf `neronDescentSH`
  (kind `published`, with the flag above).
  * `autofold.py --dry-run` reports `16/21 on 37 -> 16/21 on 37`.
  * Its module, with line 1 stripped (`AutofoldDry.lean`), compiles. `sixContactMin_of_open39` has the standard
    axioms. VERIFIED.
* `scratch/neron-flt/autofold-after-neron-ext.json`: the variant for when neron-ext's fold (field `neronDVRLocal`)
  is applied first. It discharges `neronDVRLocal` with `neronDVRLocal_of_descentSH`. Not dry-run, since that fold is
  not in this base.

## 2. The FLT theorem and the port

**The theorem (VERIFIED, read in `~/flt-src` @ 6e837e75):**
`GoodReductionJacobian.RelativeGroupLaw.exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing`.
* *Hypotheses:* `R` a domain, `IsDiscreteValuationRing R`, `HenselianLocalRing R`. Henselian, **not** strictly
  henselian; no condition on the residue field.
* *The abelian variety:* `K` the fraction field, and `AK → Spec K` with a relative group law and
  `AbelianSchemePropertyBundle` (smooth, proper, connected fibres).
* *Conclusion:* `B → Spec R` with a commutative relative group law and `NeronModelPropertyBundle R K` (smooth,
  separated, locally of finite type, quasi-compact, and `genericFibreRestrict` bijective for every smooth
  `T → Spec R`; this is BLR §1.2 Def. 1). There is also an isomorphism of the generic fibre with `AK` respecting the
  group laws.

**Where henselian is used (VERIFIED, grep).** Only in the group-law step and its subtree:
* Hensel lifting of smooth points over finite étale local DVR extensions;
* `DescentAction.effective_of_finiteEtale` (finite étale descent of schemes in which every finite set lies in an
  affine open);
* `exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing`: that affine-open property for smooth group
  schemes over a henselian DVR.

The proper model (`exists_modelFamily_finite_catchesIndexOnePoints_of_isProper`) and the smoothening step take any
DVR.

**The port (VERIFIED).** The closure has 577 modules (`scratch/neron-flt/closure.txt`).
* **Location.** 576 modules are copied to `ZInQKernel/Contrib/OneProof/NeronFLT/Vendor/AnthropicFLT/<upstream path>`
  (6.7 MB, every file under 150 KB). `P2M.Util` is Cloud Worker 2's copy.
* **What was changed:**
  * header comments;
  * relocated imports;
  * the upstream lakefile options, as `set_option` lines;
  * changes forced by Lean 4.33.1 → 4.35.0 and Mathlib db584cd6 → v4.35.0, each marked `-- [port]`.
* **The Lean 4.35 changes:**
  * The monoidal API of presheaves of modules over `CommRingCat` moved to `PresheafOfModulesOfCommRing`.
  * Instance search no longer sees `CommRing ((T ⋙ forget₂ CommRingCat RingCat).obj X)`. The fix is a file-local
    instance plus the `instanceSearchTypes` backward flag, as in Mathlib's own `Presheaf/Monoidal.lean`.
  * `TFAE.out` is 1-indexed.
  * `isMaximal_comap_of_isIntegral_of_isMaximal` became `…_under`; likewise `isMaximal_of_isIntegral_of_isMaximal_comap`.
  * Renames: `Ideal.bot_prime` → `Ideal.isPrime_bot`; `ULift.ext` now takes implicit points; `MvPolynomial.coeff`
    is a projection.
  * Three trailing `rfl` became redundant, and one `simp only` became `try simp only`.
  * Backward-compatibility elaboration flags were added in a few files.
  * For 9 modules the 4.35 bodies are Cloud Worker 3's port of the same upstream files, with its namespace wrapper
    removed (`tools/unwrap.py`).
* **Audit (`tools/audit_diff.py` → `audit.txt`).** Every difference from upstream is one of:
  * an import line;
  * a `set_option` line;
  * an `_nflt` rename;
  * a line inside a `-- [port]` block;
  * one of the 9 Cloud-Worker-3 bodies.

  No statement changed apart from the renames.
* **Name clashes with the chain (VERIFIED).** The scan compared 9714 constants of the port with 197382 non-library
  constants of Main, Discharges and the imports. 58 names are shared.
  * 7 are realized `eq_1`/`congr_simp` lemmas, which do not block imports.
  * The rest clash with CloudW07JacobiansCurves: the `Scheme.Modules` tensor API, the `SheafOfModules` monoidal
    instances, `GeometricallyIrreducible.geometricallyConnected`, `IsRegularLocalRing.isDomain` and
    `Smooth.isRegularLocalRing_stalk`.
  * Two clash with CloudB3W16Dimension's Stacks depth: `Module.depth` and
    `Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes`.
  * These 19 names were renamed with the suffix `_nflt` in 47 files (`tools/rename_clash.py`; each header records
    it).
* **Build.** `Build completed successfully (9623 jobs)` for the theorem's module (build5.log, and build7.log after
  the renames). No `sorry` is reported, and grep finds no `sorry`/`axiom`/`native_decide` in the vendored files.
* **Notices.** Following the earlier FLT vendorings, the directory holds:
  * `LICENSE`;
  * `NOTICE` (upstream notice plus a modification paragraph);
  * `NOTICE.upstream` and `ATTRIBUTION.upstream.md`;
  * `SOURCE_MANIFEST.neron-flt.json` (576 modules with the sha256 of each upstream file).

  There is no repository-root NOTICE.md in this tree; earlier vendorings keep their notices per directory.
* **Namespace.** The FLT declarations keep FLT's own namespaces (`NeronModelInfra`, `GoodReductionJacobian`,
  `P2MW.…`), as in the CloudB2 and CloudW02 FLT vendorings. The reason: the modules are disjoint from those
  vendorings' modules, so their names are disjoint, and wrapping 576 files would have needed CloudW03's opens shim
  throughout. This task's own code is in namespace `NeronFLT`.

**Bridge (`NeronFLT/Henselian.lean`, 120 lines).**
* `relativeGroupLawOfGrpObj` is CloudW03's definition restated over the unwrapped names.
* `isNeronModelOver_of_bundle'` is neron-ext's lemma, likewise restated.
* `exists_neron_of_henselian` builds the `AbelianSchemePropertyBundle` from `PkgI3.AbVar`: smooth, proper, and
  connected fibres from geometric integrality.

**Reduction (`NeronDVRLocalSH.lean`, 130 lines).**
* `valSubEquiv : R ≃+* (ValuationRing.valuation R K).valuationSubring`, which makes `O` a DVR.
* gt-shpair's `exists_comap_eq` and `isSHSep_inertia` give the strict henselization `O₁` inside `L̄`. It is
  henselian, so the FLT theorem applies to `(A_L)_{K₁}`.
* Then the leaf gives the Néron model over the given presentation `R_v` of `(𝓞_L)_v`.

## 3. Why the descent stays a leaf

`(𝓞_L)_v` is never henselian. Descending a Néron model `N^h` from `R^h` (or `R^sh`) to `R` needs **effective** descent
along a non-finite flat map, equivalently gluing along the elementary distinguished square
`(Spec K ← Spec K^h → Spec R^h)`.
* **What the ported tools give.** FLT's `effective_of_finiteEtale` needs `R → R'` finite étale. Every étale
  neighbourhood of `v` through which `N^h` descends is a localization of a finite `R`-algebra, which may be ramified
  at the other primes over `v`. For example, a cubic field in which `p` factors as `w₁w₂²` has `w₁` with `e = f = 1`,
  and every field containing it is ramified above `w₂` (SPECULATIVE that such neighbourhoods cannot be avoided). So
  finite étale descent does not apply.
* **Why FLT's method does not generalize.** FLT's construction gets points of the special fibre over finite étale
  local extensions. That is Hensel's lemma and fails over a non-henselian `R`.
* **What BLR use.** BLR descend via quasi-projectivity of the Néron model (§6.4, Raynaud) and descent of
  quasi-projective schemes with a compatible ample bundle (§6.1); both locators UNVERIFIED. Neither is in Mathlib
  4.35, the tree, or the 577-module FLT closure (grep of `~/flt-src` for henselization descent: none, VERIFIED).
* **Alternatives considered.** Splitting the leaf into "descent to an étale neighbourhood" plus "Nisnevich gluing
  for AF schemes" gives statements that are not printed in that form. So the single printed BLR statement is kept.

## 4. Files

* `ZInQKernel/Contrib/OneProof/NeronDVRLocalSH.lean`: the contributor file. It imports `NeronFLT.Henselian` (and, through it,
  `NeronSchemeExtensionExists`, which defines `NeronDVRLocal`), `StrictHenselizationPair` and `EGAIV_8_10_5_xii`, and
  never `OneProof.Main`. It contains the leaf, the reduction, and `neronSchemeExtensionExists_of_descentSH`.
* `ZInQKernel/Contrib/OneProof/NeronSchemeExtensionDVRSH.lean`: the verbatim copy of group-law-dvr's
  `NeronSchemeExtensionDVR` (textually identical, checked by `diff`) and its proof from the leaf. Upon integration
  next to `MumfordGroupLawNeron.lean`, `Iff.rfl` between the two copies is the remaining one-line check.
* `ZInQKernel/Contrib/OneProof/NeronFLT/Henselian.lean`: the bridge.
* `ZInQKernel/Contrib/OneProof/NeronFLT/Vendor/AnthropicFLT/`: the port, 576 files plus notices and manifest.
* `scratch/neron-flt/`:
  * `log.md`;
  * `closure.txt`, `modules.txt`;
  * `tools/` (closure, port, unwrap, fix, tfae, flags, patch_pm, rename_clash, audit_diff, chk.sh);
  * `clash/` (dump files and `clashes.txt`);
  * `Discharges.lean`, `discharges.txt`, `DVRCheck.lean`, `dvrcheck.txt`;
  * `autofold.json`, `autofold-after-neron-ext.json`, `AutofoldDry.lean`, `audit.txt`;
  * build logs `build1..8.log`, `build-main.log`.

## 5. Remarks for the integrator

* Count: the fold is neutral on the current chain. Combined with group-law-dvr's F2 fold (DVR form), the single leaf
  `neronDescentSH` stands for both Néron existence leaves. That is the same count as group-law-dvr's planned
  follow-up, with a smaller leaf: descent instead of existence.
* The port duplicates, under renamed names, monoidal instances that CloudW07 also provides: FLT's
  `Scheme.Modules.monoidalCategory_nflt` and CloudW07's `Scheme.Modules.monoidalCategory` are both global instances
  on `X.Modules`. Only modules importing both are affected: the contributor files, Discharges, and the generated fold
  module, all of which compile. A future file that uses `⊗` on `X.Modules` after importing both may see an instance
  ambiguity (SPECULATIVE).
* Building the 576 modules took about 10 minutes here, with lake's parallelism and LEAN_NUM_THREADS=8.
* The discharge check on a hosted runner will need to build them too.
