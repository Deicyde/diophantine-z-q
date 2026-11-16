# dict-models: four Néron-model and group-law rows back to printed-form leaves

Task dict-models, 2026-11-16. Base e22df37c (origin/main; top module `TailZ41`, `sixContactMin_of_open34`). This is
model work; no human has reviewed it. No network: every SGA/BLR/GIT/EGA locator below is recalled and UNVERIFIED.

Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, with a reference),
**SPECULATIVE** (my argument), **UNVERIFIED** (a theorem number or wording recalled from memory).

## 1. Result

**Each of the four research fields is now proved exactly (statement unchanged) from a new leaf in the print's own
form.** The new leaves use only fields already in the bundles, `sga3_VIB_3_10` (research) and
`geomConnOfRationalPoint` (textbook). The 11-16 dictionary pass rated these four rows as consequences, because
each Lean statement equals its print only through a further theorem (SGA 3 VI_B 3.3, base change of a semi-abelian
group to `k̄` with Stacks 04KV, the gluing over connected components, EGA IV 18.8.8). That further theorem is now a
Lean proof in each case (cases 1–3), or is no longer needed (case 4).

| field (bundle `OpenResearchLeaves26`) | new leaf | proof of the field | other inputs | rating of the new leaf |
| --- | --- | --- | --- | --- |
| `sga7_IX_3_3_SH` | `DictModels.SGA7Pre.SGA7_IX_3_3_SHpre` | `sga7_IX_3_3_SH_of_pre` | `sga3_VIB_3_10`, `geomConnOfRationalPoint` | printed form (unread) |
| `raynaudSemistableSH` | `DictModels.RaynaudOr.RaynaudSemistableSHOr` | `raynaudSemistableSH_of_or` | `geomConnOfRationalPoint` | printed form under both readings of "semistable"; old reading risks remain |
| `mumfordGroupLaw` | `DictModels.MumfordConn.MumfordGroupLawConn` | `mumfordGroupLaw_of_conn` | none | printed form (unread) |
| `neronBaseChangeStrictHenselization` | `DictModels.NeronBLR72.BLR_7_2_1` | `neronBaseChangeStrictHenselization_of_BLR72` | none | printed form if BLR 7.2/1 is stated for all ramification-index-1 extensions (reading risk) |

Each new leaf is implied by the field it replaces (`pre_of_SH`, `or_of_field`, `conn_of_field`, together with the
bundle leaves where needed). For `BLR_7_2_1` this does not hold: the leaf is more general than the field, and it is a
leaf only because it is the printed theorem. So none of the new leaves can be false while the old field is true,
except possibly `BLR_7_2_1`, and that only if BLR's print is narrower (§5).

Contributions (VERIFIED: each compiles, no errors, no `sorry`, standard axioms):

* `ZInQKernel/Contrib/OneProof/SGA7IX33SHPre.lean` (imports `SGA7PersistsNF`)
* `ZInQKernel/Contrib/OneProof/RaynaudSemistableOr.lean` (imports `UnipotentForward`)
* `ZInQKernel/Contrib/OneProof/MumfordGroupLawConn.lean` (imports `MumfordRigidity`)
* `ZInQKernel/Contrib/OneProof/NeronBaseChangeBLR72.lean` (imports `StrictHenselizationPair`)

Autofold spec: `scratch/dict-models/autofold.json`, one spec with four discharges. The dry run is
`scratch/dict-models/autofold-dryrun.txt`. The counts on this base are strict 40/8 → 40/8 and strictest 39/9 → 39/9,
because the rows are still LEAF on e22df37c (the dictionary re-rating is not in this base). On a base where the
dictionary pass has re-rated these rows, the fold would turn up to four GLUE rows back into LEAF.
`#discharges` output and axioms: §6 (all four fields discharged, standard axioms).

## 2. `sga7_IX_3_3_SH`: `N⁰ ×_S S'` as printed

**Issue.** The field takes `U = idCompSet (N ×_O O')`, the identity component of the base change. The print's
`N⁰ ×_S S'` is the base change of the open subscheme `N⁰ ⊆ N`, i.e. the open set `pullback.fst ⁻¹' N⁰` of
`N ×_O O'`. The two sets agree by SGA 3 VI_B 3.3.

**New leaf** `SGA7_IX_3_3_SHpre`: the field word for word, except that the hypothesis on `U` is
`(U : Set _) = pullback.fst 𝒩.G.hom (Spec.map (ofHom (comapHom hO))) ⁻¹' idCompSet 𝒩.G`.

**Proof.** `preimage_eq` is the chain's `CToPrinted.idComp_baseChange h3 hG` (TailZ19, a Lean proof from
`SGA3_VIB_3_10` and `GeomConnOfRationalPoint`). The field and the leaf differ only in that hypothesis, so each
implies the other given the two bundle leaves (`sga7_IX_3_3_SH_of_pre`, `pre_of_SH`). VERIFIED.

**Rating: printed form.** The conclusion "`U → N'` is an open immersion with image `N'⁰`" is "`N⁰ ×_S S' → N'⁰` is an
isomorphism", since `N'⁰` is open (SGA 3 VI_B 3.10). Remaining risk, unchanged from the old row (UNVERIFIED): SGA 7 IX
may assume an algebraically closed residue field. Then the print is the restriction to such `O`, which is the
`SGA7_IX_3_3_SHcp` axis of gt-sga7/sga7-cp. `c` is any homomorphism whose generic fibre is an isomorphism: the
canonical map composed with an automorphism of `N'`, which preserves `N'⁰`. `K'/K` finite is a specialization.

## 3. `raynaudSemistableSH`: the conclusion as a disjunction

**Issue.** The field concludes `SemistableNeronModels A O`, i.e. `HasSemiAbelianIdentityComponent` of the
*geometric* special fibre `𝒩 ×_O κ̄`. If SGA 7 IX Déf. 2.2/3.1 reads semistability over `k(s)` (UNVERIFIED), the
print gives the `k(s)` form.

**The `k(s)` form, faithfully** (`HasSemiAbelianIdCompTorus`, `IsSemistableResT`). There is an open connected
subgroup `U ⊆ 𝒩_{k(s)}` and a flat surjective homomorphism `π : U → B` onto an abelian variety over `k(s)` whose
kernel is a torus. "Torus" is stated in the functor of points over `k̄`: `ker(U(R) → B(R)) ≅ (Rˣ)^r` for
`k̄`-algebras `R`, naturally in `k̄`-algebra maps. By Yoneda this says `(ker π)_{k̄} ≅ 𝔾_m^r`, which is the
definition of a torus over a field (SGA 3 IX 1.1; Borel 8.2; UNVERIFIED numbers). So the form does not assume the
torus split over `k(s)`, and it is weaker than unipotent-b's `IsSemistableRes`, which asks for a split torus
(`isSemistableResT_of_res`, VERIFIED).

**New leaf** `RaynaudSemistableSHOr`: the field's hypotheses word for word, with the conclusion
`(∀ 𝒩, 𝒩.IsNeronModel → IsSemistableResT 𝒩) ∨ SemistableNeronModels A O`. Under either reading the print gives it by
`Or.inl`/`Or.inr`.

**Glue PROVED: ascent from `k(s)` to `k̄`** (`isSemistable_of_resT`), for every DVR and every residue field
(perfect or not, separably closed or not). It uses only `GeomConnOfRationalPoint` (Stacks 04KV):

1. `hasSemiAbelian_pullback_bar`: the base change along `k → k̄` of a group scheme of finite type with a
   general-torus semi-abelian identity component has a split-torus semi-abelian identity component.
   - `U_{k̄}` is an open subgroup.
   - `U_{k̄}` is connected: `U` is connected, of finite type, quasi-compact (an open of a noetherian scheme), and has
     the rational point `e`. So it is geometrically connected by 04KV, and `connectedSpace_of_subsingleton` applies.
   - `B_{k̄}` is an abelian variety (proper, smooth and geometrically integral are stable under base change).
   - `π_{k̄}` is flat and surjective (base change along the `Over.pullback` square, `pbmap_isPullback`).
   - The torus clause transports along `Φ : (Spec R/k̄ ⟶ U_{k̄}) ≃* (Spec R/k ⟶ U)`.

   The transport is reduct-glue's `section Transport` (TailZ14, written for field isomorphisms), generalized to
   field extensions; only the connectedness step needed a new input.
2. Then `geomSpecialFibre 𝒩 ≅ (specialFibre 𝒩)_{k̄}` as group schemes (`pbCompIso`), and
   `hasSemiAbelian_of_iso` finishes.

**Field**: `raynaudSemistableSH_of_or h hGC` (VERIFIED).

**Rating: printed form**, with the `k(s)`-versus-`κ̄` reading item removed. Other readings stay open, unchanged from the
old row (UNVERIFIED):
* the print may assume an algebraically closed residue field (sga7-cp's `RaynaudSemistableSHcp` axis);
* it may require `m > 3` (locators.md R6);
* it may give a Galois-form conclusion.

Byproduct: the ascent also shows that unipotent-b's two semistability notions agree in one direction for every
residue field (`IsSemistableRes → IsSemistable`). The other direction is the still-open
`SemiAbelianDescendsSepClosed`.

## 4. `mumfordGroupLaw`: GIT 6.14 over a connected base, gluing in Lean

**New leaf** `MumfordGroupLawConn`: the field word for word with `ConnectedSpace S` added.

**Glue PROVED** (`MumfordGroupLawConn.lean`, §1, for any cover of `S` by pairwise disjoint opens `U i`):

* `glue_ext`: morphisms in `Over S` are determined by their base changes to the `U i`
  (`Scheme.hom_ext_of_forall` on the preimages `X.hom ⁻¹ᵁ U i`, via `pullbackRestrictIsoRestrict`).
* `glue_exists`: compatible families glue. This uses Mathlib's `Scheme.Cover.glueMorphisms` on
  `X.left.openCoverOfIsOpenCover (X.hom ⁻¹ᵁ U ·)`. On the overlaps, `i = j` is handled by the mono `ι`, and for
  `i ≠ j` the pullback has no points.
* `grpObj_of_pieces`: group objects on the base changes `P i F` glue to a group object on `F`. The proof goes through
  Yoneda (`GrpObj.ofRepresentableBy`). `Hom(T, F)` gets the group structure transported along the bijection
  `Ψ : (T ⟶ F) ≃ ∀ i, (P i T ⟶ P i F)`, and precomposition is a homomorphism (`comp_mulT`, `comp_oneT`), so the
  axioms come for free. `pb_eta`: the base changes of the glued identity are the given identities.

**Field** (`mumfordGroupLaw_of_conn`). The cover is by the connected components, indexed by `ConnectedComponents S`,
which are open because `S` is locally noetherian (gt-rigidity's `isOpen_connectedComponent_of_isLocallyNoetherian`).
On each component:
* the leaf's hypotheses pass by base change (proper, smooth, geometrically connected);
* the section is `pullback.lift (ι ≫ e) (𝟙 _)`;
* the abelian-variety fibres pass by the pasting lemma (`IsPullback.of_right`).

The glued identity has `left = e`, by `glue_ext` and `pb_eta`. VERIFIED.

**Rating: printed form.** GIT Thm 6.14 (3rd ed., Ch. 6; UNVERIFIED), as recalled, assumes `S` connected and locally
noetherian, `F → S` smooth and proper with a section, and one fibre an abelian variety. The leaf's hypotheses are at
least as strong: geometrically connected, and *every* field fibre an abelian variety with origin `e(s)`. Its
conclusion (a group object with identity `e`) is part of "abelian scheme with identity `e`". So the leaf is a
consequence of the print. Consumers are unchanged: `QMFamilyGroupLaw` still comes from the field, which is now a
theorem from the leaf.

## 5. `neronBaseChangeStrictHenselization`: BLR 7.2 Thm. 1 instead of BLR 1.2/2 with EGA IV 18.8.8

**Issue.** `IsSHSep O O₁` (strictly henselian DVR, `K₁/K` separable algebraic, `e = 1`, separable residue extension)
makes `O₁ ≅ O^sh` only through EGA IV₄ 18.8.8 (gt-shpair §2).

**Choice: the second option of the task** (state the leaf in BLR 7.2 Thm. 1's form). The first option was not
taken. It would define `O^sh` by its universal property and prove the pinning, which means:
* showing that `IsSHSep` extensions are ind-étale (finite separable subextensions with `e = 1` and separable residue
  field are essentially étale over `O`);
* henselian lifting of étale points.

That needs commutative algebra Mathlib 4.35 lacks (standard étale presentations of unramified extensions of DVRs); it
is SPECULATIVE that it would fit the time.

**New leaf** `BLR_7_2_1 := ReductGlue.NeronBaseChangeUnramifiedDVR`, the chain's existing statement (TailZ14), with no
new Lean statement. For DVRs `O ⊆ O'`:
* `O' ∩ K = O`;
* `K'/K` separable algebraic;
* every uniformizer of `O` irreducible in `O'`;
* `κ(O')/κ(O)` separable.

Then the base change of a Néron model is a Néron model. **Field**:
`GapSHPair.neronBaseChangeStrictHenselization_of_unramified`. Every clause of `IsSHSep` except "strictly henselian"
is a hypothesis of the 7.2 form, so no pinning is used. VERIFIED.

**Rating: printed form, with a reading risk.** BLR §7.2 Thm. 1 is recalled (UNVERIFIED) as stated for local
homomorphisms of DVRs of ramification index 1 with separable residue extension, for smooth group schemes of finite
type with a Néron model. The Lean leaf specializes it to abelian varieties and to separable algebraic `K'/K`.
Reading risk (as reduct-glue §5 already recorded): if the print covers only étale maps, strict henselization and
completion, this leaf exceeds it, and the old leaf with EGA IV 18.8.8 is the honest form. The flag in the autofold
spec says so. The new leaf is strictly more general than the old field (it does not ask `O'` to be strictly
henselian). That is fine only because it is the published statement; it should be checked against the print first
(`STATEMENT-CHECKS.md`).

## 6. Checks (all VERIFIED)

* Compile: each of the four files with `lake env lean`. No errors, no `sorry`.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` plus the four contributions: 13,699 jobs,
  success.
* Verbatim statements: `scratch/dict-models/Statements.lean` copies the four field statements from the tree and checks
  each one `rfl` against the original. It compiles.
* `#discharges` (`scratch/dict-models/Discharges.lean`, output `scratch/dict-models/discharges.txt`):

```
DISCHARGES [OpenResearchLeaves26.mumfordGroupLaw] by DictModels.MumfordConn.mumfordGroupLaw_of_conn
  still assumes: [DictModels.MumfordConn.MumfordGroupLawConn]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.neronBaseChangeStrictHenselization] by DictModels.NeronBLR72.neronBaseChangeStrictHenselization_of_BLR72
  still assumes: [DictModels.NeronBLR72.BLR_7_2_1]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.raynaudSemistableSH] by DictModels.RaynaudOr.raynaudSemistableSH_of_or
  still assumes: [DictModels.RaynaudOr.RaynaudSemistableSHOr, AVGlue.GeomConnOfRationalPoint]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves26.sga7_IX_3_3_SH] by DictModels.SGA7Pre.sga7_IX_3_3_SH_of_pre
  still assumes: [DictModels.SGA7Pre.SGA7_IX_3_3_SHpre, CToPrinted.SGA3_VIB_3_10, AVGlue.GeomConnOfRationalPoint]
  axioms: [propext, Classical.choice, Quot.sound]
```

  `GeomConnOfRationalPoint` and `SGA3_VIB_3_10` are fields of the current bundles (textbook and research).
* Fold check: the autofold dry run (`autofold-dryrun.txt`, line 1 stripped) compiles as
  `scratch/dict-models/FoldCheck.lean`. `HDec.HSyn.sixContactMin_of_open35` has axioms
  `[propext, Classical.choice, Quot.sound]`.

## 7. What remains

* Reading checks (no network): GIT 6.14's hypotheses (connected `S`); BLR 7.2/1's class of extensions; SGA 7 IX
  3.3 / 4.7 residue-field and `k(s)` readings; locators.md rows for the four new leaves.
* The integrator runs autofold on `scratch/dict-models/autofold.json` (on top of whatever fold is current; the spec
  names fields only) and does the usual build, axiom and hash checks.
