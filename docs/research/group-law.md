# group-law: the chain's use of `mumfordGroupLaw` proved from *GIT* Thm 6.14 over a discrete valuation ring; the field itself is not removed

Task group-law, 2026-11-16. Base 0caafe66 (wip/group-law). Results log: scratch/group-law/log.md. Model work, no human
review.

Marks: **VERIFIED** means compiled, or read in a named file on this host. **STANDARD** means published mathematics
with a reference. **SPECULATIVE** means judgement. **UNVERIFIED** marks a theorem number recalled without a source
(no network).

## 1. Verdict

**Target missed: `mumfordGroupLaw` is not removed (no −1).** The field is `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw`:
*GIT* Thm 6.14 over **every** locally noetherian `S`, non-reduced bases included. It is not proved here, and I found
no route to it in the tree. Over a non-reduced base the theorem is Grothendieck's deformation argument. That
argument needs:
* obstruction theory over Artinian thickenings;
* Grothendieck's existence theorem;
* rigidity over the base.

None of these is in Mathlib, the fork, or the vendored libraries (§4).

**What is proved (VERIFIED, no `sorry`, standard axioms).** The field's **only** use in `frozenTarget`'s closure follows
from *GIT* Thm 6.14 over the spectrum of a **discrete valuation ring**. That use is `QMFamilyGroupLaw`: QM families over
proper smooth curves over ℚ.

```lean
theorem LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr (hD : ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR) :
    LeafQM.AV.R1UnivRigid.QMFamilyGroupLaw
```

The new leaf `MumfordGroupLawDVR` is the field's statement with `S = Spec R`, where `R` is a DVR. It is strictly weaker
than the field (`dvr_of_field : MumfordGroupLaw → MumfordGroupLawDVR`). Where the local ring is a field, the group law needs no leaf
(`grpObj_of_isField`). Everything else is proved in Lean:
* the local rings of a smooth curve are fields or DVRs;
* the local group laws spread out to neighbourhoods;
* the local laws glue, because on field points they are the fibres' group laws (field-level rigidity).

| | before | after the narrowing fold (§5; compiled in an overlay) |
|---|---|---|
| field | `mumfordGroupLaw : MumfordGroupLaw` (any locally noetherian `S`) | `mumfordGroupLaw : MumfordGroupLawDVR` (`S = Spec` of a DVR) |
| count | 1 LEAF (pending review) | 1 LEAF (printed form, special case of the print) |
| net | | **0** (no −1), leaf strictly weaker |

The swap is **not autofold-compatible**: the old generations' field type is `MumfordGroupLaw`, and no theorem can fill
it from the DVR leaf. It needs an in-place fold like rigid-prune's: four consumer sites and one field type per bundle
generation (§5). **That fold compiles (VERIFIED, in an olean overlay outside the repository).**
* `frozenTarget` builds with field type `MumfordGroupLawDVR`.
* `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
* `MumfordGroupLaw` is no longer in `frozenTarget`'s closure.

Evidence: scratch/group-law/fold/ (narrowing.patch, foldcheck.txt).

## 2. The field and its consumers (VERIFIED)

* Statement: `ZInQKernel/Contrib/OneProof/MumfordRigidity.lean` L82. Its kinds.tsv row: research, published, LEAF, flagged
  "pending review", locator UNVERIFIED.
* **Consumers in `frozenTarget`'s closure** (scratch/group-law/ClosureCheck.lean → closure_check.txt). Only
  `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw` (OneProof/H/TailZ40.lean) uses `MumfordGroupLaw`. It is called
  from three places:
  * `HDec.HSyn.x6Rows_of_open14` (TailZ23);
  * `HDec.HSyn.researchLeaves9_of_open14` (TailZ23, twice);
  * `DCY3Used.y3Connected_of_leaves` (Contrib, used by TailZ34).

  So the chain needs exactly `QMFamilyGroupLaw`: for every QM family over a proper smooth curve `S/ℚ` whose field
  fibres are `QML3` objects, the family underlies a `QMAbScheme`.
* **rigid-prune's two sites are gone.** Rigid-prune found two places that need the universal clause on non-abelian
  families:
  * N1: `MCRGlue.QuotientP1Coordinate` and `modelCoordinateResidue_of_quotient'`;
  * N2: `HDec.ModelGlue.exists_genFib_to_Y` and `heckeVertWitness_of_curveBijIso`.

  Neither is in the closure any more: the NV route replaced QuotientP1Coordinate. I reran rigid-prune's scan
  (scratch/group-law/RigidScan.lean, scan_*.txt): 34 constants mention `R1univProps` in their value. The two new since
  rigid-prune:
  * `SGRDirect.elkies_coordinate` applies the universal clause to Elkies' family, which comes from an Ab clause, so
    it is fine on abelian schemes;
  * `GapST.cm_pointW` only destructures `R1fpProps`.

  The non-Ab `R1fpProps` appears in field types only in old generations (OpenResearchLeaves ≤ 9, OpenAddedLeaves ≤ 8,
  OpenGlue ≤ 7).

  **Consequence (SPECULATIVE, not attempted):** the field could be pruned with no new leaf, the target outcome, by
  re-typing those old generations and their consumers to the abelian-scheme forms. Every remaining use of the
  universal clause is on abelian schemes. But that changes about 74 definitions and 255 typed constants of existing
  modules (scan_defs.txt, scan_typed.txt), which the fold contract forbids ("no existing constant may change").

## 3. The Lean (VERIFIED)

All files are new, under `ZInQKernel/Contrib/OneProof/` (1,544 lines in total). Each compiles with `lake env lean`, and
`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.MumfordGroupLawRed`
succeeds (13,704 jobs). Their imports contain no `OneProof/H/TailZ` module above 22 except TailZ40, which TailZ23
already imports, so a fold may import them from TailZ23 without a cycle (checked by an import BFS, log).

| file | content |
|---|---|
| `GroupLawGlue.lean` | `FibreHyp` (the field's fibre hypothesis); `isAbVarFibre_of_isPullback`, `fibreHyp_of_isPullback` (the hypothesis passes to base changes); `LocalLaw F e` (a group law on `F ×_S T` for an open `T ⊆ S`, identity the base change of `e`); `mulP_pt`, `invP_pt` (on field points a local law is the fibre abelian variety's law, by the chain's `isGrpFibre_of_rigidity`, i.e. field-level rigidity); `glue_of_rel` (gluing over the cover by the local opens; compatibility on field points of reduced overlaps, `hom_ext_pts`); **`exists_grpObj_of_localLaws`**: local laws through every point and `F`, `F×_S F`, `(F×_S F)×_S F` reduced ⇒ `∃ GrpObj F, η = e`. |
| `GroupLawStage.lean` | `exists_grp_stage_Q`: spread-out's `exists_grp_stage` (verbatim proof) carrying an invariant of the stages. |
| `GroupLawLocDiagram.lean` | verbatim copy of gt-blr's Mathlib-only `Spec R_𝔭 = lim Spec R[1/s]` (avoids importing BLRLocalizes, which imports TailZ24). |
| `GroupLawSpread.lean` | `exists_stage_law` (generic cofiltered limit: a group law on `F ×_S lim D` with identity `e` descends to a stage, then its identity is made equal to `e` by `exists_map_eq`); **`localLaw_of_stalk`**: a group law on `F ×_S Spec Γ(S,V)_𝔭` with identity `e` gives a `LocalLaw` whose open contains `𝔭`. |
| `GroupLawStalks.lean` | `grpObj_of_stalkLaws` (group laws at all `Γ(S,V)_𝔭` ⇒ group law on `F`); `stalkData`; **`grpObj_of_isField`** (over a field the group law exists outright: the fibre at the identity point is `F`); `isDomain_of_maximalIdeal_eq_span`; **`stalk_field_or_dvr`**, `field_or_dvr_localization` (for `S` smooth of relative dimension 1 over a field, every local ring is a field or a DVR, from the fork's `ZInQ.Contrib.Dim` and Mathlib's `ringKrullDim_stalk_eq_coheight`). |
| `MumfordGroupLawRed.lean` (final) | the leaves `MumfordGroupLawDVR`, `MumfordGroupLawLocal`; `local_of_field`, `dvr_of_local`, `dvr_of_field`; the narrowed forms `MumfordGroupLawCurve` (base smooth of relative dimension 1 over a field) and `MumfordGroupLawRed` (reduced base); **`mumfordGroupLawCurve_of_dvr`**, **`mumfordGroupLawRed_of_local`**; `LeafQM.AV.R1UnivRigid.exists_qmAbScheme_of` (rigid-prune's `exists_qmAbScheme_gl` verbatim, with the group law over `S` as hypothesis); `qmFamilyGroupLaw_of_curve`, **`qmFamilyGroupLaw_of_dvr`**, `qmFamilyGroupLaw_of_local`. |

`#discharges` (scratch/group-law/Discharges.lean → discharges.txt) checks 2,994 theorems and finds 7 discharges, none
from these files. That is expected: no new theorem has type `MumfordGroupLaw`. The `mumfordGroupLaw` line it prints is
the existing `mumfordGroupLaw_of_core`. `#print axioms` of the main theorems: `[propext, Classical.choice, Quot.sound]`.

### Proof of `mumfordGroupLawCurve_of_dvr` (the chain's case)

Let `S` be smooth of relative dimension 1 over a field `k`, and `F → S` proper and smooth with a section `e`, every field
fibre an abelian variety with origin `e(s)`. Then `S`, `F`, `F×_S F` and `(F×_S F)×_S F` are smooth over `k`, hence
reduced.
1. Fix `s ∈ S`, an affine open `V = Spec A ∋ s` and the prime `𝔭` of `s`. `A_𝔭` is a field or a DVR
   (`field_or_dvr_localization`):
   * At a non-closed point the stalk has dimension 0 (coheight argument with a closed specialization, which exists
     because `S` is Jacobson); it is reduced, so it is a field.
   * At a closed point, dimension = embedding dimension = 1 (`ZInQ.Contrib.Dim`). The maximal ideal is principal, and
     the ring is a domain (`isDomain_of_maximalIdeal_eq_span`), hence a DVR.
2. Over `Spec A_𝔭` the group law exists: outright if `A_𝔭` is a field, by the leaf if it is a DVR.
3. It descends to some `Spec A[1/f]` (EGA IV₃ 8.8.2 (i) in Mathlib, through spread-out's `Stage` machinery). After one
   more shrinking its identity is `e` (`localLaw_of_stalk`).
4. On a field point of an overlap, both local multiplications are the multiplication of the fibre abelian variety:
   the fibre identification is a homomorphism by field-level rigidity (`isGrpFibre_of_rigidity`). The overlaps are
   reduced, so the local laws agree and glue (`glue_of_rel`).
5. The group axioms of the glued maps hold on all field points (the fibres' axioms). The sources are reduced, so the
   axioms hold (`exists_grpObj_of_localLaws`).

## 4. Why the field itself is out of reach (SPECULATIVE judgement; references UNVERIFIED)

* **Over a non-reduced base**, local group laws need not agree on overlaps unless there is rigidity over the base (Mumford's
  rigidity lemma, *GIT* Prop. 6.1, or `𝒪_S ≅ p_*𝒪_F`, EGA III 7.8.6). gt-rigidity's `RigidityLemma` and
  `PushforwardStructureSheaf` are leaves, not theorems. More basically, the local existence over an Artinian base is
  Grothendieck's deformation argument (*GIT* §6.3 and the proof of 6.14): obstructions in `H²(A, T_A)` and extension over
  square-zero thickenings, then Grothendieck's existence theorem (EGA III₁ 5.4.1) for the complete local ring, fpqc
  descent to the local ring, and spreading out. Mathlib 4.35 has no formal schemes, no coherent cohomology of
  projective schemes and no deformation theory. Neither do the fork, Stacks ports, FLT or openai/math, as far as I
  found.
* **Over a DVR** (the chain's case), every proof I know uses one of the following, and none is in the tree:
  * Néron models (existence for abelian varieties over any DVR, BLR §1.4 Thm 3, UNVERIFIED number), plus Zariski's main
    theorem and field rigidity. The fork has Néron model existence only over rings of integers of number fields
    (`neronSchemeExtensionExists`), not over the local rings of a curve.
  * Matsusaka–Mumford: birational maps between smooth proper models with non-ruled special fibres extend. Applied to
    the shear map `(x, y) ↦ (x, xy)` it would give the group law. Not stated anywhere in the tree.
  * The deformation route above.
* **Other bundle fields** (sga3_VIB_3_10, groupSchemeEquidim, geomConnOfRationalPoint, egaIV_8_10_5_xii,
  neronSchemeExtensionExists, picRepresentableAbVar, …) do not imply group laws on families over a curve. So no −1 by
  reuse of existing leaves (VERIFIED by reading their statements in OPEN.md).

## 5. The narrowing fold (manual; compiled in an overlay, VERIFIED)

Leaf count unchanged; the new leaf is strictly weaker. In place, like rigid-prune's fold (the exact edits are
scratch/group-law/fold/narrowing.patch, 13 modules):
1. In every bundle generation with the field (OpenResearchLeaves14 to OpenResearchLeaves26, structures in TailZ23,
   TailZ25 to TailZ29, TailZ33 to TailZ38 and TailZ41), change the field type
   `_root_.ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` to `_root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR`. Keep the
   name, so every `mumfordGroupLaw := n.mumfordGroupLaw` stays as it is.
2. In TailZ23, add `import ZInQKernel.Contrib.OneProof.MumfordGroupLawRed`. Replace
   `qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw` with `qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw`: once in
   `x6Rows_of_open14` and twice in `researchLeaves9_of_open14`.
3. In TailZ34 (`sixContactMin_of_open28`), replace
   `DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU` with
   `DCY3Used.y3Connected_of_ab_gl (LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw)
   (DCY3Used.y3ConnectedAb_of_U r.shimuraMainThmIDeligneY3AbU)`.
4. kinds.tsv row: kind published; source "MFK *GIT* Thm 6.14 with `S = Spec R`, `R` a DVR" (numbers UNVERIFIED); flag
   "unread: new printed leaf …, locator UNVERIFIED". The row in scratch/group-law/autofold.json is in autofold's format,
   but marked manual: autofold cannot run it, because there is no proof of `MumfordGroupLaw`.

**Check (VERIFIED, 11-16 ~15:40).** No file under `ZInQKernel/` was edited.
* The 13 patched sources are in /tmp/glfold/src.
* The 31 modules downstream of TailZ23 in `Main`'s import closure (fold/downstream-modules.txt) were recompiled in
  topological order with `lean -R <root> -o` into an olean overlay: a symlink tree of the worktree's build with those
  31 modules replaced, first on `LEAN_PATH` (fold/compile_overlay.sh). No errors.
* `ZInQKernel.OneProof.Main` compiled: `frozenTarget` depends on `[propext, Classical.choice, Quot.sound]`.
* fold/FoldCheck.lean (foldcheck.txt) shows:
  * `OpenResearchLeaves26.mumfordGroupLaw : … → ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR`;
  * in `frozenTarget`'s closure: `MumfordGroupLawDVR` and `qmFamilyGroupLaw_of_dvr`;
  * not in it: `MumfordGroupLaw` and `qmFamilyGroupLaw_of_groupLaw`.

The integrator should also update the fields' docstrings (unchanged in the patch) and the kinds.tsv and OPEN.md rows.

If an autofold-compatible swap is preferred: dict-models' `MumfordGroupLawConn` (origin/wip/dict-models ca225d00) is one,
since it adds only `ConnectedSpace S`.

## 6. The new leaves, rated

* **`MumfordGroupLawDVR`: printed form.** It is *GIT* Thm 6.14 (as recalled: `S` connected and locally noetherian, `F → S`
  smooth proper with a section, one geometric fibre an abelian variety ⇒ abelian scheme with identity `e`) at
  `S = Spec R`, `R` a DVR. The hypotheses are stronger than the print's (every field fibre an abelian variety with
  origin `e(s)`; geometrically connected fibres). The conclusion is the group-object part of "abelian scheme". So it is
  a consequence of the print, and of the field (`dvr_of_field`), never stronger. Over genuine definitions:
  * Mathlib's `IsDiscreteValuationRing`, `IsProper`, `Smooth`, `GeometricallyConnected` and `GrpObj`;
  * the kernel's `AbVar` and `IsAbVarFibre`.

  Reading risk: none known beyond the UNVERIFIED theorem number. The statement is also the classical good-reduction
  fact "a smooth proper model of an abelian variety over a DVR, with a section and abelian special fibre, is an
  abelian scheme". It is the minimal form the chain uses.
* **`MumfordGroupLawLocal`: printed form**, the same print at the spectrum of a reduced noetherian local ring. It is not
  needed by the chain. It gives `MumfordGroupLawRed`, the field over every reduced base.

## 7. What remains

* The field over non-reduced bases (not used by the chain) and the DVR leaf itself: open; inputs as in §4.
* The narrowing fold of §5 is compiled only in an overlay: no integration build, no hash comparison, no
  OPEN.md regeneration.
* The re-typing prune of §2 (−1 with no leaf) is possible in principle but conflicts with the fold contract.
