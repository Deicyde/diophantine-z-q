# rigid-prune: `mumfordRigidityCore` cannot be pruned without changing field statements; the chain now uses only *GIT* Thm 6.14 on QM families (no Cor. 6.4, no `mumfordRigidity_of_core`)

Task rigid-prune, 2026-11-15. Base bb9b2e4d (wip/leaf-fold19: `frozenTarget` through
`HDec.HSyn.sixContactMin_of_open26`, 58 bundle fields). `origin/wip/gt-rigidity` merged (762ea48b; adds only
`ZInQKernel/Contrib/OneProof/MumfordRigidity.lean`, its report and scratch). Results log: scratch/rigid-prune/log.md.
Model work, no human review.

Marks: **VERIFIED** = compiled or read in a named file on this host; **STANDARD** = textbook mathematics;
**SPECULATIVE** = judgement; **UNVERIFIED** = a theorem number recalled without a source.

## 1. Main result

**The field `OpenResearchLeaves19.mumfordRigidityCore` cannot be removed by rewiring consumers onto the
abelian-scheme forms.** Two consumers need the universal clause `R1univProps` of a witness on families that are only
given as `QMFamily` (no group law). Supplying it from the abelian-scheme leaves takes rigidity. Without changing a
field statement, which this task may not do, no proof can avoid that. So **nothing was pruned**. VERIFIED:
PruneScan finds 0 unused fields of 58.

1. **Site N1: the field `OpenGlue7.quotientP1Coordinate`.** Its type, `MCRGlue.QuotientP1Coordinate` (TailW L202),
   has `R1fpProps Y Φ` among its hypotheses (its conclusion does not mention `Y`). The consumer is
   `MCRGlue.modelCoordinateResidue_of_quotient'` (TailX L275, on to `heckeVertWitness_of_curveBijIso`). To use the
   field at all, the chain must produce a witness with `R1fpProps`, i.e. with `R1univProps` on every `QMFamily` over
   a proper smooth curve over ℚ. VERIFIED: the unfolded statement is checked by `rfl` in scratch/rigid-prune/Sites.lean
   §3.
2. **Site N2: `HDec.ModelGlue.exists_genFib_to_Y`** (TailL L1645). Its users are `modelIntegral_of` and
   `modelFunctionField_of_curveBijIso`, then `heckeVertWitness_of_curveBijIso` (TailL L2425) and
   `heckeVertWitness_of_leaves5` (TailN L38). It applies `R1univProps` of the `r1r2` witness to `famBC 𝒜 j`, the
   generic fibre of the Shimura model's family. The field `shimuraGoodReductionNoGuard` gives `𝒜` as a `QMFamily`
   only. The precise fact needed there is `HDec.ModelGlue.ShimuraModelGenericAb`: for every Shimura model `(𝒴, 𝒜)`,
   `famBC 𝒜 j` underlies a `QMAbScheme`. VERIFIED, Sites.lean §2:
   * `exists_genFib_to_Y_ab` proves the site from `R1univAbProps` together with `ShimuraModelGenericAb`;
   * `shimuraModelGenericAb_of_gl` proves `ShimuraModelGenericAb` from `QMFamilyGroupLaw`.

Both needs are instances of one Prop, now in the chain:

```lean
def LeafQM.AV.R1UnivRigid.QMFamilyGroupLaw : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ 𝒜 : QMFamily S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K, IsFibreOf 𝒜 s.left P) →
      ∃ 𝒜' : QMAbScheme S.left, 𝒜'.toQMFamily = 𝒜
```

It says that a QM family over a proper smooth ℚ-curve whose field fibres are all objects is an abelian scheme with
`𝒪`-action and level 3. **What was done instead of the prune** (VERIFIED, compiled; standard axioms):

* **Clause (a) is not needed** (*GIT* Cor. 6.4 over the base, UNVERIFIED number).
  `qmFamilyGroupLaw_of_groupLaw : MumfordGroupLaw → QMFamilyGroupLaw` (new module `OneProof/H/TailZ40.lean`) uses
  only gt-rigidity's `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` (*GIT* Thm 6.14: the group law with identity
  `e`). r1univ-rigid's construction used clause (a) once, for "`ι(a)` is a homomorphism". `isMonHom_of_fibres`
  proves this instead on field points of the reduced `F ×_S F`:
  * every field point factors through `A ×_K A` for the fibre `A`;
  * the fibre map is a homomorphism by clause (b), which is r1univ-rigid's proved `isGrpFibre_of_rigidity`;
  * `ι_A(a)` is an endomorphism of abelian varieties.
* **The conversions on the chain go through `QMFamilyGroupLaw`.** Each `L ↔ LAb` used on the chain is re-proved as
  `L_iff_ab_gl` (TailZ40) from `r1fpProps_iff_ab_gl : QMFamilyGroupLaw → (R1fpProps ↔ R1fpPropsAb)`. TailZ23's
  `x6Rows_of_open14`, `addedLeaves9_of_open14` and `researchLeaves9_of_open14` now use them with
  `qmFamilyGroupLaw_of_core r.mumfordRigidityCore`; `mumfordRigidity_of14` is deleted. VERIFIED by
  scratch/rigid-prune/ClosureCheck.lean:
  * not in `frozenTarget`'s closure: `mumfordRigidity_of_core`, `MumfordRigidity`, `exists_qmAbScheme`,
    `r1univProps_of_ab`, `r1fpProps_eq_ab'`;
  * in it: `MumfordRigidityCore` (only through gt-rigidity's `mumfordGroupLaw_of_core`, which drops clause (a)),
    `MumfordGroupLaw`, `QMFamilyGroupLaw`.
* **The other uses of the universal clause need no rigidity.** This is the step (1) analysis of the task.
  * `phi_part` and its users compare two witnesses: the universal clause of one witness is applied to the family
    from the family clause of the other. In abelian-scheme form that family is a `QMAbScheme`. The users are
    `compare_iso`, `exists_surjective_of_R1fp`, `kummerFibreEquiv_transport` and `sameTripleMor_of_mobius`.
    VERIFIED: `RigidPrune.phi_part_ab` compiles (Sites.lean §1).
  * `QMSplit.Moduli.classify` and `heckeOfFine_proof` (TailU) apply the universal clause to the twists
    `twistFam 𝒜 α` and `rightMulFam 𝒜 u` of the universal family. These have the same `F` and the same group law,
    with `ι ∘ α`, `η ∘ α` and `η(· u)`, so they are again `QMAbScheme`s. STANDARD; not compiled. They are also
    instances of `QMFamilyGroupLaw`.

| | fields | strict (kinds.tsv rows, 58 H + 7 others) | OPEN.md strictest (H) |
|---|---|---|---|
| before (bb9b2e4d) | 58 | 48 LEAF / 17 GLUE | 44 / 14 |
| after | **58** | **48 / 17** | **44 / 14** |

No field was removed, so kinds.tsv, claims.tsv and the generated docs/one-proof files are unchanged. VERIFIED:
`render_open.py --check` reports "4 generated files up to date" after regenerating.

### 1.1 What would remove the field (owner's decision; each changes a field statement)

1. **Weaken the field to gt-rigidity's `MumfordGroupLaw`**: *GIT* Thm 6.14 alone. The edit is one line in the
   conversions: `qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw` in place of `qmFamilyGroupLaw_of_core
   r.mumfordRigidityCore`. `frozenTarget`'s hypothesis gets strictly weaker, and Cor. 6.4 leaves the trust base.
   gt-rigidity's `mumfordGroupLaw_of_core` shows the new field is implied by the old (VERIFIED, compiled there). The
   kind stays LEAF (a printed theorem, applied on each connected component). Recommended.
2. **Weaken it further to `QMFamilyGroupLaw`**. This is a consequence of Thm 6.14, not a printed statement, so GLUE
   (c) in the strict reading.
3. **Remove rigidity altogether.** This needs three changes:
   * restate `quotientP1Coordinate` (project glue) on `R1fpPropsAb`;
   * restate `shimuraGoodReductionNoGuard` with an abelian-scheme family. That is the published form: the integral
     model carries the universal abelian scheme. SPECULATIVE reading of Shimura, Morita and Carayol, numbers
     UNVERIFIED;
   * re-version the 245 chain constants typed with `R1fpProps`-based Props onto `R1fpPropsAb`
     (scratch/rigid-prune/scan_typed.txt: TailC 42, TailZ20 30, TailG 21, TailL 18, TailZ21 16, TailA 15, …).

   The analysis above says the copies would compile with `phi_part_ab` and twisted `QMAbScheme`s, but they were not
   written (§5).

## 2. Every hypothesis

Unchanged from the base: docs/one-proof/OPEN.md (58 H fields: `OpenResearchLeaves19` 30, `OpenTextbookLeaves11` 13,
`OpenAddedLeaves16` 14, `OpenGlue7` 1; plus the 7 TYZ/GZ hypotheses). The row of the field this task concerns is
unchanged:

| field | kind | strict | strictest |
|---|---|---|---|
| `mumfordRigidityCore` | published | LEAF | LEAF |

Its use on the chain is now through `MumfordGroupLaw` only (§1). The kinds.tsv source text ("Thm 6.14 and Cor. 6.4")
still describes the field's statement correctly, so it was not edited.

## 3. The remaining leaves by the theory they come from

Unchanged. Group "abelian schemes / moduli": `mumfordRigidityCore` stays. The chain's need from it is *GIT*
Thm 6.14, applied to QM families over proper smooth curves over ℚ (`QMFamilyGroupLaw`), at two sites (§1, N1 and
N2), both in the vertical-witness part of the proof (H-83, the Shimura model over `ℤ_(p)`).

## 4. Checks (all VERIFIED; one Lean process at a time)

* Base: `lake build +ZInQKernel.OneProof.Main` OK. DumpCompact: 13675 constants
  (scratch/rigid-prune/hashes_before.txt), `frozenTarget` standard axioms.
* RigidScan (scratch/rigid-prune/RigidScan.lean) over the closure of `frozenTarget` (243455 constants) found:
  * 85 definitions built on `R1fpProps` (scan_defs.txt);
  * 245 non-generated constants typed with them (scan_typed.txt);
  * 38 constants whose value mentions `R1univProps` (scan_univ_users.txt). Each was read with decl_src.py. Genuine
    applications: `phi_part` and its users, `classify` (twists), and `exists_genFib_to_Y`. The rest destructure
    `R1fpProps` and drop the clause.
* After: `lake build +ZInQKernel.OneProof.Main` OK (TailZ40 builds with the merged gt-rigidity module).
  `#print axioms ZInQ.OneProof.frozenTarget`: `[propext, Classical.choice, Quot.sound]`.
* PruneScan (sem-prune's version, outputs in scratch/rigid-prune/): 30 + 13 + 14 + 1 = 58 fields, 0 unused, prune
  set empty.
* DumpCompact + cmp_hashes.py (scratch/rigid-prune/cmp_hashes_out.txt): base 13675, after 13694.
  * Removed 1: `HDec.HSyn.mumfordRigidity_of14`, a dead reader of the field.
  * New 20, all in TailZ40: `QMFamilyGroupLaw`, `isMonHom_of_fibres`, `exists_qmAbScheme_gl`,
    `qmFamilyGroupLaw_of_groupLaw`, `qmFamilyGroupLaw_of_core`, `r1univProps_of_ab_gl`,
    `r1famAbProps_of_r1famProps_gl`, `r1fpProps_iff_ab_gl` (with two `match_` auxiliaries), `r1fpProps_eq_ab_gl`,
    and nine `*_iff_ab_gl`.
  * Changed 3, all in the value only: the conversions `HDec.HSyn.x6Rows_of_open14`, `addedLeaves9_of_open14` and
    `researchLeaves9_of_open14` (TailZ23).
  * `frozenTarget`, every bundle structure and every `sixContactMin_of_open*` keep their hashes.
* scratch/rigid-prune/Sites.lean compiles, standard axioms (sites_out.txt).
* scratch/contrib-kit/DischargesTest.lean (output saved to DischargesTest-output.txt):
  * the five earlier discharges and both controls are unchanged (`t1` on `quotientP1Coordinate`; `t3` flagged for
    `sorry`);
  * two more appear, gt-rigidity's `mumfordRigidityCore_of_printed` and `mumfordRigidityCore_of_pushforward`, because
    its Contrib module is now imported by the chain. The count line reads "65 open hypotheses, 1230 theorems
    checked, 7 discharge one".
* `lake env lean scripts/one_proof/OpenStatements.lean`: 65 open hypotheses. `render_open.py`: 58 H, strictest 44/14.
  `--check`: ok. No generated file changed.
* FaithCheck: not needed (no HDec copy deleted).

## 5. Not done, and why

* **The prune**: blocked by N1 and N2 (§1), which need field-statement changes outside this task's rules.
* **Abelian-scheme copies of the 245 consumers** (task step (2)). Writing them would not change `frozenTarget`'s
  hypotheses while N1 and N2 stand, and the chain would still need `QMFamilyGroupLaw` at the `r1r2` witness. What the
  copies would have shown, that every other use is rigidity-free, is established by the analysis in §1 and by
  `phi_part_ab`; `classify`'s twists are argued, not compiled. If the owner chooses §1.1 (3), the copies become the
  work of that fold.
* The off-chain conversions of TailZ17 and TailZ22 (`researchLeaves10_of_open11`, `x6Rows_of_open13`, …) still use
  `mumfordRigidity_of_core`. They are not on the chain and were left unchanged.

## 6. `frozenTarget`: removed and added hypotheses

* Removed: none.
* Added: none. `frozenTarget`'s statement and hash are unchanged. Inside the proof, the field `mumfordRigidityCore`
  is now used only through `ZInQ.Contrib.MumfordRigidity.mumfordGroupLaw_of_core`, i.e. as *GIT* Thm 6.14.

## 7. State of the branches

| branch | merged | used |
|---|---|---|
| origin/wip/gt-rigidity 762ea48b | yes (only new files) | `MumfordGroupLaw`, `mumfordGroupLaw_of_core` |
| origin/wip/prune-scan (via sem-prune's copy) | no; PruneScan.lean copied to scratch/rigid-prune/ | yes |
