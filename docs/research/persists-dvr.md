# persists-dvr: `semistablePersistsSHcp` discharged from SGA 7 IX 3.3 (second assertion)

Task persists-dvr, 2026-11-15. Base wip/r6-nf 0bc2446d. Plan from triage2 §1 Task 2. Contributor file
`ZInQKernel/Contrib/OneProof/PersistsDVR.lean`. Results log: scratch/persists-dvr/log.md. This is model work and no
person has reviewed it.

Marks: **VERIFIED** means compiled, or read in a named file on this host. **STANDARD** means textbook mathematics.
**SPECULATIVE** means judgement.

## 1. Result

The research field `OpenResearchLeaves21.semistablePersistsSHcp : ReductB.SemistablePersistsSHcp` (SGA 7 I Exp. IX
Prop. 3.3, first assertion, over a strictly henselian DVR in characteristic 0 with perfect residue field) is
**proved outright** from fields that stay in the bundles. No new leaf is needed. All of the following is VERIFIED
(scratch/persists-dvr/axioms.txt):

```lean
theorem GapPersists.semistablePersistsDVR_of_printed (h3 : CToPrinted.SGA3_VIB_3_10)
    (h7 : CToPrinted.SGA7_IX_3_3) (hG : AVGlue.GeomConnOfRationalPoint) : ReductSplit.SemistablePersistsDVR
-- 'GapPersists.semistablePersistsDVR_of_printed' depends on axioms: [propext, Classical.choice, Quot.sound]

theorem GapPersists.semistablePersistsSHcp_of_printed (h3 : CToPrinted.SGA3_VIB_3_10)
    (h7 : CToPrinted.SGA7_IX_3_3) (hG : AVGlue.GeomConnOfRationalPoint) : ReductB.SemistablePersistsSHcp
-- depends on axioms: [propext, Classical.choice, Quot.sound]

theorem GapPersists.semistablePersistsSHcp_of_SH (h3 : CToPrinted.SGA3_VIB_3_10)
    (h7 : SGA7PersistsNF.SGA7_IX_3_3_SH) (hN : GapSHPair.NeronBaseChangeStrictHenselization)
    (hG : AVGlue.GeomConnOfRationalPoint) : ReductB.SemistablePersistsSHcp
-- depends on axioms: [propext, Classical.choice, Quot.sound]

theorem GapPersists.ss1_ss3_of_printedNF (h3 : CToPrinted.SGA3_VIB_3_10) (h7 : CToPrinted.SGA7_IX_3_3)
    (hG : AVGlue.GeomConnOfRationalPoint) (h36 : ReductSplit.SemistableReductionDVR)
    (hN : GapNeron.NeronSchemeModelExistsDVRNF) (hLG : ReductSplit.SemistableLocalGlobal)
    (hAA : ReductSplit.SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists
-- depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file also contains these helpers, each with standard axioms:
- `isAlgebraic_resMap`: for `K'/K` finite and `O' ∩ K = O`, the residue extension is algebraic.
- `isMonHom_of_comp_mono`.
- `hasSemiAbelian_transfer`.

The hypotheses of `semistablePersistsSHcp_of_SH` are all bundle fields at the base:
- `sga3_VIB_3_10`, `sga7_IX_3_3_SH` and `neronBaseChangeStrictHenselization` are in `OpenResearchLeaves21` (TailZ34).
- `geomConnOfRationalPoint` is in `OpenTextbookLeaves11` (TailZ32).

`SGA7_IX_3_3` is obtained from them by the chain's `SGA7PersistsNF.sga7_IX_3_3_of_SH`.

### `#discharges` (scratch/persists-dvr/discharges.txt; VERIFIED)

```
DISCHARGES [OpenResearchLeaves21.semistablePersistsSHcp] by GapPersists.semistablePersistsSHcp_of_SH
  still assumes: [CToPrinted.SGA3_VIB_3_10,
 SGA7PersistsNF.SGA7_IX_3_3_SH,
 GapSHPair.NeronBaseChangeStrictHenselization,
 AVGlue.GeomConnOfRationalPoint]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves21.semistablePersistsSHcp] by GapPersists.semistablePersistsSHcp_of_printed
  still assumes: [CToPrinted.SGA3_VIB_3_10, CToPrinted.SGA7_IX_3_3, AVGlue.GeomConnOfRationalPoint]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 62 open hypotheses, 1651 theorems checked, 7 discharge one
```

The other five DISCHARGES lines in the file come from contributions that were already in the tree.

## 2. Fold: autofold spec (field discharged outright)

The spec is `scratch/persists-dvr/autofold.json`:

```json
{"name": "persists-dvr",
 "imports": ["ZInQKernel.Contrib.OneProof.PersistsDVR"],
 "discharges": [
   {"field": "semistablePersistsSHcp",
    "proof": "_root_.GapPersists.semistablePersistsSHcp_of_SH {n}.sga3_VIB_3_10 {n}.sga7_IX_3_3_SH {n}.neronBaseChangeStrictHenselization {t}.geomConnOfRationalPoint"}]}
```

Checks (VERIFIED):
- `python3 scripts/one_proof/autofold.py scratch/persists-dvr/autofold.json --dry-run` exits 0. Its counts line:
  `strict count: 45/10 on 55 -> 44/10 on 54; strictest 44/11 -> 43/11`.
- The full dry-run output is in scratch/persists-dvr/autofold-dryrun.txt. That module, with line 1 stripped, is
  scratch/persists-dvr/FoldCheck.lean. It compiles over the built base, and `HDec.HSyn.sixContactMin_of_open29`
  depends on `[propext, Classical.choice, Quot.sound]`.
- The new generation is `OpenResearchLeaves22`, which is `OpenResearchLeaves21` without `semistablePersistsSHcp`.
  The field is refilled in `openResearchLeaves21_of_OpenResearchLeaves22` by the proof above.

**Coordination (sga7-cp).** The autofold route edits no existing consumer: TailZ26 `ss1_ss3_of14NF` keeps reading
the field of `OpenResearchLeaves14`, which is now filled by the proof. I did not touch `raynaudSemistableSH`
or `sga7_IX_3_5_ForwardGeom`. The autofold's new bundle copies them unchanged.

**Optional manual alternative.** Instead of autofold, the lead can reroute the one reader at the base:
- Site: `HDec.HSyn.ss1_ss3_of14NF`, ZInQKernel/OneProof/H/TailZ26.lean L200-205.
- Replace its body `_root_.GapNeron.ss1_ss3_of_cpNF r.semistablePersistsSHcp r.strictHenselizationPair (semistableReductionDVR_of14 r t) N L A` with
  `_root_.GapPersists.ss1_ss3_of_printedNF r.sga3_VIB_3_10 r.sga7_IX_3_3 t.geomConnOfRationalPoint (semistableReductionDVR_of14 r t) N L A`,
  keeping the same `N`, `L` and `A` arguments.
- TailZ26 must then also import `ZInQKernel.Contrib.OneProof.PersistsDVR`. That works because the module imports
  only NeronDVR and SGA7PersistsNF, both of which are below TailZ26.
- Then prune the field from bundles 14-21.

This alternative edits the SS1/SS3 site that sga7-cp is also working on, so the autofold route is preferable.

## 3. Method

The plan departs from triage2's in one point: the semi-abelian structure never has to be transported along a field
extension κ̄ → κ̄'. Notation: K'/K finite, O' ∩ K = O. 𝒩 is a semistable Néron model of A at O (from
`HasSemistableReduction`), and 𝒩' is any Néron model of A_{K'} at O'.

1. **Residue extension algebraic** (`isAlgebraic_resMap`, STANDARD, compiled). Take x ∈ O'. The element x is
   algebraic over K with some polynomial p ≠ 0. Divide p by a coefficient c of maximal valuation, so that all
   coefficients lie in O and the i-th is 1. Reducing mod the maximal ideals gives a nonzero polynomial over κ(O)
   that kills x̄.

   With this, `ReductGlue.isSemistable_bcDVR_iff` (TailZ14 L1299) turns semistability of 𝒩 into semistability of
   `bcDVR hO 𝒩 = 𝒩 ×_O O'`, read on the geometric special fibre over κ̄(O').

2. **Identity component and SGA 7 IX 3.3 (ii).**
   - W = 𝒩⁰ is an open subgroup scheme. The construction is `CToPrinted.OpenSub` with `idCompSubgroup_of h3 hG`
     (TailZ19), and its range is `idCompSet 𝒩.G`.
   - `identityComponentBaseChangeDVRRange_of h3 h7 hG` (TailZ19 L1595) gives an open-immersion homomorphism
     j : W ×_O O' → 𝒩'.
   - `idCompBaseChangeDVR_of` together with `Scheme.Pullback.range_map` shows that W ×_O O' → 𝒩 ×_O O' has image
     `idCompSet (𝒩 ×_O O')`.

3. **Transfer** (`hasSemiAbelian_transfer`, general over any base S and any field point p : Spec k → S).
   - Setting: V ⊆ G is open with image G⁰, V → H is an open-immersion homomorphism, and U ⊆ G_k is a connected
     open subgroup.
   - U lies in one fibre (Spec k is a point) and contains e. So its image in G is a preconnected subset of
     G_s ∋ e(s), and that image lies in `idCompSet G` (`IsPreconnected.subset_connectedComponentIn`, `unit_bc_fst`).
   - Hence U factors through V_k (`IsOpenImmersion.lift`). The lift is a homomorphism because V_k → G_k is a mono
     homomorphism, and an open immersion by `IsOpenImmersion.of_comp`.
   - U → V_k → H_k is therefore an open-immersion homomorphism. The same U, B, π, r and e witness
     `HasSemiAbelianIdentityComponent (H_k)`.

   Apply this with S = Spec O', p = Spec κ̄(O'), G = 𝒩 ×_O O', H = 𝒩' and V = W ×_O O'. The fibre objects are
   definitionally `geomSpecialFibre (bcDVR hO 𝒩)` and `geomSpecialFibre 𝒩'`, so no pullback-pasting is needed.

4. `SemistablePersistsSHcp` is the specialization of `SemistablePersistsDVR` to CharZero, perfect residue field and
   strictly henselian O. The proof follows the pattern of `ReductB.cp_of_general`.

`GeomConnOfRationalPoint` enters only through the chain's proved lemmas `idCompSubgroup_of`,
`idCompBaseChangeDVR_of` and `identityComponentBaseChangeDVRRange_of`.

**Mathematical status.** The argument is complete in Lean, so triage2's SPECULATIVE "second assertion implies
first" is now VERIFIED, relative to the Lean forms of the leaves `SGA7_IX_3_3` and `SGA3_VIB_3_10`. The reading
risks of those leaves are unchanged, and the readings recorded for them stay as they are.

## 4. Files

- `ZInQKernel/Contrib/OneProof/PersistsDVR.lean`: the contributor file. It builds with
  `lake build ZInQKernel.Contrib.OneProof.PersistsDVR`; the only warning is a deprecated `if_pos`.
- In scratch/persists-dvr/:
  - `Core.lean`: the development copy.
  - `Discharges.lean` and `discharges.txt`.
  - `Axioms.lean` and `axioms.txt`.
  - `autofold.json` and `autofold-dryrun.txt`.
  - `FoldCheck.lean`.
  - `log.md`.
