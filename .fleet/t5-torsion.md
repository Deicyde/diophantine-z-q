# t5-torsion (2026-11-13)

**Verdict.** T5 (`PkgI2.TorsionStructure`, Mumford §4: `A(K̄)[n] ≅ (ℤ/n)^{2g}`) is reduced, and
every use of it in the H proof follows from T35 (`UniformizationExists`, already
`TextbookLeaves.t35`). Everything below compiles: `scratch/t5-torsion/T5Full.lean`, no `sorry`,
axioms `propext`, `Classical.choice`, `Quot.sound` only. Report: `docs/research/t5-torsion.md`.

**What compiles (main theorems).**
- `T5Torsion.torsionStructureC_of_uniformization : UniformizationExists → TorsionStructureC`.
  This is T5 for every field with a ring map to `ℂ`, from T35. The proof chains the uniformization
  `ℂ^g/Λ`, the descent of torsion along `K̄ → ℂ` (using the proved `mulIsogeny`), and a rank-`r`
  structure theorem from the torsion counts.
- `LeafQM.AV.Pin.mobiusGlue_of_T35 : UniformizationExists → MobiusGlue`. This closes
  `GluePiecesPin.mobius` without T5.
- T35 replacements for the other T5 consumers, all at `ℚ̄`, subfields of `ℚ̄`, or number fields:
  - `QML3.goodReductionC` and `goodReduction_of_QM_rational3_C'` (glue A6, G3);
  - `torsionBound3_of_T35` and `torsionCountPts_of_T35` (copies of the assembly Props);
  - `torsionStructure_numberField` (lt-local).
- `torsionStructure_of_degree : KernelDegree → MulUnramifiedPosChar → PkgI2.TorsionStructure`.
  Full T5 follows from Mumford's two facts about `[n]`: `deg [n] = n^{2g}` in fibre form
  (`A[n] ≅ Spec R`, `dim R = n^{2g}`), and separability in characteristic `p`. The glue is
  proved:
  - points of `A[n]`;
  - finite unramified algebras are étale;
  - `#Hom_K(R, K̄) = dim R`;
  - structure from the counts.

  `torsionStructureCharZero_of_degree` gives T5 in characteristic 0 from `KernelDegree` alone, since
  separability is proved via the kernel's `kerUnitOpen`. Also `torsionStructure_of_torsionCard`
  (from the count `#A(K̄)[n] = n^{2g}`) and `torsionStructure_of_uniformization_of_nonC`.
- `TateFree.tateModuleFree_of_torsionStructure : T5 → PkgI3.TateModuleFree`. So T26 is glue given
  T5. Also `tateModuleFreeC_of_uniformization`, which gives T26 for subfields of `ℂ` from T35.
- `tate_surj_numberField`: `T_ℓ A → A[ℓᵏ]` is onto, from T35. It replaces the only main-chain use
  of the `GluePieces4` leaf `divisiblePoints`, in `tatePairingZl_of_leaves`.

**Effect (proposals; integration not done).**
- `t26 := tateModuleFree_of_torsionStructure t.t5` removes T26 as a leaf.
- Alternatively, replace T5 and T26 by `KernelDegree` + `MulUnramifiedPosChar`, or by
  `TorsionCardNonC`.
- `divisiblePoints` can be dropped after one rewiring.
- Rewiring recipe: report §3.

**What remains.** (Final check: all eight files in scratch/t5-torsion compile with no error and no `sorry`.)
- Leaves left for full T5: `KernelDegree` (Mumford §6 App. 2) and `MulUnramifiedPosChar` (Mumford
  §4, Milne Thm 8.2; locators UNVERIFIED). H needs neither on subfields of `ℂ`, which T35 covers.
- Alternative bundle option: replace T5 and T26 by these two smaller leaves.
- The rewiring of the consumers in the assemblies and in ZInQKernel (report §3) is integration work.
