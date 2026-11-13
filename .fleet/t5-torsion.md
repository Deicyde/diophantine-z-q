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
- `torsionStructure_of_torsionCard : TorsionCard → PkgI2.TorsionStructure`. Full T5 follows from
  the count `#A(K̄)[n] = n^{2g}`. Also
  `torsionStructure_of_uniformization_of_nonC : T35 → TorsionCardNonC → T5`, where only fields with
  no map to `ℂ` still need the count.
- `TateFree.tateModuleFree_of_torsionStructure : T5 → PkgI3.TateModuleFree`. So T26 is glue given
  T5. Also `tateModuleFreeC_of_uniformization`, which gives T26 for subfields of `ℂ` from T35.
- `tate_surj_numberField`: `T_ℓ A → A[ℓᵏ]` is onto, from T35. It replaces the only main-chain use
  of the `GluePieces4` leaf `divisiblePoints`, in `tatePairingZl_of_leaves`.

**Effect (proposals; integration not done).**
- `t26 := tateModuleFree_of_torsionStructure t.t5` removes T26 as a leaf.
- Alternatively, replace both T5 and T26 by `TorsionCardNonC`, which H never uses in substance.
- `divisiblePoints` can be dropped after one rewiring.
- Rewiring recipe: report §3.

**What remains.**
- `TorsionCardNonC`: positive characteristic and huge fields of characteristic 0 (Mumford §4/§6
  App. 2, locators UNVERIFIED). An algebraic proof needs `deg [n] = n^{2g}`, étaleness of `ker [n]`,
  and a count for finite étale schemes.
- The rewiring of the consumers in the assemblies and in ZInQKernel (report §3) is integration work.
