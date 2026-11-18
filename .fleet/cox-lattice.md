# cox-lattice (2026-11-17)

**Result: the textbook leaf `HDec.CMBranch.CoxProperLattice` is proved in Lean from Mathlib alone, statement
unchanged, standard axioms.** `HDec.CMBranch.CoxLattice.coxProperLattice_proof : CoxProperLattice` in
`ZInQKernel/Contrib/OneProof/CoxProperLattice.lean`; hence `ReducedCMPeriod` (manuscript L598-599) follows from the
chain's textbook fields t35, homLatticeCorr, t11b only (`reducedCMPeriod_of_leaves_cox`). Cox (not cited by the
manuscript) leaves the route. Proof: a non-integer of R maps to a multiplier α = p + qτ ∉ ℤ, giving a primitive form
(a, b, c') for τ; Cox 7.5's computation shows the multipliers are ℤ + ℤaτ; θ = φ⁻¹(aτ) generates R; cm-branch2's
`discr_order` gives b² − 4ac' = [𝓞_k:R]² d_k. No invariance of discriminants under ring isomorphisms is needed.

**Overlap**: cm-branch2 proved the same leaf independently while this ran (CMBranch/CoxProof.lean,
`HDec.CMBranch.coxProperLattice_proof`) and moved to CMInputs3/Open73; merged here, this proof kept in sub-namespace
`CoxLattice` (no duplicate names). Either proof can be used.

**Compiles** (lake build, EXIT 0): `CoxProperLattice.lean`; fold dry run `CoxProperLattice/Fold.lean`
(`HDec.HSyn.sixContactMin_of_open72_coxlattice r t l (c : CMInputs3)`, cm-branch2's CMInputs3); axioms propext, Classical.choice, Quot.sound. `#discharges`: 30 open, 120 discharge one (16
pre-existing + 104 `_r5` projection noise); none from this task (the leaf is not a top field on main).

**Fold** (`scratch/cox-lattice/autofold.json`): = cm-branch2's updated spec (Open73) with this proof as alternative
provider. Net vs cm-branch2 at task start: GLUE column 0; strict count (pending leaves as GLUE) −1 (+5 → +4);
vs cm-branch2's updated spec: 0.

**Manuscript check L598-600**: correct as written, no missing hypothesis (Δ = disc of End(E_{L̄}) ≅ multiplier ring of
every period lattice; bounds homothety invariant; the upper bound holds for any period, since a ≥ 1). ELLIOT
(uncited step); Lean proof steps on-the-spot (report §2). Known issues: none.

**Remains**: nothing for this leaf. The CM branch's open items are cm-branch2's (CMFibreSplit glue; 4 leaves pending
review). Report: docs/research/cox-lattice.md.
