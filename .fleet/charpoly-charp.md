# charpoly-charp (2026-11-16, base wip/degpoly-proof 0a9e6698 + origin/main c1e4ed1b8)

**Verdict.** The field `charPolyIndepOfEllAlgClosed` (Mumford §19 Thm 4, T7) is **removed with no new leaf (−1;
strict 16/21 → 15/21)**. Its characteristic-p use (`common_trace` at FrobTraceLink's reduction Ā, α' = F̄∘Fr) does
not need T7: G8's intertwiners, already hypotheses of `common_trace`, make V_ℓ(α')⊗ℚ̄_ℓ conjugate to M⊕M (M 2×2),
so its minimal polynomial has degree ≤ 2; Mumford §19 Thm 3 (homFree: ℤ_ℓ⊗End → End(T_ℓ) injective) makes it the
minimal polynomial m ∈ ℚ[X] of α' in End⁰ for every ℓ, so tr V_ℓ(α') = −(4/deg m)·nextCoeff(m), ℓ-independent.
The other consumer (R16, over ℚ) uses only characteristic 0 (degpoly-proof's CharPolyIndepOfEllC).

**Compiles** (standard axioms): `ZInQKernel/Contrib/OneProof/CommonTraceHomFree.lean` (`common_trace_of_homFree`,
`g14TraceCompat_of_link_homFree`, `G0AssembleMod.linkedTateData_of_local_homFree`, `exists_minpoly_endE`,
`trace_eq_of_minpoly`) and `R16PrintedC.lean` (`R16Split.r16_of_printedC`; imports degpoly-proof's CharPolyLattice).
Manual fold `scratch/charpoly-charp/fold_edit.py` (= `fold.patch`, 14 H files): in a reflink copy of the tree
`lake build ZInQKernel.OneProof.Main` succeeds; `FoldCheck.lean` there: field absent, closure of frozenTarget
(268,676 constants) contains neither `CharPolyIndepOfEll` nor `CharPolyIndepOfEllAlgClosed`, axioms standard.
`#discharges` recorded (no direct discharge, as expected for a reroute).

**Remains (integrator).** Apply fold_edit.py on main (bring CharPolyLattice.lean along), full build, hash guard,
render_open, drop the field's kinds/claims rows. Report: docs/research/charpoly-charp.md.
Final: see docs/research/charpoly-charp.md.
