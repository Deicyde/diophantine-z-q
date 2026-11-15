# triage2 (final, 11-15 ~06:35 PST; base 9a100aa7): next tasks that remove fields
Report: docs/research/triage2.md (§1 first pass, §2 probes, per-statement details, final ranking). Probes:
scratch/triage2/*.lean (all compile at the base).

Final ranking (one agent each):
1. **babaGranathRationalAb (−1, T1).** It follows from the other top-bundle fields; proved end-to-end in scratch with
   standard axioms. `babaGranathRationalAb_of_open28T2 n t l` (scratch/triage2/ProbeD.lean) uses:
   - Elkies (`elkiesEquationsX6Ab_of_printed`);
   - CM pairs over ℂ (`IsShimuraHolFamily` of shimuraMainThmIDeligneY3AbU, proved `cmFixedHasCM_of`, `cm*_exists`, h69);
   - the truncated `descend_main` (no TorsionDescends, no R1R2fpRep).
   Left to do: a contribution file plus the fold (thread `l` into the open21→20 converter, or replace at open28).
   This also drops BG's UNVERIFIED §3.1 table reading.
2. **Semantic prune of deligneComponentsX6PrintedAb and geomConnOfAlgClosure (−2, T2).** They feed only `R1pi0Props`,
   the last conjunct of `R1R2fpRep`, and no live constant reads it (compiled binder-use probe Pi0Use.lean). The base
   witness comes from GonzalezRotgerX6 (ProbeC). Scope: 41 live types mention R1R2fpRep. geomConnOfAlgClosure is
   HELD (cloud batch 2): the lead should decide before both run.
3. **semistablePersistsSHcp (−1, T2).** Prove `ReductSplit.SemistablePersistsDVR` from SGA3_VIB_3_10, SGA7_IX_3_3
   (derived) and GeomConnOfRationalPoint, via the proved `identityComponentBaseChangeDVRRange_of` plus fibre
   transport. Template: `hasSemiAbelian_pullback`, TailZ14:1006. This is a plain field replacement; the fold check
   compiles (ProbeA).
4. deligneComponentsY3PrintedAb (−1, T3): only `Y3Connected` is used; prove it from shimuraMainThmIDeligneY3AbU plus
   a (𝒪/3)^× `decide` at ℚ(i).
5. gonzalezRotgerProp56X6 (−1, T3–T4, bypass): identify R ∈ {ℤ[i], ℤ[√−6]} in nocm_on_witness. Needs CommRing.Pic
   computations, which are not in the tree.
6. gaudronRemondThm14 one-direction narrowing (0 fields, T1–T2) via milneIsogenyQuasiInverse.

Keep (T4, no narrowing removes them): r9a, r9b, hodgeTateDecompAbVar, deRhamH1AbVarT, dsThm965, bostLowerBound,
javanpeykarBound, pazukiCor13Upper, gonzalezRotgerX6Ab, raynaudSemistableSH, sga7_IX_3_3_SH, sga7_IX_3_5_ForwardGeom,
hCM, h33. Reasons: the objects vary with u, J₁(N) has no potentially good reduction, and the target needs effective
exponents.

Changes since pass 1:
- BG went from T2–T3 to T1 and from #3 to #1: the ℂ-side CM and the descent were already in the tree (ProbeB, ProbeD).
- The persistence task's risk dropped because the transport template exists.
- The GR-count bypass's risk rose (Pic computations).
- No further clause prune exists in the X₆ row (ClauseUse.lean).
