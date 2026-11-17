# pb-bypass (fleet summary)

**Verdict.** The research field `r11r12 : HDec.PkgI4.PanBerger` (composite GLUE, "not splittable: no B_st in
Mathlib") is now a theorem from two published-form leaves. `ZInQKernel/Contrib/OneProof/PanBerger.lean` defines
Fontaine's `A_cris` (p-adic completion of the divided power envelope `A_inf[x^n/n! : θx = 0]`), `B_cris^+`,
`log [ε]` (a genuine p-adic limit), `B_cris = B_cris^+[1/t]` (localization at all `log [ε]`, choice-free),
`B_st = B_cris[u]` with the `G_{ℚ_p}`-action (functoriality from pkg-I4's `oAct`; `σ(u) = u + log [σ(p♭)/p♭]`),
and `LocalIsPst` (Fontaine's potentially semistable, in the `LocalIsDeRham` convention). Then
`panBerger_of_printed : PanPrinted → BergerPrinted → PanBerger` with `PanPrinted = PanFor LocalIsPst` (Pan, JAMS 35
(2022) Thm 1.0.4, p ≥ 5) and `BergerPrinted = BergerDR LocalIsPst` (Berger, Invent. Math. 148 (2002) Thm 0.7).

**Consumers.** One: `G0Galois.g12` applies the field once, at p = 5, to r₅ of the QM surface (TailA l. 2220).
Weakest form `PanBerger5` (p = 5) recorded and checked (`scratch/pb-bypass/Weakest.lean`). No other field can
supply modularity of r₅ (non-CM), so the field could not be removed; it is split instead.

**What compiles (VERIFIED).** The contribution file (no warnings; standard axioms); `#discharges`:
`DISCHARGES [OpenResearchLeaves21.r11r12] by HDec.PkgI4.PanBergerSplit.panBerger_of_printed`, still assuming
exactly the two leaves; the autofold dry run (`scratch/pb-bypass/autofold.json`) compiles, counts strict
46/10 → 48/9, strictest 45/11 → 47/10. Sanity: trivial representation semistable over every K (unconditional).

**What remains.** A statement check of the two leaves and of the new definitions (B_cris ≠ 0, B_st^{G_K} = K_0
and the group-action property are not proved, as for pkg-I4's IsDeRham); JAMS / Springer locators UNVERIFIED;
the fold itself. Report: docs/research/pb-bypass.md; log: scratch/pb-bypass/log.md.
