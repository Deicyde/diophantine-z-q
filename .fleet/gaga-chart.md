# gaga-chart (fleet note)

**Result: `gagaMorphism` is proved from one printed leaf plus an existing field (VERIFIED, compiled, standard
axioms).**

```lean
theorem GAGAAn.gagaMorphism_of_gagaChart (hU : UniformizationLeafAll) (hG : GAGAChart) :
    ZInQ.HomLattice.GAGAMorphism
```

- **The new leaf.** `GAGAAn.GAGAChart` is GAGA for maps of complex abelian varieties. Its hypothesis is a map
  `A(ℂ) → B(ℂ)` that is holomorphic (`ContMDiff ω`) in charts satisfying `IsAnStr`, over unif-topology's
  `analyticTopology`. `IsAnStr` is the three clauses of `SmoothComplexManifoldAn`, and sga1-etale's étale atlas
  satisfies it. The conclusion is `F = (· ≫ f)` for a morphism `f`.
- **Rating: printed form, special case.** Sources: Serre GAGA (projective varieties); SGA 1 XII 4.4 for proper `X`;
  locators UNVERIFIED. The reading from the print to the leaf no longer needs the holomorphic inverse function
  theorem. Two facts are proved in Lean:
  - any two `IsAnStr` atlases have the same holomorphic maps (`contMDiff_id_of_isAnStr`, `gagaChart_of_some`);
  - such atlases exist (from the uniformization, or from sga1-etale).
- **The inverse function step is now glue.** It is proved twice, with Mathlib's analytic inverse function theorem
  at `ω`. First, `F = ψ ∘ G⁻¹ ∘ Θ` near each point. Second, `IsAnStr` charts `Q ↦ Θ Q` on `A(ℂ)` are built from any
  uniformization (`exists_rChart`, `exists_isAnStr_of_unif`). So no `SmoothComplexManifoldAn` or SGA 1 leaf is
  needed.
- **Compiles.** The module is `ZInQKernel/Contrib/OneProof/GAGAChart.lean` (33 KB). It imports TailQ and
  sga1-etale's module.
- **`#discharges`.** Output in `scratch/gaga-chart/discharges.txt`: `DISCHARGES [OpenTextbookLeaves11.gagaMorphism]
  by GAGAAn.gagaMorphism_of_gagaChart`, still assumes `[UniformizationLeafAll, GAGAAn.GAGAChart]`, standard axioms.
- **Autofold.** Spec in `scratch/gaga-chart/autofold.json`, leaf `gagaChart` with kind published and flag unread. The
  dry run exits 0 with "46/10 on 56 -> 46/10 on 56": neutral at this base, which still rates `gagaMorphism` LEAF.
  Under leaf-fold32's re-rating (consequence, GLUE) the fold is −1 GLUE. `FoldDryRun.lean` compiles.
- **`ShimuraThm54` (hcm-g1): not settled by this restatement.** That leaf is stated over Mathlib's Weierstrass
  points, which have no analytic structure in Lean, and `IsAnalyticIso` has no derivative clause to feed the
  inverse function theorem. A suggested correction (add a coordinates clause, as in `IsStrongUnif.coords`) is in the
  report, marked SPECULATIVE.

**What remains.**
- A statement check of `GAGAChart` against the print: the GAGA and SGA 1 XII section numbers are UNVERIFIED.
- A row in `locators.md`, proposed in the report.
- The fold. If sga1-etale's fold lands first, the proof term for `uniformizationLeafAll` goes in place of
  `{n}.uniformizationLeafAll` (spelled out in report §5).
- The `ShimuraThm54` restatement, as a separate task.

Report: `docs/research/gaga-chart.md`.
