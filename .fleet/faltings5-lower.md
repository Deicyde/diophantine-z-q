# faltings5-lower (2026-11-15) — done

**Proved, no hypotheses** (no sorry; axioms `[propext, Classical.choice, Quot.sound]`;
`lake build ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower` green):

```lean
theorem GapHeight.faltingsLemma5Lower : ZInQ.HeightSplit.FaltingsLemma5Lower
```
`h(𝒩_B) ≤ h(𝒩_A) + ½ log deg φ`, from the kernel's definition of `GroupModel.height` (semistability unused).
Contributor file `ZInQKernel/Contrib/OneProof/FaltingsLemma5Lower.lean`, helpers in
`ZInQKernel/Contrib/OneProof/FaltingsLemma5Lower/` (13 files, ~110 KB). Proved along the way:
`height_le_of_metrized` (each metrization of 𝒩_A gives one of 𝒩_B: uniformization `Φ ≫ f`, period superlattice of
index `#ker f(ℂ)`), `isogPtsSurjective`, `isogKerCard` (`#ker f(ℂ) ≤ #ker φ(K̄)`), `isogCotBijective` (f étale at
the origin), `tangent_trivial` (char 0: tangent vectors killed by a finite homomorphism are trivial, Cartier's
argument), `covolume_eq_relIndex_mul` (any Haar measure).

**#discharges**: `63 open hypotheses, 1806 theorems checked, 5 discharge one` (no new match: the statement is
weaker than the field, so the fold is a manual rerouting; no autofold spec).

**Manual fold**: the only live use of `faltingsLemma5Printed` is TailZ23.lean L814; replace
`(_root_.CToPrinted.faltingsLemma5BCLower_of_printed r.faltingsLemma5Printed)` by
`(_root_.ReductSplit.faltingsLemma5BCLower_final _root_.GapHeight.faltingsLemma5Lower)`.
TailZ19 L1898 and TailZ22 L309 are off the chain (dependency closure of `frozenTarget`); the other consumers are
field copies, pruned afterwards (sem-prune recipe). Checked in `scratch/faltings5-lower/FoldCheck.lean` (primed
chain `open17'..open28'`, `frozenTarget'`, standard axioms, field no longer read). Counts: 56 → 55 H hypotheses;
strict 45/11 → **44/11** (strictest), 46/10 → 45/10.

**Remains**: nothing on this target. Report: `docs/research/faltings5-lower.md`.
