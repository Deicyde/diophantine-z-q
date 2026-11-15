# sir-printed: fleet summary

**Verdict.** The goal as posed cannot be reached in Lean today, and the field does not need it.
- Kottwitz 1992 §5 and Lan 2013 Thm 1.4.1.11 are PEL functors. Mathlib v4.35 and the kernel have no dual abelian
  scheme, no polarization and no Weil pairing over a base. So the PEL functor, the relative Lemma P (step (a)) and the
  integral comparison of level structures (step (b)) cannot be stated in Lean.
- The field `shimuraIntegralModelRep` is used only at `S = Spec ℚ̄` and for Yoneda on the Hecke relabelings of the
  universal object over `𝒴`.
- New leaf `SIRPrinted.ShimuraIntegralModelUsed` asks exactly that. Proved in Lean (standard axioms):
  - `ShimuraIntegralModelRep → ShimuraIntegralModelUsed` (never stronger);
  - `ShimuraIntegralModelUsed → ShimuraGoodReductionNoGuard` (enough for the consumer).
- Its derivation from Lan 1.4.1.11 + 5.3.3.1 uses Lemma P over `ℚ̄` only, plus explicit automorphisms of the PEL
  functor. Their algebra is compiled in `scratch/sir-printed/TwistAlgebra.lean`.
- Level 3 at `3 | D` is allowed by Lan (`□ = {p}`, `H ⊂ G(Ẑ^p)`) and by Kottwitz. `p = 2, 3` are false cases (bad
  reduction) but no consumer uses them: every consumer needs all `p > 324`, and nothing more.

**Compiles.**
- `ZInQKernel/Contrib/OneProof/ShimuraIntegralModelUsed.lean`.
- `scratch/sir-printed/TwistAlgebra.lean`, with `trd_map`, `rosati_twist`, `E0_twist`, `E0_rightMul`,
  `twist_cocycle`, `trd_ne_zero_of_dag`.
- `scratch/sir-printed/BypassFold.lean`: hand fold `OpenAddedLeaves18 → OpenAddedLeaves16`,
  `sixContactMin_of_open29`, and a `frozenTarget` copy. All standard axioms.
- `#discharges`: nothing new matches. This is expected, because the new leaf is weaker than the open field.

**Leaf rating.** `shimuraIntegralModelUsed` is not the printed form. It is a consequence of the printed PEL theorem
plus Lemma P over `ℚ̄`, by a paper-only derivation (report §3).
- Spec: kind published, flag "pending reading" (`scratch/sir-printed/autofold.json`, with the bypass
  instructions, since `autofold.py` cannot fold a weaker leaf).
- Strict counts are unchanged; the reading needed shrinks to Lan 1.4.1.11 / 5.3.3.1 for one datum.

**Remains.**
- A reading of Lan for the datum (report §3.1).
- The integrator's hand fold, and a locators.md row (text in report §7).
- The full field, with every base, would need the relative Lemma P (true and published per §4, unstatable in Lean).

Report: docs/research/sir-printed.md; log: scratch/sir-printed/log.md.
