# rv-leaves-a — fleet report

Task: an adversarial review of the leaves the announcement will cite from pkg-I1 and pkg-I5, and of
glue-assembly's `GlueOutputs` and its assembly theorem. Full report: `docs/research/rv-leaves-a.md`.
Log: `scratch/rv-leaves-a/log.md`.

**Verdicts.**
- `ThetaModularity`: FAITHFUL.
- `QMHauptmodul`: FAITHFUL, but COMPOSITE. No paper prints it as one theorem. It combines Lin–Yang
  Ex. 30, Igusa's theta formulas, the Shimura/Hashimoto embedding and the (2,4,6) signature. Its
  "Baba–Granath §3" citation should be narrowed to Thm 2.1 and the §3 datum, because BG 3.7/3.9
  are not needed.
- `IgusaClebschSeparation`: FAITHFUL.
- `BostEC`, `BostGoodGenus2`: FAITHFUL, as consequences. In Faltings' normalization Bost's bound
  is −log(π√2)·g ≈ −1.4913·g, which is at least −(3/2)·g.
- `PazukiGoodGenus2`: FAITHFUL modulo an UNVERIFIED normalization. It assumes Pazuki uses
  Deligne's metric (shift log π). A hardened form with shift +3 is a consequence for any shift up
  to 3, keeps the final constant 10000·2²⁴, and compiles.
- `GlueOutputs`: each conjunct matches its cited theorem's constants (GR14 κ, Faltings Lemma 5,
  Bost, Pazuki; Javanpeykar's printed form is UNVERIFIED). But it is a disguised height bound,
  essentially equivalent to `JHeightBound`, so it is glue and **must not be announced as a leaf**.
- None of the statements is vacuous, wrong or trivially true.

**Compiles** (`lake env lean`, axioms propext, Classical.choice, Quot.sound only):
- `ConclusionCheck.lean`: `GlueAssembly.SixContactMinAt Mult.S_mul = ZInQ.SixContactMin := rfl`,
  and `GlueOutputs Mult.S_mul → ZInQ.SixContactMin` against the real `HeightMin`. Glue-assembly
  §1.3's "cannot import HeightMin" is wrong: run `lake build ZInQKernel.Hypotheses.HeightMin`
  first.
- `PazukiHardened.lean`, `I5Hardened.lean` (`PazukiGoodGenus2'` and old ⇒ new), and
  `ConclusionCheckHardened.lean` (the whole assembly with `PazukiOutput` at `hA + 3`).

**Numerics** (VERIFIED):
- `qm_check.py`, written independently from the Lean definitions:
  - j_θ is invariant under the Atkin–Lehner elements of norm 2, 3 and 6;
  - j_θ = 0, ∞ and −16/27 at the fixed points of i+j, (1+j)/2 and μ;
  - the local orders there are 4, 6 and 2, matching the elliptic orders, so j_θ has degree 1.
- `theta_modular.py` re-run: weights and signs hold on 5 generators of Sp₄(ℤ).

**Remains:** all theorem numbers and constants are UNVERIFIED, since no papers were available
here; this includes Pazuki's C₂ and normalization and Javanpeykar's Thm 1.1.1 form. Lin–Yang
Ex. 30's divisor statement was not read. Satisfiability of `Genus2Eq.Good` is SPECULATIVE.
