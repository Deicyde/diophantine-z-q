# rv-wave17 (adversarial review of the wave-17 Lean statements)

**Verdict: every statement reviewed is FAITHFUL.** This covers leaf-push's R8, T9, T29a/b,
T32a/b and T23, and the glue of glue-c10 (C10), glue-a6-alg (A6 = Lemma PR(ii)) and
glue-d1-local (D1). No leaf is stronger than the published theorem, none is vacuous, no glue
hypothesis smuggles in its conclusion, and every glue hypothesis can be met. Report:
docs/research/rv-wave17.md.

Qualifications:
- T23 clause (i), basis invariance with no continuity hypothesis, is trivially true. It is now
  proved in Lean from the definitions (`RvW17.t23_clause_i`, scratch/rv-wave17/T23i.lean), so it
  is glue, not literature content. Clauses (ii)-(v) carry Fontaine's content. T23 inherits
  pkg-I4's `B_dR`, which was not re-examined.
- C10's trace hypotheses can be met only with `S ⊇ {3, 5} ∪ ramified primes`. This is a usage
  note for the docstring, not a defect.
- Wording repair: glue-c10's "all of C10's glue is proved" should say "the Galois-side glue";
  the link `c_p = ½β(σ)⁻¹a_σ tr α_σ` is still unwritten (glue-c10 §3 item 3 says so).

Compiles (VERIFIED, `lake env lean`, one process at a time): Push, PushDR, C10, Lift, Trace,
A6, Quat, Extend and Local, with 0 errors. A check over all 605 declarations finds only
propext, Classical.choice and Quot.sound. Also compiled: scratch/rv-wave17/Probe.lean (Krull
topology on `G_ℚ`, discrete `ℤˣ`, quaternion notation, `d % 4` for negative `d`) and T23i.lean.
The copied leaves are identical to their sources (diff).

Remains: the leaves copied from earlier packages (pkg-I2, I3, I4's `B_dR`, I6,
glue-conductor) were taken from their own reviews, not re-reviewed. T9's `GSp` limit and the
C10 trace link are still unwritten glue.
