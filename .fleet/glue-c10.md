# glue-c10 (C10: one compatible system at 3 and 5)

**Result.** All of C10's glue is proved in Lean, from the two leaves `ChebotarevExists` and
`BrauerNesbittChar0` (pkg-I6, copied verbatim). The main theorem is `GlueC10.c10` in
`scratch/glue-c10/C10.lean`, N5's identification of `r₃` with `ρ_{f,ι₃}`:
- inputs: the trace data `tr r_ℓ(g) = ι_ℓ(c_p)` and `tr ρ_ℓ(g) = ι_ℓ(a_p)` at every arithmetic
  Frobenius `g ∈ G_ℚ` at `p ∉ S`, and C9's 5-adic trace equality;
- it holds for continuous semisimple representations over any Hausdorff topological field of
  characteristic 0.

The proof of `c10` covers:
- the passage from Frobenius classes to `G_ℚ` (density plus continuity);
- the lift of a finite-level unramified Frobenius to `G_ℚ` (`frobLift`). glue-I6-rest left this
  open; it is now proved from Mathlib alone, using compactness of `G_ℚ`,
  `IsArithFrobAt.exists_of_isInvariant`, lying-over and uniqueness at unramified primes;
- the transport `c_p = a_p` through `ι₅`;
- the halving `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`;
- semisimplicity of subrepresentations.

The finite-quotient form recommended by glue-I6-rest is also proved
(`iso_of_trace_eq_frob_finite`). The characteristic-polynomial comparison, a single integer trace
for every `ℓ` from Mumford §19 Thm 4 (pkg-I3 `CharPolyIndepOfEll`), is
`PkgI3.trace_indep_of_ell` in `scratch/glue-c10/Trace.lean`, over pkg-I3's definitions.

**What compiles.** Three files compile with `lake env lean` with no errors and no `sorry`:
- `scratch/glue-c10/C10.lean`, self-contained;
- `scratch/glue-c10/Lift.lean`, the `FrobLift` proof alone;
- `scratch/glue-c10/Trace.lean`.

Every `#print axioms` shows `[propext, Classical.choice, Quot.sound]` (VERIFIED, 23:35-23:47 PST).

**What remains (not glue).** The trace hypotheses of `c10` come from:
- the Néron mapping property;
- Serre–Tate specialization;
- Eichler–Shimura;
- with the link `c_p = ½ β(σ)⁻¹ a_σ tr α_σ` to `trace_indep_of_ell`.

They also need the semisimplicity of `r₃` and `ρ_{f,ι₃}` (C2, or Faltings Satz 3 with
`semisimple_of_le`). None of these is statable over Mathlib today (glue-assembly §2.2).

Report: `docs/research/glue-c10.md`. Log: `scratch/glue-c10/log.md`.
