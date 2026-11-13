# kf-glue (fleet note)

**Verdict.**
- `EndTransport` is **proved** (no hypotheses): `G0ModField.KernelField.endTransport`, from kernel-field's
  reduction plus mul-rigidity's `rigidityHom`.
- `ConjIsogMaps` is **reduced** to `MulIsogeny` (mul-rigidity's textbook leaf, which itself reduces to the
  leaf `KerUnitOpen` or to two cotangent glue Props) plus one new glue Prop, `TwistDescent`.
  - `TwistDescent` is Galois descent of twisted isomorphisms between conjugate abelian varieties from ℚ̄
    to the Hom field `L`. It has no moduli content and is not QM-PIN.
  - Main theorem: `conjIsogMaps_of_descent : MulIsogeny → TwistDescent → ConjIsogMaps`.
  - Both statements are copied verbatim from scratch/kernel-field, unchanged.

**What compiles.** VERIFIED: `lake env lean scratch/kf-glue/KfGlue.lean` gives rc=0, no sorry, and all
21 `#print axioms` lines are standard (`build7.txt`). `KfGlue.lean` is built by `assemble.sh` from
verbatim copies of KernelField.lean and MulRigidity.lean plus the new `Points.lean` and `New.lean`.
New proofs:
- **Level 1 (points bookkeeping).** `conjIsogMaps_of_semilinear`: `m_σ(x) = Spec σ ≫ x ≫ F_σ`.
  `LiftQbarPoints` and `FiniteFibreQbarPoints` are proved from Mathlib: finite surjective morphisms are
  surjective with finite fibres on ℚ̄-points.
- **Level 2.** `semilinearIsogAt_of_twist` constructs `F_σ = E_σ ≫ ι(b_σ)`:
  - Skolem–Noether gives `b_σ`;
  - `ι(b)` is an isogeny with explicit quasi-inverse `ι(N b⁻¹)`, so no Mumford §8 leaf is needed;
  - the discrepancy lies in `End_L` via rigidity.
- **Level 3.** `bc_transport` and `conjTwist_of_rational`: A7 (`conj_iso_of_rational`) transported to
  the Galois conjugates of the rational fibre.
- **Final form.** `kernelFieldExists_of_kerUnitOpen`, from the leaves T6, NOS, Raynaud,
  TorsionStructure, T27 and KerUnitOpen plus the glue FS5 and TwistDescent.
- **Sanity check.** `semilinearTwistAt_bot`.

**What remains.**
- `TwistDescent` (glue; SPECULATIVE truth argument from a model check). Mathlib route:
  - Mathlib v4.35 has the fpqc topology subcanonical and `EffectiveEpi` for flat surjective
    quasi-compact morphisms (VERIFIED by reading `Sites/Fpqc.lean`);
  - the standard statement is `GaloisDescentMor` (stated and typechecked in New.lean, unused);
  - still missing: `L'⊗_L L' ≅ ∏ L'` (not found in Mathlib) and the conjugate/semilinear bookkeeping.
- `MulIsogeny` (mul-rigidity) and FS5 (g0-fibresimple, the only NoCM/QM-PIN input) are unchanged.
- Porting note: kernel-field's KernelField.lean needs `hR1.2.2.2` changed to `hR1.2.2.2.1` on this
  base, because `R1fpProps` now has 6 clauses. `assemble.sh` applies this fix.

Report: docs/research/kf-glue.md. Log: scratch/kf-glue/log.md.
