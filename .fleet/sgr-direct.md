# sgr-direct (2026-11-15) — summary

**Main result.** The consumer of `shimuraIntegralModelRep` is now proved with no integral model of the Shimura
curve. It is proved from bundle fields plus one new GLUE Prop.

- **The consumer.** The field is used only through `HDec.HeckeRestNV.HeckeVertWitness`: the Hecke cover `E/ℚ(X)` has
  no vertical ramification at `p > 324`. `quotientP1Coordinate` has the same single consumer. Both facts were
  checked by reading the chain.
- **Compiled theorem** (standard axioms), in `ZInQKernel/Contrib/OneProof/SGRDirectElkies.lean`:
  `SGRDirect.heckeVertWitness_of_nvElkies : R1R2fp → TorsionStructure → QMAutCard → SerreRigidity3 →
  ALFixedPoints → NVLocalInertia → ElkiesX6StarPrinted → HeckeVertWitness`.
  - Every input except `NVLocalInertia` is an existing field: `r1r2`, `t5`, `qmAutCard`, `serreRigidity3`,
    `alFixedPoints`, `elkiesX6StarPrinted`.
  - `NVLocalInertia` is h-b1's Lemma NV step 3. It is commutative algebra of tame covers, with no Shimura content:
    from unramified residue fields over a branch point, vertical inertia is conjugate into the inertia over that
    point.
- **Proved along the way**, in `SGRDirectNV.lean` (imports TailG):
  - `ramifiedSqrtInertia` and `vertInertiaTrivial` (Mathlib Hilbert theory; the second over the DVR `ℤ[X]_(p)`);
  - `heckeBranchFibreUnram` (from `R1R2fp` and T5);
  - `exists_good_sqrt` and `even_padicValRat_of_sq_mem`;
  - Lemma NV simplified to one branch point (`−16/27`) and one square root.
- **Proved in `SGRDirectElkies.lean`:**
  - `heckeSqrtBranchAny_of_elkies`: `√(−(27X+16)) ∈ E`, from Elkies' chart. It uses R1(b) universality,
    `CurveBijIso`, a Möbius coordinate comparison through `MobiusGlue`, and a section pulled back to `Spec B`;
  - Nullstellensatz density, `eq_zero_of_forall_ringHom_qbar`.

**Counts.** A deep bypass fold would remove `shimuraIntegralModelRep` and `quotientP1Coordinate` and add
`nvLocalInertia`, for a net of −1 GLUE. The fold is not executed: `autofold.py` cannot do it. The plan is in
`scratch/sgr-direct/autofold.json` and report §5.

**Checks.**
- `lake build` of both Contrib files succeeds.
- `#discharges`: 63 open hypotheses, 1869 theorems checked, 7 discharge one; none from these files, as expected.
- No `sorry` and no code that runs at build time.

**What remains.**
1. `NVLocalInertia`. Proof route: a Kummer base change at `(p, X − b)`, purity in dimension 2 (already proved in the
   chain) and T2, then the inertia comparison. Report §6.
2. The deep fold.

The abelian-variety route (NOS, Raynaud, Néron, CM) cannot replace this. It needs characteristic-`p` moduli (report
§3, argued).

Report: `docs/research/sgr-direct.md`. Log: `scratch/sgr-direct/log.md`.
