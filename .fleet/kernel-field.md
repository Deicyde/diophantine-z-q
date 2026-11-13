# kernel-field (fleet summary)

**Result.** g0-mod-field's `KernelFieldExists` (G4 + B1's geometric half) is proved in Lean, with
its statement unchanged, from five leaves and three named glue Props:

- Theorem: `G0ModField.KernelField.kernelFieldExists_of_final`, in
  `scratch/kernel-field/KernelField.lean`.
- Leaves:
  - `HomFreeFinite` (t6);
  - `NeronOggShafarevich` (r7a);
  - `RaynaudCriterion` (r6);
  - `TorsionStructure` (t5);
  - `QMDichotomyYu` (t27).
- Glue:
  - FS5 `FibreComTrivial` (g0-fibresimple's piece; its truth for every triple is qm-pin's repair);
  - `EndTransport`;
  - `ConjIsogMaps`.
- Check: 0 errors, no sorry, standard axioms only (VERIFIED, `build_final.txt`, about 70 s).

**What compiles (new, in `scratch/kernel-field/New.lean`).**

- **G4 connected.** `kernelField_core` and `kernelField_of_model` expose the kernel field `E`
  and `G ≤ GL_r(ℤ)` from g4-weilres/inertia-homs/morph-descend. G4's `hdim`, `hgood` and `hK`
  are proved on rational fibres.
- **B1's discrepancy algebra.** `conjugacyData_of_maps`: the rational cocycle `c`, its inflation,
  `c(1,1) = 1`, and the kernel-degree identity.
- **Torsion count.** `|A(ℚ̄)[n]| = n⁴`, from `TorsionStructure`.
- **Skolem–Noether descent.**
  - `aut_O_inner`: `Aut 𝒪` is inner in `B`.
  - `blinear_of_twisted_iso`: A7's twisted QM isomorphism gives an `𝒪`-linear `μ_σ`.
- **NoCM made explicit.** NoCM is FS5's `End_𝒪 = ℤ`.
  - `endEqOFibre_of` turns it into `End = ι(𝒪)`, via T27 and FS4.
  - `oMaximal`: `𝒪` is a maximal order, proved by Gauss's lemma plus a congruence check by
    `decide`.
  - `conjMaps_of_qm`: integrality and commutation follow (centre of `𝒪` is `ℤ`, faithfulness).
- **Sanity.** The new clause list is satisfiable (`conjIsogMapsAt_bot`).

**Findings.**

1. `KernelFieldExists` genuinely needs NoCM: for a CM fibre, clause 3 of `ConjugacyData` fails
   when `σ` moves the CM field. The pinning issue sits in FS5 alone.
2. `IsBaseChangeOf` and `IsModelOver` record only scheme isomorphisms, so `EndTransport` needs
   rigidity (`RigidityHom`).

**What remains.** `ConjIsogMaps` (large) still needs:

- moving `μ_σ` to `conjData`;
- Galois descent to `L`;
- the quasi-inverse of an isogeny;
- the points/semilinear-`F_σ` bookkeeping.

`EndTransport` (medium) still needs the R1-naturality iso, rigidity, and faithful base change.

Report: `docs/research/kernel-field.md`. Log: `scratch/kernel-field/log.md`.
