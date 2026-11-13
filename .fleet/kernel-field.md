# kernel-field (fleet summary)

**Result.** g0-mod-field's `KernelFieldExists` (G4 + B1's geometric half) is proved in Lean, with
its statement unchanged, from six leaves and two named glue Props.

- Theorem: `G0ModField.KernelField.kernelFieldExists_of_rigidity`, in
  `scratch/kernel-field/KernelField.lean`.
- Leaves:
  - `HomFreeFinite` (t6);
  - `NeronOggShafarevich` (r7a);
  - `RaynaudCriterion` (r6);
  - `TorsionStructure` (t5);
  - `QMDichotomyYu` (t27);
  - `RigidityHom` (g0-fibresimple's textbook leaf, Mumford §4 Cor. 1).
- Glue:
  - FS5 `FibreComTrivial` (g0-fibresimple's piece; its truth for every triple is qm-pin's repair);
  - `ConjIsogMaps` (the conjugacy maps, geometric part).
- Check: 0 errors, no sorry, standard axioms only (VERIFIED, `build_final.txt`, about 75 s).

**What compiles (new, `scratch/kernel-field/New.lean`, about 1900 lines).**

- **G4 connected.** `kernelField_core` and `kernelField_of_model` expose the kernel field `E` and
  `G ≤ GL_r(ℤ)` from g4-weilres/inertia-homs/morph-descend. G4's `hdim`, `hgood` and `hK` are
  proved on rational fibres.
- **B1's discrepancy algebra** (`conjugacyData_of_maps`). It gives the rational cocycle `c`, its
  inflation, `c(1,1) = 1`, and the kernel-degree identity.
- **Torsion count.** `|A(ℚ̄)[n]| = n⁴`, from `TorsionStructure`.
- **Skolem–Noether descent.**
  - `aut_O_inner`: `Aut 𝒪` is inner in `B`.
  - `blinear_of_twisted_iso`: A7's twisted QM isomorphism gives an `𝒪`-linear `μ_σ`.
- **NoCM made explicit.** NoCM is FS5's `End_𝒪 = ℤ`.
  - `endEqOFibre_of` turns it into `End = ι(𝒪)`, via T27 and FS4.
  - `oMaximal`: `𝒪` is a maximal order, proved by Gauss's lemma plus a congruence check by
    `decide`.
  - `endTransportBC_of_rigidity`: the result transported to the Hom field (pullback pasting plus
    rigidity).
  - `conjMaps_of_qm`: integrality and commutation follow.
- **Sanity.** The new clause list is satisfiable (`conjIsogMapsAt_bot`).

**Findings.**

1. `KernelFieldExists` genuinely needs NoCM: for a CM fibre, clause 3 of `ConjugacyData` fails
   when `σ` moves the CM field. The pinning issue sits in FS5 alone.
2. `IsBaseChangeOf` and `IsModelOver` record only scheme isomorphisms, so moving endomorphisms
   between models needs rigidity. This is now done.

**What remains.** `ConjIsogMaps` (large) still needs:

- moving `μ_σ` from `P` to `conjData` (same pasting and rigidity argument);
- Galois descent of the `G_L`-fixed `μ_σ` to `L`;
- the quasi-inverse of an isogeny (Mumford §8);
- the points/semilinear-`F_σ` bookkeeping.

Report: `docs/research/kernel-field.md`. Log: `scratch/kernel-field/log.md`.
