# qm-pin (2026-11-13): pin Φ by the universal family

**Main result.** The rv-g0pieces defect is repaired. `R1fpProps` gains two clauses, both
consequences of Shimura–Deligne R1(a) under the existing Lemma P premise:

- `R1famProps`: `Φ` is induced by a family `𝒜 → Y` (proper, smooth of relative dimension 2, `ι`,
  level sections). Every object in `Φ_K(y)` is the pullback `y*𝒜` (`IsFibreOf`).
- `R1univProps`: every such family over a proper smooth curve `S/ℚ` is classified by a morphism
  `S → Y`.

`R2fpProps` is unchanged. Option 2 of the review (an F1 clause in R2fp) was rejected: with all
polarizations it does not pin `π`, and pinned to type `μ` it moves glue F1 into a leaf. Option 3
(the leaf's own triple) leaves the pieces unprovable.

**What this buys (compiled).**

- Two triples satisfying the repaired clauses agree up to a morphism `g`. The `Φ`-half is
  compiled (`phi_part`). The `π`-half is one named piece of curve glue, `MobiusGlue` (Möbius map
  fixing `0, ∞, −16/27`), argued in the report but not compiled.
- So `FibreSimple`, `ThetaPointOfFibre` and `ModularConstituent`, which quantify over all triples,
  reduce to their statement for the leaf's own triple (`pointwise_of_witness_mor`).
- Relabeling attack: a natural relabeling survives only through a family (`r1fpPin_relabel_iff`).
  Automorphisms survive and are harmless (`r1fpPin_aut`, `transfer_pointwise`). Under the
  comparison every surviving relabeling is geometric (`relabel_geometric`). The old list cannot
  have the comparison (`relabel_geometric_old`).

**Lean: everything below compiles, 0 errors, standard axioms only.**

- `scratch/qm-pin/QMPin.lean` (imports the kernel's QM.Leaves): 20 `#print axioms` lines.
- Kernel `QM/Leaves.lean` with the edit, minimal and full versions. The only proof change is two
  `obtain` patterns. A4, A7, NV step 2, M9 and notes-fix's `fibre_conjugates_isomorphic` go through.
- `Split.lean` with the edit: 0 `sorry`; `glueOutputs_of_leaves` and `sixContactMin_of_leaves` are
  standard.
- `h-decomposition/Leaves.lean` with the edit: only its known `sorry`.
- `QMPinKernelFull.lean`: a drop-in `QM/Pin.lean` candidate for the full edit.

Patches for the integration: `scratch/qm-pin/QM-Leaves-full.patch`, `Split-full.patch` and
`HDecLeaves-full.patch` (minimal versions alongside), plus `apply_edit.py`.

**Open arithmetic question.** Are two rational fibres of `Y₃ → P¹` ever `ℚ`-isomorphic?

- Rational non-branch fibres are `G`-torsors, `|G| = 144`, so `Y_t ≅ Y_s` iff `L_t = L_s`.
- For each `u`, only finitely many `s` qualify (Faltings; the components of `Y₃` have genus 4).
- For `u` with full monodromy, the fibre over `J(u)` is never isomorphic to a CM fibre. The group
  fact behind this is computed (`deck_group.py`: `(𝒪/3𝒪)^×/±1` has no abelian subgroup of
  index ≤ 2).
- The question is not settled, and it no longer matters for soundness.

**What remains.**

- `MobiusGlue` (glue, not compiled).
- The genuine-triple arguments for the three pieces (NoCM, F1 on `A`, Glazer §4).
- A human check that `R1univProps` is faithful. It uses the extension of the type-`μ` polarization
  over a normal base (Faltings–Chai I.2.7, number UNVERIFIED).

Report: `docs/research/qm-pin.md`.
