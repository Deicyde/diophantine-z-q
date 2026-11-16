# CloudW06PoincareRigidity: provenance, licences and changes

Task cloud-w06 (owner-requested ten-worker fleet, worker 6), 2026-11-14. Frontier rows (fork `main`,
`docs/research/frontier.md`): **H-75** `AVB2.T11bExists` (proved here) and **H-72**
`ZInQ.Contrib.AVB1.PoincareComplement` (not proved; see the issue status on
elliotglazer/diophantine-z-q#81). Statements fixed at fork `main` `cba8157f7d5d09a4a3c8462aba2f3245494a870e`;
the branch is rebased on `f70ec251fd4bca6ae3115741c21fe661e7aaac3e`, where the files below are
unchanged: `scratch/av-b2/olean/AVB2Main.lean`, `ZInQKernel/HDecomp/Objects.lean`,
`ZInQKernel/HDecomp/LeafPush2/T.lean`, `ZInQKernel/Contrib/AVB1/Poincare.lean` and the pins.
Lean v4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (the project's pin, unchanged).

## Files

| File | Origin | Main declarations |
|---|---|---|
| `T11bExists.lean` | new | `T11bExists` (verbatim copy, see below), `T11bExists_proof : T11bExists`, `T11bRigidity_unique`, `exists_stage_factorization`, `exists_point_stage`, `family_split`, `isMonHom_of_isMonHom_map` |
| `T11bRigidity.lean` | new | `T11b_Rigidity_proof : ZInQ.LeafPush2.T11b_Rigidity` (corollary) |
| `Rigidity.lean` | adapted from AxiomMath/Mordell (Apache-2.0), modified | `rigidity_family` |
| `AdjoinFinset.lean` | vendored from AxiomMath/Stacks (Apache-2.0), namespace renamed | `AdjoinFinset.isLimitBcCone`, `bcDiagram_isAffineHom`, `bcDiagram_compactSpace_and_quasiSeparatedSpace`, `bcProj_fst`, `bcProj_snd` |
| `LICENSE` | the Apache License 2.0 text, as distributed with AxiomMath/Mordell (identical to `ThirdParty/GreenTao/LICENSE`) | |

All declarations live in the namespace `ZInQ.Contrib.CloudW06PoincareRigidity`. They depend only on
`propext`, `Classical.choice` and `Quot.sound` (`#print axioms`); no `sorry`, no `axiom`, no
`native_decide`.

## The copied statement (H-75)

`T11bExists` in `T11bExists.lean` is a byte-for-byte copy (916 UTF-8 bytes / 887 characters, docstring included) of
`scratch/av-b2/olean/AVB2Main.lean` lines 209-219, the definition `HDec.AVB2.T11bExists`, at
`cba8157f` and at `f70ec251`. In that scratch assembly `PkgI3` resolves to `HDec.PkgI3`, leaf-fold3's
renamed copy of the kernel's `PkgI3`; in this file the same text resolves to the kernel's
`_root_.PkgI3` (`ZInQKernel/HDecomp/Objects.lean`), checked by
`example : T11bExists = (… _root_.PkgI3.AbVar …) := rfl`.

## Third-party code

* **AxiomMath/Stacks**, https://github.com/AxiomMath/Stacks, commit
  `c496df0d9beea9deaeabcea8492605f9a0a2313b`, Apache License 2.0; file
  `StacksFrontier/AlgebraicGeometry/Limits/AdjoinFinsetSystem.lean` (sha256 `4e260d67…`; no copyright
  line in the file) → `AdjoinFinset.lean`. Changes: a provenance and change-notice comment is added
  at the top, and the namespace `AlgebraicGeometry.AdjoinFinset` becomes
  `ZInQ.Contrib.CloudW06PoincareRigidity.AdjoinFinset` (with `open AlgebraicGeometry`), so that it
  cannot clash with another port of the same file that keeps the upstream names. The file is
  otherwise unchanged.
* **AxiomMath/Mordell**, https://github.com/AxiomMath/Mordell, commit
  `82a30cb7857f6e3cfdb1be91f5533c0ccb57d493`, Apache License 2.0; theorem `Faltings.rigidity` in
  `Mordell/AbelianVariety/Rigidity.lean` (sha256 `78109b29…`; no copyright line in the file). The
  proof of `rigidity_family` in `Rigidity.lean` is adapted from it. Changes: `F : G ⊗ G ⟶ G` for a
  proper group scheme `G` becomes `F : Y ⊗ G ⟶ H` with `Y` only locally of finite type, `H` only
  separated and locally of finite type, and the unit sections replaced by arbitrary `K`-points. The
  proof is rewritten to match (`φ = (pr₁, F)` lands in `Y ⊗ H`, closed points via
  `isClosedImmersion_of_comp_eq_id`), and the declaration is renamed. Mordell's proof follows
  Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`
  (`Mathlib/AlgebraicGeometry/Group/Abelian.lean`, Copyright (c) 2026 Andrew Yang, Authors: Andrew
  Yang, Christian Merten, Apache-2.0).
* `isMonHom_of_isMonHom_map` in `T11bExists.lean` reuses the proof of Mathlib's
  `Functor.FullyFaithful.isMonHom_preimage` (`Mathlib/CategoryTheory/Monoidal/Mon.lean`).

## AI use

Written by an AI agent (Metamate / agentcloud session, worker 6). It compiles with the project's
pinned toolchain; it has not been reviewed by a person.
