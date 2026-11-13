# hom-unify (2026-11-13)

**Main result.** r1b-state's `T11aHom` and conj-twist's `HomLinearLift` are over the same layer
(`PkgI3.AbVar`, `LeafPush2.CPts`, `LeafPush2.IsUniformization`). They are the two **converse
halves** of `Hom(A_ℂ, B_ℂ) ≅ {M : MΛ_A ⊆ Λ_B}`:
- `T11aHom` goes from a lattice map to a homomorphism, over ℂ (GAGA);
- `HomLinearLift` goes from a homomorphism to a linear map, over any K (BL 1.2.1).

So neither implies the other. The single leaf `ZInQ.HomUnify.HomLatticeCorr` (both halves) implies
`T11aHom`, `HomLinearLift` and the existing leaf T11(a) `T11a_RiemannEnd`. The uniqueness clause is
proved outright. In the assembly, G10 now comes from `HomLinearLift` (with the bundle's T5, T26 and
T35), with an end-to-end theorem to `ZInQ.SixContactMin`.

**Compiles (VERIFIED, all axioms `[propext, Classical.choice, Quot.sound]`, no sorry):**
- `ZInQKernel/Contrib/HomUnify/Corr.lean` (`lake build ZInQKernel.Contrib.HomUnify.Corr`).
  Proves `homLinearLift_of_corr`, `t11aHom_of_corr`, `t11a_riemannEnd_of_corr`, `corr_iff`,
  `hom_ext_of_cpts`, `induces_unique`, `t11aHom_iff_ex`, `corr_iff_lift_realize` and
  `t11aHom_of_realize`.
- `scratch/hom-unify/HomUnifyFlat.lean`: linked-tate's flat file plus conj-twist §1-§16, plus
  rv-gluepieces2's c1, plus `parts/H20_bundle.lean`. `lake env lean` exits 0 in 602 s, with 233
  standard axiom reports. It proves:
  - `G0Galois.g10Glue_of_homLinearLift : T5 → T26 → T35 → HomLinearLift → G10Glue`, for the
    assembly's `G10Glue`;
  - `G0Galois.GaloisPiecesHom` (with `homLift : HomLinearLift` in place of `odd`) and
    `G0Galois.galoisPieces_of_hom : TextbookLeaves → GaloisPiecesHom → GaloisPieces`;
  - `HSyn.GluePieces3Hom` (linked-tate's `GluePieces3` with `homLinearLift` in place of
    `g10Glue`), `HSyn.gluePieces3_of_hom`, and
    `HSyn.sixContactMin_of_leaves3Hom : ResearchLeaves → TextbookLeaves → GluePieces3Hom → ZInQ.SixContactMin`;
  - `HomUnify.homLinearLift_of_corr` and `HomUnify.g10Glue_of_corr`.
- Copied statements were checked mechanically by `scratch/hom-unify/py/verbatim_check.py`: ALL OK.

**Leaf for the list.** `HomLatticeCorr`, in place of T11(a); it implies T11(a). Sources:
Birkenhake–Lange, *Complex Abelian Varieties* §1.2, Prop. 1.2.1; Mumford, *Abelian Varieties*
§1 and §3; Serre's GAGA / Chow. All theorem numbers are UNVERIFIED. This is a proposal only; no
existing file was changed.

**Remains.** `HomLatticeCorr` is a textbook leaf and is not proved: it needs analytification and
GAGA, which Mathlib lacks. r1b-state's `T11aHom` consumers are not re-run; they can use
`t11aHom_of_corr`.

Report: docs/research/hom-unify.md. Log: scratch/hom-unify/log.md.
