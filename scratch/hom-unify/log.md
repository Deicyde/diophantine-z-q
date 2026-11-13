# hom-unify results log

Marks: VERIFIED (read in a file, computed, or compiled), STANDARD (published, reference given),
SPECULATIVE. Theorem numbers from memory: UNVERIFIED.

## Set-up (2026-11-13)
- `git merge origin/wip/r1b-state`, `git merge origin/wip/conj-twist`: both already contained in the
  worktree base 57a7fa26. `git merge origin/main` (b7cdba8e, fork main moved): clean, brings
  linked-tate (GluePieces3), rv-gluepieces2. No ZInQKernel/HDecomp file changed.
- `lake build ZInQKernel.Hypotheses.JHeight …` needed before the Leaves prefix (upstream `ZInQ.*`
  helpers; first prefix run failed with "unknown module prefix 'ZInQ'").

## Step 1: the layers and the two statements (VERIFIED, read)
- `R1bState.T11aHom` (scratch/r1b-state/Part8b_Hom.part L23-29) and `G0Galois.HomLinearLift`
  (scratch/conj-twist/ConjTwist.lean L787-795) are over the SAME layer: the build's `PkgI3.AbVar`
  (ZInQKernel/HDecomp/Objects.lean; R1b's `open LeafQM LeafQM.AV PkgI3` resolves `AbVar` to
  `PkgI3.AbVar`, no `LeafQM.AV.AbVar` exists), `ZInQ.LeafPush2.CPts`, `ZInQ.LeafPush2.IsUniformization`
  (HDecomp/LeafPush2/R22.lean). No bridge between layers is needed.
- They are converse halves of `Hom(A_ℂ,B_ℂ) ≅ {M : MΛ_A ⊆ Λ_B}`:
  - `T11aHom`: K = ℂ, σ = id, dim A = dim B = g; lattice-preserving `M` ⇒ ∃! `f` (realization; GAGA).
  - `HomLinearLift`: any K, σ, dims g, h; `f` ⇒ ∃ `M` (lifting; holomorphy + BL 1.2.1).
  Neither is a formal consequence of the other (each asserts the existence of the objects the other
  takes as input). Both are true (STANDARD).
- `ZInQKernel/Contrib/HomUnify/Corr.lean`: `HomLatticeCorr` (both halves; clause 1 = HomLinearLift body,
  clause 2 = realization for all g, h). Proved: `homLinearLift_of_corr`, `t11aHom_of_corr`,
  `t11a_riemannEnd_of_corr`, `corr_iff`, `hom_ext_of_cpts` (Mathlib `ext_of_apply_eq` + `pointOfClosedPoint`),
  `induces_unique`, `t11aHom_iff_ex`, `corr_iff_lift_realize`, `t11aHom_of_realize`.
  Runs: (1) final `rw` on `p0 (closedPoint)` failed (PrimeSpectrum vs ↥Spec coercion in motive);
  (2) same with `key`; (3) unknown `isLocallyClosed_univ` → `isOpen_univ.isLocallyClosed`;
  (4) VERIFIED `lake build ZInQKernel.Contrib.HomUnify.Corr` success, 9 axiom reports standard.
- verbatim_check.py: ALL OK (T11aHom, HomLinearLift copies; HomLatticeCorr copy; ConjTwistNontrivial c1 =
  conj-twist; GaloisPiecesHom and GluePieces3Hom differ from the originals only in the G10 field).

## Step 2: assembly (linked-tate's flat file + H10/H11/H20)
- LPrefix.olean (linked-tate's Leaves + 3 extra imports): exit 0, 580 s.
- TailBase.olean (= scratch/linked-tate/olean/Tail.lean): exit 0, ~2 min.
- HConj (H10 = ConjTwist L39-2005 minus resQ/qEmbRing/resQ_spec; H11 = c1_g10 minus 4 dup decls):
  run 1 parse error (block extractor missed a docstring containing a blank line), run 2 parse error
  (block end inside docstring); fixed extractor; run 3 VERIFIED exit 0, 33 s.
- HBundle (H20): VERIFIED exit 0, 5 s, first try; 8 axiom reports standard.
- HomUnifyFlat.lean (47459 lines): VERIFIED exit 0 in 602 s, 0 errors, no sorry, 233 axiom reports, all
  standard (2 line-wrapped in the output).
- Declarations: `G0Galois.g10Glue_of_homLinearLift`, `G0Galois.GaloisPiecesHom`, `G0Galois.galoisPieces_of_hom`,
  `HSyn.GluePieces3Hom`, `HSyn.gluePieces3_of_hom`, `HSyn.sixContactMin_of_leaves3Hom`,
  `HomUnify.homLinearLift_of_corr`, `HomUnify.g10Glue_of_corr`.
- Note: conj-twist's own `g10Glue_of_leaves` proves g10-odd's ORIGINAL G10Glue (opaque T11/T12 hypotheses), not
  the assembly's (T11a/T11b hypotheses); the assembly's is obtained through rv-gluepieces2 c1's
  `g10Glue_of_conjTwist_new`.

## Step 3
- Single leaf: `HomLatticeCorr` (BL §1.2 Prop. 1.2.1, Mumford §1/§3, GAGA; UNVERIFIED numbers), to replace
  T11(a) `T11a_RiemannEnd` on the leaf list (it implies T11a, T11aHom, HomLinearLift). Proposal only.
