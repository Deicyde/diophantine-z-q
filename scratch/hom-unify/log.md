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
