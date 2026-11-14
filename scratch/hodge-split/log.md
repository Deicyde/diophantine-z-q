# hodge-split results log

Task hodge-split, 2026-11-14. Base cba8157f. Lean checks: `lake env lean scratch/hodge-split/<file>.lean`
after `lake build ZInQKernel.Contrib.R10.Amend ZInQKernel.Contrib.AbVarBC.Dim` (both built 03:40, exit 0).

## H-52 `G0Galois.FiniteImageHT` (FiniteImage.lean)
- Row copied verbatim from scratch/leaf-fold5/Leaves5.lean l.50965 (objects from ZInQKernel/Contrib/G9/I4Layer.lean).
- LEAVES: `TateTwistInvariants` (Tate 1967 §3.3 Thm 2, K finite over ℚ_p inside ℚ̄_p), `AxSenTate`
  (Tate 1967 §3.3 Thm 1 / Sen 1969 / Ax 1970). Locators UNVERIFIED (no source on host).
- PROOF `finiteImageHT_of_tate : TateTwistInvariants → AxSenTate → G0Galois.FiniteImageHT`.
  Steps: open kernel (continuity of Mathlib's absoluteGaloisGroup.map, closed finite-index ⇒ open,
  krullTopology_mem_nhds_one_iff_of_normal), finite coefficient field (adjoin of the finitely many
  entries; g9-derham's `liftGL`), finite descent (g9-derham's `descent_finrank`, Speiser — replaces
  Hilbert 90 of the row's citation).
- COMPILED 03:50: axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
