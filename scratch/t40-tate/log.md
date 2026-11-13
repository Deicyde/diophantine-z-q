# t40-tate results log

Target: `ZInQ.RLeaf.TateCuspLaurent` (ZInQKernel/Contrib/RLeaf/X1RationalCusp.lean).

## Plan (2026-11-13 09:30)
- Split: `TateLaurentTorsion` (exists elliptic W/ℚ((t)), j ∉ ℚ[[t]], point of exact order N, N ≥ 2)
  ⇒ `TateCuspLaurent` (algebraic glue: φ: ℚ(j) → ℚ((t)), j ↦ j(W); W ≅ E_j^φ over the algebraic
  closure with L-rational x-transform (char 0, j ≠ 0,1728); torsion counting (T36) to lift the
  point back to `EjBar`).
- `TateLaurentTorsion` from Tau Ceti's Tate uniformization hom (tc-main
  TateCurve/Homomorphism.lean; closure 69 modules / 16k lines, 57 not vendored, 22 main/nov01-only)
  plus a complete ultrametric NormedField structure on ℚ((t)).

## Results
- 09:32 TateCuspGlue.lean with `def TateLaurentTorsion` compiles (lake env lean). VERIFIED.
- 10:15 Backport of tc-main (4d91513e) TateCurve.Homomorphism closure: 57 full modules under Backport/ + 5 extras files (decls absent from vendored oct16 versions); lake build ...TateCurve.Homomorphism succeeds. VERIFIED.
- 10:35 TateCuspTorsion.lean: `ZInQ.RLeaf.TateCuspTorsion.tateLaurentTorsion : TateLaurentTorsion` compiles, axioms [propext, Classical.choice, Quot.sound]. VERIFIED (lake env lean). Normed field on ℚ((t)) = Valued.toNormedField with RankOne hom' = toNNReal 2 ∘ embedding.
- 09:50 (host clock) TateCuspGlue.lean: `ZInQ.RLeaf.tateCuspLaurent_of_tateLaurentTorsion : TateLaurentTorsion → TateCuspLaurent`, axioms [propext, Classical.choice, Quot.sound]. VERIFIED (lake env lean).
- 09:53 TateCusp.lean: `ZInQ.RLeaf.tateCuspLaurent : TateCuspLaurent`, `x1RationalCusp_of_igusaTransitive : IgusaTransitive → X1Belyi.X1RationalCusp`, `x1ConstantField_of_igusaTransitive : IgusaTransitive → X1Belyi.X1ConstantField`; `lake build ZInQKernel.Contrib.RLeaf.TateCusp` exit 0, all three axioms [propext, Classical.choice, Quot.sound]. VERIFIED (build log scratch/t40-tate/build-tatecusp.txt).
  (Earlier log timestamps 10:15/10:35 were estimates, not the host clock; the host clock read 09:26 at start.)
- diffcheck2: counts {'IDENT': 1644, 'NOTE-ONLY': 0, 'MOD-NOTED': 35, 'MOD-UNNOTED': 0, 'NOPROV': 110, 'NOSRC': 0}. VERIFIED. NOTICE: t40-tate entries added (Source bullet + Location paragraph).
