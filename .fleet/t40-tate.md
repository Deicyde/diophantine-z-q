# t40-tate (2026-11-13)

**Main result.** `ZInQ.RLeaf.TateCuspLaurent` is proved outright: `ZInQ.RLeaf.tateCuspLaurent :
TateCuspLaurent` (ZInQKernel/Contrib/RLeaf/TateCusp.lean). Hence T40 and T39 follow from
`IgusaTransitive` alone (`x1RationalCusp_of_igusaTransitive`, `x1ConstantField_of_igusaTransitive`).
Also proved, for task t40-igusa (agreed by message): `ZInQ.RLeaf.tateMuN : TateMuN`
(ZInQKernel/Contrib/RLeaf/TateCuspMuN.lean). With t40-igusa's `IgusaTransitive ↔ X0Transitive ∧
TateMuN`, T40/T39 now depend only on `X0Transitive`; t40-igusa writes T40.lean.

**Declarations proved** (all `#print axioms` = [propext, Classical.choice, Quot.sound]):
- `ZInQ.RLeaf.tateCuspLaurent : ZInQ.RLeaf.TateCuspLaurent`
- `ZInQ.RLeaf.x1RationalCusp_of_igusaTransitive : IgusaTransitive → X1Belyi.X1RationalCusp`
- `ZInQ.RLeaf.x1ConstantField_of_igusaTransitive : IgusaTransitive → X1Belyi.X1ConstantField`
- `ZInQ.RLeaf.TateCuspTorsion.tateLaurentTorsion : ZInQ.RLeaf.TateLaurentTorsion` (new Prop: an
  elliptic curve over ℚ((t)) with j ∉ ℚ[[t]] and a rational point of exact order N, N ≥ 2)
- `ZInQ.RLeaf.tateCuspLaurent_of_tateLaurentTorsion : TateLaurentTorsion → TateCuspLaurent`
- `ZInQ.RLeaf.tateMuN : ZInQ.RLeaf.TateMuN`
- generic steps `TateCuspMuN.tateMuNAt_of_unit`, `TateCuspMuN.tateMuNAt_of_root`.

**What compiles.** `lake build ZInQKernel.Contrib.RLeaf.TateCuspMuN ZInQKernel.Contrib.RLeaf.TateCusp`:
"Build completed successfully (9394 jobs)". New files: RLeaf/TateCuspGlue.lean,
TateCuspTorsion.lean, TateCusp.lean, TateCuspMuN.lean; 57 Tau Ceti main (4d91513e) modules
backported whole and 5 partial "extras" files under ZInQKernel/Contrib/TauCeti/Backport/ (Tate
uniformization homomorphism closure; six files patched for the pinned Mathlib, each with a
"Modified" note); ThirdParty/TauCeti/NOTICE updated; diffcheck2: MOD-UNNOTED 0, NOTE-ONLY 0.

**Method.** ℚ((t)) (and K((t))) as complete normed fields via `Valued.toNormedField`; Tate curve
E_q, q = t^N, point t (TateCuspTorsion); glue via the j-isomorphism over the algebraic closure
(u², r ∈ ℚ((t))) and torsion counting with T36; TateMuN via ζ_N on ℚ(ζ_N)((t)) and the
coefficientwise Galois action.

**What remains.** Nothing of my target. For T40: `X0Transitive` (t40-igusa's open leaf).
Report: docs/research/t40-tate.md; log: scratch/t40-tate/log.md.
