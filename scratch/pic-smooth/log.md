# pic-smooth results log

Base: wip/pic-fix be79cb5b. `git merge origin/main`: already up to date (main = 2880fef1e is in the base).

## Cartier's theorem in the tree
* VERIFIED (git): `cartierSmooth_proof : AVGlue.CartierSmooth` (ZInQKernel/Contrib/OneProof/CartierSmooth.lean) exists
  only on `origin/cloud-b3/w16-h98` (4fa17fc59, 68 added files, no modified file), not on origin/main.
  Merged into wip/pic-smooth (additive merge, no conflict).
* VERIFIED (read): `AVGlue.CartierSmooth` (ZInQKernel/OneProof/H/TailP.lean:305):
  `∀ (k : Type) [Field k] [CharZero k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], LocallyOfFiniteType G.hom → Smooth G.hom`.
  Hypotheses available for the Picard scheme P: `GrpObj P` from `picardFunctorCommGrpObj A.X.hom rep` (CommGrpObj),
  `LocallyOfFiniteType P.hom` from `PicLocFinType`. `CharZero K` is NOT available: `PicDict.PicZeroSmooth`
  and the bundle field `picZeroAbVar : T09Pic.PicZeroAbVar` quantify over every field.

## Finding
* VERIFIED (read): `PicDict.PicZeroSmooth` is `∀ (K : Type) [Field K] (A : AbVar K) ...`, all characteristics.
  Cartier gives the characteristic-0 case only. In characteristic p the claim is true (Mumford §13, STANDARD,
  locator UNVERIFIED) but not a consequence of Cartier. So PicZeroSmooth cannot be removed by Cartier alone.
* Consumers: picZeroAbVar is read only by `T09Pic.t09SymmIsogenyExists_of_four` (TailZ24.lean:807), whose target
  `WeilPairing.T09_SymmIsogenyExists` is again ∀ fields (TailB.lean:3752), consumed by detTate_of_leaves4 (TailK)
  and t9_of_leaves5 (TailN). A char-0 restriction would need a consumer-restricted refactor of pinned modules.
