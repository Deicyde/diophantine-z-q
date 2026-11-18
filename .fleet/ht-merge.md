# ht-merge (2026-11-17)

**Result.** derham-scholze's `ScholzeDeRhamAlg` and ht-abvar's `HodgeNumberH1AbVar` are merged into one consequence leaf,
`DeRhamScholze.HTMerge.ScholzeH1AbVar`. For an abelian variety `A` of dimension `g` over a finite `F/ℚ_p`, it says that
`H¹_ét(A_{F̄}, ℚ_p)` (Mathlib's pro-étale cohomology) is de Rham, the Hodge filtration has its jumps in `[0, 1]`, and
`dim_{ℚ_p} Fil¹ D_dR = [F:ℚ_p]·g`. Sources: manuscript `lem:de-rham-descent` L10954-10965 (Scholze 2013 Cor. 1.8 +
Thms 9.1/9.3 + corrigendum) and L10996 (Hodge numbers `2,2`). Net change on kinds.tsv H rows: the joint fold goes from
5/27 on 32 (ht-abvar's spec) to **5/26 on 31**, one GLUE lower (against the current top 5/24 on 29: +2 instead of +3).

* (1) Search: `ScholzeDeRhamAlg` is applied only in `dual_deRham_of_scholze` (`hS p F A.X 1`: an abelian variety in
  degree 1), so the merge is allowed.
* (2) Which `g`: the end consumers (G9, through R10) use only abelian surfaces (`A'.dim = 2`). But the H field
  `hodgeTateDecompAbVar`, R10 and the four theorems kept unchanged are stated for every `g`. So the fold leaf is for
  general `g`, labelled a generalization (on-the-spot). The manuscript-exact `ScholzeH1AbSurf` (`g = 2`) is also stated,
  follows from the general leaf, and proves the H field for every abelian surface. A `g = 2` fold would mean restricting
  the bundle field types (report §2.3) and saves no row.
* (3) Re-proved from `ScholzeH1AbVar` + `T10_TateDuality`, with the same conclusions: `deRhamVpAbVarDirect_of_scholzeH1`(`Milne`),
  `hodgeTateDecompHom_of_scholzeH1`, `hodgeTateDecompOr_of_scholzeH1Milne`, `hodgeTateDecompAbVar_of_scholzeH1`.
  `scholzeH1AbVar_of_old` shows the old pair implies the new leaf.

**Compiles** (standard axioms): `ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean` (lake build); `scratch/ht-merge/Axioms.lean`;
`#discharges` (both open fields discharged, each still assuming exactly `[ScholzeH1AbVar, T10_TateDuality]`); the dry
run `scratch/ht-merge/HTMergeDryRun.lean` (`frozenTarget_hm` over main's new Main with `hPC`, standard axioms). The
hand-fold spec is `scratch/ht-merge/autofold.json` and supersedes ht-abvar's. Base: origin/main merged, no conflicts.

**Remains:** the fold itself (integrator; needs `--allow-rise` or a ruling, +2 GLUE net with c8-conrad3), readings of
Milne Thm 12.1(a) and of `h^{1,0} = g`, and optionally the `g = 2` reroute. Report: `docs/research/ht-merge.md`.
