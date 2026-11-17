# piclft (fleet note)

**Verdict: proved outright, no new leaf.** `PicDict.PicLocFinType` says that every scheme representing
`Pic_{A/K}`, for an abelian variety `A` over a field `K`, is locally of finite type (cited as Kleiman 9.4.8 /
BLR 8.2 Thm 3). It is proved as stated, in every characteristic: `PicLFT.picLocFinType_proof` in
`ZInQKernel/Contrib/OneProof/PicLocFinType.lean`. No Picard scheme is constructed.

**Compiles (VERIFIED).** `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.PicLocFinType` succeeded. Axioms: propext, Classical.choice, Quot.sound. `#discharges`
shows `DISCHARGES [OpenAddedLeaves24.picLocFinType] by PicLFT.picLocFinType_proof` with `still assumes: []`. The
autofold spec is `scratch/piclft/autofold.json`. Its dry run generates `OpenAddedLeaves25` and
`sixContactMin_of_open48`, and reports strict 12/18 on 30 -> 11/18 on 29 (strictest 12/18 -> 11/18). The generated
module compiles (`scratch/piclft/FoldDryRun.lean.txt`).

**Proof idea.**
1. Functor-of-points criterion: if every `Spec B → X` over `K` factors through `Spec S` for a finitely generated
   `S ≤ B`, then `X` is locally of finite type. The argument is a retraction on each affine open.
2. Yoneda, plus the vendored Kleiman 9.2.5 (`PicDict.Θ`, applicable since `pushforwardUnitUniversal` is proved),
   reduces this to: every Picard class on `A ×_K Spec B` comes from `A ×_K Spec K[s]` for some finite `s`.
3. That spreading-out statement is proved from tools already in the tree:
   - CloudW07 EGA IV 8.5.2 for finitely presented module sheaves;
   - CloudW07 affine hom-descent;
   - CloudW06 `AdjoinFinset` limits;
   - Mathlib `AffineTransitionLimit`.
   The new step is that invertibility descends to a finite stage, by local trivializations on preimages of
   affine opens.

**Remaining.** Nothing for this field. The integrator runs autofold (without `--dry-run`) and the usual fold
checks. After the fold, piczero-char0's `picZeroAbVar0_of_leaves` rests only on `kleimanPicZeroProper` (host task
kleiman-proper). Report: docs/research/piclft.md.

Commits: 756791df3 (criterion) … 48ee2ca3d (contribution file, discharges, autofold), b2ca8e83d (report).
