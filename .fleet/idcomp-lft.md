# idcomp-lft (fleet note)

**Verdict: proved outright, no new leaf.** `PicDict.IdentityComponentLFT` (SGA 3 VI_A 2.4 / Stacks 0B7R: the
identity component of a group scheme locally of finite type over a field is open, a subgroup, and geometrically
irreducible) is proved as stated, in every characteristic: `IdCompLFT.identityComponentLFT_proof` in
`ZInQKernel/Contrib/OneProof/IdentityComponentLFT.lean`.

**Compiles (VERIFIED).** `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.IdentityComponentLFT` succeeded, with no warnings in the new module. `#discharges`:
`DISCHARGES [OpenAddedLeaves23.identityComponentLFT] by IdCompLFT.identityComponentLFT_proof`, `still assumes: []`,
axioms propext, Classical.choice, Quot.sound. Autofold spec `scratch/idcomp-lft/autofold.json`. Its dry run
generates `OpenAddedLeaves24` and `sixContactMin_of_open47`, reports strict 13/18 on 31 -> 12/18 on 30 (strictest
13/18 -> 12/18), and the generated module compiles (`scratch/idcomp-lft/FoldDryRun.lean`).

**Proof idea.** Openness: locally noetherian schemes have open connected components. Geometric connectedness:
Stacks 04KV in its rational-section form (already vendored and proved). Subgroup: `V ×_K V` is connected, so its
images under `μ` and `ι` are connected and contain `e`. Geometric irreducibility: reduce to an algebraically closed
`L`. There, the set of points with an open irreducible neighbourhood is open and nonempty, so by Jacobson it contains
a closed point. Translations by rational points act transitively on closed points, so it contains every closed point,
and by Jacobson again it is everything. `V_L` is open in `G_L` and connected, hence irreducible. No smoothness of
`G_red` and no Cartier's theorem is used.

**Remaining.** Nothing for this field. The integrator runs autofold (without `--dry-run`) and the usual fold checks.
After the fold, piczero-char0's `picZeroAbVar0_of_leaves` rests only on `picLocFinType` and `kleimanPicZeroProper`.
Report: docs/research/idcomp-lft.md.
