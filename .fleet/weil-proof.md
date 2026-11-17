# weil-proof (field `weilPairingMumford`): status

**Main result (VERIFIED, standard axioms).** Three of pic-dict's seven Mumford displays for this field are now
Lean theorems with no hypotheses:
* §20 `MumfordWeilPairingAC` (Mumford's `ē_n = t_x^*ψ ∘ ψ⁻¹` is well defined, `μ_n`-valued, bilinear),
  `WeilProof.mumfordWeilPairingAC_proof`, via `pullbackCompMonoidal_proof` (pull-back of sheaves of modules is a
  monoidal pseudofunctor for the vendored structure);
* §23 `MumfordWeilAltAC` (`e^L_n(x,x) = 1`), `WeilProof.Theta.mumfordWeilAltAC_proof`, by a theta-group
  commutator argument plus divisibility of `X(k)` (`divisibleAC`, from the tree's étaleness of `[n]`);
* `MumfordKLFiniteAC` is no longer used (the open field `phiAmpleIsogeny` replaces it).

`WeilProof.Theta.weilPairingMumford_final` gives the field from 4 Mumford leaves (§6 Cor. 4, §8 (iv), §8 Thm 1,
§20 nondegeneracy) and the open field `phiAmpleIsogeny`. Files `ZInQKernel/Contrib/OneProof/WeilFormula.lean`,
`WeilFormulaTheta.lean` (build; `#discharges` lists it). No new leaf.

**Count.** `scratch/weil-proof/autofold.json` (nondegeneracy flagged pending reading): 34/11 -> 37/11, no rise;
with pic-dict's "unread" flag: 34/11 -> 38/10. Dry-run modules compile. On origin/wip/leaf-fold32b
(`autofold-lf32.json`, tested in a temporary worktree): 16/21 -> 18/21, module compiles.

**Not done.** The field is not removed: nondegeneracy (descent + `#X̂[n] = #X[n]`) and the three line-bundle
displays (seesaw / cube) stay leaves.

Report: `docs/research/weil-proof.md`.
