# H-67 verification report

## Result

Closed theorem:

```lean
ZariskiConn.ZariskiConnectedness_proof.{u} :
  ZariskiConn.ZariskiConnectedness.{u}
```

This is the exact fixed H-67 proposition, at arbitrary universe `u`, with no
additional hypotheses. It proves geometric connectedness, including the
nonemptiness built into Mathlib's `ConnectedSpace` fibre condition.
No other #80 row or reduction-naturality edge is claimed.

Fixed statement revision: `cba8157f7d5d09a4a3c8462aba2f3245494a870e`.
Verified working base: `f70ec251fd4bca6ae3115741c21fe661e7aaac3e`.
The current fork `main` was read back as that same revision before packaging.

## Builds

On Lean 4.35.0 / Lake 5, with `LEAN_NUM_THREADS=2`:

```text
lake build +ZInQKernel.Contrib.CloudW02Connectedness.Basic:olean
Build completed successfully (9217 jobs).
exit code: 0

lake build +ZInQKernel.Contrib.CloudW02Connectedness.Checks:olean
Build completed successfully (9218 jobs).
exit code: 0
```

Job totals include replayed cached dependencies; they are not counts of newly
compiled source files. `Checks.lean` checks the exact proposition at arbitrary
universe `u` and prints the closed theorem's type and axioms.

The required `lake exe cache get` was run under the owner's cache lock before
builds, with unchanged pins: no downloads, already decompressed 9,031 files.

## Kernel axiom outputs

```text
'ZariskiConn.ZariskiConnectedness_proof' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

The target is a closed proof, not the preexisting conditional
`properSmoothGenConnected_of_zariskiConnectedness` wrapper. Both named-module
builds exited zero. The final candidate's 137 Lean files have no code occurrence
of `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, or `run_tac`.
The lexical audit is supplementary to the kernel checks above.

## Source and bridge

The complete exact affine-noetherian input proof is reused from Anthropic FLT at
`6e837e75355538c7f80bab5b956861e86c4eacc2`:

https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.lean

The selected import closure is 135 original modules / 1,178,538 source bytes.
Every original source matches its immutable Git blob and size. Its proofs use
proper coherent-cohomology finiteness, formal-functions image stabilization,
flat base change, and idempotent arguments; the source includes fibre nonemptiness.
The current contribution adds only transport across an affine target's
`Y ≅ Spec Γ(Y)` and the proven Zariski-local-at-target reduction.

`SOURCE_MANIFEST.json`, `NOTICE.md`, `PORT_CHANGES.md`, and the per-file notices
record origin and modifications. The complete upstream LICENSE, NOTICE and
ATTRIBUTION are copied unchanged. The 36 source files adapted beyond imports
contain proof-elaboration/API changes, not weaker mathematical claims.

AxiomMath/Stacks at `c496df0d9beea9deaeabcea8492605f9a0a2313b` was also inspected:
its full Stein-factorization and noetherian formal-functions input are available.
The smaller exact FLT closure was selected; this contribution copies no W1
Stacks declarations under a second module path.

## Unchanged inputs and scope

- `ZInQKernel/Contrib/ZariskiConn/Basic.lean` is untouched.
- The full vendored Tau Ceti subtree used by that fixed target is unchanged.
- Root `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` are unchanged.
- Mathlib remains `56a005855ea17e0b0958f73ec801ae140b0a1679` / v4.35.0.
- New committed files are confined to `ZInQKernel/Contrib/CloudW02Connectedness/`.
- No extra hypotheses, replacement definition, desired axiom, weak substitute,
  default-root/scratch build, `lake update`, other-worker branch, or merge.

There is no mathematical or compilation gap for H-67. The owner coordinator's
independent validation and PR to `Deicyde/diophantine-z-q main` remain outside this
worker's work; this worker does not merge or open that PR.
