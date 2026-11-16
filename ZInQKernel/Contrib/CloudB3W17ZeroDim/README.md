# W17: zero-dimensional uniformization and GAGA suppliers

These files prove **special cases**, not either universal OneProof field.

- `Basic.lean`: a locally Noetherian irreducible scheme of dimension at most zero
  is a singleton; an abelian variety of dimension at most zero over an
  algebraically closed field has a singleton rational-point group.
- `Uniformization.lean`: `uniformizationLeaf_of_dim_le_zero` proves the exact
  existing `BPAnalytic.Uniformization.UniformizationLeaf A`, including every
  coordinate-form field, for `A.dim ≤ 0`. The witness is `g = 0`, the zero lattice,
  and the unique additive equivalence.
- `GAGA.lean`: `gagaMorphism_zero_dim` has the exact original GAGA binders and
  realization conclusion for a source `A.dim ≤ 0`. Its proof actually needs only
  the quotient equivalence and the lattice-killing condition: the algebraic zero
  morphism realizes the resulting constant map.

No target statement is edited. No uniformization, analytification, or GAGA leaf
is assumed. No `OneProof.Main` is imported by these modules.

## Reproduction

Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The original target declarations are in
`ZInQKernel/HDecomp/Analytic/Uniformization.lean:91` and
`ZInQKernel/OneProof/H/TailQ.lean:875`.

Build the named modules (the default project build does not compile them):

```sh
LEAN_NUM_THREADS=4 lake build \
  +ZInQKernel.Contrib.CloudB3W17ZeroDim.Uniformization \
  +ZInQKernel.Contrib.CloudB3W17ZeroDim.GAGA
```

Use a scratch file importing `OneProof.Main`, `OneProof.Discharges`, and both
modules to run `#print axioms` on the exported theorems and `#discharges`.
**Neither `uniformizationLeafAll` nor `gagaMorphism` is discharged by these
special cases.** The full command output belongs in the PR evidence.

Reuse is through existing Mathlib Artinian, irreducibility, closed-point,
quotient-group, constant-analytic-function and categorical zero-morphism APIs.
No copied third-party module or new dependency was added. AI-assisted original
proofs; independent rebuilt-commit review is required before readiness.
