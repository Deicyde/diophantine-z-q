# milne-compile: `milneIsogenyQuasiInverse` proved (draft PR #23 compiled)

**Verdict (VERIFIED, compiled).** The source of draft fork PR #23 compiles on this repository's pins (Lean 4.35.0,
Mathlib v4.35.0) after two technical fixes, and proves the field outright, with no new leaf:

```
ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof : AvSplit.MilneIsogenyQuasiInverse
'...milneIsogenyQuasiInverse_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves17.milneIsogenyQuasiInverse] by ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
```

(`scratch/milne-compile/discharges-output.txt`, from `scratch/milne-compile/Check.lean` against
`ZInQKernel.OneProof.Main` of fork `main` 2880fef1e.) The statement `AvSplit.MilneIsogenyQuasiInverse`
(`ZInQKernel/OneProof/H/TailQ.lean:1207`) is unchanged; `scratch/milne-compile/CheckField.lean` checks
`b.milneIsogenyQuasiInverse = milneIsogenyQuasiInverse_proof := rfl` for `b : HDec.HSyn.OpenAddedLeaves17`.
Target met: the field leaves the bundle (-1 field; strict count 34/11 on 45 -> 33/11 on 44, strictest
34/11 -> 33/11, from `autofold.py --dry-run`).

## What was built

Branch `wip/milne-compile`: base `proof/milne-quasiinverse-20261115` (0eab413d) merged with fork `main` (2880fef1e).
Entry point `ZInQKernel/Contrib/OneProof/MilneIsogenyQuasiInverse.lean` (imports `ZInQKernel.OneProof.H.TailQ`, the
module declaring the statement, and `MilneQuasiInverse.Main`; never `ZInQKernel.OneProof.Main`). 16 modules,
130 KB of Lean in total:

| module | outcome |
| --- | --- |
| 9 vendor modules `MilneQuasiInverse/Vendor/OAI/...` (openai/math 4eaee875, Apache-2.0, LICENSE kept) | compiled, no change |
| `GroupAnnihilator` (wrapper) | compiled, no change |
| `Kernel` (vendor port + additions) | compiled, no change |
| `Descent` (vendor port cuts) | compiled, no change |
| `RingFlatness` (new) | compiled, no change |
| `Flatness` (new) | **fix 1**: in `flat_of_kernelPair`, an anonymous `have : IsAffine X` shadowed the `wlog` hypothesis `this` (error "Function expected at this"); renamed `hXaff` |
| `Main` (new) | **fix 2**: `attribute [local instance] Kernel.kernelGroup` (instance search could not find `MonObj`/`IsCommMonObj (Kernel.kernelGrp f.hom).X`, since the reducible `kernelGrp` unfolds to `kernelObject f.hom`; `Kernel.lean` uses the same local instance) |
| `MilneIsogenyQuasiInverse` (entry) | compiled |

No mathematical step failed. Status comments in the non-vendor files and a compile record in
`MilneQuasiInverse/NOTICE.md` were updated; the vendor files are byte-unchanged. Scan of all 16 modules: no
`sorry`, `#eval`, `run_cmd`, `initialize`, `syntax`, `notation`, macro, elaborator, `native_decide`,
`implemented_by`, `extern`, `axiom`, `unsafe` or `opaque`. The only options are
`backward.isDefEq.respectTransparency(.types) false` (elaboration only), in `Descent`, `Flatness` and two vendor
files.

## The proof (all in Lean, all compiled)

For a field `K`, `A B : PkgI3.AbVar K`, `f : Hom A B` with `f.hom.left` finite and surjective:

1. **Kernel** `G = pullback f.hom η[B.X]` in `Over (Spec K)` with the group structure of the represented kernel
   functor; commutative (as `A.X` is) and finite over `K` (base change of the finite `f.hom.left`).
2. **Annihilator** (vendored finite-Hopf rank annihilation, openai/math): a finite commutative group scheme over a
   field is killed by its (positive) coordinate rank `n`, on every test scheme; transferred to every
   `x : T ⟶ A.X` with `x ≫ f.hom = 1` through the kernel point bijection.
3. **Flatness** (new): the shear `(a, a') ↦ (a, a⁻¹a')` identifies the kernel pair of `f.hom` with
   `A ×_K ker f` over the first factor, so the first projection of the kernel pair of `f.hom.left` is finite, flat
   and of constant rank; a finite surjective morphism onto a reduced scheme with this property is flat
   (affine-local reduction to `RingFlatness.flat_of_rankAtStalk_tensor_self`: a finite module over a reduced ring
   with constant fibre rank is flat). `B.X.left` is reduced because it is geometrically integral over `K`.
4. **Descent** (vendored cuts, openai/math, with Mathlib's fpqc `EffectiveEpi`): `f.hom.left` is flat, surjective
   and quasi-compact, so `(𝟙 A.X) ^ n`, which kills the kernel, descends to `r : B.X ⟶ A.X` with
   `f.hom ≫ r = (𝟙 A.X) ^ n` and `r ≫ f.hom = (𝟙 B.X) ^ n`, `r` a monoid homomorphism.
5. **Packaging**: `g = Hom.mk' r`, `d = n`, and `(𝟙 _) ^ n = [n]` by `AvSplit.comp_natCast_hom'`.

## Leaves

None new. The field was a published leaf (Milne 1986 Rem. 8.4; `kinds.tsv` LEAF); it is now a theorem from Mathlib
alone (plus the vendored, compiled openai/math code and this contribution's new code).

## Fold

`scratch/milne-compile/autofold.json`:

```json
{"name": "milne-compile",
 "imports": ["ZInQKernel.Contrib.OneProof.MilneIsogenyQuasiInverse"],
 "discharges": [{"field": "milneIsogenyQuasiInverse",
   "proof": "_root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof"}]}
```

`autofold.py --dry-run` (fork `main` 2880fef1e, top module TailZ42) writes `sixContactMin_of_open36` over
`OpenAddedLeaves18`; that module (`scratch/milne-compile/AutofoldDryRun.lean`, the dry-run output minus its first
line) compiles, and `#print axioms HDec.HSyn.sixContactMin_of_open36` is standard. The fold itself (TailZ, Main,
kinds.tsv, claims.tsv, OPEN.md) is left to the integrator.

## Files

* `ZInQKernel/Contrib/OneProof/MilneIsogenyQuasiInverse.lean`, `ZInQKernel/Contrib/OneProof/MilneQuasiInverse/`
  (16 modules, LICENSE, NOTICE.md with the compile record).
* `scratch/milne-compile/`: `log.md`, `Check.lean` + `discharges-output.txt`, `CheckField.lean`, `autofold.json`,
  `AutofoldDryRun.lean`.
