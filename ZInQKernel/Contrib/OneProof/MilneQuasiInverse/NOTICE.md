# Milne quasi-inverse source — provenance and adaptation log

## Scope and status

This directory contains the **source-only, uncompiled** graph for `AvSplit.MilneIsogenyQuasiInverse`: a finite-Hopf annihilator port, the actual scheme kernel and power descent, and new ring/flatness and final assembly proofs. Source authorship and independent source review are complete; no compiler result, elaborated axiom report, native body check or discharge result is asserted here.

Source preparation date: 2026-11-15. The source port is AI-assisted (Metamate), with independent source reading of the complete seven-module rank-annihilation closure. Independent source reading is not independent compilation or human mathematical review.

The source worktree base read before writing was `Deicyde/diophantine-z-q@9b3f414e3c29ca692d384630db0b4ebd9a7b4322`. The existing target definitions, assemblies, unrelated contributions, and dependency pins are not part of this port's edit scope.

## Immutable upstream source and license

Repository: https://github.com/openai/math

Revision: **`4eaee87548250b2682affda7d05d947c05554bae`**.

Upstream README at this revision describes model-produced proof artifacts at differing verification stages. No individual authorship or verification status is inferred beyond what that source states.

The adjacent `LICENSE` is the byte-preserved upstream root Apache License, Version 2.0, January 2004, including its original appendix/template text:

- Immutable source: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/LICENSE
- Git blob SHA-1: `261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`
- SHA-256: `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`

Original file text and docstrings are retained below the added per-file provenance banners. This notice records source metadata and adaptations, not a legal or compliance assessment.

## Per-file upstream identities

Every path below is relative to the upstream repository. The corresponding local source path is obtained by replacing leading `lean/OAI/` with `Vendor/OAI/` under this contribution directory.

| Upstream path | Git blob SHA-1 | SHA-256 |
| --- | --- | --- |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/RankAnnihilation.lean` | `287848159537c3f564cb7231d586a2aab3a4977c` | `9154c34abfcfd42eb1eef822fb2e7c3e27532ee1d709c42276875594c105d924` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/HopfShear.lean` | `e6653376d31e4b4018473972773bbd40f981131f` | `5dec46551e6a7b45d1c37c916325ae2937c0e5b677ebdb2e06832fa240b7a95c` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/NormCharactersEq.lean` | `bce73e78700f482ddcbd354a3bc95aa6c653fb26` | `834beed44e7298b8bdbbb772894dedaaf37f7a8ac3dd5ca596cdd08efd93a1a7` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/CharacterGroups.lean` | `cf6520e086a45a76b7e9070238300372049f956d` | `bfc279ad3e9f6bc78900ec8442613ea341019805871e5c0498278ffe41101bf9` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/Characters.lean` | `c5a64751025ea6bbcadb07133ade7128d38f39e4` | `130658ccb408c42ef704dc5216dd8427fb47015aff2fbf09a933474996117e0f` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/Naturality.lean` | `d9d48cbc25cdc384659463feea48a4ee1a0215a2` | `e4fa11e3c6ae05ec92e2072a2544ee5dcd0869be457b6d110e72978394a69408` |
| `lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/DualAlgebra.lean` | `aa2c37f5d27e1dad01e055b20431a624a666fcec` | `e1879f7703fea7b2cc43b4622add65e25363a50dbd6a9f5062258a63c9f2c5f7` |
| `lean/OAI/AlgebraicGeometry/Picard/Homomorphisms/FiniteHopfPresentation.lean` | `4412c863798a4a88c0882be70aaf1eccb24ef300` | `90eafc894034a82518f0f3f20328e1b43ab1ae115ad4f87a7062d39095efc2e3` |
| `lean/OAI/AlgebraicGeometry/FormalGeometry/Completion/Finite/GroupAnnihilator.lean` | `260714323bd22e89689b30e59b7df503659490ad` | `28100a234b0415307dc09c4a6d97152f307058ce3b7f744ac50f44d7228f1612` |

Immutable file URL pattern: `https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/<upstream path>`.

## Adaptations

Only these source adaptations are intended in the first conservative port:

1. Add an attribution/provenance banner containing the immutable revision, upstream path, Git blob SHA-1, SHA-256, and source-only status.
2. Relocate every foreign `import OAI.…` to `import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Vendor.OAI.…`.
3. Relocate all upstream OAI namespace declarations, named `end` clauses, and explicit qualified references from `OAI.…` to `MilneQuasiInverse.Vendor.OAI.…` consistently. Canonical Mathlib `_root_.CategoryTheory`, `_root_.AlgebraicGeometry`, algebra, and group carriers remain untouched.
4. Add `GroupAnnihilator.lean`, a small wrapper exporting `ZInQ.Contrib.MilneQuasiInverse.finiteGroup_exists_annihilator` by applying the relocated upstream theorem.
5. Header-order repair (2026-11-15, independent review B1): change only the first-line added-banner opener from `/-!` to ordinary `/-` in `Vendor/OAI/AlgebraicGeometry/Picard/Homomorphisms/FiniteHopfPresentation.lean` and `Vendor/OAI/AlgebraicGeometry/FormalGeometry/Completion/Finite/GroupAnnihilator.lean`. Ordinary comments can precede imports; module-doc comments are body commands. Existing module-doc comments after the imports and every import/proof-body byte are retained. A narrow static header preflight accepts all ten owned modules and rejects the reconstructed original banners; no Lean parser/compiler was executed.

Current destination SHA-256 values for the two header-repaired files (upstream hashes above remain unchanged):

| Vendor path | Destination SHA-256 |
| --- | --- |
| `Vendor/OAI/AlgebraicGeometry/Picard/Homomorphisms/FiniteHopfPresentation.lean` | `6e2fc6d5da9d35bff10fe52765c7cb73bf121db38a5626128698d300f4ebacf5` |
| `Vendor/OAI/AlgebraicGeometry/FormalGeometry/Completion/Finite/GroupAnnihilator.lean` | `28dde398c83403dd1011f341ce0b311daa4912b6d5a606c4755836b20e79a985` |

No pruning of the seven-module rank closure, mathematical proof-body change, dependency upgrade, new Lake dependency, replacement target structure, root/Source alias, supplied-annihilator hypothesis, or extra flat/quotient premise is intended. Any later elaboration compatibility edit must be recorded separately in this adaptation log.

The copied upstream `set_option` directives are retained as source. They have not been exercised by this port preparation.

## Exact finite-Hopf import graph

All foreign imports are contained in this nine-file Vendor subtree; every other import is a named existing Mathlib module.

```text
GroupAnnihilator.lean (public wrapper)
  Vendor/OAI/AlgebraicGeometry/FormalGeometry/Completion/Finite/GroupAnnihilator
    Vendor/OAI/AlgebraicGeometry/Picard/Homomorphisms/FiniteHopfPresentation
      Mathlib.AlgebraicGeometry.Group.Affine
      Mathlib.AlgebraicGeometry.Morphisms.Finite
    Vendor/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/RankAnnihilation
      HopfShear
        NormCharactersEq
          Mathlib.RingTheory.Norm.Basic
      CharacterGroups
        Characters
          DualAlgebra
        Naturality
          DualAlgebra
      Mathlib.LinearAlgebra.Dual.Basis
```

The nine upstream modules total 1,566 physical source lines before added banners; the whole seven-module rank branch is retained. `DualAlgebra` constructs the finite-projective convolution Hopf dual and bidual with their laws; it is not a structure storing an assumed answer. The rank theorem uses an explicit Hopf shear/norm calculation, and its conclusion is an equality of actual scheme multiplication morphisms after treating all algebra-valued points.

## Wrapper contract

The exported wrapper is on the existing Mathlib `Grp (Over (Spec K))` carrier:

```lean
ZInQ.Contrib.MilneQuasiInverse.finiteGroup_exists_annihilator
  (K : Type u) [Field K]
  (G : Grp (Over (Spec (CommRingCat.of K))))
  [IsCommMonObj G.X] [IsFinite G.X.hom] :
  ∃ n : ℕ, 0 < n ∧
    ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ G.X), x ^ n = 1
```

It has no characteristic-zero, perfect-field, algebraic-closedness, reducedness, finite-flatness, quotient, or supplied-annihilator hypothesis. Powers use the internal group law on Hom. The quantifier covers actual scheme-valued tests, including infinitesimal tests, not only rational or geometric points. `n` is the positive finite-Hopf coordinate rank provided by the copied proof.

## Dependency and validation boundary

Target unchanged pins: Lean `4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Original upstream pins read: Lean `4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Static source inspection found the needed current norm, finite-projective contraction, convolution, affine/Hopf, and fpqc interfaces. That is not an elaboration certificate. Compatibility of every old-version structure construction, typeclass inference, simp lemma and transparency option remains unrun.

No Lean/Lake/native compiler, upstream hooks, downloaded project artifacts, cached foreign binaries, or old source acknowledgments were used while preparing or independently reviewing this source. The parent owns later isolated validation, claims, commits, PRs and publishing. The original annihilator-only checkpoint was commit `364d19e9d14f4319f901654300c062972b6030ea`; the complete source graph adds the separate kernel/descent and flatness/assembly work described below. This notice does not certify any compiled result.

## Kernel and descent source port

The following source pieces are from `openai/math@4eaee87548250b2682affda7d05d947c05554bae`, with the same adjacent byte-preserved Apache-2.0 LICENSE. The prefixes below are `lean/OAI/AlgebraicGeometry/` in the upstream repository.

- `Kernel.lean` ports `Picard/PoincareBundle/Kernel/Scheme.lean` whole (192 lines), with a clearly marked appended section constructing the bundled kernel group, commutativity/finiteness and annihilator transport.
  - Git blob: `ab6f03c943082039b04385cbf780dde6102137b2`
  - SHA-256: `94ddea6b724d09c068ebaf8ece143e8a7f8e9f013d63c712d54359eb386d4b76`
- `Descent.lean` combines the following retained source:
  - `FormalGeometry/Completion/OverEffectiveDescent.lean`, whole (44 lines): blob `8732be16cd8087897d1f78d67c053607cff71977`, SHA-256 `f438ccf0407e2dc9ed6472d46fdd0228a08bb26d14fa873ecd57ea8869a7e81a`.
  - `AbelianScheme/IsogenyQuotient/GroupKernelPowerDescent.lean`, whole (51 lines): blob `af69877b23c79f93a7114ec55b17b4198eaf5aab`, SHA-256 `1ce80408aeee6ad89f9746308ab74cca2c26afa327096688cde41203f7bf5a67`.
  - `Picard/Homomorphisms/GroupDescent.lean`, cut at original lines 15, 23–51 and 79–107: blob `09aa0c686a95d8d2bb8f624e91bba2b663154d1c`, SHA-256 `e32a098eded998cec64db44ce33762944e0691519b5ab2d9a7349fc38ba85a4d`.
  - `AbelianScheme/IsogenyQuotient/FppfPowerComplement.lean`, cut at original lines 16–28: blob `c6f1a83a70cc672a27210a4cbf1969fca17e2cf6`, SHA-256 `82d4d3f5db1634ca7e40af16a7a60a58767e7681fd5d9b2b5ee09f980c2b639d`.

Adaptations are ordinary provenance comments before imports; namespaces relocated under `ZInQ.Contrib.MilneQuasiInverse.{Kernel,Descent.*}`; qualified cross-references re-pointed; internal OAI imports replaced by the explicit pinned Mathlib imports needed for the retained cuts; unused declarations omitted; and one redundant local `IsStableUnderComposition @Surjective` instance omitted because the pinned Mathlib supplies it. The retained upstream proof bodies are otherwise preserved. The appended Kernel section reopens the required namespace/universe context; two cross-instance joins use explicit `have`/`exact` rather than rewriting through a different instance path. All compatibility edits remain in these new contribution files.

Independent non-author source review re-fetched all five pieces at the immutable source revision, compared their hashes and retained lines, checked the added kernel transport and both power-composition equations, and cleared them for isolated compilation only.

## New ring, geometry and assembly source

`RingFlatness.lean`, `Flatness.lean` and `Main.lean` are new AI-assisted proof source for this contribution, not copies of a foreign target or result-bearing structure.

- `RingFlatness` proves the finite constant-fibre-rank criterion over reduced rings via residue fields, Nakayama, the kernel/nilradical argument and localization.
- `Flatness` proves the actual shear pullback, transfers the finite/flat constant-rank kernel-pair projection, reduces to affine rings, and derives `finite_surjective_abVarHom_flat` for the original all-fields canonical `PkgI3` inputs `f` and `hf`. No assumed shear, rank, flatness, characteristic-zero or new printed leaf is added.
- `Main` combines the actual kernel group, positive annihilator, this flatness proof and fpqc power descent. It packages the reverse scheme homomorphism with `PkgI3.AbVar.Hom.mk'` and uses the original `AvSplit.comp_natCast_hom'` to obtain both required integer-multiplication equations.
- The top-level `MilneIsogenyQuasiInverse.lean` is an import-only contribution entry point. It adds no target alias or premise and never imports `ZInQKernel.OneProof.Main`.

All proof bodies were independently read against the unchanged Mathlib pin. The source review resolved the needed connected-limit preservation for `Over.forget` from the actual pinned Mathlib instances. Remaining risks are target-version elaboration and instance/rewrite compatibility; no native result is implied by that source review.

## Complete source graph and validation boundary

The graph is `MilneIsogenyQuasiInverse → MilneQuasiInverse.Main → TailQ, Kernel, Descent, GroupAnnihilator, Flatness`; `GroupAnnihilator` reaches the nine vendor modules, and `Flatness` reaches canonical `HDecomp.Objects` plus `RingFlatness`. Kernel, Descent, RingFlatness and the vendor modules import Mathlib only. The graph has no cycle through `OneProof.Main` and does not change the original target, canonical objects, dependency pins or assemblies.

The final export is exactly `ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof : _root_.AvSplit.MilneIsogenyQuasiInverse`. Its source supplies every original premise with no desired-result assumption. This is still a source claim awaiting actual compilation, axiom/discharge output, whole stored-type/body/instance-data validation and independent final review on the final integration.

`#check`/`#print axioms` test scratch and the additional whole-declaration/negative-control checker are kept outside the published mathematical source; they do not provide proof axioms or native proof shortcuts. Pinned Lean computational primitives are trusted only under the documented base/source boundary, with their logical bodies audited; project/vendor custom native delegation remains disallowed. No compiler, checker or control outcome is claimed by this notice.

The Z-is-Diophantine-in-Q goal remains open. Finishing this intermediate source graph, compiling a helper or receiving green CI does not finish the intended theorem.

## Compile record (milne-compile, 2026-11-16)

Compiled on Lean 4.35.0 / Mathlib v4.35.0 (this repository's pins) on a project build machine, on branch
`wip/milne-compile` (base `proof/milne-quasiinverse-20261115` 0eab413d merged with fork `main` 2880fef1e).
The nine vendor modules, `GroupAnnihilator`, `Kernel`, `Descent` and `RingFlatness` compiled with no change.
Two compatibility edits, both outside the vendor subtree, no statement changed:

1. `Flatness.lean`, `flat_of_kernelPair`: the anonymous `have : IsAffine X` shadowed the `wlog`
   hypothesis `this`; renamed `hXaff`.
2. `Main.lean`: `attribute [local instance] ZInQ.Contrib.MilneQuasiInverse.Kernel.kernelGroup`, so that
   instance search finds the group structure on `(Kernel.kernelGrp f.hom).X` (the reducible `kernelGrp`
   unfolds to `kernelObject f.hom`, as in `Kernel.lean`, which declares the same local instance).

Status comments in the non-vendor files were updated. The vendor files are byte-unchanged (their added banners
still say "elaboration at the target pins has not been run"; this record supersedes that line).

`#print axioms ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof`: `[propext, Classical.choice,
Quot.sound]`. `#discharges` (with `ZInQKernel.OneProof.Main` at fork `main` 2880fef1e):
`DISCHARGES [OpenAddedLeaves17.milneIsogenyQuasiInverse] by
ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof`, still assumes `[]`. Full output:
`scratch/milne-compile/discharges-output.txt`; report `docs/research/milne-compile.md`.
