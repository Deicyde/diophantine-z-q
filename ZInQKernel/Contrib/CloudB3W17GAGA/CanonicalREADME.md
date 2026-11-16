# W17 canonical analytic supplier — honest partial H105

**This contribution constructs a holomorphic group map of complex-point sets, not a morphism of schemes.** It does not prove `ZInQ.HomLattice.GAGAMorphism`, and adds no new field, printed leaf, or algebraicity premise. The supplied source uniformization remains an explicit hypothesis.

## Results and exact hypothesis boundary

Namespace: `ZInQ.Contrib.CloudB3W17GAGA`.

- `strongUnif_canonical_diffeomorph` identifies the **given arbitrary** `g`, discrete `Λ`, and strong `φ` with the actual canonical complex-point model. Its only substantive premise is the original `IsStrongUnif A (RingHom.id ℂ) Λ φ`; it does not exhibit such a `φ`.
- `existsUnique_holomorphic_descent_canonical` produces a unique `F : CPts A (RingHom.id ℂ) →* CPts B (RingHom.id ℂ)` satisfying `F (Additive.toMul (φ (proj Λ z))) = ψ z`. Its premises are exactly the original strong-source predicate, `IsAnalyticHom` for `ψ`, and `ψ` killing `Λ`.
- The descended `F` is **`MDifferentiable`** in the actual canonical models. This is not an asserted multivariable `ContMDiff … ω` upgrade of `ψ`, whose regular-function pullbacks are only `DifferentiableOn ℂ` in the original predicate.
- There is no `g = canonical model dimension`, fullness/`IsZLattice`, B-uniformization, H103, GAGA, or separately supplied model-fact premise in these two canonical headlines.

The arbitrary-source inverse uses `φ`'s own `g` regular coordinates and invertible derivative on `ℂ^g → ℂ^g`, the ordinary analytic inverse function theorem, and a small quotient covering chart. The original model dimension is not assumed equal to `g`. The canonical topology, atlas, carrier comparison, and Γ-evaluations are the committed Hodge dictionary values, not replacements.

## The genuine remaining obligation

H105 asks for `f : A.X ⟶ B.X` with `ψ z = Additive.toMul (φ (proj Λ z)) ≫ f`. This package does **not** construct `f`.

After the proved point-level descent, the residual obligation is genuine **SGA 1 XII Corollary 4.5 full faithfulness**: turn the resulting canonical holomorphic map into an algebraic morphism inducing it on points. That theorem is **not used or assumed in any proof here**. The source locator is Cor. 4.5 (proper complex schemes), not Thm. 4.4 (coherent sheaves). Neither density, rigidity, nor a closed/compact graph by itself supplies the missing scheme map. No `GAGAMorphism_proof` closing file is included.

## Self-contained source scope and shared prerequisites

The mathematical source is the independently reviewed private head `2b5dae91d333d83c3441c3fb72cf6c079e0425bc`. This fresh publication copy is based on fork main `2880fef1e827a05ab9238cd200e555c585f00e30`. The only change to its Lean bytes is the comment clarification in `CanonicalOriginalPoints.lean` formerly headed “Unconditional”. No theorem type or proof changed.

Until the shared prerequisites are merged, a self-contained snapshot includes:

- The four canonical files listed below.
- The byte-identical `Descent.lean` and `Graph.lean` suppliers shared with [PR #32](https://github.com/Deicyde/diophantine-z-q/pull/32). Their **27 declarations are separate** from the canonical census below.
- The needed `CloudB3W17Hodge` core: its 25 port modules, `Bridge.lean`, `RelativeDimension.lean`, and unchanged `LICENSE`, `NOTICE`, `Port/MODIFIED.md`, shared with [PR #35](https://github.com/Deicyde/diophantine-z-q/pull/35).

These are the actual import dependencies, not unstated external prerequisites. No H103 closing file, Lie/proper/compactness supplier, or H103 assembly module is carried merely because the shared PR has it. Refreshing after prerequisite integration can remove duplicate added files.

Hodge provenance: `Paul-Lez/HodgeConjecture` at `2ead713179628a3c738197d5996f51c8a9c886ac`, Apache-2.0, The Formal Conjectures Authors. Preserve the port's file headers, `CloudB3W17Hodge/LICENSE`, `NOTICE`, and `Port/MODIFIED.md` verbatim. The previously reviewed import remapping and three removed custom notations are documented there; this packaging introduces no further port edits. Original W17 analytic bridges are AI-assisted work of this project.

## Verified declaration census — all 55, explicitly

Independent review checked **30 CanonicalModels + 2 AtlasTransport + 7 CanonicalPointComparison + 16 CanonicalOriginalPoints = 55 declarations**, including definitions and instances, not just selected headline theorems. All use only `propext`, `Classical.choice`, and `Quot.sound`. The older author's 51 selected reports were not a complete census. The fresh-base gate repeats all 55.

### `CanonicalModels.lean` — 30

`APts`, `pointDom`, `continuous_of_regular_pullbacks`, `continuous_analyticHom`, `mdifferentiableAt_of_regular`, `contMDiffAt_of_regular`, `mdifferentiable_analyticHom`, `mdifferentiable_quotientDescent`, `phiPts`, `phiInv`, `phiPts_phiInv`, `phiInv_phiPts`, `isAnalyticHom_strongPhi`, `continuous_phiPts`, `continuous_phiInv`, `strongUnifHomeomorph`, `strongUnifHomeomorph_apply`, `strongUnifHomeomorph_symm_apply`, `contMDiff_phiPts`, `contMDiff_phiInv`, `strongUnifDiffeomorph`, `strongUnif_diffeomorph`, `pointDescentHom`, `pointDescentHom_spec`, `pointDescentHom_unique`, `mdifferentiable_pointDescentHom`, `existsUnique_holomorphic_descent`, `canonicalPoint_neighbourhood`, `canonicalPoint_holo`, `canonicalPoint_coords`.

### `AtlasTransport.lean` — 2

`contMDiff_homeomorph_transported`, `contMDiff_homeomorph_symm_transported`.

This standalone module imports only `Mathlib.Geometry.Manifold.ContMDiff.Defs`. Its `module`, `public import`, and `public section` are **built-in Lean 4.35 module-system keywords**, not new custom syntax, notation, macros, elaborators, or build-time code. Both comparisons use the unchanged choice-based `Homeomorph.chartedSpace` construction; no `IsManifold` premise or alternate atlas is inserted.

### `CanonicalPointComparison.lean` — 7

`comparisonTopology`, `comparisonChartedSpace`, `contMDiff_cptHomeomorph`, `contMDiff_cptHomeomorph_symm`, `cptDiffeomorph`, `cptDiffeomorph_apply`, `cptDiffeomorph_symm_apply`.

This imports the pure atlas helper and the committed Bridge, without importing H105 or the quotient-descent module. Thus H103 can reuse the atlas helper without a cycle.

### `CanonicalOriginalPoints.lean` — 16

`cptsIntegral`, `cptsTopology`, `cptsChartedSpace`, `cptModelEquiv`, `cptModelHomeomorph`, `cptModelDiffeomorph`, `cEvalAt_eq_canonicalEvaluate`, `pointDom_eq_canonicalPreimage`, `canonical_isOpen_pointDom`, `regular_neighbourhood_of_homeomorph`, `canonical_cpts_neighbourhood`, `contMDiffOn_pullback`, `canonical_cpts_holo`, `canonical_cpts_coords`, `strongUnif_canonical_diffeomorph`, `existsUnique_holomorphic_descent_canonical`.

## Verification contract

Lean: `leanprover/lean4:v4.35.0`; Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`. Dependency pins, original target, `Objects.lean`, and `OneProof.Main` source are unchanged.

Fresh verification is serialized in an isolated publication clone: named `Main`, `Discharges`, and the four canonical modules, then one Lean check containing all 55 axiom reports, exact-original-hypothesis wrappers, and current-file headline restatements. The baseline and contribution `#discharges` rows are compared directly. Because these suppliers live outside `Contrib.OneProof`, merely importing them and seeing no row is not enough; the active restatements test the headlines themselves.

Private evidence bundle available to the maintainer. The historical worked example in CONTRIBUTING is not the baseline. No H103 closing module is imported in this package, and no new H103 or H105 discharge is claimed.

Independent mathematical PASS at `2b5dae91d` is distinct from final fresh-head/documentation reaffirmation. Fresh-head source gates and exact-head reaffirmation are required before review-ready publication; a draft may be published for that review. This file is `CanonicalREADME.md` and does not overwrite PR32's separate `README.md`.
