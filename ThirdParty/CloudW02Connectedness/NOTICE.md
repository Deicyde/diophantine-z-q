# Zariski connectedness: source and port notice

The contribution targets only H-67, the exact fixed proposition
`ZariskiConn.ZariskiConnectedness` from project revision
`cba8157f7d5d09a4a3c8462aba2f3245494a870e`. The working branch was synchronized to
`f70ec251fd4bca6ae3115741c21fe661e7aaac3e` at the owner's request. The target,
its vendored Tau Ceti inputs, and the project's pins were verified byte-identical.

## Reused proof

The affine-noetherian input comes from
[Anthropic's Fermat's Last Theorem formalization](https://github.com/anthropics/fermats-last-theorem),
immutable source revision `6e837e75355538c7f80bab5b956861e86c4eacc2`:

- Module:
  `P2M.Sol.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop`.
- Declaration:
  `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop.solution`.
- Statement: for a proper `f : X ⟶ Spec A` with `A` noetherian, bijectivity of
  `f.appTop` implies `GeometricallyConnected f`, including fibre nonemptiness.

The complete code-import closure of this proof is vendored: 135 Lean modules,
1,178,538 upstream source bytes. `Vendor/AnthropicFLT/SOURCE_MANIFEST.json` records
all original module names, immutable URLs, Git blob hashes, and relocated names.
Every selected original source was verified against immutable Git blob/size metadata.

The source was built against Lean 4.33.1 / Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. This port uses the project's unchanged
Lean 4.35.0 / Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Modifications

- Imports of selected source modules are relocated under
  `ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT`.
- Original declaration namespaces are retained.
- In files where needed, backward elaboration transparency options restore the
  older source's proof-elaboration behavior under Lean 4.35.
- Proof-only API changes update coefficient evaluation to the polynomial-first
  API, rename injective `Finsupp.mapDomain_apply` uses, and adapt tactic sequencing
  where a rewrite now closes a goal without a trailing tactic.
- Source mathematical definitions and claims are preserved. Coefficient notation
  is adapted, not weakened. No target definition, hypothesis, project pin, root
  configuration, or other worker branch is changed.
- `Basic.lean` adds affine-target isomorphism transport and Zariski-local
  restriction to connect the affine input to the fixed project proposition.

Per-file origin/change notices identify all copied files and proof adaptations.
The complete unchanged upstream `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are
preserved as `Vendor/AnthropicFLT/LICENSE`, `NOTICE.upstream`, and
`ATTRIBUTION.upstream.md`. Upstream attribution includes material credited to the
Imperial FLT project, flt-regular, and Mathlib; it has not been abbreviated here.

## Alternate source route inspected

AxiomMath/Stacks at `c496df0d9beea9deaeabcea8492605f9a0a2313b` provides the general
Stein-factorization connectedness theorem and the noetherian formal-functions
idempotent-extension input, on the project's exact Lean/Mathlib pins. The latter's
source import closure has 3,702 modules / 57,637,708 bytes. The smaller exact FLT
proof was selected for this contribution; no W1 Stacks declaration copy is included.

## Verification contract

The named module is `ZInQKernel.Contrib.CloudW02Connectedness.Basic`; the required
closed declaration is `ZariskiConn.ZariskiConnectedness_proof`. Acceptance requires
a successful named-module build and kernel `#print axioms` output containing only
`propext`, `Classical.choice`, and `Quot.sound`. A lexical source audit alone is not
claimed as proof completion. The worker report records the actual build outcomes.
