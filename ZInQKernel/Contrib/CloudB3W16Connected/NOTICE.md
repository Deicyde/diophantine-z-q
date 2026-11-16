# Source reuse: Cloud batch 3 Worker16 H-99

This family ports selected mathematical proof sources from
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) at exactly
`c496df0d9beea9deaeabcea8492605f9a0a2313b`, with Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` and Lean 4.35.0.
The complete upstream Apache-2.0 license is reproduced in `LICENSE`.
That file was compared byte-for-byte with the pinned upstream `LICENSE`.
The pinned upstream tree has no tracked NOTICE file. Source prose, references,
and the predecessor's original-hash/vendoring notices are retained in the ports.

## Recovery and attribution

The recovered H99-H150 V3a-v1 packet's
`sources/canonical/ZInQKernel/Contrib/CloudR2CharPoly` supplied the actual Lean
source, not predecessor binary artifacts. Its vendoring notices identify the
original Stacks modules and hashes. `SOURCE_MANIFEST.json` records the recovered
source hashes and per-module modifications. The source cone was checked against
existing `MulEtale`, `CloudW01Spread` and `TauCeti` declarations before porting;
none of the connectedness declarations needed here were provided there.
Existing Mathlib declarations and instances are reused through imports.

The exact leaf in `../OneProof/GeomConnOfRationalPoint.lean` reuses the three-line
proof in the packet's `sources/owned/RationalPoint.lean`, preserving the original
rational section and its equation. It applies
`AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section`.
The theorem is the rational-point consequence of Stacks Tag 04KV (Varieties,
Lemma 33.7.14); the declaration in `OneProof/H/TailP.lean` is not changed.

## Deliberate pruning and adaptation

- Only the rational-section consequence of `ConnectedPoint` is retained. Its
  unused general residue-field criterion, `IsAlgClosedIn`, algebraic-closure and
  geometrically-irreducible/Tower dependencies are not ported.
- The separable-closure equivalence uses the recovered arbitrary-field-base-change
  and separably-closed-base equivalences directly. This removes the unused
  finite-separable-level and quasi-compact-open scheme-descent modules.
- Over a separably closed base, geometric connectedness of a field extension
  follows directly from the recovered tensor-product connectedness theorem.
  Ring finite-separable criteria, the extra prime-spectrum topology module,
  and the ring filtered-union/colimit/bijection results are not needed.
- `TensorProduct/Connected` retains only connectedness of a tensor product over a
  separably closed field, not the unused idempotent/connected-components bijection
  or tensor-product-map injectivity helper.
- Import paths are adapted to this owned supporting family. Broad unrelated
  Mathlib imports in the algebra definitions/tensor module are narrowed to the
  mathematical dependencies used in those proofs.
- Upstream `stacks`, `ega` and `sga` citation attributes, `add_to_stacks` metadata
  commands, and their registration imports are omitted. Mathematical references
  remain in the source prose. No attribute registration, new syntax, notation,
  macro, elaborator, initialization or build-time executable command is added.
- The predecessor's explicit type-inference options are retained. Proof/API
  compatibility repairs, if needed, are part of this port, not changes to the
  theorem's assumptions or to any existing module.

This is H-99 only. No H-98, H-100, H-102 or H-150 theorem is claimed here.
