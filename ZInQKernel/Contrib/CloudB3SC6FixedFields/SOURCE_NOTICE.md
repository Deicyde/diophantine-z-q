# Source provenance and modifications

## Reused proof

`GeometricPointDensity.lean` extracts the algebraic-point density and morphism-extensionality
helpers from the Anthropic Fermat's Last Theorem development:

- Repository: https://github.com/anthropics/fermats-last-theorem
- Revision: `6e837e75355538c7f80bab5b956861e86c4eacc2`
- File: `P2M/Sol/S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.lean`
- Source ranges: helpers in lines 20–115, especially `dense_range_of_points` at 53–92 and
  `ext_of_forall_geometric_point` at 94–115.
- Whole source SHA-256: `bfb625cdc43e117f9bd0ec483c3a1dd439b7d7775f390d60728b211866dc591d`.
- Copyright 2026 Anthropic, PBC; Apache License 2.0.

`LICENSE`, `NOTICE`, and `ATTRIBUTION.md` are preserved byte-for-byte from that revision.
The notices describe the upstream repository as a whole; unrelated libraries and files
listed there are not redistributed by this extraction.

## Deliberate changes

- Specialize the domain base to a field. This is sufficient for the rational-base application.
  The generic fibre is then the entire scheme, replacing the source's general flat-domain
  generic-fibre density argument. No unavailable flat-generalizing helper is assumed.
- Isolate all new declarations under `CloudB3SC6FixedFields`.
- Replace the source's local notation by the definition `geometricBaseMap`.
- Import selected Mathlib modules, not the source's `Mathlib` umbrella, Néron carrier wrapper,
  or `P2M.Util`.
- Update `Ideal.bot_prime` to Mathlib 4.35's `Ideal.isPrime_bot`.
- Use the closed-point equivalence's inverse identity directly for the point calculation.
- Spell the final open-set membership as membership in its underlying set.
- Enable `backward.isDefEq.respectTransparency` and its `.types` compatibility options in the
  extracted module. These affect elaboration only; kernel axiom checks are separate.
- Add `exists_geometric_point_mem` as a consequence of the extracted density theorem.

`SectionDetection.lean` is new glue over the extracted density theorem and Mathlib's section,
basic-open, residue-field and generic-stalk APIs. It detects zero/equality of sections and
equality of generic germs from algebraic-point values.

`PointFibreInvariance.lean` is new project glue. It imports the existing Elkies definitions
and proves that point-fibre invariance fixes the coordinate germ. It proves only the
containment `Q(t) ⊆ fixedByW`; it neither assumes the equality nor constructs a moduli witness.
The old function-field-to-fibre proofs are unchanged.

`SignRealization.lean` is new project glue. On the same chart and coarse-witness hypotheses,
`exists_W_with_signs_of_point_fibres` proves that every coordinate-sign pair is realized by a
member of W on the function field. It uses one point fibre with both coordinates nonzero
and reuses the existing constant-sign/chart-action proof. It does not assert a degree bound,
construct a field automorphism enumeration, or assume a fixed-field equality.

## Scope

These are supporting theorems, not a proof of the existential
`ElkiesX6StarFunctionField` field. No existing source or dependency pin is modified. No module
imports `ZInQKernel.OneProof.Main` or defines build-time commands, parser extensions,
notation, macros, evaluators, initialization code, or axioms.

Author and independent-review evidence are supplied privately to the maintainer. A conditional
converse alone must not be folded as an unconditional target discharge or in a way that
increases the glue count.
