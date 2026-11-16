# X6 quotient fixed-field converse

The target is the unchanged proposition
`HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField`.

The existing development proves the implication from its fixed-field clause to
`ElkiesX6StarPrinted`, the point-fibre form. The converse is not supplied there.
This contribution adds checked supporting proofs on the same moduli objects:

- Algebraic-closure points detect morphisms, sections and generic germs over a
  field, reusing a proof from the pinned Anthropic Fermat development.
- The point-fibre clause forces invariance of the coordinate germ and proves
  `Q(t) ⊆ fixedByW` without assuming fixed-field equality.
- A complete list of distinct automorphisms of a finite extension, together
  with the matching degree bound, determines its fixed field. The four-action
  specialization is ready for the X6 application.

The concrete four sign actions and degree bound, and hence the reverse
containment and full conditional converse, remain separate obligations.
`ZInQKernel.Contrib.OneProof.X6FixedFieldSupport` is the build/check entry point.

Only new supporting files are added. The fine-moduli construction, target
statements, existing modules, and dependency pins remain untouched.

A proof of a conditional converse is not an unconditional proof of the target.
In particular, the existence of its fine-moduli witness, canonical coarse curve,
coordinate and CM normalization must not be treated as consequences of an
abstract fixed-field lemma. No target discharge is claimed by this support.

Base: `0caafe66103a89994198e26d8d68af6ae227ed0e`.
AI-assisted mathematical and Lean development. Private evidence bundle
available to the maintainer.
