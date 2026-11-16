# X6 quotient fixed-field converse

The target is the unchanged proposition
`HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField`.

The existing development proves the implication from its fixed-field clause to
`ElkiesX6StarPrinted`, the point-fibre form. The converse is not supplied there.
This contribution investigates the converse on the same moduli witness:

1. Detect sections and rational functions using their values on algebraic points
   of a reduced scheme of finite type over the rational numbers.
2. Use the point-fibre clause to show that the Atkin–Lehner automorphisms fix the
   coordinate, and use the two quadratic chart relations to determine their
   action on the other generators.
3. Recover the fixed field from the resulting four sign changes.

Only new supporting files are added. The fine-moduli construction, target
statements, existing modules, and dependency pins remain untouched.

A proof of a conditional converse is not an unconditional proof of the target.
In particular, the existence of its fine-moduli witness, canonical coarse curve,
coordinate and CM normalization must not be treated as consequences of an
abstract fixed-field lemma. No target discharge is claimed in this scaffold.

Base: `0caafe66103a89994198e26d8d68af6ae227ed0e`.
AI-assisted mathematical and Lean development. Private evidence bundle
available to the maintainer.
