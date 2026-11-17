# Round-4 primary source verification

The ten primary-retained modules from provider round4 have been recompiled after
recovery on the unchanged Lean4.35.0 / Mathlib56a00585 toolchain. This is a provider
porting checkpoint, not an assertion that the full degree/cardinality root or
Mumford torsion leaf is proved.

Changes retain the original mathematical statements and hypotheses. They adapt
one-based TFAE indices, ENat cardinalities, existing root section scopes, and the
definitionally identical commutative-ring presheaf abbreviation. Scalar actions
and transported module carriers are specified using their original bundled module
data, not substituted group structures. Evaluation and duality proofs use the
source's existing naturality and coordinate arguments. The existing IsIso proofs
are supplied directly to asIso where implicit inference became ambiguous. The
Cartier composition proofs retain the original maps and use explicit existing
functorial isomorphism proofs. No notation, syntax, admission or extra axiom is added.

Successful module compiles were observed separately from failed intermediate
elaborations; no failed elaboration is counted as verified. Complete raw compiler
outputs, current source/cache hashes and replay commands are preserved privately.
The final leaf must still pass its own exact statement, discharge and axiom checks.
