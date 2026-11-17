/-
Adapted from AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b.
Original source: StacksFrontier/FieldTheory/PerfectClosure.lean
Apache-2.0; upstream licence and source credits are preserved.
Compatibility: import paths remapped; metadata-only Stacks/SGA/EGA attributes omitted.
Mathematical declarations and proofs otherwise unchanged at initial port.
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# The perfect closure of a field

Stacks 046X names the purely inseparable extension of Stacks 046W the *perfect closure* of `k`,
written `k^perf`. Mathlib has it as `perfectClosure k E`, the largest purely inseparable
subextension of `E/k` — maximal by `le_perfectClosure_iff` — which for `E` an algebraic closure
of `k` is the tag's field, perfect by `perfectClosure.perfectField`.

Note that Mathlib's unrelated `PerfectClosure k p` is the perfection of `k`, a colimit of copies
of `k` along the Frobenius, and not this object.
-/

@[expose] public section

-- Metadata-only upstream add_to_stacks commands are omitted from this proof port.
