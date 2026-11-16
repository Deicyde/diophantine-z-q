import ZInQKernel.HDecomp.QM.Structures
import ZInQKernel.Contrib.OneProof.Y3FineModuli.CharZeroTrace

/-!
# Y3 fine-moduli witness prerequisites: actual characteristic-zero tangent trace

The exported proof is
`ZInQ.Contrib.OneProof.Y3FineModuli.literal_order_charZero_tangent_trace`.
It uses the literal `LeafQM.O`, actual scheme morphisms and dual-number tangent
points. The finite two-dimensional tangent model and order operators are derived
from the full source-style hypotheses, not supplied as a trace or derivative
assumption.

This partial contribution does **not** prove
`LeafQM.AV.R1UnivRigid.R1fpAb`. It supplies no moduli scheme, `PtEquiv`, universal
family, classification on proper curves, geometric nonemptiness, or inverse
level-3 generation/full-torsion bridge. It does not restate or discharge an open
field and does not re-prove the separate maximal-order/ramification suppliers.
The defining modules are imported, not `ZInQKernel.OneProof.Main`.
-/
