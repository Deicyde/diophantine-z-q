import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.PacketOfLeaves
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.IsGenDescent
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.GeomConnDescent
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.ActionMulCompat
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.TorsionRep
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
namespace Y3Buzzard

/-!
# The level-three moduli target from the printed leaves

Four hypotheses of `y3Packet_of_parts` are discharged here: generator descent
(`isGenDescentFinite`), descent of geometric connectedness (`geomConnLocalOnBase`), the
homomorphism property of the frame action (from the printed leaf `ZeroPreservingIsHom`, used
over a locally noetherian base), and
torsion representability (from the printed leaf `MilneProp207 5`).
-/

theorem isGenDescentFin3 : IsGenDescentFin3 :=
  fun S A T T' f P h1 h2 h3 h4 => isGenDescentFinite 3 S A T T' f P h1 h2 h3 h4

/-- `Y3RouteA.Y3FullThreeRepZ30` from the printed leaves it uses. -/
theorem y3FullThreeRepZ30_of_printed (hB1 : BuzzardThm21Cor23V15')
    (hB23 : BuzzardFrameRepNS 3) (hB25 : BuzzardFrameRepTorsor 5)
    (hB3 : SerreRigidityLevel3') (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hCI : DescentClosedImmersion) (hM : MilneProp207 5) (hP : ProperLocalOnBase) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_packet
    (y3Packet_of_parts hB1 hB23 hB25 hB3 hB6 hB7b hCI (torsionRep5_of_milne hM)
      properMonoIsClosedImmersion hP geomConnLocalOnBase isGenDescentFin3
      (actionMulCompatLN_of_B4 hB4))

/-- The same, from the bundle of printed leaves. -/
theorem y3FullThreeRepZ30_of_printed_leaves (hL : Y3PrintedLeaves) (hM : MilneProp207 5)
    (hP : ProperLocalOnBase) :
    Y3RouteA.Y3FullThreeRepZ30 := by
  obtain ⟨hB1, hB23, hB25, hB3, hB4, hB6, -, hB7b, -, -, hCI⟩ := hL
  exact y3FullThreeRepZ30_of_printed hB1 (frameRepNS_of_rep (frameRep_of_torsor hB23)) hB25 hB3
    (zeroPreservingIsHomLN_of hB4) hB6 (descentSmoothRelDimFiniteEtale_of_general hB7b) hCI hM hP

end Y3Buzzard
