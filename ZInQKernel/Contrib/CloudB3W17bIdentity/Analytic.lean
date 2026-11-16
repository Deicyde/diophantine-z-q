import ZInQKernel.Contrib.CloudB3W17bIdentity.Section
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.GAGA.ClosedImmersion

/-!
# The analytic image of the actual identity section

Using only Oka's proved description of the image of the analytification of a closed immersion
(`ComplexAnalytic.range_analytification_map_of_isClosedImmersion`), the image of `e_B^an` in
`B^an` is exactly the fibre of the comparison morphism `π_B : B^an ⟶ B` over the original
identity point. No point model, point dictionary, algebraicity or GAGA input is used.
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic MonoidalCategory MonObj
open ZInQ.Contrib.CloudB3W17bProjectiveBridge

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bIdentity

/-- **The image of `e_B^an` is the `π_B`-fibre over the original identity point.** -/
theorem range_analytification_identitySection (B : PkgI3.AbVar ℂ) :
    Set.range (analytification.map (identitySection B)).toLRSHom.base =
      (analytificationπLRS (abVarLiftedLFT B)).base ⁻¹' {identityPoint B} := by
  rw [range_analytification_map_of_isClosedImmersion, range_identitySection]

/-- Membership form: an analytic point lies in the image of `e_B^an` iff `π_B` sends it to the
point of the kernel's identity element `1 ∈ CPts B id`. -/
theorem mem_range_analytification_identitySection_iff (B : PkgI3.AbVar ℂ)
    (x : analytification.obj (abVarLiftedLFT B)) :
    x ∈ Set.range (analytification.map (identitySection B)).toLRSHom.base ↔
      (analytificationπLRS (abVarLiftedLFT B)).base x =
        (1 : ZInQ.LeafPush2.CPts B (RingHom.id ℂ)).left (IsLocalRing.closedPoint ℂ) := by
  rw [range_analytification_identitySection, cpts_one_left_closedPoint]
  rfl

/-- **`e_B^an` is a closed embedding** of underlying spaces. -/
theorem isClosedEmbedding_analytification_identitySection (B : PkgI3.AbVar ℂ) :
    Topology.IsClosedEmbedding (analytification.map (identitySection B)).toLRSHom.base :=
  isClosedEmbedding_analytification_map (identitySection B)

end ZInQ.Contrib.CloudB3W17bIdentity
