import ZInQKernel.Contrib.CloudB3W17bAnalyticIdeal.ClosedEmbeddingLocus
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.PullbackCoherent
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.GAGA.ClosedImmersionCoherent
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.GAGA.ClosedImmersion

/-!
# The identity ideal pulled back through an analytic morphism: coherence and vanishing locus

For an algebraic closed immersion `e : P ⟶ B` of schemes locally of finite type over `ℂ` (for
instance the identity section of a separated group scheme) and an analytic morphism
`H : X ⟶ B^an` from a complex analytic space, the inverse image under `H` of the ideal of `e^an`
is a coherent ideal of `𝒪_X` whose vanishing locus is `H⁻¹(range e^an)`.
`H` is an arbitrary morphism of locally ringed spaces out of the analytic space `X`; nothing about
it being algebraic is assumed.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Topology ComplexAnalytic

universe u

namespace ZInQ.Contrib.CloudB3W17bAnalyticIdeal

/-- **The inverse-image ideal of a coherent ideal along a morphism out of an analytic space is
coherent.** Uses the canonical pullback coherence, Oka's theorem for `𝒪_X` and image stability. -/
theorem isCoherent_invImageIdeal {X : AnalyticSpace.{u}} {Y : LocallyRingedSpace.{u}}
    (H : X.toLocallyRingedSpace ⟶ Y) {J : SheafOfModules.{u} Y.ringSheaf} [J.IsCoherent]
    (ιJ : J ⟶ SheafOfModules.unit Y.ringSheaf) : (invImageIdeal H ιJ).IsCoherent := by
  have : (H.pullbackModules.obj J).IsCoherent :=
    ComplexAnalytic.isCoherent_pullbackModules_of_isCoherent H J
  have : (SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf).IsCoherent :=
    X.isCoherentStructureSheaf
  exact SheafOfModules.IsCoherent.image_of_isFiniteType _

/-- **The ideal of the analytification of a closed immersion is coherent.** -/
theorem isCoherent_closedIdeal_analytification {Zs Xs : SchemeLFTℂ.{u}} (i : Zs ⟶ Xs)
    [IsClosedImmersion i.hom.left] :
    (closedIdeal (analytification.map i).toLRSHom).IsCoherent := by
  have : (SheafOfModules.unit
      (analytification.obj Xs).toLocallyRingedSpace.ringSheaf).IsCoherent :=
    (analytification.obj Xs).isCoherentStructureSheaf
  have : (SheafOfModules.unit
      (analytification.obj Zs).toLocallyRingedSpace.ringSheaf).IsCoherent :=
    (analytification.obj Zs).isCoherentStructureSheaf
  have := isCoherent_pushforward_analytification_map i
    (SheafOfModules.unit (analytification.obj Zs).toLocallyRingedSpace.ringSheaf)
  exact SheafOfModules.IsCoherent.kernel _

variable {X : AnalyticSpace.{u}} {Ps Bs : SchemeLFTℂ.{u}} (e : Ps ⟶ Bs)
  [IsClosedImmersion e.hom.left]
  (H : X.toLocallyRingedSpace ⟶ (analytification.obj Bs).toLocallyRingedSpace)

/-- **The ideal of the closed immersion `e` (e.g. the identity section) pulled back through the
analytic morphism `H`.** -/
noncomputable abbrev pulledIdeal : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf :=
  invImageIdeal H (closedIdealι (analytification.map e).toLRSHom)

/-- **It is coherent.** -/
theorem isCoherent_pulledIdeal : (pulledIdeal e H).IsCoherent := by
  have := isCoherent_closedIdeal_analytification e
  exact isCoherent_invImageIdeal H _

/-- **Its vanishing locus is `H⁻¹` of the image of `e^an`.** -/
theorem vanishingLocus_pulledIdeal :
    vanishingLocus (invImageIdealι H (closedIdealι (analytification.map e).toLRSHom)) =
      H.base ⁻¹' Set.range (analytification.map e).toLRSHom.base := by
  rw [vanishingLocus_invImageIdeal, vanishingLocus_closedIdeal _
    (isClosedEmbedding_analytification_map e)]

end ZInQ.Contrib.CloudB3W17bAnalyticIdeal
