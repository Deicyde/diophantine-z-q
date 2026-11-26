import ZInQKernel.Contrib.OneProof.C8Manuscript.RankOnePeriod
import ZInQKernel.Contrib.OneProof.C8Conrad

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.ZInQ.Contrib.G9
open _root_.ZInQ.Contrib.G9.PkgI4 (GQp BdR bdrAct IsDeRham LocalIsDeRham)
open _root_.ZInQ.Contrib.G9.RankOnePeriod

variable (p : ℕ) [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]
variable (χ : GQp p →* Eˣ)

/-- The full underlying `ℚ_p`-linear representation of the actual coefficient
character is de Rham if it has a nonzero positive-character period over `G_E`,
using a Galois-compatible realization of the coefficients in `B_dR`.
Continuity of the character is not needed by this algebraic rank argument. -/
theorem isDeRham_char_of_period_with_embedding
    (ι : E →ₐ[ℚ_[p]] BdR p)
    (hι : ∀ g x, bdrAct p g (ι x) = ι ((AlgEquiv.restrictNormalHom E) g x))
    (c : BdR p) (hc : c ≠ 0)
    (hperiod : ∀ g ∈ E.fixingSubgroup, bdrAct p g c = ι (χ g : E) * c) :
    IsDeRham p (charRep χ) := by
  refine isDeRham_of_scalar_period p E χ (charRep χ) ?_ ι hι c hc hperiod
  intro g v
  simp [rRep_apply, charRep, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
    Matrix.algebraMap_matrix_apply]

/-- Premise-minimal endpoint using the existing proved period-ring coefficient embedding. -/
theorem isDeRham_char_of_period
    (c : BdR p) (hc : c ≠ 0)
    (hperiod : ∀ g ∈ E.fixingSubgroup,
      bdrAct p g c = transportedIotaDR p E (χ g : E) * c) :
    IsDeRham p (charRep χ) :=
  isDeRham_char_of_period_with_embedding p E χ (transportedIotaDR p E)
    (bdrAct_transportedIotaDR p E) c hc hperiod

/-- Use the same coefficient character as the `LocalIsDeRham` witness for any
local model pointwise equal to its scalar extension. -/
theorem localIsDeRham_char_of_period_on_model
    (ι : E →ₐ[ℚ_[p]] BdR p)
    (hι : ∀ g x, bdrAct p g (ι x) = ι ((AlgEquiv.restrictNormalHom E) g x))
    (c : BdR p) (hc : c ≠ 0)
    (hperiod : ∀ g ∈ E.fixingSubgroup, bdrAct p g c = ι (χ g : E) * c)
    (r : GQp p →* GL (Fin 1) (PadicAlgCl p))
    (hr : ∀ g, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (charRep χ g) = r g) :
    LocalIsDeRham p 1 r :=
  ⟨E, inferInstance, charRep χ, hr,
    isDeRham_char_of_period_with_embedding p E χ ι hι c hc hperiod⟩

/-- The same actual character model supplies `LocalIsDeRham` for its scalar
extension to the algebraic closure. -/
theorem localIsDeRham_char_of_period
    (c : BdR p) (hc : c ≠ 0)
    (hperiod : ∀ g ∈ E.fixingSubgroup,
      bdrAct p g c = transportedIotaDR p E (χ g : E) * c) :
    LocalIsDeRham p 1
      (charRep ((Units.map (algebraMap E (PadicAlgCl p)).toMonoidHom).comp χ)) := by
  refine ⟨E, inferInstance, charRep χ, ?_, isDeRham_char_of_period p E χ c hc hperiod⟩
  intro g
  ext i j
  have he : i = j := Subsingleton.elim i j
  subst j
  simp [charRep, Matrix.algebraMap_matrix_apply]

end HDec.G0Galois.C8Conrad.Manuscript
