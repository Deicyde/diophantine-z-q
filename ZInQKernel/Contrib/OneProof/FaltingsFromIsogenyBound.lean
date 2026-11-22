import ZInQKernel.Contrib.OneProof.TateGeometricSplitting
import ZInQKernel.Contrib.OneProof.AVSplitMorphisms

/-! # Faltings semisimplicity from the uniform isogeny bound -/

noncomputable section
open PkgI3.AbVar
open scoped CategoryTheory.MonObj TensorProduct

namespace ZInQ.Contrib.TateFiniteApproximation

/-- The scalar-extended endomorphism algebra of any abelian variety over a
number field is semisimple. -/
theorem semisimple_endomorphism_algebra {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (E : Type*) [Field E] [CharZero E] :
    IsSemisimpleRing (E ⊗[ℤ] End A) := by
  have h := OneProof.HomFreeC.homFreeFiniteNF uniformizationLeafAll_proof
    CloudB3W16Torsion.mumfordTorsionAlgClosed_proof K A A
  let := h.2.1
  exact semisimple_of_integral_splitting E (AVSplitMorphisms.exists_inner_inverse_up_to_mul A)

/-- Faltings semisimplicity for A at every prime from the Gaudron–Rémond
isogeny bound and a witness to the stable height of A. -/
theorem faltingsSemisimple_at_of_isogeny_bound {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (g : ℕ) (height : ℝ) (hdim : A.dim = (g : WithBot ℕ∞))
    (hheight : ZInQ.SemistabAssembly.IsAnStableHeightSS A height) :
    (A.galRep ℓ).IsSemisimpleRepresentation :=
  faltingsSemisimple_at_of_geometric_splitting A ℓ hGR g height hdim hheight
    (AVSplitMorphisms.exists_inner_inverse_up_to_mul A)

/-- The literal semisimplicity input r9a under the isogeny bound and the
existing Néron, semistable reduction and uniformization height inputs. -/
theorem faltingsSemisimple_of_gaudronRemond
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (hN : ZInQ.H5Neron.NeronModelExists) (hSS : ZInQ.HeightSplit.SemistableReductionThm)
    (hU : ZInQ.LeafPush2.UniformizationExists) (hD : ZInQ.HeightFix.SemiAbelianDescendsPerfect) :
    PkgI3.FaltingsSemisimple := by
  intro K _ _ A ℓ _
  obtain ⟨g, h, hd, hh⟩ := GRUniformQuasiInverse.exists_anStableHeightSS hN hSS hU hD K A
  exact faltingsSemisimple_at_of_isogeny_bound A ℓ hGR g h hd hh

end ZInQ.Contrib.TateFiniteApproximation
