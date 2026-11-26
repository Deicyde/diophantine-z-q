import ZInQKernel.Contrib.CloudR2NOS.Valuation.Conjugacy
import ZInQKernel.HDecomp.A6.Extend

/-! A valued-field step used in the proof of SGA 7 I, Exp. IX, Théorème 3.6. Locator UNVERIFIED:
no reading of the SGA 7 original is on record (the page is not given). The proof takes `F` to be
the normal closure of `E`. -/

namespace SZRaynaud

open ZInQ.Contrib.CloudR2NOS.Valuation

/-- A finite separable valued extension embeds into a single finite Galois field over
all prolongations of the base valuation. The embedding may depend on the prolongation. -/
theorem exists_finiteGalois_forall_prolongation_embedding
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (O : ValuationSubring K) (W : ValuationSubring E) (hW : W.comap (algebraMap K E) = O) :
    ∃ F : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K F ∧ IsGalois K F ∧
        (∀ V : ValuationSubring F, V.comap (algebraMap K F) = O →
          ∃ i : E →ₐ[K] F, V.comap i.toRingHom = W) := by
  let F := IntermediateField.normalClosure K E (AlgebraicClosure K)
  let j : E →ₐ[K] F := (normalClosure.algHomEquiv K E _).symm
    (IsAlgClosed.lift : E →ₐ[K] AlgebraicClosure K)
  let _ : Algebra E F := j.toRingHom.toAlgebra
  obtain ⟨V₀, hV₀⟩ := GlueA6Alg.exists_valuationSubring_comap_eq (L := F) W
  change V₀.comap j.toRingHom = W at hV₀
  have hcomp : j.toRingHom.comp (algebraMap K E) = algebraMap K F :=
    RingHom.ext fun x => j.commutes x
  have hV₀O : V₀.comap (algebraMap K F) = O := by
    rw [← hcomp, ← ValuationSubring.comap_comap, hV₀, hW]
  refine ⟨F, inferInstance, inferInstance, fun V hV => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_algEquiv_forall_mem_iff_of_isGalois O V₀ V
    (fun x => by change x ∈ V₀.comap _ ↔ x ∈ O; rw [hV₀O])
    (fun x => by change x ∈ V.comap _ ↔ x ∈ O; rw [hV])
  refine ⟨σ.toAlgHom.comp j, ?_⟩
  ext x
  change σ (j x) ∈ V ↔ x ∈ W
  rw [hσ]
  change x ∈ V₀.comap j.toRingHom ↔ x ∈ W
  rw [hV₀]

end SZRaynaud
