import ZInQKernel.Contrib.OneProof.EllAdic.ProEtAffineCoverageV1
import ZInQKernel.Contrib.OneProof.EllAdic.ProEtAffineProductCoverV2
import ZInQKernel.Contrib.OneProof.EllAdic.CountableProductsExactOfEpiV2

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

/-- Countable products of epimorphisms of actual small pro-étale abelian
sheaves are epimorphisms, by lifting sections over affine open restrictions. -/
theorem proEt_piMap_epi (S : Scheme.{u})
    {F G : ℕ → Sheaf (Scheme.ProEt.topology S) Ab.{u+1}}
    (f : ∀ n, F n ⟶ G n) (hf : ∀ n, Epi (f n)) : Epi (Limits.Pi.map f) := by
  let J := Scheme.ProEt.topology S
  let : Sheaf.IsLocallySurjective (Limits.Pi.map f) :=
    { imageSieve_mem := by
        intro U y
        let R := Presheaf.imageSieve (Limits.Pi.map f).hom y
        apply (Scheme.ProEt.mem_topology_iff_affine_sources U R).2
        intro V g hV
        let : IsAffine V.left := hV
        have hr : R.pullback g = Presheaf.imageSieve (Limits.Pi.map f).hom
            ((∏ᶜ G).obj.map g.op y) := Presheaf.pullback_imageSieve _ y g
        exact hr.symm ▸ proEt_affine_piMap_imageSieve_covers V f ((∏ᶜ G).obj.map g.op y) hf }
  infer_instance

/-- The required exactness is for the actual countable limit functor on the
same lifted abelian sheaf category used in `Scheme.EllAdicCohomology`. -/
theorem proEt_countableProducts_exact (S : Scheme.{u}) :
    HasExactLimitsOfShape (Discrete ℕ) (Sheaf (Scheme.ProEt.topology S) Ab.{u+1}) :=
  countableProductsExact_of_piMap_epi (C := Sheaf (Scheme.ProEt.topology S) Ab.{u+1})
    (fun f hf => proEt_piMap_epi S f hf)

end RC53.EllAdic
