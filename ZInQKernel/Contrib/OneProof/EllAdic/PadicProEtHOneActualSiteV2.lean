import ZInQKernel.Contrib.OneProof.EllAdic.PadicProEtHOneCompatibleV1
import ZInQKernel.Contrib.OneProof.EllAdic.ProEtCountableProductsExactV2

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

/-- Once the actual site exactness theorem is available, its instance
supplies the bijectivity of the original, literal cohomology reduction. -/
theorem ellAdicHOne_actualSite_bijective (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    Function.Bijective (ellAdicHOneToCompatibleResidues S p) := by
  let : HasExactLimitsOfShape (Discrete ℕ) (Sheaf (Scheme.ProEt.topology S) Ab.{u+1}) :=
    proEt_countableProducts_exact S
  exact ellAdicHOneToCompatibleResidues_bijective S p

/-- Degree one of the original lifted p-adic sheaf and the group of
compatible finite-degree-one classes on the same small pro-étale site. -/
noncomputable def ellAdicHOne_actualSite_equiv (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    S.EllAdicCohomology p 1 ≃+ ↥(residueHOneSubShift S p).ker :=
  AddEquiv.ofBijective (ellAdicHOneToCompatibleResidues S p) (ellAdicHOne_actualSite_bijective S p)

/-- The equivalence's coordinates remain the maps of the original
coefficient's actual reductions. -/
theorem ellAdicHOne_actualSite_equiv_apply (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (x : S.EllAdicCohomology p 1) (n : ℕ) :
    (ellAdicHOne_actualSite_equiv S p x).1 n =
      Sheaf.H.map ((continuousResidueProEtSheafCone S p).π.app (op n)) 1 x :=
  ellAdicHOneToCompatibleResidues_apply S p x n

end RC53.EllAdic
