import ZInQKernel.Contrib.OneProof.EllAdic.AxiomStacksFiniteHOneV1
import ZInQKernel.Contrib.OneProof.EllAdic.PadicEtaleHOneAssemblyV2

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

local instance actualEtaleEtaleSheafification (S : Scheme.{u}) :
    HasSheafify S.smallEtaleTopology Ab.{u+1} := Scheme.hasSheafify_smallEtaleTopology.{u, 0} S

local instance actualEtaleProEtSheafification (S : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology S) Ab.{u+1} := ProEtale.hasSheafify_proetale.{u, 0} S

local instance actualEtaleFinalGroth (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) := by
  let : EssentiallySmall.{u+1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall S.smallEtaleTopology Ab.{u+1}

local instance actualEtaleFinalExt (S : Scheme.{u}) :
    HasExt.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) :=
  IsGrothendieckAbelian.hasExt (Sheaf S.smallEtaleTopology Ab.{u+1})

/-- The compatible-family equivalence supplied by the actual finite comparison. -/
noncomputable def etaleResidueHOneCompatibleEquiv (S : Scheme.{u}) (p : ℕ) :
    ↥(etaleResidueHOneSubShift S p).ker ≃+ ↥(residueHOneSubShift S p).ker :=
  etaleResidueHOneCompatibleEquiv_of_bijective S p (smallEtaleResidueHOneForward_bijective S p)

/-- Integral pro-étale degree one, compared with the actual compatible étale classes. -/
noncomputable def ellAdicHOne_actualEtale_equiv (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    S.EllAdicCohomology p 1 ≃+ ↥(etaleResidueHOneSubShift S p).ker :=
  ellAdicHOne_actualEtale_equiv_of_bijective S p (smallEtaleResidueHOneForward_bijective S p)

/-- Pulling back the finite coordinate is exactly the original cohomology reduction. -/
theorem ellAdicHOne_actualEtale_equiv_apply (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (x : S.EllAdicCohomology p 1) (n : ℕ) :
    smallEtaleResidueHOneForward S p n ((ellAdicHOne_actualEtale_equiv S p x).1 n) =
      Sheaf.H.map ((continuousResidueProEtSheafCone S p).π.app (op n)) 1 x :=
  ellAdicHOne_actualEtale_equiv_apply_of_bijective S p (smallEtaleResidueHOneForward_bijective S p) x n

end RC53.EllAdic
