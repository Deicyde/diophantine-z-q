import ZInQKernel.Contrib.OneProof.EllAdic.FiniteAbDictionary
import ZInQKernel.Contrib.OneProof.EllAdic.ConstantComparisonRebaseV1
import ZInQKernel.Contrib.OneProof.EllAdic.PadicEtaleHOneGeometryFiniteMapsV1

/-!
# Pullback of integral pro-étale cohomology along a scheme isomorphism

For `σ : S ≅ T`, `ellAdicHOne_rebase σ p : H¹_proet(T, ℤ_p) →+ H¹_proet(S, ℤ_p)` is the degree-one
`Ext` transport along the pro-étale rebase equivalence `proEtAbRebasePullback σ`, with the
constant-sheaf comparison `proEtConstantRebaseIso σ` on the source and the identity-on-sections
coefficient isomorphism `continuousResidueProEtRebaseIso σ p` on the target. This is the same
construction as `proEtResidueHOne_rebase` on the finite residue coefficients, and
`ellAdicHOne_rebase_projection` says the two commute with the cone projections.

This file uses no vendored source.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped RC53.EllAdic.FiniteAbDictionary

namespace RC53.EllAdic

universe u

local instance rebaseProEtEquivalence {S T : Scheme.{u}} (σ : S ≅ T) :
    (proEtAbRebasePullback σ).IsEquivalence :=
  inferInstanceAs (proEtAbRebaseEquivalence σ).functor.IsEquivalence

local instance rebaseProEtAdditive {S T : Scheme.{u}} (σ : S ≅ T) :
    (proEtAbRebasePullback σ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The pullback of integral pro-étale classes along `σ : S ≅ T`. -/
noncomputable def ellAdicHOne_rebase {S T : Scheme.{u}} (σ : S ≅ T) (p : ℕ) [Fact p.Prime] :
    T.EllAdicCohomology p 1 →+ S.EllAdicCohomology p 1 :=
  let z : Ab.{u+1} := FiniteAbDictionary.zCoeff
  extOneTransport (proEtAbRebasePullback σ) ((proEtConstantRebaseIso σ).hom.app z)
    (continuousResidueProEtRebaseIso σ p).hom

/-- The integral pullback commutes with the projections to the finite residue coefficients. -/
theorem ellAdicHOne_rebase_projection {S T : Scheme.{u}} (σ : S ≅ T) (p : ℕ) [Fact p.Prime]
    (n : ℕ) (x : T.EllAdicCohomology p 1) :
    Sheaf.H.map ((continuousResidueProEtSheafCone S p).π.app (op n)) 1
        (ellAdicHOne_rebase σ p x) =
      proEtResidueHOne_rebase σ p n
        (Sheaf.H.map ((continuousResidueProEtSheafCone T p).π.app (op n)) 1 x) :=
  extOneTransport_postcomp (proEtAbRebasePullback σ)
    ((proEtConstantRebaseIso σ).hom.app FiniteAbDictionary.zCoeff)
    (continuousResidueProEtRebaseIso σ p).hom (liftedFiniteResidueProEtRebaseIso σ p n).hom
    ((continuousResidueProEtSheafCone T p).π.app (op n))
    ((continuousResidueProEtSheafCone S p).π.app (op n))
    (continuousResidueProEtRebaseIso_projection σ p n) x

end RC53.EllAdic
