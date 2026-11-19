import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.PointEvaluation
import ZInQKernel.Contrib.RC53Assist.S2aNumberField.IdentityPlace
import ZInQKernel.Contrib.RC53Assist.S2aNumberField.RegularComparison
import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.LocalFacts
import ZInQKernel.HDecomp.Objects

/-!
# Evaluation at the origin of differentials on a one-dimensional abelian variety

Let `B` be an abelian variety over a field `L`, `X` its underlying scheme and `o` its identity
point. The unit section gives the value map `𝒪_{X,o} → L` (`originRetraction`), a retraction of
the constants, so the evaluation of Kähler differentials at a rational point applies:
`originEval : Ω[𝒪_{X,o}/L] → 𝔪_o/𝔪_o²`, `D a ↦ (a - a(o)) mod 𝔪_o²`.

A differential of the function field is regular at the origin if it comes from `Ω[𝒪_{X,o}/L]`
(`regularAtOrigin`). For `dim B = 1` and `L` of characteristic zero the map
`Ω[𝒪_{X,o}/L] → Ω[L(X)/L]` is injective (the local ring is a discrete valuation ring), so a
regular differential has a well-defined value at the origin (`originValue`): the evaluation of
its unique local preimage. No basis of any line is chosen.

Locator: Hartshorne, *Algebraic Geometry*, II.8.7; Silverman, *The Arithmetic of Elliptic
Curves*, second edition, II.4.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open AlgebraicGeometry CategoryTheory KaehlerDifferential IsLocalRing
open ZInQ.Contrib.RC53Assist.S2aNumberField (identityPoint identitySection
  stalkClosedPointTo_identity_constant stalkKaehlerMap stalkKaehlerMap_injective)
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra stalkAlgebra
  stalk_functionField_tower abelian_scheme_integral)

variable {L : Type} [Field L]

/-- DEFINITION. The value at the origin, `𝒪_{X,o} → L`: restriction along the unit section of
`B`. Locator: Mathlib, `Scheme.stalkClosedPointTo`. -/
def originRetraction (B : PkgI3.AbVar L) :
    B.X.left.presheaf.stalk (identityPoint B.X) →+* L :=
  (Scheme.stalkClosedPointTo (identitySection B.X)).hom

/-- THEOREM (proved). The value at the origin of a constant is that constant: the unit section
is a section of the structure morphism. Locator: `stalkClosedPointTo_identity_constant`. -/
theorem originRetraction_algebraMap (B : PkgI3.AbVar L) (c : L) :
    letI := stalkAlgebra B.X.hom (identityPoint B.X)
    originRetraction B (algebraMap L _ c) = c :=
  stalkClosedPointTo_identity_constant B.X c

/-- DEFINITION. Evaluation at the origin of Kähler differentials of the local ring:
`D a ↦ (a - a(o)) mod 𝔪_o²`. Locator: `pointEval`. -/
def originEval (B : PkgI3.AbVar L) :
    letI := stalkAlgebra B.X.hom (identityPoint B.X)
    Ω[B.X.left.presheaf.stalk (identityPoint B.X)⁄L] →ₗ[B.X.left.presheaf.stalk (identityPoint B.X)]
      CotangentSpace (B.X.left.presheaf.stalk (identityPoint B.X)) :=
  letI := stalkAlgebra B.X.hom (identityPoint B.X)
  pointEval (originRetraction B) (originRetraction_algebraMap B)

/-- DEFINITION. The differentials of the function field that are regular at the origin: the image
of `Ω[𝒪_{X,o}/L]`. Locator: `stalkKaehlerMap`. -/
abbrev regularAtOrigin (B : PkgI3.AbVar L) :
    letI := abelian_scheme_integral B.X
    letI := functionFieldAlgebra B.X.hom
    Submodule L Ω[B.X.left.functionField⁄L] :=
  letI := stalkAlgebra B.X.hom (identityPoint B.X)
  haveI := abelian_scheme_integral B.X
  letI := functionFieldAlgebra B.X.hom
  LinearMap.range (stalkKaehlerMap B.X.hom (identityPoint B.X))

/-- THEOREM (proved). The image of a local differential is regular at the origin.
Locator: Mathlib, `LinearMap.mem_range_self`. -/
theorem stalkKaehlerMap_mem_regularAtOrigin (B : PkgI3.AbVar L)
    (ω : letI := stalkAlgebra B.X.hom (identityPoint B.X)
      Ω[B.X.left.presheaf.stalk (identityPoint B.X)⁄L]) :
    letI := stalkAlgebra B.X.hom (identityPoint B.X)
    haveI := abelian_scheme_integral B.X
    stalkKaehlerMap B.X.hom (identityPoint B.X) ω ∈ regularAtOrigin B := by
  letI := stalkAlgebra B.X.hom (identityPoint B.X)
  haveI := abelian_scheme_integral B.X
  letI := functionFieldAlgebra B.X.hom
  exact LinearMap.mem_range_self _ ω

/-- THEOREM (proved). For a one-dimensional abelian variety over a field of characteristic zero,
the Kähler map from the local ring at the origin to the function field is injective. Locator:
`stalkKaehlerMap_injective` with the proved local fact `LocalFacts.localUniformizerBasis`. -/
theorem stalkKaehlerMap_origin_injective [CharZero L] (B : PkgI3.AbVar L) (hdim : B.dim = 1) :
    letI := abelian_scheme_integral B.X
    letI := functionFieldAlgebra B.X.hom
    Function.Injective (stalkKaehlerMap B.X.hom (identityPoint B.X)) := by
  haveI := abelian_scheme_integral B.X
  exact stalkKaehlerMap_injective AbelianCurveInputs.LocalFacts.localUniformizerBasis B.X.hom
    hdim _

/-- DEFINITION. The value at the origin of a differential regular there: the evaluation of its
unique local preimage. Locator: `originEval`, `stalkKaehlerMap_origin_injective`. -/
def originValue [CharZero L] (B : PkgI3.AbVar L) (hdim : B.dim = 1) :
    letI := stalkAlgebra B.X.hom (identityPoint B.X)
    regularAtOrigin B →ₗ[L] CotangentSpace (B.X.left.presheaf.stalk (identityPoint B.X)) :=
  letI := stalkAlgebra B.X.hom (identityPoint B.X)
  haveI := abelian_scheme_integral B.X
  ((originEval B).restrictScalars L).comp
    (LinearEquiv.ofInjective _ (stalkKaehlerMap_origin_injective B hdim)).symm.toLinearMap

/-- THEOREM (proved). The value at the origin of the image of a local differential `ω` is the
evaluation of `ω`. Locator: Mathlib, `LinearEquiv.ofInjective_apply`. -/
theorem originValue_stalkKaehlerMap [CharZero L] (B : PkgI3.AbVar L) (hdim : B.dim = 1)
    (ω : letI := stalkAlgebra B.X.hom (identityPoint B.X)
      Ω[B.X.left.presheaf.stalk (identityPoint B.X)⁄L]) :
    letI := stalkAlgebra B.X.hom (identityPoint B.X)
    haveI := abelian_scheme_integral B.X
    originValue B hdim ⟨stalkKaehlerMap B.X.hom (identityPoint B.X) ω,
      stalkKaehlerMap_mem_regularAtOrigin B ω⟩ = originEval B ω := by
  letI := stalkAlgebra B.X.hom (identityPoint B.X)
  haveI := abelian_scheme_integral B.X
  have h : (⟨stalkKaehlerMap B.X.hom (identityPoint B.X) ω,
      stalkKaehlerMap_mem_regularAtOrigin B ω⟩ : regularAtOrigin B) =
      LinearEquiv.ofInjective _ (stalkKaehlerMap_origin_injective B hdim) ω :=
    Subtype.ext (LinearEquiv.ofInjective_apply _ _).symm
  rw [h]
  change (originEval B) ((LinearEquiv.ofInjective _ (stalkKaehlerMap_origin_injective B hdim)).symm
    (LinearEquiv.ofInjective _ (stalkKaehlerMap_origin_injective B hdim) ω)) = _
  rw [LinearEquiv.symm_apply_apply]

end ZInQ.Contrib.RC53Assist.HodgeLineBinding
