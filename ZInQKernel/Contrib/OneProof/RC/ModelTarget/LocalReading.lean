import ZInQKernel.Contrib.OneProof.RC.ModelTarget.ComplexReading
import ZInQKernel.Contrib.OneProof.RC.ModelNeron.LocalExtension
import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron
import ZInQKernel.Contrib.OneProof.NeronDVR.RelativeSquare
import ZInQKernel.Contrib.NeronC.NeronGroup

/-! The complex reading on the local Néron target, tex 8476–8479.
The local existence input of `ModelNeron.LocalExtension` is discharged by the
proved closed term below. The group law on the target is the one transported from
the rational chord-and-tangent law through the Néron mapping property, so the
generic identification is a homomorphism (`NeronC.isMonHom_of_neron`).
The packaging is on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve PkgI3
open WeierstrassCurve.ModelTorsion
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

open PMWire (complexBase ellipticTarget)
open GoodReduction (generic)
open ZInQ.Contrib.NeronC (grpObjOfNeron isMonHom_of_neron smooth_tensor smooth_tensorUnit)

/-- Local existence of Néron models over discrete valuation rings, proved on main:
the Dedekind extension theorem specialized to rings of integers, then localized. -/
theorem neronDVRLocal : NeronExt.NeronDVRLocal :=
  NeronExt.dvrLocal_of_extension
    (ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind
      NeronDVR.neronSchemeExtensionDedekind_proof)

variable (ell : ℕ) [Fact ell.Prime] (E₀ : WeierstrassCurve ℚ) [E₀.IsElliptic]

/-- The local Néron target at the detector, with the proved existence input. -/
abbrev detectorTarget : ModelNeron.LocalTarget ell E₀ :=
  ModelNeron.localTarget (ell := ell) (E₀ := E₀) neronDVRLocal

variable {ell E₀}

omit [E₀.IsElliptic] in
private theorem target_bijective (T : ModelNeron.LocalTarget ell E₀)
    (Y : Over (Spec (.of (LocalIntegers ell)))) (hY : Smooth Y.hom) :
    Function.Bijective fun f : Y ⟶ T.E => (generic (LocalIntegers ell) ℚ).map f ≫ T.jE.hom := by
  have := hY
  have hj : Function.Bijective
      (fun f : (generic (LocalIntegers ell) ℚ).obj Y ⟶ (generic (LocalIntegers ell) ℚ).obj T.E =>
        f ≫ T.jE.hom) :=
    ⟨fun a b h => (cancel_mono T.jE.hom).mp h, fun f => ⟨f ≫ T.jE.inv, by simp⟩⟩
  exact hj.comp (T.neron.2.2.2.2 Y)

/-- The group law on the local Néron model transported from the rational
chord-and-tangent law `complexLaw E₀` by the Néron mapping property. -/
@[instance_reducible]
def neronLaw (T : ModelNeron.LocalTarget ell E₀) : GrpObj T.E :=
  letI := complexLaw E₀
  grpObjOfNeron (generic (LocalIntegers ell) ℚ) (fun Y => Smooth Y.hom)
    (smooth_tensorUnit _) (fun X Y hX hY => smooth_tensor X Y hX hY)
    T.E T.neron.1 (ellipticTarget E₀) T.jE (target_bijective T)

/-- The generic identification is a homomorphism from the base-changed transported
law to the rational chord-and-tangent law. -/
theorem neronLaw_isMonHom (T : ModelNeron.LocalTarget ell E₀) :
    letI := neronLaw T
    letI := complexLaw E₀
    IsMonHom T.jE.hom := by
  let _ := complexLaw E₀
  exact isMonHom_of_neron (generic (LocalIntegers ell) ℚ) (fun Y => Smooth Y.hom)
    (smooth_tensorUnit _) (fun X Y hX hY => smooth_tensor X Y hX hY)
    T.E T.neron.1 (ellipticTarget E₀) T.jE (target_bijective T)

/-- The complex reading of the local Néron target with the transported law. -/
def localReadComplex (T : ModelNeron.LocalTarget ell E₀) :
    letI := neronLaw T
    (complexBase ⟶ (generic (LocalIntegers ell) ℚ).obj T.E) →*
      Multiplicative (E₀.baseChange ℂ).toAffine.Point :=
  letI := neronLaw T
  readComplex T.E T.jE (complexLaw E₀) (complexLaw_spec E₀) (neronLaw_isMonHom T)

theorem localReadComplex_eq (T : ModelNeron.LocalTarget ell E₀)
    (a : complexBase ⟶ (generic (LocalIntegers ell) ℚ).obj T.E) :
    (localReadComplex T a).toAdd = PreparedParam.projectiveValue (a.left ≫ T.jE.hom.left) :=
  rfl

/-- The two fields have exactly the types of `PMWire.GoodRow.readComplex` and
`readComplex_eq` with `E := T.E`, `groupE := neronLaw T`, `jE := T.jE`. -/
theorem localReadComplex_fits (T : ModelNeron.LocalTarget ell E₀) :
    letI := neronLaw T
    ∃ r : (complexBase ⟶ (generic (LocalIntegers ell) ℚ).obj T.E) →*
        Multiplicative (E₀.baseChange ℂ).toAffine.Point,
      ∀ a, (r a).toAdd = PreparedParam.projectiveValue (a.left ≫ T.jE.hom.left) :=
  ⟨localReadComplex T, localReadComplex_eq T⟩

#print axioms neronDVRLocal
#print axioms detectorTarget
#print axioms neronLaw
#print axioms neronLaw_isMonHom
#print axioms localReadComplex
#print axioms localReadComplex_eq
#print axioms localReadComplex_fits

end ZInQ.Manuscript.RC.ModelTarget
