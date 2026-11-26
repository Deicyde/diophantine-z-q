import ZInQKernel.Contrib.OneProof.RC.ModelNeron.GoodRow
import ZInQKernel.Contrib.OneProof.RC.ModelNeron.LocalTarget

/-! Extend the fixed parametrization into the local Néron target, tex 8478–8479.
The application to the pinned generic open is on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open WeierstrassCurve.ModelTorsion WeierstrassCurve.ModelLevels
  WeierstrassCurve.ModelLevels.ModelGeneric2

namespace ZInQ.Manuscript.RC.ModelNeron

open PMWire (rationalSource ellipticTarget)
open GoodReduction (generic)

set_option autoImplicit false

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N]
  (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)
  {E₀ : WeierstrassCurve ℚ} [E₀.IsElliptic]
  (π : rationalSource N ⟶ ellipticTarget E₀)
  (hloc : NeronExt.NeronDVRLocal)

/-- The target at the detector, with its Néron property and fixed generic identification. -/
def localTarget : LocalTarget ell E₀ :=
  Classical.choice (nonempty_localTarget ell hloc E₀)

/-- The Néron extension of the fixed parametrization on the actual pinned model. -/
def localπInt : Pinned.Y0Level h₅ htame h₂ ⟶ (localTarget (ell := ell) (E₀ := E₀) hloc).E :=
  let T := localTarget (ell := ell) (E₀ := E₀) hloc
  πInt h₅ htame h₂ π T.neron T.jE

theorem local_hInt :
    (generic (LocalIntegers ell) ℚ).map (localπInt h₅ htame h₂ π hloc) =
      (source h₅ htame h₂).jX ≫ (π ≫ (localTarget (ell := ell) (E₀ := E₀) hloc).jE.inv) :=
  let T := localTarget (ell := ell) (E₀ := E₀) hloc
  hInt h₅ htame h₂ π T.neron T.jE

theorem local_hInt_target :
    ((generic (LocalIntegers ell) ℚ).map (localπInt h₅ htame h₂ π hloc) ≫
      (localTarget (ell := ell) (E₀ := E₀) hloc).jE.hom).left =
        (genericIso h₅ htame h₂).hom.left ≫ restrictParametrization h₂ π.left :=
  let T := localTarget (ell := ell) (E₀ := E₀) hloc
  hInt_target h₅ htame h₂ π T.neron T.jE

#print axioms localTarget
#print axioms localπInt
#print axioms local_hInt
#print axioms local_hInt_target

end ZInQ.Manuscript.RC.ModelNeron
