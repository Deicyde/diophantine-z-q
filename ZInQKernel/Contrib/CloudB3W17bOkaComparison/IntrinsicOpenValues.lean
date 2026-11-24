import ZInQKernel.Contrib.CloudB3W17bOkaComparison.IntrinsicResidueNaturality
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.OpenAnalyticMap

/-!
# Actual intrinsic residue values on a genuine Euclidean Oka-open source

The value is computed from the actual germ-colimit evaluation and the actual
complex constants. No Taylor expansion, Weierstrass theorem, reduced-model
compatibility or additional witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic IsLocalRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- On a genuine Oka-open source, intrinsic evaluation is the actual representative's value. -/
theorem intrinsicEval_open_germ (n : ℕ) (V : Opens (_root_.complexAffineSpace.{0} n))
    (w : euclideanOpen n V) (A : Opens (euclideanOpen n V)) (hw : w ∈ A)
    (s : (euclideanOpen n V).presheaf.obj (op A)) :
    intrinsicStalkEval (euclideanOpen n V) w ((euclideanOpen n V).presheaf.germ A w hw s) =
      OkaRing.evalHom (U := openOkaSectionImage V A) (openOkaMemSectionImage V w A hw) s := by
  let Z := euclideanOpen n V
  let E := openOkaGermEval V w
  let a := Z.presheaf.germ A w hw s
  let c := OkaRing.evalHom (U := openOkaSectionImage V A) (openOkaMemSectionImage V w A hw) s
  let α := Z.toLocallyRingedSpace.stalkAlgMap Z.algebraMap w
  have ha : E a = c := openOkaGermEval_germ V w A hw s
  have hc : E (α c) = c := openOkaGermEval_const V w c
  have hz : E (a - α c) = 0 :=
    (map_sub E a (α c)).trans
      ((congrArg (fun x : ℂ => x - E (α c)) ha).trans
        ((congrArg (fun x : ℂ => c - x) hc).trans (sub_self c)))
  apply (intrinsicStalkEval_eq_iff Z w a c).mpr
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact not_isUnit_zero ((congrArg IsUnit hz).mp (hu.map E))

/-- The genuine section-value map on an Oka-open source is literal holomorphic evaluation. -/
theorem intrinsicEval_open (n : ℕ) (V : Opens (_root_.complexAffineSpace.{0} n))
    (w : euclideanOpen n V) (A : Opens (euclideanOpen n V)) (hw : w ∈ A)
    (s : (euclideanOpen n V).presheaf.obj (op A)) :
    intrinsicEval (euclideanOpen n V) w hw s =
      OkaRing.evalHom (U := openOkaSectionImage V A) (openOkaMemSectionImage V w A hw) s :=
  intrinsicEval_open_germ n V w A hw s

end ZInQ.Contrib.CloudB3W17bOkaComparison
