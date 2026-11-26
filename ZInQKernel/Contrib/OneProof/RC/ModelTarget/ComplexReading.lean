import ZInQKernel.Contrib.OneProof.RC.PMWire.Model
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveGroupLaw

/-! The complex point reading of the generic elliptic model, tex 8476–8479.
For any integral model whose generic identification carries the generic group
law to a law on the fixed rational cubic with the chord-and-tangent complex
points, the reading is the coordinate value of `J0Cusps` composed with that
identification. The packaging as a monoid homomorphism is on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve PkgI3
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

open PMWire (complexBase ellipticTarget)
open GoodReduction (generic)
open PreparedParam (projectiveValue)

variable {E₀ : WeierstrassCurve ℚ} [E₀.IsElliptic]

/-- A group law on the fixed rational cubic is the chord-and-tangent law on complex
points when the coordinate value `projectiveValue` turns its products into sums. -/
def IsComplexLaw (g : GrpObj (ellipticTarget E₀)) : Prop :=
  letI := g
  ∀ p q : complexBase ⟶ ellipticTarget E₀,
    projectiveValue (p * q).left = projectiveValue p.left + projectiveValue q.left

/-- The rational scheme law of `J0Cusps.projectiveGroup_exists` is such a law. -/
theorem exists_complexLaw (E₀ : WeierstrassCurve ℚ) [E₀.IsElliptic] :
    ∃ g : GrpObj (ellipticTarget E₀), IsComplexLaw g :=
  J0Cusps.projectiveGroup_exists E₀

/-- The chosen rational chord-and-tangent scheme law on the fixed cubic. -/
@[instance_reducible]
def complexLaw (E₀ : WeierstrassCurve ℚ) [E₀.IsElliptic] : GrpObj (ellipticTarget E₀) :=
  (exists_complexLaw E₀).choose

theorem complexLaw_spec (E₀ : WeierstrassCurve ℚ) [E₀.IsElliptic] :
    IsComplexLaw (complexLaw E₀) :=
  (exists_complexLaw E₀).choose_spec

/-- The coordinate value on complex points of the fixed cubic, as a monoid
homomorphism for any law with complex chord-and-tangent points. -/
def targetReading (g : GrpObj (ellipticTarget E₀)) (hg : IsComplexLaw g) :
    letI := g
    (complexBase ⟶ ellipticTarget E₀) →* Multiplicative (E₀.baseChange ℂ).toAffine.Point :=
  letI := g
  { toFun := fun p => Multiplicative.ofAdd (projectiveValue p.left)
    map_one' := by
      have h := hg 1 1
      rw [one_mul] at h
      exact congrArg Multiplicative.ofAdd (left_eq_add.mp h).symm ▸ rfl
    map_mul' := fun p q => congrArg Multiplicative.ofAdd (hg p q) }

theorem targetReading_apply (g : GrpObj (ellipticTarget E₀)) (hg : IsComplexLaw g)
    (p : complexBase ⟶ ellipticTarget E₀) :
    (targetReading g hg p).toAdd = projectiveValue p.left :=
  rfl

variable {R : Type} [CommRing R] [Algebra R ℚ]

/-- The complex reading of an integral group model `E`. The generic fibre carries
the group law induced by base change. When `jE` is a homomorphism to a law with
complex chord-and-tangent points, the reading of `a` is the coordinate value of
`a ≫ jE.hom`. -/
def readComplex (E : Over (Spec (.of R))) [GrpObj E]
    (jE : (generic R ℚ).obj E ≅ ellipticTarget E₀)
    (g : GrpObj (ellipticTarget E₀)) (hg : IsComplexLaw g)
    (hj : letI := g; IsMonHom jE.hom) :
    (complexBase ⟶ (generic R ℚ).obj E) →* Multiplicative (E₀.baseChange ℂ).toAffine.Point :=
  letI := g
  (targetReading g hg).comp (@IsMonHom.monoidHom _ _ _ _ _ _ _ jE.hom hj complexBase)

theorem readComplex_eq (E : Over (Spec (.of R))) [GrpObj E]
    (jE : (generic R ℚ).obj E ≅ ellipticTarget E₀)
    (g : GrpObj (ellipticTarget E₀)) (hg : IsComplexLaw g)
    (hj : letI := g; IsMonHom jE.hom) (a : complexBase ⟶ (generic R ℚ).obj E) :
    (readComplex E jE g hg hj a).toAdd = projectiveValue (a.left ≫ jE.hom.left) :=
  rfl

#print axioms IsComplexLaw
#print axioms exists_complexLaw
#print axioms complexLaw
#print axioms complexLaw_spec
#print axioms targetReading
#print axioms targetReading_apply
#print axioms readComplex
#print axioms readComplex_eq

end ZInQ.Manuscript.RC.ModelTarget
