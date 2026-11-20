import ZInQKernel.Contrib.OneProof.RC.PMWire.Generic
import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Model
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelJacobian
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Consumer

/-! The single smooth source and Néron extension for tex 8476–8492.
Only the supersingular evaluations and the elliptic translation are used.
The reduction and specialization diagrams are on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve CartesianMonoidalCategory PkgI3
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 350000

namespace ZInQ.Manuscript.RC.PMWire

open GoodReduction (generic)
open PMQuotient (residueSource residueFrob residueUnit)
open PreparedParam Stages

abbrev ellipticTarget (E : WeierstrassCurve ℚ) : Over (Spec (.of ℚ)) :=
  Over.mk (projectiveOverQ E)

abbrev complexBase : Over (Spec (.of ℚ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))

/-- Data from a smooth separated modular model and the good elliptic
model at the detector. Its coarse point readings need no cusp on the
source. The Atkin–Lehner existence and specialization are part of the
moduli construction; see `ExtendsAtkin`. -/
structure GoodRow (R : Type) [CommRing R] [Algebra R ℚ]
    (ell N : ℕ) [Fact ell.Prime] [NeZero N]
    (K : Type) [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    (Ebar : WeierstrassCurve (ZMod ell)) (X : PMAdelic.CoarseFibre)
    {E₀ : WeierstrassCurve ℚ} [E₀.IsElliptic] (π : rationalSource N ⟶ ellipticTarget E₀) where
  closed : R →+* ZMod ell
  M : Over (Spec (.of R))
  [smoothM : Smooth M.hom]
  [reducedM : IsReduced M.left]
  [separatedM : IsSeparated M.hom]
  [denseGeneric : IsDominant (genericProjection M)]
  source : GenericSource ((generic R ℚ).obj M) N
  E : Over (Spec (.of R))
  [groupE : GrpObj E]
  neron : CToPrinted.IsNeronModelOver R ℚ E
  jE : (generic R ℚ).obj E ≅ ellipticTarget E₀
  [properGenericE : IsProper ((generic R ℚ).obj E).hom]
  [geomIntGenericE : GeometricallyIntegral ((generic R ℚ).obj E).hom]
  /-- The complex group law of the generic elliptic model in Weierstrass coordinates. -/
  readComplex : (complexBase ⟶ (generic R ℚ).obj E) →*
    Multiplicative (E₀.baseChange ℂ).toAffine.Point
  readComplex_eq : ∀ a, (readComplex a).toAdd = projectiveValue (a.left ≫ jE.hom.left)
  point : X.Point →
    (residueSource ell K ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom closed))).obj M)
  extension : ∀ q : ℕ, q.Prime → 0 < N.factorization q →
    ∃ W : M ⟶ M, ExtendsAtkin source q W
  point_W : ∀ q hq he x, point (X.W q x) = point x ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom closed))).map (extension q hq he).choose
  read : (residueSource ell K ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom closed))).obj E) ≃*
    Multiplicative (Ebar.baseChange K).toAffine.Point
  read_frob : ∀ y, (read (residueFrob ell K ≫ y)).toAdd = curveFrob (K := K) Ebar (read y).toAdd
  point_frob : ∀ x, point (X.frobenius x) = residueFrob ell K ≫ point x
  frobenius_sq : Function.Involutive X.frobenius

attribute [instance] GoodRow.smoothM GoodRow.reducedM GoodRow.separatedM GoodRow.denseGeneric
  GoodRow.groupE GoodRow.properGenericE GoodRow.geomIntGenericE

namespace GoodRow

variable {R : Type} [CommRing R] [Algebra R ℚ]
  {ell N : ℕ} [Fact ell.Prime] [NeZero N] {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
  {Ebar : WeierstrassCurve (ZMod ell)} {X : PMAdelic.CoarseFibre}
  {E₀ : WeierstrassCurve ℚ} [E₀.IsElliptic] {π : rationalSource N ⟶ ellipticTarget E₀}
  (G : GoodRow R ell N K Ebar X π)

abbrev jX := G.source.jX

abbrev special := Over.pullback (Spec.map (CommRingCat.ofHom G.closed))

abbrev genericE := (generic R ℚ).obj G.E

/-- The generic elliptic curve with the group law inherited from the integral model. -/
def abVar : AbVar ℚ where
  X := G.genericE
  smooth := by
    have := G.neron.1
    change Smooth (pullback.snd G.E.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    infer_instance

/-- The integral Atkin–Lehner operator is the unique extension of the rational one. -/
def W (q : ℕ) (hq : q.Prime) (he : 0 < N.factorization q) : G.M ⟶ G.M :=
  (G.extension q hq he).choose

theorem W_generic (q : ℕ) (hq : q.Prime) (he : 0 < N.factorization q) :
    (generic R ℚ).map (G.W q hq he) ≫ G.jX = G.jX ≫ rationalW N q :=
  (G.extension q hq he).choose_spec

/-- The map on the fixed rational source, with the generic elliptic model as target. -/
def φ : rationalSource N ⟶ G.genericE := π ≫ G.jE.inv

/-- The very same Néron extension as in the proper case of PMQuotient. -/
def πInt : G.M ⟶ G.E :=
  ((G.neron.2.2.2.2 G.M).surjective (G.jX ≫ G.φ)).choose

theorem hInt : (generic R ℚ).map G.πInt = G.jX ≫ G.φ :=
  ((G.neron.2.2.2.2 G.M).surjective (G.jX ≫ G.φ)).choose_spec

theorem hInt_target : (generic R ℚ).map G.πInt ≫ G.jE.hom = G.jX ≫ π := by
  rw [G.hInt]
  simp [φ]

/-- Restrict a morphism and evaluate at a geometric residue section. -/
def readAt {B : Over (Spec (.of R))} (b : residueSource ell K ⟶ G.special.obj B) :
    (B ⟶ G.E) →* Multiplicative (Ebar.baseChange K).toAffine.Point :=
  G.read.toMonoidHom.comp
    (({ toFun := fun f => b ≫ f
        map_one' := MonObj.comp_one b
        map_mul' := fun f g => MonObj.comp_mul b f g } :
      (G.special.obj B ⟶ G.special.obj G.E) →* _).comp
      (G.special.homMonoidHom (X := B) (M := G.E)))

/-- Evaluation of the extended fixed map on a geometric section of the source. -/
def evaluate (x : residueSource ell K ⟶ G.special.obj G.M) :
    (Ebar.baseChange K).toAffine.Point :=
  (G.readAt x G.πInt).toAdd

theorem evaluate_frob (x : X.Point) :
    G.evaluate (G.point (X.frobenius x)) = curveFrob (K := K) Ebar (G.evaluate (G.point x)) := by
  change (G.read (G.point (X.frobenius x) ≫ G.special.map G.πInt)).toAdd = _
  rw [G.point_frob, Category.assoc, G.read_frob]
  rfl

/-- The residue value of the actual fixed map, in the quadratic residue group. -/
def value (x : X.Point) : PM.ReducedPoints (K := K) Ebar :=
  ⟨G.evaluate (G.point x), (mem_fixedSq _).mpr (by
    rw [← G.evaluate_frob x, ← G.evaluate_frob (X.frobenius x), G.frobenius_sq x])⟩

theorem value_frob (x : X.Point) :
    G.value (X.frobenius x) = fixedFrob (curveFrob (K := K) Ebar) (G.value x) :=
  Subtype.ext (G.evaluate_frob x)

/-- The rational translation in the generic elliptic model. The based map
has zero base value, so this is π(W∞) − π(∞). -/
def translationQ (q : ℕ) : 𝟙_ (Over (Spec (.of ℚ))) ⟶ G.genericE :=
  J0Cusps.infinity N ≫ rationalW N q ≫ G.φ

/-- The Néron extension of the rational translation, on the target only. -/
def translationInt (q : ℕ) : 𝟙_ (Over (Spec (.of R))) ⟶ G.E := by
  letI : Smooth (𝟙_ (Over (Spec (.of R)))).hom := by
    change Smooth (𝟙 (Spec (.of R)))
    infer_instance
  exact ((G.neron.2.2.2.2 _).surjective
    (toUnit _ ≫ G.translationQ q)).choose

theorem translationInt_generic (q : ℕ) :
    (generic R ℚ).map (G.translationInt q) = toUnit _ ≫ G.translationQ q := by
  letI : Smooth (𝟙_ (Over (Spec (.of R)))).hom := by
    change Smooth (𝟙 (Spec (.of R)))
    infer_instance
  exact ((G.neron.2.2.2.2 _).surjective (toUnit _ ≫ G.translationQ q)).choose_spec

/-- The reduction of the rational translation belongs to the quadratic
residue group: it is already fixed by the prime-field Frobenius. -/
def translation (q : ℕ) : PM.ReducedPoints (K := K) Ebar := by
  refine ⟨(G.readAt (residueUnit G.closed) (G.translationInt q)).toAdd, (mem_fixedSq _).mpr ?_⟩
  have h : residueFrob ell K ≫ residueUnit G.closed = residueUnit G.closed :=
    (IsTerminal.isTerminalObj _ _ isTerminalTensorUnit).hom_ext _ _
  have hh := G.read_frob (residueUnit G.closed ≫ G.special.map (G.translationInt q))
  rw [← Category.assoc, h] at hh
  let y := (G.read (residueUnit G.closed ≫ G.special.map (G.translationInt q))).toAdd
  change curveFrob (K := K) Ebar (curveFrob (K := K) Ebar y) = y
  exact (congrArg (curveFrob (K := K) Ebar) hh.symm).trans hh.symm


end GoodRow
end ZInQ.Manuscript.RC.PMWire
