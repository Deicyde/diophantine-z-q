import ZInQKernel.Contrib.OneProof.RC.ModelTarget.CubicComplex
import ZInQKernel.Contrib.OneProof.RC.ModelTarget.ReadEquiv
import ZInQKernel.Contrib.OneProof.RC.PMWire.Model

/-! The target-side fields of `PMWire.GoodRow` at the detector, all from the good cubic
of the fixed integral equation (tex 8476–8492). `GoodTarget` lists exactly the fields `E`,
`groupE`, `neron`, `jE`, `properGenericE`, `geomIntGenericE`, `readComplex`,
`readComplex_eq`, `read` and `read_frob` of `PMWire.GoodRow` with `closed :=
ModelNeron.closed ℓ`; `goodTarget` supplies them, and `GoodTarget.toGoodRow` assembles a
`GoodRow` from them and the remaining (source-side and same-place) fields. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve WeierstrassCurve.ModelTorsion
open scoped WeierstrassCurve CategoryTheory.Obj MonoidalCategory CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.ModelTarget

open GoodReduction (generic)
open PMWire (complexBase ellipticTarget rationalSource GenericSource genericProjection ExtendsAtkin)
open PMQuotient (residueSource residueFrob)
open PMGeometry (ReducedEquation)

/-- The target-side fields of `PMWire.GoodRow` at the detector `ℓ`. -/
structure GoodTarget (ell : ℕ) [Fact ell.Prime] (K : Type) [Field K] [Algebra (ZMod ell) K]
    [DecidableEq K] (Ebar : WeierstrassCurve (ZMod ell)) (E₀ : WeierstrassCurve ℚ) [E₀.IsElliptic] where
  E : Over (Spec (.of (LocalIntegers ell)))
  [groupE : GrpObj E]
  neron : CToPrinted.IsNeronModelOver (LocalIntegers ell) ℚ E
  jE : (generic (LocalIntegers ell) ℚ).obj E ≅ ellipticTarget E₀
  [properGenericE : IsProper ((generic (LocalIntegers ell) ℚ).obj E).hom]
  [geomIntGenericE : GeometricallyIntegral ((generic (LocalIntegers ell) ℚ).obj E).hom]
  readComplex : (complexBase ⟶ (generic (LocalIntegers ell) ℚ).obj E) →*
    Multiplicative (E₀.baseChange ℂ).toAffine.Point
  readComplex_eq : ∀ a, (readComplex a).toAdd = PreparedParam.projectiveValue (a.left ≫ jE.hom.left)
  read : (residueSource ell K ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj E) ≃*
    Multiplicative (Ebar.baseChange K).toAffine.Point
  read_frob : ∀ y, (read (residueFrob ell K ≫ y)).toAdd = Stages.curveFrob (K := K) Ebar (read y).toAdd

attribute [instance] GoodTarget.groupE GoodTarget.properGenericE GoodTarget.geomIntGenericE

variable (ell : ℕ) [Fact ell.Prime] (W₀ : WeierstrassCurve ℤ)
  (K : Type) [Field K] [Algebra (ZMod ell) K] [DecidableEq K]

/-- **The target-side fields of `PMWire.GoodRow` from the good cubic.** For an integral
Weierstrass equation `W₀` with discriminant prime to the detector `ℓ ≥ 5`, every field is the
actual object or reading of the projective cubic of `W₀` over `ℤ_(ℓ)`. -/
def goodTarget (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    haveI : (W₀⁄ℚ).IsElliptic := detRational_isElliptic hΔ
    GoodTarget ell K (ReducedEquation W₀ ell) (W₀⁄ℚ) :=
  haveI : (W₀⁄ℚ).IsElliptic := detRational_isElliptic hΔ
  letI := weierstrassModelGrp ell h₅ W₀ hΔ
  haveI := detProperGeneric h₅ hΔ
  haveI := detGeomIntGeneric h₅ hΔ
  { E := detE ell W₀
    neron := weierstrassModel_isNeron ell h₅ W₀ hΔ
    jE := cubicJE h₅ hΔ
    readComplex := readComplexCubic h₅ hΔ
    readComplex_eq := readComplexCubic_eq h₅ hΔ
    read := read ell W₀ K h₅ hΔ
    read_frob := read_frob ell W₀ K h₅ hΔ }

variable {ell K}

/-- A `PMWire.GoodRow` from the target-side fields and the remaining source-side and
same-place fields, with `closed := ModelNeron.closed ℓ`. -/
def GoodTarget.toGoodRow {Ebar : WeierstrassCurve (ZMod ell)} {E₀ : WeierstrassCurve ℚ}
    [E₀.IsElliptic] (T : GoodTarget ell K Ebar E₀) {N : ℕ} [NeZero N] {X : PMAdelic.CoarseFibre}
    {π : rationalSource N ⟶ ellipticTarget E₀}
    (M : Over (Spec (.of (LocalIntegers ell)))) [Smooth M.hom] [IsReduced M.left]
    [IsSeparated M.hom] [IsDominant (genericProjection M)]
    (source : GenericSource ((generic (LocalIntegers ell) ℚ).obj M) N)
    (point : X.Point → (residueSource ell K ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj M))
    (extension : ∀ q : ℕ, q.Prime → 0 < N.factorization q → ∃ W : M ⟶ M, ExtendsAtkin source q W)
    (point_W : ∀ q hq he x, point (X.W q x) = point x ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).map (extension q hq he).choose)
    (point_frob : ∀ x, point (X.frobenius x) = residueFrob ell K ≫ point x)
    (frobenius_sq : Function.Involutive X.frobenius) :
    PMWire.GoodRow (LocalIntegers ell) ell N K Ebar X π where
  closed := ModelNeron.closed ell
  M := M
  source := source
  E := T.E
  neron := T.neron
  jE := T.jE
  readComplex := T.readComplex
  readComplex_eq := T.readComplex_eq
  point := point
  extension := extension
  point_W := point_W
  read := T.read
  read_frob := T.read_frob
  point_frob := point_frob
  frobenius_sq := frobenius_sq

#print axioms goodTarget
#print axioms GoodTarget.toGoodRow

end ZInQ.Manuscript.RC.ModelTarget
