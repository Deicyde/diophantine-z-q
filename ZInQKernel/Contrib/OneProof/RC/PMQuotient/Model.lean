import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Atkin

/-! Tex 8476–8479: the single good-reduction diagram for the fixed map.
The point and divisor interfaces are on-the-spot glue (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve
open FreeAbelianGroup (of)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 350000
set_option maxHeartbeats 900000

namespace ZInQ.Manuscript.RC.PMQuotient

open GoodReduction (generic)
open PMGeometry (DivZero center)
open Stages

/-- Passage from the prime residue field to the detector's geometric residue field. -/
abbrev residueSource (ell : ℕ) (K : Type) [Fact ell.Prime] [Field K] [Algebra (ZMod ell) K] :
    Over (Spec (.of (ZMod ell))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ZMod ell) K)))

/-- The arithmetic Frobenius action on sections is precomposition by this map. -/
def residueFrob (ell : ℕ) (K : Type) [Fact ell.Prime] [Field K] [Algebra (ZMod ell) K] :
    residueSource ell K ⟶ residueSource ell K :=
  Over.homMk (Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom (ZMod ell) K).toRingHom))
    (by
      change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (ZMod ell) K)) = _
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      ext a
      exact (FiniteField.frobeniusAlgHom (ZMod ell) K).commutes a)

/-- A section of the base changed terminal object is unique (c). -/
def residueUnit {R : Type} [CommRing R] {ell : ℕ} [Fact ell.Prime]
    {K : Type} [Field K] [Algebra (ZMod ell) K] (closed : R →+* ZMod ell) :
    residueSource ell K ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom closed))).obj (𝟙_ (Over (Spec (.of R)))) :=
  (IsTerminal.isTerminalObj _ _ isTerminalTensorUnit).from _

/-- The one remaining good-model input, over a trait with prime residue field, at
the chosen detector place. The generic identifications are with the actual
rational source and target of the fixed parametrization. -/
structure GoodRow (R : Type) [CommRing R] [Algebra R ℚ]
    (ell N : ℕ) [Fact ell.Prime] (K : Type) [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    (Ebar : WeierstrassCurve (ZMod ell)) (X : PMAdelic.CoarseFibre)
    {XQ EQ : Over (Spec (.of ℚ))} (π : XQ ⟶ EQ) where
  /-- The reduction map of the local base at the rational detector prime (c). -/
  closed : R →+* ZMod ell
  /-- Deligne–Rapoport, LNM 349 (1973), VI.6; Igusa (1959), locators UNVERIFIED. -/
  M : Over (Spec (.of R))
  /-- Good elliptic model from the integral Weierstrass equation with unit discriminant. -/
  E : Over (Spec (.of R))
  /-- Smooth good reduction of the modular curve, Deligne–Rapoport VI.6 (UNVERIFIED). -/
  [smoothM : Smooth M.hom]
  /-- The group law on the smooth Weierstrass cubic with its zero section. -/
  [groupE : GrpObj E]
  /-- Néron property of the good group model, proved by
  `NeronExt.isNeronModelOver_of_grpObj` over a DVR. -/
  neron : CToPrinted.IsNeronModelOver R ℚ E
  /-- Generic identification in the good model theorem, in the fixed rational chart (c). -/
  jX : (generic R ℚ).obj M ≅ XQ
  /-- Generic identification of the good elliptic model with the given equation (c). -/
  jE : (generic R ℚ).obj E ≅ EQ
  /-- The cusp at infinity of the good modular model (Deligne–Rapoport VI.6, UNVERIFIED). -/
  infinity : X.Point
  /-- Read the coarse points as sections of the modular fibre (Deligne–Rapoport
  VI.6), using Ribet's supersingular description (Invent. Math. 100 (1990),
  Prop. 3.3, Prop. 3.6, Rem. 3.5(a)(b)); locators UNVERIFIED. -/
  point : X.Point →
    (residueSource ell K ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom closed))).obj M)
  /-- Integral section at the rational cusp infinity; Deligne–Rapoport VI.6 (UNVERIFIED). -/
  cusp : 𝟙_ (Over (Spec (.of R))) ⟶ M
  /-- The coarse infinity label reads the reduction of the same cusp (c). -/
  point_infinity : point infinity = residueUnit closed ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom closed))).map cusp
  /-- The full prime-power Atkin–Lehner operator on the integral curve;
  Deligne–Rapoport VI.6 (UNVERIFIED), via the cyclic-isogeny moduli action. -/
  W : ∀ q : ℕ, q.Prime → 0 < N.factorization q → (M ⟶ M)
  /-- The coarse action of the same Atkin–Lehner operator, including at the cusp (c). -/
  point_W : ∀ q hq he x, point (X.W q x) =
    point x ≫ (Over.pullback (Spec.map (CommRingCat.ofHom closed))).map (W q hq he)
  /-- The identification with the actual reduced Weierstrass points, respecting
  the group law (c). This is an equivalence, so the readout cannot collapse the group. -/
  read :
    (residueSource ell K ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom closed))).obj E) ≃*
      Multiplicative (Ebar.baseChange K).toAffine.Point
  /-- Naturality of the coordinate reading over the prime field (c). -/
  read_frob : ∀ y, (read (residueFrob ell K ≫ y)).toAdd = curveFrob (K := K) Ebar (read y).toAdd
  /-- Geometric arithmetic Frobenius on the coarse points, with the same residue
  map as the elliptic group; Ribet's description and the section identification (c). -/
  point_frob : ∀ x, point (X.frobenius x) = residueFrob ell K ≫ point x
  /-- The cusp and coarse points are over the quadratic field; Ribet, locators above. -/
  frobenius_sq : Function.Involutive X.frobenius
  /-- Rationality of the cusp at infinity (Deligne–Rapoport VI.6, UNVERIFIED). -/
  frobenius_infinity : X.frobenius infinity = infinity
  /-- The good Hecke correspondence at the base cusp with multiplicities,
  from the prime-to-level cyclic correspondences (tex 8486–8487). -/
  T_infinity : ∀ q, q.Prime → ¬ q ∣ N * ell → X.T q infinity = (q + 1) • of infinity

attribute [instance] GoodRow.smoothM GoodRow.groupE

namespace GoodRow

variable {R : Type} [CommRing R] [Algebra R ℚ]
    {ell N : ℕ} [Fact ell.Prime] {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    {Ebar : WeierstrassCurve (ZMod ell)} {X : PMAdelic.CoarseFibre}
    {XQ EQ : Over (Spec (.of ℚ))} {π : XQ ⟶ EQ}
    (G : GoodRow R ell N K Ebar X π)

/-- Base change to the prime residue field. -/
abbrev special := Over.pullback (Spec.map (CommRingCat.ofHom G.closed))

/-- The Néron extension of the fixed generic parametrization (tex 8477–8479). -/
def πInt : G.M ⟶ G.E :=
  ((G.neron.2.2.2.2 G.M).surjective (G.jX.hom ≫ π ≫ G.jE.inv)).choose

/-- The extension diagram over the generic point, by the Néron property. -/
theorem hInt : (generic R ℚ).map G.πInt ≫ G.jE.hom = G.jX.hom ≫ π := by
  have h : (generic R ℚ).map G.πInt = G.jX.hom ≫ π ≫ G.jE.inv :=
    ((G.neron.2.2.2.2 G.M).surjective (G.jX.hom ≫ π ≫ G.jE.inv)).choose_spec
  simp [h]

/-- The residue reading of the extended fixed map on a given geometric section. -/
def evaluate (x : residueSource ell K ⟶ G.special.obj G.M) :
    (Ebar.baseChange K).toAffine.Point :=
  (G.read (x ≫ G.special.map G.πInt)).toAdd

/-- Equivariance follows from precomposition and coordinate naturality (c). -/
theorem evaluate_frob (x : X.Point) :
    G.evaluate (G.point (X.frobenius x)) = curveFrob (K := K) Ebar (G.evaluate (G.point x)) := by
  unfold evaluate
  rw [G.point_frob, Category.assoc, G.read_frob]

/-- The same value in the detector's quadratic residue group. -/
def value (x : X.Point) : PM.ReducedPoints (K := K) Ebar :=
  ⟨G.evaluate (G.point x), (mem_fixedSq _).mpr (by
    rw [← G.evaluate_frob x, ← G.evaluate_frob (X.frobenius x), G.frobenius_sq x])⟩

/-- The additive extension to divisors, and then restriction to degree zero (c).
No factorization through a geometric Jacobian is needed by the row. -/
def quotient : DivZero X.Point →+ PM.ReducedPoints (K := K) Ebar :=
  (FreeAbelianGroup.lift G.value).comp (DivZero X.Point).subtype

/-- Evaluation after centering a point subtracts the value at the base cusp (c). -/
theorem quotient_center (x : X.Point) :
    G.quotient (center G.infinity (of x)) = G.value x - G.value G.infinity := by
  change FreeAbelianGroup.lift G.value
      (of x - FreeAbelianGroup.lift (fun _ : X.Point => (1 : ℤ)) (of x) • of G.infinity) = _
  simp

/-- The based specialization of Frobenius follows from functoriality over
the prime residue field, including at the chosen base cusp. -/
theorem frobenius_quotient (x : X.Point) :
    G.quotient (center G.infinity (of (X.frobenius x) - of (X.frobenius G.infinity))) =
      fixedFrob (curveFrob (K := K) Ebar) (G.quotient (center G.infinity (of x))) := by
  simp only [map_sub, G.quotient_center]
  apply Subtype.ext
  change (G.evaluate (G.point (X.frobenius x)) - G.evaluate (G.point G.infinity)) -
      (G.evaluate (G.point (X.frobenius G.infinity)) - G.evaluate (G.point G.infinity)) =
    curveFrob (K := K) Ebar (G.evaluate (G.point x)) -
      curveFrob (K := K) Ebar (G.evaluate (G.point G.infinity))
  rw [G.evaluate_frob, G.evaluate_frob]
  abel

end GoodRow


end ZInQ.Manuscript.RC.PMQuotient
