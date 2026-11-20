import ZInQKernel.Contrib.OneProof.RC.PMWire.Fibre
import ZInQKernel.Contrib.OneProof.RC.PMQuotient.CM

/-! Transport the existing CM diagram comparison along the generic open
immersion. This compares the same contracted place and does not prove
the separate conductor-one orbit assertion. Tex 8476–8479, 9265–9291;
on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Contrib.ChebFD.C10 (GQ)
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj WeierstrassCurve Classical

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 350000
set_option maxHeartbeats 1300000
set_option maxRecDepth 1600

namespace ZInQ.Manuscript.RC.PMWire

open GoodReduction (generic)
open PreparedParam PMGeometry WitnessSpec Stages

open PMQuotient (residueSource genericInclusion cmRing cmGeneric cmResidue cmGeneric_dominant)

namespace GoodRow

variable {R : Type} [CommRing R] [Algebra R ℚ]
    {ell N : ℕ} [Fact ell.Prime] [NeZero N] {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    {Ebar : WeierstrassCurve (ZMod ell)} {X : PMAdelic.CoarseFibre}
    {E₀ : WeierstrassCurve ℚ} [E₀.IsElliptic] {π : rationalSource N ⟶ ellipticTarget E₀}
    (G : GoodRow R ell N K Ebar X π)

/-- The actual geometric residue point of the local base. -/
abbrev geometricResidue : Spec (.of K) ⟶ Spec (.of R) :=
  (residueSource ell K).hom ≫ Spec.map (CommRingCat.ofHom G.closed)

/-- A closed-fibre section as a morphism into the integral model. -/
def rawSection {A : Over (Spec (.of R))}
    (x : residueSource ell K ⟶ G.special.obj A) : Spec (.of K) ⟶ A.left :=
  x.left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom G.closed))

/-- Only maps over the chosen residue point are used in the diagram. -/
theorem rawSection_over {A : Over (Spec (.of R))}
    (x : residueSource ell K ⟶ G.special.obj A) :
    G.rawSection x ≫ A.hom = G.geometricResidue := by
  simp only [rawSection, Category.assoc, pullback.condition]
  rw [← Category.assoc]
  exact congrArg (fun k => k ≫ _) (Over.w x)

/-- Naturality of the map from the closed fibre to the integral model (c). -/
theorem rawSection_map {A B : Over (Spec (.of R))}
    (x : residueSource ell K ⟶ G.special.obj A) (f : A ⟶ B) :
    G.rawSection (x ≫ G.special.map f) = G.rawSection x ≫ f.left := by
  simp [rawSection, special, Over.pullback_map_left, Category.assoc]

/-- Recover the closed-fibre section from a map known to lie over the
detector's geometric residue point (c). -/
def sectionOf {A : Over (Spec (.of R))} (x : Spec (.of K) ⟶ A.left)
    (h : x ≫ A.hom = G.geometricResidue) :
    residueSource ell K ⟶ G.special.obj A :=
  Over.homMk (pullback.lift x (residueSource ell K).hom h) (by simp [special])

/-- The recovered section has the original point coordinates (c). -/
theorem sectionOf_rawSection {A : Over (Spec (.of R))}
    (x : residueSource ell K ⟶ G.special.obj A) (h) :
    G.sectionOf (G.rawSection x) h = x := by
  ext : 1
  apply pullback.hom_ext
  · simp [sectionOf, rawSection]
  · exact (pullback.lift_snd _ _ _).trans (Over.w x).symm

/-- Totalize the reading for the old diagram API. Every use in the
comparison has both the base equality and quadratic descent. -/
def readRaw (y : Spec (.of K) ⟶ G.E.left) : PM.ReducedPoints (K := K) Ebar :=
  if h : y ≫ G.E.hom = G.geometricResidue then
    let P := (G.read (G.sectionOf y h)).toAdd
    if hP : P ∈ (PM.ReducedPoints (K := K) Ebar) then ⟨P, hP⟩ else 0
  else 0

/-- Read a map known to be a section with the indicated quadratic value (c). -/
theorem readRaw_eq {y : Spec (.of K) ⟶ G.E.left}
    (h : y ≫ G.E.hom = G.geometricResidue) (P : PM.ReducedPoints (K := K) Ebar)
    (hy : (G.read (G.sectionOf y h)).toAdd = P.val) : G.readRaw y = P := by
  unfold readRaw
  rw [dite_eq_left h]
  have hP : (G.read (G.sectionOf y h)).toAdd ∈ PM.ReducedPoints (K := K) Ebar :=
    by rw [hy]; exact P.property
  rw [dite_eq_left hP]
  exact Subtype.ext hy

/-- The old `hPM` premise on a coarse section is now a definitional
value comparison. No independent PM map occurs. -/
theorem readRaw_value (x : X.Point) :
    G.readRaw (G.rawSection (G.point x) ≫ G.πInt.left) = G.value x := by
  rw [← G.rawSection_map]
  apply G.readRaw_eq (G.rawSection_over _) (G.value x)
  rw [G.sectionOf_rawSection]
  rfl

end GoodRow

section Datum

variable {C : WeierstrassCurve ℤ} [(C⁄ℚ).IsElliptic]
    [NeZero (newformLevel (C⁄ℚ))]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (C⁄ℚ)) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ} {D d₁ : ℤ}
    (dat : HeegnerDatum (C⁄ℚ) f Lat κ (D * d₁) 1 d₁)
    {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)
    (w : DatumPlace dat v) (hg : ¬ (p : ℤ) ∣ C.Δ)

variable (π : (X0Model3.model (newformLevel (C⁄ℚ))).X ⟶ Proj (C⁄ℚ).toProjective.grading)
    (hQ : π ≫ projectiveOverQ (C⁄ℚ) = (X0Model3.model (newformLevel (C⁄ℚ))).overQ)

/-- The fixed rational map as a map over the rational base. -/
abbrev fixedMap {C : WeierstrassCurve ℤ} [NeZero (newformLevel (C⁄ℚ))]
    (π : (X0Model3.model (newformLevel (C⁄ℚ))).X ⟶ Proj (C⁄ℚ).toProjective.grading)
    (hQ : π ≫ projectiveOverQ (C⁄ℚ) = (X0Model3.model (newformLevel (C⁄ℚ))).overQ) :
    Over.mk (X0Model3.model (newformLevel (C⁄ℚ))).overQ ⟶
      Over.mk (projectiveOverQ (C⁄ℚ)) :=
  Over.homMk π hQ

variable {R : Type} [CommRing R] [Algebra R ℚ] {X : PMAdelic.CoarseFibre}
  (G : GoodRow R p (newformLevel (C⁄ℚ)) (ResidueAt v) (ReducedEquation C p) X (fixedMap π hQ))
  {Cl : Type} (r : Cl → X.Point) (artin : Cl → DatumGalois dat)

/-- The remaining comparisons for the CM point. This concerns lifts of the
actual point and the actual coordinate reduction at `w`. It contains no
quotient, specialized value identity, or CM-to-adelic orbit assertion. -/
structure CMDiagram where
  /-- Field of definition of the selected conductor-one CM point. -/
  x : letI := dat.field; letI := dat.nf; letI := dat.nz
    FieldPoint (X0Model3.model (newformLevel (C⁄ℚ))).overQ (DatumField dat)
  /-- The chosen CM embedding and the analytic level chart. -/
  analytic : letI := dat.field; letI := dat.nf; letI := dat.nz
    x.map dat.ι = (X0Model3.model (newformLevel (C⁄ℚ))).complexPoint
      (cmPoint dat.A dat.B ((D * d₁) * (1 : ℤ) ^ 2))
  /-- The lift of the generic CM point to the generic open of the model. -/
  xGeneric : letI := dat.field; letI := dat.nf
    Cl → (Spec (.of (DatumField dat)) ⟶ ((generic R ℚ).obj G.M).left)
  /-- Integral source lifts; for an open model the selected reduction
  must belong to the open (the noncuspidal locus). -/
  xInt : Cl → (Spec (.of (cmRing dat v w)) ⟶ G.M.left)
  /-- Independently computed good elliptic lifts by properness. -/
  yInt : Cl → (Spec (.of (cmRing dat v w)) ⟶ G.E.left)
  /-- The two lifts have the same local base (c). -/
  base : ∀ c, (xInt c ≫ G.πInt.left) ≫ G.E.hom = yInt c ≫ G.E.hom
  /-- The generic lift maps to the actual rational-model point. -/
  source : letI := dat.field; letI := dat.nf; letI := dat.nz
    ∀ c, xGeneric c ≫ G.jX.left = (x.map ((artin c).toAlgHom.restrictScalars ℚ)).val
  /-- The lift agrees with the integral source at the contracted place. -/
  source_lift : letI := dat.field; letI := dat.nf
    ∀ c, cmGeneric dat v w ≫ xInt c = xGeneric c ≫ genericProjection G.M
  /-- The fixed generic target, in the chosen Weierstrass equation (c). -/
  target : letI := dat.field; letI := dat.nf; letI := dat.nz
    ∀ c, cmGeneric dat v w ≫ yInt c =
      ((x.map ((artin c).toAlgHom.restrictScalars ℚ)).comp π hQ).val ≫ genericInclusion G.jE
  /-- The source reading of the actual reduced CM lift, before applying π (c). -/
  sourceResidue : ∀ c, G.rawSection (G.point (r c)) = cmResidue dat v w ≫ xInt c
  /-- The target lift specializes over the same residue point (c). -/
  targetOver : ∀ c, (cmResidue dat v w ≫ yInt c) ≫ G.E.hom = G.geometricResidue
  /-- The coordinate comparison for the good Weierstrass model, with
  the exact reduction already used by the detector (c). -/
  targetResidue : letI := dat.field; letI := dat.nf; letI := dat.nz
    letI := Classical.decEq (DatumField dat)
    ∀ c, (G.read (G.sectionOf (cmResidue dat v w ≫ yInt c) (targetOver c))).toAdd =
      (datumReduction dat v w hg
        (projectiveValue (((x.map ((artin c).toAlgHom.restrictScalars ℚ)).comp π hQ).val))).val

/-- The integral map agrees with the fixed rational map after including
the open generic source and the identified generic elliptic target. -/
theorem genericProjection_comp :
    genericProjection G.M ≫ G.πInt.left = G.jX.left ≫ π ≫ genericInclusion G.jE := by
  calc
    _ = ((generic R ℚ).map G.πInt).left ≫ genericProjection G.E := by
      simp [generic, genericProjection, Over.pullback_map_left]
    _ = _ := by
      rw [G.hInt]
      simp only [GoodRow.φ, Over.comp_left, Category.assoc]
      rfl

/-- Pointwise specialization of the same Néron extension. It uses the
generic lift already implicit in the integral source diagram. -/
theorem hpi_of_cmDiagram (B : CMDiagram dat v w hg π hQ G r artin)
    (han : ∀ τ : UpperHalfPlane, projectiveValue
      (((X0Model3.model (newformLevel (C⁄ℚ))).complexPoint τ).comp π hQ).val =
        phiAn (C⁄ℚ) f Lat κ τ) :
    ∀ c, G.value (r c) = datumReduction dat v w hg (conjugate dat (artin c)) := by
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  letI := Classical.decEq (DatumField dat)
  letI := G.neron.2.1
  letI := cmGeneric_dominant dat v w
  intro c
  have hgen : cmGeneric dat v w ≫ (B.xInt c ≫ G.πInt.left) =
      cmGeneric dat v w ≫ B.yInt c := by
    rw [← Category.assoc, B.source_lift, Category.assoc, genericProjection_comp,
      ← Category.assoc (B.xGeneric c), B.source, B.target]
    rfl
  rw [← G.readRaw_value (r c), B.sourceResidue,
    X0Model3.specialize_of_integral_extension G.E.hom (cmGeneric dat v w) (cmResidue dat v w)
      (B.xInt c) G.πInt.left (B.yInt c) (B.base c) hgen,
    G.readRaw_eq (B.targetOver c) _ (B.targetResidue c)]
  exact X0Model3.datumReduction_projectiveValue dat v w hg π hQ han B.x B.analytic (artin c)

end Datum


end ZInQ.Manuscript.RC.PMWire
