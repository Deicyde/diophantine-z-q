import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Operators
import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Row

/-! The source lift at the selected datum's contracted place, and
the comparison with the detector's coordinate reduction (c),
tex 8476–8479, 9265–9291. -/

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

namespace ZInQ.Manuscript.RC.PMQuotient

open GoodReduction (generic)
open PreparedParam PMGeometry WitnessSpec Stages

/-- The map on total spaces from the identified generic fibre (c). -/
abbrev genericInclusion {R : Type} [CommRing R] [Algebra R ℚ] {A : Over (Spec (.of R))}
    {AQ : Over (Spec (.of ℚ))} (j : (generic R ℚ).obj A ≅ AQ) :
    AQ.left ⟶ A.left :=
  j.inv.left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))

/-- Forgetting the generic identifications gives the underlying square
used by `GoodReduction.hpi_of_integralDiagram` (c). -/
theorem genericInclusion_comp {R : Type} [CommRing R] [Algebra R ℚ]
    {A B : Over (Spec (.of R))} {AQ BQ : Over (Spec (.of ℚ))}
    (jA : (generic R ℚ).obj A ≅ AQ) (jB : (generic R ℚ).obj B ≅ BQ)
    (f : A ⟶ B) (fQ : AQ ⟶ BQ)
    (h : (generic R ℚ).map f ≫ jB.hom = jA.hom ≫ fQ) :
    genericInclusion jA ≫ f.left = fQ.left ≫ genericInclusion jB := by
  have hh : jA.inv ≫ (generic R ℚ).map f = fQ ≫ jB.inv := by
    calc
      _ = jA.inv ≫ ((generic R ℚ).map f ≫ jB.hom) ≫ jB.inv := by simp
      _ = _ := by simp [h]
  have hl := congrArg (fun z => z.left) hh
  change jA.inv.left ≫ ((generic R ℚ).map f).left = fQ.left ≫ jB.inv.left at hl
  rw [genericInclusion, genericInclusion, ← Category.assoc fQ.left, ← hl, Category.assoc]
  simp [generic, Over.pullback_map_left]

namespace GoodRow

variable {R : Type} [CommRing R] [Algebra R ℚ]
    {ell N : ℕ} [Fact ell.Prime] {K : Type} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    {Ebar : WeierstrassCurve (ZMod ell)} {X : PMAdelic.CoarseFibre}
    {XQ EQ : Over (Spec (.of ℚ))} {π : XQ ⟶ EQ}
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
  rw [dif_pos h]
  have hP : (G.read (G.sectionOf y h)).toAdd ∈ PM.ReducedPoints (K := K) Ebar :=
    by rw [hy]; exact P.property
  rw [dif_pos hP]
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

/-- Precisely the restriction of the detector place along the datum embedding. -/
abbrev cmRing :=
  letI := dat.field; letI := dat.nf
  ((v.restrictHeightOne w.emb).valuation (DatumField dat)).valuationSubring

/-- The generic point of that valuation ring. -/
abbrev cmGeneric :=
  letI := dat.field; letI := dat.nf
  Spec.map (CommRingCat.ofHom (algebraMap (cmRing dat v w) (DatumField dat)))

/-- The generic point of the selected valuation ring is dense. -/
theorem cmGeneric_dominant : IsDominant (cmGeneric dat v w) := by
  letI := dat.field
  letI := dat.nf
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap (cmRing dat v w) (DatumField dat)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective _ _)]
  exact bot_le

/-- The geometric residue point of the selected valuation ring, embedded
into the detector residue field by its specified residue embedding. -/
abbrev cmResidue :=
  letI := dat.field; letI := dat.nf
  Spec.map (CommRingCat.ofHom ((v.residueEmbedding w.emb).toRingHom.comp
    (IsLocalRing.residue (cmRing dat v w))))

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
  /-- Integral source lifts by properness. -/
  xInt : Cl → (Spec (.of (cmRing dat v w)) ⟶ G.M.left)
  /-- Independently computed good elliptic lifts by properness. -/
  yInt : Cl → (Spec (.of (cmRing dat v w)) ⟶ G.E.left)
  /-- The two lifts have the same local base (c). -/
  base : ∀ c, (xInt c ≫ G.πInt.left) ≫ G.E.hom = yInt c ≫ G.E.hom
  /-- The fixed generic source, with the selected Artin label (c). -/
  source : letI := dat.field; letI := dat.nf; letI := dat.nz
    ∀ c, cmGeneric dat v w ≫ xInt c =
      (x.map ((artin c).toAlgHom.restrictScalars ℚ)).val ≫ genericInclusion G.jX
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

/-- Pointwise `hπ` at the same detector place. The `hPM` premise of
the integral-diagram lemma follows by reading the source section. -/
theorem hpi_of_cmDiagram {ap : ℕ → ℤ} {signs : ℕ → ℤˣ} (H : G.Relations ap signs)
    {hp4 : p % 4 = 3} {hN : 0 < newformLevel (C⁄ℚ)} {hc : (newformLevel (C⁄ℚ)).Coprime p}
    (J : PMAdelic.JetchevKane p hp4 (newformLevel (C⁄ℚ)) hN hc X)
    (han : ∀ τ : UpperHalfPlane, projectiveValue
      (((X0Model3.model (newformLevel (C⁄ℚ))).complexPoint τ).comp π hQ).val =
        phiAn (C⁄ℚ) f Lat κ τ)
    (B : CMDiagram dat v w hg π hQ G r artin) :
    ∀ c, (PMAdelic.geometricInput J (G.specialFibre H).toSpecialFibre).specialize (r c) =
      datumReduction dat v w hg (conjugate dat (artin c)) := by
  letI := G.neron.2.1
  letI := cmGeneric_dominant dat v w
  exact GoodReduction.hpi_of_integralDiagram dat v w hg π hQ han
    (PMAdelic.geometricInput J (G.specialFibre H).toSpecialFibre) r artin B.x B.analytic
    G.E.hom (cmGeneric dat v w) (cmResidue dat v w)
    (genericInclusion G.jX) (genericInclusion G.jE) G.πInt.left
    (genericInclusion_comp G.jX G.jE G.πInt (fixedMap π hQ) G.hInt)
    B.xInt B.yInt B.base B.source B.target G.readRaw
    (fun c => by rw [G.specialize_eq_value H J, ← B.sourceResidue c, G.readRaw_value])
    (fun c => G.readRaw_eq (B.targetOver c) _ (B.targetResidue c))

end Datum


end ZInQ.Manuscript.RC.PMQuotient
