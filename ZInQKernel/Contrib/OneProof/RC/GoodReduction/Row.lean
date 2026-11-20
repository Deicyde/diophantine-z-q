import ZInQKernel.Contrib.OneProof.RC.X0Model3.Specialize

/-! The pointwise square at the detector's place (tex 8476–8479,
9265–9291, on-the-spot glue (c)). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Contrib.ChebFD.C10 (GQ)
open scoped WeierstrassCurve Classical

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace ZInQ.Manuscript.RC.GoodReduction

open PreparedParam PMGeometry WitnessSpec

variable {C : WeierstrassCurve ℤ} [(C⁄ℚ).IsElliptic]
    [NeZero (newformLevel (C⁄ℚ))]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (C⁄ℚ)) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ} {D d₁ : ℤ}
    (dat : HeegnerDatum (C⁄ℚ) f Lat κ (D * d₁) 1 d₁)
    {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)
    (w : DatumPlace dat v) (hg : ¬ (p : ℤ) ∣ C.Δ)

variable (π : (X0Model3.model (newformLevel (C⁄ℚ))).X ⟶ Proj (C⁄ℚ).toProjective.grading)
    (hQ : π ≫ projectiveOverQ (C⁄ℚ) = (X0Model3.model (newformLevel (C⁄ℚ))).overQ)
    (han : ∀ τ : UpperHalfPlane, projectiveValue
      (((X0Model3.model (newformLevel (C⁄ℚ))).complexPoint τ).comp π hQ).val =
        phiAn (C⁄ℚ) f Lat κ τ)

include han in
set_option maxHeartbeats 950000 in
/-- Compare the integral lift of the fixed map with the detector's
existing target reduction. The source comparison uses the actual
label and the fixed map. The target comparison reads a separately
lifted target point in the detector's point type. -/
theorem hpi_of_integralDiagram
    {a b : ℚ} {R : Eichler.Order a b}
    {B : PMGeometry.Adelic (ell := p) (N := newformLevel (C⁄ℚ)) R} {ap : ℕ → ℤ}
    (G : GeometricInput B (ResidueAt v) (ReducedEquation C p) ap)
    {Cl : Type} (r : Cl → G.Point) (artin : Cl → DatumGalois dat)
    (x : letI := dat.field; letI := dat.nf; letI := dat.nz
      FieldPoint (X0Model3.model (newformLevel (C⁄ℚ))).overQ (DatumField dat))
    (hx : letI := dat.field; letI := dat.nf; letI := dat.nz
      x.map dat.ι = (X0Model3.model (newformLevel (C⁄ℚ))).complexPoint
        (cmPoint dat.A dat.B ((D * d₁) * (1 : ℤ) ^ 2)))
    {A : Type} [CommRing A] [IsDomain A] {M E S V : Scheme.{0}}
    (base : E ⟶ S) [IsSeparated base]
    (j : letI := dat.field; letI := dat.nf; letI := dat.nz
      Spec (.of (DatumField dat)) ⟶ Spec (.of A)) [IsDominant j]
    (k : V ⟶ Spec (.of A))
    (jX : (X0Model3.model (newformLevel (C⁄ℚ))).X ⟶ M)
    (jE : Proj (C⁄ℚ).toProjective.grading ⟶ E)
    (πInt : M ⟶ E) (hInt : jX ≫ πInt = π ≫ jE)
    (xInt : Cl → (Spec (.of A) ⟶ M)) (yInt : Cl → (Spec (.of A) ⟶ E))
    (hbase : ∀ c, (xInt c ≫ πInt) ≫ base = yInt c ≫ base)
    (hsource : letI := dat.field; letI := dat.nf; letI := dat.nz
      ∀ c, j ≫ xInt c = (x.map ((artin c).toAlgHom.restrictScalars ℚ)).val ≫ jX)
    (htarget : letI := dat.field; letI := dat.nf; letI := dat.nz
      ∀ c, j ≫ yInt c = ((x.map ((artin c).toAlgHom.restrictScalars ℚ)).comp π hQ).val ≫ jE)
    (read : (V ⟶ E) → PM.ReducedPoints (K := ResidueAt v) (ReducedEquation C p))
    (hPM : ∀ c, G.specialize (r c) = read ((k ≫ xInt c) ≫ πInt))
    (hread : letI := dat.field; letI := dat.nf; letI := dat.nz
      letI := Classical.decEq (DatumField dat)
      ∀ c, read (k ≫ yInt c) = datumReduction dat v w hg
        (projectiveValue (((x.map ((artin c).toAlgHom.restrictScalars ℚ)).comp π hQ).val))) :
    ∀ c, G.specialize (r c) = datumReduction dat v w hg (conjugate dat (artin c)) := by
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  letI := Classical.decEq (DatumField dat)
  intro c
  have hgen : j ≫ (xInt c ≫ πInt) = j ≫ yInt c := by
    rw [← Category.assoc, hsource c, Category.assoc, hInt, htarget c]
    simp only [FieldPoint.comp, Category.assoc]
  rw [hPM c, X0Model3.specialize_of_integral_extension base j k (xInt c) πInt (yInt c)
    (hbase c) hgen, hread c]
  exact X0Model3.datumReduction_projectiveValue dat v w hg π hQ han x hx (artin c)


end ZInQ.Manuscript.RC.GoodReduction
