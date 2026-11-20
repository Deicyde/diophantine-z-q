import ZInQKernel.Contrib.OneProof.RC.X0Model3.Model
import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Parametrization
import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Heegner

/-! Pointwise reduction for the characteristic-zero parametrization, and
uniqueness of specialization when the integral maps are available
(tex 2915–2917, 8476–8479, 9265–9291; on the spot, provenance (c)).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Contrib.ChebFD.C10 (GQ)
open scoped WeierstrassCurve Classical

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace ZInQ.Manuscript.RC.X0Model3

open PreparedParam PMGeometry WitnessSpec

/-- The selected elliptic point is determined over its field by the
complex value of the rational parametrization on the selected source point. -/
theorem projectiveValue_eq_of_complexPoint {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [NeZero (newformLevel E)] {X : PreparedParam.X0Model (newformLevel E)}
    {F : Type} [Field F] [Algebra ℚ F] (ι : F →ₐ[ℚ] ℂ)
    (x : FieldPoint X.overQ F) (τ : UpperHalfPlane)
    (π : X.X ⟶ Proj E.toProjective.grading) (hQ : π ≫ projectiveOverQ E = X.overQ)
    (hx : x.map ι = X.complexPoint τ)
    (y : (E.baseChange F).toAffine.Point)
    (hy : Affine.Point.map (W' := E.toAffine) ι y =
      projectiveValue ((X.complexPoint τ).comp π hQ).val) :
    projectiveValue (x.comp π hQ).val = y := by
  apply Affine.Point.map_injective (W' := E.toAffine) ι
  calc
    _ = projectiveValue (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ (x.comp π hQ).val) :=
      projectiveValue_map ι _
    _ = projectiveValue ((x.map ι).comp π hQ).val := by
      simp only [FieldPoint.map, FieldPoint.comp, Category.assoc]
    _ = projectiveValue ((X.complexPoint τ).comp π hQ).val :=
      congrArg (fun z : FieldPoint X.overQ ℂ => projectiveValue (z.comp π hQ).val) hx
    _ = _ := hy.symm

section Datum

variable {C : WeierstrassCurve ℤ} [(C⁄ℚ).IsElliptic]
    [NeZero (newformLevel (C⁄ℚ))]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (C⁄ℚ)) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ} {D d₁ : ℤ}
    (dat : HeegnerDatum (C⁄ℚ) f Lat κ (D * d₁) 1 d₁)
    {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)
    (w : DatumPlace dat v) (hg : ¬ (p : ℤ) ∣ C.Δ)

variable (π : (model (newformLevel (C⁄ℚ))).X ⟶ Proj (C⁄ℚ).toProjective.grading)
    (hQ : π ≫ projectiveOverQ (C⁄ℚ) = (model (newformLevel (C⁄ℚ))).overQ)
    (han : ∀ τ : UpperHalfPlane, projectiveValue
      (((model (newformLevel (C⁄ℚ))).complexPoint τ).comp π hQ).val =
        phiAn (C⁄ℚ) f Lat κ τ)

include han

/-- At the detector's place, evaluating the fixed-scale map on the
conjugate source point and then applying datum reduction gives the
reduction of the conjugate already used by Stage Kummer. The source
point is taken at the embedding of the selected datum. -/
theorem datumReduction_projectiveValue
    (x : letI := dat.field; letI := dat.nf; letI := dat.nz
      FieldPoint (model (newformLevel (C⁄ℚ))).overQ (DatumField dat))
    (hx : letI := dat.field; letI := dat.nf; letI := dat.nz
      x.map dat.ι = (model (newformLevel (C⁄ℚ))).complexPoint
        (cmPoint dat.A dat.B ((D * d₁) * (1 : ℤ) ^ 2)))
    (σ : DatumGalois dat) :
    letI := dat.field; letI := dat.nf; letI := dat.nz
    letI := Classical.decEq (DatumField dat)
    datumReduction dat v w hg
      (projectiveValue (((x.map (σ.toAlgHom.restrictScalars ℚ)).comp π hQ).val)) =
    datumReduction dat v w hg (conjugate dat σ) := by
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  letI := Classical.decEq (DatumField dat)
  have hy := projectiveValue_eq_of_complexPoint dat.ι x _ π hQ hx dat.y
    (dat.hy.trans (han _).symm)
  apply congrArg (datumReduction dat v w hg)
  let e := σ.toAlgHom.restrictScalars ℚ
  change projectiveValue ((x.map e).comp π hQ).val =
    Affine.Point.map (W' := (C⁄ℚ).toAffine) e dat.y
  calc
    _ = projectiveValue (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ (x.comp π hQ).val) := by
      simp only [FieldPoint.map, FieldPoint.comp, Category.assoc]
    _ = Affine.Point.map (W' := (C⁄ℚ).toAffine) e (projectiveValue (x.comp π hQ).val) :=
      (projectiveValue_map e _).symm
    _ = _ := congrArg (Affine.Point.map (W' := (C⁄ℚ).toAffine) e) hy

/-- For the chosen characteristic-zero CM point, the actual row's
pointwise Artin comparison is exactly the comparison between the PM
special-fibre map and reduction of the rational map on its conjugates. -/
theorem hpi_iff_specialize_projectiveValue
    {a b : ℚ} {R : Eichler.Order a b}
    {A : PMGeometry.Adelic (ell := p) (N := newformLevel (C⁄ℚ)) R} {ap : ℕ → ℤ}
    (G : GeometricInput A (ResidueAt v) (ReducedEquation C p) ap)
    {Cl : Type} (r : Cl → G.Point) (artin : Cl → DatumGalois dat)
    (x : letI := dat.field; letI := dat.nf; letI := dat.nz
      FieldPoint (model (newformLevel (C⁄ℚ))).overQ (DatumField dat))
    (hx : letI := dat.field; letI := dat.nf; letI := dat.nz
      x.map dat.ι = (model (newformLevel (C⁄ℚ))).complexPoint
        (cmPoint dat.A dat.B ((D * d₁) * (1 : ℤ) ^ 2))) :
    letI := dat.field; letI := dat.nf; letI := dat.nz
    letI := Classical.decEq (DatumField dat)
    (∀ c, G.specialize (r c) = datumReduction dat v w hg (conjugate dat (artin c))) ↔
    (∀ c, G.specialize (r c) = datumReduction dat v w hg
      (projectiveValue (((x.map ((artin c).toAlgHom.restrictScalars ℚ)).comp π hQ).val))) := by
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  letI := Classical.decEq (DatumField dat)
  simp only [datumReduction_projectiveValue dat v w hg π hQ han x hx]

end Datum

/-- Once a map over the local base exists, its value on the closed point
of a lifted section is controlled by its generic value. Separatedness
identifies the composite with any other extension of that generic value. -/
theorem specialize_of_integral_extension {A : Type} [CommRing A] [IsDomain A]
    {X Y S U V : Scheme.{0}} (b : Y ⟶ S) [IsSeparated b]
    (j : U ⟶ Spec (.of A)) [IsDominant j] (s : V ⟶ Spec (.of A))
    (x : Spec (.of A) ⟶ X) (π : X ⟶ Y) (y : Spec (.of A) ⟶ Y)
    (hbase : (x ≫ π) ≫ b = y ≫ b)
    (hgen : j ≫ (x ≫ π) = j ≫ y) :
    (s ≫ x) ≫ π = s ≫ y := by
  rw [Category.assoc, ext_of_isDominant_of_isSeparated b hbase j hgen]


end ZInQ.Manuscript.RC.X0Model3
