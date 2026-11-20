import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Analytic
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Uniformization
import ZInQKernel.Contrib.OneProof.RC.ParamJoin.AtScale

/-! The Atkin–Lehner involution on the interior complex chart and the
comparison with the rational parametrization at the same scale.
Tex 2943–2946; the chart arguments are on-the-spot (c). -/

set_option autoImplicit false

noncomputable section

open scoped Classical MatrixGroups TauCeti.ExactDivisor
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.AtkinPin

open PreparedParam

variable {N Q : ℕ} [NeZero N]

private theorem atkinGL_chart_congr (X : X0Model N) (hQ : Q ∥ N)
    {τ σ : ℍ} (h : X.complexPoint τ = X.complexPoint σ) :
    X.complexPoint (atkinGL hQ • τ) = X.complexPoint (atkinGL hQ • σ) := by
  obtain ⟨γ, hγ, rfl⟩ := (X.complexPoint_eq_iff τ σ).mp h
  obtain ⟨δ, hδ, he⟩ := TauCeti.exists_mem_Gamma0_atkinLehnerGL_mul_mapGL hQ.pos hQ.dvd
    (TauCeti.isAtkinLehnerMatrix_atkinLehnerMatrix hQ) hγ
  change atkinGL hQ * mapGL ℝ γ = mapGL ℝ δ * atkinGL hQ at he
  apply (X.complexPoint_eq_iff _ _).mpr
  exact ⟨δ, hδ, by
    change mapGL ℝ δ • (atkinGL hQ • τ) = atkinGL hQ • (mapGL ℝ γ • τ)
    rw [← mul_smul, ← mul_smul, he]⟩

private theorem atkinGL_sq_chart (X : X0Model N) (hQ : Q ∥ N) (τ : ℍ) :
    X.complexPoint (atkinGL hQ • (atkinGL hQ • τ)) = X.complexPoint τ := by
  let H := TauCeti.isAtkinLehnerMatrix_atkinLehnerMatrix hQ
  obtain ⟨γ, hγ, hsq⟩ := H.exists_mem_Gamma0_mul_self hQ.pos.ne' hQ.dvd
  have hQR : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.pos.ne'
  have hGL : atkinGL hQ * atkinGL hQ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Q : ℝ) hQR) * mapGL ℝ γ := by
    have hscal : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Q : ℝ) hQR) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Q : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Units.val_mk0]
      split_ifs <;> simp
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, atkinGL,
      TauCeti.coe_atkinLehnerGL, mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom, ← Matrix.map_mul_intCast,
      hsq, hscal, Matrix.smul_mul, Matrix.one_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  rw [← mul_smul, hGL, mul_smul, UpperHalfPlane.glScalar_smul]
  exact ((X.complexPoint_eq_iff τ (γ • τ)).mpr ⟨γ, hγ, rfl⟩).symm

/-- The actual model's interior complex points, as the range of its chart. -/
abbrev Interior (X : X0Model N) := Set.range X.complexPoint

/-- Atkin–Lehner on the interior chart of the rational model. -/
def atkinInterior (X : X0Model N) (hQ : Q ∥ N) (x : Interior X) : Interior X :=
  ⟨X.complexPoint (atkinGL hQ • x.property.choose), _, rfl⟩

theorem atkinInterior_apply (X : X0Model N) (hQ : Q ∥ N) (τ : ℍ) :
    atkinInterior X hQ ⟨X.complexPoint τ, τ, rfl⟩ =
      ⟨X.complexPoint (atkinGL hQ • τ), _, rfl⟩ := by
  have h : ∃ σ : ℍ, X.complexPoint σ = X.complexPoint τ := ⟨τ, rfl⟩
  exact Subtype.ext (atkinGL_chart_congr X hQ h.choose_spec)

theorem atkinInterior_involutive (X : X0Model N) (hQ : Q ∥ N) :
    Function.Involutive (atkinInterior X hQ) := by
  rintro ⟨_, τ, rfl⟩
  rw [atkinInterior_apply, atkinInterior_apply]
  exact Subtype.ext (atkinGL_sq_chart X hQ τ)

/-- The algebraic model comparison needed for descent: an involution over
`ℚ` inducing the specified action on the interior complex chart. -/
structure RationalAtkin (X : X0Model N) (hQ : Q ∥ N) where
  hom : X.X ⟶ X.X
  overQ : hom ≫ X.overQ = X.overQ
  square : hom ≫ hom = 𝟙 X.X
  chart : ∀ τ : ℍ, (X.complexPoint τ).comp hom overQ =
    X.complexPoint (atkinGL hQ • τ)

/-- The signed translation of `phiAn` in the elliptic curve point group.
The constant is expressed as the difference of the two values at any
interior basepoint. -/
theorem phiAn_transform (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1) (hQ : Q ∥ N)
    (Lat : PeriodPair) (κ : ℂ) (hLat : IsLatticeOf E Lat) (base τ : ℍ) :
    let φ := phiAn E (f.toCuspFormGamma0 hχ) Lat κ
    φ (atkinGL hQ • τ) = (signUnit f hχ hQ : ℤ) • φ τ +
      (φ (atkinGL hQ • base) - (signUnit f hχ hQ : ℤ) • φ base) := by
  let U : ℂ →+ (E.baseChange ℂ).toAffine.Point :=
    AddMonoidHom.mk' (weierPt E Lat) (weierPt_add E Lat hLat)
  have h := scaled_eichler_transform f hχ hQ κ base τ
  rw [← zsmul_eq_mul, ← zsmul_eq_mul] at h
  simpa only [phiAn, map_add, map_sub, map_zsmul, U, AddMonoidHom.mk'_apply] using congrArg U h

/-- Apply the identity to one fixed rational morphism using its at-scale
chart comparison. This version also applies when the involution has
only been constructed on the interior chart. -/
theorem projectiveValue_transform_chart {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (X : X0Model N) (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1) (hQ : Q ∥ N)
    (Lat : PeriodPair) (κ : ℂ) (hLat : IsLatticeOf E Lat)
    (π : X.X ⟶ Proj E.toProjective.grading) (hπ : π ≫ projectiveOverQ E = X.overQ)
    (hscale : ∀ τ : ℍ, projectiveValue ((X.complexPoint τ).comp π hπ).val =
      phiAn E (f.toCuspFormGamma0 hχ) Lat κ τ) (base τ : ℍ) :
    let P := fun t : ℍ => projectiveValue ((X.complexPoint t).comp π hπ).val
    P (atkinGL hQ • τ) = (signUnit f hχ hQ : ℤ) • P τ +
      (P (atkinGL hQ • base) - (signUnit f hχ hQ : ℤ) • P base) := by
  simp only [hscale]
  exact phiAn_transform E f hχ hQ Lat κ hLat base τ

/-- The actual at-scale join supplies the rational morphism to which the
interior transformation applies. -/
theorem actualParametrization_transform_chart {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    [NeZero (newformLevel (Ecurve ℓ))]
    (f : HeckeRing.GL2.Newform (newformLevel (Ecurve ℓ)) 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 (f.toCuspFormGamma0 hχ)).coeff n =
      ((Ecurve ℓ).LFunction n : ℂ))
    (hQ : Q ∥ newformLevel (Ecurve ℓ)) {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) (f.toCuspFormGamma0 hχ) Lat κ)
    (hr : ∃ c : ℚ, (c : ℂ) = κ) :
    let X := X0Branch.model (newformLevel (Ecurve ℓ))
    ∃ (π : X.X ⟶ Proj (Ecurve ℓ).toProjective.grading)
      (hπ : π ≫ projectiveOverQ (Ecurve ℓ) = X.overQ), IsDominant π ∧
      (∀ τ : ℍ, projectiveValue ((X.complexPoint τ).comp π hπ).val =
        phiAn (Ecurve ℓ) (f.toCuspFormGamma0 hχ) Lat κ τ) ∧
      ∀ base τ : ℍ,
        let P := fun t : ℍ => projectiveValue ((X.complexPoint t).comp π hπ).val
        P (atkinGL hQ • τ) = (signUnit f hχ hQ : ℤ) • P τ +
          (P (atkinGL hQ • base) - (signUnit f hχ hQ : ℤ) • P base) := by
  obtain ⟨π, hπ, hd, hs⟩ := ParamJoin.algebraicParametrizationAtScale
    (f.toCuspFormGamma0 hχ) hf hLat hκ hr
  exact ⟨π, hπ, hd, hs, projectiveValue_transform_chart _ f hχ hQ Lat κ hLat π hπ hs⟩

/-- The basepoint at infinity of the actual chart, from its rational
formal arc. -/
def infinityPoint (N : ℕ) [NeZero N] : FieldPoint (X0Branch.model N).overQ ℚ :=
  ⟨X0Model.cusp N, by
    change X0Model.cusp N ≫ X0Model.overQ N = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ))
    rw [X0Model.cusp_overQ]
    simp⟩

/-- The rational generic-fibre statement still needed on the algebraic
model, expressed on field-valued points. At the based cusp `b` the
translation is the image of the rational point `W_Q b` under `π`
when `π b = 0`. The difference form keeps that normalization explicit
and is what specialization uses. -/
def BasedAtkinOnPoints {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (X : X0Model N) {hQ : Q ∥ N} (W : RationalAtkin X hQ)
    (π : X.X ⟶ Proj E.toProjective.grading) (hπ : π ≫ projectiveOverQ E = X.overQ)
    (b : FieldPoint X.overQ ℚ) (e : ℤ) : Prop :=
  ∀ (F : Type) [Field F] [Algebra ℚ F] (x : FieldPoint X.overQ F),
    let a := b.map (Algebra.ofId ℚ F)
    let P := fun y : FieldPoint X.overQ F => projectiveValue (y.comp π hπ).val
    P (x.comp W.hom W.overQ) - P (a.comp W.hom W.overQ) = e • (P x - P a)

set_option backward.isDefEq.respectTransparency false in
/-- The rational translation is the based difference of rational
values, transported by extension of fields. -/
theorem translatedAtkinOnPoints {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (X : X0Model N) {hQ : Q ∥ N} (W : RationalAtkin X hQ)
    (π : X.X ⟶ Proj E.toProjective.grading) (hπ : π ≫ projectiveOverQ E = X.overQ)
    (b : FieldPoint X.overQ ℚ) (e : ℤ) (h : BasedAtkinOnPoints X W π hπ b e)
    (F : Type) [Field F] [Algebra ℚ F] (x : FieldPoint X.overQ F) :
    let P := fun y : FieldPoint X.overQ F => projectiveValue (y.comp π hπ).val
    let c := projectiveValue ((b.comp W.hom W.overQ).comp π hπ).val -
      e • projectiveValue (b.comp π hπ).val
    P (x.comp W.hom W.overQ) = e • P x + Affine.Point.map (W' := E.toAffine) (Algebra.ofId ℚ F) c := by
  have hh := h F x
  dsimp only at hh ⊢
  let ι := Algebra.ofId ℚ F
  have hbase : Affine.Point.map (W' := E.toAffine) ι (projectiveValue (b.comp π hπ).val) =
      projectiveValue ((b.map ι).comp π hπ).val := by
    calc
      _ = projectiveValue (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ (b.comp π hπ).val) :=
        projectiveValue_map (E := E) ι (b.comp π hπ).val
      _ = _ := by simp only [FieldPoint.map, FieldPoint.comp, Category.assoc]
  have hmove : Affine.Point.map (W' := E.toAffine) ι
      (projectiveValue ((b.comp W.hom W.overQ).comp π hπ).val) =
        projectiveValue (((b.map ι).comp W.hom W.overQ).comp π hπ).val := by
    calc
      _ = projectiveValue (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫
          ((b.comp W.hom W.overQ).comp π hπ).val) :=
        projectiveValue_map (E := E) ι ((b.comp W.hom W.overQ).comp π hπ).val
      _ = _ := by simp only [FieldPoint.map, FieldPoint.comp, Category.assoc]
  rw [map_sub, map_zsmul, hbase, hmove]
  rw [zsmul_sub] at hh
  exact sub_eq_iff_eq_add.mp hh |>.trans (by abel)

/-- At the normalized cusp of the actual model the rational translation
is exactly the image of that cusp under the involution and parametrization. -/
theorem translatedAtkinAtInfinity {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {hQ : Q ∥ N} (W : RationalAtkin (X0Branch.model N) hQ)
    (π : (X0Branch.model N).X ⟶ Proj E.toProjective.grading)
    (hπ : π ≫ projectiveOverQ E = (X0Branch.model N).overQ)
    (e : ℤ) (h : BasedAtkinOnPoints (X0Branch.model N) W π hπ (infinityPoint N) e)
    (hzero : projectiveValue ((infinityPoint N).comp π hπ).val = 0)
    (F : Type) [Field F] [Algebra ℚ F] (x : FieldPoint (X0Branch.model N).overQ F) :
    projectiveValue ((x.comp W.hom W.overQ).comp π hπ).val =
      e • projectiveValue (x.comp π hπ).val +
        Affine.Point.map (W' := E.toAffine) (Algebra.ofId ℚ F)
          (projectiveValue (((infinityPoint N).comp W.hom W.overQ).comp π hπ).val) := by
  simpa only [hzero, zsmul_zero, sub_zero] using
    translatedAtkinOnPoints (X0Branch.model N) W π hπ (infinityPoint N) e h F x


end ZInQ.Manuscript.RC.AtkinPin
