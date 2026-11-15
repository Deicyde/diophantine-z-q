import RayDefs

/-! # rayclass-cft, Part P1: algebra of `ι : B → M₂(ℝ)`, fixed points, field-theoretic lemmas -/

set_option linter.all false

noncomputable section

namespace RayClassCFT

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT

/-! ## P1a. `ι` is a `ℚ`-algebra map with `det ι(x) = nrd x` -/

open BPAnalytic.QM in
theorem iota_eq (x : LeafQM.B) : BPAnalytic.QM.iota x =
    !![(x.re : ℝ) + x.imI * √2, -3 * x.imJ - 3 * x.imK * √2;
       (x.imJ : ℝ) - x.imK * √2, (x.re : ℝ) - x.imI * √2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [BPAnalytic.QM.iota, Mi, Mj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem iota_add (x y : LeafQM.B) :
    BPAnalytic.QM.iota (x + y) = BPAnalytic.QM.iota x + BPAnalytic.QM.iota y := by
  rw [iota_eq, iota_eq, iota_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem iota_smul (r : ℚ) (x : LeafQM.B) :
    BPAnalytic.QM.iota (r • x) = (r : ℝ) • BPAnalytic.QM.iota x := by
  rw [iota_eq, iota_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem iota_algebraMap (r : ℚ) :
    BPAnalytic.QM.iota (algebraMap ℚ LeafQM.B r) = (r : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [iota_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem sqrt2_sq : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem iota_mul (x y : LeafQM.B) :
    BPAnalytic.QM.iota (x * y) = BPAnalytic.QM.iota x * BPAnalytic.QM.iota y := by
  rw [iota_eq, iota_eq, iota_eq]
  have h := sqrt2_sq
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · first | linear_combination ((x.imI : ℝ) * y.imI + 3 * x.imK * y.imK) * h
          | linear_combination (-((x.imI : ℝ) * y.imI + 3 * x.imK * y.imK)) * h
  · first | linear_combination (-3 * (x.imI : ℝ) * y.imK + 3 * x.imK * y.imI) * h
          | linear_combination (-(-3 * (x.imI : ℝ) * y.imK + 3 * x.imK * y.imI)) * h
  · first | linear_combination ((x.imI : ℝ) * y.imK - x.imK * y.imI) * h
          | linear_combination (-((x.imI : ℝ) * y.imK - x.imK * y.imI)) * h
  · first | linear_combination ((x.imI : ℝ) * y.imI + 3 * x.imK * y.imK) * h
          | linear_combination (-((x.imI : ℝ) * y.imI + 3 * x.imK * y.imK)) * h

theorem det_iota (x : LeafQM.B) :
    (BPAnalytic.QM.iota x).det = (ShimuraGlue.nrdQ ℚ x : ℝ) := by
  rw [iota_eq, Matrix.det_fin_two_of, ShimuraGlue.nrdQ_apply]
  have h := sqrt2_sq
  push_cast
  linear_combination (-(x.imI : ℝ) ^ 2 - 3 * (x.imK : ℝ) ^ 2) * h


/-! ## P1b. A real `2 × 2` matrix with a non-real eigenvector `(τ, 1)ᵀ` -/

theorem eig_coords {N : Matrix (Fin 2) (Fin 2) ℝ} {τ lam : ℂ}
    (h : Matrix.mulVec (N.map (algebraMap ℝ ℂ)) ![τ, 1] = lam • ![τ, 1]) :
    (N 0 0 : ℂ) * τ + N 0 1 = lam * τ ∧ (N 1 0 : ℂ) * τ + N 1 1 = lam := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  exact ⟨h0, h1⟩

/-- `det N = (a − c x)² + c² y²` for `N = [[a, b], [c, d]]` with eigenvector `(x + iy, 1)ᵀ`. -/
theorem det_nonneg_of_eig {N : Matrix (Fin 2) (Fin 2) ℝ} {τ lam : ℂ} (hτ : τ.im ≠ 0)
    (h : Matrix.mulVec (N.map (algebraMap ℝ ℂ)) ![τ, 1] = lam • ![τ, 1]) : 0 ≤ N.det := by
  obtain ⟨e0, e1⟩ := eig_coords h
  rw [← e1] at e0
  have hre := congrArg Complex.re e0
  have him := congrArg Complex.im e0
  simp [Complex.mul_re, Complex.mul_im] at hre him
  set a := N 0 0; set b := N 0 1; set c := N 1 0; set d := N 1 1
  set x := τ.re; set y := τ.im
  have hd : d = a - 2 * c * x := by
    have : y * (a - 2 * c * x - d) = 0 := by linear_combination him
    have := (mul_eq_zero.mp this).resolve_left hτ
    linear_combination -this
  have hdet : N.det = (a - c * x) ^ 2 + c ^ 2 * y ^ 2 := by
    rw [Matrix.det_fin_two]
    linear_combination (-c) * hre + (a - c * x) * hd
  rw [hdet]; positivity

theorem det_pos_of_eig {N : Matrix (Fin 2) (Fin 2) ℝ} {τ lam : ℂ} (hτ : τ.im ≠ 0)
    (h : Matrix.mulVec (N.map (algebraMap ℝ ℂ)) ![τ, 1] = lam • ![τ, 1]) (h0 : N.det ≠ 0) : 0 < N.det :=
  lt_of_le_of_ne (det_nonneg_of_eig hτ h) (Ne.symm h0)

/-- **`M ∈ GL₂(ℝ)` with eigenvector `(τ, 1)ᵀ` fixes `τ ∈ ℍ`.** -/
theorem smul_eq_of_eig (M : GL (Fin 2) ℝ) (τ : UpperHalfPlane) {lam : ℂ}
    (h : Matrix.mulVec ((M : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ)) ![(τ : ℂ), 1] =
      lam • ![(τ : ℂ), 1]) : M • τ = τ := by
  have hpos : 0 < (M : Matrix (Fin 2) (Fin 2) ℝ).det :=
    det_pos_of_eig τ.im_pos.ne' h (by
      have := M.det.ne_zero; simpa [Matrix.GeneralLinearGroup.val_det_apply] using this)
  obtain ⟨e0, e1⟩ := eig_coords h
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa [Matrix.GeneralLinearGroup.val_det_apply] using hpos)]
  have hden : UpperHalfPlane.denom M τ = lam := e1
  have hnum : UpperHalfPlane.num M τ = lam * τ := e0
  have hl : lam ≠ 0 := by rw [← hden]; exact UpperHalfPlane.denom_ne_zero M τ
  rw [hnum, hden]; field_simp

/-! ## P1c. Points over `ℚ̄` and `ℂ`, residue fields, Galois descent -/

/-- The fixed embedding `ℚ̄ → ℂ`. -/
def ιC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift

/-- A map of an algebraic extension of `ℚ` to `ℂ` factors through `ιC`. -/
theorem exists_lift_ringHom {L : Type} [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    (f : L →+* ℂ) : ∃ g : L →+* Qbar, ∀ x, ιC (g x) = f x := by
  letI : Algebra Qbar ℂ := (ιC : Qbar →+* ℂ).toAlgebra
  have hrange : ∀ x : L, ∃ b : Qbar, ιC b = f x := by
    intro x
    have h1 : IsAlgebraic ℚ (f x) := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom f.toRatAlgHom
    have h2 : IsAlgebraic Qbar (f x) := h1.extendScalars (algebraMap ℚ Qbar).injective
    obtain ⟨b, hb⟩ := T5Glue.mem_range_of_isAlgebraic h2
    exact ⟨b, hb⟩
  choose g hg using hrange
  have hinj : Function.Injective (ιC : Qbar → ℂ) := (ιC : Qbar →+* ℂ).injective
  refine ⟨{ toFun := g
            map_one' := hinj (by rw [hg, map_one, map_one])
            map_mul' := fun x y => hinj (by rw [hg, map_mul, map_mul, hg, hg])
            map_zero' := hinj (by rw [hg, map_zero, map_zero])
            map_add' := fun x y => hinj (by rw [hg, map_add, map_add, hg, hg]) }, hg⟩

theorem sigma_comp_inj {X : Scheme.{0}} {K L : Type} [Field K] [Field L] (f : K →+* L)
    (p q : Σ x : X, X.residueField x ⟶ CommRingCat.of K)
    (h : (⟨p.1, p.2 ≫ CommRingCat.ofHom f⟩ : Σ x : X, X.residueField x ⟶ CommRingCat.of L) =
      ⟨q.1, q.2 ≫ CommRingCat.ofHom f⟩) : p = q := by
  obtain ⟨x, ρ⟩ := p
  obtain ⟨x', ρ'⟩ := q
  simp only [Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have h3 := eq_of_heq h2
  have hr : ∀ r, f (ρ.hom r) = f (ρ'.hom r) := fun r => by
    simpa using congrArg (fun φ => φ.hom r) h3
  have : ρ = ρ' := CommRingCat.hom_ext (RingHom.ext fun r => f.injective (hr r))
  rw [this]

theorem sigma_fix {X : Scheme.{0}} {K : Type} [Field K] (f : K →+* K)
    (p : Σ x : X, X.residueField x ⟶ CommRingCat.of K)
    (h : (⟨p.1, p.2 ≫ CommRingCat.ofHom f⟩ : Σ x : X, X.residueField x ⟶ CommRingCat.of K) = p) :
    ∀ r, f (p.2.hom r) = p.2.hom r := by
  obtain ⟨x, ρ⟩ := p
  simp only [Sigma.mk.injEq, true_and] at h
  have h3 := eq_of_heq h
  intro r
  simpa using congrArg (fun φ => φ.hom r) h3

theorem fieldMap_left {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L) :
    (fieldMap f).left = Spec.map (CommRingCat.ofHom (f : K →+* L)) := rfl

/-- `y ↦ ιC^* y` is injective on `ℚ̄`-points. -/
theorem fieldMap_ιC_inj {Y : Over (Spec (CommRingCat.of ℚ))} {a b : fieldPt Qbar ⟶ Y}
    (h : fieldMap ιC ≫ a = fieldMap ιC ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  have h1 := congrArg CommaMorphism.left h
  simp only [Over.comp_left, fieldMap_left] at h1
  have h2 := congrArg (Scheme.SpecToEquivOfField ℂ Y.left) h1
  have e1 := specToEquivOfField_comp (ιC : Qbar →+* ℂ) a.left
  have e2 := specToEquivOfField_comp (ιC : Qbar →+* ℂ) b.left
  have h3 := sigma_comp_inj (ιC : Qbar →+* ℂ) _ _ (e1.symm.trans (h2.trans e2))
  exact (Scheme.SpecToEquivOfField Qbar Y.left).injective h3

/-- The Galois action on `ℂ`-points of `ιC^* y` is that of `ℚ̄` when `σ̃` extends `σ`. -/
theorem galPt_fieldMap {Y : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt Qbar ⟶ Y)
    (σ : Qbar ≃ₐ[ℚ] Qbar) (σC : ℂ ≃+* ℂ) (hσ : ∀ a, σC (ιC a) = ιC (σ a)) :
    galPt σC (fieldMap ιC ≫ y) = fieldMap ιC ≫ (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y) := by
  unfold galPt
  rw [← Category.assoc, ← Category.assoc]
  have e : fieldMap ((σC : ℂ →+* ℂ).toRatAlgHom) ≫ fieldMap ιC =
      fieldMap ιC ≫ fieldMap (σ : Qbar →ₐ[ℚ] Qbar) := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, fieldMap_left]
    have key : (Spec.map (CommRingCat.ofHom ((σC : ℂ →+* ℂ).toRatAlgHom : ℂ →+* ℂ)) ≫
        Spec.map (CommRingCat.ofHom (ιC : Qbar →+* ℂ)) :
          Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of Qbar)) =
        Spec.map (CommRingCat.ofHom (ιC : Qbar →+* ℂ)) ≫
          Spec.map (CommRingCat.ofHom ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun a => hσ a
    exact key
  rw [e]

/-- A `ℚ̄`-point fixed by `σ` has its residue field fixed by `σ`. -/
theorem residue_fixed {X : Scheme.{0}} (y : Spec (CommRingCat.of Qbar) ⟶ X) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (h : Spec.map (CommRingCat.ofHom ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫ y = y) :
    ∀ r, σ ((Scheme.SpecToEquivOfField Qbar X y).2.hom r) =
      (Scheme.SpecToEquivOfField Qbar X y).2.hom r := by
  have h2 := congrArg (Scheme.SpecToEquivOfField Qbar X) h
  rw [specToEquivOfField_comp ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar) y] at h2
  exact sigma_fix _ _ h2

/-- **Galois descent of the residue field**: if every `σ` fixing `F` fixes `y`, then `ℚ(y) ⊆ F`. -/
theorem residueImage_le {X : Scheme.{0}} (y : Spec (CommRingCat.of Qbar) ⟶ X)
    (F : IntermediateField ℚ Qbar)
    (h : ∀ σ ∈ F.fixingSubgroup,
      Spec.map (CommRingCat.ofHom ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫ y = y) :
    residueImage y ≤ F := by
  rw [residueImage, IntermediateField.adjoin_le_iff]
  rintro _ ⟨r, rfl⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup F, SetLike.mem_coe,
    IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact residue_fixed y σ (h σ hσ) r

end RayClassCFT
