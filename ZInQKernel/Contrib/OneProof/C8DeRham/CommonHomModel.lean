import ZInQKernel.Contrib.OneProof.C8DeRham.BdRHomPeriod

/-! # A common finite coefficient model of the actual C8 intertwiner

No conjugacy of different models is postulated: all matrices map pointwise to
the given ones in the original algebraic closure. The finite field is the
normal closure of the compositum of the given fields and the entries of T.
-/

noncomputable section

namespace C8HomModel

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4

variable {p : ℕ} [Fact p.Prime] {n : ℕ}
variable {E F : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- Extend a matrix action along an inclusion of actual coefficient fields. -/
abbrev extendModel (h : E ≤ F) (r : GQp p →* GL (Fin n) E) : GQp p →* GL (Fin n) F :=
  (Matrix.GeneralLinearGroup.map (IntermediateField.inclusion h).toRingHom).comp r

/-- Extend the coefficient character along the same inclusion. -/
abbrev extendCharacter (h : E ≤ F) (χ : GQp p →* Eˣ) : GQp p →* Fˣ :=
  (Units.map (IntermediateField.inclusion h).toRingHom.toMonoidHom).comp χ

theorem map_extendModel (h : E ≤ F) (r : GQp p →* GL (Fin n) E) (σ : GQp p) :
    Matrix.GeneralLinearGroup.map (algebraMap F (PadicAlgCl p)) (extendModel h r σ) =
      Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (r σ) := by
  apply Units.ext
  ext i j
  rfl

/-- A single matrix lifts into the finite field once its entries do. -/
theorem exists_GL_model (T : GL (Fin n) (PadicAlgCl p))
    (h : ∀ i j, (T : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E) :
    ∃ U : GL (Fin n) E, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) U = T := by
  let U : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => ⟨(T : Matrix _ _ _) i j, h i j⟩
  have he : U.map (algebraMap E (PadicAlgCl p)) = (T : Matrix _ _ _) := by
    ext i j
    rfl
  have hdet : U.det ≠ 0 := by
    intro hz
    have hT : (T : Matrix (Fin n) (Fin n) (PadicAlgCl p)).det = (algebraMap E (PadicAlgCl p)) U.det := by
      have hmap := (RingHom.map_det (algebraMap E (PadicAlgCl p)) U).symm
      change (U.map (algebraMap E (PadicAlgCl p))).det = _ at hmap
      exact (congrArg Matrix.det he).symm.trans hmap
    exact Matrix.GeneralLinearGroup.det_ne_zero T (by rw [hT, hz, map_zero])
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero U hdet, ?_⟩
  apply Units.ext
  exact he

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- The lifted intertwiner satisfies the same equation over one finite Galois
field. Equality is verified by the injective scalar embedding. -/
theorem exists_common_hom_model
    (R D C : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] R] [FiniteDimensional ℚ_[p] D] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin n) R) (ρ : GQp p →* GL (Fin n) D) (χ : GQp p →* Cˣ)
    (T : GL (Fin n) (PadicAlgCl p))
    (ht : ∀ σ,
      (Matrix.GeneralLinearGroup.map (algebraMap R (PadicAlgCl p)) (r σ) :
        Matrix (Fin n) (Fin n) (PadicAlgCl p)) * (T : Matrix (Fin n) (Fin n) (PadicAlgCl p)) =
      (((χ σ : Cˣ) : C) : PadicAlgCl p) •
        ((T : Matrix (Fin n) (Fin n) (PadicAlgCl p)) *
          (↑(Matrix.GeneralLinearGroup.map (algebraMap D (PadicAlgCl p)) (ρ σ)) :
            Matrix (Fin n) (Fin n) (PadicAlgCl p)))) :
    ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
      (_ : IsGalois ℚ_[p] E) (hr : R ≤ E) (hρ : D ≤ E) (hχ : C ≤ E) (T' : GL (Fin n) E),
      Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) T' = T ∧
      ∀ σ, (extendModel hr r σ : Matrix (Fin n) (Fin n) E) * (T' : Matrix (Fin n) (Fin n) E) =
        (extendCharacter hχ χ σ : E) •
          ((T' : Matrix (Fin n) (Fin n) E) * (extendModel hρ ρ σ : Matrix (Fin n) (Fin n) E)) := by
  classical
  let X := Set.range (fun ij : Fin n × Fin n => (T : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ij.1 ij.2)
  letI : Finite X := (Set.finite_range _).to_subtype
  let M := IntermediateField.adjoin ℚ_[p] X
  letI : FiniteDimensional ℚ_[p] M := IntermediateField.finiteDimensional_adjoin
    fun x _ => Algebra.IsIntegral.isIntegral x
  let U := ((R ⊔ D) ⊔ C) ⊔ M
  let E := IntermediateField.normalClosure ℚ_[p] U (PadicAlgCl p)
  letI : FiniteDimensional ℚ_[p] U := inferInstance
  letI : FiniteDimensional ℚ_[p] E := normalClosure.is_finiteDimensional ℚ_[p] U (PadicAlgCl p)
  letI : IsGalois ℚ_[p] E := IsGalois.normalClosure ℚ_[p] U (PadicAlgCl p)
  have hUE : U ≤ E := IntermediateField.le_normalClosure U
  have hr : R ≤ E := le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hUE))
  have hρ : D ≤ E := le_sup_right.trans (le_sup_left.trans (le_sup_left.trans hUE))
  have hχ : C ≤ E := le_sup_right.trans (le_sup_left.trans hUE)
  have hME : M ≤ E := le_sup_right.trans hUE
  obtain ⟨T', hT'⟩ := exists_GL_model (E := E) T fun i j =>
    hME (IntermediateField.subset_adjoin ℚ_[p] _ (show (T : Matrix _ _ _) i j ∈ X from ⟨(i, j), rfl⟩))
  refine ⟨E, inferInstance, inferInstance, hr, hρ, hχ, T', hT', fun σ => ?_⟩
  let f := algebraMap E (PadicAlgCl p)
  apply Matrix.map_injective f.injective
  have he (A : GL (Fin n) E) : (A : Matrix (Fin n) (Fin n) E).map f =
      (Matrix.GeneralLinearGroup.map f A : Matrix (Fin n) (Fin n) (PadicAlgCl p)) := rfl
  have hs (c : E) (A : Matrix (Fin n) (Fin n) E) : (c • A).map f = f c • A.map f := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  change ((extendModel hr r σ : Matrix (Fin n) (Fin n) E) * (T' : Matrix (Fin n) (Fin n) E)).map f =
    ((extendCharacter hχ χ σ : E) • ((T' : Matrix (Fin n) (Fin n) E) *
      (extendModel hρ ρ σ : Matrix (Fin n) (Fin n) E))).map f
  rw [hs, Matrix.map_mul, Matrix.map_mul, he, he, he, map_extendModel, map_extendModel, hT']
  exact ht σ

end C8HomModel
