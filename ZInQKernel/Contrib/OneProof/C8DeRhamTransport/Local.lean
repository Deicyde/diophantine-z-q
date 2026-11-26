import ZInQKernel.Contrib.G9.G9
import ZInQKernel.Contrib.G9.CoefDescent

/-! # Transport of the genuine local de Rham predicate

Finite coefficient extension makes the restricted `ℚ_p`-linear matrix action a
finite family of copies, as in the coefficient-independence argument for
Hodge–Tate weights. Here the equivariant maps are into the actual `B_dR`,
and their full rank, rather than HT multiplicities, is transported.
-/

noncomputable section

namespace ZInQ.Contrib.G9.C8DeRhamTransport

open PkgI4 Module

private theorem finrank_fin_fun' {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (d : ℕ) :
    finrank K (Fin d → V) = d * finrank K V := by
  rw [finrank, rank_fun_eq_lift_mul, Cardinal.toNat_mul, Cardinal.toNat_natCast,
    Cardinal.toNat_lift, Fintype.card_fin]
  rfl

/-- Over a finite coefficient extension, the actual matrix action is a family
of copies on the underlying base-field vectors. This counts equivariant maps
without assuming their space finite-dimensional. -/
private theorem finrank_Dsp_extend {K E F G B : Type*} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] [FiniteDimensional E F]
    [Group G] [AddCommGroup B] [Module K B] {n : ℕ} (act : G → B →ₗ[K] B)
    (M : G → Matrix (Fin n) (Fin n) E) (S : Set G) :
    finrank K (Dsp act (fun g => (Matrix.mulVecLin ((M g).map (algebraMap E F))).restrictScalars K) S) =
      finrank E F * finrank K (Dsp act (fun g => (Matrix.mulVecLin (M g)).restrictScalars K) S) := by
  classical
  let d := finrank E F
  let b : Basis (Fin d) E F := Module.finBasis E F
  let swap : (Fin n → Fin d → E) ≃ₗ[K] (Fin d → Fin n → E) :=
    { toFun := fun x j i => x i j
      invFun := fun x i j => x j i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let ΨE : (Fin n → F) ≃ₗ[E] (Fin n → Fin d → E) := LinearEquiv.piCongrRight fun _ => b.equivFun
  let Ψ : (Fin n → F) ≃ₗ[K] (Fin d → Fin n → E) := (ΨE.restrictScalars K).trans swap
  have hΨ : ∀ y j i, Ψ y j i = b.repr (y i) j := fun _ _ _ => rfl
  let ρ : G → (Fin n → E) →ₗ[K] (Fin n → E) := fun g => (Matrix.mulVecLin (M g)).restrictScalars K
  have hequiv : ∀ g y, Ψ ((Matrix.mulVecLin ((M g).map (algebraMap E F))).restrictScalars K y) =
      piRep ρ (Fin d) g (Ψ y) := by
    intro g y
    funext j i
    rw [hΨ, piRep_apply]
    simp only [ρ, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.map_apply, ← Algebra.smul_def, map_sum, map_smul, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rfl
  rw [finrank_Dsp_congr act _ (piRep ρ (Fin d)) S Ψ hequiv,
    (DspPiEquiv act ρ S (Fin d)).finrank_eq, finrank_fin_fun']

variable (p : ℕ) [Fact p.Prime] {n : ℕ}

/-- Transport full de Rham rank in either direction along an inclusion of
finite coefficient fields, provided the lifted matrices have the same entries
in the fixed algebraic closure. -/
theorem isDeRham_iff_of_le {E F : IntermediateField ℚ_[p] (PadicAlgCl p)} (hEF : E ≤ F)
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] F]
    (r : GQp p →* GL (Fin n) E) (s : GQp p →* GL (Fin n) F)
    (h : ∀ σ i j, ((s σ : Matrix (Fin n) (Fin n) F) i j : PadicAlgCl p) =
      ((r σ : Matrix (Fin n) (Fin n) E) i j : PadicAlgCl p)) :
    IsDeRham p r ↔ IsDeRham p s := by
  letI alg : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Module E F := alg.toModule
  haveI : Module.Free E F := Module.Free.of_divisionRing E F
  have hinc : ∀ a : E, ((algebraMap E F a : F) : PadicAlgCl p) = (a : PadicAlgCl p) := fun _ => rfl
  haveI : IsScalarTower ℚ_[p] E F := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    rw [hinc]
    rfl
  haveI : FiniteDimensional E F := FiniteDimensional.right ℚ_[p] E F
  have hmat : ∀ σ, (s σ : Matrix (Fin n) (Fin n) F) =
      (r σ : Matrix (Fin n) (Fin n) E).map (algebraMap E F) := fun σ =>
    Matrix.ext fun i j => Subtype.ext ((h σ i j).trans (hinc _).symm)
  have hD : finrank ℚ_[p] (ddrSpace p s) = finrank E F * finrank ℚ_[p] (ddrSpace p r) := by
    rw [ddrSpace_eq_DspAct, ddrSpace_eq_DspAct]
    have hs : (rRep p s : GQp p → (Fin n → F) →ₗ[ℚ_[p]] (Fin n → F)) =
        fun σ => (Matrix.mulVecLin ((r σ : Matrix (Fin n) (Fin n) E).map
          (algebraMap E F))).restrictScalars ℚ_[p] := by
      funext σ
      rw [← hmat]
      rfl
    rw [hs]
    exact finrank_Dsp_extend (bdrActHom p) (fun σ => (r σ : Matrix (Fin n) (Fin n) E)) Set.univ
  have hdeg : finrank ℚ_[p] F = finrank ℚ_[p] E * finrank E F :=
    (Module.finrank_mul_finrank ℚ_[p] E F).symm
  have hd : 0 < finrank E F := Module.finrank_pos
  unfold IsDeRham
  rw [hD, hdeg, ← Nat.mul_assoc, Nat.mul_comm (n * finrank ℚ_[p] E) (finrank E F)]
  exact ⟨congrArg ((finrank E F) * ·), Nat.eq_of_mul_eq_mul_left hd⟩

/-- Scalar extension of the actual matrices along a finite coefficient
inclusion preserves de Rhamness. -/
theorem isDeRham_extend {E F : IntermediateField ℚ_[p] (PadicAlgCl p)} (hEF : E ≤ F)
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] F]
    (r : GQp p →* GL (Fin n) E) (hdr : IsDeRham p r) :
    IsDeRham p ((Matrix.GeneralLinearGroup.map (IntermediateField.inclusion hEF).toRingHom).comp r) :=
  (isDeRham_iff_of_le p hEF r _ (fun _ _ _ => rfl)).mp hdr

private theorem lift_entry {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {r : GQp p →* GL (Fin n) (PadicAlgCl p)} (rE : GQp p →* GL (Fin n) E)
    (h : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (rE σ) = r σ)
    (σ : GQp p) (i j : Fin n) :
    ((rE σ : Matrix (Fin n) (Fin n) E) i j : PadicAlgCl p) =
      (r σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j := by
  rw [← h σ]
  rfl

/-- The de Rham condition holds on any specified finite lift of the same
matrices, not just on the lift originally used by `LocalIsDeRham`. -/
theorem localIsDeRham_iff_of_lift (r : GQp p →* GL (Fin n) (PadicAlgCl p))
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    (rE : GQp p →* GL (Fin n) E)
    (hrE : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (rE σ) = r σ) :
    LocalIsDeRham p n r ↔ IsDeRham p rE := by
  refine ⟨?_, fun h => ⟨E, inferInstance, rE, hrE, h⟩⟩
  rintro ⟨F, hF, rF, hrF, h⟩
  letI : FiniteDimensional ℚ_[p] F := hF
  let L := F ⊔ E
  have hmem (σ : GQp p) (i j : Fin n) : (r σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ L := by
    rw [← lift_entry p rF hrF σ i j]
    exact (le_sup_left : F ≤ L) ((rF σ : Matrix (Fin n) (Fin n) F) i j).2
  let rL := liftGL L r hmem
  have extendF := isDeRham_iff_of_le p (le_sup_left : F ≤ L) rF rL
    (fun σ i j => (liftGL_coe L r hmem σ i j).trans (lift_entry p rF hrF σ i j).symm)
  have extendE := isDeRham_iff_of_le p (le_sup_right : E ≤ L) rE rL
    (fun σ i j => (liftGL_coe L r hmem σ i j).trans (lift_entry p rE hrE σ i j).symm)
  exact extendE.mpr (extendF.mp h)

/-- Conjugation by inverse matrices over a finite coefficient field preserves
the full rank of the equivariant maps into `B_dR`. -/
theorem isDeRham_iff_of_matrix_conj {E : Type*} [Field E] [Algebra ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E] (r s : GQp p →* GL (Fin n) E)
    (P Q : Matrix (Fin n) (Fin n) E) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (h : ∀ σ, (r σ : Matrix (Fin n) (Fin n) E) = P * (s σ : Matrix (Fin n) (Fin n) E) * Q) :
    IsDeRham p r ↔ IsDeRham p s := by
  let e : (Fin n → E) ≃ₗ[ℚ_[p]] (Fin n → E) :=
    { toFun := fun v => Q.mulVec v
      invFun := fun v => P.mulVec v
      map_add' := fun v w => Matrix.mulVec_add _ _ _
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [show c • v = algebraMap ℚ_[p] E c • v from (algebraMap_smul E c v).symm,
          Matrix.mulVec_smul, algebraMap_smul]
      left_inv := fun v => by simp only [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
      right_inv := fun v => by simp only [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec] }
  have he : ∀ σ v, e (rRep p r σ v) = rRep p s σ (e v) := by
    intro σ v
    change Q.mulVec ((r σ : Matrix (Fin n) (Fin n) E).mulVec v) =
      (s σ : Matrix (Fin n) (Fin n) E).mulVec (Q.mulVec v)
    rw [h σ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc, hQP, one_mul]
  unfold IsDeRham
  rw [ddrSpace_eq_DspAct, ddrSpace_eq_DspAct,
    finrank_Dsp_congr (bdrActHom p) (rRep p r) (rRep p s) Set.univ e he]

/-- If `r = P s P⁻¹` on the original local Galois group, transport de Rhamness
from `r` to `s`, adjoining the actual entries of `P` and `P⁻¹` as needed. -/
theorem localIsDeRham_of_conj (r s : GQp p →* GL (Fin n) (PadicAlgCl p))
    (P : GL (Fin n) (PadicAlgCl p)) (hP : ∀ σ, r σ = P * s σ * P⁻¹)
    (hdr : LocalIsDeRham p n r) : LocalIsDeRham p n s := by
  obtain ⟨E, hE, rE, hrE, hdrE⟩ := hdr
  letI : FiniteDimensional ℚ_[p] E := hE
  classical
  let Pm := (P : Matrix (Fin n) (Fin n) (PadicAlgCl p))
  let Qm := ((P⁻¹ : GL (Fin n) (PadicAlgCl p)) : Matrix (Fin n) (Fin n) (PadicAlgCl p))
  let X : Set (PadicAlgCl p) := (Set.range fun ij : Fin n × Fin n => Pm ij.1 ij.2) ∪
    Set.range fun ij : Fin n × Fin n => Qm ij.1 ij.2
  haveI : Finite X := (Set.finite_range _ |>.union (Set.finite_range _)).to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] X) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let F := E ⊔ IntermediateField.adjoin ℚ_[p] X
  have hPm : ∀ i j, Pm i j ∈ F := fun i j =>
    (le_sup_right : _ ≤ F) (IntermediateField.subset_adjoin _ _ (Or.inl ⟨(i, j), rfl⟩))
  have hQm : ∀ i j, Qm i j ∈ F := fun i j =>
    (le_sup_right : _ ≤ F) (IntermediateField.subset_adjoin _ _ (Or.inr ⟨(i, j), rfl⟩))
  have hrmem (σ : GQp p) (i j : Fin n) : (r σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ F := by
    rw [← lift_entry p rE hrE σ i j]
    exact (le_sup_left : E ≤ F) ((rE σ : Matrix (Fin n) (Fin n) E) i j).2
  have hseq (σ : GQp p) : (s σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) =
      Qm * (r σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) * Pm := by
    have hs : s σ = P⁻¹ * r σ * P := by rw [hP]; group
    rw [hs]
    rfl
  have hsmem (σ : GQp p) (i j : Fin n) : (s σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ F := by
    rw [hseq]
    simp only [Matrix.mul_apply]
    refine F.sum_mem fun k _ => F.mul_mem ?_ (hPm k j)
    exact F.sum_mem fun m _ => F.mul_mem (hQm i m) (hrmem σ m k)
  let rF := liftGL F r hrmem
  let sF := liftGL F s hsmem
  let PF : Matrix (Fin n) (Fin n) F := fun i j => ⟨Pm i j, hPm i j⟩
  let QF : Matrix (Fin n) (Fin n) F := fun i j => ⟨Qm i j, hQm i j⟩
  let ι := algebraMap F (PadicAlgCl p)
  have hinj := Matrix.map_injective (m := Fin n) (n := Fin n) ι.injective
  have hPF : PF.map ι = Pm := by ext; rfl
  have hQF : QF.map ι = Qm := by ext; rfl
  have hQP : QF * PF = 1 := hinj (by
    simp only [Matrix.map_mul, hPF, hQF, Matrix.map_one _ (map_zero _) (map_one _)]
    simp [Qm, Pm])
  have hPQ : PF * QF = 1 := hinj (by
    simp only [Matrix.map_mul, hPF, hQF, Matrix.map_one _ (map_zero _) (map_one _)]
    simp [Qm, Pm])
  have hrmap (σ : GQp p) : (rF σ : Matrix (Fin n) (Fin n) F).map ι = r σ := by ext; rfl
  have hsmap (σ : GQp p) : (sF σ : Matrix (Fin n) (Fin n) F).map ι = s σ := by ext; rfl
  have hconj (σ : GQp p) : (sF σ : Matrix (Fin n) (Fin n) F) =
      QF * (rF σ : Matrix (Fin n) (Fin n) F) * PF :=
    hinj (by simp only [Matrix.map_mul, hsmap, hrmap, hPF, hQF, hseq])
  refine ⟨F, inferInstance, sF, liftGL_map F s hsmem, ?_⟩
  apply (isDeRham_iff_of_matrix_conj p sF rF QF PF hPQ hQP hconj).mpr
  apply (isDeRham_iff_of_le p (le_sup_left : E ≤ F) rE rF ?_).mp hdrE
  exact fun σ i j => (liftGL_coe F r hrmem σ i j).trans (lift_entry p rE hrE σ i j).symm

/-- Conjugacy over the original algebraic closure preserves the genuine
local predicate in either direction. -/
theorem localIsDeRham_iff_of_conj (r s : GQp p →* GL (Fin n) (PadicAlgCl p))
    (P : GL (Fin n) (PadicAlgCl p)) (hP : ∀ σ, r σ = P * s σ * P⁻¹) :
    LocalIsDeRham p n r ↔ LocalIsDeRham p n s := by
  refine ⟨localIsDeRham_of_conj p r s P hP, localIsDeRham_of_conj p s r P⁻¹ ?_⟩
  intro σ
  rw [hP]
  group

end ZInQ.Contrib.G9.C8DeRhamTransport
