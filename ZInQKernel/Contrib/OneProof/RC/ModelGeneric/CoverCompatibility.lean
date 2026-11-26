import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.CoverBaseChange
import Batteries.Tactic.OpenPrivate
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ShortLevelAction
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.UnitActionBaseChange

/-! # Compatibility of the scalar extension of the marked short cover -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open ModelTorsion Algebra
open scoped TensorProduct

open private exactOrderCurveCongr shortCoverBaseChange_tmul_one
  shortCoverCoefficientBaseChange_algebraMap from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric.CoverBaseChange

section Exact

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {n : ℕ} (W : WeierstrassCurve A) [W.IsElliptic] (hn : IsUnit ((n + 2 : ℕ) : A))

private theorem exactOrderCurveCongr_xy {V V' : WeierstrassCurve B}
    [V.IsElliptic] [V'.IsElliptic] (h : V = V') (hN : IsUnit ((n + 2 : ℕ) : B)) :
    exactOrderCurveCongr h hN (exactOrderX V hN) = exactOrderX V' hN ∧
      exactOrderCurveCongr h hN (exactOrderY V hN) = exactOrderY V' hN := by
  cases h
  exact ⟨rfl, rfl⟩

private theorem exactOrderCurveCongr_units [IsDomain B] {V V' : WeierstrassCurve B}
    [V.IsElliptic] [V'.IsElliptic] (h : V = V') (hN : IsUnit ((n + 2 : ℕ) : B))
    (a : (ZMod (n + 2))ˣ) (x : ExactOrderAlgebra V hN) :
    exactOrderCurveCongr h hN ((levelUnitAut V hN (by omega) a) x) =
      (levelUnitAut V' hN (by omega) a) (exactOrderCurveCongr h hN x) := by
  cases h
  rfl

end Exact

private theorem shortDiscriminant_mul_inv (T : Type*) [CommRing T] :
    (shortFamily T).Δ * IsLocalization.Away.invSelf (shortEquation T).Δ = 1 := by
  rw [shortFamily, map_Δ]
  exact IsLocalization.Away.mul_invSelf (shortEquation T).Δ

private theorem j_congr {B : Type*} [CommRing B] {V W : WeierstrassCurve B}
    [V.IsElliptic] [W.IsElliptic] (h : V = W) : V.j = W.j := by
  cases h
  rfl

section Short

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : ShortBase R))
  (hB : IsUnit ((n + 2 : ℕ) : ShortBase B))
  [Algebra R (ExactOrderAlgebra (shortFamily R) hn)]
  [IsScalarTower R (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)]
  [Algebra B (ExactOrderAlgebra (shortFamily B) hB)]
  [IsScalarTower B (ShortBase B) (ExactOrderAlgebra (shortFamily B) hB)]

/-- The marked abscissa and ordinate commute with coefficient extension. -/
private theorem shortCoverCoefficientBaseChange_xy :
    shortCoverCoefficientBaseChange hn hB
      ((1 : ShortBase B) ⊗ₜ[ShortBase R] exactOrderX (shortFamily R) hn) =
        exactOrderX (shortFamily B) hB ∧
    shortCoverCoefficientBaseChange hn hB
      ((1 : ShortBase B) ⊗ₜ[ShortBase R] exactOrderY (shortFamily R) hn) =
        exactOrderY (shortFamily B) hB := by
  simp only [shortCoverCoefficientBaseChange, AlgEquiv.trans_apply]
  unfold exactOrderX exactOrderY
  rw [exactOrderBaseChange_affine, exactOrderBaseChange_affine, affineTorsionBaseChange_x,
    affineTorsionBaseChange_y]
  exact exactOrderCurveCongr_xy shortFamily_map_shortBaseMap hB

/-- The canonical base change carries the five weighted coordinates to the corresponding
weighted coordinates over the new base. -/
theorem shortCoverBaseChange_coordinates (i : Fin 5) :
    shortCoverBaseChange hn hB ((1 : B) ⊗ₜ[R] exactOrderShortCoordinates hn i) =
      exactOrderShortCoordinates hB i := by
  rw [shortCoverBaseChange_tmul_one]
  have hW := shortFamily_map_shortBaseMap (R := R) (B := B)
  have h₄ := congrArg WeierstrassCurve.a₄ hW
  have h₆ := congrArg WeierstrassCurve.a₆ hW
  fin_cases i
  · exact (shortCoverCoefficientBaseChange_algebraMap hn hB _).trans
      (congrArg (algebraMap (ShortBase B) _) h₄)
  · exact (shortCoverCoefficientBaseChange_algebraMap hn hB _).trans
      (congrArg (algebraMap (ShortBase B) _) h₆)
  · exact (shortCoverCoefficientBaseChange_xy hn hB).1
  · exact (shortCoverCoefficientBaseChange_xy hn hB).2
  · let f := algebraMap (ShortBase R) (ShortBase B)
    have hΔ : f (shortFamily R).Δ = (shortFamily B).Δ := by
      rw [← map_Δ, hW]
    have hinv : f (IsLocalization.Away.invSelf (shortEquation R).Δ) =
        IsLocalization.Away.invSelf (shortEquation B).Δ := by
      apply (shortFamily B).isUnit_Δ.mul_left_cancel
      calc
        (shortFamily B).Δ * f (IsLocalization.Away.invSelf (shortEquation R).Δ) =
            f ((shortFamily R).Δ * IsLocalization.Away.invSelf (shortEquation R).Δ) := by
              rw [map_mul, hΔ]
        _ = 1 := by rw [shortDiscriminant_mul_inv R, map_one]
        _ = _ := (shortDiscriminant_mul_inv B).symm
    exact (shortCoverCoefficientBaseChange_algebraMap hn hB _).trans
      (congrArg (algebraMap (ShortBase B) _) hinv)

/-- Scalar extension of the marked cover preserves the actual source j-invariant. -/
theorem shortCoverBaseChange_j :
    shortCoverBaseChange hn hB ((1 : B) ⊗ₜ[R]
      algebraMap (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn) (shortFamily R).j) =
    algebraMap (ShortBase B) (ExactOrderAlgebra (shortFamily B) hB) (shortFamily B).j := by
  rw [shortCoverBaseChange_tmul_one, shortCoverCoefficientBaseChange_algebraMap]
  apply congrArg (algebraMap (ShortBase B) (ExactOrderAlgebra (shortFamily B) hB))
  exact ((shortFamily R).map_j (algebraMap (ShortBase R) (ShortBase B))).symm.trans
    (j_congr shortFamily_map_shortBaseMap)

set_option backward.isDefEq.respectTransparency false in
private theorem shortCoverBaseChange_presentation (p : MvPolynomial (Fin 5) R) :
    shortCoverBaseChange hn hB ((1 : B) ⊗ₜ[R] exactOrderShortPresentation hn p) =
      exactOrderShortPresentation hB (MvPolynomial.map (algebraMap R B) p) := by
  let T := ExactOrderAlgebra (shortFamily B) hB
  letI : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra
  letI : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f := (shortCoverBaseChange hn hB).toAlgHom.restrictScalars R
  let i : ExactOrderAlgebra (shortFamily R) hn →ₐ[R]
      B ⊗[R] ExactOrderAlgebra (shortFamily R) hn := Algebra.TensorProduct.includeRight
  let g := (exactOrderShortPresentation hB).restrictScalars R
  let b := MvPolynomial.mapAlgHom (σ := Fin 5) (Algebra.ofId R B)
  change (f.comp (i.comp (exactOrderShortPresentation hn))) p = (g.comp b) p
  have he : f.comp (i.comp (exactOrderShortPresentation hn)) = g.comp b := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa only [i, b, g, f, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      AlgEquiv.coe_toAlgHom, exactOrderShortPresentation, MvPolynomial.aeval_X,
      MvPolynomial.mapAlgHom_apply, MvPolynomial.map_X,
      Algebra.TensorProduct.includeRight_apply] using shortCoverBaseChange_coordinates hn hB j
  rw [he]

/-- Scalar extension of the marked cover preserves the graded components. -/
theorem shortCoverBaseChange_mem (i : ℤ) {x : B ⊗[R] ExactOrderAlgebra (shortFamily R) hn}
    (hx : x ∈ (shortExactOrderGrading hn i).baseChange B) :
    shortCoverBaseChange hn hB x ∈ shortExactOrderGrading hB i := by
  obtain ⟨y, hy⟩ := Submodule.toBaseChange_surjective' B (shortExactOrderGrading hn i) hx
  rw [← hy]
  clear hy hx x
  induction y with
  | tmul b z =>
    obtain ⟨p, hp, hzp⟩ := z.property
    change exactOrderShortPresentation hn p = (z : ExactOrderAlgebra (shortFamily R) hn) at hzp
    change shortCoverBaseChange hn hB (b ⊗ₜ[R] (z : ExactOrderAlgebra (shortFamily R) hn)) ∈ _
    rw [← hzp, TensorProduct.tmul_eq_smul_one_tmul b, map_smul,
      shortCoverBaseChange_presentation]
    refine (shortExactOrderGrading hB i).smul_mem b
      ⟨MvPolynomial.map (algebraMap R B) p, ?_, rfl⟩
    intro t ht
    apply hp
    rw [MvPolynomial.coeff_map] at ht
    exact fun h => ht (by rw [h, map_zero])
  | add y z hy hz =>
    rw [map_add, Submodule.coe_add, map_add]
    exact add_mem hy hz

variable [IsDomain (ShortBase R)] [IsDomain (ShortBase B)]

private theorem shortCoverCoefficientBaseChange_units (a : (ZMod (n + 2))ˣ)
    (x : ExactOrderAlgebra (shortFamily R) hn) :
    shortCoverCoefficientBaseChange hn hB
        ((1 : ShortBase B) ⊗ₜ[ShortBase R] shortLevelUnitAut hn a x) =
      shortLevelUnitAut hB a
        (shortCoverCoefficientBaseChange hn hB ((1 : ShortBase B) ⊗ₜ[ShortBase R] x)) := by
  obtain _ | n := n
  · have hc : Fintype.card (ZMod 2)ˣ = 1 := (ZMod.card_units_eq_totient 2).trans Nat.totient_two
    letI := Fintype.card_le_one_iff_subsingleton.mp hc.le
    rw [Subsingleton.elim a 1]
    simp [shortLevelUnitAut]
  · have ht := exactOrderUnitAutBaseChange_tmul (B := ShortBase B) (shortFamily R) hn a 1 x
    rw [exactOrderUnitAutBaseChange_eq] at ht
    change _ = exactOrderBaseChange _ hn
      ((1 : ShortBase B) ⊗ₜ[ShortBase R] shortLevelUnitAut hn a x) at ht
    simp only [shortCoverCoefficientBaseChange, AlgEquiv.trans_apply]
    rw [← ht]
    exact exactOrderCurveCongr_units shortFamily_map_shortBaseMap hB a _

/-- The base change of the cover intertwines geometric multiplication by units. -/
theorem shortCoverBaseChange_units (a : (ZMod (n + 2))ˣ)
    (x : ExactOrderAlgebra (shortFamily R) hn) :
    shortCoverBaseChange hn hB
        ((1 : B) ⊗ₜ[R] shortLevelUnitAut hn a x) =
      shortLevelUnitAut hB a (shortCoverBaseChange hn hB ((1 : B) ⊗ₜ[R] x)) := by
  simp only [shortCoverBaseChange_tmul_one]
  exact shortCoverCoefficientBaseChange_units hn hB a x

end Short

#print axioms exactOrderCurveCongr_xy
#print axioms exactOrderCurveCongr_units
#print axioms shortDiscriminant_mul_inv
#print axioms j_congr
#print axioms shortCoverCoefficientBaseChange_xy
#print axioms shortCoverBaseChange_coordinates
#print axioms shortCoverBaseChange_j
#print axioms shortCoverBaseChange_presentation
#print axioms shortCoverBaseChange_mem
#print axioms shortCoverCoefficientBaseChange_units
#print axioms shortCoverBaseChange_units

end WeierstrassCurve.ModelLevels.ModelGeneric
