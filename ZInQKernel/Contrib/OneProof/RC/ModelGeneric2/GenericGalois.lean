import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.GenericPoints
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.MarkedGalois
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapEquiv

/-! # Galois equivariance of the pinned generic pair reading -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open LeafModCurves ModelGeneric Affine

open private rationalLevel_isUnit from ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational
open private genericSubgroupPair from ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.GenericPoints

variable {N : ℕ} [NeZero N]

/-- On cyclic subgroups of the actual generic equation, Galois acts on point coordinates. -/
noncomputable def galoisCyclicSubgroup (σ : Kbar ≃ₐ[Qj] Kbar) :
    CyclicSubgroups EjBar.toAffine.Point N ≃ CyclicSubgroups EjBar.toAffine.Point N :=
  cyclicSubgroupsEquiv (Point.mapEquiv Ej σ) N

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
/-- Restricting a geometric point to the rational level quotient and reading the subgroup
on `EjBar` commutes with every automorphism over the actual j-line. -/
theorem genericJSubgroups_galois (h₂ : 2 ≤ N) (σ : Kbar ≃ₐ[Qj] Kbar)
    (x : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) :
    genericJSubgroups h₂ (σ.toAlgHom.comp x) =
      galoisCyclicSubgroup σ (genericJSubgroups h₂ x) := by
  obtain _ | _ | n := N
  · omega
  · omega
  letI := invertibleOfNonzero (by norm_num : (2 : Qj) ≠ 0)
  letI := invertibleOfNonzero (by norm_num : (3 : Qj) ≠ 0)
  let v := Ej.toShortNF
  let A := v • Ej
  let V := A.baseChange Kbar
  letI : V.IsShortNF :=
    ⟨by simp [V, A, baseChange],
     by simp [V, A, baseChange, a₂_of_isShortNF],
     by simp [V, A, baseChange]⟩
  let e := Ej.pointEquivVariableChange Kbar v
  let T (P : Generators EjBar.toAffine.Point (n + 2)) : Generators V.toAffine.Point (n + 2) :=
    ⟨e.symm P.val, (addOrderOf_injective e.symm.toAddMonoidHom e.symm.injective P.val).trans P.property⟩
  let hV : v.baseChange Kbar • EjBar = V := baseChange_smul_baseChange Kbar v Ej
  let hn := rationalLevel_isUnit (N := n + 2)
  let f (P : Generators EjBar.toAffine.Point (n + 2)) :=
    (exactOrderPointOfGenerator hn V (T P)).comp (Y0RationalInclusion h₂)
  have hread (P : Generators EjBar.toAffine.Point (n + 2)) :
      rationalPoints h₂ (f P) =
        (Quot.mk _ (⟨EjBar, inferInstanceAs (Ej.baseChange Kbar).IsElliptic,
          subgroupOfGenerator P⟩ : EnhancedCurve Kbar (n + 2)) : PairClasses Kbar (n + 2)) := by
    change (rationalPointReading h₂).val (f P) = _
    rw [show f P = _ from rfl, (rationalPointReading h₂).property, shortCoverPair_marked]
    symm
    apply (pairClasses_eq_iff _ _).2
    refine ⟨v.baseChange Kbar, hV, ?_⟩
    have he : changePoints EjBar V (v.baseChange Kbar) hV = e.symm := by
      ext P
      change (AddEquiv.cast hV) ((Point.addEquivVariableChange EjBar
        (v.baseChange Kbar)).symm P) =
          ((AddEquiv.cast hV.symm).trans
            (Point.addEquivVariableChange EjBar (v.baseChange Kbar))).symm P
      rw [AddEquiv.symm_trans_apply]
      rfl
    rw [he]
    exact AddMonoidHom.map_zmultiples e.symm.toAddMonoidHom P.val
  obtain ⟨P, hP⟩ := subgroupOfGenerator_surjective (genericJSubgroups h₂ x)
  have hx : (genericJPointsOnRational h₂ x).val = f P := by
    apply (rationalPoints h₂).injective
    rw [hread, hP]
    exact (genericJSubgroups_pairClass h₂ x).symm
  let y := σ.toAlgHom.comp x
  let ρ := σ.toAlgHom.restrictScalars ℚ
  have hy : (genericJPointsOnRational h₂ y).val = ρ.comp (f P) := by
    rw [← hx]
    ext b
    rw [genericJPointsOnRational_apply]
    change σ (x (Y0RationalGenericJInclusion h₂ b)) = σ ((genericJPointsOnRational h₂ x).val b)
    rw [genericJPointsOnRational_apply]
  let P' := galoisGenerator Ej σ P
  have hT : T P' = galoisGenerator A σ (T P) := by
    apply Subtype.ext
    exact (Ej.map_pointEquivVariableChange_symm Kbar v σ.toAlgHom P.val).symm
  have hf : f P' = ρ.comp (f P) := by
    change (exactOrderPointOfGenerator hn V (T P')).comp _ = ρ.comp
      ((exactOrderPointOfGenerator hn V (T P)).comp _)
    rw [hT, exactOrderPointOfGenerator_galois, AlgHom.comp_assoc]
  have hP' : subgroupOfGenerator P' = galoisCyclicSubgroup σ (subgroupOfGenerator P) := by
    apply Subtype.ext
    exact (AddMonoidHom.map_zmultiples (Point.mapEquiv Ej σ).toAddMonoidHom P.val).symm
  change genericJSubgroups h₂ y = _
  rw [← hP, ← hP']
  apply (genericSubgroupPair (N := n + 2)).injective
  apply Subtype.ext
  change (Quot.mk _ (⟨EjBar, _, genericJSubgroups h₂ y⟩ : EnhancedCurve Kbar (n + 2)) :
    PairClasses Kbar (n + 2)) = Quot.mk _ ⟨EjBar, _, subgroupOfGenerator P'⟩
  rw [genericJSubgroups_pairClass, hy, ← hf, hread]

#print axioms galoisCyclicSubgroup
#print axioms genericJSubgroups_galois

end WeierstrassCurve.ModelLevels.ModelGeneric2
