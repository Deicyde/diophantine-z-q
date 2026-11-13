import ZInQKernel.Contrib.TYZGenus.Package

noncomputable section
namespace ZInQ.Contrib.TYZGenus.CM
open ZInQ.Contrib.TYZDecomp.CurveA WeierstrassCurve.Affine

theorem galPt_zero (σ : GalQ) : galPt σ (0 : PtA) = 0 := rfl

theorem galPt_some (σ : GalQ) {x y : Qbar} (h : curveAbar.toAffine.Nonsingular x y) :
    ∃ h', galPt σ (.some x y h) = .some (σ x) (σ y) h' :=
  ⟨_, rfl⟩

theorem mem_ptsOver_iff (K : IntermediateField ℚ Qbar) (P : PtA) :
    P ∈ ptsOver K ↔ IsDefinedOver K P := by
  constructor
  · rintro ⟨Q, rfl⟩
    rcases Q with _ | ⟨x, y, h⟩
    · trivial
    · exact ⟨x.2, y.2⟩
  · intro hP
    rcases P with _ | ⟨x, y, h⟩
    · exact ⟨0, rfl⟩
    · obtain ⟨hx, hy⟩ := hP
      have h' : (curveA.baseChange K).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ :=
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := curveA) (f := K.val) K.val.injective _ _).mp h
      exact ⟨.some _ _ h', rfl⟩

theorem iPt_mem {K : IntermediateField ℚ Qbar} (hi : iQ ∈ K) {P : PtA} (hP : P ∈ ptsOver K) :
    iPt P ∈ ptsOver K := by
  rw [mem_ptsOver_iff] at hP ⊢
  rcases P with _ | ⟨x, y, h⟩
  · trivial
  · exact ⟨K.neg_mem hP.1, K.mul_mem hi hP.2⟩

theorem galPt_mem {K : IntermediateField ℚ Qbar} (σ : GalQ) (hσ : ∀ x ∈ K, σ x ∈ K) {P : PtA}
    (hP : P ∈ ptsOver K) : galPt σ P ∈ ptsOver K := by
  rw [mem_ptsOver_iff] at hP ⊢
  rcases P with _ | ⟨x, y, h⟩
  · trivial
  · obtain ⟨h', e⟩ := galPt_some σ h
    rw [e]
    exact ⟨hσ x hP.1, hσ y hP.2⟩

theorem galPt_iPt (σ : GalQ) (hσ : σ iQ = iQ) (P : PtA) :
    galPt σ (iPt P) = iPt (galPt σ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := galPt_some σ h
    rw [e, iPt_some, iPt_some]
    obtain ⟨h'', e'⟩ := galPt_some σ (nonsingular_iPt h)
    rw [e', Point.some.injEq]
    exact ⟨map_neg σ x, by rw [map_mul, hσ]⟩

end ZInQ.Contrib.TYZGenus.CM
