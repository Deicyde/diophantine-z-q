import ZInQKernel.Contrib.TYZGenus.CM

/-!
# x0-32: complex conjugation on Heegner points, proved (bridge to cm-points' `CM.lean`)

Owner: task x0-32. Report: `docs/research/x0-32.md`. Written against `TYZGenus/CM.lean` of task
cm-points at commit ba214e17 (merged into wip/x0-32).

cm-points defines the Heegner point `CM.heegnerPt Q ∈ A(ℚ̄)` of a Heegner form `Q = [A, B, C]` of
level 32 as the algebraic point over `X0.phiC τ_Q` (junk `0` if none), and states as a leaf
`CM.CMComplexConj`: an automorphism `σ` of `ℚ̄` inducing complex conjugation through `ιC` maps the
Heegner point of `[A, B, C]` to that of `[A, −B, C]`. With x0-32's `X0.phiC_neg_conj`
(`φ(−τ̄) = conj φ(τ)`: the eta quotients have real `q`-expansions) and `τ_{[A,−B,C]} = −conj τ_{[A,B,C]}`
this leaf is a theorem (`cmComplexConj`). It needs no algebraicity input: if `X0.phiC τ_Q` has no
algebraic preimage, neither has `X0.phiC τ_{Q̄}`, and both Heegner points are the junk `0`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.X0

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM Complex

/-- `τ_{[A,−B,C]} = −conj τ_{[A,B,C]}`. -/
theorem tauH_conj {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    ((Q.conj.tauH : UpperHalfPlane) : ℂ) = -starRingEnd ℂ ((Q.tauH : UpperHalfPlane) : ℂ) := by
  show cmPoint Q.A (-Q.B) D = -starRingEnd ℂ (cmPoint Q.A Q.B D)
  simp only [cmPoint, map_div₀, map_add, map_neg, map_mul, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal, map_intCast]
  push_cast
  ring

/-- `conjQ` (cm-points) is `conjQC` (x0-32). -/
theorem conjQ_eq_conjQC : conjQ = conjQC := rfl

/-- An automorphism `σ` inducing complex conjugation through `ιC` acts on `A(ℚ̄) ⊆ A(ℂ)` as complex
conjugation. -/
theorem toC_galPt (σ : GalQ) (hσ : ∀ x : Qbar, ιC (σ x) = starRingEnd ℂ (ιC x)) (P : PtA) :
    CM.toC (galPt σ P) = WeierstrassCurve.Affine.Point.map (W' := curveA) conjQC (CM.toC P) := by
  unfold CM.toC galPt
  rw [WeierstrassCurve.Affine.Point.map_map, WeierstrassCurve.Affine.Point.map_map]
  have hcomp : ιCA.comp σ.toAlgHom = conjQC.comp ιCA := by
    ext x
    exact hσ x
  rw [hcomp]

/-- Conjugation is an involution on `A(ℂ)`. -/
theorem map_conjQC_conjQC (P : PtAC) :
    WeierstrassCurve.Affine.Point.map (W' := curveA) conjQC
      (WeierstrassCurve.Affine.Point.map (W' := curveA) conjQC P) = P := by
  rw [WeierstrassCurve.Affine.Point.map_map]
  have : conjQC.comp conjQC = AlgHom.id ℚ ℂ := by
    ext x
    exact Complex.conj_conj x
  rw [this]
  exact WeierstrassCurve.Affine.Point.map_id P

/-- **Leaf `CM.CMComplexConj`, proved.** -/
theorem cmComplexConj : CMComplexConj := by
  intro σ hσ D Q
  have hconj : X0.phiC Q.conj.tauH =
      WeierstrassCurve.Affine.Point.map (W' := curveA) conjQC (X0.phiC Q.tauH) :=
    phiC_neg_conj Q.tauH Q.conj.tauH (tauH_conj Q)
  by_cases h : ∃ P : PtA, CM.toC P = X0.phiC Q.tauH
  · obtain ⟨P, hP⟩ := h
    rw [heegnerPt_eq Q hP]
    symm
    apply heegnerPt_eq
    rw [toC_galPt σ hσ, hP, hconj]
  · have h0 : heegnerPt Q = 0 := by
      unfold heegnerPt
      simp [h]
    have h1 : heegnerPt Q.conj = 0 := by
      unfold heegnerPt
      split_ifs with h'
      swap
      · rfl
      exfalso
      obtain ⟨P', hP'⟩ := h'
      apply h
      have hσ' : ∀ x : Qbar, ιC (σ.symm x) = starRingEnd ℂ (ιC x) := by
        intro x
        have := hσ (σ.symm x)
        rw [AlgEquiv.apply_symm_apply] at this
        rw [this, Complex.conj_conj]
      refine ⟨galPt σ.symm P', ?_⟩
      rw [toC_galPt σ.symm hσ' P', hP', hconj, map_conjQC_conjQC]
    rw [h0, h1, map_zero]

end ZInQ.Contrib.TYZGenus.X0
