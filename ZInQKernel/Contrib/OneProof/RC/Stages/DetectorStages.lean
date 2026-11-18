import ZInQKernel.Contrib.OneProof.RC.Stages.Actual
import ZInQKernel.Contrib.OneProof.RC.Stages.Conjugation
import ZInQKernel.Contrib.OneProof.RC.Stages.SplitTwist
import ZInQKernel.Contrib.OneProof.RC.Stages.Translation

/-! The fixed global row and the sequence of actual primes, from the rational witness. -/

noncomputable section

open scoped WeierstrassCurve
open TauCeti WeierstrassCurve ZInQ.Manuscript
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.OpenImage

namespace ZInQ.Manuscript.RC.Stages

/-- The Tate action of actual complex conjugation is not minus the identity:
the latter has determinant +1 on rank two. -/
theorem complexConj_tate_ne_neg (A : WeierstrassCurve ℚ) [A.IsElliptic] :
    tateRep A 2 complexConj ≠ -1 := by
  intro h
  have hm : tateMatrix A complexConj = -1 := by
    rw [tateMatrix, h, map_neg, LinearMap.toMatrix_one]
  have hd := det_complexConj A
  rw [hm, Matrix.det_neg, Matrix.det_one] at hd
  norm_num at hd

/-- Given the nontorsion rational witness on the specified positive twist, choose
one detector and one sequence with precisely the stage primes of Appendix F.
The finite exclusion is arbitrary; the auxiliary field is fixed first. -/
theorem exists_detector_stages {ℓ : ℕ} (hℓ : 0 < ℓ) {Dw hstar : ℤ}
    (hDw : 0 < Dw) (hstar₀ : hstar < 0)
    [eE : (Ecurve ℓ).IsElliptic] [eA : (qtwist (Ecurve ℓ) Dw).IsElliptic]
    (P : ((qtwist (Ecurve ℓ) Dw)⁄ℚ).toAffine.Point)
    (hnt : ¬ IsOfFinAddOrder P) (hS : SerreThm3) (hA : HasNoCM (qtwist (Ecurve ℓ) Dw))
    (F₀ : IntermediateField ℚ Qbar) [IsGalois ℚ F₀] [FiniteDimensional ℚ F₀]
    {x y : Qbar} (hxmem : x ∈ F₀) (hymem : y ∈ F₀)
    (hx : x ^ 2 = (Dw : Qbar)) (hy : y ^ 2 = (hstar : Qbar)) :
    let A := qtwist (Ecurve ℓ) Dw
    let Q := Affine.Point.baseChange (W' := A) ℚ Qbar P
    let d := divisionTower (A := A) Q
    let hQ : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom Q = Q :=
      fun g => Affine.Point.map_baseChange (W' := A) g.toAlgHom P
    ∃ (a : ℕ) (σ : GalQ) (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2]),
      tateRep (Ecurve ℓ) 2 σ = tateRep (Ecurve ℓ) 2 complexConj ∧
      (∀ t, b (tateRep A 2 σ t) = b t) ∧ Function.Surjective b ∧
      b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1) ∧
      ∀ B : Finset ℕ, Nonempty (StageSequence (ActualAt A (Ecurve ℓ) Q F₀ σ Dw hstar) (a + 1)
        (stageExclusions ℓ Dw hstar B)) := by
  intro A Q d hQ
  obtain ⟨a, h, b, hh, hρ, hb, hbonto, hc⟩ :=
    d.exists_fixed_detector hQ P rfl hnt hS hA F₀ complexConj_sq (complexConj_tate_ne_neg A)
  let σ := h * complexConj
  have hρA : tateRep A 2 σ = tateRep A 2 complexConj :=
    LinearMap.ext fun t => DFunLike.congr_fun hρ t
  obtain ⟨hsx, hsy⟩ := detector_sqrt_signs F₀ hh hDw hstar₀ hxmem hymem hx hy
  have hx₀ : x ≠ 0 := by
    intro hz
    have hc : (Dw : Qbar) = 0 := by simpa [hz] using hx.symm
    exact hDw.ne' (by exact_mod_cast hc)
  have hρE : tateRep (Ecurve ℓ) 2 σ = tateRep (Ecurve ℓ) 2 complexConj :=
    geomTwist_tate_action_eq (Ecurve ℓ) rfl rfl Dw x hx₀ (by simpa using hx) σ complexConj
      hsx (complexConj_pos_sqrt hDw hx) hρA
  have hdet : (tateMatrix (Ecurve ℓ) σ).det = -1 := by
    rw [det_tateMatrix, hρE, ← det_tateMatrix, det_complexConj]
  refine ⟨a, σ, b, hρE, fun t => ?_, hbonto, hc, ?_⟩
  · rw [hρA]
    exact hb t
  · intro B
    exact ⟨actualStageSequence A (Ecurve ℓ) Q F₀ σ hdet Dw hstar (a + 1)
      (stageExclusions ℓ Dw hstar B) hxmem hymem hx hy hsx hsy
      (fun p hp hn => stageExclusions_good hℓ.ne' hDw.ne' hstar₀.ne B hp hn)⟩

#print axioms complexConj_tate_ne_neg
#print axioms exists_detector_stages

end ZInQ.Manuscript.RC.Stages
