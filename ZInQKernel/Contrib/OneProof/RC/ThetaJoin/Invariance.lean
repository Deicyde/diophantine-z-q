import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Global
import ZInQKernel.Contrib.OneProof.RC.Eichler.Stabilizer

/-! Conjugation by the unit group of the actual class order. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler

variable {a b : ℚ} {R : Order a b} {O : Type} [CommRing O]

/-- Covariance under local order units, using the ramified local factors of
the same norm character that multiplies the coefficient. -/
structure NormCovariance (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (χ : FiniteUnits R →* Oˣ) where
  eps : (q : Prime) → localUnits R q → Oˣ
  local_conj : ∀ q ∈ A.places, ∀ (u : localUnits R q) (y : Bp q.val a b),
    w q ((↑u.val⁻¹ : Bp q.val a b) * y * (u.val : Bp q.val a b)) =
      ((eps q u)⁻¹ : Oˣ) * w q y
  diagonal : ∀ u, χ (diagonal R u) = 1
  units : ∀ r : integralUnits R, χ r.val = ∏ q ∈ A.places, eps q ⟨r.val.val q, r.prop q⟩

/-- The right covariance factor is trivial on the image of a rational order
unit: rational conjugation becomes a compensating integral right translate. -/
theorem weight_conj (ha : a < 0) (hb : b < 0)
    (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O) (χ : FiniteUnits R →* Oˣ)
    (C : NormCovariance A w χ) (i : ClassSet R) (u : (B a b)ˣ)
    (hu : u ∈ classG ha hb i) (x : B a b) :
    weight A w i (rationalConj u x) = weight A w i x := by
  let z := classRepresentative i
  have hf : (fromAdelic z).val = (fromAdelic z).val.translate u := by
    rw [fromAdelic_classRepresentative]
    exact ((RightIdeal.mem_G_iff_translate ha hb (representative i).val u).mp hu).symm
  obtain ⟨r, hr⟩ := (fromAdelic_translate_iff z z u).mp hf
  have hw := weightedAt_change A w C.eps C.local_conj χ C.diagonal C.units z u r x
  rw [← hr] at hw
  exact (Units.isUnit (χ z)).mul_left_cancel hw

end ZInQ.Manuscript.RC.ThetaJoin
