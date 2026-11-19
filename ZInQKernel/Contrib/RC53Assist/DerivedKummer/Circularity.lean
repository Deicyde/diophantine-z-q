import ZInQKernel.Contrib.RC53Assist.DerivedKummer.LocalDuality

/-! # The integral reduction premise of the derived Kummer isotropy, as typed

`actualCup_divisible_of_print` and `kummerTruncIsotropy_from_print` take a premise that, for every
level `2^a` and all classes `x, y`, the `2`-adic invariant of `β x y` equals the local Tate pairing of
two Kummer classes. Given the printed local duality, the right side is already zero by finite Kummer
isotropy, and conversely zero is attained at the zero points. So, as typed, the premise says exactly
that `β` vanishes pointwise (`reductionPremise_iff_zero`): it is the trace-vanishing statement itself,
not an independent identification of reduction maps. Fixed finite-level reduction maps, their
Kummer-image identifications and the cup-invariant compatibility for those maps remain to be
supplied before these two declarations count as a reduction of the integral isotropy.
This equivalence was found and checked in an independent review.
-/

namespace ZInQ.Contrib.RC53Assist.DerivedKummer

open TauCeti TauCeti.ContCohomology
open ZInQ.Contrib.CloudB3RC53.Duality

variable (F : Type) [Field F] [DecidableEq F] [CharZero F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (B : WeierstrassCurve F) [B.IsElliptic]

/-- **The reduction premise, as typed, is pointwise vanishing.** -/
theorem reductionPremise_iff_zero (hM : MilneLocalDualityPrint)
    {X Y : Type*} (β : X → Y → ℤ_[2]) :
    (∀ (a : ℕ) (x : X) (y : Y), ∃ p q : B.toAffine.Point,
      padicInvariant a (β x y) =
        localTatePairing B (2 ^ a) (twoPower_isUnit F a)
          (B.kummerMap (2 ^ a) (twoPower_isUnit F a) p)
          (B.kummerMap (2 ^ a) (twoPower_isUnit F a) q)) ↔
      ∀ x y, β x y = 0 := by
  constructor
  · intro hred x y
    exact eq_zero_of_forall_two_pow_dvd (β x y)
      (fun a => actualCup_divisible_of_print hM F B β hred a x y)
  · intro hz a x y
    refine ⟨0, 0, ?_⟩
    rw [hz x y]
    simp

end ZInQ.Contrib.RC53Assist.DerivedKummer
