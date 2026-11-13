import ZInQKernel.Contrib.UnramifiedCocycle.KernelBridge

/-!
# Actual unramified descent through the constructed Frobenius tower

The finite action is factored through the actual surjective local quotient
using the proved kernel inclusion.  Its composition equality is checked on
all elements.  The old product-cochain theorem then supplies a locally
constant sign cochain for the original, unnormalized cocycle.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2 GlueDescent.B2Q

local instance finrank_ne_zero (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] : NeZero (Module.finrank ℚ L) := ⟨Module.finrank_pos.ne'⟩

variable (p : Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ L] [IsGalois ℚ L]

/-- Kernel inclusion for the actually constructed degree `[L:ℚ]` quotient. -/
theorem localFrobenius_kernel_le (hu : UnramifiedAt L p) :
    (localFrobeniusQuotient p (Module.finrank ℚ L)).ker ≤ (localRestriction L p).ker := by
  intro g hg
  exact localRestriction_one_of_quotient_one p L (Module.finrank ℚ L) (dvd_refl _) hu g hg

/-- The actual finite field action, obtained from a surjective quotient rather
than assumed as a cyclic-model field. -/
noncomputable def unramifiedActionFactor (hu : UnramifiedAt L p) :
    CyclicGroup (Module.finrank ℚ L) →* Gal(L/ℚ) :=
  (localFrobeniusQuotient p (Module.finrank ℚ L)).liftOfSurjective
    (localFrobeniusQuotient_surjective p (Module.finrank ℚ L))
    ⟨localRestriction L p, localFrobenius_kernel_le p L hu⟩

theorem unramifiedActionFactor_comp (hu : UnramifiedAt L p) :
    (unramifiedActionFactor p L hu).comp (localFrobeniusQuotient p (Module.finrank ℚ L)) =
      localRestriction L p := by
  apply MonoidHom.ext
  intro g
  let q := localFrobeniusQuotient p (Module.finrank ℚ L)
  let hq := localFrobeniusQuotient_surjective p (Module.finrank ℚ L)
  let f := localRestriction L p
  let hf := localFrobenius_kernel_le p L hu
  change (q.liftOfSurjective hq ⟨f, hf⟩) (q g) = f g
  exact MonoidHom.liftOfRightInverse_comp_apply q (Function.surjInv hq)
    (Function.surjInv_eq hq) ⟨f, hf⟩ g

/-- All fields required by the original bridge are constructed with their
actual continuity and composition equalities. -/
noncomputable def actualUnramifiedCyclicLift (hu : UnramifiedAt L p) : LocalCyclicLift L p where
  n := Module.finrank ℚ L
  positive := Module.finrank_pos
  quotient := localFrobeniusQuotient p (Module.finrank ℚ L)
  finiteAction := unramifiedActionFactor p L hu
  lift := localFrobeniusQuotient p (2 * Module.finrank ℚ L)
  lift_continuous := localFrobeniusQuotient_continuous p _
  lift_compatible := localFrobeniusQuotient_double_compatible p _
  action_compatible := unramifiedActionFactor_comp p L hu

/-- The arithmetic bridge, with exactly its original field and prime quantifiers. -/
theorem unramifiedCyclicBridge : UnramifiedCyclicBridge := by
  intro L _ _ p hu
  exact ⟨actualUnramifiedCyclicLift p L hu⟩

/-- The original production proposition, using the unchanged sign-cocycle
normalization/restoration and genuine finite Galois descent. -/
theorem leafUnramified : LeafUnramified :=
  leafUnramified_of_cyclicBridge unramifiedCyclicBridge

/-- The exact expanded frozen statement, used for an independent kernel type
comparison of the full provider, including all original quantifiers. -/
theorem leafUnramified_explicit :
    ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
      (ε : GQ → GQ → ℂˣ), IsSignCocycle ε → InflatedFrom L ε →
      ∀ p : Nat.Primes, UnramifiedAt L p → SignCob (pull (resp p) ε) := leafUnramified

end ZInQ.Contrib.UnramifiedCocycle

namespace ZInQ.Contrib.H

/-- Proof provider typed directly against the unchanged production leaf.
No unregistered target-reference module is imported. -/
theorem T31_holds : GlueDescent.B2Q.LeafUnramified :=
  ZInQ.Contrib.UnramifiedCocycle.leafUnramified

end ZInQ.Contrib.H
