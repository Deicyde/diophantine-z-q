import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralTatePairing
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.PadicLimit
import ZInQKernel.Contrib.RC53Assist.Finiteness.GaloisFiniteness

/-!
# The canonical all-level integral cyclotomic coefficient limit

The integral coefficient line projects to the finite cyclotomic lines through the canonical
p-adic residue maps. Continuous division and continuous compatible limits are supplied by
p-adic arithmetic, not by additional limit hypotheses. The existing cyclotomic-character
reduction theorem proves equivariance at every level.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.CoefModules (CharMod cycS)

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) [HasTwoPowerRoots K S]

/-- The finite cyclotomic coefficient line at level `k`. -/
abbrev FiniteCyclotomicLine (k : ℕ) : Type :=
  CharMod (ZMod (2 ^ k)) (cycS (HasTwoPowerRoots.roots (K := K) (S := S) k))

/-- Canonical reduction of the integral coefficient line to the finite cyclotomic line. -/
def integralCoefficientProj (k : ℕ) : IntegralTate1 K S →+ FiniteCyclotomicLine K S k where
  toFun t := PadicInt.toZModPow k (ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K S) t)
  map_zero' := map_zero (PadicInt.toZModPow k)
  map_add' a b := map_add (PadicInt.toZModPow k) a b

/-- In coefficient coordinates the projection is exactly `toZModPow`. -/
theorem integralCoefficientProj_apply (k : ℕ) (t : IntegralTate1 K S) :
    CharMod.equiv (ZMod (2 ^ k))
      (cycS (HasTwoPowerRoots.roots (K := K) (S := S) k))
      (integralCoefficientProj K S k t) =
        PadicInt.toZModPow k (ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K S) t) := rfl

/-- The actual integral cyclotomic line satisfies the existing all-level limit interface. -/
theorem integralCoefficient_isTwoAdicLimit :
    ZInQ.Contrib.RC53Assist.Finiteness.IsTwoAdicLimit (integralCoefficientProj K S) where
  continuous k := PadicLimit.continuous_toZModPow (p := 2) k
  surjective k := ZMod.ringHom_surjective (PadicInt.toZModPow (p := 2) k)
  map_two_pow_smul k t := PadicLimit.toZModPow_prime_pow_mul (p := 2) k t
  divide := fun k {X} _ f hf hker => PadicLimit.continuous_division_two_pow k f hf hker
  limit := fun {X} _ f hf hc => PadicLimit.exists_continuous_limit (p := 2) f hf hc
  separated t h := PadicLimit.separated (p := 2) t h
  torsionFree t h := PadicLimit.torsionFree (p := 2) t h

/-- Every canonical residue projection is equivariant for the actual cyclotomic actions. -/
theorem integralCoefficient_isEquivariantLevels :
    ZInQ.Contrib.RC53Assist.Finiteness.IsEquivariantLevels (GKS K S)
      (integralCoefficientProj K S) := by
  intro k σ t
  change PadicInt.toZModPow k ((cyc2 K S σ : ℤ_[2]) * (ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K S) t)) =
    (cycS (HasTwoPowerRoots.roots (K := K) (S := S) k) σ : ZMod (2 ^ k)) *
      PadicInt.toZModPow k (ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K S) t)
  rw [map_mul, toZModPow_cyc2]

end ZInQ.Contrib.RC53Assist.IntegralDuality
