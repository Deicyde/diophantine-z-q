import ZInQKernel.Contrib.OneProof.RC.PoolCharacter.Identification
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Product

/-! At the extraction primes, tex 8536–8549 and 8571–8577 prescribe the
same quadratic unit factors for the scaling and genus characters. Their
cancellation from the phase in (O.5) is (c). -/

namespace ZInQ.Manuscript.RC.PoolCharacter

open BlocksPerU ThetaCoeff WeilIndex
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped BigOperators

/-- In (O.5), the extraction-prime scaling factors cancel the genus twist.
The other factors, including the detecting-prime character, are retained. -/
theorem phase_without_extraction {O : Type*} [CommRing O]
    {m N : ℕ} [NeZero N] (h4 : 4 ∣ N) (hm : m ∣ N) (h3 : m % 4 = 3)
    (hsq : Squarefree m) {s : Finset ℕ} (hs : Disjoint s m.primeFactors)
    (u : (ZMod N)ˣ) (f : ℕ → O)
    (hf : ∀ p ∈ m.primeFactors, f p = (jacobiSym (representative u : ℤ) p : O)) :
    (∏ p ∈ s ∪ m.primeFactors, f p) * (jacobiSym (-(m : ℤ)) (representative u) : O) =
      ∏ p ∈ s, f p := by
  have hcop := ZMod.val_coe_unit_coprime u
  have htwo := hcop.of_dvd_right ((show 2 ∣ 4 by decide).trans h4)
  have hd : Odd (representative u) := by
    have hn := Nat.prime_two.coprime_iff_not_dvd.mp htwo.symm
    exact Nat.odd_iff.mpr (by change (u : ZMod N).val % 2 = 1; omega)
  have hg := LocalWeights.negativeDiscriminant_unit_character m (representative u) h3 hsq hd
  have hp : (∏ p ∈ m.primeFactors, f p) = (jacobiSym (-(m : ℤ)) (representative u) : O) := by
    rw [hg, Int.cast_prod]
    exact Finset.prod_congr rfl hf
  have hc : (-(m : ℤ)).gcd (representative u : ℤ) = 1 := by
    simpa only [Int.gcd_eq_natAbs, Int.natAbs_neg, Int.natAbs_natCast] using
      (hcop.of_dvd_right hm).symm
  have hsign : (jacobiSym (-(m : ℤ)) (representative u) : O) *
      (jacobiSym (-(m : ℤ)) (representative u) : O) = 1 := by
    rcases jacobiSym.eq_one_or_neg_one hc with he | he <;> simp [he]
  rw [Finset.prod_union hs, hp, mul_assoc, hsign, mul_one]

variable {O K L : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup L]
  {ε : L →+ ZMod 2} {T : TypeData L ε} {avoid : Finset ℕ}
  {M W N : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)}
  {P : Window T.Good S W} [NeZero N] [NeZero S.m]

/-- For the manuscript's partition of the scaling characters, the only
comparison needed is with the phase from primes away from the extraction. -/
theorem oldCharacter_comp_eq_bCharacter_iff_of_extraction (κ : K →+* ℂ)
    (Dₗ : LevelSetup P avoid N) (E : Lift S)
    (η : (ZMod N)ˣ →* Oˣ) (η_eval : ∀ u, (η u : O) = E.η (representative u))
    (η_order : ∀ u, ∃ e : ℕ, (η u : O) ^ (2 ^ e : ℕ) = 1)
    (hm : S.m ∣ Dₗ.old) (h3 : S.m % 4 = 3) (hsq : Squarefree S.m)
    (s : Finset ℕ) (hs : Disjoint s S.m.primeFactors)
    (c : ℕ → ℕ) (hc : ∀ p, c p ∣ Dₗ.old)
    (α : ∀ p, (ZMod (c p))ˣ →* ℂˣ)
    (hextract : ∀ p ∈ S.m.primeFactors, ∀ u : (ZMod N)ˣ,
      (α p (ZMod.unitsMap ((hc p).trans Dₗ.old_dvd) u) : ℂ) =
        (jacobiSym (representative u : ℤ) p : ℂ)) :
    (oldCharacter Dₗ.four_dvd hm (s ∪ S.m.primeFactors) c hc α).comp
        (ZMod.unitsMap Dₗ.old_dvd) =
      (Units.map κ).comp (bCharacter (K := K)
        (diamondCharacters Dₗ.common_four η η_eval η_order) ∅) ↔
    ∀ u : (ZMod N)ˣ, κ (algebraMap O K (E.η (representative u))) =
      ∏ p ∈ s, (α p (ZMod.unitsMap ((hc p).trans Dₗ.old_dvd) u) : ℂ) := by
  rw [oldCharacter_comp_eq_bCharacter_iff κ Dₗ E η η_eval η_order hm h3
    (s ∪ S.m.primeFactors) c hc α]
  apply forall_congr'
  intro u
  rw [phase_without_extraction Dₗ.common_four (hm.trans Dₗ.old_dvd) h3 hsq hs u
    (fun p => (α p (ZMod.unitsMap ((hc p).trans Dₗ.old_dvd) u) : ℂ))
    (fun p hp => hextract p hp u)]


end ZInQ.Manuscript.RC.PoolCharacter
