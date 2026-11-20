import ZInQKernel.Contrib.OneProof.RC.Adelic.FiniteUnits
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Genus
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Basic

/-! Local reduced norms and the ideal-norm reading of the finite quadratic
character. The arithmetic here is independent of the stage's point values. -/

noncomputable section

open scoped Quaternion NumberField
open NumberField IsDedekindDomain
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.TorusWeights

open Eichler O7Actual

/-- The full odd filter at the chosen detecting prime (tex 9105–9108,
9121–9134). Splitting at two is included even when the level is odd. -/
structure OddFilter (N ell : ℕ) [Fact ell.Prime] (D hstar : ℤ) : Prop where
  positive : 0 < D
  squarefree : Squarefree D
  coprime : D.natAbs.Coprime hstar.natAbs
  detecting : legendreSym ell D = 1
  fundamental : Nonvanishing.IsFundamentalDiscriminant (D * hstar)
  odd : Odd (D * hstar)
  split : ∀ p : ℕ, p.Prime → p ∣ 2 * N → Nonvanishing.SplitsIn (D * hstar) p

/-- The completion of the quaternion reduced norm, bundled on units. -/
def localNrd {a b : ℚ} (p : Adelic.Prime) : (Bp p.val a b)ˣ →* (ℚ_[p.val])ˣ :=
  Units.map {
    toFun := fun x => (x * star x).re
    map_one' := by simp
    map_mul' := by
      intro x y
      change ((x * y) * star (x * y)).re = (x * star x).re * (y * star y).re
      have hn (z : Bp p.val a b) :
          algebraMap (ℚ_[p.val]) (Bp p.val a b) (z * star z).re = z * star z := by
        rw [QuaternionAlgebra.coe_algebraMap]
        exact (QuaternionAlgebra.mul_star_eq_coe z).symm
      apply (QuaternionAlgebra.algebraMap_injective (R := ℚ_[p.val])
        (c₁ := (a : ℚ_[p.val])) (c₂ := 0) (c₃ := (b : ℚ_[p.val])))
      rw [(algebraMap (ℚ_[p.val]) (Bp p.val a b)).map_mul, hn, hn, hn, star_mul]
      calc
        _ = x * (y * star y) * star x := by simp only [mul_assoc]
        _ = x * star x * algebraMap (ℚ_[p.val]) (Bp p.val a b) (y * star y).re := by
          conv_lhs => rw [← hn y]
          rw [mul_assoc, Algebra.commutes, ← mul_assoc]
        _ = x * star x * (y * star y) := by rw [hn y] }

/-- The local factors of the finite character in tex 8571–8578 and
8612–8614. The unramified rule is needed only for nonnegative valuations. -/
structure NormFactors {a b : ℚ} (R : Order a b) (hstar : ℤ) where
  character : Adelic.FiniteUnits R →* ℤˣ
  atPrime : (p : Adelic.Prime) → (ℚ_[p.val])ˣ →* ℤˣ
  rational : ∀ q : (B a b)ˣ, character (Adelic.diagonal R q) = 1
  unramified : ∀ (p : Adelic.Prime), ¬ p.val ∣ hstar.natAbs →
    ∀ v : (ℚ_[p.val])ˣ, 0 ≤ Padic.valuation (v : ℚ_[p.val]) →
      (atPrime p v : ℤ) = chiD hstar p.val ^ (Padic.valuation (v : ℚ_[p.val])).toNat
  unitValuation : ∀ (p : Adelic.Prime) (u : Adelic.localUnits R p),
    Padic.valuation (localNrd p u.val : ℚ_[p.val]) = 0
  product : ∀ z : Adelic.FiniteUnits R,
    character z = ∏ᶠ p : ℕ, if hp : p.Prime then
      atPrime ⟨p, hp⟩ (localNrd ⟨p, hp⟩ (z.val ⟨p, hp⟩)) else 1

variable {a b : ℚ} {R : Order a b} {hstar : ℤ}

/-- On an integral norm prime to the partner, with norm coordinate one at
the ramified places, the unramified prime factors multiply to the symbol
of the absolute norm (tex 9178–9194). -/
theorem NormFactors.onIntegralNorm (C : NormFactors R hstar) (z : Adelic.FiniteUnits R)
    (n : ℕ) (hn : n ≠ 0)
    (hval : ∀ p : Adelic.Prime,
      Padic.valuation (localNrd p (z.val p) : ℚ_[p.val]) = (n.factorization p.val : ℤ))
    (hbad : ∀ (p : Adelic.Prime), p.val ∣ hstar.natAbs → localNrd p (z.val p) = 1) :
    (C.character z : ℤ) = chiD hstar n := by
  classical
  let f : ℕ → ℤˣ := fun p => if hp : p.Prime then
    C.atPrime ⟨p, hp⟩ (localNrd ⟨p, hp⟩ (z.val ⟨p, hp⟩)) else 1
  have hgood (p : Adelic.Prime) (hp : ¬ p.val ∣ hstar.natAbs) :
      (C.atPrime p (localNrd p (z.val p)) : ℤ) = chiD hstar p.val ^ n.factorization p.val := by
    rw [C.unramified p hp _ (by rw [hval]; positivity), hval, Int.toNat_natCast]
  have hbad' (p : Adelic.Prime) (hp : p.val ∣ hstar.natAbs) :
      n.factorization p.val = 0 := by
    have h := hval p
    rw [hbad p hp, Units.val_one, Padic.valuation_one] at h
    exact_mod_cast h.symm
  have hs : Function.mulSupport f ⊆ ↑n.primeFactors := by
    intro p hp
    by_contra hm
    have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hm
    apply hp
    by_cases hP : p.Prime
    · dsimp [f]
      rw [dite_eq_left hP]
      by_cases hb : p ∣ hstar.natAbs
      · rw [hbad ⟨p, hP⟩ hb, map_one]
      · apply Units.ext
        simpa only [hz, pow_zero, Units.val_one] using hgood ⟨p, hP⟩ hb
    · simp [f, hP]
  have hfactor : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n :=
    Nat.prod_factorization_pow_eq_self hn
  have hprod : C.character z = ∏ p ∈ n.primeFactors, f p :=
    (C.product z).trans (finprod_eq_prod_of_mulSupport_subset f hs)
  rw [hprod, Units.coe_prod]
  calc
    _ = ∏ p ∈ n.primeFactors, chiD hstar p ^ n.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hnp : ¬ p ∣ hstar.natAbs := fun h => (Finsupp.mem_support_iff.mp hp) (hbad' ⟨p, hp'⟩ h)
      simpa only [f, dite_eq_left hp'] using hgood ⟨p, hp'⟩ hnp
    _ = chiD hstar (∏ p ∈ n.primeFactors, p ^ n.factorization p) := by
      let ψ : ℕ →* ℤ :=
        { toFun := chiD hstar
          map_one' := by simp [chiD]
          map_mul' := fun x y => by simp [chiD, jacobiSym.mul_left] }
      change (∏ p ∈ n.primeFactors, ψ p ^ n.factorization p) = ψ _
      rw [map_prod]
      simp only [map_pow]
    _ = _ := congrArg (chiD hstar) hfactor

/-- The case D = 1 uses the existing trivial descent on the field
discriminant. The other branch takes the stated descent as input. -/
theorem descent_of_filter {F : Type} [Field F] [NumberField F] {D hstar : ℤ}
    {N ell : ℕ} [Fact ell.Prime] (H : OddFilter N ell D hstar)
    (h₂ : Module.finrank ℚ F = 2) (hd : discr F = D * hstar)
    (hdesc : 1 < D → NormCharacterDescent F hstar) : NormCharacterDescent F hstar := by
  by_cases h : D = 1
  · have he : discr F = hstar := by simpa only [h, one_mul] using hd
    have ho : Odd (discr F) := hd ▸ H.odd
    exact he ▸ normCharacterDescent_self h₂ ho
  · exact hdesc (by have := H.positive; omega)


end ZInQ.Manuscript.RC.TorusWeights
