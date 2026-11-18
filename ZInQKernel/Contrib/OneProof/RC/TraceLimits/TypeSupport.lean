import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Quadratic
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Chebotarev

/-!
# Stationary quadratic tests

Tex 2016–2029, 2162–2163, 9748–9750. Extending the Frobenius calculation
to all Galois elements via a finite compositum is on-the-spot (c).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TraceLimits

open AddressGenuine
open ZInQ.Manuscript.RC.PrintsArith

/-- The tree's Frobenius formula reading fixed radicals from the type holds on
all of `G_ℚ` as soon as the modulus is a multiple of `4|k|`. -/
theorem sqrtChar_eq_kChar (m : ℕ) [NeZero m] {k : ℤ} (hk : 4 * k.natAbs ∣ m)
    (g : GalQ) :
    sqrtChar k g = Multiplicative.ofAdd (kChar m k hk (Multiplicative.toAdd (typChar m g))) := by
  obtain ⟨E, hE, hfix⟩ := exists_fixingSubgroup_le_ker_typChar m
  let K := IntermediateField.adjoin ℚ {sqrtQbar k}
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  obtain ⟨φ, p, hp, hpS, hf, hEq⟩ := ZInQ.Contrib.ChebFD.C10.frobDense
    ZInQ.Contrib.chebotarevExists m.primeFactors (E ⊔ K) inferInstance g
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
    hpS (Nat.mem_primeFactors.2 ⟨hp, hd, NeZero.ne m⟩)
  have hinl : (E : Set Qbar) ⊆ ↑(E ⊔ K) := SetLike.coe_subset_coe.mpr le_sup_left
  have hinr : (K : Set Qbar) ⊆ ↑(E ⊔ K) := SetLike.coe_subset_coe.mpr le_sup_right
  have hφg : g⁻¹ * φ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [AlgEquiv.mul_apply, hEq x (hinl hx), AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have htype : typChar m φ = typChar m g := by
    have e : g * (g⁻¹ * φ) = φ := by group
    rw [← e, map_mul, hfix _ hφg]
    exact add_zero (Multiplicative.toAdd (typChar m g))
  have hroot : φ (sqrtQbar k) = g (sqrtQbar k) :=
    hEq _ (hinr (IntermediateField.mem_adjoin_simple_self ℚ _))
  calc
    sqrtChar k g = sqrtChar k φ := by simp only [sqrtChar_apply, hroot]
    _ = _ := by
      rw [← htype]
      exact sqrtChar_eq_kChar_of_isFrobAt m hk hp hcop ((isFrobAt_iff_c10 hp).2 hf)

/-- A modulus including eight and all the stationary odd primes has all the
required fixed tests; the divisibility form also permits smaller support. -/
theorem typChar_detects_radicals (m : ℕ) [NeZero m] (S : Finset ℕ)
    (h4 : 4 ∣ m) (hS : ∀ p ∈ S, 4 * p ∣ m) : TypeDetectsRadicals (L := SqClass m) (typChar m) S := by
  intro g hg
  have h (k : ℤ) (hk : 4 * k.natAbs ∣ m) : sqrtChar k g = 1 := by
    rw [sqrtChar_eq_kChar m hk, hg]
    change Multiplicative.ofAdd (kChar m k hk 0) = 1
    rw [map_zero]
    rfl
  refine ⟨MonoidHom.mem_ker.2 (h (-1) (by simpa using h4)), MonoidHom.mem_ker.2 ?_⟩
  funext p
  exact h (p.val : ℤ) (by simpa using hS p p.2)

/-- The additional stage bit detects its radical once the sign is known. -/
theorem stageChar_detects_radicals (m ℓ : ℕ) [NeZero m] (hℓ : ℓ ≠ 0) (S : Finset ℕ)
    (h4 : 4 ∣ m) (hS : ∀ p ∈ S, 4 * p ∣ m) : TypeDetectsRadicals (L := SqClass m × ZMod 2) (stageChar m ℓ) (insert ℓ S) := by
  intro g hg
  have h₁ : typChar m g = 1 := by
    simpa [stageChar_apply] using congrArg (fun x => (Multiplicative.toAdd x).1) hg
  have h₂ : bitChar ℓ g = 1 := by
    simpa [stageChar_apply] using congrArg (fun x => (Multiplicative.toAdd x).2) hg
  have h := typChar_detects_radicals m S h4 hS g h₁
  refine ⟨h.1, MonoidHom.mem_ker.2 ?_⟩
  funext p
  change sqrtChar (p.val : ℤ) g = 1
  rcases Finset.mem_insert.1 p.2 with e | hp
  · rw [e]
    exact sqrtChar_prime_of_bit g hℓ (MonoidHom.mem_ker.1 h.1) h₂
  · exact congrFun (MonoidHom.mem_ker.1 h.2) ⟨p, hp⟩

#print axioms sqrtChar_eq_kChar
#print axioms typChar_detects_radicals
#print axioms stageChar_detects_radicals

end ZInQ.Manuscript.RC.TraceLimits
