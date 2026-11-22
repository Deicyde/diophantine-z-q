import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists

/-! # Contracting a place of `ℚ̄` to the algebraic integers -/

noncomputable section

namespace DS965Places

open ZInQ.Contrib.ChebFD.HSyn (Qbar GQ LocMem zbarLoc locMem_or_inv gZ)
open ZInQ.Contrib.ChebFD.C10 (Zbar)

/-- Every algebraic integer belongs to the given valuation ring. -/
theorem int_mem (v : ValuationSubring Qbar) (x : Zbar) : (x : Qbar) ∈ v := by
  have hx : IsIntegral v (x : Qbar) := (show IsIntegral ℤ (x : Qbar) from x.2).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact hy ▸ y.property

/-- The inclusion from the algebraic integers into the valuation ring. -/
def toVal (v : ValuationSubring Qbar) : Zbar →+* v :=
  (algebraMap Zbar Qbar).codRestrict v.toSubring (int_mem v)

/-- The prime of the algebraic integers at the chosen place. -/
def placeIdeal (v : ValuationSubring Qbar) : Ideal Zbar :=
  (IsLocalRing.maximalIdeal v).comap (toVal v)

instance (v : ValuationSubring Qbar) : (placeIdeal v).IsPrime :=
  Ideal.IsPrime.comap (toVal v)

theorem mem_placeIdeal (v : ValuationSubring Qbar) (x : Zbar) :
    x ∈ placeIdeal v ↔ (x : Qbar) ∈ v.nonunits :=
  (ValuationSubring.coe_mem_nonunits_iff (A := v) (a := toVal v x)).symm

theorem placeIdeal_under (v : ValuationSubring Qbar) {p : ℕ} (hp : p.Prime)
    (hv : (p : Qbar) ∈ v.nonunits) : (placeIdeal v).under ℤ = Ideal.span {(p : ℤ)} := by
  have hnonzero : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hprime : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime hnonzero).mpr (Nat.prime_iff_prime_int.mp hp)
  have hmax := hprime.isMaximal (mt Ideal.span_singleton_eq_bot.mp hnonzero)
  apply Eq.symm
  apply hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
  rw [Ideal.span_singleton_le_iff_mem]
  change algebraMap ℤ Zbar (p : ℤ) ∈ placeIdeal v
  apply (mem_placeIdeal v _).mpr
  change algebraMap Zbar Qbar (algebraMap ℤ Zbar (p : ℤ)) ∈ v.nonunits
  rw [← IsScalarTower.algebraMap_apply ℤ Zbar Qbar]
  have hnat : (algebraMap ℤ Qbar) (p : ℤ) = (p : Qbar) := map_natCast (algebraMap ℤ Qbar) p
  exact hnat.symm ▸ hv

/-- The contracted prime is maximal over a rational prime. -/
theorem placeIdeal_isMaximal (v : ValuationSubring Qbar) {p : ℕ} (hp : p.Prime)
    (hv : (p : Qbar) ∈ v.nonunits) : (placeIdeal v).IsMaximal := by
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ)
  rw [placeIdeal_under v hp hv]
  have hn : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact ((Ideal.span_singleton_prime hn).mpr (Nat.prime_iff_prime_int.mp hp)).isMaximal
    (mt Ideal.span_singleton_eq_bot.mp hn)

/-- The valuation-subring presentation and localization at the contracted
prime have the same elements in `ℚ̄`. -/
theorem place_eq_zbarLoc (v : ValuationSubring Qbar) {p : ℕ} (hp : p.Prime)
    (hv : (p : Qbar) ∈ v.nonunits) : v = zbarLoc (placeIdeal v) p hp (placeIdeal_under v hp hv) := by
  have hfrac : ∀ (x : Qbar), LocMem (placeIdeal v) x → x ∈ v := by
    rintro x ⟨a, s, hs, hx⟩
    have hn : (s : Qbar) ∉ v.nonunits := mt (mem_placeIdeal v s).mpr hs
    have hz : (s : Qbar) ≠ 0 := fun h => hn ((v.mem_nonunits_iff_or).mpr (Or.inl h))
    have hi : (s : Qbar)⁻¹ ∈ v := by
      by_contra h
      exact hn ((v.mem_nonunits_iff_or).mpr (Or.inr h))
    have he : x = (a : Qbar) * (s : Qbar)⁻¹ := by rw [← hx, mul_assoc, mul_inv_cancel₀ hz, mul_one]
    rw [he]
    exact v.mul_mem _ _ (int_mem v a) hi
  refine le_antisymm (fun x hx => ?_) hfrac
  show LocMem (placeIdeal v) x
  by_cases hz : x = 0
  · exact ⟨0, 1, ZInQ.Contrib.ChebFD.HSyn.one_notMem _, by simp [hz]⟩
  rcases locMem_or_inv (placeIdeal v) p hp (placeIdeal_under v hp hv) x with h | ⟨a, s, hs, he⟩
  · exact h
  · have ha : a ∉ placeIdeal v := by
      intro h
      have hinv : (a : Qbar) = 0 ∨ (a : Qbar)⁻¹ ∉ v :=
        (v.mem_nonunits_iff_or).mp ((mem_placeIdeal v a).mp h)
      have hsn : (s : Qbar) ∉ v.nonunits := mt (mem_placeIdeal v s).mpr hs
      have hs0 : (s : Qbar) ≠ 0 := fun h => hsn ((v.mem_nonunits_iff_or).mpr (Or.inl h))
      have hsi : (s : Qbar)⁻¹ ∈ v := by
        by_contra hi
        exact hsn ((v.mem_nonunits_iff_or).mpr (Or.inr hi))
      rw [← he] at hinv
      rcases hinv with hh | hh
      · exact (mul_ne_zero (inv_ne_zero hz) hs0) hh
      · apply hh
        simpa only [mul_inv_rev, inv_inv] using v.mul_mem _ _ hsi hx
    exact ⟨s, a, ha, by rw [← he, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]⟩

end DS965Places
