import FrobLift.TameRelationV001

/-!
# The tame relation produces genuine wild inertia elements

For `φ` in the decomposition group of `w` with `φ x ≡ x^q (mod 𝔪_w)` on `w`, and `τ` in the inertia
group of `w`, the element `(φ τ φ⁻¹)⁻¹ τ^q` lies in the inertia group (`PkgI2.IsInertia`: inertia is
normal in the decomposition group) and satisfies the literal wild condition.
-/

noncomputable section

namespace FrobLift

variable {K : Type} [Field K] [NumberField K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {w : ValuationSubring Ω}

omit [NumberField K] [IsAlgClosure K Ω] in
theorem isInertia_frob_conj {φ : Ω ≃ₐ[K] Ω} (hD : φ ∈ w.decompositionSubgroup K)
    {τ : Ω ≃ₐ[K] Ω} (hτ : PkgI2.IsInertia w τ) (q : ℕ) :
    PkgI2.IsInertia w ((φ * τ * φ⁻¹)⁻¹ * τ ^ q) := by
  obtain ⟨hτD, hτI⟩ := hτ
  set I := w.inertiaSubgroup K
  have hn : I.Normal := by
    show (MonoidHom.ker _).Normal
    infer_instance
  let Φ : w.decompositionSubgroup K := ⟨φ, hD⟩
  let T : w.decompositionSubgroup K := ⟨τ, hτD⟩
  have hmem : (Φ * T * Φ⁻¹)⁻¹ * T ^ q ∈ I :=
    I.mul_mem (I.inv_mem (hn.conj_mem T hτI Φ)) (I.pow_mem hτI q)
  exact ⟨((Φ * T * Φ⁻¹)⁻¹ * T ^ q).2, hmem⟩

/-- **Frobenius lift with genuine wild inertia commutators.** -/
theorem frobenius_lift_wild_inertia (hw : w.comap (algebraMap K Ω) = O) :
    ∃ φ : Ω ≃ₐ[K] Ω, φ ∈ w.decompositionSubgroup K ∧
      2 ≤ Nat.card (IsLocalRing.ResidueField O) ∧
      (∀ x ∈ w, w.valuation (φ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1) ∧
      ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
        PkgI2.IsInertia w ((φ * τ * φ⁻¹)⁻¹ * τ ^ Nat.card (IsLocalRing.ResidueField O)) ∧
        ∀ x : Ω, x ≠ 0 →
          w.valuation (((φ * τ * φ⁻¹)⁻¹ * τ ^ Nat.card (IsLocalRing.ResidueField O)) x - x) <
            w.valuation x := by
  obtain ⟨φ, hD, hq2, hcong, htame⟩ := frobenius_lift_tame hw
  exact ⟨φ, hD, hq2, hcong, fun τ hτ => ⟨isInertia_frob_conj hD hτ _, htame τ hτ⟩⟩

end FrobLift
