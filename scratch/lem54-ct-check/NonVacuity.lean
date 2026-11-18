import ZInQKernel.Contrib.OneProof.CasselsTatePairing

namespace ZInQ.Manuscript.PoleS12.CTCheck

open SelmerTwoPower

/-- Specialize the printed elliptic curve statement to the exact family used by the headline. -/
theorem pairing_on_family
    (hPrinted : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → CasselsTatePairing E) :
    CasselsTatePairingCurves := by
  intro ℓ hℓ _ _
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  exact hPrinted _ (PoleRC.curve_isElliptic hℓ0)

/-- The domain of the family is inhabited. -/
theorem eleven_in_family :
    0 < (11 : ℕ) ∧ Squarefree (11 : ℕ) ∧ (11 : ℕ) % 12 = 11 ∧ (curve (11 : ℚ)).IsElliptic :=
  ⟨by norm_num, (by norm_num : Nat.Prime 11).squarefree, by norm_num,
    PoleRC.curve_isElliptic (by norm_num)⟩

/-- The added hypothesis preserves any conjunction of retained hypotheses, relative to the print. -/
theorem retained_compatible (P : Prop)
    (hPrinted : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → CasselsTatePairing E) :
    (P ∧ CasselsTatePairingCurves) ↔ P :=
  ⟨And.left, fun hP => ⟨hP, pairing_on_family hPrinted⟩⟩

/-- If Sha is finite, as in the conclusion of the rank theorem, the radical is zero. -/
theorem nondegenerate_of_finite_sha {E : WeierstrassCurve ℚ} [Finite (sha E)]
    (hCT : CasselsTatePairing E) :
    ∃ b : sha E →+ sha E →+ QZ, (∀ x, b x x = 0) ∧
      ∀ x, (∀ y, b x y = 0) ↔ x = 0 := by
  obtain ⟨b, halt, hker⟩ := hCT
  refine ⟨b, halt, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    have hN : 0 < Nat.card (sha E) := Nat.card_pos
    obtain ⟨y, hy⟩ := exists_nsmul_eq_of_mem_divisiblePart ((hker x).mp hx) hN.ne'
    exact hy.symm.trans card_nsmul_eq_zero'
  · rintro rfl y
    simp

end ZInQ.Manuscript.PoleS12.CTCheck

#print axioms ZInQ.Manuscript.PoleS12.CTCheck.pairing_on_family
#print axioms ZInQ.Manuscript.PoleS12.CTCheck.eleven_in_family
#print axioms ZInQ.Manuscript.PoleS12.CTCheck.retained_compatible
#print axioms ZInQ.Manuscript.PoleS12.CTCheck.nondegenerate_of_finite_sha
