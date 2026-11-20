import ZInQKernel.Contrib.OneProof.CasselsTate.PrimaryFiniteLayer

/-! The finite-level Cassels–Tate pairing suffices for the manuscript's
square property, by taking a single level that kills the finite factor. -/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti ZInQ.Cofinite CasselsTateGlobal

/-- If every `2^k`-torsion group with `k > 0` has the diagonal finite Cassels–Tate pairing
with the prescribed radical, every finite factor of a `2`-primary
decomposition has square `2`-torsion order. -/
theorem square_of_pairings_on_two_pow_torsion
    {A : Type*} {F : Type} [AddCommGroup A] [AddCommGroup F] [Finite F] {t : ℕ}
    (e : AddCommGroup.primaryComponent A 2 ≃+ (Fin t → Q2Z2) × F)
    (hPair : ∀ k : ℕ, 0 < k → let B := AddSubgroup.torsionBy A (2 ^ k : ℕ)
      ∃ b : B →+ B →+ QZ, (∀ x, b x x = 0) ∧ ∀ x,
        (∀ y, b x y = 0) ↔ ∃ z : A, 2 ^ k • z = (x : A)) :
    IsSquare (Nat.card (tors F 2)) := by
  obtain ⟨k, hkpos, hk⟩ := power_kills_finite_factor e
  obtain ⟨b, halt, hrad⟩ := hPair k hkpos
  obtain ⟨β, hβalt, hβnd⟩ := finite_factor_pairing e hk b halt hrad
  exact isSquare_card_tors_two_of_alternating (fun f => ⟨k, hk f⟩) β hβalt hβnd

/-- The finite-level Cassels–Tate pairing for an elliptic curve over `ℚ`,
specialized to `m = 2^k ≥ 2`. Its left radical is the image from level `m*m`.
Fisher, *On binary quartics and the Cassels–Tate pairing*, Res. Number Theory
8 (2022), article 74, §1 (arXiv:2208.14977v1, p. 1, display after the Selmer
exact sequence), restates Cassels' theorem for all `m ≥ 2` over a number field. -/
def FiniteSelmerCasselsTatePairing (E : WeierstrassCurve ℚ) : Prop :=
  ∀ k : ℕ, 0 < k → FiniteSelmerPairingAt E (2 ^ k)

set_option maxHeartbeats 1000000 in
/-- The finite diagonal pairings and their image formula suffice for the
Cassels–Tate square property used in the manuscript. -/
theorem casselsTateSquare_of_finiteSelmerPairing (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : FiniteSelmerCasselsTatePairing E) : CasselsTateSquare E := by
  rw [casselsTateSquare_iff_fam]
  intro t F _ _ e
  apply square_of_pairings_on_two_pow_torsion e
  intro k hk
  let m : ℕ := 2 ^ k
  have hm : IsUnit (m : ℚ) := isUnit_iff_ne_zero.mpr (by
    exact_mod_cast pow_ne_zero k (two_ne_zero : (2 : ℕ) ≠ 0))
  exact fam_sha_torsion_pairing_of_finiteSelmerPairing E m hm (h k hk)

#print axioms square_of_pairings_on_two_pow_torsion
#print axioms casselsTateSquare_of_finiteSelmerPairing

end ZInQ.Manuscript.SelmerTwoPower

namespace ZInQ.Manuscript.PoleS12

open SelmerTwoPower

/-- Finite diagonal Cassels–Tate pairings for the manuscript's curves. -/
def FiniteSelmerCasselsTatePairingCurves : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
    FiniteSelmerCasselsTatePairing (Manuscript.curve ℓ)

theorem casselsTateSquareCurves_of_finiteSelmerPairing
    (h : FiniteSelmerCasselsTatePairingCurves) : CasselsTateSquareCurves := by
  intro ℓ hp hs hmod
  have := PoleRC.curve_isElliptic (by exact_mod_cast hp.ne' : (ℓ : ℚ) ≠ 0)
  exact casselsTateSquare_of_finiteSelmerPairing _ (h ℓ hp hs hmod)

/-- Lemma 5.4 on the manuscript curves from the finite-level pairings. -/
theorem lemma54At_of_finiteSelmerPairing (h : FiniteSelmerCasselsTatePairingCurves) :
    PoleRC.Lemma54At SelmerTwoPower.SelmerCorankOne :=
  lemma54At_of_casselsTate (casselsTateSquareCurves_of_finiteSelmerPairing h)

/-- The pole-completeness argument uses only the diagonal finite-level pairings. -/
theorem poleCompleteness_of_restrictedConverseGenuine_finiteSelmerPairing
    (hRC : RestrictedConverseGenuine) (hCT : FiniteSelmerCasselsTatePairingCurves)
    (hB : BCDTThmA) (hK : KolyvaginThm1) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverseGenuine_casselsTate hRC
    (casselsTateSquareCurves_of_finiteSelmerPairing hCT) hB hK

#print axioms casselsTateSquareCurves_of_finiteSelmerPairing
#print axioms lemma54At_of_finiteSelmerPairing
#print axioms poleCompleteness_of_restrictedConverseGenuine_finiteSelmerPairing

end ZInQ.Manuscript.PoleS12
