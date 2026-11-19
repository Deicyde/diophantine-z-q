import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate6Bridge
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate6Residue
import ZInQKernel.Contrib.OneProof.RC.Wiring.Data

/-!
# Theorem 5.3: the exact content of the common-coordinate leaf

`CommonCoordinateInputsLF D` holds if and only if `E_ℓ` is elliptic, the GLUE
`FrobeniusTrace (E_ℓ)` holds (a statement about `E_ℓ` alone), the graph primes of every final family
are primes of good reduction of the model `E_ℓ`, and the earlier leaf `CommonCoordinateInputsL D`
holds; and `CommonCoordinateInputsL D` is exactly (4.7) together with `ũ_x = u_{prim,x}` where
nothing is unused and `u_{prim,x}` being the `t`-expansion of an element of `F = Frac Λ`
(`commonCoordinateInputsL_iff_exact`, `commonCoordinateInputsLF_iff_exact`). The pinned Frobenius
matrix and the existential coefficient datum constrain nothing beyond the GLUE.

For data whose support contains `S₀ = {2, 3} ∪ primes of ℓ` (the headline's data, by the proved
`PreDataSpec.support_base`) the good-reduction field is automatic (`goodAt_of_support`), so the leaf is
the GLUE together with the earlier leaf (`commonCoordinateInputsLF_iff_of_support`). Contributed by
the final review (round 4); all PROVED.
-/

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)

namespace ZInQ.Manuscript.RC.Wiring

theorem commonCoordinateInputsL_iff_exact {ℓ : ℕ} (D : RCData ℓ) :
    CommonCoordinateInputsL D ↔
      CommonCoordinateTarget D ∧
      (∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
        unusedAt F x = ∅ → D.uTilde F x = D.uPrim F x) ∧
      (∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
        ∃ u : FracLam, IsTExpansion u (D.uPrim F x)) := by
  constructor
  · intro h
    refine ⟨commonCoordinateTarget_of_L h, fun Co Ce F hF x hx => ?_, fun Co Ce F hF x => ?_⟩
    · obtain ⟨M⟩ := h Co Ce F hF x
      exact M.eq_of_no_unused hx
    · obtain ⟨M⟩ := h Co Ce F hF x
      exact M.prim_mem_F
  · rintro ⟨ht, hone, hfrac⟩ Co Ce F hF x
    obtain ⟨ε, ⟨e, rfl⟩, h47⟩ := ht Co Ce F hF x
    obtain ⟨u, hu⟩ := hfrac Co Ce F hF x
    exact nonempty_trianglesL_of_eq D F x (odd_of_finalFamilyAt hF) u hu e h47 (hone Co Ce F hF x)

theorem commonCoordinateInputsLF_iff_exact {ℓ : ℕ} (D : RCData ℓ) :
    CommonCoordinateInputsLF D ↔
      (Ecurve ℓ).IsElliptic ∧ FrobeniusTrace (Ecurve ℓ) ∧
      (∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ q ∈ F.Q,
        Nonvanishing.GoodAt (Ecurve ℓ) q) ∧
      CommonCoordinateInputsL D := by
  constructor
  · intro h
    obtain ⟨hE, C, hT, hF⟩ := h
    refine ⟨hE, hT, fun Co Ce F hFam q hq => ?_, commonCoordinateInputsL_of_LF ⟨hE, C, hT, hF⟩⟩
    obtain ⟨M⟩ := hF Co Ce F hFam 0
    exact M.hgood q hq
  · rintro ⟨hE, hT, hgood, hL⟩
    have := hE
    refine ⟨hE, TateCoef.rat (Ecurve ℓ), hT, fun Co Ce F hF x => ?_⟩
    obtain ⟨M⟩ := hL Co Ce F hF x
    obtain ⟨ε, ⟨e, rfl⟩, h47⟩ := M.eq47 (odd_of_finalFamilyAt hF)
    obtain ⟨u, hu⟩ := M.prim_mem_F
    exact ⟨trianglesLF_of_eq _ hT D F x (fun q hq => ⟨(hF.1 q hq).1, (hF.1 q hq).2.1⟩)
      (hgood Co Ce F hF) u hu e h47 M.eq_of_no_unused⟩

theorem goodAt_of_support {ℓ : ℕ} (hℓ : 0 < ℓ) (D : RCData ℓ) (hS : S0 ℓ ⊆ D.S) :
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ q ∈ F.Q,
      Nonvanishing.GoodAt (Ecurve ℓ) q := by
  intro Co Ce F hF q hq
  obtain ⟨hp, -, hqS, -⟩ := hF.1 q hq
  refine goodAt_Ecurve hp fun hdvd => hqS (hS ?_)
  have hdvd' : q ∣ 6 * ℓ := by exact_mod_cast hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd' with h6 | hl
  · have h23 : q ∣ 2 * 3 := by simpa using h6
    rcases (Nat.Prime.dvd_mul hp).mp h23 with h2 | h3
    · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      simp [S0, this]
    · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      simp [S0, this]
  · simp only [S0, Finset.mem_insert, Nat.mem_primeFactors]
    exact Or.inr (Or.inr ⟨hp, hl, hℓ.ne'⟩)

/-- **For data whose support contains `S₀ = {2, 3} ∪ primes of ℓ`** (the headline's data: PROVED
`PreDataSpec.support_base`), the leaf is the GLUE plus the round-one leaf. -/
theorem commonCoordinateInputsLF_iff_of_support {ℓ : ℕ} (hℓ : 0 < ℓ) (D : RCData ℓ)
    (hS : S0 ℓ ⊆ D.S) :
    CommonCoordinateInputsLF D ↔ FrobeniusTrace (Ecurve ℓ) ∧ CommonCoordinateInputsL D := by
  constructor
  · intro h
    obtain ⟨hE, C, hT, hF⟩ := h
    exact ⟨hT, commonCoordinateInputsL_of_LF ⟨hE, C, hT, hF⟩⟩
  · rintro ⟨hT, hL⟩
    have hE := isElliptic_Ecurve hℓ
    refine ⟨hE, TateCoef.rat (Ecurve ℓ), hT, fun Co Ce F hF x => ?_⟩
    obtain ⟨M⟩ := hL Co Ce F hF x
    obtain ⟨ε, ⟨e, rfl⟩, h47⟩ := M.eq47 (odd_of_finalFamilyAt hF)
    obtain ⟨u, hu⟩ := M.prim_mem_F
    exact ⟨trianglesLF_of_eq _ hT D F x (fun q hq => ⟨(hF.1 q hq).1, (hF.1 q hq).2.1⟩)
      (goodAt_of_support hℓ D hS Co Ce F hF) u hu e h47 M.eq_of_no_unused⟩

end ZInQ.Manuscript.RC.Wiring
