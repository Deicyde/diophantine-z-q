import ZInQKernel.RouteK.Assembly.SecondCurve

/-!
# Route K: the descent lemma DL

`docs/research/slot-k.md` §1.3 and §2.5. For every admissible `B` there are a signed divisor `m`
of 2730 and an integer `n` with `β ∣ n` (`β = sqf(mB)`, `θ = sqf(m(m − B))`) such that both
`C_{|n|}` and `C_{|nθ|}` carry a certificate of Selmer type: the system `Σ` of each curve has
exactly 8 solutions and contains the class of `β` (`SelmerCertified`).

The construction: step 0 and the slots (`exists_multiplier_and_slots`, from `dl-slots`), then
`n = d₁ = |β| q₀ Π r_p Π r_ℓ > 0` with the two curves of `FirstCurve.lean` and `SecondCurve.lean`.
Besides the certificates, DL records the arithmetic that the deep input CR₃ asks for: `n` and `nθ`
are squarefree, `|n| ≡ |nθ| ≡ 5` and `|β| ≡ 7 (mod 8)`.
-/

namespace ZInQ.RouteK

open scoped BigOperators

theorem sqf_zero : sqf 0 = 0 := by simp [sqf, sqfInt]

/-- The properties (θ1)–(θ4) and the oddness of `β`, in the form used by the proof of DL. -/
theorem inputs_of_admissible {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730)
    (hβ : Odd (betaOf B m)) (h7 : (betaOf B m).natAbs % 8 = 7) {p₀ : ℕ}
    (hp₀ : p₀ ∈ primesOf (betaOf B m)) : Inputs (betaOf B m) (thetaOf B m) p₀ := by
  obtain ⟨hθpos, hθ8, -⟩ := theta1 hB hm
  have hcop := theta2_isCoprime hB hm
  have hmB : (m : ℚ) * B ≠ 0 := by
    intro h
    have : betaOf B m = 0 := by rw [betaOf, h, sqf_zero]
    rw [this] at hβ
    exact (Int.not_even_iff_odd.mpr hβ) (by decide)
  have hmθ : (m : ℚ) * (m - B) ≠ 0 := by
    intro h
    have : thetaOf B m = 0 := by rw [thetaOf, h, sqf_zero]
    omega
  have hdisj : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ betaOf B m → (q : ℤ) ∣ thetaOf B m → False :=
    fun q hq h1 h2 => (Nat.prime_iff_prime_int.mp hq).not_isUnit (hcop.isUnit_of_dvd' h1 h2)
  refine ⟨sqf_squarefree hmB, hβ, h7, hp₀, hθpos, hθ8, sqf_squarefree hmθ, hcop, ?_, ?_⟩
  · intro ℓ hℓ
    obtain ⟨hℓp, hℓθ, -⟩ := mem_primesOf.mp hℓ
    have := Fact.mk hℓp
    rw [legBit_eq_zero_iff (by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact fun h => hdisj ℓ hℓp h hℓθ)]
    exact theta3 hB hm ℓ hℓθ
  · intro p hp
    obtain ⟨hpp, hpβ, -⟩ := mem_primesOf.mp hp
    have := Fact.mk hpp
    rw [legBit_eq_zero_iff (by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact fun h => hdisj p hpp hpβ h)]
    exact theta4 hB hm p hpβ

/-- **DL** (slot-k §1.3, proved in §2.5): for every admissible `B` there are a signed divisor `m`
of 2730 and an integer `n` with `β ∣ n`, `|n| ≡ 5 (mod 8)` and `|β| ≡ 7 (mod 8)`, where
`β = sqf(mB)` and `θ = sqf(m(m − B))`, such that `n` and `nθ` are squarefree, `|nθ| ≡ 5 (mod 8)`,
and both `|n|` and `|nθ|` have configurations whose systems have exactly 8 solutions, one of them
with first coordinate the class of `β`. -/
theorem descent_lemma {B : ℚ} (hB : Admissible B) :
    ∃ m n : ℤ, m ∣ 2730 ∧ betaOf B m ∣ n ∧ n.natAbs % 8 = 5 ∧ (betaOf B m).natAbs % 8 = 7 ∧
      Squarefree n ∧ Squarefree (n * thetaOf B m) ∧ (n * thetaOf B m).natAbs % 8 = 5 ∧
      SelmerCertified n.natAbs (betaOf B m) ∧
      SelmerCertified (n * thetaOf B m).natAbs (betaOf B m) := by
  obtain ⟨m, hm, hβ, h7, ⟨p₀, hp₀⟩, hslots⟩ := exists_multiplier_and_slots hB
  obtain ⟨D⟩ := hslots p₀ hp₀
  have hI := inputs_of_admissible hB hm hβ h7 hp₀
  have hn : ((D.d₁ : ℤ) * thetaOf B m).natAbs = D.d₂ := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, D.d₂_eq hI]
  refine ⟨m, D.d₁, hm, D.β_dvd_d₁ hI, D.d₁_mod hI, h7, Int.squarefree_natCast.mpr
    (D.squarefree_d₁ hI), ?_, ?_, D.selmerCertified_d₁ hI, ?_⟩
  · rw [← Int.squarefree_natAbs, hn]; exact D.squarefree_d₂ hI
  · rw [hn, D.d₂_eq hI, Nat.mul_mod, D.d₁_mod hI, hI.θ_natAbs_mod]
  · rw [hn]; exact D.selmerCertified_d₂ hI

end ZInQ.RouteK
