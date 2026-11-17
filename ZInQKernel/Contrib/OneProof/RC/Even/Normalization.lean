import Mathlib

/-!
# Theorem 5.3, Lane RC11-even: three verifications in the construction of the even source

The 11/5 manuscript (`diophantine_zq.tex`), Appendix E. Three of Elliot's explicit checks are
finite algebra and are PROVED here:

* `coeffMap_equivariant` — **(K10)** (tex 7036–7071): the coefficient map on group bases
  `Φ_n([s]) = χ₀(s)[s̄][ψ(s)]` satisfies `Φ_n([g⁻¹s]) = χ₀(g)[ḡ]⁻¹[ψ(g)]⁻¹ Φ_n([s])`, "on each
  integral group basis before evaluation at any character";
* `twistedSum_smul` — the normalization check of (K12) (tex 7162–7168): for a quadratic character
  `χ` of a finite group acting on a module, `β_χ = Σ_g χ(g) g β` satisfies `u β_χ = χ(u) β_χ` —
  no idempotent `|G|⁻¹ Σ …` is needed;
* `sq_eq_one_mod_two_pow`, `sq_eq_one_mod_odd_prime_pow` — the support of the additive projection
  in the scalar local type (tex 7856–7884): `u² ≡ 1 (mod p^R)` exactly on `±1 + p^R ℤ_p` for odd
  `p`, and on `±1 + 2^{R−1} ℤ₂` for `p = 2`, `R ≥ 3` ("the four residue classes modulo `2^R` form
  two neighborhoods; there are not four independently assignable phases").
-/

namespace ZInQ.Manuscript.RC.Even

/-! ## (K10): equivariance of the coefficient map -/

/-- **(K10) on group bases** (tex 7041–7066; PROVED). Let `A` be a group (here
`Gal(ℚ(ζ_{F2^n})/ℚ)`), `bar : A → Γ` and `ψ : A → G` homomorphisms to commutative groups, and
`χ₀ : A → ℤˣ` a quadratic character. The map `[s] ↦ χ₀(s)[s̄][ψ(s)]` into `ℤ[Γ × G]` satisfies
`Φ([g⁻¹s]) = χ₀(g)[ḡ]⁻¹[ψ(g)]⁻¹ Φ([s])` ("since `χ₀⁻¹ = χ₀`, (K10) is equivariant"). -/
theorem coeffMap_equivariant {A Γ G : Type*} [Group A] [CommGroup Γ] [CommGroup G]
    (bar : A →* Γ) (ψ : A →* G) (χ₀ : A →* ℤˣ) (hχ : ∀ g, χ₀ g * χ₀ g = 1) (g s : A) :
    ((χ₀ (g⁻¹ * s) : ℤ) • MonoidAlgebra.single (bar (g⁻¹ * s), ψ (g⁻¹ * s)) (1 : ℤ)) =
      ((χ₀ g : ℤ) • MonoidAlgebra.single ((bar g)⁻¹, (ψ g)⁻¹) (1 : ℤ)) *
        ((χ₀ s : ℤ) • MonoidAlgebra.single (bar s, ψ s) (1 : ℤ)) := by
  -- `χ₀(g)⁻¹ = χ₀(g)` because `χ₀(g)² = 1`
  have hinv : (χ₀ g)⁻¹ = χ₀ g := inv_eq_of_mul_eq_one_right (hχ g)
  rw [smul_mul_smul_comm, MonoidAlgebra.single_mul_single, map_mul, map_mul, map_mul, map_inv,
    map_inv, map_inv, hinv, Units.val_mul, Prod.mk_mul_mk, one_mul]

/-! ## (K12): the unnormalized twisted sum -/

/-- **The twisted sum is a `χ`-eigenvector** (tex 7162–7168; PROVED): for a finite group `U`
acting linearly on `M` and a character `χ : U → ℤˣ` with `χ² = 1`, `β_χ = Σ_g χ(g) (g • β)`
satisfies `u • β_χ = χ(u) β_χ` for every `u`. -/
theorem twistedSum_smul {U M : Type*} [Group U] [Fintype U] [AddCommGroup M]
    [DistribMulAction U M] (χ : U →* ℤˣ) (hχ : ∀ g, χ g * χ g = 1) (β : M) (u : U) :
    u • (∑ g : U, (χ g : ℤ) • (g • β)) = (χ u : ℤ) • ∑ g : U, (χ g : ℤ) • (g • β) := by
  rw [Finset.smul_sum, Finset.smul_sum]
  -- reindex the right-hand sum by `g ↦ u * g`; then `χ(u) χ(u g) = χ(u)² χ(g) = χ(g)`
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun g => ?_)
  show u • ((χ g : ℤ) • g • β) = (χ u : ℤ) • (χ (u * g) : ℤ) • (u * g) • β
  rw [map_mul, Units.val_mul, smul_smul, ← mul_assoc, ← Units.val_mul, hχ u, Units.val_one,
    one_mul, mul_smul, smul_comm u ((χ g : ℤ)) (g • β)]

/-! ## The support of the local additive projection (tex 7856–7884) -/

/-- **Odd `p`** (tex 7876–7877; PROVED): `u² ≡ 1 (mod p^R)` iff `u ≡ ±1 (mod p^R)`. -/
theorem sq_eq_one_mod_odd_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (R : ℕ) (u : ℤ) :
    u ^ 2 ≡ 1 [ZMOD (p : ℤ) ^ R] ↔ u ≡ 1 [ZMOD (p : ℤ) ^ R] ∨ u ≡ -1 [ZMOD (p : ℤ) ^ R] := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have key : ∀ (n a b : ℤ), a ≡ b [ZMOD n] ↔ n ∣ a - b := fun n a b => by
    rw [Int.modEq_comm, Int.modEq_iff_dvd]
  rw [key, key, key, show u ^ 2 - 1 = (u - 1) * (u + 1) by ring, sub_neg_eq_add]
  constructor
  · intro h
    by_cases h1 : (p : ℤ) ∣ u - 1
    · left
      -- `p` cannot divide both factors: it would divide their difference `2`
      have h2 : ¬ (p : ℤ) ∣ u + 1 := by
        intro h2
        have h3 : (p : ℤ) ∣ 2 := by
          have := dvd_sub h2 h1
          rwa [show u + 1 - (u - 1) = 2 by ring] at this
        have h4 : p ∣ 2 := by exact_mod_cast h3
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
      exact hp'.pow_dvd_of_dvd_mul_right R h2 h
    · right
      exact hp'.pow_dvd_of_dvd_mul_left R h1 h
  · rintro (h | h)
    · exact h.mul_right _
    · exact h.mul_left _

/-- **`p = 2`, `R ≥ 3`** (tex 7878–7884; PROVED): for odd `u`, `u² ≡ 1 (mod 2^R)` iff
`u ≡ ±1 (mod 2^{R−1})`: the solution set is `(1 + 2^{R−1}ℤ₂) ∪ (−1 + 2^{R−1}ℤ₂)`. -/
theorem sq_eq_one_mod_two_pow {R : ℕ} (hR : 3 ≤ R) {u : ℤ} (hu : Odd u) :
    u ^ 2 ≡ 1 [ZMOD 2 ^ R] ↔ u ≡ 1 [ZMOD 2 ^ (R - 1)] ∨ u ≡ -1 [ZMOD 2 ^ (R - 1)] := by
  obtain ⟨m, rfl⟩ : ∃ m, R = m + 2 := ⟨R - 2, by omega⟩
  obtain ⟨k, rfl⟩ := hu
  have key : ∀ (n a b : ℤ), a ≡ b [ZMOD n] ↔ n ∣ a - b := fun n a b => by
    rw [Int.modEq_comm, Int.modEq_iff_dvd]
  -- with `u = 2k + 1`: `u² − 1 = 4 k (k + 1)`, `u − 1 = 2k`, `u + 1 = 2 (k + 1)`
  rw [show m + 2 - 1 = m + 1 by omega, key, key, key,
    show (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) by ring,
    show 2 * k + 1 - 1 = 2 * k by ring, show 2 * k + 1 - -1 = 2 * (k + 1) by ring,
    show (2 : ℤ) ^ (m + 2) = 4 * 2 ^ m by ring, show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m by ring,
    mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0),
    mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0),
    mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]
  constructor
  · intro h
    -- exactly one of `k`, `k + 1` is even; the odd one is coprime to `2 ^ m`
    by_cases hk : (2 : ℤ) ∣ k
    · left
      have hk1 : ¬ (2 : ℤ) ∣ k + 1 := by
        intro h'
        have h1 : (2 : ℤ) ∣ 1 := by
          have := dvd_sub h' hk
          rwa [show k + 1 - k = 1 by ring] at this
        norm_num at h1
      exact Int.prime_two.pow_dvd_of_dvd_mul_right m hk1 h
    · right
      exact Int.prime_two.pow_dvd_of_dvd_mul_left m hk h
  · rintro (h | h)
    · exact h.mul_right _
    · exact h.mul_left _

end ZInQ.Manuscript.RC.Even
