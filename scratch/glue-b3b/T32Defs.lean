
/-! ## T32(b) of the synthesis bundle (leaf-push's form), proved as glue -/

namespace LeafPush

-- verbatim from scratch/leaf-push/Push.lean (= scratch/h-decomposition/Leaves.lean, section 5)
/-- The absolute Galois group `G_ℚ = Aut(ℚ̄/ℚ)` (with Mathlib's Krull topology). -/
abbrev GQ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- `O` is the valuation subring `ℤ_(p)` of `ℚ`: a discrete valuation ring in which `p` is not a
unit (for any other valuation subring of `ℚ`, `p` is a unit). -/
def IsAtPrime (O : ValuationSubring ℚ) (p : ℕ) : Prop :=
  IsDiscreteValuationRing O ∧ ¬ IsUnit (p : O)

/-- The inertia subgroup `I_w ⊆ G_ℚ` of a valuation subring `w` of `ℚ̄` (Mathlib's
`ValuationSubring.inertiaSubgroup`, pushed into `G_ℚ`). -/
noncomputable def inertiaQ (w : ValuationSubring (AlgebraicClosure ℚ)) : Subgroup GQ :=
  ((w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype)

/-- **T32(b). The quadratic character of `ℚ(√d)` ramifies exactly at the primes dividing `d`,
for `d ≡ 1 mod 4` squarefree** (the quadratic Dirichlet character of odd squarefree conductor
`P` is that of `ℚ(√d)`, `d = ±P ≡ 1 mod 4`). Published: the discriminant of `ℚ(√d)` is `d`
(Neukirch I (2.?); Washington Ch. 3) and `p` ramifies iff `p | disc` (Neukirch III (2.12)),
together with "ramified ⇔ inertia acts nontrivially" (Neukirch I §9; numbering UNVERIFIED).
Lean form: for a square root `s ∈ ℚ̄` of `d` and `w` over `ℤ_(p)`, some inertia element moves `s`
iff `p | d`. `σ ↦ σ(s)/s` is the quadratic character, so this is the published statement. -/
def T32b_QuadraticRamification : Prop :=
  ∀ (d : ℤ), Squarefree d → d % 4 = 1 →
    ∀ (s : AlgebraicClosure ℚ), s ^ 2 = (d : AlgebraicClosure ℚ) →
    ∀ (p : ℕ), p.Prime →
    ∀ (O : ValuationSubring ℚ), IsAtPrime O p →
    ∀ (w : ValuationSubring (AlgebraicClosure ℚ)), w.comap (algebraMap ℚ _) = O →
      ((∃ σ ∈ inertiaQ w, σ s ≠ s) ↔ (p : ℤ) ∣ d)

end LeafPush

namespace GlueB3Unram

open scoped Pointwise

/-- `w` over `ℤ_(p)` (leaf-push's `IsAtPrime` form) lies over `p` in the sense of `LiesOver`. -/
theorem liesOver_of_isAtPrime {p : ℕ} (O : ValuationSubring ℚ) (hO : LeafPush.IsAtPrime O p)
    (w : ValuationSubring Qbar) (hw : w.comap (algebraMap ℚ Qbar) = O) : LiesOver w p := by
  unfold LiesOver
  have hpw : (p : Qbar) ∈ w := mem_of_isIntegral w (by
    simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := (p : ℤ)))
  rw [val_lt_one_iff]
  refine ⟨hpw, ?_⟩
  by_cases hp0 : (p : ℚ) = 0
  · left; rw [show (p : Qbar) = algebraMap ℚ Qbar (p : ℚ) by simp, hp0, map_zero]
  right
  intro hinv
  apply hO.2
  have hpO : ((p : ℚ)⁻¹) ∈ O := by
    rw [← hw, ValuationSubring.mem_comap]; simpa using hinv
  refine IsUnit.of_mul_eq_one (a := (p : O)) ⟨(p : ℚ)⁻¹, hpO⟩ ?_
  ext
  simp [hp0]

theorem val_intCast_eq_one {w : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime) (hw : LiesOver w p)
    (r : ℤ) (hd : ¬ (p : ℤ) ∣ r) : w.valuation (r : Qbar) = 1 := by
  rcases val_intCast hp hw r with h | h
  · exact h
  · exfalso
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime (p : ℤ) r := (Irreducible.coprime_iff_not_dvd hpr.irreducible).mpr hd
    obtain ⟨x, y, hxy⟩ := hcop
    have h1 := congrArg (fun z : ℤ => w.valuation (z : Qbar)) hxy
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one, map_one, Int.cast_natCast] at h1
    have h2 : w.valuation ((x : Qbar) * p + y * r) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one x)) hw
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one y)) (lt_of_le_of_lt h hw)
    rw [h1] at h2; exact lt_irrefl _ h2

/-- **T32(b) is glue** (proved from Mathlib): for squarefree `d ≡ 1 mod 4`, a square root `s` of
`d` and `w` over `ℤ_(p)`, some inertia element moves `s` iff `p ∣ d`. -/
theorem t32b : LeafPush.T32b_QuadraticRamification := by
  intro d hd hd4 s hs p hp O hO w hw
  have hwp : LiesOver w p := liesOver_of_isAtPrime O hO w hw
  have hd0 : d ≠ 0 := by rintro rfl; exact not_squarefree_zero hd
  constructor
  · rintro ⟨σ, hσ, hσs⟩
    by_contra hpd
    have hvd : w.valuation (d : Qbar) = 1 := val_intCast_eq_one hp hwp d hpd
    have hσs' : σ s = -s := (smul_sq_cases hs σ).resolve_left hσs
    obtain ⟨k, hk⟩ : ∃ k : ℤ, d = 4 * k + 1 := ⟨d / 4, by omega⟩
    have hk' : (d : Qbar) = 4 * k + 1 := by rw [hk]; push_cast; ring
    set t : Qbar := (1 + s) / 2 with htdef
    have ht : t ^ 2 - t - (k : Qbar) = 0 := by
      rw [htdef]; linear_combination (1 / 4 : Qbar) * hs + (1 / 4 : Qbar) * hk'
    have htint : IsIntegral ℤ t := by
      refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C k), ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X_add_C]; norm_num)
      · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C, eq_intCast]
        linear_combination ht
    have htw : t ∈ w := mem_of_isIntegral w htint
    obtain ⟨y, hy, hres⟩ := residue_inertia w σ hσ ⟨t, htw⟩
    have h1 : w.valuation (σ t - t) < 1 := by
      have h0 : IsLocalRing.residue w (y - ⟨t, htw⟩) = 0 := by rw [map_sub, hres, sub_self]
      rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h0
      have e : ((y - ⟨t, htw⟩ : w) : Qbar) = σ t - t := by
        show (y : Qbar) - t = σ t - t
        rw [hy]; rfl
      rwa [e] at h0
    have h2 : σ t - t = -s := by
      rw [htdef, map_div₀, map_add, map_one, hσs', map_ofNat]; ring
    rw [h2, Valuation.map_neg] at h1
    have h3 : w.valuation s * w.valuation s = 1 := by rw [← map_mul, ← sq, hs, hvd]
    have h4 : w.valuation s * w.valuation s < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' h1.le) h1
    rw [h3] at h4; exact lt_irrefl _ h4
  · intro hpd
    obtain ⟨m, rfl⟩ := hpd
    have hpm : ¬ (p : ℤ) ∣ m := by
      rintro ⟨n, rfl⟩
      have := hd (p : ℤ) ⟨n, by ring⟩
      rw [Int.isUnit_iff] at this
      rcases this with h | h
      · exact hp.one_lt.ne' (by exact_mod_cast h)
      · have : (0 : ℤ) ≤ p := by positivity
        omega
    have hvd : w.valuation (((p : ℤ) * m : ℤ) : Qbar) = w.valuation (p : Qbar) := by
      rw [Int.cast_mul, map_mul, val_intCast_eq_one hp hwp m hpm, mul_one, Int.cast_natCast]
    obtain ⟨σ, hσ⟩ := exists_neg_of_sq hs (not_isSquare_of_squarefree hd hp ⟨m, rfl⟩)
    obtain ⟨σ', hσ', hσ's⟩ := exists_inertia_neg p hp w hwp s _ hs hvd σ hσ
    refine ⟨σ', hσ', ?_⟩
    rw [hσ's]
    intro h
    have hs0 : s = 0 := by
      have h5 : (2 : Qbar) * s = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h5).resolve_left two_ne_zero
    rw [hs0] at hs
    have : (((p : ℤ) * m : ℤ) : Qbar) = 0 := by rw [← hs]; ring
    exact hd0 (by exact_mod_cast this)

end GlueB3Unram
