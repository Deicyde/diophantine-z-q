import ZInQKernel.Contrib.UnramRoots.Main

/-! # `UnramRoots` is not vacuous: the unramified quadratic character of `G_{ℚ_2}` (task frob-contrib)

Let `ω ∈ ℚ̄_2` be a root of `X² + X + 1` (a primitive cube root of unity) and
`ψ(σ) = 1` if `σ ω = ω`, `ψ(σ) = −1` otherwise (values in `ℚ̄_ℓ`). Then `ψ` satisfies every
hypothesis of `G15Ram.UnramRoots 2 ℓ` for `F = ℚ_2` (`⊥`): it is multiplicative, trivial on
`G_{ℚ_2(ω)}`, and trivial on the (metric) inertia group, since inertia fixes roots of unity of odd
order. It is **not** trivial: `X² + X + 1` has no root in `ℚ_2`, so some `σ ∈ G_{ℚ_2}` moves `ω`.
Applying `UnramRootsTask.unramRoots` gives an unramified `η` with `η⁴ = ψ` and some `η(σ)⁴ = −1`.
-/

noncomputable section

namespace UnramRootsTask.Sanity

open PkgI4 (GQp)
open LadicCond Polynomial

/-- `X² + X + 1` has no root in `ℚ_2`. -/
theorem no_root_Q2 (x : ℚ_[2]) : x ^ 2 + x + 1 ≠ 0 := by
  intro hx
  by_cases h : ‖x‖ ≤ 1
  · set z : ℤ_[2] := ⟨x, h⟩
    have hz : z ^ 2 + z + 1 = 0 := by
      apply Subtype.ext
      simp only [PadicInt.coe_add, PadicInt.coe_pow, PadicInt.coe_one, PadicInt.coe_zero]
      exact hx
    have h2 := congrArg (PadicInt.toZMod (p := 2)) hz
    rw [map_add, map_add, map_pow, map_one, map_zero] at h2
    generalize PadicInt.toZMod z = a at h2
    revert a h2
    decide
  · push_neg at h
    have h2 : x ^ 2 = -(x + 1) := by linear_combination hx
    have h3 := congrArg norm h2
    rw [norm_pow, norm_neg] at h3
    have hle : ‖x + 1‖ ≤ max ‖x‖ ‖(1 : ℚ_[2])‖ := padicNormE.nonarchimedean x 1
    rw [norm_one, max_eq_left h.le] at hle
    nlinarith

theorem exists_root : ∃ w : Kbar 2, w ^ 2 + w + 1 = 0 := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_root (X ^ 2 + X + 1 : (Kbar 2)[X]) (by
    rw [show (X ^ 2 + X + 1 : (Kbar 2)[X]).degree = 2 by compute_degree!]
    decide)
  exact ⟨w, by simpa using hw⟩

/-- A primitive cube root of unity in `ℚ̄_2`. -/
def ω : Kbar 2 := exists_root.choose

theorem hω : ω ^ 2 + ω + 1 = 0 := exists_root.choose_spec

theorem hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω

instance : CharZero (Kbar 2) := (algebraMap ℚ_[2] (Kbar 2)).charZero

theorem hω0 : ω ≠ 0 := by
  intro h
  have := hω
  rw [h] at this
  simp at this

theorem hω2 : ω ^ 2 ≠ ω := by
  intro h
  have h1 : ω = 1 := by
    have : ω * (ω - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hω0
    · exact sub_eq_zero.1 h0
  have := hω
  rw [h1] at this
  norm_num at this

theorem hω4 : (ω ^ 2) ^ 2 = ω := by linear_combination ω * hω3

theorem roots {y : Kbar 2} (hy : y ^ 2 + y + 1 = 0) : y = ω ∨ y = ω ^ 2 := by
  have : (y - ω) * (y - ω ^ 2) = 0 := by linear_combination hy - y * hω + hω3
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

theorem act (σ : GQp 2) : σ ω = ω ∨ σ ω = ω ^ 2 := by
  apply roots
  have := congrArg σ hω
  simpa only [map_add, map_pow, map_one, map_zero] using this

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The unramified quadratic character of `G_{ℚ_2}` (cutting out `ℚ_2(ω) = ℚ_2(√−3)`). -/
def ψ (σ : GQp 2) : PadicAlgCl ℓ := if σ ω = ω then 1 else -1

theorem ψ_mul (σ τ : GQp 2) : ψ ℓ (σ * τ) = ψ ℓ σ * ψ ℓ τ := by
  have hne : ω ≠ ω ^ 2 := fun h => hω2 h.symm
  rcases act σ with h1 | h1 <;> rcases act τ with h2 | h2 <;>
    simp [ψ, AlgEquiv.mul_apply, h1, h2, map_pow, hω4, hω2, hne]

theorem fixSet_bot (σ : GQp 2) : σ ∈ fixSet (⊥ : Fld 2) := by
  intro x hx
  obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.1 hx
  exact σ.commutes c

/-- Some `σ ∈ G_{ℚ_2}` moves `ω`. -/
theorem exists_move : ∃ σ : GQp 2, σ ω ≠ ω := by
  by_contra hall
  push_neg at hall
  haveI : IsGalois ℚ_[2] (Kbar 2) := IsAlgClosure.isGalois ℚ_[2] (Kbar 2)
  have hmem : ω ∈ IntermediateField.fixedField (⊥ : Fld 2).fixingSubgroup :=
    fun σ => hall σ
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hmem
  apply no_root_Q2 c
  apply (algebraMap ℚ_[2] (Kbar 2)).injective
  rw [map_add, map_add, map_pow, map_one, map_zero, hc]
  exact hω

theorem ψ_nontrivial : ∃ σ ∈ fixSet (⊥ : Fld 2), ψ ℓ σ = -1 := by
  obtain ⟨σ, hσ⟩ := exists_move
  exact ⟨σ, fixSet_bot σ, by simp [ψ, hσ]⟩

theorem ψ_hyp_open : ∃ F'' : Fld 2, FiniteDimensional ℚ_[2] F'' ∧ ∀ σ ∈ fixSet F'', ψ ℓ σ = 1 := by
  have hint : IsIntegral ℚ_[2] ω := by
    refine ⟨X ^ 2 + X + 1, by monicity!, ?_⟩
    simpa [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] using hω
  refine ⟨IntermediateField.adjoin ℚ_[2] {ω}, IntermediateField.adjoin.finiteDimensional hint,
    fun σ hσ => ?_⟩
  simp [ψ, hσ ω (IntermediateField.mem_adjoin_simple_self ℚ_[2] ω)]

theorem ψ_hyp_inertia : ∀ σ ∈ fixSet (⊥ : Fld 2) ∩ inertiaSet, ψ ℓ σ = 1 := by
  intro σ hσ
  have : σ ω = ω :=
    fix_of_mem_inertiaSet_of_pow_eq_one hσ.2 (N := 3) (by norm_num) (by norm_num) hω3
  simp [ψ, this]

/-- **Non-vacuity of `UnramRoots` at `p = 2`.** The nontrivial unramified character `ψ` satisfies
the hypotheses of `G15Ram.UnramRoots 2 ℓ` (for `F = ℚ_2`), and the theorem produces an unramified
`η` with `η⁴ = ψ`, trivial on an open subgroup, with `η(σ)⁴ = −1` for some `σ`. -/
theorem unramRoots_two_nonvacuous :
    (∃ σ ∈ fixSet (⊥ : Fld 2), ψ ℓ σ ≠ 1) ∧
    ∃ η : GQp 2 → PadicAlgCl ℓ,
      (∃ F₁ : Fld 2, FiniteDimensional ℚ_[2] F₁ ∧ ∀ σ ∈ fixSet F₁, η σ = 1) ∧
      (∀ σ ∈ fixSet (⊥ : Fld 2), ∀ τ ∈ fixSet (⊥ : Fld 2), η (σ * τ) = η σ * η τ) ∧
      (∀ σ ∈ fixSet (⊥ : Fld 2), η σ ^ 4 = ψ ℓ σ) ∧
      (∀ σ ∈ fixSet (⊥ : Fld 2) ∩ inertiaSet, η σ = 1) ∧
      ∃ σ : GQp 2, η σ ^ 4 = -1 := by
  have h1ne : (-1 : PadicAlgCl ℓ) ≠ 1 := by
    haveI : CharZero (PadicAlgCl ℓ) := (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).charZero
    intro h
    have : (2 : PadicAlgCl ℓ) = 0 := by linear_combination -h
    exact two_ne_zero this
  obtain ⟨σ₀, hσ₀, hψ₀⟩ := ψ_nontrivial ℓ
  refine ⟨⟨σ₀, hσ₀, by rw [hψ₀]; exact h1ne⟩, ?_⟩
  obtain ⟨η, hη1, hη2, hη3, hη4⟩ :=
    (unramRoots : G15Ram.UnramRoots 2 ℓ) ⊥ inferInstance (ψ ℓ)
      (fun σ _ τ _ => ψ_mul ℓ σ τ) (ψ_hyp_open ℓ) (ψ_hyp_inertia ℓ)
  exact ⟨η, hη1, hη2, hη3, hη4, σ₀, by rw [hη3 σ₀ hσ₀, hψ₀]⟩

end UnramRootsTask.Sanity
