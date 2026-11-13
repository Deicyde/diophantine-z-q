import Mathlib

/-!
# T31, global part: elements with a unit derivative at an unramified prime

Let `L/ℚ` be a finite Galois extension, `G = Gal(L/ℚ)` acting on `𝓞 L`, and `w` a maximal ideal
of `𝓞 L` with trivial inertia group. Then there is `b₀ ∈ 𝓞 L` such that for every `y ∈ 𝓞 L`
and `b = b₀ + p y` (`p ∈ w`), `b - τ b ∉ w` for every `τ ∈ G` moving `b`; hence the derivative
of the minimal polynomial of `b` at `b` is not in `w`.

Construction: `θ` lifts a generator of the cyclic group `(𝓞 L ⧸ w)ˣ`, and `b₀ ≡ θ (mod w)`,
`b₀ ∈ ρ • w` for every conjugate `ρ • w ≠ w`.
-/

namespace T31

open NumberField Polynomial
open scoped Pointwise

variable {L : Type*} [Field L] [NumberField L]

local notation "G" => L ≃ₐ[ℚ] L

/-- The ideal `I = ⋂_{ρ • w ≠ w} ρ • w`. -/
noncomputable def otherConj (w : Ideal (𝓞 L)) : Ideal (𝓞 L) :=
  (Finset.univ.filter (fun ρ : G => ρ • w ≠ w)).inf (fun ρ => ρ • w)

theorem mem_otherConj {w : Ideal (𝓞 L)} {x : 𝓞 L} (hx : x ∈ otherConj w) (ρ : G)
    (hρ : ρ • w ≠ w) : x ∈ ρ • w := by
  unfold otherConj at hx
  have hmem : ρ ∈ (Finset.univ.filter (fun ρ : G => ρ • w ≠ w)) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hρ⟩
  exact (Finset.inf_le (f := fun ρ : G => ρ • w) hmem) hx

/-- `b` is good for `(w, θ)`. -/
def IsGood (w : Ideal (𝓞 L)) (θ b : 𝓞 L) : Prop :=
  b - θ ∈ w ∧ b ∈ otherConj w

theorem smul_mem_of_stab {w : Ideal (𝓞 L)} {τ : G} (hτ : τ • w = w) {x : 𝓞 L} (hx : x ∈ w) :
    τ • x ∈ w := by
  rw [← hτ]; exact Ideal.smul_mem_pointwise_smul τ x w hx

theorem natCast_mem_smul {w : Ideal (𝓞 L)} (ρ : G) {n : ℕ} (hn : (n : 𝓞 L) ∈ w) :
    (n : 𝓞 L) ∈ ρ • w := by
  have := Ideal.smul_mem_pointwise_smul ρ (n : 𝓞 L) w hn
  have h2 : ρ • (n : 𝓞 L) = n := map_natCast (MulSemiringAction.toRingHom G (𝓞 L) ρ) n
  rwa [h2] at this


theorem otherConj_not_le (w : Ideal (𝓞 L)) [hw : w.IsMaximal] : ¬ otherConj w ≤ w := by
  intro h
  rw [otherConj, Ideal.IsPrime.inf_le' hw.isPrime] at h
  obtain ⟨ρ, hρ, hle⟩ := h
  have hρ' : ρ • w ≠ w := (Finset.mem_filter.1 hρ).2
  apply hρ'
  have h1 : w ≤ ρ⁻¹ • w := Ideal.pointwise_smul_subset_iff.1 hle
  have h2 : ρ⁻¹ • w ≠ ⊤ := by
    intro htop
    have : (1 : 𝓞 L) ∈ ρ⁻¹ • w := htop ▸ Submodule.mem_top
    rw [Ideal.mem_inv_pointwise_smul_iff, smul_one] at this
    exact hw.ne_top ((Ideal.eq_top_iff_one w).2 this)
  have h3 : w = ρ⁻¹ • w := hw.eq_of_le h2 h1
  calc ρ • w = ρ • ρ⁻¹ • w := by rw [← h3]
    _ = w := smul_inv_smul ρ w

theorem exists_isGood (w : Ideal (𝓞 L)) [hw : w.IsMaximal] (θ : 𝓞 L) : ∃ b, IsGood w θ b := by
  have hsup : otherConj w ⊔ w = ⊤ := by
    by_contra hne
    have h1 : w = otherConj w ⊔ w := hw.eq_of_le hne le_sup_right
    exact otherConj_not_le w (le_sup_left.trans h1.symm.le)
  have h1 : (1 : 𝓞 L) ∈ otherConj w ⊔ w := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨i, hi, j, hj, hij⟩ := (Submodule.mem_sup (p := otherConj w) (p' := w)).1 h1
  refine ⟨θ * i, ?_, Ideal.mul_mem_left _ _ hi⟩
  have : θ * i - θ = -(θ * j) := by
    have : θ = θ * (i + j) := by rw [hij, mul_one]
    nth_rewrite 2 [this]; ring
  rw [this]; exact neg_mem (Ideal.mul_mem_left _ _ hj)

theorem isGood_add {w : Ideal (𝓞 L)} {θ b : 𝓞 L} (hb : IsGood w θ b) {p : ℕ}
    (hp : (p : 𝓞 L) ∈ w) (y : 𝓞 L) : IsGood w θ (b + p * y) := by
  refine ⟨?_, ?_⟩
  · rw [show b + p * y - θ = (b - θ) + p * y by ring]
    exact add_mem hb.1 (Ideal.mul_mem_right _ _ hp)
  · refine add_mem hb.2 (Ideal.mul_mem_right _ _ ?_)
    unfold otherConj
    rw [Submodule.mem_finsetInf]
    intro ρ _
    exact natCast_mem_smul ρ hp

theorem exists_gen (w : Ideal (𝓞 L)) [hw : w.IsMaximal] (hw0 : w ≠ ⊥) :
    ∃ θ : 𝓞 L, θ ∉ w ∧ ∀ x : 𝓞 L, x ∈ w ∨ ∃ k : ℕ, x - θ ^ k ∈ w := by
  let := Ideal.Quotient.field w
  have : Finite (𝓞 L ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hw0
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (𝓞 L ⧸ w)ˣ)
  obtain ⟨θ, hθ⟩ := Ideal.Quotient.mk_surjective (g : 𝓞 L ⧸ w)
  refine ⟨θ, fun h => ?_, fun x => ?_⟩
  · have : (g : 𝓞 L ⧸ w) = 0 := by rw [← hθ]; exact Ideal.Quotient.eq_zero_iff_mem.2 h
    exact g.ne_zero this
  · by_cases hx : x ∈ w
    · exact Or.inl hx
    · right
      have hx0 : Ideal.Quotient.mk w x ≠ 0 := fun h => hx (Ideal.Quotient.eq_zero_iff_mem.1 h)
      have hmem : Units.mk0 _ hx0 ∈ Subgroup.zpowers g := hg _
      rw [← mem_powers_iff_mem_zpowers] at hmem
      obtain ⟨k, hk⟩ := hmem
      refine ⟨k, Ideal.Quotient.eq.1 ?_⟩
      have := congrArg (fun u : (𝓞 L ⧸ w)ˣ => (u : 𝓞 L ⧸ w)) hk
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
      rw [← this, map_pow, hθ]

variable [IsGalois ℚ L]

theorem inertia_trivial (w : Ideal (𝓞 L)) [hw : w.IsPrime] (he : w.ramificationIdx ℤ = 1)
    (τ : G) (hτ : ∀ x : 𝓞 L, τ • x - x ∈ w) : τ = 1 := by
  have hmem : τ ∈ w.inertia G := Ideal.mem_inertia.2 hτ
  have hcard : Nat.card (w.inertia G) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (w.under ℤ) w,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.under ℤ) w G, he]
  rw [Subgroup.card_eq_one.1 hcard] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem sub_smul_not_mem (w : Ideal (𝓞 L)) [hw : w.IsMaximal] (he : w.ramificationIdx ℤ = 1)
    {θ : 𝓞 L} (hθ0 : θ ∉ w) (hθ : ∀ x : 𝓞 L, x ∈ w ∨ ∃ k : ℕ, x - θ ^ k ∈ w)
    {b : 𝓞 L} (hb : IsGood w θ b) (τ : G) (hτb : τ • b ≠ b) : b - τ • b ∉ w := by
  intro h
  by_cases hτw : τ • w = w
  · apply hτb
    have hτθ : τ • θ - θ ∈ w := by
      have e : τ • θ - θ = τ • (θ - b) - (b - τ • b) + (b - θ) := by rw [smul_sub]; ring
      rw [e]
      refine add_mem (sub_mem (smul_mem_of_stab hτw ?_) h) hb.1
      rw [← neg_sub]; exact neg_mem hb.1
    have hall : ∀ x : 𝓞 L, τ • x - x ∈ w := by
      intro x
      rcases hθ x with hx | ⟨k, hk⟩
      · exact sub_mem (smul_mem_of_stab hτw hx) hx
      · have e : τ • x - x = τ • (x - θ ^ k) + ((τ • θ) ^ k - θ ^ k) - (x - θ ^ k) := by
          rw [smul_sub, smul_pow']; ring
        rw [e]
        refine sub_mem (add_mem (smul_mem_of_stab hτw hk) ?_) hk
        exact Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ _) hτθ
    rw [inertia_trivial w he τ hall, one_smul]
  · have hinv : τ⁻¹ • w ≠ w := by
      intro h'
      apply hτw
      calc τ • w = τ • τ⁻¹ • w := by rw [h']
        _ = w := smul_inv_smul τ w
    have h1 : τ • b ∈ w := Ideal.mem_inv_pointwise_smul_iff.1 (mem_otherConj hb.2 τ⁻¹ hinv)
    have h2 : b ∈ w := by
      have := add_mem h h1
      rwa [sub_add_cancel] at this
    apply hθ0
    have := sub_mem h2 hb.1
    rwa [sub_sub_cancel] at this

end T31
