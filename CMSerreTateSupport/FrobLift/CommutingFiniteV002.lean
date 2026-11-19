import FrobLift.WildImageV001

/-!
# Conditional corollary: commuting Frobenius and tame images give a finite inertia image

Let `ρ : Gal(Ω/K) →* G` be any representation, `φ` a Frobenius lift with exponent `q ≥ 2` and `τ`
an inertia element. All of the following are explicit inputs, not proved here:

* `hcomm : Commute (ρ φ) (ρ τ)`. For a CM abelian variety over a field containing its CM field,
  the image of the whole Galois group is abelian. Commutativity of the inertia image alone is not
  enough: a Tate curve has an infinite abelian inertia image;
* finiteness of the wild image `ρ(W)`;
* density of `⟨τ⟩ W` in the inertia group (`TameGeneratorDense`), the topological-generator input.

From these: `(ρτ)^(q-1) ∈ ρ(W)` (`pow_pred_mem_wildImage_of_commute`), `ρτ` has finite order
(`isOfFinOrder_of_commute`), and for continuous `ρ` into a `T₁` group the inertia image is finite
(`finite_inertiaImage_of_commute`). The wild image is not assumed trivial and the whole image is not
assumed finite.
-/

noncomputable section

namespace FrobLift

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
  {G : Type*} [Group G] {ρ : (Ω ≃ₐ[K] Ω) →* G} {w : ValuationSubring Ω}

/-- The topological-generator input: inertia lies in the closure of `{τ^k x : k ∈ ℤ, x ∈ W}`. -/
def TameGeneratorDense (w : ValuationSubring Ω) (τ : Ω ≃ₐ[K] Ω) : Prop :=
  {σ : Ω ≃ₐ[K] Ω | PkgI2.IsInertia w σ} ⊆
    closure {σ : Ω ≃ₐ[K] Ω | ∃ k : ℤ, ∃ x ∈ wildSubgroup w, σ = τ ^ k * x}

/-- **Commuting images: `(ρτ)^(q-1)` lies in the wild image.** -/
theorem pow_pred_mem_wildImage_of_commute [Algebra.IsAlgebraic K Ω] {φ : Ω ≃ₐ[K] Ω}
    (hD : φ ∈ w.decompositionSubgroup K) {q : ℕ} (hcong : ∀ x ∈ w, w.valuation (φ x - x ^ q) < 1)
    {τ : Ω ≃ₐ[K] Ω} (hτ : PkgI2.IsInertia w τ) (hq : 1 ≤ q) (hcomm : Commute (ρ φ) (ρ τ)) :
    ρ τ ^ (q - 1) ∈ wildImage ρ w := by
  have h := frob_tame_mem_wildImage (ρ := ρ) hD hcong hτ
  have e : ρ φ * ρ τ * (ρ φ)⁻¹ = ρ τ := by rw [hcomm.eq, mul_inv_cancel_right]
  have e2 : (ρ τ)⁻¹ * ρ τ ^ q = ρ τ ^ (q - 1) := by
    conv_lhs => rw [show q = (q - 1) + 1 by omega, pow_succ']
    rw [inv_mul_cancel_left]
  rw [e, e2] at h
  exact h

/-- **Commuting images with finite wild image: `ρτ` has finite order.** -/
theorem isOfFinOrder_of_commute [Algebra.IsAlgebraic K Ω] [Finite (wildImage ρ w)]
    {φ : Ω ≃ₐ[K] Ω} (hD : φ ∈ w.decompositionSubgroup K) {q : ℕ}
    (hcong : ∀ x ∈ w, w.valuation (φ x - x ^ q) < 1) {τ : Ω ≃ₐ[K] Ω} (hτ : PkgI2.IsInertia w τ)
    (hq : 2 ≤ q) (hcomm : Commute (ρ φ) (ρ τ)) : IsOfFinOrder (ρ τ) := by
  have h := pow_pred_mem_wildImage_of_commute hD hcong hτ (by omega) hcomm
  have h1 : (⟨_, h⟩ : wildImage ρ w) ^ Nat.card (wildImage ρ w) = 1 := pow_card_eq_one'
  have h2 : ρ τ ^ ((q - 1) * Nat.card (wildImage ρ w)) = 1 := by
    rw [pow_mul]
    simpa using congrArg Subtype.val h1
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨(q - 1) * Nat.card (wildImage ρ w), ?_, h2⟩
  exact Nat.mul_pos (by omega) Nat.card_pos

/-- **Finite inertia image** from commuting images, finite wild image and the generator input. -/
theorem finite_inertiaImage_of_commute [Algebra.IsAlgebraic K Ω] [TopologicalSpace G] [T1Space G]
    (hρ : Continuous ρ) [Finite (wildImage ρ w)]
    {φ : Ω ≃ₐ[K] Ω} (hD : φ ∈ w.decompositionSubgroup K) {q : ℕ}
    (hcong : ∀ x ∈ w, w.valuation (φ x - x ^ q) < 1) {τ : Ω ≃ₐ[K] Ω} (hτ : PkgI2.IsInertia w τ)
    (hq : 2 ≤ q) (hcomm : Commute (ρ φ) (ρ τ)) (hgen : TameGeneratorDense w τ) :
    (ρ '' {σ : Ω ≃ₐ[K] Ω | PkgI2.IsInertia w σ}).Finite := by
  have hfo := isOfFinOrder_of_commute hD hcong hτ hq hcomm
  set A := {σ : Ω ≃ₐ[K] Ω | ∃ k : ℤ, ∃ x ∈ wildSubgroup w, σ = τ ^ k * x}
  set F : Set G := Set.image2 (· * ·) (Subgroup.zpowers (ρ τ) : Set G) (wildImage ρ w : Set G)
  have hZ : (Subgroup.zpowers (ρ τ) : Set G).Finite := hfo.finite_zpowers
  have hF : F.Finite := hZ.image2 _ (Set.toFinite _)
  have hAF : ρ '' A ⊆ F := by
    rintro _ ⟨σ, ⟨k, x, hx, rfl⟩, rfl⟩
    exact ⟨ρ τ ^ k, ⟨k, rfl⟩, ρ x, ⟨x, hx, rfl⟩, by rw [map_mul, map_zpow]⟩
  have hsub : ρ '' {σ : Ω ≃ₐ[K] Ω | PkgI2.IsInertia w σ} ⊆ F :=
    calc ρ '' {σ : Ω ≃ₐ[K] Ω | PkgI2.IsInertia w σ} ⊆ ρ '' closure A := Set.image_mono hgen
      _ ⊆ closure (ρ '' A) := image_closure_subset_closure_image hρ
      _ ⊆ closure F := closure_mono hAF
      _ = F := hF.isClosed.closure_eq
  exact hF.subset hsub

end FrobLift
