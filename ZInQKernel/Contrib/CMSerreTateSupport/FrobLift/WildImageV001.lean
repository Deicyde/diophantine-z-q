import ZInQKernel.Contrib.CMSerreTateSupport.FrobLift.WildSubgroupV001

/-!
# Frobenius and tame covariance of the wild image under an arbitrary representation

Let `ρ : Gal(Ω/K) →* G` be any group homomorphism (for instance the Galois action on a Tate module).
Write `ρ(W)` for the image of the wild subgroup of `w` and `ρ(D)` for the image of the decomposition
group. Then:

* `ρ(W) ≤ ρ(D)`, and `ρ(D)` normalizes `ρ(W)`; in particular the image of every Frobenius lift and
  of every inertia element lies in the normalizer of `ρ(W)` (`mem_normalizer_wildImage`);
* for a Frobenius lift `φ` (congruence exponent `q`) and an inertia element `τ`,
  `(ρφ ρτ ρφ⁻¹)⁻¹ (ρτ)^q ∈ ρ(W)` (`frob_tame_mem_wildImage`);
* `ρ(W)` is normal in `ρ(D)`, and in the quotient `ρ(D) ⧸ ρ(W)` the relation is exact:
  `Φ T Φ⁻¹ = T^q` (`frob_tame_relation_quotient`);
* with the constructed Frobenius lift, `2 ≤ q` and `q` is prime to every `ℓ` invertible in `O`
  (`exists_frobenius_wildImage_relation`).
-/

noncomputable section

namespace FrobLift

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
  {G : Type*} [Group G] (ρ : (Ω ≃ₐ[K] Ω) →* G) (w : ValuationSubring Ω)

/-- The image `ρ(W)` of the wild subgroup. -/
abbrev wildImage : Subgroup G := (wildSubgroup w).map ρ

/-- The image `ρ(D)` of the decomposition group. -/
abbrev decompImage : Subgroup G := (w.decompositionSubgroup K).map ρ

theorem wildSubgroup_le_decomposition : wildSubgroup w ≤ w.decompositionSubgroup K :=
  fun _ h => mem_decomposition_of_wild h

theorem wildImage_le_decompImage : wildImage ρ w ≤ decompImage ρ w :=
  Subgroup.map_mono (wildSubgroup_le_decomposition w)

variable {ρ w}

theorem conj_mem_wildImage [Algebra.IsAlgebraic K Ω] {g : Ω ≃ₐ[K] Ω}
    (hg : g ∈ w.decompositionSubgroup K) {x : G} (hx : x ∈ wildImage ρ w) :
    ρ g * x * (ρ g)⁻¹ ∈ wildImage ρ w := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  exact ⟨g * σ * g⁻¹, conj_mem_wildSubgroup hg hσ, by rw [map_mul, map_mul, map_inv]⟩

/-- **The image of the decomposition group normalizes the wild image.** -/
theorem mem_normalizer_wildImage [Algebra.IsAlgebraic K Ω] {g : Ω ≃ₐ[K] Ω}
    (hg : g ∈ w.decompositionSubgroup K) :
    ρ g ∈ Subgroup.normalizer (wildImage ρ w : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_wildImage hg
  · intro h
    have h' := conj_mem_wildImage (inv_mem hg) h
    rw [map_inv, inv_inv] at h'
    simpa [mul_assoc] using h'

/-- **Frobenius–tame relation modulo the wild image**, for any representation. -/
theorem frob_tame_mem_wildImage [Algebra.IsAlgebraic K Ω] {φ : Ω ≃ₐ[K] Ω}
    (hD : φ ∈ w.decompositionSubgroup K) {q : ℕ} (hcong : ∀ x ∈ w, w.valuation (φ x - x ^ q) < 1)
    {τ : Ω ≃ₐ[K] Ω} (hτ : PkgI2.IsInertia w τ) :
    (ρ φ * ρ τ * (ρ φ)⁻¹)⁻¹ * ρ τ ^ q ∈ wildImage ρ w :=
  ⟨(φ * τ * φ⁻¹)⁻¹ * τ ^ q, WildTameCharacter.isWild_frobenius_of_inertia q hτ hD hcong, by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, map_pow]⟩

/-- The wild image as a subgroup of the decomposition image. -/
abbrev wildImageIn : Subgroup (decompImage ρ w) := (wildImage ρ w).subgroupOf (decompImage ρ w)

/-- **The wild image is normal in the decomposition image.** -/
theorem wildImageIn_normal [Algebra.IsAlgebraic K Ω] : (wildImageIn (ρ := ρ) (w := w)).Normal := by
  constructor
  intro n hn h
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨g, hg, hgh⟩ := h.2
  have e : ((h * n * h⁻¹ : decompImage ρ w) : G) = ρ g * (n : G) * (ρ g)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hgh]
  rw [e]
  exact conj_mem_wildImage hg hn

/-- The image of an element of the decomposition group, as an element of `ρ(D)`. -/
def decompElt {g : Ω ≃ₐ[K] Ω} (hg : g ∈ w.decompositionSubgroup K) : decompImage ρ w :=
  ⟨ρ g, g, hg, rfl⟩

/-- **The Frobenius–tame relation is exact in `ρ(D) ⧸ ρ(W)`.** -/
theorem frob_tame_relation_quotient [Algebra.IsAlgebraic K Ω] {φ : Ω ≃ₐ[K] Ω}
    (hD : φ ∈ w.decompositionSubgroup K) {q : ℕ} (hcong : ∀ x ∈ w, w.valuation (φ x - x ^ q) < 1)
    {τ : Ω ≃ₐ[K] Ω} (hτ : PkgI2.IsInertia w τ) :
    haveI := wildImageIn_normal (ρ := ρ) (w := w)
    ((decompElt (ρ := ρ) hD : decompImage ρ w ⧸ wildImageIn (ρ := ρ) (w := w)) *
        (decompElt (ρ := ρ) hτ.1 : decompImage ρ w ⧸ wildImageIn (ρ := ρ) (w := w)) *
        (decompElt (ρ := ρ) hD : decompImage ρ w ⧸ wildImageIn (ρ := ρ) (w := w))⁻¹) =
      (decompElt (ρ := ρ) hτ.1 : decompImage ρ w ⧸ wildImageIn (ρ := ρ) (w := w)) ^ q := by
  haveI := wildImageIn_normal (ρ := ρ) (w := w)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
    QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h := frob_tame_mem_wildImage (ρ := ρ) hD hcong hτ
  simpa [decompElt] using h

end FrobLift

namespace FrobLift

variable {K : Type} [Field K] [NumberField K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {w : ValuationSubring Ω}
  {G : Type*} [Group G]

/-- **The constructed Frobenius lift, under any representation `ρ`**: `ρ φ` and the image of every
inertia element normalize `ρ(W)`, and `(ρφ ρτ ρφ⁻¹)⁻¹ (ρτ)^q ∈ ρ(W)`, with `2 ≤ q` and `q` prime to
every `ℓ` invertible in `O`. -/
theorem exists_frobenius_wildImage_relation (hw : w.comap (algebraMap K Ω) = O)
    (ρ : (Ω ≃ₐ[K] Ω) →* G) :
    ∃ φ : Ω ≃ₐ[K] Ω, φ ∈ w.decompositionSubgroup K ∧
      2 ≤ Nat.card (IsLocalRing.ResidueField O) ∧
      (∀ ℓ : ℕ, IsUnit (ℓ : O) → Nat.Coprime ℓ (Nat.card (IsLocalRing.ResidueField O))) ∧
      (∀ x ∈ w, w.valuation (φ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1) ∧
      ρ φ ∈ Subgroup.normalizer (wildImage ρ w : Set G) ∧
      ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
        ρ τ ∈ Subgroup.normalizer (wildImage ρ w : Set G) ∧
        (ρ φ * ρ τ * (ρ φ)⁻¹)⁻¹ * ρ τ ^ Nat.card (IsLocalRing.ResidueField O) ∈ wildImage ρ w := by
  obtain ⟨φ, hD, hcong⟩ := exists_frobenius_lift hw
  exact ⟨φ, hD, two_le_card_residueField O, fun ℓ hℓ => coprime_card_residueField_of_isUnit O hℓ,
    hcong, mem_normalizer_wildImage hD,
    fun τ hτ => ⟨mem_normalizer_wildImage hτ.1, frob_tame_mem_wildImage hD hcong hτ⟩⟩

end FrobLift
