import Mathlib

/-!
# Elementary glue of step C8 (twist and weight) and of E1, over genuine Mathlib objects

* `weight_match`: the Hodge–Tate weight comparison `{n, n+1−k} = {0, −1}`, `k ≥ 1` ⇒ `k = 2`,
  `n = 0` (Tate normalization), and its cohomological variant.
* The determinant argument for the finiteness of the twisting character `ψ` (h-trust C8 items
  1-3), as group theory: (a) a character trivial-on-squares on a finite-index subgroup has finite
  image; (b) a character into the units of a field whose square has finite image has finite image.
  These are stated for an arbitrary group `G` (for C8, `G = G_ℚ` and `H = G_F`), with values in
  `Eˣ` for a field `E` (for C8, `E = \bar ℚ₅`).
-/

namespace GlueAssembly

/-- **Weight comparison, Tate normalization** (h-trust C8 "Check here"). If the weights
`{n, n + 1 − k}` of `ρ_g ⊗ χ^{-n}`-type twist equal `{0, −1}` as sets and `k ≥ 1`, then `k = 2`
and `n = 0`. -/
theorem weight_match {n k : ℤ} (hk : 1 ≤ k)
    (h : ({n, n + 1 - k} : Finset ℤ) = {0, -1}) : k = 2 ∧ n = 0 := by
  have h0 : (0 : ℤ) ∈ ({n, n + 1 - k} : Finset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + 1 - k} : Finset ℤ) := by rw [h]; simp
  have hn : n ∈ ({0, -1} : Finset ℤ) := by rw [← h]; simp
  have hm : n + 1 - k ∈ ({0, -1} : Finset ℤ) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1 hn hm
  omega

/-- **Weight comparison, cohomological normalization** (Pan's convention, weights `{0, k − 1}`):
`{n, n + k − 1} = {0, −1}`, `k ≥ 1` ⇒ `k = 2`, `n = −1` (twist by `χ¹`, rv-h-c8 `weights.py`). -/
theorem weight_match_coh {n k : ℤ} (hk : 1 ≤ k)
    (h : ({n, n + k - 1} : Finset ℤ) = {0, -1}) : k = 2 ∧ n = -1 := by
  have h0 : (0 : ℤ) ∈ ({n, n + k - 1} : Finset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + k - 1} : Finset ℤ) := by rw [h]; simp
  have hn : n ∈ ({0, -1} : Finset ℤ) := by rw [← h]; simp
  have hm : n + k - 1 ∈ ({0, -1} : Finset ℤ) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1 hn hm
  omega

/-- **Determinant argument, step 2** (h-trust C8 item 2): a homomorphism `α : G →* M` whose
values on a finite-index subgroup `H` lie in a finite set has finite image. For C8: `α = det r₅·χ⁻¹`,
`H = G_F`, `α(H) ⊆ {±1}`. -/
theorem finite_range_of_finiteIndex {G M : Type*} [Group G] [Group M] (α : G →* M)
    (H : Subgroup G) [H.FiniteIndex] (hH : (α '' H).Finite) : (Set.range α).Finite := by
  classical
  -- `G` is a finite union of cosets `g H`, and `α(gH) = α(g)·α(H)`.
  obtain ⟨T, hT⟩ : ∃ T : Finset G, ∀ g : G, ∃ t ∈ T, t⁻¹ * g ∈ H := by
    haveI := H.fintypeQuotientOfFiniteIndex
    refine ⟨(Finset.univ : Finset (G ⧸ H)).image fun q => q.out, fun g => ?_⟩
    refine ⟨(g : G ⧸ H).out, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    have := QuotientGroup.mk_out_eq_mul H g
    obtain ⟨h, hh⟩ := this
    rw [hh]; simp [mul_assoc]
  have hsub : Set.range α ⊆ ⋃ t ∈ T, (fun m => α t * m) '' (α '' H) := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨t, ht, hg⟩ := hT g
    simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨t, ht, α (t⁻¹ * g), ⟨t⁻¹ * g, hg, rfl⟩, by simp⟩
  exact Set.Finite.subset (Set.Finite.biUnion T.finite_toSet fun t _ => hH.image _) hsub

/-- **Determinant argument, step 3** (h-trust C8 item 3): a character `ψ : G →* Eˣ` into the units
of a field whose square `ψ²` has finite image has finite image (each value is a square root of
one of finitely many scalars). For C8: `ψ² = α ε_g⁻¹`. -/
theorem finite_range_of_sq {G E : Type*} [Group G] [Field E] (ψ : G →* Eˣ)
    (h : (Set.range fun g => ψ g ^ 2).Finite) : (Set.range ψ).Finite := by
  classical
  have hsub : Set.range ψ ⊆ ⋃ c ∈ h.toFinset, {x : Eˣ | (x : E) ∈ Polynomial.nthRoots 2 (c : E)} := by
    rintro _ ⟨g, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.Finite.mem_toFinset, Set.mem_range]
    refine ⟨ψ g ^ 2, ⟨g, rfl⟩, ?_⟩
    rw [Polynomial.mem_nthRoots (by norm_num)]
    simp
  refine Set.Finite.subset (Set.Finite.biUnion h.toFinset.finite_toSet fun c _ => ?_) hsub
  have hfin : ((Polynomial.nthRoots 2 (c : E)).toFinset : Set E).Finite := Finset.finite_toSet _
  refine Set.Finite.subset (hfin.preimage Units.val_injective.injOn) ?_
  intro x hx
  simpa using hx

/-- **Determinant argument, assembled** (h-trust C8 items 1-3, group-theoretic content). Let
`G` be a group with a finite-index subgroup `H`, `E` a field, and `r, ε, χ, ψ : G →* Eˣ` with
`r = ε · χ · ψ²` (`det r₅ = det ρ_g · ψ² = ε_g χ ψ²` at `k = 2`), `r² = χ²` on `H`
(`(det r₅)² = det V₅(A) = χ²` on `G_F`), and `ε` of finite image (a nebentypus). Then `ψ` has
finite image. -/
theorem twist_finite {G E : Type*} [Group G] [Field E] (H : Subgroup G) [H.FiniteIndex]
    (r ε χ ψ : G →* Eˣ) (hdet : ∀ g, r g = ε g * χ g * ψ g ^ 2)
    (hH : ∀ h ∈ H, r h ^ 2 = χ h ^ 2) (hε : (Set.range ε).Finite) : (Set.range ψ).Finite := by
  classical
  -- `α = r χ⁻¹` is `±1` on `H`, hence of finite image.
  let α : G →* Eˣ := r * χ⁻¹
  have hαH : (α '' H).Finite := by
    refine Set.Finite.subset ((Polynomial.nthRoots 2 (1 : E)).toFinset.finite_toSet.preimage
      Units.val_injective.injOn) ?_
    rintro _ ⟨h, hh, rfl⟩
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_nthRoots (by norm_num)]
    have := hH h hh
    have e : (α h) ^ 2 = 1 := by
      simp only [α, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, inv_pow, this,
        mul_inv_cancel]
    have := congrArg Units.val e
    simpa using this
  have hα := finite_range_of_finiteIndex α H hαH
  -- `ψ² = α ε⁻¹`.
  have hsq : (Set.range fun g => ψ g ^ 2) ⊆ (fun p : Eˣ × Eˣ => p.1 * p.2⁻¹) '' (Set.range α ×ˢ Set.range ε) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨(α g, ε g), ⟨⟨g, rfl⟩, ⟨g, rfl⟩⟩, ?_⟩
    simp only [α, MonoidHom.mul_apply, MonoidHom.inv_apply, hdet]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have h1 := (ε g).ne_zero
    have h2 := (χ g).ne_zero
    field_simp
  exact finite_range_of_sq ψ (((hα.prod hε).image _).subset hsq)

end GlueAssembly
