import ZInQKernel.Contrib.OneProof.RC.CoefModules.LocalConditions

/-!
# Lane RC29 (round 2): the inflation of the cyclotomic twist `A(1)` is a cyclotomic twist

Manuscript `diophantine_zq.tex` (11/5), tex 2798–2805 ("The Weil pairing gives the following
`R_i`-linear perfect pairing: `M_i ⊗_{R_i} τ^*M_i → R_i(1)` … `e_2` transforms by the cyclotomic
character") and the support comparisons, tex 3466–3499 (the coefficient modules live over
`G_{K,S₀}`, `S₀` the ramification support of the coefficients; the Selmer complexes over
`G_{K,S}`, `S₀ ⊆ S`).

The finite Selmer duality of lane RC29 (`orthSelmerDuality_actualKummer`, round 1) applies lane
RC26's PRINT `NekovarProp543T` over `G_{K,S}` to the inflated Weil pairing
`M_i × M_i(α⁻¹) → A_i(1)`, whose target is lane RC28's `Tate1 A_i hμ₀` over `G_{K,S₀}` inflated to
`G_{K,S}`. The PRINT needs that target to be a cyclotomic twist over `S` (lane RC26's
`IsCyclotomicTwist`). Round 1 left this as the hypothesis `hT`. This file proves it, in small
steps:

* `cycloInflIncl`: the inclusion `K_{S₀} ⊆ K_S` (`unramifiedOutside_mono`) as a `K`-algebra map.
* `cycloInfl_inflMap_resAbs`, `cycloInfl_galS_incl`: **the action formula**. An element
  `g ∈ G_{K,S}` acts on `K_{S₀} ⊆ K_S` through its restriction `inflMap g ∈ G_{K,S₀}`, where
  `inflMap = resUnrCont`. The proof lifts `g` to `Gal(K̄/K)` and uses `resUnr_comp` and
  `resAbs_apply_coe`.
* `cycloInflRootsEquiv`: the `N`-th roots of unity of `K_S` as a subtype are Mathlib's
  `rootsOfUnity N K_S`.
* `cycloInfl_hasRootsOfUnity_of_card`: a field `K_S` with exactly `N` `N`-th roots of unity has
  a primitive one (their group is cyclic).
* `cycloInfl_hasRootsOfUnity`: a primitive `N`-th root of unity of `K_{S₀}` stays primitive in
  `K_S`.
* `cycloInfl_card_roots`: then `K_S` has exactly `N` `N`-th roots of unity
  (`card_rootsOfUnity_KS`).
* `cycloInfl_galS_root`: every `N`-th root of unity of `K_S` is a power of the image of the
  primitive root of `K_{S₀}`. So if `inflMap g` raises the `N`-th roots of unity of `K_{S₀}` to
  the power `c`, then `g` raises those of `K_S` to the power `c`.
* **`cycloInfl_isCyclotomicTwist`**: for `S₀ ⊆ S`, the inflation `InflMod hS T₀` of a cyclotomic
  twist `T₀` over `S₀` is a cyclotomic twist over `S`.
* **`cycloInfl_isCyclotomicTwist_tate1`**:
  `IsCyclotomicTwist K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀))`. This is round 1's `hT`.
* Non-vacuity at `i = 1`: `cycloInfl_hasRootsOfUnity_two` (`-1` is a primitive square root of
  unity of every `K_S`) and `cycloInfl_isCyclotomicTwist_tate1_one`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside unramifiedOutside_mono GaloisGroupS
  resAbs resAbs_apply_coe resAbs_surjective resUnr_comp)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S₀ S : Set (HeightOneSpectrum (𝓞 K))}

/-! ### The inclusion `K_{S₀} ⊆ K_S` and the action formula -/

/-- **The inclusion `K_{S₀} ⊆ K_S`** for `S₀ ⊆ S` (`unramifiedOutside_mono`), as a `K`-algebra
map. -/
def cycloInflIncl (hS : S₀ ⊆ S) : KS K S₀ →ₐ[K] KS K S :=
  IntermediateField.inclusion (unramifiedOutside_mono K hS)

omit [NumberField K] in
/-- The inclusion does not move the underlying element of `K̄`. PROVED (Mathlib's
`IntermediateField.coe_inclusion`; a bare `rfl` here makes the kernel unfold `K_S`). -/
theorem cycloInflIncl_coe (hS : S₀ ⊆ S) (x : KS K S₀) :
    ((cycloInflIncl hS x : KS K S) : AlgebraicClosure K) = (x : AlgebraicClosure K) :=
  IntermediateField.coe_inclusion _ x

omit [NumberField K] in
/-- The inclusion is injective. PROVED. -/
theorem cycloInflIncl_injective (hS : S₀ ⊆ S) : Function.Injective (cycloInflIncl hS) :=
  IntermediateField.inclusion_injective _

/-- **The restriction `inflMap : G_{K,S} → G_{K,S₀}` of a restriction from `Gal(K̄/K)`** is the
restriction to `K_{S₀}` (lane RC26's `inflMap` is the tree's `resUnrCont`; `resUnr_comp`).
PROVED. -/
theorem cycloInfl_inflMap_resAbs (hS : S₀ ⊆ S) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    inflMap K hS (resAbs K S σ) = resAbs K S₀ σ :=
  resUnr_comp K hS σ

/-- **The action formula**: `g ∈ G_{K,S}` acts on `K_{S₀} ⊆ K_S` through its restriction
`inflMap g ∈ G_{K,S₀}`: `g (x) = (inflMap g)(x)` for `x ∈ K_{S₀}`. PROVED (lift `g` to
`Gal(K̄/K)`). -/
theorem cycloInfl_galS_incl (hS : S₀ ⊆ S) (g : GKS K S) (x : KS K S₀) :
    galS K S g (cycloInflIncl hS x) = cycloInflIncl hS (galS K S₀ (inflMap K hS g) x) := by
  obtain ⟨σ, hσ⟩ := resAbs_surjective K S (g : GaloisGroupS K S)
  have h1 : inflMap K hS g = resAbs K S₀ σ := by
    rw [← cycloInfl_inflMap_resAbs hS σ, hσ]
  apply Subtype.ext
  have h2 : ((galS K S g (cycloInflIncl hS x) : KS K S) : AlgebraicClosure K) =
      σ ((cycloInflIncl hS x : KS K S) : AlgebraicClosure K) := by
    rw [← hσ]
    exact resAbs_apply_coe K S σ (cycloInflIncl hS x)
  have h3 : ((galS K S₀ (inflMap K hS g) x : KS K S₀) : AlgebraicClosure K) =
      σ (x : AlgebraicClosure K) := by
    rw [h1]
    exact resAbs_apply_coe K S₀ σ x
  rw [h2, cycloInflIncl_coe, cycloInflIncl_coe, h3]

/-! ### Roots of unity of `K_{S₀}` and `K_S` -/

section Roots

variable (S) in
/-- The `N`-th roots of unity of `K_S`, as a subtype, are Mathlib's `rootsOfUnity N K_S`. -/
def cycloInflRootsEquiv (N : ℕ) [NeZero N] :
    {x : KS K S // x ^ N = 1} ≃ rootsOfUnity N (KS K S) where
  toFun x := ⟨Units.mk0 x.1 (by
      rintro h0
      have h := x.2
      rw [h0, zero_pow (NeZero.ne N)] at h
      exact zero_ne_one h), by
      rw [mem_rootsOfUnity]
      exact Units.ext (by simpa using x.2)⟩
  invFun u := ⟨((u : (KS K S)ˣ) : KS K S), by
      have h := (mem_rootsOfUnity _ _).mp u.2
      rw [← Units.val_pow_eq_pow_val, h, Units.val_one]⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

/-- **A field `K_S` with exactly `N` `N`-th roots of unity contains a primitive one** (the group
of `N`-th roots of unity of a field is cyclic; a generator has order `N`). PROVED. -/
theorem cycloInfl_hasRootsOfUnity_of_card {N : ℕ} [NeZero N]
    (hcard : Nat.card {ζ : unramifiedOutside K S // ζ ^ N = 1} = N) : HasRootsOfUnity K S N := by
  have hc : Nat.card (rootsOfUnity N (KS K S)) = N := by
    rw [← Nat.card_congr (cycloInflRootsEquiv S N)]
    exact hcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity N (KS K S))
  rw [hc] at hg
  have h1 : IsPrimitiveRoot g N := by
    have h0 := IsPrimitiveRoot.orderOf g
    rwa [hg] at h0
  have h2 : IsPrimitiveRoot (g : (KS K S)ˣ) N := IsPrimitiveRoot.coe_submonoidClass_iff.mpr h1
  exact ⟨((g : (KS K S)ˣ) : KS K S), IsPrimitiveRoot.coe_units_iff.mpr h2⟩

omit [NumberField K] in
/-- **A primitive `N`-th root of unity of `K_{S₀}` is one of `K_S`** (`S₀ ⊆ S`). PROVED. -/
theorem cycloInfl_hasRootsOfUnity (hS : S₀ ⊆ S) {N : ℕ} (hμ₀ : HasRootsOfUnity K S₀ N) :
    HasRootsOfUnity K S N := by
  obtain ⟨ζ, hζ⟩ := hμ₀
  exact ⟨cycloInflIncl hS ζ, hζ.map_of_injective (cycloInflIncl_injective hS)⟩

/-- **`K_S` has exactly `N` `N`-th roots of unity** when it has a primitive one
(`card_rootsOfUnity_KS`). PROVED. -/
theorem cycloInfl_card_roots {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N) :
    Nat.card {ζ : unramifiedOutside K S // ζ ^ N = 1} = N := by
  rw [Nat.card_congr (cycloInflRootsEquiv S N)]
  exact card_rootsOfUnity_KS hμ

/-- **The action on the roots of unity of `K_S`**: if the restriction `inflMap g` raises every
`N`-th root of unity of `K_{S₀}` to the power `c`, then `g` raises every `N`-th root of unity of
`K_S` to the power `c` (each is a power of the image of a primitive root of `K_{S₀}`). PROVED. -/
theorem cycloInfl_galS_root (hS : S₀ ⊆ S) {N : ℕ} [NeZero N] (hμ₀ : HasRootsOfUnity K S₀ N)
    (g : GKS K S) (c : ℕ)
    (hc : ∀ ζ₀ : KS K S₀, ζ₀ ^ N = 1 → galS K S₀ (inflMap K hS g) ζ₀ = ζ₀ ^ c)
    {ζ : KS K S} (hζ : ζ ^ N = 1) : galS K S g ζ = ζ ^ c := by
  obtain ⟨ζ₀, hζ₀⟩ := hμ₀
  obtain ⟨k, -, rfl⟩ :=
    (hζ₀.map_of_injective (cycloInflIncl_injective hS)).eq_pow_of_pow_eq_one hζ
  rw [map_pow, cycloInfl_galS_incl, hc ζ₀ hζ₀.pow_eq_one, map_pow, ← pow_mul, ← pow_mul,
    mul_comm]

end Roots

/-! ### The inflation of a cyclotomic twist -/

/-- **The inflation of a cyclotomic twist is a cyclotomic twist**: for `S₀ ⊆ S` and
`T₀ ≅ R(1)` over `G_{K,S₀}` (lane RC26's `IsCyclotomicTwist`), the inflation `InflMod hS T₀` to
`G_{K,S}` is `R(1)` over `G_{K,S}`. Same `N` and same `e : T₀ ≃ R`; the exponent of `g ∈ G_{K,S}`
is that of `inflMap g`. `K_S` has exactly `N` `N`-th roots of unity, and `g` acts on them through
`inflMap g` (`cycloInfl_galS_root`). PROVED. -/
theorem cycloInfl_isCyclotomicTwist (hS : S₀ ⊆ S) {R T₀ : Type} [CommRing R] [AddCommGroup T₀]
    [Module R T₀] [DistribMulAction (GKS K S₀) T₀] (h : IsCyclotomicTwist K S₀ R T₀) :
    IsCyclotomicTwist K S R (InflMod hS T₀) := by
  obtain ⟨N, hN, e, c, hNR, hcard, hζ, he⟩ := h
  have : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
  have hμ₀ : HasRootsOfUnity K S₀ N := cycloInfl_hasRootsOfUnity_of_card hcard
  have hroot : ∀ (g : GKS K S) (ζ : unramifiedOutside K S), ζ ^ N = 1 →
      toGal K g ζ = ζ ^ c (inflMap K hS g) := fun g ζ hζN =>
    cycloInfl_galS_root hS hμ₀ g (c (inflMap K hS g))
      (fun ζ₀ h0 => hζ (inflMap K hS g) ζ₀ h0) hζN
  exact ⟨N, hN, e, fun g => c (inflMap K hS g), hNR,
    cycloInfl_card_roots (cycloInfl_hasRootsOfUnity hS hμ₀), hroot,
    fun g t => he (inflMap K hS g) t⟩

/-- **The target of the inflated Weil pairing is a cyclotomic twist over `S`**:
`IsCyclotomicTwist K S A (InflMod hS (Tate1 A hμ₀))` for a commutative `ℤ/N`-algebra `A` and
`hμ₀ : HasRootsOfUnity K S₀ N`, `S₀ ⊆ S` (lane RC28's `isCyclotomicTwist_tate1` over `S₀`, then
`cycloInfl_isCyclotomicTwist`). PROVED. -/
theorem cycloInfl_isCyclotomicTwist_tate1A (hS : S₀ ⊆ S) (A : Type) [CommRing A] {N : ℕ}
    [NeZero N] [Algebra (ZMod N) A] (hμ₀ : HasRootsOfUnity K S₀ N) :
    IsCyclotomicTwist K S A (InflMod hS (Tate1 A hμ₀)) :=
  cycloInfl_isCyclotomicTwist hS (isCyclotomicTwist_tate1 A hμ₀)

/-- **Round 1's hypothesis `hT`** (of `orthSelmerDuality_urOutside` and
`orthSelmerDuality_actualKummer`): the inflation of `A_i(1)` from `G_{K,S₀}` to `G_{K,S}` is a
cyclotomic twist over `S`, `IsCyclotomicTwist K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀))`.
PROVED. -/
theorem cycloInfl_isCyclotomicTwist_tate1 (hS : S₀ ⊆ S) (i : ℕ)
    (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i)) :
    IsCyclotomicTwist K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)) :=
  cycloInfl_isCyclotomicTwist_tate1A hS (Acoef i) hμ₀

/-! ### Non-vacuity at `i = 1` -/

variable (S) in
/-- **`-1` is a primitive square root of unity of `K_S`** (`K_S` has characteristic zero), so the
hypothesis `HasRootsOfUnity K S₀ (2 ^ 1)` holds for every `K` and `S₀`. PROVED. -/
theorem cycloInfl_hasRootsOfUnity_two : HasRootsOfUnity K S (2 ^ 1) := by
  refine ⟨-1, ?_⟩
  rw [pow_one]
  exact IsPrimitiveRoot.neg_one 0 (by norm_num)

/-- **Non-vacuity of `cycloInfl_isCyclotomicTwist_tate1` at `i = 1`**: for every number field
`K` and every `S₀ ⊆ S`, the inflation of `A_1(1)` (for the primitive square root `-1` of unity)
is a cyclotomic twist over `S`. PROVED. -/
theorem cycloInfl_isCyclotomicTwist_tate1_one (hS : S₀ ⊆ S) :
    IsCyclotomicTwist K S (Acoef 1) (InflMod hS (Tate1 (Acoef 1) (cycloInfl_hasRootsOfUnity_two S₀))) :=
  cycloInfl_isCyclotomicTwist_tate1 hS 1 (cycloInfl_hasRootsOfUnity_two S₀)

end ZInQ.Manuscript.RC.KummerMaps
