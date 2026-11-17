import Mathlib.RingTheory.Length
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Length and dimension calculus of the fixed-field budget (5.7) (Lane RC7, manuscript §9)

This file formalizes the module-theoretic content of the fixed-field budget (5.7) of Lemma
`ex:limits-fixed-field-budget` (`diophantine_zq.tex`, tex 5251–5392).  The arithmetic input — the
Selmer complexes `C_K`, `D_c = C_old ⊗^L_Λ ℤ₂`, the singular complexes `Q_r`, the triangle (5.7c),
Kummer self-duality — is *not* formalized here: it enters only through exact sequences of modules
and numerical identities taken as hypotheses, and each docstring says which hypothesis encodes
which manuscript display.  Everything deduced from these hypotheses is PROVED with the Mathlib
notions `Module.length` (over an arbitrary commutative ring `R`; in the manuscript `R = ℤ_[2]`,
tex 5254–5255), `Submodule.torsion` and `Module.finrank` over a field `k` (`k = 𝔽₂` in the text).

* Length calculus (tex 5359–5373): subadditivity of length along a sequence exact in the middle,
  restriction of exact sequences to torsion submodules, and the torsion budget
  `h₁ = Σᵢ length H^i(D_c)_tors ≤ h_K + 2 c_E + 2 t_K` (`fixed_field_torsion_budget`), from the
  integral long exact sequence (5.7d) of the triangle (5.7c).
* Dimension calculus (tex 5279–5283, 5318–5322, 5355–5359): `finrank_le_of_exact`, the count
  `dim ker + dim coker ≤ 4` of one reduced rank-two singular disk
  (`singular_disk_cohomology_le_four`), and the total `2 d_K + 12` (`total_rank_budget`).
* Smith count (tex 5375–5387) and the total torsion `h_K + 2 t_K` of `C_K` (tex 5312–5313);
  the combination of all three parts is `fixed_field_budget`, the display (5.7).
* Specializations to `R = ℤ_[2]` and to reductions modulo two of `2 × 2` matrices over `ℤ_[2]`.
-/

namespace ZInQ.Manuscript.RC.Determinant

open Submodule

/-! ## Length along sequences exact in the middle -/

section LengthCalculus

variable {R : Type*} [Ring R]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- **Tex 5359–5369 (PROVED).**  For `N →f M →g P` exact at `M`, the length of `M` is the length
of the image of `f` plus the length of the image of `g`: additivity of `Module.length` on the short
exact sequence `0 → range f → M → range g → 0` (equalities in `ℕ∞`). -/
theorem length_eq_add_of_exact_middle (f : N →ₗ[R] M) (g : M →ₗ[R] P) (H : Function.Exact f g) :
    Module.length R M =
      Module.length R (LinearMap.range f) + Module.length R (LinearMap.range g) := by
  refine Module.length_eq_add_of_exact (LinearMap.range f).subtype g.rangeRestrict
    (LinearMap.range f).subtype_injective g.surjective_rangeRestrict ?_
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  exact H.linearMap_ker_eq

/-- **Tex 5359–5369 (PROVED).**  Length is subadditive along a sequence exact in the middle: for
`N →f M →g P` exact at `M`, `length M ≤ length N + length P` in `ℕ∞` (the image of `f` is a
quotient of `N`, the image of `g` a submodule of `P`). -/
theorem length_le_add_of_exact (f : N →ₗ[R] M) (g : M →ₗ[R] P) (H : Function.Exact f g) :
    Module.length R M ≤ Module.length R N + Module.length R P := by
  rw [length_eq_add_of_exact_middle f g H]
  exact add_le_add (Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict)
    (Module.length_le_of_injective (LinearMap.range g).subtype
      (LinearMap.range g).subtype_injective)

end LengthCalculus

/-! ## Torsion submodules along linear maps -/

section Torsion

variable {R : Type*} [CommRing R]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- **Tex 5367–5369 (PROVED), auxiliary.**  A linear map sends torsion elements (elements killed by
a non-zero-divisor) to torsion elements. -/
theorem map_mem_torsion (f : M →ₗ[R] N) {x : M} (hx : x ∈ torsion R M) : f x ∈ torsion R N := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨a, ?_⟩
  rw [Submonoid.smul_def] at ha ⊢
  rw [← map_smul, ha, map_zero]

/-- **Tex 5367–5369 (PROVED), auxiliary.**  An injective linear map reflects torsion: if `f x` is
torsion, then so is `x`. -/
theorem mem_torsion_of_injective (f : M →ₗ[R] N) (hf : Function.Injective f) {x : M}
    (hx : f x ∈ torsion R N) : x ∈ torsion R M := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨a, hf ?_⟩
  rw [Submonoid.smul_def] at ha ⊢
  rw [map_smul, ha, map_zero]

/-- Tex 5367–5369 (definition): the restriction `torsion R M →ₗ[R] torsion R N` of a linear map
`f : M →ₗ[R] N` (well defined by `map_mem_torsion`). -/
def torsionRestrict (f : M →ₗ[R] N) : torsion R M →ₗ[R] torsion R N :=
  f.restrict fun _ hx => map_mem_torsion f hx

/-- **Tex 5367–5369 (PROVED), auxiliary.**  `torsionRestrict f` is `f` on underlying elements. -/
@[simp]
theorem coe_torsionRestrict_apply (f : M →ₗ[R] N) (x : torsion R M) :
    (torsionRestrict f x : N) = f x :=
  rfl

/-- **Tex 5367–5369 (PROVED), auxiliary.**  The restriction of an injective map to torsion is
injective. -/
theorem torsionRestrict_injective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (torsionRestrict f) := fun x y hxy =>
  Subtype.ext <| hf <| by simpa using congrArg Subtype.val hxy

/-- **Tex 5362 (PROVED), auxiliary.**  An injective linear map does not increase the length of the
torsion submodule. -/
theorem length_torsion_le_of_injective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Module.length R (torsion R M) ≤ Module.length R (torsion R N) :=
  Module.length_le_of_injective (torsionRestrict f) (torsionRestrict_injective f hf)

/-- **Tex 5362 (PROVED).**  Isomorphic modules have torsion submodules of the same length. -/
theorem length_torsion_eq_of_linearEquiv (e : M ≃ₗ[R] N) :
    Module.length R (torsion R M) = Module.length R (torsion R N) :=
  le_antisymm (length_torsion_le_of_injective e.toLinearMap e.injective)
    (length_torsion_le_of_injective e.symm.toLinearMap e.symm.injective)

/-- **Tex 5367–5369 (PROVED).**  Let `N →i M →j P` be exact at `M` with `i` injective.  Then the
restricted sequence `torsion N → torsion M → P` (the restriction of `i`, then `j` on `torsion M`)
is again exact at `torsion M`, and its first map is injective (`torsionRestrict_injective`): the
kernel of `torsion M → P` is exactly the image of `torsion N`, because the injective map `i`
reflects torsion (`mem_torsion_of_injective`).  For (5.7d), `torsion N = H²(C_K)_tors`,
`torsion M = H²(D_c)_tors` and `P = J_r`. -/
theorem exact_torsionRestrict (i : N →ₗ[R] M) (j : M →ₗ[R] P) (hi : Function.Injective i)
    (H : Function.Exact i j) :
    Function.Exact (torsionRestrict i) (j ∘ₗ (torsion R M).subtype) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (H (x : M)).mp hx
    have hyt : y ∈ torsion R N := mem_torsion_of_injective i hi (by rw [hy]; exact x.2)
    exact ⟨⟨y, hyt⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    exact H.apply_apply_eq_zero (y : N)

/-- **Tex 5367–5369 (PROVED).**  In the situation of `exact_torsionRestrict`, the kernel of
`torsion M → P` is the image of `torsion N` ("its kernel is `H²(C_K)_tors`"). -/
theorem ker_torsion_eq_range_torsionRestrict (i : N →ₗ[R] M) (j : M →ₗ[R] P)
    (hi : Function.Injective i) (H : Function.Exact i j) :
    LinearMap.ker (j ∘ₗ (torsion R M).subtype) = LinearMap.range (torsionRestrict i) :=
  (exact_torsionRestrict i j hi H).linearMap_ker_eq

/-- **Tex 5367–5369 (PROVED).**  In the situation of `exact_torsionRestrict`, the length of
`torsion M` is the length of `torsion N` (the kernel of `torsion M → P`) plus the length of the
image of `torsion M` in `P`. -/
theorem length_torsion_eq_add_length_image (i : N →ₗ[R] M) (j : M →ₗ[R] P)
    (hi : Function.Injective i) (H : Function.Exact i j) :
    Module.length R (torsion R M) =
      Module.length R (torsion R N) +
        Module.length R (LinearMap.range (j ∘ₗ (torsion R M).subtype)) := by
  rw [length_eq_add_of_exact_middle _ _ (exact_torsionRestrict i j hi H),
    ← (LinearEquiv.ofInjective (torsionRestrict i) (torsionRestrict_injective i hi)).length_eq]

/-- **Tex 5367–5369 (PROVED), torsion length budget.**  If `N →i M →j P` is exact at `M` and `i`
is injective, then `length (torsion M) ≤ length (torsion N) + length P`: the image of
`torsion M` in `P` has length at most `length P`, and its kernel is the image of `torsion N`. -/
theorem torsion_length_budget (i : N →ₗ[R] M) (j : M →ₗ[R] P) (hi : Function.Injective i)
    (H : Function.Exact i j) :
    Module.length R (torsion R M) ≤ Module.length R (torsion R N) + Module.length R P :=
  length_le_add_of_exact _ _ (exact_torsionRestrict i j hi H)

end Torsion

/-! ## The torsion budget `h₁ ≤ h_K + 2 c_E + 2 t_K` from (5.7d) -/

section FixedFieldTorsionBudget

variable {R : Type*} [CommRing R]
  {H0D H1C H1D H2C H2D J H3C H3D : Type*}
  [AddCommGroup H0D] [Module R H0D] [AddCommGroup H1C] [Module R H1C]
  [AddCommGroup H1D] [Module R H1D] [AddCommGroup H2C] [Module R H2C]
  [AddCommGroup H2D] [Module R H2D] [AddCommGroup J] [Module R J]
  [AddCommGroup H3C] [Module R H3C] [AddCommGroup H3D] [Module R H3D]

variable (R) in
/-- **Tex 5285, 5343–5351, 5370–5372 (PROVED), degree zero.**  `H⁰(D_c) = 0` (encoded by
`Subsingleton H0D`; it follows from `H⁰(C_K) = T^{G_K} = 0`, tex 5285, and the triangle (5.7c),
whose third term `Q_r` lives in degrees one and two), so its torsion has length zero. -/
theorem length_torsion_H0_eq_zero [Subsingleton H0D] : Module.length R (torsion R H0D) = 0 :=
  Module.length_eq_zero

/-- **Tex 5362 (PROVED), degree one.**  The first display of (5.7d), `H¹(D_c) ≃ H¹(C_K)`
(encoded by `e`), gives `length H¹(D_c)_tors = length H¹(C_K)_tors`. -/
theorem length_torsion_H1_eq (e : H1D ≃ₗ[R] H1C) :
    Module.length R (torsion R H1D) = Module.length R (torsion R H1C) :=
  length_torsion_eq_of_linearEquiv e

/-- **Tex 5363, 5367–5369 (PROVED), degree two.**  From the start
`0 → H²(C_K) →i H²(D_c) →j J_r` of the second display of (5.7d) (encoded by `hi`, `hij`):
`length H²(D_c)_tors ≤ length H²(C_K)_tors + length J_r`. -/
theorem length_torsion_H2_le (i : H2C →ₗ[R] H2D) (j : H2D →ₗ[R] J) (hi : Function.Injective i)
    (hij : Function.Exact i j) :
    Module.length R (torsion R H2D) ≤ Module.length R (torsion R H2C) + Module.length R J :=
  torsion_length_budget i j hi hij

/-- **Tex 5364–5366 (PROVED), degree three.**  From the end `H³(C_K) →l H³(D_c) → 0` of the
second display of (5.7d) (encoded by `hl`), `H³(D_c)` is a quotient of `H³(C_K)`, so
`length H³(D_c) ≤ length H³(C_K)`. -/
theorem length_H3_le (l : H3C →ₗ[R] H3D) (hl : Function.Surjective l) :
    Module.length R H3D ≤ Module.length R H3C :=
  Module.length_le_of_surjective l hl

/-- **Tex 5364–5366, 5370–5372 (PROVED), degree three.**
`length H³(D_c)_tors ≤ length H³(D_c) ≤ length H³(C_K)`. -/
theorem length_torsion_H3_le (l : H3C →ₗ[R] H3D) (hl : Function.Surjective l) :
    Module.length R (torsion R H3D) ≤ Module.length R H3C :=
  (Module.length_le_of_injective (torsion R H3D).subtype
    (torsion R H3D).subtype_injective).trans (length_H3_le l hl)

/-- **Tex 5363–5364 (PROVED), complement.**  For the exact sequence of the second display of
(5.7d), `0 → H²(C_K) →i H²(D_c) →j J_r →k H³(C_K) →l H³(D_c) → 0`, the lengths satisfy the Euler
identity `length H²(C_K) + length J_r + length H³(D_c) = length H²(D_c) + length H³(C_K)` in `ℕ∞`.
(Not needed for (5.7); it records the full length calculus of the sequence.) -/
theorem length_five_term_exact (i : H2C →ₗ[R] H2D) (j : H2D →ₗ[R] J) (k : J →ₗ[R] H3C)
    (l : H3C →ₗ[R] H3D) (hi : Function.Injective i) (hij : Function.Exact i j)
    (hjk : Function.Exact j k) (hkl : Function.Exact k l) (hl : Function.Surjective l) :
    Module.length R H2C + Module.length R J + Module.length R H3D =
      Module.length R H2D + Module.length R H3C := by
  have e₂ := length_eq_add_of_exact_middle i j hij
  have eJ := length_eq_add_of_exact_middle j k hjk
  have e₃ := length_eq_add_of_exact_middle k l hkl
  rw [← (LinearEquiv.ofInjective i hi).length_eq] at e₂
  rw [LinearMap.range_eq_top.mpr hl, Module.length_top] at e₃
  rw [e₂, eJ, e₃]
  ring

/-- **Tex 5359–5373 (PROVED), the torsion budget `h₁ ≤ h_K + 2 c_E + 2 t_K` of (5.7).**
Here `h₁ = Σᵢ length H^i(D_c)_tors` (tex 5370–5372) is the left-hand side, and lengths are in `ℕ∞`
over an arbitrary commutative ring `R` (`R = ℤ_[2]` in the text, see
`fixed_field_torsion_budget_padicInt`).  Hypotheses and the displays they encode:
* `[Subsingleton H0D]`: `H⁰(D_c) = 0`, from `H⁰(C_K) = 0` (tex 5285) and the triangle (5.7c);
* `e`: the first display of (5.7d), `H¹(D_c) ≃ H¹(C_K)` (tex 5362);
* `h57d`: the second display of (5.7d), exactness of
  `0 → H²(C_K) →i H²(D_c) →j J_r →k H³(C_K) →l H³(D_c) → 0` (tex 5363–5364), the integral long
  exact sequence of the triangle (5.7c);
* `ht₁`: `length H¹(C_K)_tors = t_K`, from `H¹(C_K)_tors = E(K)[2^∞]` (tex 5288–5292) and the
  definition of `t_K` (tex 5258);
* `ht₃`: `length H³(C_K) = t_K`, the second half of (5.7b) (tex 5300–5302);
* `hh`: `length H²(C_K)_tors = h_K`, the definition of `h_K` (tex 5259);
* `hJ`: `length J_r ≤ 2 c_E`, where `J_r = H²(Q_r)` for the third term `Q_r` of (5.7c)
  (tex 5331–5334, 5350–5351).
Of `h57d` only injectivity of `i`, exactness at `H²(D_c)` and surjectivity of `l` are used
(tex 5366–5369); exactness at `J_r` and at `H³(C_K)` is not needed. -/
theorem fixed_field_torsion_budget [Subsingleton H0D] (e : H1D ≃ₗ[R] H1C)
    (i : H2C →ₗ[R] H2D) (j : H2D →ₗ[R] J) (k : J →ₗ[R] H3C) (l : H3C →ₗ[R] H3D)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j k ∧
      Function.Exact k l ∧ Function.Surjective l)
    {t h c : ℕ∞} (ht₁ : Module.length R (torsion R H1C) = t) (ht₃ : Module.length R H3C = t)
    (hh : Module.length R (torsion R H2C) = h) (hJ : Module.length R J ≤ 2 * c) :
    Module.length R (torsion R H0D) + Module.length R (torsion R H1D) +
        Module.length R (torsion R H2D) + Module.length R (torsion R H3D) ≤
      h + 2 * c + 2 * t := by
  obtain ⟨hi, hij, -, -, hl⟩ := h57d
  have h₂ := length_torsion_H2_le i j hi hij
  have h₃ := length_torsion_H3_le l hl
  rw [hh] at h₂
  rw [ht₃] at h₃
  rw [length_torsion_H0_eq_zero R, length_torsion_H1_eq e, ht₁, zero_add]
  calc t + Module.length R (torsion R H2D) + Module.length R (torsion R H3D)
      ≤ t + (h + 2 * c) + t := add_le_add (add_le_add le_rfl (h₂.trans (add_le_add le_rfl hJ))) h₃
    _ = h + 2 * c + 2 * t := by ring

/-- **Tex 5359–5373 (PROVED), the torsion budget in natural numbers.**  The form of
`fixed_field_torsion_budget` with `t_K, h_K, c_E : ℕ` and with `h₁ : ℕ` the (finite) value of
`Σᵢ length H^i(D_c)_tors` (`hh₁`, tex 5370–5372); the hypotheses encode the same displays as in
`fixed_field_torsion_budget`.  Conclusion: `h₁ ≤ h_K + 2 c_E + 2 t_K` in `ℕ`. -/
theorem fixed_field_torsion_budget_nat [Subsingleton H0D] (e : H1D ≃ₗ[R] H1C)
    (i : H2C →ₗ[R] H2D) (j : H2D →ₗ[R] J) (k : J →ₗ[R] H3C) (l : H3C →ₗ[R] H3D)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j k ∧
      Function.Exact k l ∧ Function.Surjective l)
    {t h c h₁ : ℕ} (ht₁ : Module.length R (torsion R H1C) = t) (ht₃ : Module.length R H3C = t)
    (hh : Module.length R (torsion R H2C) = h) (hJ : Module.length R J ≤ 2 * c)
    (hh₁ : Module.length R (torsion R H0D) + Module.length R (torsion R H1D) +
        Module.length R (torsion R H2D) + Module.length R (torsion R H3D) = h₁) :
    h₁ ≤ h + 2 * c + 2 * t := by
  have hb := fixed_field_torsion_budget (H0D := H0D) e i j k l h57d ht₁ ht₃ hh hJ
  rw [hh₁] at hb
  exact_mod_cast hb

end FixedFieldTorsionBudget

/-! ## The dimension budget over a field -/

section DimensionBudget

variable {k : Type*} [Field k]

/-- **Tex 5355–5359 (PROVED).**  Dimension is subadditive along a sequence exact in the middle:
for `V₁ →f V₂ →g V₃` exact at `V₂` with `V₁`, `V₃` finite-dimensional,
`finrank V₂ ≤ finrank V₁ + finrank V₃`.  This is the step from the long exact sequence of the
reduction modulo two of (5.7c), `H^i(C_K ⊗ 𝔽₂) → H^i(D_c ⊗ 𝔽₂) → H^i(Q_r ⊗ 𝔽₂)`, to the
dimension budget. -/
theorem finrank_le_of_exact {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    [FiniteDimensional k V₁] [FiniteDimensional k V₃]
    (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃) (H : Function.Exact f g) :
    Module.finrank k V₂ ≤ Module.finrank k V₁ + Module.finrank k V₃ := by
  by_cases h₂ : FiniteDimensional k V₂
  · have h := length_le_add_of_exact f g H
    rw [Module.length_eq_finrank k V₁, Module.length_eq_finrank k V₂,
      Module.length_eq_finrank k V₃] at h
    exact_mod_cast h
  · rw [Module.finrank_of_not_finite h₂]
    exact Nat.zero_le _

variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **Tex 5318–5322, 5355–5356 (PROVED).**  Euler identity of a two-term complex `[V →φ W]`
(in degrees one and two) over a field: its cohomology `H¹ = ker φ`, `H² = W ⧸ range φ` satisfies
`dim H¹ + dim H² + 2 · rank φ = dim V + dim W`. -/
theorem finrank_ker_add_finrank_coker [FiniteDimensional k V] [FiniteDimensional k W]
    (φ : V →ₗ[k] W) :
    Module.finrank k (LinearMap.ker φ) + Module.finrank k (W ⧸ LinearMap.range φ) +
        2 * Module.finrank k (LinearMap.range φ) =
      Module.finrank k V + Module.finrank k W := by
  have h₁ := LinearMap.finrank_range_add_finrank_ker φ
  have h₂ := Submodule.finrank_quotient_add_finrank (LinearMap.range φ)
  omega

/-- **Tex 5318–5322, 5355–5356 (PROVED), one singular disk.**  The reduction modulo two of a
rank-two singular disk `Q_{r_i,w} = [ℤ₂² → ℤ₂²]` is a map `φ : V → V` with `dim V = 2` (in
degrees one and two); by rank–nullity its total cohomology dimension is
`dim ker φ + dim coker φ = 2 · (2 - rank φ)`. -/
theorem singular_disk_cohomology_eq (φ : V →ₗ[k] V) (hV : Module.finrank k V = 2) :
    Module.finrank k (LinearMap.ker φ) + Module.finrank k (V ⧸ LinearMap.range φ) =
      2 * (2 - Module.finrank k (LinearMap.range φ)) := by
  have : FiniteDimensional k V := Module.finite_of_finrank_pos (by omega)
  have h := finrank_ker_add_finrank_coker φ
  have hr := LinearMap.finrank_range_le φ
  omega

/-- **Tex 5318–5322, 5355–5356 (PROVED), one singular disk.**  A reduced rank-two singular disk
`[V →φ V]`, `dim V = 2`, contributes at most four to total cohomology dimension:
`dim ker φ + dim coker φ ≤ 4`. -/
theorem singular_disk_cohomology_le_four (φ : V →ₗ[k] V) (hV : Module.finrank k V = 2) :
    Module.finrank k (LinearMap.ker φ) + Module.finrank k (V ⧸ LinearMap.range φ) ≤ 4 := by
  rw [singular_disk_cohomology_eq φ hV]
  omega

/-- **Tex 5318–5322, 5355–5356 (PROVED), one singular disk, matrix form.**  For a `2 × 2` matrix
`A` over `k`, the map `A : k² → k²` satisfies `dim ker A + dim coker A ≤ 4`. -/
theorem singular_disk_matrix_cohomology_le_four (A : Matrix (Fin 2) (Fin 2) k) :
    Module.finrank k (LinearMap.ker A.mulVecLin) +
        Module.finrank k ((Fin 2 → k) ⧸ LinearMap.range A.mulVecLin) ≤ 4 :=
  singular_disk_cohomology_le_four A.mulVecLin (Module.finrank_fin_fun k)

/-- **Tex 5350, 5355–5356 (PROVED), two singular disks.**  `Q_r` is the sum of two rank-two
singular disks `[V₁ →φ₁ V₁] ⊕ [V₂ →φ₂ V₂]` in degrees one and two; modulo two its cohomology is
`ker φ₁ × ker φ₂` in degree one and `coker φ₁ × coker φ₂` in degree two, of total dimension at
most eight. -/
theorem two_singular_disks_le_eight {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] (φ₁ : V₁ →ₗ[k] V₁) (φ₂ : V₂ →ₗ[k] V₂)
    (h₁ : Module.finrank k V₁ = 2) (h₂ : Module.finrank k V₂ = 2) :
    Module.finrank k (LinearMap.ker φ₁ × LinearMap.ker φ₂) +
        Module.finrank k ((V₁ ⧸ LinearMap.range φ₁) × (V₂ ⧸ LinearMap.range φ₂)) ≤ 8 := by
  have : FiniteDimensional k V₁ := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional k V₂ := Module.finite_of_finrank_pos (by omega)
  rw [Module.finrank_prod, Module.finrank_prod]
  have d₁ := singular_disk_cohomology_le_four φ₁ h₁
  have d₂ := singular_disk_cohomology_le_four φ₂ h₂
  omega

end DimensionBudget

/-- **Tex 5278–5283 (PROVED).**  The dimensions `(2, d_K, d_K, 2)` of (5.7a) add up to
`2 d_K + 4`, the total rank of a minimal finite free `ℤ₂`-model of `C_K`. -/
theorem sum_dims_57a (d : ℕ) : ∑ i, (![2, d, d, 2] : Fin 4 → ℕ) i = 2 * d + 4 := by
  rw [Fin.sum_univ_four]
  simp
  omega

/-- **Tex 5355–5359 (PROVED), dimension budget, numerical form.**  Let `a i`, `b i`, `c i`
(`i = 0, …, 3`) be the dimensions of `H^i(C_K ⊗ 𝔽₂)`, `H^i(D_c ⊗ 𝔽₂)`, `H^i(Q_r ⊗ 𝔽₂)`.  If
`b i ≤ a i + c i` (exactness of the reduced long exact sequence of (5.7c) in the middle,
`finrank_le_of_exact`), `Σ a = 2 d + 4` ((5.7a), `sum_dims_57a`) and `Σ c ≤ 8` (the two
singular disks, `two_singular_disks_le_eight`), then `Σ b ≤ 2 d + 12`. -/
theorem total_rank_budget_nat (a b c : Fin 4 → ℕ) (d : ℕ) (hb : ∀ i, b i ≤ a i + c i)
    (ha : ∑ i, a i = 2 * d + 4) (hc : ∑ i, c i ≤ 8) : ∑ i, b i ≤ 2 * d + 12 := by
  have hsum : ∑ i, b i ≤ ∑ i, (a i + c i) := Finset.sum_le_sum fun i _ => hb i
  rw [Finset.sum_add_distrib] at hsum
  omega

section DimensionBudgetSpaces

variable {k : Type*} [Field k] {HC HD HQ : Fin 4 → Type*}
  [∀ i, AddCommGroup (HC i)] [∀ i, Module k (HC i)]
  [∀ i, AddCommGroup (HD i)] [∀ i, Module k (HD i)]
  [∀ i, AddCommGroup (HQ i)] [∀ i, Module k (HQ i)]

/-- **Tex 5278–5283, 5355–5359 (PROVED), dimension budget for vector spaces indexed by degree.**
`HC i`, `HD i`, `HQ i` (`i = 0, …, 3`) stand for `H^i(C_K ⊗ 𝔽₂)`, `H^i(D_c ⊗ 𝔽₂)`,
`H^i(Q_r ⊗ 𝔽₂)` over the field `k`.  Hypotheses and the displays they encode:
* `hfg`: exactness at `HD i` of `HC i →f HD i →g HQ i`, a piece of the long exact sequence of the
  reduction modulo two of the triangle (5.7c);
* `h57a`: the dimensions `(2, d_K, d_K, 2)` of (5.7a);
* `hQ`: the two singular disks of (5.7c) contribute at most eight (tex 5355–5356; see
  `two_singular_disks_le_eight`).
Conclusion: the total dimension of the cohomology of `D_c ⊗ 𝔽₂`, which is the total rank of a
minimal finite free model obtained by cancelling unit entries, is at most `2 d_K + 12`. -/
theorem total_rank_budget [∀ i, FiniteDimensional k (HC i)] [∀ i, FiniteDimensional k (HQ i)]
    (f : ∀ i, HC i →ₗ[k] HD i) (g : ∀ i, HD i →ₗ[k] HQ i) (hfg : ∀ i, Function.Exact (f i) (g i))
    {d : ℕ} (h57a : ∀ i, Module.finrank k (HC i) = (![2, d, d, 2] : Fin 4 → ℕ) i)
    (hQ : ∑ i, Module.finrank k (HQ i) ≤ 8) :
    ∑ i, Module.finrank k (HD i) ≤ 2 * d + 12 :=
  total_rank_budget_nat (fun i => Module.finrank k (HC i)) (fun i => Module.finrank k (HD i))
    (fun i => Module.finrank k (HQ i)) d (fun i => finrank_le_of_exact (f i) (g i) (hfg i))
    ((Finset.sum_congr rfl fun i _ => h57a i).trans (sum_dims_57a d)) hQ

/-- **Tex 5278–5283, 5318–5322, 5350–5359 (PROVED), dimension budget with the two singular
disks made explicit.**  As `total_rank_budget`, with the cohomology of `Q_r ⊗ 𝔽₂` given by the
two reduced rank-two singular disks `φ₁ : V₁ → V₁`, `φ₂ : V₂ → V₂` (`dim V₁ = dim V₂ = 2`):
`hQ₀`, `hQ₃` say that `Q_r` has no cohomology in degrees zero and three (it lives in degrees one
and two, tex 5320–5322), and `eQ₁`, `eQ₂` identify its degree-one and degree-two cohomology with
`ker φ₁ × ker φ₂` and `coker φ₁ × coker φ₂`. -/
theorem total_rank_budget_of_singular_disks [∀ i, FiniteDimensional k (HC i)]
    [∀ i, FiniteDimensional k (HQ i)]
    (f : ∀ i, HC i →ₗ[k] HD i) (g : ∀ i, HD i →ₗ[k] HQ i) (hfg : ∀ i, Function.Exact (f i) (g i))
    {d : ℕ} (h57a : ∀ i, Module.finrank k (HC i) = (![2, d, d, 2] : Fin 4 → ℕ) i)
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    (φ₁ : V₁ →ₗ[k] V₁) (φ₂ : V₂ →ₗ[k] V₂)
    (h₁ : Module.finrank k V₁ = 2) (h₂ : Module.finrank k V₂ = 2)
    (hQ₀ : Module.finrank k (HQ 0) = 0) (hQ₃ : Module.finrank k (HQ 3) = 0)
    (eQ₁ : HQ 1 ≃ₗ[k] LinearMap.ker φ₁ × LinearMap.ker φ₂)
    (eQ₂ : HQ 2 ≃ₗ[k] (V₁ ⧸ LinearMap.range φ₁) × (V₂ ⧸ LinearMap.range φ₂)) :
    ∑ i, Module.finrank k (HD i) ≤ 2 * d + 12 := by
  refine total_rank_budget f g hfg h57a ?_
  rw [Fin.sum_univ_four, hQ₀, hQ₃, eQ₁.finrank_eq, eQ₂.finrank_eq]
  have := two_singular_disks_le_eight φ₁ φ₂ h₁ h₂
  omega

end DimensionBudgetSpaces

/-! ## The Smith count and the total torsion of `C_K` -/

/-- **Tex 5375–5387 (PROVED), Smith count.**  If a finite free model has total rank
`rank_total = 2 + 2 m` (one free cohomology generator in each of degrees one and two, and `m` Smith
disks `[ℤ₂ → ℤ₂]` of rank two each, tex 5379–5381) and `rank_total ≤ 2 d_K + 12`, then
`m ≤ d_K + 5`. -/
theorem smith_disk_count {rankTotal m d : ℕ} (hm : rankTotal = 2 + 2 * m)
    (hrank : rankTotal ≤ 2 * d + 12) : m ≤ d + 5 := by
  omega

/-- **Tex 5285, 5291, 5302, 5312–5313 (PROVED), arithmetic form.**  The torsion lengths
`(0, t_K, h_K, t_K)` of `C_K` in degrees `0, …, 3` add up to `h_K + 2 t_K` (in `ℕ∞`). -/
theorem total_torsion_arith (t h : ℕ∞) : 0 + t + h + t = h + 2 * t := by
  ring

section TotalTorsion

variable {R : Type*} [CommRing R] {H0C H1C H2C H3C : Type*}
  [AddCommGroup H0C] [Module R H0C] [AddCommGroup H1C] [Module R H1C]
  [AddCommGroup H2C] [Module R H2C] [AddCommGroup H3C] [Module R H3C]

/-- **Tex 5285–5313 (PROVED), total torsion of `C_K`.**  The total integral torsion length of
`C_K` is `h_K + 2 t_K`.  Hypotheses and the displays they encode:
* `[Subsingleton H0C]`: `H⁰(C_K) = T^{G_K} = 0` (tex 5285–5287);
* `ht₁`: `length H¹(C_K)_tors = t_K`, from `H¹(C_K)_tors = E(K)[2^∞]` (tex 5288–5292, 5258);
* `hh`: `length H²(C_K)_tors = h_K`, the definition of `h_K` (tex 5259);
* `hT₃`, `ht₃`: `H³(C_K) ≃ Ext¹(H¹(C_K), ℤ₂)` is torsion, of length `t_K` (5.7b)
  (tex 5300–5302). -/
theorem total_torsion_length [Subsingleton H0C] {t h : ℕ∞}
    (ht₁ : Module.length R (torsion R H1C) = t) (hh : Module.length R (torsion R H2C) = h)
    (hT₃ : Module.IsTorsion R H3C) (ht₃ : Module.length R H3C = t) :
    Module.length R (torsion R H0C) + Module.length R (torsion R H1C) +
        Module.length R (torsion R H2C) + Module.length R (torsion R H3C) = h + 2 * t := by
  have htop : torsion R H3C = ⊤ := (Submodule.isTorsion'_iff_torsion'_eq_top _).mp hT₃
  rw [htop, Module.length_top, Module.length_eq_zero (M := torsion R H0C), ht₁, hh, ht₃]
  exact total_torsion_arith t h

end TotalTorsion

/-! ## The fixed-field budget (5.7) -/

/-- **Tex 5355–5387 (PROVED), the fixed-field budget (5.7).**  The three bounds
`rank_total C_old ≤ 2 d_K + 12`, `m ≤ d_K + 5`, `h₁ ≤ h_K + 2 c_E + 2 t_K`, from the dimension
budget (`total_rank_budget`), the Smith count (`smith_disk_count`) and the torsion budget
(`fixed_field_torsion_budget`).  Hypotheses and the displays they encode:
* `hfg` (reduced long exact sequence of (5.7c)), `h57a` ((5.7a)) and `hQ` (the two singular disks
  of (5.7c) contribute at most eight), as in `total_rank_budget`;
* `hmodel`: the total rank of the chosen finite free model is at most the total dimension of the
  cohomology of its reduction (equality for the minimal model obtained by cancelling unit
  entries, tex 5357–5359);
* `hsmith`: its Smith decomposition has one free generator in each of degrees one and two and
  `m` Smith disks, so `rank_total = 2 + 2 m` (tex 5375–5381);
* `[Subsingleton H0D]` (from (5.7c)), `e` and `h57d` ((5.7d)), `ht₁` (tex 5288–5292), `ht₃`
  ((5.7b)), `hh` (tex 5259) and `hJ` (`J_r = H²(Q_r)` of (5.7c)), as in
  `fixed_field_torsion_budget`; the connecting map `J_r → H³(C_K)` of (5.7d) is called `δ`. -/
theorem fixed_field_budget
    {k : Type*} [Field k] {HC HD HQ : Fin 4 → Type*}
    [∀ n, AddCommGroup (HC n)] [∀ n, Module k (HC n)]
    [∀ n, AddCommGroup (HD n)] [∀ n, Module k (HD n)]
    [∀ n, AddCommGroup (HQ n)] [∀ n, Module k (HQ n)]
    [∀ n, FiniteDimensional k (HC n)] [∀ n, FiniteDimensional k (HQ n)]
    (f : ∀ n, HC n →ₗ[k] HD n) (g : ∀ n, HD n →ₗ[k] HQ n) (hfg : ∀ n, Function.Exact (f n) (g n))
    {d : ℕ} (h57a : ∀ n, Module.finrank k (HC n) = (![2, d, d, 2] : Fin 4 → ℕ) n)
    (hQ : ∑ n, Module.finrank k (HQ n) ≤ 8)
    {rankTotal m : ℕ} (hmodel : rankTotal ≤ ∑ n, Module.finrank k (HD n))
    (hsmith : rankTotal = 2 + 2 * m)
    {R : Type*} [CommRing R] {H0D H1C H1D H2C H2D J H3C H3D : Type*}
    [AddCommGroup H0D] [Module R H0D] [AddCommGroup H1C] [Module R H1C]
    [AddCommGroup H1D] [Module R H1D] [AddCommGroup H2C] [Module R H2C]
    [AddCommGroup H2D] [Module R H2D] [AddCommGroup J] [Module R J]
    [AddCommGroup H3C] [Module R H3C] [AddCommGroup H3D] [Module R H3D]
    [Subsingleton H0D] (e : H1D ≃ₗ[R] H1C)
    (i : H2C →ₗ[R] H2D) (j : H2D →ₗ[R] J) (δ : J →ₗ[R] H3C) (l : H3C →ₗ[R] H3D)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    {t h c : ℕ∞} (ht₁ : Module.length R (torsion R H1C) = t) (ht₃ : Module.length R H3C = t)
    (hh : Module.length R (torsion R H2C) = h) (hJ : Module.length R J ≤ 2 * c) :
    rankTotal ≤ 2 * d + 12 ∧ m ≤ d + 5 ∧
      Module.length R (torsion R H0D) + Module.length R (torsion R H1D) +
          Module.length R (torsion R H2D) + Module.length R (torsion R H3D) ≤
        h + 2 * c + 2 * t := by
  have hrank : rankTotal ≤ 2 * d + 12 := hmodel.trans (total_rank_budget f g hfg h57a hQ)
  exact ⟨hrank, smith_disk_count hsmith hrank,
    fixed_field_torsion_budget e i j δ l h57d ht₁ ht₃ hh hJ⟩

/-! ## Specializations: lengths over `ℤ_[2]`, reductions modulo two -/

/-- **Tex 5254–5255, 5359–5373 (PROVED).**  The torsion budget `fixed_field_torsion_budget` with
lengths over `ℤ_[2]`, as in the manuscript ("Lengths in this paragraph are lengths over `ℤ₂`");
the hypotheses encode the same displays as there. -/
theorem fixed_field_torsion_budget_padicInt {H0D H1C H1D H2C H2D J H3C H3D : Type*}
    [AddCommGroup H0D] [Module ℤ_[2] H0D] [AddCommGroup H1C] [Module ℤ_[2] H1C]
    [AddCommGroup H1D] [Module ℤ_[2] H1D] [AddCommGroup H2C] [Module ℤ_[2] H2C]
    [AddCommGroup H2D] [Module ℤ_[2] H2D] [AddCommGroup J] [Module ℤ_[2] J]
    [AddCommGroup H3C] [Module ℤ_[2] H3C] [AddCommGroup H3D] [Module ℤ_[2] H3D]
    [Subsingleton H0D] (e : H1D ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] H2D) (j : H2D →ₗ[ℤ_[2]] J) (k : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] H3D)
    (h57d : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j k ∧
      Function.Exact k l ∧ Function.Surjective l)
    {t h c : ℕ∞} (ht₁ : Module.length ℤ_[2] (torsion ℤ_[2] H1C) = t)
    (ht₃ : Module.length ℤ_[2] H3C = t) (hh : Module.length ℤ_[2] (torsion ℤ_[2] H2C) = h)
    (hJ : Module.length ℤ_[2] J ≤ 2 * c) :
    Module.length ℤ_[2] (torsion ℤ_[2] H0D) + Module.length ℤ_[2] (torsion ℤ_[2] H1D) +
        Module.length ℤ_[2] (torsion ℤ_[2] H2D) + Module.length ℤ_[2] (torsion ℤ_[2] H3D) ≤
      h + 2 * c + 2 * t :=
  fixed_field_torsion_budget e i j k l h57d ht₁ ht₃ hh hJ

/-- **Tex 5320–5322, 5355–5356 (PROVED), one singular disk reduced modulo two.**  For the matrix
`X` of a singular disk `Q_{r_i,w} = [ℤ₂² →X ℤ₂²]` (`X = Φ_{r_i} - r_i`), the reduction
`X̄ = X mod 2 : 𝔽₂² → 𝔽₂²` satisfies `dim ker X̄ + dim coker X̄ ≤ 4`; these are the dimensions of
the cohomology of `Q_{r_i,w} ⊗ 𝔽₂` in degrees one and two. -/
theorem singular_disk_mod_two_le_four (X : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    Module.finrank (ZMod 2) (LinearMap.ker (X.map PadicInt.toZMod).mulVecLin) +
        Module.finrank (ZMod 2)
          ((Fin 2 → ZMod 2) ⧸ LinearMap.range (X.map PadicInt.toZMod).mulVecLin) ≤ 4 :=
  singular_disk_matrix_cohomology_le_four _

/-- **Tex 5350, 5355–5356 (PROVED), two singular disks reduced modulo two.**  For the matrices
`X`, `Y` of the two singular disks of `Q_r` (at the two places over the moving prime), the
cohomology of `Q_r ⊗ 𝔽₂`, namely `ker X̄ × ker Ȳ` in degree one and `coker X̄ × coker Ȳ` in
degree two, has total dimension at most eight. -/
theorem two_singular_disks_mod_two_le_eight (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    Module.finrank (ZMod 2) (LinearMap.ker (X.map PadicInt.toZMod).mulVecLin ×
        LinearMap.ker (Y.map PadicInt.toZMod).mulVecLin) +
      Module.finrank (ZMod 2)
        (((Fin 2 → ZMod 2) ⧸ LinearMap.range (X.map PadicInt.toZMod).mulVecLin) ×
          ((Fin 2 → ZMod 2) ⧸ LinearMap.range (Y.map PadicInt.toZMod).mulVecLin)) ≤ 8 :=
  two_singular_disks_le_eight _ _ (Module.finrank_fin_fun _) (Module.finrank_fin_fun _)

end ZInQ.Manuscript.RC.Determinant
