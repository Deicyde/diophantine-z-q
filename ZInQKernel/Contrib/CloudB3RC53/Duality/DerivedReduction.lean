import Mathlib

/-!
# Duality area: derived reduction of the Kummer condition (tex L3416–3418, L3429–3431)

Lemma `ex:arith-local-kummer`, tex L3416–3418: "the condition `U_F = B(F)^∧_2[−1] → RΓ(F, T₂B)`
includes the finite two-primary torsion. Its reduction modulo `2^a` has `B(F)[2^a]` in degree zero
and `B(F)/2^a B(F)` in degree one" (again at L3429–3431, "derived reduction modulo `2^a`").

This is Elliot's own step. It is algebraic: if `M = B(F)^∧_2` is presented by an injective map
`f : P₁ → P₀` (a two-term model `[P₁ → P₀]` of `M[−1]` in degrees zero and one, e.g. a free
resolution), its reduction modulo `n = 2^a` is the two-term complex
`f̄ : P₁/nP₁ → P₀/nP₀`, and

* `ker f̄ ≅ M[n]` (`kerReduction_equiv`): degree zero is the `n`-torsion of `M`, so the finite
  torsion of `M` appears in degree zero;
* `coker f̄ ≅ M/nM` (`cokerReduction_equiv`): degree one is `M/nM`.

Hypotheses: `f` injective, `g : P₀ → M` surjective with `ker g = im f`, and `n` regular on `P₀`
(true for free `ℤ₂`-modules and `n = 2^a`). The coefficient ring is any commutative ring.

* Non-vacuity: `reduction_example` — over `ℤ`, `M = ℤ/2` presented by `2 : ℤ → ℤ` and `n = 2`:
  the hypotheses hold and `M[2] = ℤ/2` is nonzero, so `ker f̄` is nonzero
  (`reduction_example_nontrivial`). Degree zero really carries the torsion.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Duality

open Submodule

variable {R : Type*} [CommRing R] {P₁ P₀ M : Type*} [AddCommGroup P₁] [Module R P₁]
  [AddCommGroup P₀] [Module R P₀] [AddCommGroup M] [Module R M]

/-- Multiplication by `n` on a module. -/
abbrev mulBy (n : R) (N : Type*) [AddCommGroup N] [Module R N] : N →ₗ[R] N :=
  n • LinearMap.id

/-- `nN`, the image of multiplication by `n`. -/
abbrev nSub (n : R) (N : Type*) [AddCommGroup N] [Module R N] : Submodule R N :=
  LinearMap.range (mulBy n N)

/-- `N[n]`, the kernel of multiplication by `n`. -/
abbrev torsionN (n : R) (N : Type*) [AddCommGroup N] [Module R N] : Submodule R N :=
  LinearMap.ker (mulBy n N)

/-- **The reduction modulo `n`** of `f : P₁ → P₀`, `f̄ : P₁/nP₁ → P₀/nP₀`. -/
def reduction (n : R) (f : P₁ →ₗ[R] P₀) : (P₁ ⧸ nSub n P₁) →ₗ[R] (P₀ ⧸ nSub n P₀) :=
  (nSub n P₁).mapQ (nSub n P₀) f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simp⟩)

theorem reduction_mk (n : R) (f : P₁ →ₗ[R] P₀) (x : P₁) :
    reduction n f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  rfl

theorem mem_nSub {n : R} {N : Type*} [AddCommGroup N] [Module R N] {y : N} :
    y ∈ nSub n N ↔ ∃ z, n • z = y := by
  simp [nSub, mulBy]

variable (n : R) (f : P₁ →ₗ[R] P₀) (g : P₀ →ₗ[R] M)

/-- The pairs `(x, y)` with `f x = n y`. -/
def pairSub : Submodule R (P₁ × P₀) :=
  LinearMap.ker (f.comp (LinearMap.fst R P₁ P₀) - n • LinearMap.snd R P₁ P₀)

theorem mem_pairSub {x : P₁} {y : P₀} : (x, y) ∈ pairSub n f ↔ f x = n • y := by
  simp [pairSub, sub_eq_zero]

variable {n f g}

/-- `(x, y) ↦ x̄ ∈ ker f̄`. -/
def pairToKer : pairSub n f →ₗ[R] LinearMap.ker (reduction n f) :=
  LinearMap.codRestrict _
    ((nSub n P₁).mkQ.comp ((LinearMap.fst R P₁ P₀).comp (pairSub n f).subtype)) (by
      rintro ⟨⟨x, y⟩, hxy⟩
      rw [mem_pairSub] at hxy
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk (f x) = (0 : P₀ ⧸ nSub n P₀)
      rw [Submodule.Quotient.mk_eq_zero, hxy]
      exact ⟨y, rfl⟩)

/-- `(x, y) ↦ g y ∈ M[n]`. -/
def pairToTors (hfg : g.comp f = 0) : pairSub n f →ₗ[R] torsionN n M :=
  LinearMap.codRestrict _ (g.comp ((LinearMap.snd R P₁ P₀).comp (pairSub n f).subtype)) (by
    rintro ⟨⟨x, y⟩, hxy⟩
    rw [mem_pairSub] at hxy
    rw [LinearMap.mem_ker]
    change n • g y = 0
    rw [← map_smul, ← hxy]
    exact LinearMap.congr_fun hfg x)

theorem pairToKer_surjective : Function.Surjective (pairToKer (n := n) (f := f)) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := (nSub n P₁).mkQ_surjective q
  rw [LinearMap.mem_ker] at hq
  change Submodule.Quotient.mk (f x) = (0 : P₀ ⧸ nSub n P₀) at hq
  rw [Submodule.Quotient.mk_eq_zero, mem_nSub] at hq
  obtain ⟨y, hy⟩ := hq
  exact ⟨⟨(x, y), (mem_pairSub n f).2 hy.symm⟩, rfl⟩

theorem pairToTors_surjective (hfg : g.comp f = 0) (hg : Function.Surjective g)
    (hex : ∀ y, g y = 0 → ∃ x, f x = y) : Function.Surjective (pairToTors (n := n) hfg) := by
  rintro ⟨m, hm⟩
  rw [LinearMap.mem_ker] at hm
  obtain ⟨y, rfl⟩ := hg m
  obtain ⟨x, hx⟩ := hex (n • y) (by rw [map_smul]; exact hm)
  exact ⟨⟨(x, y), (mem_pairSub n f).2 hx⟩, rfl⟩

theorem ker_pairToKer_le (hfg : g.comp f = 0) (hreg : IsSMulRegular P₀ n) :
    LinearMap.ker (pairToKer (n := n) (f := f)) ≤ LinearMap.ker (pairToTors (n := n) hfg) := by
  rintro ⟨⟨x, y⟩, hxy⟩ h
  rw [mem_pairSub] at hxy
  rw [LinearMap.mem_ker] at h ⊢
  have h' : Submodule.Quotient.mk x = (0 : P₁ ⧸ nSub n P₁) := congrArg Subtype.val h
  rw [Submodule.Quotient.mk_eq_zero, mem_nSub] at h'
  obtain ⟨x', rfl⟩ := h'
  have hy : y = f x' := hreg (by change n • y = n • f x'; rw [← hxy, map_smul])
  apply Subtype.ext
  change g y = 0
  rw [hy]
  exact LinearMap.congr_fun hfg x'

theorem ker_pairToTors_le (hfg : g.comp f = 0) (hf : Function.Injective f)
    (hex : ∀ y, g y = 0 → ∃ x, f x = y) :
    LinearMap.ker (pairToTors (n := n) hfg) ≤ LinearMap.ker (pairToKer (n := n) (f := f)) := by
  rintro ⟨⟨x, y⟩, hxy⟩ h
  rw [mem_pairSub] at hxy
  rw [LinearMap.mem_ker] at h ⊢
  have h' : g y = 0 := congrArg Subtype.val h
  obtain ⟨z, rfl⟩ := hex y h'
  have hx : x = n • z := hf (by rw [hxy, map_smul])
  apply Subtype.ext
  change Submodule.Quotient.mk x = (0 : P₁ ⧸ nSub n P₁)
  rw [Submodule.Quotient.mk_eq_zero, hx]
  exact ⟨z, rfl⟩

/-- **Degree zero of the derived reduction is the `n`-torsion** (tex L3417–3418): for a
presentation `0 → P₁ --f--> P₀ --g--> M → 0` with `n` regular on `P₀`,
`ker (f mod n) ≅ M[n]`. PROVED. -/
noncomputable def kerReduction_equiv (hfg : g.comp f = 0) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : ∀ y, g y = 0 → ∃ x, f x = y)
    (hreg : IsSMulRegular P₀ n) : LinearMap.ker (reduction n f) ≃ₗ[R] torsionN n M :=
  (LinearMap.quotKerEquivOfSurjective _ pairToKer_surjective).symm.trans
    (((LinearMap.ker (pairToKer (n := n) (f := f))).quotEquivOfEq _
      (le_antisymm (ker_pairToKer_le hfg hreg) (ker_pairToTors_le hfg hf hex))).trans
      (LinearMap.quotKerEquivOfSurjective _ (pairToTors_surjective hfg hg hex)))

/-- **The equivalence of degree zero sends `x̄` to `g y` for `f x = n y`.** -/
theorem kerReduction_equiv_apply (hfg : g.comp f = 0) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : ∀ y, g y = 0 → ∃ x, f x = y)
    (hreg : IsSMulRegular P₀ n) (x : P₁) (y : P₀) (hxy : f x = n • y)
    (hmem : Submodule.Quotient.mk x ∈ LinearMap.ker (reduction n f)) :
    (kerReduction_equiv hfg hf hg hex hreg ⟨_, hmem⟩ : M) = g y := by
  have h : (⟨_, hmem⟩ : LinearMap.ker (reduction n f)) =
      pairToKer ⟨(x, y), (mem_pairSub n f).2 hxy⟩ := rfl
  rw [h]
  unfold kerReduction_equiv
  rw [LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- The map `P₀/nP₀ → M/nM` induced by `g`. -/
def cokerMap (g : P₀ →ₗ[R] M) : (P₀ ⧸ nSub n P₀) →ₗ[R] (M ⧸ nSub n M) :=
  (nSub n P₀).mapQ (nSub n M) g (by
    rintro _ ⟨y, rfl⟩
    exact ⟨g y, by simp⟩)

theorem cokerMap_surjective (hg : Function.Surjective g) :
    Function.Surjective (cokerMap (n := n) g) := by
  intro q
  obtain ⟨m, rfl⟩ := (nSub n M).mkQ_surjective q
  obtain ⟨y, rfl⟩ := hg m
  exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem ker_cokerMap (hfg : g.comp f = 0) (hg : Function.Surjective g)
    (hex : ∀ y, g y = 0 → ∃ x, f x = y) :
    LinearMap.ker (cokerMap (n := n) g) = LinearMap.range (reduction n f) := by
  ext q
  obtain ⟨y, rfl⟩ := (nSub n P₀).mkQ_surjective q
  constructor
  · intro h
    rw [LinearMap.mem_ker] at h
    change Submodule.Quotient.mk (g y) = (0 : M ⧸ nSub n M) at h
    rw [Submodule.Quotient.mk_eq_zero, mem_nSub] at h
    obtain ⟨m, hm⟩ := h
    obtain ⟨y', rfl⟩ := hg m
    obtain ⟨x, hx⟩ := hex (y - n • y') (by rw [map_sub, map_smul, hm, sub_self])
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    change Submodule.Quotient.mk (f x) = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq, hx, sub_sub_cancel_left, mem_nSub]
    exact ⟨-y', by rw [smul_neg]⟩
  · rintro ⟨q', hq'⟩
    obtain ⟨x, rfl⟩ := (nSub n P₁).mkQ_surjective q'
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk (f x) = Submodule.Quotient.mk y at hq'
    change Submodule.Quotient.mk (g y) = (0 : M ⧸ nSub n M)
    rw [Submodule.Quotient.eq, mem_nSub] at hq'
    obtain ⟨z, hz⟩ := hq'
    rw [Submodule.Quotient.mk_eq_zero, mem_nSub]
    refine ⟨-g z, ?_⟩
    have hy : y = f x - n • z := by rw [hz]; abel
    have hgf : g (f x) = 0 := LinearMap.congr_fun hfg x
    rw [hy, map_sub, hgf, map_smul, zero_sub, smul_neg]

/-- **Degree one of the derived reduction is `M/nM`** (tex L3417–3418): for a presentation
`P₁ --f--> P₀ --g--> M → 0`, `coker (f mod n) ≅ M/nM`. PROVED (no regularity or injectivity is
needed for degree one). -/
noncomputable def cokerReduction_equiv (hfg : g.comp f = 0) (hg : Function.Surjective g)
    (hex : ∀ y, g y = 0 → ∃ x, f x = y) :
    ((P₀ ⧸ nSub n P₀) ⧸ LinearMap.range (reduction n f)) ≃ₗ[R] (M ⧸ nSub n M) :=
  (Submodule.quotEquivOfEq _ _ (ker_cokerMap hfg hg hex).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (cokerMap_surjective hg))

/-! ### Non-vacuity -/

/-- **Non-vacuity**: `M = ℤ/2` presented by `2 : ℤ → ℤ`, reduced modulo `2`: the hypotheses hold,
and degree zero `ker f̄ ≅ M[2] = ℤ/2` is nonzero. -/
theorem reduction_example :
    let f : ℤ →ₗ[ℤ] ℤ := mulBy (2 : ℤ) ℤ
    let g : ℤ →ₗ[ℤ] ZMod 2 := (Int.castAddHom (ZMod 2)).toIntLinearMap
    g.comp f = 0 ∧ Function.Injective f ∧ Function.Surjective g ∧
      (∀ y, g y = 0 → ∃ x, f x = y) ∧ IsSMulRegular ℤ (2 : ℤ) ∧
      Nontrivial (torsionN (2 : ℤ) (ZMod 2)) := by
  intro f g
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    change ((2 * x : ℤ) : ZMod 2) = 0
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
  · intro a b h
    have h' : (2 : ℤ) * a = 2 * b := h
    omega
  · intro m
    exact ⟨m.val, by change ((m.val : ℤ) : ZMod 2) = m; simp⟩
  · intro y hy
    change ((y : ℤ) : ZMod 2) = 0 at hy
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨k, by change 2 • k = 2 * k; rfl⟩
  · intro a b h
    have h' : (2 : ℤ) * a = 2 * b := h
    omega
  · refine ⟨⟨⟨1, ?_⟩, 0, ?_⟩⟩
    · rw [LinearMap.mem_ker]; rfl
    · intro h; exact absurd (congrArg Subtype.val h) (by decide)

/-- **Non-vacuity, conclusion**: in the example, degree zero of the reduction, `ker (2 mod 2)`, is
nonzero: it is `M[2] = ℤ/2` (`kerReduction_equiv`). -/
theorem reduction_example_nontrivial :
    Nontrivial (LinearMap.ker (reduction (2 : ℤ) (mulBy (2 : ℤ) ℤ))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := reduction_example
  have := h6
  exact (kerReduction_equiv h1 h2 h3 h4 h5).toEquiv.nontrivial

end ZInQ.Contrib.CloudB3RC53.Duality
