/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed (git blob 65f188db0dedb60c04a75d358425cab446a41c62, sha256 9fc65469ce0f389ee2ee20be16131084bc12e9261475e9fa1d45c5dd83b2cd5b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Algebra_finite_integralClosure_adjoin_singleton_of_isAlgClosed

open Polynomial IntermediateField

open scoped IntermediateField.algebraAdjoinAdjoin Pointwise

namespace FiniteIntegralClosureAdjoinSingleton

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem isNoetherianRing_adjoin (y : F) :
    IsNoetherianRing (Algebra.adjoin k ({y} : Set F)) :=
  isNoetherianRing_of_fg ⟨{y}, by rw [Finset.coe_singleton]⟩

theorem fg_of_image_le {A A' : Subalgebra k F} (φ : F →+* F) (hφ : Function.Injective φ)
    (hlift : ∀ a' ∈ A', ∃ a ∈ A, φ a = a') [IsNoetherianRing A']
    (M' : Submodule A' F) (hM' : M'.FG) (B : Submodule A F) (hB : ∀ b ∈ B, φ b ∈ M') :
    B.FG := by
  classical
  haveI : IsNoetherian A' M' := isNoetherian_of_fg_of_noetherian M' hM'

  let P : Submodule A' F :=
    { carrier := φ '' (B : Set F)
      add_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨b + c, add_mem hb hc, map_add φ b c⟩
      zero_mem' := ⟨0, zero_mem _, map_zero φ⟩
      smul_mem' := by
        rintro a' _ ⟨b, hb, rfl⟩
        obtain ⟨a, ha, hφa⟩ := hlift a' a'.2
        refine ⟨(⟨a, ha⟩ : A) • b, B.smul_mem _ hb, ?_⟩
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        change φ a * φ b = (a' : F) * φ b
        rw [hφa] }
  have hPM' : P ≤ M' := by
    rintro _ ⟨b, hb, rfl⟩
    exact hB b hb
  have hPfg : P.FG := (isNoetherian_submodule.mp inferInstance) P hPM'

  obtain ⟨G, hG⟩ := hPfg
  have hGP : ∀ g ∈ G, ∃ b ∈ B, φ b = g := by
    intro g hg
    have : g ∈ P := hG ▸ Submodule.subset_span hg
    exact this
  choose t ht htφ using hGP
  let T : Finset F := G.attach.image fun g => t g.1 g.2
  have hTB : (T : Set F) ⊆ B := by
    intro y hy
    rw [Finset.coe_image] at hy
    obtain ⟨g, _, rfl⟩ := hy
    exact ht g.1 g.2

  have hkey : ∀ y ∈ P, ∃ c ∈ Submodule.span A (T : Set F), φ c = y := by
    intro y hy
    rw [← hG] at hy
    induction hy using Submodule.span_induction with
    | mem g hg =>
      refine ⟨t g hg, Submodule.subset_span ?_, htφ g hg⟩
      rw [Finset.mem_coe]
      exact Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩
    | zero => exact ⟨0, zero_mem _, map_zero φ⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨d, hd, rfl⟩ := hz
      exact ⟨c + d, add_mem hc hd, map_add φ c d⟩
    | smul a' y _ hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨a, ha, hφa⟩ := hlift a' a'.2
      refine ⟨(⟨a, ha⟩ : A) • c, Submodule.smul_mem _ _ hc, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      change φ a * φ c = (a' : F) * φ c
      rw [hφa]
  refine ⟨T, le_antisymm (Submodule.span_le.mpr hTB) ?_⟩
  intro b hb
  obtain ⟨c, hc, hφc⟩ := hkey (φ b) ⟨b, hb, rfl⟩
  rw [← hφ hφc]
  exact hc

section WithX

variable (x : F)




theorem fg_toSubmodule_integralClosure_of_isSeparable (hx : Transcendental k x)
    (E : IntermediateField (IntermediateField.adjoin k ({x} : Set F)) F) [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) E] [Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) E] :
    (Subalgebra.toSubmodule (integralClosure (Algebra.adjoin k ({x} : Set F)) E)).FG := by
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k ({x} : Set F)) := hx.uniqueFactorizationMonoid_adjoin
  haveI : IsIntegrallyClosed (Algebra.adjoin k ({x} : Set F)) := inferInstance
  haveI : IsNoetherianRing (Algebra.adjoin k ({x} : Set F)) := isNoetherianRing_adjoin x
  letI : Algebra (Algebra.adjoin k ({x} : Set F)) (integralClosure (Algebra.adjoin k ({x} : Set F)) E) := Subalgebra.algebra (integralClosure (Algebra.adjoin k ({x} : Set F)) E)
  letI : SMul (Algebra.adjoin k ({x} : Set F)) (integralClosure (Algebra.adjoin k ({x} : Set F)) E) := Algebra.toSMul
  haveI : IsScalarTower (Algebra.adjoin k ({x} : Set F)) (integralClosure (Algebra.adjoin k ({x} : Set F)) E) E :=
    IsScalarTower.subalgebra' (Algebra.adjoin k ({x} : Set F)) E E (integralClosure (Algebra.adjoin k ({x} : Set F)) E)
  exact Module.Finite.iff_fg.mp (IsIntegralClosure.finite (Algebra.adjoin k ({x} : Set F)) (IntermediateField.adjoin k ({x} : Set F)) E (integralClosure (Algebra.adjoin k ({x} : Set F)) E))

theorem exists_fg_of_isSeparable (hx : Transcendental k x)
    (E : IntermediateField (IntermediateField.adjoin k ({x} : Set F)) F) [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) E] [Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) E] :
    ∃ N : Submodule (Algebra.adjoin k ({x} : Set F)) F, N.FG ∧ ∀ f : F, f ∈ E → IsIntegral (Algebra.adjoin k ({x} : Set F)) f → f ∈ N := by
  have h1 := fg_toSubmodule_integralClosure_of_isSeparable x hx E
  let ψ : E →ₗ[(Algebra.adjoin k ({x} : Set F))] F := ((IntermediateField.val E).restrictScalars (Algebra.adjoin k ({x} : Set F))).toLinearMap
  refine ⟨(Subalgebra.toSubmodule (integralClosure (Algebra.adjoin k ({x} : Set F)) E)).map ψ, h1.map _, ?_⟩
  intro f hf hint
  refine ⟨⟨f, hf⟩, ?_, rfl⟩
  change IsIntegral (Algebra.adjoin k ({x} : Set F)) (⟨f, hf⟩ : E)
  have : ((IntermediateField.val E).restrictScalars (Algebra.adjoin k ({x} : Set F))) ⟨f, hf⟩ = f := rfl
  rw [← this] at hint
  exact (isIntegral_algHom_iff _ Subtype.val_injective).mp hint

theorem exists_pow_mem_separableClosure [FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F] :
    ∃ p e : ℕ, ExpChar F p ∧ ∀ f : F, f ^ p ^ e ∈ separableClosure (IntermediateField.adjoin k ({x} : Set F)) F := by
  haveI : IsPurelyInseparable (separableClosure (IntermediateField.adjoin k ({x} : Set F)) F) F :=
    separableClosure.isPurelyInseparable (IntermediateField.adjoin k ({x} : Set F)) F
  refine ⟨ringExpChar F, IsPurelyInseparable.exponent (separableClosure (IntermediateField.adjoin k ({x} : Set F)) F) F,
    inferInstance, fun f => ?_⟩
  obtain ⟨y, hy⟩ :=
    IsPurelyInseparable.exponent_def' (separableClosure (IntermediateField.adjoin k ({x} : Set F)) F) (L := F) (ringExpChar F) f
  rw [← hy]
  exact y.2

theorem exists_pow_eq_of_mem_adjoin_pow [IsAlgClosed k] (p e : ℕ) [ExpChar F p]
    {a' : F} (ha' : a' ∈ Algebra.adjoin k ({x ^ p ^ e} : Set F)) :
    ∃ a ∈ (Algebra.adjoin k ({x} : Set F)), a ^ p ^ e = a' := by
  induction ha' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨x, Algebra.self_mem_adjoin_singleton k x, hy.symm⟩
  | algebraMap c =>
    obtain ⟨d, rfl⟩ := IsAlgClosed.exists_pow_nat_eq c (pow_pos (expChar_pos F p) e)
    exact ⟨algebraMap k F d, Subalgebra.algebraMap_mem _ d, by rw [map_pow]⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a + b, add_mem ha hb, add_pow_expChar_pow a b p e⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a * b, mul_mem ha hb, mul_pow a b _⟩

theorem exists_fg_adjoin_pow_of_fg (q : ℕ) (hq : 0 < q) (N : Submodule (Algebra.adjoin k ({x} : Set F)) F) (hN : N.FG) :
    ∃ M' : Submodule (Algebra.adjoin k ({x ^ q} : Set F)) F,
      M'.FG ∧ ∀ f ∈ N, f ∈ M' := by

  have hxq : x ^ q ∈ Algebra.adjoin k ({x ^ q} : Set F) := Algebra.self_mem_adjoin_singleton k _
  have hxint : IsIntegral (Algebra.adjoin k ({x ^ q} : Set F)) x :=
    IsIntegral.of_pow hq
      (isIntegral_algebraMap (A := F) (x := (⟨x ^ q, hxq⟩ : Algebra.adjoin k ({x ^ q} : Set F))))
  obtain ⟨t, ht⟩ := hxint.fg_adjoin_singleton

  have hAA₁ : ∀ a ∈ (Algebra.adjoin k ({x} : Set F)), a ∈ Algebra.adjoin (Algebra.adjoin k ({x ^ q} : Set F)) ({x} : Set F) := by
    intro a ha
    have h1 : Algebra.adjoin k ({x} : Set F) ≤ Algebra.adjoin k ({x ^ q} ∪ {x} : Set F) :=
      Algebra.adjoin_mono Set.subset_union_right
    have h2 := Algebra.adjoin_union_eq_adjoin_adjoin k ({x ^ q} : Set F) ({x} : Set F)
    have := h1 ha
    rw [h2] at this
    exact this
  obtain ⟨S, hS⟩ := hN
  refine ⟨Submodule.span _ ((t : Set F) • (S : Set F)),
    Submodule.fg_span (Set.Finite.smul t.finite_toSet S.finite_toSet), ?_⟩

  have hstable : ∀ a ∈ Algebra.adjoin (Algebra.adjoin k ({x ^ q} : Set F)) ({x} : Set F),
      ∀ m ∈ Submodule.span (Algebra.adjoin k ({x ^ q} : Set F)) ((t : Set F) • (S : Set F)),
      a * m ∈ Submodule.span (Algebra.adjoin k ({x ^ q} : Set F)) ((t : Set F) • (S : Set F)) := by
    intro a ha m hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ti, hti, sj, hsj, rfl⟩ := Set.mem_smul.mp hy
      have hti' : ti ∈ Algebra.adjoin (Algebra.adjoin k ({x ^ q} : Set F)) ({x} : Set F) := by
        rw [← Subalgebra.mem_toSubmodule, ← ht]
        exact Submodule.subset_span hti
      have hat : a * ti ∈ Submodule.span (Algebra.adjoin k ({x ^ q} : Set F)) (t : Set F) := by
        rw [ht, Subalgebra.mem_toSubmodule]
        exact mul_mem ha hti'
      have hassoc : a * ti • sj = (a * ti) • sj := by
        simp only [smul_eq_mul, mul_assoc]
      rw [hassoc]
      exact Submodule.smul_mem_span_smul_of_mem hat hsj
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a' y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ hy
  intro f hf
  rw [← hS] at hf
  induction hf using Submodule.span_induction with
  | mem s hs =>
    have h1 : (1 : F) ∈ Submodule.span (Algebra.adjoin k ({x ^ q} : Set F)) (t : Set F) := by
      rw [ht, Subalgebra.mem_toSubmodule]; exact one_mem _
    have := Submodule.smul_mem_span_smul_of_mem h1 hs
    rwa [one_smul] at this
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y _ hy =>
    rw [Algebra.smul_def]
    exact hstable _ (hAA₁ _ a.2) _ hy

theorem fg_toSubmodule_integralClosure [IsAlgClosed k] (hx : Transcendental k x)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    (Subalgebra.toSubmodule (integralClosure (Algebra.adjoin k ({x} : Set F)) F)).FG := by

  obtain ⟨N, hNfg, hN⟩ := exists_fg_of_isSeparable x hx (separableClosure (IntermediateField.adjoin k ({x} : Set F)) F)

  obtain ⟨p, e, hp, hpe⟩ := exists_pow_mem_separableClosure (k := k) x
  haveI := hp
  have hq0 : 0 < p ^ e := pow_pos (expChar_pos F p) e
  let φ : F →+* F := iterateFrobenius F p e
  have hφ : ∀ f : F, φ f = f ^ p ^ e := fun f => iterateFrobenius_def p e f

  obtain ⟨M', hM'fg, hNM'⟩ := exists_fg_adjoin_pow_of_fg x (p ^ e) hq0 N hNfg
  haveI : IsNoetherianRing (Algebra.adjoin k ({x ^ p ^ e} : Set F)) :=
    isNoetherianRing_adjoin (x ^ p ^ e)
  refine fg_of_image_le φ φ.injective ?_ M' hM'fg _ ?_
  · intro a' ha'
    obtain ⟨a, ha, h⟩ := exists_pow_eq_of_mem_adjoin_pow x p e ha'
    exact ⟨a, ha, by rw [hφ, h]⟩
  · intro b hb
    refine hNM' _ (hN _ ?_ ?_)
    · rw [hφ]; exact hpe b
    · rw [hφ]; exact IsIntegral.pow hb _

end WithX

end FiniteIntegralClosureAdjoinSingleton

theorem solution
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] (x : F)
    (hx : Transcendental k x)
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    Module.Finite (Algebra.adjoin k ({x} : Set F))
      (integralClosure (Algebra.adjoin k ({x} : Set F)) F) :=
  Module.Finite.iff_fg.mpr
    (FiniteIntegralClosureAdjoinSingleton.fg_toSubmodule_integralClosure x hx hfd)
