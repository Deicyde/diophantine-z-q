/-
Brauer–Nesbitt in characteristic zero, module form over an arbitrary algebra.

Project proof written for the pinned Lean 4.35.0 / Mathlib `v4.35.0` (2026-11-13).
The argument is the classical one (Lang, *Algebra*, rev. 3rd ed., XVII §3, Thm. 3.7 and
Cor. 3.8; locator recalled from memory, UNVERIFIED): the projection onto an isotypic component
commutes with every module endomorphism, so by the Jacobson density theorem it is the action of
an element of the algebra; that element is an idempotent on each module, and in characteristic
zero a nonzero idempotent has nonzero trace. No group, finiteness of a group, algebraic closure
or separability hypothesis is used. Only Mathlib is imported.
-/
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic

namespace ZInQ.Contrib.BrauerNesbitt

open Module

universe u v w

section Character

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- The character `a ↦ tr_k (a • ·)` of an `A`-module carrying a compatible `k`-structure. -/
noncomputable def character (V : Type w) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] (a : A) : k :=
  LinearMap.trace k V (Module.toModuleEnd k (S := A) V a)

theorem character_def (V : Type w) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] (a : A) :
    character k V a = LinearMap.trace k V (Module.toModuleEnd k (S := A) V a) :=
  rfl

variable {k}

/-- An `A`-submodule of a finite-dimensional `k`-space is finite-dimensional over `k`. -/
theorem finiteDimensional_submodule {V : Type w} [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [FiniteDimensional k V] (p : Submodule A V) :
    FiniteDimensional k p :=
  Module.Finite.of_injective (p.subtype.restrictScalars k) p.injective_subtype

/-- Isomorphic modules have the same character. -/
theorem character_congr {V W : Type*} [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    (e : V ≃ₗ[A] W) (a : A) : character k V a = character k W a := by
  rw [character_def, character_def, ← LinearMap.trace_conj' _ (e.restrictScalars k)]
  congr 1
  ext w
  simp [LinearEquiv.conj_apply]

/-- The character of a product is the sum of the characters. -/
theorem character_prod (V W : Type*) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] [Module A W]
    [IsScalarTower k A W] [FiniteDimensional k W] (a : A) :
    character k (V × W) a = character k V a + character k W a := by
  rw [character_def, character_def, character_def, ← LinearMap.trace_prodMap']
  congr 1

/-- The character is additive along a decomposition into complementary submodules. -/
theorem character_eq_add_of_isCompl {V : Type w} [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [FiniteDimensional k V] {p q : Submodule A V} (h : IsCompl p q)
    (a : A) : character k V a = character k p a + character k q a := by
  have := finiteDimensional_submodule (k := k) p
  have := finiteDimensional_submodule (k := k) q
  rw [← character_prod]
  exact (character_congr (Submodule.prodEquivOfIsCompl p q h) a).symm

end Character

section Semisimple

variable {A : Type v} [Ring A]

/-- A product of two semisimple modules is semisimple. -/
theorem isSemisimpleModule_prod (V W : Type*) [AddCommGroup V] [Module A V] [AddCommGroup W]
    [Module A W] [IsSemisimpleModule A V] [IsSemisimpleModule A W] :
    IsSemisimpleModule A (V × W) := by
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (ι := Bool)
    (p := fun b => cond b (LinearMap.range (LinearMap.inl A V W))
      (LinearMap.range (LinearMap.inr A V W))) (fun b => ?_) ?_
  · cases b
    · exact IsSemisimpleModule.range (LinearMap.inr A V W)
    · exact IsSemisimpleModule.range (LinearMap.inl A V W)
  · rw [iSup_bool_eq]
    exact LinearMap.sup_range_inl_inr

end Semisimple

section Separation

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- **Separating element.** In a semisimple `A`-module that is finite-dimensional over `k`, the
projection onto the isotypic component of a simple submodule `S`, along the sum of the other
isotypic components, is the action of one element `a : A`. -/
theorem exists_smul_eq_projection {M : Type w} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M] [IsSemisimpleModule A M]
    (S : Submodule A M) [IsSimpleModule A S] :
    ∃ a : A, (∀ m ∈ isotypicComponent A M S, a • m = m) ∧
      ∀ m : M, a • m ∈ isotypicComponent A M S := by
  set c := isotypicComponent A M S
  have hc : c ∈ isotypicComponents A M := ⟨S, inferInstance, rfl⟩
  set C := sSup (isotypicComponents A M \ {c})
  have hcompl : IsCompl c C := by
    refine ⟨sSupIndep_isotypicComponents A M hc, ?_⟩
    rw [codisjoint_iff, ← sSup_insert, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hc]
    exact sSup_isotypicComponents A M
  have hcinv : c.IsFullyInvariant := Submodule.IsFullyInvariant.isotypicComponent A M S
  have hCinv : C.IsFullyInvariant :=
    mem_fullyInvariantSubmodule_iff.mp <| (fullyInvariantSubmodule A M).sSupClosed fun x hx =>
      mem_fullyInvariantSubmodule_iff.mpr
        (Submodule.IsFullyInvariant.of_mem_isotypicComponents hx.1)
  have hcomm : ∀ (f : Module.End A M) (m : M),
      c.projection C hcompl (f m) = f (c.projection C hcompl m) := by
    intro f m
    have hm : m ∈ c ⊔ C := hcompl.sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hm
    have hfx : f x ∈ c := hcinv f hx
    have hfy : f y ∈ C := hCinv f hy
    rw [map_add, map_add, map_add,
      Submodule.projection_apply_of_mem_left hcompl hx,
      Submodule.projection_apply_of_mem_right hcompl hy,
      Submodule.projection_apply_of_mem_left hcompl hfx,
      Submodule.projection_apply_of_mem_right hcompl hfy, add_zero, add_zero]
  let P : Module.End (Module.End A M) M :=
    { toFun := c.projection C hcompl
      map_add' := map_add _
      map_smul' := fun f m => hcomm f m }
  have : Module.Finite (Module.End A M) M :=
    Module.Finite.of_restrictScalars_finite k (Module.End A M) M
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := M) P
  have hsmul : ∀ m : M, a • m = c.projection C hcompl m := fun m => LinearMap.congr_fun ha m
  refine ⟨a, fun m hm => (hsmul m).trans (Submodule.projection_apply_of_mem_left hcompl hm),
    fun m => ?_⟩
  rw [hsmul m]
  exact Submodule.projection_apply_mem hcompl m

/-- **Key step.** If two semisimple modules have the same character over a field of
characteristic zero, then every simple submodule of the first embeds in the second. -/
theorem exists_linearEquiv_submodule_of_character_eq [CharZero k]
    {V W : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSemisimpleModule A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W] [IsSemisimpleModule A W]
    (h : ∀ a : A, character k V a = character k W a)
    (S : Submodule A V) [IsSimpleModule A S] :
    ∃ T : Submodule A W, Nonempty (S ≃ₗ[A] T) := by
  by_contra hne
  have hW : isotypicComponent A W S = ⊥ := by
    refine sSup_eq_bot.mpr fun T hT => ?_
    obtain ⟨e⟩ := hT
    exact absurd ⟨T, ⟨e.symm⟩⟩ hne
  have : IsSemisimpleModule A (V × W) := isSemisimpleModule_prod V W
  let S' : Submodule A (V × W) := S.map (LinearMap.inl A V W)
  let eS : S ≃ₗ[A] S' :=
    Submodule.equivMapOfInjective (LinearMap.inl A V W) LinearMap.inl_injective S
  have : IsSimpleModule A S' := IsSimpleModule.congr eS.symm
  obtain ⟨a, ha₁, ha₂⟩ := exists_smul_eq_projection (k := k) S'
  -- `a` kills `W`: the second projection maps the `S`-isotypic component of `V × W`
  -- into the `S`-isotypic component of `W`, which is `⊥`.
  have hzero : ∀ w : W, a • w = 0 := by
    intro w
    have h2 := LinearMap.le_comap_isotypicComponent (↥S') (LinearMap.snd A V W)
      (ha₂ ((0 : V), w))
    rw [Submodule.mem_comap, eS.symm.isotypicComponent_eq, hW, Submodule.mem_bot] at h2
    simpa using h2
  -- `a` is the identity on `S`.
  have hid : ∀ v ∈ S, a • v = v := by
    intro v hv
    have h1 : ((v, 0) : V × W) ∈ isotypicComponent A (V × W) S' :=
      S'.le_isotypicComponent ⟨v, hv, rfl⟩
    simpa using congrArg Prod.fst (ha₁ _ h1)
  -- `a` is idempotent on `V`.
  have hidem : ∀ v : V, a • a • v = a • v := by
    intro v
    simpa using congrArg Prod.fst (ha₁ _ (ha₂ ((v, 0) : V × W)))
  set φ : Module.End k V := Module.toModuleEnd k (S := A) V a
  have hφidem : IsIdempotentElem φ := LinearMap.ext fun v => hidem v
  have hφne : φ ≠ 0 := by
    have := IsSimpleModule.nontrivial A S
    obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : S)
    intro hφ0
    apply hv0
    have h1 : a • v = 0 := LinearMap.congr_fun hφ0 v
    rw [hid v hv] at h1
    exact Subtype.ext h1
  have htrV : character k V a ≠ 0 := fun h0 =>
    hφne ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hφidem).mp h0)
  have htrW : character k W a = 0 := by
    have h0 : Module.toModuleEnd k (S := A) W a = 0 := LinearMap.ext fun w => hzero w
    rw [character_def, h0, map_zero]
  exact htrV ((h a).trans htrW)

end Separation

section Main

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

theorem nonempty_linearEquiv_of_character_eq_aux [CharZero k] (d : ℕ) :
    ∀ (V : Type w) (W : Type*) [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] [FiniteDimensional k V] [IsSemisimpleModule A V]
      [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
      [FiniteDimensional k W] [IsSemisimpleModule A W],
      finrank k V = d → (∀ a : A, character k V a = character k W a) →
        Nonempty (V ≃ₗ[A] W) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro V W _ _ _ _ _ _ _ _ _ _ _ _ hd h
    rcases subsingleton_or_nontrivial V with hV | hV
    · have h1 := h 1
      rw [character_def, character_def, (Module.toModuleEnd k (S := A) V).map_one,
        (Module.toModuleEnd k (S := A) W).map_one, LinearMap.trace_one, LinearMap.trace_one,
        Module.finrank_zero_of_subsingleton, Nat.cast_zero, eq_comm, Nat.cast_eq_zero] at h1
      have : Subsingleton W := Module.finrank_zero_iff.mp h1
      exact ⟨LinearEquiv.ofSubsingleton V W⟩
    · obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule A V
      obtain ⟨T, ⟨e⟩⟩ := exists_linearEquiv_submodule_of_character_eq h S
      obtain ⟨S', hSS'⟩ := exists_isCompl S
      obtain ⟨T', hTT'⟩ := exists_isCompl T
      have := finiteDimensional_submodule (k := k) S
      have := finiteDimensional_submodule (k := k) S'
      have := finiteDimensional_submodule (k := k) T'
      have hchar : ∀ a : A, character k S' a = character k T' a := by
        intro a
        have h1 := h a
        rw [character_eq_add_of_isCompl hSS', character_eq_add_of_isCompl hTT',
          character_congr e] at h1
        exact add_left_cancel h1
      have hlt : finrank k S' < d := by
        have h1 := ((Submodule.prodEquivOfIsCompl S S' hSS').restrictScalars k).finrank_eq
        rw [Module.finrank_prod] at h1
        have := IsSimpleModule.nontrivial A S
        have hpos : 0 < finrank k S := Module.finrank_pos
        omega
      obtain ⟨e'⟩ := ih (finrank k S') hlt S' T' rfl hchar
      exact ⟨(Submodule.prodEquivOfIsCompl S S' hSS').symm.trans
        ((e.prodCongr e').trans (Submodule.prodEquivOfIsCompl T T' hTT'))⟩

/-- **Brauer–Nesbitt in characteristic zero, module form** (Lang XVII Cor. 3.8, UNVERIFIED
locator). Let `A` be any algebra over a field `k` of characteristic zero. Two `A`-modules that are
semisimple, finite-dimensional over `k`, and have the same character `a ↦ tr_k (a • ·)` are
isomorphic. -/
theorem nonempty_linearEquiv_of_character_eq [CharZero k]
    (V : Type w) (W : Type*) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [FiniteDimensional k V] [IsSemisimpleModule A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k W] [IsSemisimpleModule A W]
    (h : ∀ a : A, character k V a = character k W a) : Nonempty (V ≃ₗ[A] W) :=
  nonempty_linearEquiv_of_character_eq_aux (finrank k V) V W rfl h

end Main

end ZInQ.Contrib.BrauerNesbitt
