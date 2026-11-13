import Mathlib

/-! # Killing cotangent-independent elements lowers the embedding dimension

Task infra-smooth-dim. Mathlib-only.

If `ψ : B → C` is a ring map of local rings with `𝔪_B · C = 𝔪_C` (e.g. a surjective local map) that
kills elements `f_1, …, f_c ∈ 𝔪_B` whose classes in `𝔪_B/𝔪_B²` are linearly independent, then
`edim C + c ≤ edim B` (`edim = spanFinrank` of the maximal ideal). -/

open IsLocalRing

namespace InfraSmoothDim

theorem spanFinrank_add_card_le {B C : Type*} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [CommRing C] [IsLocalRing C] (ψ : B →+* C)
    (hmap : (maximalIdeal B).map ψ = maximalIdeal C)
    {σ : Type*} [Fintype σ] (f : σ → maximalIdeal B)
    (hf : LinearIndependent (ResidueField B) (fun i => (maximalIdeal B).toCotangent (f i)))
    (hker : ∀ i, ψ (f i) = 0) :
    (maximalIdeal C).spanFinrank + Fintype.card σ ≤ (maximalIdeal B).spanFinrank := by
  classical
  set κ := ResidueField B
  set V := CotangentSpace B
  let v : σ → V := fun i => (maximalIdeal B).toCotangent (f i)
  let W : Submodule κ V := Submodule.span κ (Set.range v)
  have hW : Module.finrank κ W = Fintype.card σ := finrank_span_eq_card hf
  have hVW := Submodule.finrank_quotient_add_finrank W
  set d := Module.finrank κ (V ⧸ W)
  let b := Module.finBasis κ (V ⧸ W)
  have hsurj : Function.Surjective
      (fun x : maximalIdeal B => W.mkQ ((maximalIdeal B).toCotangent x)) :=
    (Submodule.mkQ_surjective W).comp (Ideal.toCotangent_surjective _)
  choose g hg using fun j : Fin d => hsurj (b j)
  -- the classes of `f` and `g` span `V`
  let s : Set (maximalIdeal B) := Set.range f ∪ Set.range g
  have hspan : Submodule.span κ ((maximalIdeal B).toCotangent '' s) = ⊤ := by
    have h1 : W ≤ Submodule.span κ ((maximalIdeal B).toCotangent '' s) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨f i, Or.inl ⟨i, rfl⟩, rfl⟩
    have h2 : (Submodule.span κ ((maximalIdeal B).toCotangent '' s)).map W.mkQ = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [← hg j]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨g j, Or.inr ⟨j, rfl⟩, rfl⟩)
    have := Submodule.comap_map_mkQ W (Submodule.span κ ((maximalIdeal B).toCotangent '' s))
    rw [h2, Submodule.comap_top, sup_eq_right.mpr h1] at this
    exact this.symm
  have hspanB : Submodule.span B s = ⊤ := (CotangentSpace.span_image_eq_top_iff).mp hspan
  have hmB : maximalIdeal B = Ideal.span (((↑) : maximalIdeal B → B) '' s) := by
    have := congrArg (Submodule.map (maximalIdeal B).subtype) hspanB
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
    exact this.symm
  have hmC : maximalIdeal C = Ideal.span (Set.range fun j => ψ (g j)) := by
    rw [← hmap, congrArg (Ideal.map ψ) hmB, Ideal.map_span]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨_, ⟨x, hx | hx, rfl⟩, rfl⟩
      · obtain ⟨i, rfl⟩ := hx
        simp [hker i]
      · obtain ⟨j, rfl⟩ := hx
        exact Ideal.subset_span ⟨j, rfl⟩
    · rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨_, ⟨g j, Or.inr ⟨j, rfl⟩, rfl⟩, rfl⟩
  have hle : (maximalIdeal C).spanFinrank ≤ d := by
    rw [hmC]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := C)
      (Set.finite_range fun j => ψ (g j))
    refine this.trans ?_
    have h3 : (Set.range fun j => ψ (g j)).ncard ≤ Nat.card (Fin d) := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (Set.ncard_univ _).le
    rw [Nat.card_fin] at h3
    exact h3
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace B]
  change _ ≤ Module.finrank κ V
  omega

end InfraSmoothDim

#print axioms InfraSmoothDim.spanFinrank_add_card_le
