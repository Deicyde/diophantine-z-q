
/-! ## unif-dims: `ProductCotangent`, proved -/

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)

/-- **`ProductCotangent`, proved** (the statement is the body of `ZInQ.UnifDims.ProductCotangent`).
`jᵢ` is the cotangent map of the projection `pᵢ`; the retractions are the cotangent maps of
`x ↦ (x, 1)` and `y ↦ (1, y)`; `cot_decomp` gives surjectivity, the retractions injectivity, and
`omega_map_le` (functoriality of `ω`) the lattice. -/
theorem productCotangent_aux :
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    ∃ (j₁ : 𝒢₁.cotangent →ₗ[𝓞 L] 𝒢P.cotangent) (j₂ : 𝒢₂.cotangent →ₗ[𝓞 L] 𝒢P.cotangent),
      (∀ f : IsLocalRing.maximalIdeal 𝒢₁.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ fst _ _)).hom (f : 𝒢₁.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₁ (𝒢₁.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      (∀ f : IsLocalRing.maximalIdeal 𝒢₂.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ snd _ _)).hom (f : 𝒢₂.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₂ (𝒢₂.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      Function.Bijective (LinearMap.coprod j₁ j₂) ∧
      𝒢P.omega = 𝒢₁.omega.map j₁ ⊔ 𝒢₂.omega.map j₂ := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd
  set j₁ := cotMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) with hj₁
  set j₂ := cotMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) with hj₂
  set ψ₁ := cotMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) with hψ₁
  set ψ₂ := cotMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) with hψ₂
  have r11 : ∀ a, ψ₁ (j₁ a) = a := by
    intro a
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₁.genStalk).toCotangent_surjective a
    change ψ₁ (j₁ (𝒢₁.dCls f)) = 𝒢₁.dCls f
    rw [hψ₁, hj₁, cotMap_dCls, cotMap_dCls]
    congr 1
    exact Subtype.ext (germ_retract₁ 𝒢P 𝒢₁ 𝒢₂ e f)
  have r22 : ∀ a, ψ₂ (j₂ a) = a := by
    intro a
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₂.genStalk).toCotangent_surjective a
    change ψ₂ (j₂ (𝒢₂.dCls f)) = 𝒢₂.dCls f
    rw [hψ₂, hj₂, cotMap_dCls, cotMap_dCls]
    congr 1
    exact Subtype.ext (germ_retract₂ 𝒢P 𝒢₁ 𝒢₂ e f)
  have r12 : ∀ c, ψ₁ (j₂ c) = 0 := by
    intro c
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₂.genStalk).toCotangent_surjective c
    change ψ₁ (j₂ (𝒢₂.dCls f)) = 0
    rw [hψ₁, hj₂, cotMap_dCls, cotMap_dCls]
    have h0 : (⟨_, map_nonunit _ _ (map_nonunit _ _ f.2)⟩ :
        IsLocalRing.maximalIdeal 𝒢₁.genStalk) = 0 :=
      Subtype.ext (germ_cross₁₂ 𝒢P 𝒢₁ 𝒢₂ e f f.2)
    exact (congrArg (IsLocalRing.maximalIdeal 𝒢₁.genStalk).toCotangent h0).trans (map_zero _)
  have r21 : ∀ a, ψ₂ (j₁ a) = 0 := by
    intro a
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₁.genStalk).toCotangent_surjective a
    change ψ₂ (j₁ (𝒢₁.dCls f)) = 0
    rw [hψ₂, hj₁, cotMap_dCls, cotMap_dCls]
    have h0 : (⟨_, map_nonunit _ _ (map_nonunit _ _ f.2)⟩ :
        IsLocalRing.maximalIdeal 𝒢₂.genStalk) = 0 :=
      Subtype.ext (germ_cross₂₁ 𝒢P 𝒢₁ 𝒢₂ e f f.2)
    exact (congrArg (IsLocalRing.maximalIdeal 𝒢₂.genStalk).toCotangent h0).trans (map_zero _)
  have dec : ∀ x, x = j₁ (ψ₁ x) + j₂ (ψ₂ x) := cot_decomp 𝒢P 𝒢₁ 𝒢₂ e
  refine ⟨j₁, j₂, fun f => ⟨map_nonunit (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)) _ f.2, ?_⟩,
    fun f => ⟨map_nonunit (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)) _ f.2, ?_⟩,
    ⟨?_, ?_⟩, ?_⟩
  · rw [hj₁, cotMap_dCls]; rfl
  · rw [hj₂, cotMap_dCls]; rfl
  · rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [LinearMap.coprod_apply] at h
    have h1 := congrArg ψ₁ h
    have h2 := congrArg ψ₂ h
    simp only [map_add, r11, r12, r21, r22, add_zero, zero_add] at h1 h2
    rw [h1, h2]
  · intro x
    exact ⟨(ψ₁ x, ψ₂ x), by rw [LinearMap.coprod_apply]; exact (dec x).symm⟩
  · refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
    · rw [dec x]
      exact Submodule.add_mem_sup
        (Submodule.mem_map_of_mem (omega_map_le 𝒢₁ 𝒢P _ (eta_inc₁ 𝒢P 𝒢₁ 𝒢₂ e)
          (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (Submodule.mem_map_of_mem hx)))
        (Submodule.mem_map_of_mem (omega_map_le 𝒢₂ 𝒢P _ (eta_inc₂ 𝒢P 𝒢₁ 𝒢₂ e)
          (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (Submodule.mem_map_of_mem hx)))
    · exact omega_map_le 𝒢P 𝒢₁ _ (IsMonHom.one_hom _) (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)
    · exact omega_map_le 𝒢P 𝒢₂ _ (IsMonHom.one_hom _) (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.productCotangent_aux
