import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.AffineLinePicard

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.ToricOrthogonality

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) {h : Polynomial k}

/-- A global unit equal to one along the constant section of a product
with an open line is pulled back from the line. -/
theorem exists_parameter_unit_of_normalized_global (hh : h ≠ 0) [IsIntegral (Limits.pullback f (affineLineOpenMap h))]
    {s : X ⟶ Limits.pullback f (affineLineOpenMap h)}
    (hs : s ≫ pullback.fst f (affineLineOpenMap h) = 𝟙 X)
    {a : Spec (.of k) ⟶ Spec (.of (Localization.Away h))}
    (hsa : s ≫ pullback.snd f (affineLineOpenMap h) = f ≫ a)
    (u : Γ(Limits.pullback f (affineLineOpenMap h), ⊤)ˣ) (hu : s.appTop u.val = 1) :
    ∃ w : Γ(Spec (.of (Localization.Away h)), ⊤)ˣ,
      u.val = (pullback.snd f (affineLineOpenMap h)).appTop w.val := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) (by trivial)
  have hle : U ≤ s ⁻¹ᵁ (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hs, Scheme.Hom.id_preimage]
  let ρ := (Limits.pullback f (affineLineOpenMap h)).presheaf.map (homOfLE (le_top : (pullback.fst f (affineLineOpenMap h)) ⁻¹ᵁ U ≤ ⊤)).op
  let u' := Units.map ρ.hom.toMonoidHom u
  have hu' : s.appLE _ U hle u'.val = 1 := by
    change s.appLE _ U hle (ρ u.val) = 1
    rw [← CommRingCat.comp_apply]
    erw [Scheme.Hom.map_appLE s hle (homOfLE (le_top : (pullback.fst f (affineLineOpenMap h)) ⁻¹ᵁ U ≤ ⊤)).op]
    change (s.appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) u.val = 1
    rw [CommRingCat.comp_apply, hu, map_one]
  obtain ⟨w, hw⟩ := exists_parameter_unit_of_normalized f hh hU ⟨x, hx⟩ hs hsa u' hle hu'
  refine ⟨w, ?_⟩
  have : Nonempty ((pullback.fst f (affineLineOpenMap h)) ⁻¹ᵁ U : (Limits.pullback f (affineLineOpenMap h)).Opens) := ⟨⟨s x, hle hx⟩⟩
  apply map_injective_of_isIntegral (Limits.pullback f (affineLineOpenMap h)) (homOfLE (le_top : (pullback.fst f (affineLineOpenMap h)) ⁻¹ᵁ U ≤ ⊤))
  exact hw

/-- A unit on the product which is one on both coordinate sections is one. -/
theorem unit_eq_one_of_coordinate_sections (hh : h ≠ 0) [IsIntegral (Limits.pullback f (affineLineOpenMap h))]
    {s : X ⟶ Limits.pullback f (affineLineOpenMap h)}
    (hs : s ≫ pullback.fst f (affineLineOpenMap h) = 𝟙 X)
    {a : Spec (.of k) ⟶ Spec (.of (Localization.Away h))}
    (hsa : s ≫ pullback.snd f (affineLineOpenMap h) = f ≫ a)
    {t : Spec (.of (Localization.Away h)) ⟶ Limits.pullback f (affineLineOpenMap h)}
    (ht : t ≫ pullback.snd f (affineLineOpenMap h) = 𝟙 (Spec (.of (Localization.Away h))))
    (u : Γ(Limits.pullback f (affineLineOpenMap h), ⊤)ˣ)
    (hu : s.appTop u.val = 1)
    (htu : t.appTop u.val = 1) :
    u.val = 1 := by
  obtain ⟨w, hw⟩ := exists_parameter_unit_of_normalized_global f hh hs hsa u hu
  have hw1 : w.val = 1 := by
    rw [hw, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ht, Scheme.Hom.id_appTop] at htu
    exact htu
  rw [hw, hw1, map_one]

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.unit_eq_one_of_coordinate_sections
