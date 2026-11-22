import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricFrameGluing
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.AffineLineUnits

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules

namespace ZInQ.ToricOrthogonality

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) {h : Polynomial k}

private theorem appLE_congr {A B : Scheme.{0}} {g g' : A ⟶ B} (hg : g = g')
    {U : B.Opens} {V : A.Opens} (e : V ≤ g ⁻¹ᵁ U) (e' : V ≤ g' ⁻¹ᵁ U) :
    g.appLE U V e = g'.appLE U V e' := by
  subst hg
  rfl

omit [IsAlgClosed k] [IsIntegral X] in
/-- Restriction of the unit from the parameter factor along a constant section. -/
private theorem section_parameter {U : X.Opens}
    {s : X ⟶ pullback f (affineLineOpenMap h)}
    {a : Spec (.of k) ⟶ Spec (.of (Localization.Away h))}
    (hsa : s ≫ pullback.snd f (affineLineOpenMap h) = f ≫ a)
    (hsU : U ≤ s ⁻¹ᵁ (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U))
    (w : Γ(Spec (.of (Localization.Away h)), ⊤)) :
    s.appLE _ U hsU ((pullback.snd f (affineLineOpenMap h)).appLE ⊤ (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U) le_top w) =
      f.appLE ⊤ U le_top (a.appTop w) := by
  rw [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE s (pullback.snd f (affineLineOpenMap h)) ⊤
        (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U) U le_top hsU,
    appLE_congr hsa _ le_top, Scheme.Hom.comp_appLE]
  rfl

omit [IsAlgClosed k] [IsIntegral X] in
private theorem fst_scalar_eq_snd {U : X.Opens} (v : Γ(Spec (.of k), ⊤)) :
    (pullback.fst f (affineLineOpenMap h)).app U (f.appLE ⊤ U le_top v) =
      (pullback.snd f (affineLineOpenMap h)).appLE ⊤
        (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U) le_top
        ((affineLineOpenMap h).appTop v) := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE (pullback.fst f (affineLineOpenMap h)) f ⊤ U (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U) le_top le_rfl,
    appLE_congr (pullback.condition (f := f) (g := affineLineOpenMap h)) _ le_top, Scheme.Hom.comp_appLE]
  rfl

/-- Units equal to one along a constant section of the product come from
the parameter factor. -/
theorem exists_parameter_unit_of_normalized (hh : h ≠ 0) {U : X.Opens}
    (hU : IsAffineOpen U) (hUn : (U : Set X).Nonempty)
    {s : X ⟶ pullback f (affineLineOpenMap h)}
    (hs : s ≫ pullback.fst f (affineLineOpenMap h) = 𝟙 X)
    {a : Spec (.of k) ⟶ Spec (.of (Localization.Away h))}
    (hsa : s ≫ pullback.snd f (affineLineOpenMap h) = f ≫ a)
    (u : Γ(pullback f (affineLineOpenMap h), (pullback.fst f (affineLineOpenMap h)) ⁻¹ᵁ U)ˣ)
    (hUpre : U ≤ s ⁻¹ᵁ (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U))
    (hu : s.appLE _ U hUpre u.val = 1) :
    ∃ w : Γ(Spec (.of (Localization.Away h)), ⊤)ˣ,
      u.val = (pullback.snd f (affineLineOpenMap h)).appLE ⊤
        (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U) le_top w.val := by
  obtain ⟨c, w, hcw⟩ := exists_unit_factorization f hh hU hUn u
  rw [hcw, map_mul, section_appLE_projection hs, section_parameter f hsa] at hu
  let v := Units.map a.appTop.hom.toMonoidHom w
  let v' := Units.map (f.appLE ⊤ U le_top).hom.toMonoidHom v
  have hcv : c = v'⁻¹ := by
    apply Units.ext
    apply v'.isUnit.mul_right_cancel
    exact hu.trans (Units.inv_mul v').symm
  let w' := Units.map (affineLineOpenMap h).appTop.hom.toMonoidHom v⁻¹ * w
  refine ⟨w', ?_⟩
  rw [hcw, hcv]
  change (pullback.fst f (affineLineOpenMap h)).app U (f.appLE ⊤ U le_top (v⁻¹).val) *
      (pullback.snd f (affineLineOpenMap h)).appLE ⊤ (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U) le_top w.val =
    (pullback.snd f (affineLineOpenMap h)).appLE ⊤
        (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U) le_top
        ((affineLineOpenMap h).appTop (v⁻¹).val * w.val)
  rw [map_mul, fst_scalar_eq_snd f]

/-- A line bundle on this product that is trivialized on one fibre over the
parameter line is trivial globally. -/
theorem exists_frame_product_of_section (hh : h ≠ 0)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    [IsIntegral (pullback f (affineLineOpenMap h))]
    (a : Spec (.of k) ⟶ Spec (.of (Localization.Away h)))
    (ha : a ≫ affineLineOpenMap h = 𝟙 (Spec (.of k)))
    (M : (pullback f (affineLineOpenMap h)).Modules) [M.IsInvertible]
    {v : Γ((Scheme.Modules.pullback (pullback.lift (𝟙 X) (f ≫ a) (by simp [ha]) : X ⟶ pullback f (affineLineOpenMap h))).obj M, ⊤)}
    (hv : IsFreeGenerator v) :
    ∃ m : Γ(M, ⊤), IsFreeGenerator m := by
  let s : X ⟶ pullback f (affineLineOpenMap h) := pullback.lift (𝟙 X) (f ≫ a) (by simp [ha])
  have hs : s ≫ pullback.fst f (affineLineOpenMap h) = 𝟙 X := pullback.lift_fst _ _ _
  have hsa : s ≫ pullback.snd f (affineLineOpenMap h) = f ≫ a := pullback.lift_snd _ _ _
  apply exists_frame_of_normalized_units hs (pullback.snd f (affineLineOpenMap h)) v
  · intro x
    obtain ⟨U, -, hx, m, hm⟩ := exists_isFreeGenerator_preimage_fst hX f hh M x
    obtain ⟨m', hm', hv'⟩ := exists_normalized_frame hs hm (hv.map (le_top : U ≤ ⊤))
    exact ⟨U, hx, m', hm', hv'⟩
  · intro W hW hWn u hu
    exact exists_parameter_unit_of_normalized f hh hW hWn hs hsa u _ hu

/-- A frame on the constant section extends to a trivialization of the product line. -/
theorem nonempty_iso_unit_product_of_section (hh : h ≠ 0)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    [IsIntegral (pullback f (affineLineOpenMap h))]
    (a : Spec (.of k) ⟶ Spec (.of (Localization.Away h)))
    (ha : a ≫ affineLineOpenMap h = 𝟙 (Spec (.of k)))
    (M : (pullback f (affineLineOpenMap h)).Modules) [M.IsInvertible]
    (e : unit X ≅ (Scheme.Modules.pullback
      (pullback.lift (𝟙 X) (f ≫ a) (by simp [ha]) : X ⟶ pullback f (affineLineOpenMap h))).obj M) :
    Nonempty (unit (pullback f (affineLineOpenMap h)) ≅ M) := by
  obtain ⟨m, hm⟩ := exists_frame_product_of_section f hh hX a ha M
    ((isFreeGenerator_one (⊤ : X.Opens)).app_hom e)
  have : IsIso (homOfGlobalSection M m) := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (fun a : Γ(pullback f (affineLineOpenMap h), U) => (homOfGlobalSection M m).app U a)
    rw [funext (homOfGlobalSection_app M m U)]
    exact hm U le_top
  exact ⟨asIso (homOfGlobalSection M m)⟩

/-- Picard classes on the product with an open affine line are pulled back from
the first factor when the parameter has a rational point. -/
theorem pic_map_fst_surjective (hh : h ≠ 0)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    [IsIntegral (pullback f (affineLineOpenMap h))]
    (a : Spec (.of k) ⟶ Spec (.of (Localization.Away h)))
    (ha : a ≫ affineLineOpenMap h = 𝟙 (Spec (.of k))) :
    Function.Surjective (Scheme.Pic.map (pullback.fst f (affineLineOpenMap h))) := by
  let s : X ⟶ pullback f (affineLineOpenMap h) := pullback.lift (𝟙 X) (f ≫ a) (by simp [ha])
  have hs : s ≫ pullback.fst f (affineLineOpenMap h) = 𝟙 X := pullback.lift_fst _ _ _
  intro L
  let C := L * (Scheme.Pic.map (pullback.fst f (affineLineOpenMap h)) (Scheme.Pic.map s L))⁻¹
  have hC : Scheme.Pic.map s C = 1 := by
    simp only [C, ← Scheme.Pic.mapHom_apply, map_mul, map_inv]
    simp only [Scheme.Pic.mapHom_apply, ← Scheme.Pic.map_comp]
    rw [← Category.assoc, hs, Category.id_comp, mul_inv_cancel]
  let M := (fromSkeleton (pullback f (affineLineOpenMap h)).Modules).obj C.val
  obtain ⟨α⟩ : Nonempty ((Scheme.Modules.pullback s).obj M ≅ unit X) :=
    (Scheme.Pic.mk_eq_mk_iff _ _).mp hC
  let x := α.inv.app ⊤ (1 : Γ(X, ⊤))
  have hx : IsFreeGenerator x := (isFreeGenerator_one (⊤ : X.Opens)).app_hom α.symm
  obtain ⟨m, hm⟩ := exists_frame_product_of_section f hh hX a ha M hx
  have : IsIso (homOfGlobalSection M m) := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (fun a : Γ(pullback f (affineLineOpenMap h), U) => (homOfGlobalSection M m).app U a)
    rw [funext (homOfGlobalSection_app M m U)]
    exact hm U le_top
  have hC1 : C = 1 := (Scheme.Pic.mk_fromSkeleton C).symm.trans
    ((Scheme.Pic.mk_eq_mk_iff _ _).mpr ⟨(asIso (homOfGlobalSection M m)).symm⟩)
  exact ⟨Scheme.Pic.map s L, (mul_inv_eq_one.mp hC1).symm⟩

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.pic_map_fst_surjective
