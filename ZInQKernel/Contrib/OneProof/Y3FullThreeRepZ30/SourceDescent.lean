import Mathlib

/-!
# Source descent of local finite type along finite, flat, surjective morphisms

Main result: if `f : X ⟶ Y` is finite, flat and surjective, `Z` is locally noetherian and
`f ≫ q` is locally of finite type, then `q : Y ⟶ Z` is locally of finite type.

Proof outline.
* Ring level (Artin-Tate, `fg_of_fg_of_fg`): for `R → S → T` with `R` noetherian, `T` of
  finite type over `R`, `T` finite over `S` and `S → T` injective, `S` is of finite type
  over `R`.
* Scheme level: by `HasRingHomProperty.iff_appLE` it suffices to treat
  `q.appLE U V e : Γ(Z, U) ⟶ Γ(Y, V)` for affine opens `U`, `V`. Put `W := f ⁻¹ᵁ V`, which is
  affine since `f` is affine. Then `Γ(Y, V) ⟶ Γ(X, W)` is finite (`IsFinite.finite_app`), and
  faithfully flat (flat by `HasRingHomProperty.appLE`, surjective on spectra by the square
  `IsAffineOpen.SpecMap_appLE_fromSpec`), hence injective; the composite
  `Γ(Z, U) ⟶ Γ(X, W)` is of finite type, and `Γ(Z, U)` is noetherian.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace Y3Buzzard.SourceDescent

universe u

/-! ## Ring level -/

/-- Artin-Tate in ring-hom form: if `R` is noetherian, `g.comp f` is of finite type, and `g` is
finite and injective, then `f` is of finite type. -/
theorem finiteType_of_comp_finite_injective {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [IsNoetherianRing R] (f : R →+* S) (g : S →+* T)
    (hgf : (g.comp f).FiniteType) (hg : g.Finite) (hinj : Function.Injective g) :
    f.FiniteType := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra S T := g.toAlgebra
  letI : Algebra R T := (g.comp f).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hAC : Algebra.FiniteType R T := hgf
  have hBC : Module.Finite S T := hg
  have hfg : (⊤ : Subalgebra R S).FG :=
    fg_of_fg_of_fg R S T hAC.out (Module.finite_def.mp hBC) hinj
  have hRS : Algebra.FiniteType R S := ⟨hfg⟩
  exact hRS

/-! ## Faithful flatness of `Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V)` -/

/-- For `f` flat and surjective and `V` an affine open of `Y` with affine preimage, the ring
map `Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V)` is faithfully flat. -/
theorem faithfullyFlat_appLE_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Flat f) (hfs : AlgebraicGeometry.Surjective f)
    {V : Y.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen (f ⁻¹ᵁ V)) :
    (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.FaithfullyFlat := by
  have hflat : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.Flat :=
    HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) f hf ⟨V, hV⟩ ⟨f ⁻¹ᵁ V, hW⟩ le_rfl
  have hsq : Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl) ≫ hV.fromSpec = hW.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hW le_rfl
  have hsurj : Function.Surjective (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)) := by
    intro p
    obtain ⟨x, hx⟩ := hfs.1 (hV.fromSpec p)
    have h1 : hV.fromSpec p ∈ (V : Set Y) :=
      (Set.ext_iff.mp hV.range_fromSpec _).mp ⟨p, rfl⟩
    have hxW : x ∈ ((f ⁻¹ᵁ V : X.Opens) : Set X) :=
      Eq.subst (motive := fun y => y ∈ (V : Set Y)) hx.symm h1
    obtain ⟨p', hp'⟩ := (Set.ext_iff.mp hW.range_fromSpec x).mpr hxW
    refine ⟨p', hV.fromSpec.isOpenEmbedding.toIsEmbedding.injective ?_⟩
    exact (Scheme.Hom.comp_apply (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)) hV.fromSpec
      p').symm.trans
      ((congrArg (fun g : Spec Γ(X, f ⁻¹ᵁ V) ⟶ Y => g p') hsq).trans
        ((Scheme.Hom.comp_apply hW.fromSpec f p').trans
          ((congrArg (fun y => f y) hp').trans hx)))
  have hflatSpec : AlgebraicGeometry.Flat (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)).mpr hflat
  exact (flat_and_surjective_SpecMap_iff (f.appLE V (f ⁻¹ᵁ V) le_rfl)).mp
    ⟨hflatSpec, ⟨hsurj⟩⟩

/-! ## Scheme level -/

/-- Source descent of local finite type along a finite, flat, surjective morphism, over a
locally noetherian base. -/
theorem locallyOfFiniteType_of_comp_finite {X Y Z : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ Z)
    [IsLocallyNoetherian Z] (hfin : AlgebraicGeometry.IsFinite f)
    (hflat : AlgebraicGeometry.Flat f) (hsurj : AlgebraicGeometry.Surjective f)
    (hfq : LocallyOfFiniteType (f ≫ q)) : LocallyOfFiniteType q := by
  haveI : AlgebraicGeometry.IsFinite f := hfin
  refine (HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)).mpr ?_
  rintro ⟨U, hU⟩ ⟨V, hV⟩ e
  have hU' : IsAffineOpen U := hU
  have hV' : IsAffineOpen V := hV
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := IsAffineOpen.preimage hV' f
  haveI : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU'⟩
  -- the inclusion `f ⁻¹ᵁ V ≤ (f ≫ q) ⁻¹ᵁ U`, as the image of `e` under pulling back along `f`
  have e' : f ⁻¹ᵁ V ≤ (f ≫ q) ⁻¹ᵁ U :=
    CategoryTheory.leOfHom ((TopologicalSpace.Opens.map f.base).map (CategoryTheory.homOfLE e))
  have hcomp := Scheme.Hom.appLE_comp_appLE f q U V (f ⁻¹ᵁ V) e le_rfl
  have h1 : RingHom.FiniteType (q.appLE U V e ≫ f.appLE V (f ⁻¹ᵁ V) le_rfl).hom :=
    (congrArg (fun g : Γ(Z, U) ⟶ Γ(X, f ⁻¹ᵁ V) => RingHom.FiniteType g.hom) hcomp).mpr
      (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (f ≫ q) hfq ⟨U, hU'⟩
        ⟨f ⁻¹ᵁ V, hW⟩ e')
  have h2 : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.Finite :=
    (congrArg (fun g : Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V) => g.hom.Finite)
      (Scheme.Hom.app_eq_appLE f (U := V))).mp (IsFinite.finite_app f V hV')
  have h3 : (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.FaithfullyFlat :=
    faithfullyFlat_appLE_preimage f hflat hsurj hV' hW
  exact finiteType_of_comp_finite_injective (q.appLE U V e).hom
    (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom h1 h2 h3.injective

/-- Special case of source descent for local finite type: `f` finite, flat and surjective,
the base locally noetherian. -/
def DescentLocallyOfFiniteTypeFinite : Prop :=
  ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (q : Y ⟶ Z), IsLocallyNoetherian Z →
    AlgebraicGeometry.IsFinite f → AlgebraicGeometry.Flat f →
      AlgebraicGeometry.Surjective f → LocallyOfFiniteType (f ≫ q) → LocallyOfFiniteType q

theorem descentLocallyOfFiniteTypeFinite : DescentLocallyOfFiniteTypeFinite := by
  intro X Y Z f q hZ hfin hflat hsurj hfq
  haveI : IsLocallyNoetherian Z := hZ
  exact locallyOfFiniteType_of_comp_finite f q hfin hflat hsurj hfq

end Y3Buzzard.SourceDescent

end
