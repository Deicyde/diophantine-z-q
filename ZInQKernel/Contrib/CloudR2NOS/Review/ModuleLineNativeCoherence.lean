/-
NEW H5 edition (lost original), authored from importer usage; helper of lead 21826d9b

Native coherence facts for `modulesPseudofunctor`: the explicit five-factor form of
`pullHom`, and the vanishing of `pullbackCongr` along a self-equality. `modulesPseudofunctor`,
`pullHom` and `modulesPseudofunctor_pullHom_eq` are imported, not redefined. No line cocycle
or ampleness assumption and no kernel budget changes.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PullbackUnit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- Component form: `pullbackCongr` along a self-equality has identity inverse components. -/
theorem native_pullbackCongr_self_inv_nat {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).inv.app M = 𝟙 _ := by
  first
  | rfl
  | simp [Scheme.Modules.pullbackCongr]

/-- `Iso.app` form of the same fact. -/
theorem native_pullbackCongr_self_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    ((Scheme.Modules.pullbackCongr (rfl : f = f)).app M).inv = 𝟙 _ := by
  rw [Iso.app_inv]
  exact native_pullbackCongr_self_inv_nat f M

/-- `pullHom` of `modulesPseudofunctor` as the literal native five-factor composite. -/
theorem native_pullHom_explicit {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules}
    {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (F := modulesPseudofunctor) (M₁ := M₁) (M₂ := M₂)
        (f₁ := f₁) (f₂ := f₂) φ g gf₁ gf₂ hgf₁ hgf₂ =
      (Scheme.Modules.pullbackCongr hgf₁).inv.app M₁ ≫
        (Scheme.Modules.pullbackComp g f₁).inv.app M₁ ≫
          (Scheme.Modules.pullback g).map φ ≫
            (Scheme.Modules.pullbackComp g f₂).hom.app M₂ ≫
              (Scheme.Modules.pullbackCongr hgf₂).hom.app M₂ := by
  subst hgf₁ hgf₂
  have hQ : (Scheme.Modules.pullbackCongr (rfl : g ≫ f₂ = g ≫ f₂)).hom.app M₂ = 𝟙 _ := by
    first
    | rfl
    | simp [Scheme.Modules.pullbackCongr]
  rw [native_pullbackCongr_self_inv_nat (g ≫ f₁) M₁, hQ, Category.id_comp, Category.comp_id]
  exact modulesPseudofunctor_pullHom_eq φ g

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
