import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private abbrev productLiftSections (U : Cᵒᵖ) : Sheaf J Ab.{w} ⥤ Type w :=
  sheafToPresheaf J Ab.{w} ⋙ (evaluation Cᵒᵖ Ab.{w}).obj U ⋙ forget Ab.{w}

private noncomputable def productLiftCoordinates (U : Cᵒᵖ) (F : ℕ → Sheaf J Ab.{w}) :
    (productLiftSections J U).obj (∏ᶜ F) ≅ (∀ n, (productLiftSections J U).obj (F n)) :=
  PreservesProduct.iso (productLiftSections J U) F ≪≫ Types.productIso _

private lemma productLiftCoordinates_hom_apply (U : Cᵒᵖ) (F : ℕ → Sheaf J Ab.{w})
    (x : (productLiftSections J U).obj (∏ᶜ F)) (n : ℕ) :
    ((productLiftCoordinates J U F).hom x) n = (productLiftSections J U).map (Pi.π F n) x := by
  have he : (productLiftCoordinates J U F).hom ≫ (↾fun a => a n) =
      (productLiftSections J U).map (Pi.π F n) := by
    unfold productLiftCoordinates
    rw [Iso.trans_hom, Category.assoc, Types.productIso_hom_comp_eval,
      PreservesProduct.iso_hom, piComparison_comp_π]
  exact congrArg (fun g : (productLiftSections J U).obj (∏ᶜ F) ⟶
    (productLiftSections J U).obj (F n) => g x) he

/-- Over a single specified arrow, coordinatewise local lifts yield a lift
for the literal product map. This is pointwise in the arrow and does not
assert that general covering sieves have a covering countable intersection. -/
theorem sheafPiMap_imageSieve_of_coordinateLifts
    {F G : ℕ → Sheaf J Ab.{w}} (f : ∀ n, F n ⟶ G n)
    {U V : C} (q : V ⟶ U) (y : (∏ᶜ G).obj.obj (op U))
    (hlift : ∀ n, (Presheaf.imageSieve (f n).hom ((Pi.π G n).hom.app (op U) y)) q) :
    (Presheaf.imageSieve (Limits.Pi.map f).hom y) q := by
  classical
  let EU := productLiftSections J (op U)
  let EV := productLiftSections J (op V)
  let yn (n : ℕ) := EU.map (Pi.π G n) y
  have lifts (n : ℕ) : ∃ z : EV.obj (F n),
      EV.map (f n) z = (G n).obj.map q.op (yn n) := hlift n
  choose z hz using lifts
  let eF := productLiftCoordinates J (op V) F
  let eG := productLiftCoordinates J (op V) G
  let x := eF.inv z
  refine ⟨x, ?_⟩
  change EV.map (Limits.Pi.map f) x = (∏ᶜ G).obj.map q.op y
  have hx : eF.hom x = z := congrArg (fun g : (∀ n, EV.obj (F n)) ⟶ (∀ n, EV.obj (F n)) => g z)
    eF.inv_hom_id
  have invhom (a : EV.obj (∏ᶜ G)) : eG.inv (eG.hom a) = a :=
    congrArg (fun g : EV.obj (∏ᶜ G) ⟶ EV.obj (∏ᶜ G) => g a) eG.hom_inv_id
  have inj : Function.Injective eG.hom := fun a b hab =>
    (invhom a).symm.trans ((congrArg (fun k => eG.inv k) hab).trans (invhom b))
  apply inj
  funext n
  change ((productLiftCoordinates J (op V) G).hom (EV.map (Limits.Pi.map f) x)) n =
    ((productLiftCoordinates J (op V) G).hom ((∏ᶜ G).obj.map q.op y)) n
  rw [productLiftCoordinates_hom_apply, productLiftCoordinates_hom_apply]
  have hmap : EV.map (Pi.π G n) (EV.map (Limits.Pi.map f) x) = EV.map (f n) (EV.map (Pi.π F n) x) := by
    rw [← types_comp_apply, ← EV.map_comp, Pi.map_π, EV.map_comp, types_comp_apply]
  have hn : EV.map (Pi.π G n) ((∏ᶜ G).obj.map q.op y) = (G n).obj.map q.op (yn n) :=
    congrArg (fun g : (∏ᶜ G).obj.obj (op U) ⟶ (G n).obj.obj (op V) => g y)
      ((Pi.π G n).hom.naturality q.op)
  have hp : EV.map (Pi.π F n) x = z n :=
    (productLiftCoordinates_hom_apply J (op V) F x n).symm.trans (congrFun hx n)
  rw [hmap, hn, hp]
  exact hz n

end RC53.EllAdic
