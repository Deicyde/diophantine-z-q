import Mathlib.CategoryTheory.Iso
import ZInQKernel.Contrib.OneProof.EllAdic.RebaseEndpointLawsV1

set_option autoImplicit false

open CategoryTheory

namespace RC53.EllAdic.EndpointComparison

variable {C : Type*} [Category* C] {A B D E J U W : C}

/-- The source endpoint of the normalized inverse-image mate. -/
theorem source_after_rebase (a : A ≅ B) (k : A ≅ D) (t : D ⟶ E)
    (b : E ≅ J) (c : B ≅ J) (h : k.hom ≫ t ≫ b.hom = a.hom ≫ c.hom) :
    (a.inv ≫ k.hom) ≫ t = c.hom ≫ b.inv :=
  sourceAfterRebase (fun X Y : C => X ⟶ Y) (fun f g => f ≫ g) (fun X => 𝟙 X)
    (fun f g j => Category.assoc f g j) (fun f => Category.id_comp f) (fun f => Category.comp_id f)
    a.hom a.inv k.hom t b.hom b.inv c.hom a.inv_hom_id b.hom_inv_id h

/-- The target endpoint after applying the finite residue diagonal. -/
theorem target_after_rebase (a : A ≅ B) (k : A ≅ D) (t : D ⟶ E)
    (b : E ≅ J) (c : B ≅ J) (r : J ⟶ U) (l : U ⟶ W) (d : B ⟶ W)
    (h : k.hom ≫ t ≫ b.hom = a.hom ≫ c.hom) (hd : c.hom ≫ r ≫ l = d) :
    k.inv ≫ a.hom ≫ d = t ≫ b.hom ≫ r ≫ l :=
  targetAfterRebase (fun X Y : C => X ⟶ Y) (fun f g => f ≫ g) (fun X => 𝟙 X)
    (fun f g j => Category.assoc f g j) (fun f => Category.id_comp f)
    a.hom k.hom k.inv t b.hom c.hom r l d k.inv_hom_id h hd

end RC53.EllAdic.EndpointComparison
