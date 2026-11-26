import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace RC53.EllAdic

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasLimitsOfShape (Discrete ℕ) C]

/-- It is enough to check that the literal countable product maps of
component epimorphisms are epi. The functor whose finite-colimit preservation
is returned is the same `lim` used by `Pi.map`. -/
theorem countableProductsExact_of_piMap_epi
    (h : ∀ {A B : ℕ → C} (f : ∀ n, A n ⟶ B n),
      (∀ n, Epi (f n)) → Epi (Limits.Pi.map f)) : HasExactLimitsOfShape (Discrete ℕ) C := by
  let : (lim (J := Discrete ℕ) (C := C)).PreservesEpimorphisms := {
    preserves := by
      intro A B f hf
      let : Epi f := hf
      let a (n : ℕ) := A.obj (Discrete.mk n)
      let b (n : ℕ) := B.obj (Discrete.mk n)
      let d (n : ℕ) : a n ⟶ b n := f.app (Discrete.mk n)
      let α : Discrete.functor a ≅ A := NatIso.ofComponents (fun _ => Iso.refl _)
        (by rintro ⟨i⟩ ⟨j⟩ ⟨hij⟩; cases hij; simp)
      let β : Discrete.functor b ≅ B := NatIso.ofComponents (fun _ => Iso.refl _)
        (by rintro ⟨i⟩ ⟨j⟩ ⟨hij⟩; cases hij; simp)
      let γ : Discrete.functor a ⟶ Discrete.functor b :=
        Discrete.natTrans (fun n => d n.as)
      have hn : γ ≫ β.hom = α.hom ≫ f := by
        apply NatTrans.ext
        funext n
        cases n
        simp only [α, β, γ, Discrete.natTrans, NatIso.ofComponents_hom_app,
          NatTrans.comp_app, Iso.refl_hom, Category.comp_id, Category.id_comp, d]
      let L := lim (J := Discrete ℕ) (C := C)
      have hh : Limits.Pi.map d ≫ L.map β.hom = L.map α.hom ≫ L.map f := by
        change L.map γ ≫ L.map β.hom = L.map α.hom ≫ L.map f
        exact (L.map_comp γ β.hom).symm.trans
          ((congrArg (fun t => L.map t) hn).trans (L.map_comp α.hom f))
      let : Epi (Limits.Pi.map d) := h d (fun n => inferInstanceAs (Epi (f.app (Discrete.mk n))))
      have he : Epi (Limits.Pi.map d ≫ L.map β.hom) := inferInstance
      rw [hh] at he
      exact epi_of_epi (L.map α.hom) (L.map f) }
  exact hasExactLimitsOfShape_of_preservesEpi (C := C) (Discrete ℕ)

end RC53.EllAdic
