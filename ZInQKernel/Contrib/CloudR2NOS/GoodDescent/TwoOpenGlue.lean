/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.
New two-open scheme-morphism gluing helper for the actual diagonal/generic
comparison construction. No effective scheme descent is assumed here.
-/
import Mathlib.AlgebraicGeometry.Gluing

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent

private def side {T : Scheme.{u}} (D G : T.Opens) : Bool → T.Opens
  | false => D
  | true => G

private def twoCover {T : Scheme.{u}} (D G : T.Opens) (hDG : D ⊔ G = ⊤) : T.OpenCover where
  I₀ := Bool
  X i := (side D G i).toScheme
  f i := (side D G i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun t => ?_, inferInstance⟩
    have ht : t ∈ D ⊔ G := by rw [hDG]; trivial
    rcases ht with ht | ht
    · exact ⟨false, ⟨t, ht⟩, rfl⟩
    · exact ⟨true, ⟨t, ht⟩, rfl⟩

private def charts {T Y : Scheme.{u}} {D G : T.Opens}
    (d : D.toScheme ⟶ Y) (g : G.toScheme ⟶ Y) :
    (i : Bool) → (side D G i).toScheme ⟶ Y
  | false => d
  | true => g

private theorem charts_compatible {T Y : Scheme.{u}} {D G : T.Opens}
    (d : D.toScheme ⟶ Y) (g : G.toScheme ⟶ Y)
    (h : pullback.fst D.ι G.ι ≫ d = pullback.snd D.ι G.ι ≫ g) :
    ∀ i j : Bool,
      pullback.fst (side D G i).ι (side D G j).ι ≫ charts d g i =
        pullback.snd (side D G i).ι (side D G j).ι ≫ charts d g j := by
  intro i j
  cases i <;> cases j
  · change pullback.fst D.ι D.ι ≫ d = pullback.snd D.ι D.ι ≫ d
    rw [(cancel_mono D.ι).mp (pullback.condition (f := D.ι) (g := D.ι))]
  · exact h
  · change pullback.fst G.ι D.ι ≫ g = pullback.snd G.ι D.ι ≫ d
    have h' := congrArg ((pullbackSymmetry G.ι D.ι).hom ≫ ·) h.symm
    simpa only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
      pullbackSymmetry_hom_comp_fst_assoc] using h'
  · change pullback.fst G.ι G.ι ≫ g = pullback.snd G.ι G.ι ≫ g
    rw [(cancel_mono G.ι).mp (pullback.condition (f := G.ι) (g := G.ι))]

/-- Glue the two *constructed* local morphisms along their actual overlap. -/
def glueTwo {T Y : Scheme.{u}} {D G : T.Opens}
    (hDG : D ⊔ G = ⊤) (d : D.toScheme ⟶ Y) (g : G.toScheme ⟶ Y)
    (h : pullback.fst D.ι G.ι ≫ d = pullback.snd D.ι G.ι ≫ g) : T ⟶ Y :=
  (twoCover D G hDG).glueMorphisms (charts d g) (charts_compatible d g h)

@[reassoc (attr := simp)]
theorem ι_glueTwo_left {T Y : Scheme.{u}} {D G : T.Opens}
    (hDG : D ⊔ G = ⊤) (d : D.toScheme ⟶ Y) (g : G.toScheme ⟶ Y)
    (h : pullback.fst D.ι G.ι ≫ d = pullback.snd D.ι G.ι ≫ g) :
    D.ι ≫ glueTwo hDG d g h = d := by
  exact (twoCover D G hDG).ι_glueMorphisms (charts d g) (charts_compatible d g h) false

@[reassoc (attr := simp)]
theorem ι_glueTwo_right {T Y : Scheme.{u}} {D G : T.Opens}
    (hDG : D ⊔ G = ⊤) (d : D.toScheme ⟶ Y) (g : G.toScheme ⟶ Y)
    (h : pullback.fst D.ι G.ι ≫ d = pullback.snd D.ι G.ι ≫ g) :
    G.ι ≫ glueTwo hDG d g h = g := by
  exact (twoCover D G hDG).ι_glueMorphisms (charts d g) (charts_compatible d g h) true

/-- Uniqueness is equality of scheme morphisms, not merely of points. -/
theorem hom_ext_two {T Y : Scheme.{u}} {D G : T.Opens}
    (hDG : D ⊔ G = ⊤) (a b : T ⟶ Y)
    (hd : D.ι ≫ a = D.ι ≫ b) (hg : G.ι ≫ a = G.ι ≫ b) : a = b := by
  apply (twoCover D G hDG).hom_ext
  intro i
  cases i
  · exact hd
  · exact hg

#print axioms ι_glueTwo_left
#print axioms ι_glueTwo_right
#print axioms hom_ext_two

end ZInQ.Contrib.CloudR2NOS.GoodDescent
