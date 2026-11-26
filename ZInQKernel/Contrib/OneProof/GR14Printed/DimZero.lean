import ZInQKernel.HDecomp.Faltings.Leaves
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # GR14Printed (B1): the field at `g = 0`

Gaudron–Rémond, Duke Math. J. 163 (2014), p. 2058, take `A` of dimension `g ≥ 1`; the field
`ZInQ.SemistabAssembly.GaudronRemondThm14AnSS` also quantifies over `g = 0`. This file proves that
case outright (`gr14_dim_zero`): an abelian variety of dimension `0` has one point
(`subsingleton_of_dim_zero`: irreducible of Krull dimension `0`, and `T₀`), so it is `Spec K`
(`isIso_hom_of_subsingleton`: the unit section is a surjective closed immersion into a reduced
scheme); an isogenous `B` is then `Spec K` too, every isogeny out of either has degree `≤ 1`, and
`κ = 1` at `g = 0` (`grKappa_zero`). The height hypothesis is not used.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.DefFaltings

namespace ZInQ.GR14Printed

variable {K : Type} [Field K]

/-- An abelian variety whose underlying space has at most one point is `Spec K`: the unit section
`e : Spec K → A` is a closed immersion (a section over a one-point base), surjective, into a
reduced scheme, hence an isomorphism, and so is the structure morphism. -/
theorem isIso_hom_of_subsingleton (A : AbVar K) [Subsingleton A.X.left] : IsIso A.X.hom := by
  have hw : (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X).left ≫ A.X.hom = 𝟙 _ := by
    have := Over.w (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X)
    rw [Over.tensorUnit_hom] at this
    exact this
  have : IsClosedImmersion
      (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X).left :=
    isClosedImmersion_of_comp_eq_id A.X.hom _ hw
  have : Surjective (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X).left :=
    ⟨fun _ => ⟨(default : Spec (CommRingCat.of K)), Subsingleton.elim _ _⟩⟩
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have : IsIso (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X).left :=
    isIso_of_isClosedImmersion_of_surjective _
  have h2 : A.X.hom = inv (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X).left := by
    exact (IsIso.inv_eq_of_hom_inv_id hw).symm
  rw [h2]
  infer_instance

/-- Morphisms into an `Over` object whose structure morphism is an isomorphism are unique. -/
theorem subsingleton_hom_of_isIso {T X : Over (Spec (CommRingCat.of K))} [IsIso X.hom] :
    Subsingleton (T ⟶ X) :=
  ⟨fun u v => Over.OverMorphism.ext <| (cancel_mono X.hom).mp (by rw [Over.w u, Over.w v])⟩

/-- **An abelian variety of dimension `0` has one point**: its space is irreducible of Krull
dimension `0`, so the closure of every point is the whole space, and the space is `T₀`. -/
theorem subsingleton_of_dim_zero (A : AbVar K) (h : A.dim = ((0 : ℕ) : WithBot ℕ∞)) :
    Subsingleton A.X.left := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have hmax : ∀ c : TopologicalSpace.IrreducibleCloseds A.X.left, IsMax c := by
    rw [← Order.krullDim_nonpos_iff_forall_isMax]
    change topologicalKrullDim A.X.left ≤ 0
    rw [show topologicalKrullDim A.X.left = A.dim from rfl, h]
    rfl
  have hcl : ∀ x : A.X.left, closure ({x} : Set A.X.left) = Set.univ := by
    intro x
    let cx : TopologicalSpace.IrreducibleCloseds A.X.left :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    let cu : TopologicalSpace.IrreducibleCloseds A.X.left :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
    have hle : cx ≤ cu := fun _ _ => trivial
    have := (hmax cx).eq_of_le hle
    exact congrArg TopologicalSpace.IrreducibleCloseds.carrier this
  refine ⟨fun x y => ?_⟩
  exact (inseparable_iff_closure_eq.mpr ((hcl x).trans (hcl y).symm)).eq

/-- The degree of any homomorphism out of a `Spec K` is at most `1`. -/
theorem isogDeg_le_one {A B : AbVar K} [IsIso A.X.hom] (φ : A.X ⟶ B.X) : isogDeg φ ≤ 1 := by
  have := subsingleton_hom_of_isIso (T := ptObj K (AlgebraicClosure K)) (X := A.X)
  exact Finite.card_le_one_iff_subsingleton.mpr inferInstance

/-- `κ` at `g = 0` is `1`. -/
theorem grKappa_zero (d : ℕ) (x : ℝ) : grKappa 0 d x = 1 := by
  simp [grKappa]

/-- **The `g = 0` case of the field** (B1): if `A` has dimension `0` and is isogenous to `B`, both
are `Spec K`, the given isogeny has degree `≤ 1`, and `B → Spec K = A` is an isogeny of degree
`≤ 1`; `κ(A) = 1` at `g = 0`. -/
theorem gr14_dim_zero (A B : AbVar K) (hA : A.dim = ((0 : ℕ) : WithBot ℕ∞)) (d : ℕ) (x : ℝ)
    (hiso : ∃ φ : A.X ⟶ B.X, IsIsogeny φ) :
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa 0 d x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa 0 d x) := by
  obtain ⟨φ, hφ⟩ := hiso
  have hsA := subsingleton_of_dim_zero A hA
  have hsB : Subsingleton B.X.left := by
    refine ⟨fun y₁ y₂ => ?_⟩
    obtain ⟨x₁, rfl⟩ := hφ.2.2.surj y₁
    obtain ⟨x₂, rfl⟩ := hφ.2.2.surj y₂
    rw [Subsingleton.elim x₁ x₂]
  have := isIso_hom_of_subsingleton A
  have := isIso_hom_of_subsingleton B
  rw [grKappa_zero]
  refine ⟨⟨φ, hφ, by exact_mod_cast isogDeg_le_one φ⟩, ?_⟩
  let ψ : B.X ⟶ A.X := toUnit B.X ≫ η[A.X]
  have hψ : ψ.left = B.X.hom ≫ inv A.X.hom := by
    rw [IsIso.eq_comp_inv, Over.w ψ]
  have : IsIso ψ.left := by
    rw [hψ]
    infer_instance
  refine ⟨ψ, ⟨inferInstance, inferInstance, inferInstance⟩, by exact_mod_cast isogDeg_le_one ψ⟩

end ZInQ.GR14Printed
