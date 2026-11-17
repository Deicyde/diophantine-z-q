import ZInQKernel.Contrib.CloudB3W17bOkaComparison.GermSheafMaps
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.Basic

/-!
# Local coordinate maps as actual Oka analytic-space morphisms

The source object is the genuine open Euclidean Oka space with its actual
restricted holomorphic sheaf.  Its local-model proof is the empty-equation
identity chart, not a compatibility hypothesis.  The morphism carries the
proved germ/sheaf precomposition map and the proved preservation of constants.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace ComplexAnalytic
open Opposite Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- The actual top restriction has the same topological space. -/
def topRestrictionHomeomorph (Y : LocallyRingedSpace) :
    Y.restrict (⊤ : Opens Y).isOpenEmbedding ≃ₜ Y where
  toFun x := x.1
  invFun x := ⟨x, trivial⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- The top restriction is cut out by no equations in the same genuine ringed space. -/
theorem isCutOutBy_top_restriction (Y : LocallyRingedSpace) :
    IsCutOutBy (Y.ofRestrict (⊤ : Opens Y).isOpenEmbedding)
      (Fin.elim0 : Fin 0 → Y.presheaf.obj (op ⊤)) := by
  have he : (topRestrictionHomeomorph Y : Y.restrict (⊤ : Opens Y).isOpenEmbedding → Y) =
      (Y.ofRestrict (⊤ : Opens Y).isOpenEmbedding).base := rfl
  refine ⟨he ▸ (topRestrictionHomeomorph Y).isClosedEmbedding, ?_, ?_, ?_⟩
  · have hr := (topRestrictionHomeomorph Y).surjective.range_eq
    simpa only [he, Fin.forall_fin_zero, Set.setOf_true] using hr
  · intro x
    exact (ConcreteCategory.bijective_of_isIso
      ((Y.ofRestrict (⊤ : Opens Y).isOpenEmbedding).stalkMap x)).surjective
  · intro x
    rw [Set.range_eq_empty, Ideal.span_empty]
    have hi := (ConcreteCategory.bijective_of_isIso
      ((Y.ofRestrict (⊤ : Opens Y).isOpenEmbedding).stalkMap x)).injective
    ext a
    change ((Y.ofRestrict (⊤ : Opens Y).isOpenEmbedding).stalkMap x).hom a = 0 ↔ a = 0
    exact ⟨fun ha => hi (ha.trans (map_zero _).symm), fun ha => ha ▸ map_zero _⟩

/-- A genuine open subset of Oka's Euclidean model, with its restricted holomorphic sheaf. -/
def euclideanOpen (n : ℕ) (U : Opens (_root_.complexAffineSpace n)) : AnalyticSpace where
  toLocallyRingedSpace := (_root_.complexAffineSpace n).restrict U.isOpenEmbedding
  algebraMap := constantsAlgMap n U
  local_model _ :=
    ⟨⟨⊤, trivial⟩, n, 0, U,
      ((_root_.complexAffineSpace n).restrict U.isOpenEmbedding).ofRestrict
        (⊤ : Opens ((_root_.complexAffineSpace n).restrict U.isOpenEmbedding)).isOpenEmbedding,
      Fin.elim0,
      isCutOutBy_top_restriction ((_root_.complexAffineSpace n).restrict U.isOpenEmbedding),
      isCLinearHom_ofRestrict ((_root_.complexAffineSpace n).restrict U.isOpenEmbedding)
        (constantsAlgMap n U) ⊤⟩

/-- A locally analytic coordinate map gives an actual Oka analytic-space morphism. -/
def localCoordinateAnalytic {n m : ℕ} (U : Opens (_root_.complexAffineSpace n))
    (f : (ULift.{0} (Fin n) → ℂ) → (ULift.{0} (Fin m) → ℂ))
    (hf : ∀ x ∈ U, AnalyticAt ℂ f x) :
    euclideanOpen n U ⟶ AnalyticSpace.complexAffineSpace m :=
  ⟨localCoordinateLRS U f hf, fun _ => rfl⟩

@[simp]
theorem localCoordinateAnalytic_base {n m : ℕ} (U : Opens (_root_.complexAffineSpace n))
    (f : (ULift.{0} (Fin n) → ℂ) → (ULift.{0} (Fin m) → ℂ))
    (hf : ∀ x ∈ U, AnalyticAt ℂ f x) (x : U) :
    (localCoordinateAnalytic U f hf).toLRSHom.base x = f x.1 := rfl

end ZInQ.Contrib.CloudB3W17bOkaComparison
