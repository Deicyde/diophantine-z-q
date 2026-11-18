import NeronRelativeDimensionV001
import SemiAbelianDimensionV003
import AbelianDimensionLinkV001
import ZInQKernel.Contrib.CloudB3W16Dimension.StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.Dimension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing

/-!
# The three relative-dimension statement forms from the repository's proved theorems

* `SmoothRelDimKrullDim` is the conjunction of `SmoothOfRelativeDimension.topologicalKrullDim_le`
  and `SmoothOfRelativeDimension.le_topologicalKrullDim`.
* `SmoothGroupRelDimLocal` is
  `RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing` applied to the
  natural law on points of the given group object over `Spec R` (its multiplication, unit and
  inverse are those of the given `GrpObj` structure; the construction is the field-base one of the
  kernel's relative bridges, with the base ring arbitrary).
* `GroupSchemeDimStalk` is Stacks 045X, `topologicalKrullDim_eq_ringKrullDim_stalk_of_groupScheme`.

With these, the dimension relation for the generic fibre of a smooth group model holds with no
statement-form premise: `dim A = dim B + r` from the natural torus presentation.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GoodReductionJacobian NeronModelInfra
open scoped CategoryTheory.MonObj

namespace NeronRelativeDimension.Instantiation

theorem smoothRelDimKrullDim_proof : SmoothRelDimKrullDim := by
  intro K _ X f n _ _
  exact le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le f n)
    (SmoothOfRelativeDimension.le_topologicalKrullDim f n)

variable {R : Type} [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

/-- Points of `G` over a test scheme, as over-category morphisms and as scheme maps over `R`. -/
def pointOverEquiv {T : Scheme} (t : T ⟶ Spec (CommRingCat.of R)) :
    (Over.mk t ⟶ G) ≃ SchemeHomOver t G.hom where
  toFun p := ⟨p.left, Over.w p⟩
  invFun p := Over.homMk p.1 p.2
  left_inv p := Over.OverMorphism.ext rfl
  right_inv p := Subtype.ext rfl

/-- The natural group law on points of the group object `G`. -/
def relativeLaw : RelativeGroupLaw R G.hom where
  mul {T} t x y := pointOverEquiv G t ((pointOverEquiv G t).symm x * (pointOverEquiv G t).symm y)
  one {T} t := pointOverEquiv G t 1
  inv {T} t x := pointOverEquiv G t ((pointOverEquiv G t).symm x)⁻¹
  mul_assoc {T} t x y z := by simp only [Equiv.symm_apply_apply]; rw [_root_.mul_assoc]
  one_mul {T} t x := by simp only [Equiv.symm_apply_apply, _root_.one_mul, Equiv.apply_symm_apply]
  mul_one {T} t x := by simp only [Equiv.symm_apply_apply, _root_.mul_one, Equiv.apply_symm_apply]
  inv_mul_cancel {T} t x := by simp only [Equiv.symm_apply_apply]; rw [inv_mul_cancel]
  mul_natural {T T'} t t' ψ hψ x y := by
    let P : Over.mk t' ⟶ Over.mk t := Over.homMk ψ hψ
    have key : ∀ z : SchemeHomOver t G.hom,
        GoodReductionJacobian.schemeHomOverComp ψ hψ z =
          pointOverEquiv G t' (P ≫ (pointOverEquiv G t).symm z) := by
      intro z
      apply Subtype.ext
      rfl
    rw [key, key, key]
    simp only [Equiv.symm_apply_apply]
    rw [MonObj.comp_mul]

theorem smoothGroupRelDimLocal_proof : SmoothGroupRelDimLocal := by
  intro R _ _ G _ _
  exact RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
    (relativeLaw G)

/-- Group-scheme homogeneity at closed points (Stacks 045X, the repository's vendored proof). -/
theorem groupSchemeDimStalk_proof : GroupSchemeDimStalk := by
  intro k _ G _ hft g hg
  letI : G.left.Over (Spec (CommRingCat.of k)) := ⟨G.hom⟩
  letI : GrpObj (G.left.asOver (Spec (CommRingCat.of k))) := by
    change GrpObj G
    infer_instance
  letI : LocallyOfFiniteType (G.left ↘ Spec (CommRingCat.of k)) := by
    change LocallyOfFiniteType G.hom
    exact hft
  exact topologicalKrullDim_eq_ringKrullDim_stalk_of_groupScheme k G.left g hg

/-- **`dim A = a + t`** with all three statement forms discharged; the closed-fibre local
dimension `hfib` at the identity is the remaining input. -/
theorem dim_generic_eq_add_of_fibre {K : Type} [Field K] {O : ValuationSubring K}
    {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (e : (Over.pullback (jO O)).obj N ≅ A.X)
    {k : Type} [Field k] [IsAlgClosed k] (φ : O →+* k)
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N) [IsOpenImmersion inc.left]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) [Flat π.left] (a t : ℕ)
    (hB : topologicalKrullDim B.X.left = (a : WithBot ℕ∞))
    (hfib : letI := (π.left.stalkMap (idPt U)).hom.toAlgebra
      ringKrullDim (U.left.presheaf.stalk (idPt U) ⧸
        (IsLocalRing.maximalIdeal (B.X.left.presheaf.stalk (π.left (idPt U)))).map
          (algebraMap (B.X.left.presheaf.stalk (π.left (idPt U)))
            (U.left.presheaf.stalk (idPt U)))) = (t : WithBot ℕ∞)) :
    topologicalKrullDim A.X.left = ((a + t : ℕ) : WithBot ℕ∞) :=
  dim_generic_eq_add smoothGroupRelDimLocal_proof smoothRelDimKrullDim_proof
    groupSchemeDimStalk_proof N e φ U inc B π a t hB hfib

/-- **Closed endpoint: `dim A = dim B + r`** for the generic fibre `A` of a smooth group model `N`
over `O` (with its generic-fibre group isomorphism), any geometric fibre `N ×_O k`, an open
subgroup `U` of it with a flat homomorphism `π : U → B` to an abelian variety, and a split-torus
presentation of `ker π` that is natural in `k`-algebras, injective and onto the kernel. No
statement-form premise remains. -/
theorem dim_generic_closed {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (eA : (Over.pullback (jO O)).obj N ≅ A.X)
    {k : Type} [Field k] [IsAlgClosed k] (φ : O →+* k)
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N) [IsOpenImmersion inc.left]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) [IsMonHom π] [Flat π.left] (r : ℕ)
    {e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (SemiAbelianKernel.algPt k R ⟶ U)}
    (hnat : SemiAbelianKernel.IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : SemiAbelianKernel.algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) :
    ∃ a : ℕ, B.dim = (a : WithBot ℕ∞) ∧
      topologicalKrullDim A.X.left = ((a + r : ℕ) : WithBot ℕ∞) :=
  SemiAbelianKernel.exists_dim_generic_of_presentation smoothGroupRelDimLocal_proof
    smoothRelDimKrullDim_proof groupSchemeDimStalk_proof N eA φ U inc B π r hnat he hker

/-- **Closed endpoint for the identity component: `dim U = dim B + r`.** -/
theorem dim_identityComponent_closed {k : Type} [Field k] [IsAlgClosed k]
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U] [LocallyOfFiniteType U.hom]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) [IsMonHom π] [Flat π.left] (a r : ℕ)
    (hB : topologicalKrullDim B.X.left = (a : WithBot ℕ∞))
    {e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (SemiAbelianKernel.algPt k R ⟶ U)}
    (hnat : SemiAbelianKernel.IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : SemiAbelianKernel.algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) :
    topologicalKrullDim U.left = ((a + r : ℕ) : WithBot ℕ∞) :=
  SemiAbelianKernel.dim_identityComponent_of_presentation groupSchemeDimStalk_proof B π a hB
    hnat he hker

end NeronRelativeDimension.Instantiation
