/-
H5 lane3 Step 1: E1 `StabilizerClosedLocus` (Extraction.lean) PROVED NATIVELY. It uses the closed
trivial-fibre locus of the proved GM1 chain. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED.
Universe u.

Construction. On `A ×_K A → A` (second factor) put `Λ := μ^*M ⊗ (pr₁^*M)ᵛ`.
* Its rational slice at `x` is `(t_x)^*M ⊗ Mᵛ`, because `slice_x ≫ μ = t_x` (definitionally:
  `slice_x = (lift 𝟙 (toUnit ≫ x)).left`) and `slice_x ≫ pr₁ = 𝟙`.
* `Z :=` the trivial-residue-fibre locus of `Λ`. It is closed by `trivialFibreLocusClosed`
  (SeesawLocus, proved from H72 producers).
* For a rational point `x`, with closed image `τ`:
  `τ ∈ Z` ⇔ the residue fibre is trivial ⇔ the slice at `pointOfClosedPoint τ = x.left` is
  trivial ⇔ `t_x^*M ⊗ Mᵛ ≅ O` ⇔ `t_x^*M ≅ M`.
  - The slice-to-fibre direction is `residueFibre_trivial_of_slice`.
  - The fibre-to-slice direction is the factorization of the slice through the fibre (proved
    here).
  - The point identification uses Mathlib `pointEquivClosedPoint` and
    `ext_of_apply_closedPoint_eq`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.SeesawComplete
import ZInQKernel.Contrib.CloudR2NOS.Step1.Extraction

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- PROVED: at a closed point, a trivial residue fibre gives a trivial rational slice. -/
theorem slice_trivial_of_residueFibre {K : Type u} [Field K] [IsAlgClosed K] {X T : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of K)) (fT : T ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType fT]
    (L : (Limits.pullback fX fT).Modules) [L.IsInvertible] (τ : T) (hτ : IsClosed {τ})
    (hF : Scheme.Pic.map (pullback.fst (pullback.snd fX fT) (T.fromSpecResidueField τ))
      (Scheme.Pic.mk L) = 1) :
    Nonempty ((Scheme.Modules.pullback (sliceAt fX fT (pointOfClosedPoint fT τ hτ)
      (pointOfClosedPoint_comp fT τ hτ))).obj L ≅ 𝟙_ X.Modules) := by
  let e := residueFieldIsoBase fT τ hτ
  let t := pointOfClosedPoint fT τ hτ
  have ht : t ≫ fT = 𝟙 _ := pointOfClosedPoint_comp fT τ hτ
  have htdef : t = Spec.map e.hom ≫ T.fromSpecResidueField τ := rfl
  have hcond : sliceAt fX fT t ht ≫ pullback.snd fX fT =
      (fX ≫ Spec.map e.hom) ≫ T.fromSpecResidueField τ := by
    rw [pullback.lift_snd, Category.assoc, ← htdef]
  let φ := pullback.lift (sliceAt fX fT t ht) (fX ≫ Spec.map e.hom) hcond
  have hφp : φ ≫ pullback.fst (pullback.snd fX fT) (T.fromSpecResidueField τ) =
      sliceAt fX fT t ht := pullback.lift_fst _ _ _
  have h1 : Scheme.Pic.map (sliceAt fX fT t ht) (Scheme.Pic.mk L) = 1 := by
    rw [← hφp, Scheme.Pic.map_comp, hF, Scheme.Pic.map_one]
  rw [Scheme.Pic.map_mk, Scheme.Pic.one_eq_mk_unit] at h1
  exact (Scheme.Pic.mk_eq_mk_iff _ _).mp h1

/-- E1, PROVED natively. -/
theorem stabilizerClosedLocus : StabilizerClosedLocus.{u} := by
  intro K _ _ A _ M _
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  let Λ : (Limits.pullback A.X.hom A.X.hom).Modules :=
    (Scheme.Modules.pullback (μ[A.X]).left).obj M ⊗
      Scheme.Modules.dual ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M)
  refine ⟨{τ | Scheme.Pic.map (pullback.fst (pullback.snd A.X.hom A.X.hom)
      (A.X.left.fromSpecResidueField τ)) (Scheme.Pic.mk Λ) = 1},
    trivialFibreLocusClosed openImmersionFibreIff A.X.hom A.X.hom Λ, fun x => ?_⟩
  -- the rational point, its closed image, and the identification with `pointOfClosedPoint`
  let τ := x.left.base (IsLocalRing.closedPoint K)
  have hτ : IsClosed {τ} := (pointEquivClosedPoint A.X.hom ⟨x.left, Over.w x⟩).2
  have hpt : pointOfClosedPoint A.X.hom τ hτ = x.left :=
    ext_of_apply_closedPoint_eq A.X.hom (pointOfClosedPoint_comp _ _ _) (Over.w x)
      (pointOfClosedPoint_apply _ _ _ _)
  -- the slice of `Λ` at `x` is `t_x^*M ⊗ Mᵛ`
  have hsl : ∀ (t : Spec (CommRingCat.of K) ⟶ A.X.left) (ht : t ≫ A.X.hom = 𝟙 _), t = x.left →
      (Iso' ((Scheme.Modules.pullback (sliceAt A.X.hom A.X.hom t ht)).obj Λ) (𝟙_ _) ↔
        Iso' ((Scheme.Modules.pullback (transl A x)).obj M) M) := by
    intro t ht htx
    subst htx
    have hμ : sliceAt A.X.hom A.X.hom x.left ht ≫ (μ[A.X]).left = transl A x := rfl
    have hfst : sliceAt A.X.hom A.X.hom x.left ht ≫ pullback.fst A.X.hom A.X.hom = 𝟙 _ :=
      pullback.lift_fst _ _ _
    have hΛ : Iso' ((Scheme.Modules.pullback (sliceAt A.X.hom A.X.hom x.left ht)).obj Λ)
        ((Scheme.Modules.pullback (transl A x)).obj M ⊗ Scheme.Modules.dual M) :=
      (iso'_pb_tensor _ _ _).trans <|
        ((iso'_pb_comp _ _ _).trans (iso'_pb_congr hμ _)).tensor
          ((iso'_pb_dual _ _).trans
            ((iso'_pb_comp _ _ _).trans ((iso'_pb_congr hfst _).trans (iso'_pb_id _))).dual)
    constructor
    · intro h
      exact Iso'.of_tensor_dual_unit (hΛ.symm.trans h)
    · intro h
      exact hΛ.trans ((h.tensor (iso'_refl _)).trans (iso'_dual M))
  constructor
  · intro hx
    exact residueFibre_trivial_of_slice A.X.hom A.X.hom Λ τ hτ
      ((hsl _ _ hpt).mpr hx)
  · intro hZ
    exact (hsl _ _ hpt).mp (slice_trivial_of_residueFibre A.X.hom A.X.hom Λ τ hτ hZ)

/-- E with E1 discharged: from E3 alone. -/
theorem infiniteStabilizerExtraction_of_E3 (hE3 : InfiniteClosedSubgroupContainsIntegral.{u}) :
    InfiniteStabilizerExtraction.{u} :=
  infiniteStabilizerExtraction stabilizerClosedLocus hE3

end ZInQ.Contrib.CloudR2NOS.Step1
