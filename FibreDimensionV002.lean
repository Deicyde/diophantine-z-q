import FibreKernelV003

/-!
# `hfib` from the natural presentation, and `dim A = a + t`

The closed-fibre local ring of `π` at the identity, `𝒪_{U,1}/𝔪_{π 1}𝒪_{U,1}`, is the local ring
of the fibre at the identity (fibre local-ring identification), which is the local ring of the
scheme-theoretic kernel (the kernel is the fibre), which is the local ring of `𝔾_m^r` at the
identity (the kernel is the torus), of Krull dimension `r`. This discharges the input `hfib` of
the dimension formula; with it, `dim U = a + r` and `dim A = a + r` for the generic fibre of a
smooth group model.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open TorusDimension IsLocalRing NeronRelativeDimension

namespace SemiAbelianKernel

variable {k : Type} [Field k] {r : ℕ} {U B : Over (Spec (CommRingCat.of k))} [GrpObj U] [GrpObj B]
  {e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)}

theorem isClosed_unit_image [IsAlgClosed k] [LocallyOfFiniteType B.hom] (π : U ⟶ B)
    [IsMonHom π] : IsClosed ({π.left (idPt U)} : Set B.left) := by
  have h := mem_closedPoints_iff.mp (pointEquivClosedPoint B.hom ⟨unitSec B, unitSec_comp⟩).2
  have h' : IsClosed ({unitSec B (closedPoint k)} : Set B.left) := h
  rwa [unitSec_apply π] at h'

/-- **`hfib`, derived**: the closed-fibre local ring of `π` at the identity has Krull dimension
`r`, the rank of the natural torus presentation of `ker π`. -/
theorem hfib_of_presentation [IsAlgClosed k] [LocallyOfFiniteType B.hom] (π : U ⟶ B)
    [IsMonHom π] (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) :
    letI := (π.left.stalkMap (idPt U)).hom.toAlgebra
    ringKrullDim (U.left.presheaf.stalk (idPt U) ⧸
      (maximalIdeal (B.left.presheaf.stalk (π.left (idPt U)))).map
        (algebraMap (B.left.presheaf.stalk (π.left (idPt U)))
          (U.left.presheaf.stalk (idPt U)))) = (r : WithBot ℕ∞) := by
  let hy := isClosed_unit_image (B := B) π
  let m := kernelToFibre π hy
  let p : kernel π := (kernelLift π hker) (onePointT k r)
  have hmp : m p = π.left.asFiber (idPt U) := by
    apply (π.left.fiberι (π.left (idPt U))).isEmbedding.injective
    rw [Scheme.Hom.fiberι_asFiber, ← Scheme.Hom.comp_apply, kernelToFibre_fiberι]
    show (kernelLift π hker ≫ pullback.fst π.left (unitSec B)) (onePointT k r) = idPt U
    rw [kernelLift_fst]
    exact tauL_onePoint hnat
  have h1 := ringKrullDim_eq_of_ringEquiv
    (ZInQ.Contrib.MulEtale.StacksVendor.AlgebraicGeometry.quotientStalkEquivFiberStalk π.left
      (idPt U))
  have h2 : ringKrullDim ((π.left.fiber (π.left (idPt U))).presheaf.stalk (m p)) =
      ringKrullDim ((kernel π).presheaf.stalk p) :=
    ringKrullDim_eq_of_ringEquiv (asIso (m.stalkMap p)).commRingCatIsoToRingEquiv
  rw [hmp] at h2
  have h3 := kernel_stalk_dim π hnat he hker
  exact h1.trans (h2.trans h3)

/-- **`dim U = a + r`** for a flat torus-by-abelian extension with natural presentation. -/
theorem dim_identityComponent_of_presentation (hHom : GroupSchemeDimStalk) [IsAlgClosed k]
    [LocallyOfFiniteType U.hom] (B : PkgI3.AbVar k) (π : U ⟶ B.X) [IsMonHom π] [Flat π.left]
    (a : ℕ) (hB : topologicalKrullDim B.X.left = (a : WithBot ℕ∞))
    {e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)}
    (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) :
    topologicalKrullDim U.left = ((a + r : ℕ) : WithBot ℕ∞) :=
  dim_identityComponent_eq_add hHom U B π a r hB (hfib_of_presentation π hnat he hker)

variable {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}

/-- **`dim A = a + r`** for the generic fibre of a smooth group model, from the natural torus
presentation of the identity component of a geometric fibre. -/
theorem dim_generic_of_presentation (hV1 : SmoothGroupRelDimLocal) (hV3 : SmoothRelDimKrullDim)
    (hHom : GroupSchemeDimStalk)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (eA : (Over.pullback (jO O)).obj N ≅ A.X)
    {k : Type} [Field k] [IsAlgClosed k] (φ : O →+* k)
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N) [IsOpenImmersion inc.left]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) [IsMonHom π] [Flat π.left] (a r : ℕ)
    (hB : topologicalKrullDim B.X.left = (a : WithBot ℕ∞))
    {e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)}
    (hnat : IsNatural r U e)
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hker : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range) :
    topologicalKrullDim A.X.left = ((a + r : ℕ) : WithBot ℕ∞) :=
  dim_generic_eq_add hV1 hV3 hHom N eA φ U inc B π a r hB (hfib_of_presentation π hnat he hker)

end SemiAbelianKernel
