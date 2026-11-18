import TorusKernelIsoV005
import SemiAbelianDimensionV003
import ZInQKernel.Contrib.MulEtale.Direct.Shared.StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# The closed fibre of `π` at the identity is the kernel; its local dimension is `r`

Over an algebraically closed field `k`, with `B` locally of finite type, the identity section
`η_B : Spec k → B` is the canonical rational point at `y = π(1_U)`, so it factors as
`Spec k ≅ Spec κ(y) → B`. Hence the scheme-theoretic kernel `K = U ×_{B, η} Spec k` is
isomorphic to the fibre `U ×_B Spec κ(y)` of `π`, compatibly with the maps to `U`, and the
identity of the torus goes to the identity of `U`.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open TorusDimension IsLocalRing

namespace SemiAbelianKernel

variable {k : Type} [Field k] {r : ℕ} {U B : Over (Spec (CommRingCat.of k))} [GrpObj U] [GrpObj B]
  {e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)}

variable (k) in
/-- The closed point of `Spec k`, as a point of the scheme. -/
def ptK : Spec (CommRingCat.of k) := closedPoint k

/-- The identity section of `B` maps the closed point to `π(1_U)`. -/
theorem unitSec_apply (π : U ⟶ B) [IsMonHom π] :
    unitSec B (closedPoint k) = π.left (NeronRelativeDimension.idPt U) := by
  have h : (η[U] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U).left ≫ π.left = unitSec B :=
    congrArg (fun p => p.left) (IsMonHom.one_hom π)
  rw [← h]
  rfl

/-- The identity section is the canonical rational point at `π(1_U)`. -/
theorem unitSec_eq_point [IsAlgClosed k] [LocallyOfFiniteType B.hom] (π : U ⟶ B) [IsMonHom π]
    (hy : IsClosed ({π.left (NeronRelativeDimension.idPt U)} : Set B.left)) :
    unitSec B = pointOfClosedPoint B.hom (π.left (NeronRelativeDimension.idPt U)) hy :=
  ext_of_apply_closedPoint_eq B.hom unitSec_comp (pointOfClosedPoint_comp _ _ _)
    ((unitSec_apply π).trans (pointOfClosedPoint_apply _ _ _ _).symm)

theorem isIso_specMap_of_iso {R S : CommRingCat} (f : R ≅ S) : IsIso (Spec.map f.hom) :=
  ⟨⟨Spec.map f.inv, by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id],
    by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]⟩⟩

/-- **The kernel is the closed fibre**: `K ≅ U ×_B Spec κ(π 1_U)` over `U`. -/
def kernelToFibre [IsAlgClosed k] [LocallyOfFiniteType B.hom] (π : U ⟶ B) [IsMonHom π]
    (hy : IsClosed ({π.left (NeronRelativeDimension.idPt U)} : Set B.left)) :
    kernel π ⟶ π.left.fiber (π.left (NeronRelativeDimension.idPt U)) :=
  pullback.map π.left (unitSec B) π.left
    (B.left.fromSpecResidueField (π.left (NeronRelativeDimension.idPt U))) (𝟙 _)
    (Spec.map (residueFieldIsoBase B.hom (π.left (NeronRelativeDimension.idPt U)) hy).hom)
    (𝟙 _) (by simp) (by rw [Category.comp_id, unitSec_eq_point π hy]; rfl)

instance kernelToFibre_isIso [IsAlgClosed k] [LocallyOfFiniteType B.hom] (π : U ⟶ B)
    [IsMonHom π] (hy : IsClosed ({π.left (NeronRelativeDimension.idPt U)} : Set B.left)) :
    IsIso (kernelToFibre π hy) := by
  have := isIso_specMap_of_iso
    (residueFieldIsoBase B.hom (π.left (NeronRelativeDimension.idPt U)) hy)
  unfold kernelToFibre
  exact pullback.map_isIso _ _ _ _ _ _ _ _ _

theorem kernelToFibre_fiberι [IsAlgClosed k] [LocallyOfFiniteType B.hom] (π : U ⟶ B)
    [IsMonHom π] (hy : IsClosed ({π.left (NeronRelativeDimension.idPt U)} : Set B.left)) :
    kernelToFibre π hy ≫ π.left.fiberι (π.left (NeronRelativeDimension.idPt U)) =
      pullback.fst π.left (unitSec B) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The identity of the torus goes to the identity of `U`. -/
theorem tauL_onePoint (hnat : IsNatural r U e) :
    tauL r U e (onePointT k r) = NeronRelativeDimension.idPt U := by
  have h := congrArg (fun p => p.left) (onePoint_comp_univPoint hnat)
  rw [Hom.one_def] at h
  have h' : Spec.map (CommRingCat.ofHom (oneChar k r : TorusRing k r →+* k)) ≫ tauL r U e =
      Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ unitSec U := h
  have h2 := congrArg (fun f => f (ptK k)) h'
  simp only [Scheme.Hom.comp_apply] at h2
  have hpt : Spec.map (CommRingCat.ofHom (oneChar k r : TorusRing k r →+* k)) (ptK k) =
      onePointT k r := by
    apply PrimeSpectrum.ext
    show Ideal.comap (oneChar k r : TorusRing k r →+* k) (maximalIdeal k) = idealOne k r
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    rfl
  have hc : Spec.map (CommRingCat.ofHom (algebraMap k k)) (ptK k) = ptK k :=
    Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [hpt, hc] at h2
  exact h2

end SemiAbelianKernel
