import ZInQKernel.Contrib.CloudB3W16Torsion.NativeBridges
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq

/-! Exact bridges retain `A.X` and `A.grp`, rather than replacing its group structure on
`Over.mk A.X.hom`. All source laws below are transported from the original morphism group. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GoodReductionJacobian NeronModelInfra
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudB3W16Torsion
variable {k : Type} [Field k] (A : Grp (Over (Spec (.of k)))) [PkgI2.IsAbelianVariety A]

/-- The structure equation on a scheme map is the original over-category morphism. -/
def pointOverEquiv {T : Scheme} (t : T ⟶ Spec (.of k)) :
    (Over.mk t ⟶ A.X) ≃ SchemeHomOver t A.X.hom where
  toFun p := ⟨p.left, Over.w p⟩
  invFun p := Over.homMk p.1 p.2
  left_inv p := Over.OverMorphism.ext rfl
  right_inv p := Subtype.ext rfl

/-- The genuine natural law on points, using the original `A.grp` throughout. -/
def relativeLaw : RelativeGroupLaw k A.X.hom where
  mul {T} t x y := pointOverEquiv A t ((pointOverEquiv A t).symm x * (pointOverEquiv A t).symm y)
  one {T} t := pointOverEquiv A t 1
  inv {T} t x := pointOverEquiv A t ((pointOverEquiv A t).symm x)⁻¹
  mul_assoc {T} t x y z := by simp only [Equiv.symm_apply_apply]; rw [_root_.mul_assoc]
  one_mul {T} t x := by simp only [Equiv.symm_apply_apply, _root_.one_mul, Equiv.apply_symm_apply]
  mul_one {T} t x := by simp only [Equiv.symm_apply_apply, _root_.mul_one, Equiv.apply_symm_apply]
  inv_mul_cancel {T} t x := by simp only [Equiv.symm_apply_apply]; rw [inv_mul_cancel]
  mul_natural {T T'} t t' ψ hψ x y := by
    let P : Over.mk t' ⟶ Over.mk t := Over.homMk ψ hψ
    have key : ∀ z : SchemeHomOver t A.X.hom,
        GoodReductionJacobian.schemeHomOverComp ψ hψ z =
          pointOverEquiv A t' (P ≫ (pointOverEquiv A t).symm z) := by
      intro z
      apply Subtype.ext
      rfl
    rw [key, key, key]
    simp only [Equiv.symm_apply_apply]
    rw [MonObj.comp_mul]

theorem relativeLaw_commutative : (relativeLaw A).IsCommutative := by
  intro T t x y
  change pointOverEquiv A t ((pointOverEquiv A t).symm x * (pointOverEquiv A t).symm y) =
    pointOverEquiv A t ((pointOverEquiv A t).symm y * (pointOverEquiv A t).symm x)
  rw [mul_comm]

theorem fibre_eq_univ (s : Spec (.of k)) : A.X.hom.base ⁻¹' {s} = Set.univ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact Subsingleton.elim _ _

theorem abelianSchemePropertyBundle : AbelianSchemePropertyBundle k A.X.hom := by
  haveI := PkgI2.IsAbelianVariety.geomIntegral (A := A)
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  refine ⟨PkgI2.IsAbelianVariety.smooth, PkgI2.IsAbelianVariety.proper, ?_, ⟨relativeLaw A⟩⟩
  intro s
  rw [fibre_eq_univ]
  exact isConnected_univ

theorem smoothOfRelativeDimension (g : ℕ)
    (hg : topologicalKrullDim A.X.left = (g : WithBot ℕ∞)) :
    SmoothOfRelativeDimension g A.X.hom := by
  haveI := PkgI2.IsAbelianVariety.smooth (A := A)
  apply RelativeGroupLaw.smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq (relativeLaw A) g
  intro s
  rw [fibre_eq_univ]
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ A.X.left).isHomeomorph).trans hg

theorem specOver_self_hom : (PkgI2.specOver k k).hom = 𝟙 (Spec (.of k)) := by
  simp [PkgI2.specOver]

def selfSpecIso : PkgI2.specOver k k ≅ Over.mk (𝟙 (Spec (.of k))) :=
  Over.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Over.mk_hom, Category.id_comp]
    exact (specOver_self_hom (k := k)).symm)

def pointEquiv : PkgI2.Pts A k ≃ SchemeHomOver (𝟙 (Spec (.of k))) A.X.hom where
  toFun p := pointOverEquiv A (𝟙 _) ((selfSpecIso (k := k)).inv ≫ p)
  invFun p := (selfSpecIso (k := k)).hom ≫ (pointOverEquiv A (𝟙 _)).symm p
  left_inv p := by simp only [Equiv.symm_apply_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv p := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, Equiv.apply_symm_apply]

theorem pointEquiv_mul (x y : PkgI2.Pts A k) :
    pointEquiv A (x * y) = (relativeLaw A).mul (𝟙 _) (pointEquiv A x) (pointEquiv A y) := by
  change pointOverEquiv A (𝟙 _) ((selfSpecIso (k := k)).inv ≫ (x * y)) =
    pointOverEquiv A (𝟙 _)
      ((pointOverEquiv A (𝟙 _)).symm (pointOverEquiv A (𝟙 _) ((selfSpecIso (k := k)).inv ≫ x)) *
        (pointOverEquiv A (𝟙 _)).symm (pointOverEquiv A (𝟙 _) ((selfSpecIso (k := k)).inv ≫ y)))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, MonObj.comp_mul]

theorem pointEquiv_one : pointEquiv A (1 : PkgI2.Pts A k) = (relativeLaw A).one (𝟙 _) := by
  change pointOverEquiv A (𝟙 _) ((selfSpecIso (k := k)).inv ≫ (1 : PkgI2.Pts A k)) =
    pointOverEquiv A (𝟙 _) (1 : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X)
  rw [MonObj.comp_one]

theorem pointEquiv_pow (n : ℕ) (x : PkgI2.Pts A k) :
    pointEquiv A (x ^ n) = (relativeLaw A).nsmul (𝟙 _) n (pointEquiv A x) := by
  induction n with
  | zero => simpa only [pow_zero, RelativeGroupLaw.nsmul_zero] using pointEquiv_one A
  | succ n ih => rw [pow_succ, pointEquiv_mul, ih, RelativeGroupLaw.nsmul_succ]

def torsionEquivRelative (n : ℕ) : PkgI2.torsion A k n ≃
    {x : SchemeHomOver (𝟙 (Spec (.of k))) A.X.hom // (relativeLaw A).IsTorsionPoint (𝟙 _) n x} :=
  Equiv.subtypeEquiv (pointEquiv A) fun x => by
    change x ^ n = 1 ↔ (relativeLaw A).nsmul (𝟙 _) n (pointEquiv A x) = (relativeLaw A).one (𝟙 _)
    rw [← pointEquiv_pow, ← pointEquiv_one, (pointEquiv A).injective.eq_iff]

end ZInQ.Contrib.CloudB3W16Torsion
