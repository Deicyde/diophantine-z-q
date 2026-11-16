import ZInQKernel.Contrib.CloudB3W16Torsion.NativeBridges
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq

/-!
# Exact geometric bridges from PkgI2 abelian varieties to the FLT source

The field, underlying scheme, structure map and original multiplicative law are
unchanged. These bridges discharge only the geometric prerequisites of the source
cardinality theorem; they do not assert that cardinality theorem.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GoodReductionJacobian NeronModelInfra
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudB3W16Torsion

variable {k : Type} [Field k] (A : Grp (Over (Spec (.of k))))
  [PkgI2.IsAbelianVariety A]

/-- The original group scheme law, viewed as the source's natural law on points. -/
def relativeLaw : RelativeGroupLaw k A.X.hom := by
  haveI : GrpObj (Over.mk A.X.hom) := inferInstanceAs (GrpObj A.X)
  exact relativeGroupLawOfGrpObj k A.X.hom

/-- Commutativity comes from Mathlib's theorem for the original abelian variety. -/
theorem relativeLaw_commutative : (relativeLaw A).IsCommutative := by
  haveI : GrpObj (Over.mk A.X.hom) := inferInstanceAs (GrpObj A.X)
  exact fun t x y => relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj
    (inferInstanceAs (IsCommMonObj A.X)) t x y

/-- Every set-theoretic fibre over `Spec k` is the entire underlying space. -/
theorem fibre_eq_univ (s : Spec (.of k)) :
    A.X.hom.base ⁻¹' {s} = Set.univ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact Subsingleton.elim _ _

/-- The genuine source abelian-scheme property bundle follows from PkgI2's three properties. -/
theorem abelianSchemePropertyBundle : AbelianSchemePropertyBundle k A.X.hom := by
  haveI := PkgI2.IsAbelianVariety.geomIntegral (A := A)
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  refine ⟨PkgI2.IsAbelianVariety.smooth, PkgI2.IsAbelianVariety.proper, ?_, ⟨relativeLaw A⟩⟩
  intro s
  rw [fibre_eq_univ]
  exact isConnected_univ

/-- The source's smooth-relative-dimension hypothesis follows from the *exact* Krull dimension
in TailQ1257, with no replacement dimension or extra connectedness assumption. -/
theorem smoothOfRelativeDimension (g : ℕ)
    (hg : topologicalKrullDim A.X.left = (g : WithBot ℕ∞)) :
    SmoothOfRelativeDimension g A.X.hom := by
  haveI := PkgI2.IsAbelianVariety.smooth (A := A)
  apply RelativeGroupLaw.smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq
    (relativeLaw A) g
  intro s
  rw [fibre_eq_univ]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (Homeomorph.Set.univ A.X.left).isHomeomorph).trans hg

/-- `Spec k` over itself has the identity structure morphism. -/
theorem specOver_self_hom : (PkgI2.specOver k k).hom = 𝟙 (Spec (.of k)) := by
  simp [PkgI2.specOver]

/-- Original rational points, with their structure equation, are exactly the source points. -/
def pointEquiv : PkgI2.Pts A k ≃ SchemeHomOver (𝟙 (Spec (.of k))) A.X.hom where
  toFun p := ⟨p.left, (Over.w p).trans (specOver_self_hom (k := k))⟩
  invFun p := Over.homMk p.1 (p.2.trans (specOver_self_hom (k := k)).symm)
  left_inv p := Over.OverMorphism.ext rfl
  right_inv p := Subtype.ext rfl

/-- The source law is precisely the original multiplication after the point comparison. -/
theorem pointEquiv_mul (x y : PkgI2.Pts A k) :
    pointEquiv A (x * y) = (relativeLaw A).mul (𝟙 _) (pointEquiv A x) (pointEquiv A y) := by
  have hs : PkgI2.specOver k k = Over.mk (𝟙 (Spec (.of k))) := by
    exact congrArg Over.mk (specOver_self_hom (k := k))
  change (⟨(x * y).left, _⟩ : SchemeHomOver (𝟙 _) A.X.hom) = _
  apply Subtype.ext
  cases hs
  rfl

/-- The source identity is the original multiplicative identity. -/
theorem pointEquiv_one :
    pointEquiv A (1 : PkgI2.Pts A k) = (relativeLaw A).one (𝟙 _) := by
  have hs : PkgI2.specOver k k = Over.mk (𝟙 (Spec (.of k))) :=
    congrArg Over.mk (specOver_self_hom (k := k))
  apply Subtype.ext
  cases hs
  rfl

/-- Natural multiplication on source points agrees with the original power operation. -/
theorem pointEquiv_pow (n : ℕ) (x : PkgI2.Pts A k) :
    pointEquiv A (x ^ n) = (relativeLaw A).nsmul (𝟙 _) n (pointEquiv A x) := by
  induction n with
  | zero => simpa only [pow_zero, RelativeGroupLaw.nsmul_zero] using pointEquiv_one A
  | succ n ih =>
    rw [pow_succ', pointEquiv_mul, ih, RelativeGroupLaw.nsmul_succ]

/-- Torsion points of PkgI2 and of the genuine relative law are equivalent. -/
def torsionEquivRelative (n : ℕ) :
    PkgI2.torsion A k n ≃
      {x : SchemeHomOver (𝟙 (Spec (.of k))) A.X.hom //
        (relativeLaw A).IsTorsionPoint (𝟙 _) n x} :=
  Equiv.subtypeEquiv (pointEquiv A) fun x => by
    change x ^ n = 1 ↔ (relativeLaw A).nsmul (𝟙 _) n (pointEquiv A x) =
      (relativeLaw A).one (𝟙 _)
    rw [← pointEquiv_pow, ← pointEquiv_one, (pointEquiv A).injective.eq_iff]

end ZInQ.Contrib.CloudB3W16Torsion
