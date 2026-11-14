import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.CanonicalDegree
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.Dim.Basic

set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace DimJacGlue

variable {X : Scheme.{0}} [IsIntegral X] (g : X ⟶ Spec (CommRingCat.of ℚ))
  {F : Type} [Field F] [Algebra ℚ F] (e : X.functionField ≃+* F)

lemma generic_mem (U : X.Opens) (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- `Γ(X, U) → F`, the germ at the generic point followed by `e`. -/
def ψ (U : X.Opens) (hU : (U : Set X).Nonempty) : Γ(X, U) →+* F :=
  e.toRingHom.comp (X.presheaf.germ U (genericPoint X) (generic_mem U hU)).hom

/-- `Φ_U : Γ(Ω, U) → Ω_{F/ℚ}` for an affine nonempty open `U`. -/
def Φ (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    Γ(g.relativeDifferentials, U) →+ Ω[F⁄ℚ] :=
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
  haveI : IsScalarTower ℚ Γ(X, U) F := IsScalarTower.of_algebraMap_eq (fun q =>
    congrArg (· q) (RingHom.ext_rat (algebraMap ℚ F) ((ψ e U hne).comp (g.specStructureMap U).hom)))
  (KaehlerDifferential.map ℚ ℚ Γ(X, U) F).toAddMonoidHom.comp
    (g.kaehlerSectionsEquiv U rfl hU).symm.toLinearMap.toAddMonoidHom


variable {g e}

lemma kse_smul_D (U : X.Opens) (hU : IsAffineOpen U) (a b : Γ(X, U)) :
    letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
    g.kaehlerSectionsEquiv U rfl hU (a • KaehlerDifferential.D ℚ Γ(X, U) b) = a • g.sectionsD U b := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  rw [LinearEquiv.map_smul, Scheme.Hom.kaehlerSectionsEquiv_D]

/-- Induction principle for sections of `Ω¹` over an affine open. -/
lemma induction_affine (U : X.Opens) (hU : IsAffineOpen U) (P : Γ(g.relativeDifferentials, U) → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ a b : Γ(X, U), P (a • g.sectionsD U b)) (s : Γ(g.relativeDifferentials, U)) : P s := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  obtain ⟨η, rfl⟩ := (g.kaehlerSectionsEquiv U rfl hU).surjective s
  suffices H : ∀ c : Γ(X, U), P (g.kaehlerSectionsEquiv U rfl hU (c • η)) by simpa using H 1
  have hη : η ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D ℚ Γ(X, U))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hη using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    intro c; rw [kse_smul_D]; exact hgen c b
  | zero => intro c; simpa using h0
  | add x y _ _ hx hy => intro c; rw [smul_add, map_add]; exact hadd _ _ (hx c) (hy c)
  | smul a x _ hx => intro c; rw [smul_smul]; exact hx _

lemma Φ_smul_D (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) (a b : Γ(X, U)) :
    Φ g e U hU hne (a • g.sectionsD U b) = ψ e U hne a • KaehlerDifferential.D ℚ F (ψ e U hne b) := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
  haveI : IsScalarTower ℚ Γ(X, U) F := IsScalarTower.of_algebraMap_eq (fun q =>
    congrArg (· q) (RingHom.ext_rat (algebraMap ℚ F) ((ψ e U hne).comp (g.specStructureMap U).hom)))
  have := kse_smul_D (g := g) U hU a b
  simp only [Φ, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
    LinearEquiv.coe_coe]
  rw [← this, LinearEquiv.symm_apply_apply, LinearMap.map_smul, KaehlerDifferential.map_D]
  rfl

lemma Φ_smul (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) (a : Γ(X, U))
    (s : Γ(g.relativeDifferentials, U)) :
    Φ g e U hU hne (a • s) = ψ e U hne a • Φ g e U hU hne s := by
  induction s using induction_affine U hU with
  | h0 => simp
  | hadd x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | hgen c b => rw [smul_smul, Φ_smul_D, Φ_smul_D, map_mul, mul_smul]

end DimJacGlue
