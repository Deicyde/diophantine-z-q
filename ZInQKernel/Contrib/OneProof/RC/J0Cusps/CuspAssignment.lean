import ZInQKernel.Contrib.OneProof.RC.J0Cusps.TranslatedBranches
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.LimitUniqueness
import ZInQKernel.Contrib.OneProof.RC.X0Model2.ChartReparam

/-! The algebraic cusp assigned to each orbit (tex 1785–1787, 2937–2939).
The specialization and descent from labels are on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve PkgI3 UpperHalfPlane
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

namespace ZInQ.Manuscript.RC.J0Cusps

abbrev cuspIndex (N : ℕ) :=
  CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))

def orbitOfSL (N : ℕ) [NeZero N] (σ : SL(2, ℤ)) : cuspIndex N :=
  ElkikPrint.cuspOrbit N (mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ))

theorem orbitOfSL_surjective (N : ℕ) [NeZero N] : Function.Surjective (orbitOfSL N) := by
  rintro ⟨c, (hc : IsCusp c _)⟩
  obtain ⟨r, hr⟩ := isCusp_SL2Z_iff.mp ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)
  obtain ⟨g, hg⟩ := r.exists_mem_SL2 ℤ
  refine ⟨g, ?_⟩
  rw [orbitOfSL, hg]
  unfold ElkikPrint.cuspOrbit
  congr 1
  exact Subtype.ext hr

theorem orbitOfSL_eq (N : ℕ) [NeZero N] (σ : SL(2, ℤ)) :
    orbitOfSL N σ = ElkikPrint.cuspOrbit N (mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ)) := rfl

private theorem rat_label_real (g : SL(2, ℤ)) :
    OnePoint.map Rat.cast (mapGL ℚ g • (OnePoint.infty : OnePoint ℚ)) =
      mapGL ℝ g • (OnePoint.infty : OnePoint ℝ) := by
  rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
    ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_mapGL]

private theorem translated_limit_congr (N : ℕ) [NeZero N] {σ τ : SL(2, ℤ)}
    (h : orbitOfSL N σ = orbitOfSL N τ)
    {p : AbVar.ptObj (K := ℚ) ℂ ⟶ source N}
    (hp : Tendsto (fun z : ℍ => complexLift (interior N (σ • z))) atImInfty
      (𝓝 (complexLift p))) :
    Tendsto (fun z : ℍ => complexLift (interior N (τ • z))) atImInfty
      (𝓝 (complexLift p)) := by
  unfold orbitOfSL ElkikPrint.cuspOrbit at h
  obtain ⟨d, hd⟩ := Quotient.exact h
  have hd' := congrArg Subtype.val hd
  change d.1 • OnePoint.map (Rat.cast : ℚ → ℝ) (mapGL ℚ τ • (OnePoint.infty : OnePoint ℚ)) =
    OnePoint.map (Rat.cast : ℚ → ℝ) (mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ)) at hd'
  obtain ⟨g, hg, hmap⟩ := d.property
  rw [rat_label_real, rat_label_real, ← hmap] at hd'
  let ν := σ⁻¹ * g * τ
  have hν : mapGL ℝ ν • (OnePoint.infty : OnePoint ℝ) = OnePoint.infty := by
    simp only [ν, map_mul, map_inv, mul_smul, hd', inv_smul_smul]
  have hv : Tendsto (fun z : ℍ => ν • z) atImInfty atImInfty := by
    exact tendsto_smul_atImInfty (OnePoint.smul_infty_eq_self_iff.mp hν)
  refine (hp.comp hv).congr fun z => ?_
  have hgroup : σ * ν = g * τ := by simp [ν, ← mul_assoc]
  change complexLift (interior N (σ • (ν • z))) = complexLift (interior N (τ • z))
  rw [← mul_smul, hgroup, mul_smul]
  congr 1
  apply Over.OverMorphism.ext
  exact X0Model2.complexPoint_smul N g hg (τ • z)

/-- The point over an algebraic closure corresponding to a cusp orbit. Its
complex extension is the limit of every integral modular translate in the orbit. -/
def algebraicCusp (N : ℕ) [NeZero N] (c : cuspIndex N) :
    AbVar.ptObj (K := ℚ) Qbar ⟶ source N :=
  let σ := (orbitOfSL_surjective N c).choose
  let e := (exists_algebraic_cusp_limit N σ).choose
  Over.homMk (branchPoint N e) (maps_to_rat_unique _ _)

/-- Extension of the coordinates of a geometric point to the complex numbers. -/
def extendPoint {X : Over (Spec (.of ℚ))} (p : AbVar.ptObj (K := ℚ) Qbar ⟶ X) :
    AbVar.ptObj (K := ℚ) ℂ ⟶ X :=
  Over.homMk (Spec.map (CommRingCat.ofHom qbarToComplex) ≫ p.left) (maps_to_rat_unique _ _)

/-- Extension to complex coordinates is faithful for separated schemes. -/
theorem extendPoint_injective (X : Over (Spec (.of ℚ))) [IsSeparated X.hom] :
    Function.Injective (extendPoint (X := X)) := by
  intro p q h
  let i := Spec.map (CommRingCat.ofHom qbarToComplex)
  have hi : IsDominant i := ⟨by
    intro y
    let z := IsLocalRing.closedPoint ℂ
    rw [Subsingleton.elim y (i z)]
    exact subset_closure (Set.mem_range_self z)⟩
  have hred : IsReduced (AbVar.ptObj (K := ℚ) Qbar).left :=
    inferInstanceAs (IsReduced (Spec (.of Qbar)))
  apply Over.OverMorphism.ext
  exact @ext_of_isDominant_of_isSeparated _ _ _ _ hred _ _ X.hom inferInstance
    (by simp) i hi (congrArg CommaMorphism.left h)

/-- Regard a rational point as a point with coordinates in the algebraic closure. -/
def rationalAsGeometric {X : Over (Spec (.of ℚ))} (p : Spec (.of ℚ) ⟶ X.left) :
    AbVar.ptObj (K := ℚ) Qbar ⟶ X :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)) ≫ p)
    (maps_to_rat_unique _ _)

private theorem extend_rationalAsGeometric {X : Over (Spec (.of ℚ))}
    (p : Spec (.of ℚ) ⟶ X.left) :
    (extendPoint (rationalAsGeometric p)).left =
      Spec.map (CommRingCat.ofHom (Rat.castHom ℂ)) ≫ p := by
  change Spec.map (CommRingCat.ofHom qbarToComplex) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)) ≫ p = _
  have hh : CommRingCat.ofHom (algebraMap ℚ Qbar) ≫ CommRingCat.ofHom qbarToComplex =
      CommRingCat.ofHom (Rat.castHom ℂ) :=
    CommRingCat.hom_ext (Subsingleton.elim _ _)
  rw [← Category.assoc, ← Spec.map_comp, hh]

theorem algebraicCusp_limit (N : ℕ) [NeZero N] (σ : SL(2, ℤ)) :
    Tendsto (fun z : ℍ => complexLift (interior N (σ • z))) atImInfty
      (𝓝 (complexLift (extendPoint (algebraicCusp N (orbitOfSL N σ))))) := by
  let c := orbitOfSL N σ
  let ρ := (orbitOfSL_surjective N c).choose
  have hρ : orbitOfSL N ρ = orbitOfSL N σ := (orbitOfSL_surjective N c).choose_spec
  exact translated_limit_congr N hρ (exists_algebraic_cusp_limit N ρ).choose_spec

theorem algebraicCusp_zero (N : ℕ) [NeZero N] :
    extendPoint (algebraicCusp N (ElkikPrint.cuspOrbit N ((0 : ℚ) : OnePoint ℚ))) =
      branchComplex N (Rat.castHom ℂ) (zeroField N) := by
  have hS : mapGL ℚ ModularGroup.S • (OnePoint.infty : OnePoint ℚ) = (0 : ℚ) := by
    rw [OnePoint.smul_infty_eq_ite]
    change (if (1 : ℚ) = 0 then OnePoint.infty else ((0 / 1 : ℚ) : OnePoint ℚ)) = _
    simp
  have h := algebraicCusp_limit N ModularGroup.S
  rw [orbitOfSL_eq, hS] at h
  exact source_limit_unique N h (tendsto_zero N)

theorem algebraicCusp_infinity (N : ℕ) [NeZero N] :
    extendPoint (algebraicCusp N (ElkikPrint.cuspOrbit N OnePoint.infty)) =
      branchComplex N (Rat.castHom ℂ) (modularFunctionField N).subtype := by
  have h := algebraicCusp_limit N (1 : SL(2, ℤ))
  simp only [orbitOfSL_eq, map_one, one_smul] at h
  exact source_limit_unique N h (tendsto_infinity N)

/-- The geometric assignment at zero is defined over the rationals. -/
theorem algebraicCusp_zero_rational (N : ℕ) [NeZero N] :
    algebraicCusp N (ElkikPrint.cuspOrbit N ((0 : ℚ) : OnePoint ℚ)) =
      rationalAsGeometric (zeroPoint N) := by
  let : IsProper (source N).hom := X0Model.proper N
  apply extendPoint_injective (source N)
  rw [algebraicCusp_zero]
  exact Over.OverMorphism.ext (extend_rationalAsGeometric (X := source N) (zeroPoint N)).symm

/-- The geometric assignment at infinity is the rational base point. -/
theorem algebraicCusp_infinity_rational (N : ℕ) [NeZero N] :
    algebraicCusp N (ElkikPrint.cuspOrbit N OnePoint.infty) =
      rationalAsGeometric (X0Model.cusp N) := by
  let : IsProper (source N).hom := X0Model.proper N
  apply extendPoint_injective (source N)
  rw [algebraicCusp_infinity]
  exact Over.OverMorphism.ext (extend_rationalAsGeometric (X := source N) (X0Model.cusp N)).symm

/-- The source hypothesis of the weighted comparison is discharged for the
complex extension of the geometric cusp assignment. -/
theorem cuspAssignment_zero_limit (N : ℕ) [NeZero N] :
    Tendsto (fun τ : ℍ => complexLift (interior N (ModularGroup.S • τ))) atImInfty
      (𝓝 (complexLift (extendPoint
        (algebraicCusp N (ElkikPrint.cuspOrbit N ((0 : ℚ) : OnePoint ℚ)))))) := by
  rw [algebraicCusp_zero]
  exact tendsto_zero N


end ZInQ.Manuscript.RC.J0Cusps
