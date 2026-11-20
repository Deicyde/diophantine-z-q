import ZInQKernel.Contrib.OneProof.RC.PMWire.Generic
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspAssignment
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelJacobian

/-! The rational image of infinity is the geometric cusp in the orbit
selected by the Atkin–Lehner matrix. Tex 2943–2946, 8282–8285.
Matrix and limit comparison are on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve PkgI3 UpperHalfPlane Matrix
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology TauCeti.ExactDivisor

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace ZInQ.Manuscript.RC.PMWire

open J0Cusps
open AtkinPin (atkinGL)

private theorem atkin_dilate {N Q : ℕ} [NeZero N] [NeZero Q] (hQ : Q ∥ N) :
    ∃ σ : SL(2, ℤ), ∀ τ : ℍ, atkinGL hQ • τ = σ • X0Model.dilate Q τ := by
  let M := N / Q
  have hm : N = Q * M := (Nat.mul_div_cancel' hQ.dvd).symm
  obtain ⟨a, b, c, d, h, hd⟩ :=
    (TauCeti.isAtkinLehnerMatrix_atkinLehnerMatrix hQ).exists_entries hQ.pos.ne' hm
  let g : SL(2, ℤ) := ⟨!![a, b; (M : ℤ) * c, (Q : ℤ) * d], by
    rw [Matrix.det_fin_two_of]
    linear_combination hd⟩
  refine ⟨g, fun τ => ?_⟩
  have ha : ((atkinGL hQ • τ : ℍ) : ℂ) =
      ((Q : ℂ) * a * τ + b) / ((Q : ℂ) * M * c * τ + (Q : ℂ) * d) := by
    unfold atkinGL
    rw [coe_smul_of_det_pos (TauCeti.val_det_atkinLehnerGL_pos hQ.pos _)]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, TauCeti.coe_atkinLehnerGL, Matrix.map_apply, h]
    change (((((Q : ℤ) * a : ℤ) : ℝ) : ℂ) * τ + ((b : ℝ) : ℂ)) /
      (((((Q : ℤ) * (M : ℤ) * c : ℤ) : ℝ) : ℂ) * τ + ((((Q : ℤ) * d : ℤ) : ℝ) : ℂ)) = _
    push_cast
    rfl
  apply UpperHalfPlane.ext
  rw [ha, coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast]
  change _ = (((a : ℂ) * ((Q : ℂ) * τ) + b) /
    ((((M : ℤ) * c : ℤ) : ℂ) * ((Q : ℂ) * τ) + (((Q : ℤ) * d : ℤ) : ℂ)))
  push_cast
  congr 1 <;> ring

private theorem tendsto_dilate (Q : ℕ) [NeZero Q] :
    Tendsto (X0Model.dilate Q) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  refine tendsto_atTop.mpr fun b => ?_
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  exact (atImInfty_mem _).mpr ⟨b / Q, fun τ hτ => by
    change b ≤ (((Q : ℂ) * (τ : ℂ))).im
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    rw [mul_comm, ← div_le_iff₀ hQ]
    exact hτ⟩

/-- The moved rational cusp is one of the actual geometric cusp points;
no rationality is asserted for the other cusp orbits. -/
def MovingCusps (N : ℕ) [NeZero N] : Prop :=
  ∀ q : ℕ, q.Prime → 0 < N.factorization q → ∃ r : OnePoint ℚ,
    algebraicCusp N (ElkikPrint.cuspOrbit N r) =
      rationalAsGeometric (X := source N) ((infinity N ≫ rationalW N q).left)

/-- The pin follows by transporting the width-one limit along the rational
involution and, on the chart, comparing with a determinant-one translate
of a positive dilation. Extend to ℂ for the limit and descend by faithfulness. -/
theorem movingCusps (N : ℕ) [NeZero N] : MovingCusps N := by
  intro q _ _
  let Q := q ^ N.factorization q
  let hQ : Q ∥ N := TauCeti.Nat.isExactDivisor_primePow (N := N) (p := q)
  letI : NeZero Q := ⟨hQ.pos.ne'⟩
  obtain ⟨σ, hσ⟩ := atkin_dilate hQ
  refine ⟨mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ), ?_⟩
  let W : source N ⟶ source N := rationalW N q
  let p : AbVar.ptObj (K := ℚ) ℂ ⟶ source N :=
    extendPoint (rationalAsGeometric (X := source N) (X0Model.cusp N))
  let w : AbVar.ptObj (K := ℚ) ℂ ⟶ source N :=
    extendPoint (rationalAsGeometric (X := source N) ((infinity N ≫ W).left))
  have hp : p = branchComplex N (Rat.castHom ℂ) (modularFunctionField N).subtype := by
    exact (congrArg (extendPoint (X := source N)) (algebraicCusp_infinity_rational N).symm).trans
      (algebraicCusp_infinity N)
  have hw : w = p ≫ W := by
    apply Over.OverMorphism.ext
    let a := Spec.map (CommRingCat.ofHom qbarToComplex)
    let b := Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
    change a ≫ b ≫ (infinity N).left ≫ W.left = (a ≫ b ≫ (infinity N).left) ≫ W.left
    simp only [Category.assoc]
  have hchart (τ : ℍ) : interior N τ ≫ W = interior N (σ • X0Model.dilate Q τ) := by
    apply Over.OverMorphism.ext
    rw [← hσ]
    exact congrArg Subtype.val ((AtkinRational.rationalAtkin hQ).chart τ)
  have hlim : Tendsto (fun τ : ℍ => complexLift (interior N τ)) atImInfty
      (𝓝 (complexLift p)) := by
    rw [hp]
    exact tendsto_infinity N
  have hmap := (Point.continuous_map (complexBaseChange.map W)).continuousAt.tendsto.comp hlim
  have hlimit : Tendsto (fun τ : ℍ => complexLift (interior N (σ • X0Model.dilate Q τ)))
      atImInfty (𝓝 (complexLift w)) := by
    rw [hw, complexLift_comp]
    exact hmap.congr fun τ => by rw [Function.comp_apply, ← complexLift_comp, hchart]
  have hσlim := (algebraicCusp_limit N σ).comp (tendsto_dilate Q)
  letI : IsProper (source N).hom := X0Model.proper N
  apply extendPoint_injective (source N)
  exact source_limit_unique N hσlim hlimit


end ZInQ.Manuscript.RC.PMWire
