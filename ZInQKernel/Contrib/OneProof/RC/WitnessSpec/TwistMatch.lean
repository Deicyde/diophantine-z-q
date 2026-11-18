import ZInQKernel.Contrib.OneProof.RC.Stages.SplitTwist
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Twist

/-! The twist map used for the rational witness and the twist map on geometric
torsion use the same specified root (tex 8340–8343, 8392–8394). -/

noncomputable section

open WeierstrassCurve ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped WeierstrassCurve Classical

namespace ZInQ.Manuscript.RC.WitnessSpec

/-- The geometric point of a rational point. -/
def rationalGeomPoint (A : WeierstrassCurve ℚ) :
    A.toAffine.Point →+ GeomPoint A :=
  (Affine.Point.map (W' := A) (Algebra.ofId ℚ Qbar)).comp
    (Affine.Point.equivBaseChangeSelf A.toAffine).toAddMonoidHom

/-- The rational point supplies the fixed-point input of the division cocycle. -/
theorem rationalGeomPoint_fixed (A : WeierstrassCurve ℚ) (R : A.toAffine.Point) (g : GalQ) :
    Affine.Point.map (W' := A) g.toAlgHom (rationalGeomPoint A R) = rationalGeomPoint A R := by
  have h : g.toAlgHom.comp (Algebra.ofId ℚ Qbar) = Algebra.ofId ℚ Qbar := by
    ext
  simp only [rationalGeomPoint, AddMonoidHom.comp_apply, Affine.Point.map_map, h]

/-- Extending the ring-class twist embedding to the algebraic closure gives
exactly the geometric twist map, with no change of root. -/
theorem map_twistEmb_eq_geomTwist {H : Type*} [Field H] [Algebra ℚ H]
    (e : H →ₐ[ℚ] Qbar) (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    (D : ℚ) {s : H} (hs : s ≠ 0) (hD : s ^ 2 = algebraMap ℚ H D)
    (R : (qtwist E D).toAffine.Point) :
    let hs' : e s ≠ 0 := fun h => hs (e.injective (h.trans (map_zero e).symm))
    let hD' : (e s) ^ 2 = algebraMap ℚ Qbar D := by
      rw [← map_pow, hD, e.commutes]
    Affine.Point.map (W' := E) e (twistEmb E D s (twistVC_smul E h₁ h₃ hs hD) R) =
      geomTwist E h₁ h₃ D (e s) hs' hD' (rationalGeomPoint (qtwist E D) R) := by
  dsimp only
  let hs' : e s ≠ 0 := fun h => hs (e.injective (h.trans (map_zero e).symm))
  let hD' : (e s) ^ 2 = algebraMap ℚ Qbar D := by rw [← map_pow, hD, e.commutes]
  change Affine.Point.map (W' := E) e (twistEmb E D s (twistVC_smul E h₁ h₃ hs hD) R) =
    twistEmb E D (e s) (twistVC_smul E h₁ h₃ hs' hD') R
  rcases R with _ | ⟨x, y, hxy⟩
  · simp only [← Affine.Point.zero_def, map_zero]
  · obtain ⟨_, h₀⟩ := twistEmb_some E h₁ h₃ D hs hD hxy
    obtain ⟨_, h₁'⟩ := twistEmb_some E h₁ h₃ D hs' hD' hxy
    rw [h₀, h₁', Affine.Point.map_some]
    simp only [map_div₀, map_pow, e.commutes]

#print axioms rationalGeomPoint
#print axioms rationalGeomPoint_fixed
#print axioms map_twistEmb_eq_geomTwist

end ZInQ.Manuscript.RC.WitnessSpec
