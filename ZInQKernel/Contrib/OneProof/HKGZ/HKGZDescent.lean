import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisDescent
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
import ZInQKernel.Contrib.OneProof.HKGZ.HKGZPrints

/-! # Rational point descent after the conjugation comparison -/

namespace ZInQ.Manuscript.HKGZ

open NumberField WeierstrassCurve

open Classical in
/-- A non-torsion point fixed modulo torsion by the nontrivial automorphism of a quadratic
field gives a non-torsion rational point. Kill the difference by a positive multiple and
use point descent for the resulting fixed point. -/
theorem exists_rational_of_conjugate_sub_torsion
    (E : WeierstrassCurve ℚ) (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {σ : K ≃ₐ[ℚ] K} (hσ : σ ≠ 1)
    (P : (E.baseChange K).toAffine.Point) (hP : ¬ IsOfFinAddOrder P)
    (hfix : IsOfFinAddOrder (Affine.Point.map (W' := E.toAffine) σ.toAlgHom P - P)) :
    ∃ Q : E.toAffine.Point, ¬ IsOfFinAddOrder Q := by
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  obtain ⟨m, hm, hmul⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hfix
  have hfixed : Affine.Point.map (W' := E.toAffine) σ.toAlgHom (m • P) = m • P := by
    rw [map_nsmul]
    rw [nsmul_sub, sub_eq_zero] at hmul
    exact hmul
  obtain ⟨Q, hQ⟩ := Affine.Point.exists_baseChange_eq_of_map_eq K hσ hfixed
  let e := Affine.Point.equivBaseChangeSelf E.toAffine
  refine ⟨e.symm Q, fun ht => hP ?_⟩
  obtain ⟨n, hn, hnt⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
  have hQt : n • Q = 0 := by
    simpa only [map_nsmul, e.apply_symm_apply, map_zero] using congrArg e hnt
  have hnP : n • (m • P) = 0 := by
    rw [← hQ, ← map_nsmul, hQt, map_zero]
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨n * m, Nat.mul_pos hn hm, by simpa only [smul_smul] using hnP⟩

end ZInQ.Manuscript.HKGZ
