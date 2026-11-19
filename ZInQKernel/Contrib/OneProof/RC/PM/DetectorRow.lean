import ZInQKernel.Contrib.OneProof.RC.PM.Stage
import ZInQKernel.Contrib.OneProof.RC.Stages.Kummer

/-! Use the detector's existing finite row in the supersingular stage (tex 8452–8456).
The comparison of torsion at the chosen good-reduction place is an input. -/

noncomputable section

open scoped WeierstrassCurve

namespace ZInQ.Manuscript.RC.PM.Evaluation

open Stages TauCeti PrintsArith

variable {ell : ℕ} [Fact ell.Prime] {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
variable {Ebar : WeierstrassCurve (ZMod ell)} {A : WeierstrassCurve ℚ} [A.IsElliptic] {M : ℕ}

/-- Transport the existing finite row from the Tate tower by the supplied specialization
of the prime-to-`ell` torsion. `hfrob` is the invariance of that row after specialization
(tex 8453–8456). -/
def ofTateRow (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2]) (hell : ell ≠ 2)
    (htriv : ∀ t : (Ebar⁄K).toAffine.Point, (2 ^ M : ℕ) • t = 0 →
      curveFrob (K := K) Ebar (curveFrob (K := K) Ebar t) = t)
    (spec : TateModuleLevel 2 (GeomPoint A) M ≃+
      AddSubgroup.torsionBy (Ebar⁄K).toAffine.Point (2 ^ M : ℕ))
    (hfrob : ∀ t, finiteRow b M (spec.symm (torsionFrob (curveFrob (K := K) Ebar) (2 ^ M) t)) =
      finiteRow b M (spec.symm t)) : Evaluation K Ebar M where
  ell_ne_two := hell
  square_trivial := htriv
  row := (finiteRow b M).comp spec.symm.toAddMonoidHom
  row_fixed := hfrob

/-- On-the-spot (c) normalization check: evaluating the transported row on a
specialized Tate vector gives the original row modulo `2^M`. -/
theorem ofTateRow_row_proj (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2]) (hell : ell ≠ 2)
    (htriv : ∀ t : (Ebar⁄K).toAffine.Point, (2 ^ M : ℕ) • t = 0 →
      curveFrob (K := K) Ebar (curveFrob (K := K) Ebar t) = t)
    (spec : TateModuleLevel 2 (GeomPoint A) M ≃+
      AddSubgroup.torsionBy (Ebar⁄K).toAffine.Point (2 ^ M : ℕ))
    (hfrob : ∀ t, finiteRow b M (spec.symm (torsionFrob (curveFrob (K := K) Ebar) (2 ^ M) t)) =
      finiteRow b M (spec.symm t)) (t : TateMod A 2) :
    (ofTateRow b hell htriv spec hfrob).row (spec (TateModule.proj M t)) =
      PadicInt.toZModPow M (b t) := by
  simpa only [ofTateRow, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply] using finiteRow_proj b M t

#print axioms ofTateRow
#print axioms ofTateRow_row_proj

end ZInQ.Manuscript.RC.PM.Evaluation
