import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Torsion
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.TwistMatch
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Witness

/-! The finite Kummer inputs at the selected place: compose the geometric
twist with reduction, and carry Frobenius and torsion through that map. -/

noncomputable section

open WeierstrassCurve TauCeti ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.ChebFD.C10 (GQ)
open scoped WeierstrassCurve Classical

namespace ZInQ.Manuscript.RC.WitnessSpec

private theorem torsionMap_equiv {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (n : ℕ) (e : X ≃+ Y) : Function.Bijective (torsionMap n e.toAddMonoidHom) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)
  · intro t
    exact ⟨torsionMap n e.symm.toAddMonoidHom t, Subtype.ext (e.apply_symm_apply t.val)⟩

namespace FrobeniusPlace

variable {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)
variable (C : WeierstrassCurve ℤ) [(C⁄ℚ).IsElliptic] (hg : ¬ (p : ℤ) ∣ C.Δ)

local notation "wₚ" => (ValuationSubring.valuation (valuationRing v))
local notation "kₚ" => (IsLocalRing.ResidueField (Valuation.valuationSubring wₚ))
local notation "B" => (WeierstrassCurve.map C (Int.castRingHom (ZMod p)))
local notation "E" => (WeierstrassCurve.baseChange C ℚ)

omit [(C⁄ℚ).IsElliptic] in
private theorem reduced_elliptic (hg : ¬ (p : ℤ) ∣ C.Δ) : (B⁄kₚ).IsElliptic := by
  rw [← integralEquation_residue wₚ C p]
  let := integralEquation_elliptic wₚ C p hg
  infer_instance

private theorem two_ne_zero_residue (hodd : p ≠ 2) : (2 : kₚ) ≠ 0 := by
  change ((2 : ℕ) : kₚ) ≠ 0
  rw [ne_eq, CharP.cast_eq_zero_iff kₚ p]
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).not.mpr hodd

/-- Construct the local stage from the actual place and the exact split twist.
The squared global action on level torsion is the input supplied by the stages. -/
def localStage (hodd : p ≠ 2) (M : ℕ)
    (h₁ : (WeierstrassCurve.a₁ E) = 0) (h₃ : (WeierstrassCurve.a₃ E) = 0) (D : ℚ) (s : Qbar)
    (hs : s ≠ 0) (hsD : s ^ 2 = algebraMap ℚ Qbar D) (hsf : g s = s)
    (hEsq : ∀ t : GeomPoint E, (2 ^ M : ℕ) • t = 0 →
      Affine.Point.map (W' := E) g.toAlgHom (Affine.Point.map (W' := E) g.toAlgHom t) = t) :
    LocalStage (qtwist E D) M g := by
  let t := geomTwist E h₁ h₃ D s hs hsD
  let r := v.curveReduction C hg
  let n := 2 ^ M
  have heq (P : GeomPoint (qtwist E D)) :
      t (Affine.Point.map (W' := qtwist E D) g.toAlgHom P) =
        Affine.Point.map (W' := E) g.toAlgHom (t P) :=
    geomTwist_equivariant E h₁ h₃ D s hs hsD g hsf P
  refine ⟨(B⁄kₚ).toAffine.Point, inferInstance, r.comp t.toAddMonoidHom,
    curveFrob (K := kₚ) B, ?_, ?_, ?_, ?_⟩
  · intro P
    change r (t (Affine.Point.map (W' := qtwist E D) g.toAlgHom P)) = curveFrob B (r (t P))
    rw [heq]
    exact v.curveReduction_frobenius C hg (t P)
  · intro P hP
    apply t.injective
    rw [heq, heq]
    apply hEsq
    rw [← map_nsmul t, hP, map_zero]
  · have h := (v.curveReduction_torsion_bijective C hg hodd M).comp (torsionMap_equiv n t)
    exact h
  · let := v.reduced_elliptic C hg
    apply (B⁄kₚ).toAffine.nsmul_surjective
    push_cast
    exact pow_ne_zero M (v.two_ne_zero_residue hodd)

/-- The reduction in the constructed stage is reduction of the untwisted point
at the exact place. -/
theorem localStage_red (hodd : p ≠ 2) (M : ℕ)
    (h₁ : (WeierstrassCurve.a₁ E) = 0) (h₃ : (WeierstrassCurve.a₃ E) = 0) (D : ℚ) (s : Qbar)
    (hs : s ≠ 0) (hsD : s ^ 2 = algebraMap ℚ Qbar D) (hsf : g s = s) (hEsq)
    (P : GeomPoint (qtwist E D)) :
    (v.localStage C hg hodd M h₁ h₃ D s hs hsD hsf hEsq).red P =
      v.curveReduction C hg (geomTwist E h₁ h₃ D s hs hsD P) := rfl

#print axioms torsionMap_equiv
#print axioms reduced_elliptic
#print axioms two_ne_zero_residue
#print axioms localStage
#print axioms localStage_red

end FrobeniusPlace
end ZInQ.Manuscript.RC.WitnessSpec
