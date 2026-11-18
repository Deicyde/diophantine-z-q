import WeightTwoQuadraticConstants02
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitivePeterssonSlashTransport
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# The genuine weight-two coset-profile constraint

The actual modular-form trace to level one vanishes in weight two. Taking
limits of its finite sum of genuine translates proves the constant-profile
constraint on the complete principal coset quotient. Local q-differentials
are identified by pullback to the original holomorphic function; their
circle residues are computed by the actual Cauchy coefficient formula.
The coset quotient still records stabilizer repetitions.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex Filter Matrix Matrix.SpecialLinearGroup ModularForm
open UpperHalfPlane hiding I
open scoped Topology Real ModularForm MatrixGroups Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants

open ZInQ.Contrib.HeckePrimeRationality

abbrev principalLevel (N : ℕ) := (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The complete finite principal coset quotient used by the actual trace. -/
abbrev principalCosets (N : ℕ) := 𝒮ℒ ⧸ (principalLevel N).subgroupOf 𝒮ℒ

/-- A genuine same-level translate; the reused normality lemma has no weight hypothesis. -/
def principalMFSlash (N : ℕ) (k : ℤ) (f : ModularForm (principalLevel N) k) (γ : SL(2, ℤ)) :
    ModularForm (principalLevel N) k :=
  ModularForm.restrict (PrimitivePetersson.principal_translate_level N γ)
    (ModularForm.translate f (mapGL ℝ γ))

lemma principalMFSlash_coe (N : ℕ) (k : ℤ) (f : ModularForm (principalLevel N) k) (γ : SL(2, ℤ)) :
    (principalMFSlash N k f γ : ℍ → ℂ) = (f : ℍ → ℂ) ∣[k] γ := rfl

/-- The actual period-N constant on a quotient translate; the trace uses inverse representatives. -/
def cosetConstant (N : ℕ) (f : ModularForm (principalLevel N) 2) (q : principalCosets N) : ℂ :=
  (qExpansion (N : ℝ) (SlashInvariantForm.quotientFunc f q)).coeff 0

lemma quotientFunc_tendsto (N : ℕ) [NeZero N] (f : ModularForm (principalLevel N) 2)
    (q : principalCosets N) :
    Tendsto (SlashInvariantForm.quotientFunc f q) atImInfty (𝓝 (cosetConstant N f q)) := by
  refine Quotient.inductionOn q ?_
  intro r
  obtain ⟨γ, hγ⟩ := r.property
  have he : SlashInvariantForm.quotientFunc f (⟦r⟧ : principalCosets N) =
      (principalMFSlash N 2 f γ⁻¹ : ℍ → ℂ) := by
    rw [SlashInvariantForm.quotientFunc_mk, principalMFSlash_coe, ModularForm.SL_slash]
    rw [← hγ, map_inv]
    rfl
  rw [cosetConstant, he]
  exact ModularFormClass.tendsto_atImInfty (principalMFSlash N 2 f γ⁻¹)
    (by exact_mod_cast NeZero.pos N) (principalPeriod_mem N)

/-- This is the actual modular-form trace, not a trace-vanishing hypothesis. -/
theorem principal_trace_zero (N : ℕ) [NeZero N] (f : ModularForm (principalLevel N) 2) :
    ModularForm.trace 𝒮ℒ f = 0 := by
  exact (rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero) _

/-- Every actual weight-two modular form satisfies the complete finite coset constant constraint. -/
theorem principal_coset_constants_sum_zero (N : ℕ) [NeZero N]
    (f : ModularForm (principalLevel N) 2) :
    let _ : Fintype (principalCosets N) := Fintype.ofFinite _
    ∑ q : principalCosets N, cosetConstant N f q = 0 := by
  let : Fintype (principalCosets N) := Fintype.ofFinite _
  have h := tendsto_finsetSum Finset.univ (fun q _ => quotientFunc_tendsto N f q)
  have he : (fun τ : ℍ => ∑ q : principalCosets N, SlashInvariantForm.quotientFunc f q τ) =
      fun _ : ℍ => (0 : ℂ) := by
    funext τ
    have hz := congrArg (fun g : ModularForm 𝒮ℒ 2 => (g : ℍ → ℂ)) (principal_trace_zero N f)
    rw [ModularForm.coe_trace] at hz
    have hp := congrFun hz τ
    simpa only [Finset.sum_apply, FunLike.coe_zero, Pi.zero_apply] using hp
  rw [he] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The q-coordinate coefficient of the differential f(tau) d tau. -/
def localDifferential (N : ℕ) (f : ℍ → ℂ) (q : ℂ) : ℂ :=
  (N : ℂ) / thetaScale * (cuspFunction (N : ℝ) f q / q)

/-- The correctly normalized local residue coefficient. -/
def localResidue (N : ℕ) (f : ℍ → ℂ) : ℂ :=
  (N : ℂ) / thetaScale * (qExpansion (N : ℝ) f).coeff 0

lemma qParam_hasDerivAt (N : ℕ) (τ : ℂ) :
    HasDerivAt (Function.Periodic.qParam (N : ℝ))
      (Function.Periodic.qParam (N : ℝ) τ * (thetaScale / (N : ℂ))) τ := by
  unfold Function.Periodic.qParam
  simpa only [thetaScale, id_eq, mul_one, Complex.ofReal_natCast] using!
    ((((hasDerivAt_id τ).const_mul thetaScale).div_const (N : ℂ)).cexp)

/-- Pulling the q-differential back gives the actual original holomorphic differential coefficient. -/
theorem localDifferential_pullback (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (principalLevel N) k) (τ : ℍ) :
    localDifferential N f (Function.Periodic.qParam (N : ℝ) τ) *
      deriv (Function.Periodic.qParam (N : ℝ)) (τ : ℂ) = f τ := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hq := Function.Periodic.qParam_ne_zero (h := (N : ℝ)) (τ : ℂ)
  rw [localDifferential, SlashInvariantFormClass.eq_cuspFunction f τ (principalPeriod_mem N)
    (by exact_mod_cast NeZero.ne N), (qParam_hasDerivAt N τ).deriv]
  field_simp [hN, hq, thetaScale_ne_zero]

/-- The actual Cauchy contour gives the local residue; no nonintegrable default is used. -/
theorem circleIntegral_localDifferential (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (principalLevel N) k) (R : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    thetaScale⁻¹ * (∮ q : ℂ in C(0, R), localDifferential N f q) = localResidue N f := by
  have hh : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f (principalPeriod_mem N)
  have hhol := ModularFormClass.holo f
  have hbd := ModularFormClass.bdd_at_infty f
  have hc := qExpansion_coeff_eq_circleIntegral hh hper hhol hbd 0 hR hR1
  have hi : (∮ q : ℂ in C(0, R), localDifferential N f q) =
      (N : ℂ) / thetaScale * (∮ q : ℂ in C(0, R), cuspFunction (N : ℝ) f q / q) := by
    unfold localDifferential circleIntegral
    simp only [smul_eq_mul]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [hi, localResidue]
  simp only [Nat.reduceAdd, pow_one] at hc
  rw [hc]
  change thetaScale⁻¹ * ((N : ℂ) / thetaScale * _) =
    (N : ℂ) / thetaScale * ((2 * (Real.pi : ℂ) * I)⁻¹ * _)
  rw [← thetaScale]
  ring

/-- The same genuine constraint in the identified local-residue normalization, retaining coset multiplicities. -/
theorem principal_coset_residues_sum_zero (N : ℕ) [NeZero N]
    (f : ModularForm (principalLevel N) 2) :
    let _ : Fintype (principalCosets N) := Fintype.ofFinite _
    ∑ q : principalCosets N, localResidue N (SlashInvariantForm.quotientFunc f q) = 0 := by
  let : Fintype (principalCosets N) := Fintype.ofFinite _
  simp only [localResidue, ← Finset.mul_sum]
  change (N : ℂ) / thetaScale * (∑ q : principalCosets N, cosetConstant N f q) = 0
  rw [principal_coset_constants_sum_zero N f, mul_zero]

#print axioms principal_trace_zero
#print axioms principal_coset_constants_sum_zero
#print axioms localDifferential_pullback
#print axioms circleIntegral_localDifferential
#print axioms principal_coset_residues_sum_zero

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants
