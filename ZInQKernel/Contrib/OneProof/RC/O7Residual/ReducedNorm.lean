import ZInQKernel.Contrib.OneProof.RC.O7Residual.IdealNorm
import ZInQKernel.Contrib.OneProof.RC.O7Assemble.Ideals
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.AdelicNorm
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.NumberTheory.NumberField.Norm

/-! The reduced norm on the embedded idele block. This proves the
local valuation implicit in tex 9180–9194, on-the-spot (c). -/

noncomputable section

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open ZInQ.Contrib.CloudB3RC53

namespace ZInQ.Manuscript.RC.O7Residual

open Adelic Eichler O7Actual O7Orbits PicardFibers Visibility ThetaJoin LocalTorus O7Assemble

variable {F : Type} [Field F] [NumberField F] {d : ℤ}

/-- The quaternion reduced norm restricts to the quadratic field norm. -/
theorem nrd_embedding {a b : ℚ} (Q : QuadraticBasis F d) (ι : F →ₐ[ℚ] B a b)
    (htrace : (ι (Q.model QuadraticAlgebra.omega)).re = 0) (x : F) :
    nrd (ι x) = Algebra.norm ℚ x := by
  let f := ι.comp Q.model.toAlgHom
  have hw : star (f QuadraticAlgebra.omega) = -f QuadraticAlgebra.omega :=
    QuaternionAlgebra.star_eq_neg.mpr htrace
  have hs (y : QuadraticAlgebra ℚ (d : ℚ) 0) : star (f y) = f (star y) := by
    obtain ⟨r, i⟩ := y
    rw [QuadraticAlgebra.star_mk, zero_mul, add_zero,
      QuadraticAlgebra.mk_eq_add_smul_omega, QuadraticAlgebra.mk_eq_add_smul_omega]
    simp only [map_add, AlgHom.commutes, map_smul, star_add, QuaternionAlgebra.star_smul',
      QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.star_coe, hw, smul_neg, neg_smul, map_neg]
  let y := Q.model.symm x
  have hy : Q.model y = x := Q.model.apply_symm_apply x
  rw [← hy, Algebra.norm_eq_of_algEquiv Q.model y,
    show ι (Q.model y) = f y from rfl]
  change (f y * star (f y)).re = Algebra.norm ℚ y
  rw [hs, ← map_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, f.commutes]
  exact (QuadraticAlgebra.det_toLinearMap_eq_norm y).symm

/-- The completed valuation of a nonzero integer reads its principal ideal exponent. -/
theorem adicOrd_integer (v : HeightOneSpectrum (𝓞 F)) (k : 𝓞 F) (hk : k ≠ 0) :
    -WithZero.log (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) k)) =
      FractionalIdeal.count F v
        ((Ideal.span {k} : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) := by
  classical
  have hi : (Ideal.span {k} : Ideal (𝓞 F)) ≠ 0 :=
    fun h => hk (Ideal.span_singleton_eq_bot.mp h)
  have he : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) k) = v.intValuation k :=
    (v.valuedAdicCompletion_eq_valuation (K := F) k).trans (v.valuation_of_algebraMap k)
  rw [he, v.intValuation_if_neg hk, WithZero.log_exp, neg_neg, FractionalIdeal.count_coe _ _ hi]

/-- If an idele induces a nonzero integral ideal, the valuation of
reduced norm on its embedded (p)-block is the (p)-part of the ideal
norm. This uses any integral realization at (p) to apply the chart. -/
theorem block_norm_valuation {ell N : ℕ} [Fact ell.Prime] (hell : ell % 4 = 3) (hN : 0 < N)
    (Q : QuadraticBasis F d) (ι : F →ₐ[ℚ] B (-1) (-(ell : ℚ)))
    (htrace : (ι (Q.model QuadraticAlgebra.omega)).re = 0)
    {x₀ : (B (-1) (-(ell : ℚ)))ˣ} {α : B (-1) (-(ell : ℚ))}
    (p : Prime) (T : LocalTorusChart (levelOrder ell hell N hN) ι x₀ α p)
    (z : (Bp p.val (-1) (-(ell : ℚ)))ˣ)
    (hz : unitConjRing z⁻¹ (toLocal p.val α) ∈ (levelOrder ell hell N hN).completion p.val)
    (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (J : Ideal (𝓞 F)) (hJ : J ≠ 0)
    (ha : (toFractionalIdeal a).val = (J : FractionalIdeal (𝓞 F)⁰ F)) :
    Padic.valuation (TorusWeights.localNrd p (T.units (idelePrimeBlocks F a p)).val :
      ℚ_[p.val]) = ((Ideal.absNorm J).factorization p.val : ℤ) := by
  classical
  let u := idelePrimeBlocks F a p
  have hcount (v : HeightOneSpectrum (𝓞 F)) :
      -WithZero.log (Valued.v (a.val v)) =
        FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← adicOrd_def, ← count_coe_toFractionalIdeal, ha]
  have hu (v : PlacesAbove F p) : Valued.v (u v).val ≤ 1 := by
    rw [← WithZero.exp_zero]
    apply WithZero.le_exp_of_log_le
    change WithZero.log (Valued.v (a.val v.val)) ≤ 0
    have h := hcount v.val
    rw [FractionalIdeal.count_coe _ _ hJ] at h
    omega
  obtain ⟨k, hk, hv⟩ := exists_integer_of_block p u hu
  let K : Ideal (𝓞 F) := Ideal.span {k}
  have hK : K ≠ 0 := fun h => hk (Ideal.span_singleton_eq_bot.mp h)
  have hJK := absNorm_factorization_eq_of_counts p J K hJ hK (fun v =>
    (hcount v.val).symm.trans
      ((congrArg (fun x => -WithZero.log x) (hv v).symm).trans
        (adicOrd_integer v.val k hk)))
  let b : Fˣ := Units.mk0 (algebraMap (𝓞 F) F k)
    (fun h => hk ((IsFractionRing.injective (𝓞 F) F) (h.trans (map_zero _).symm)))
  let d := idelePrimeBlocks F (FiniteAdeleRing.unitEmbedding (𝓞 F) F b) p
  have hd (v : PlacesAbove F p) :
      (d v).val = algebraMap (𝓞 F) (v.val.adicCompletion F) k := by
    change algebraMap F (v.val.adicCompletion F) (algebraMap (𝓞 F) F k) = _
    rw [← IsScalarTower.algebraMap_apply]
  let r := u * d⁻¹
  have hr : r ∈ primeBlockIntegral F p := by
    intro v
    apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    change Valued.v ((u v * (d v)⁻¹).val) = 1
    have hval : Valued.v (d v).val = Valued.v (u v).val :=
      (congrArg (fun y : v.val.adicCompletion F => Valued.v y) (hd v)).trans (hv v)
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hval, mul_inv_cancel₀]
    exact (Valuation.ne_zero_iff _).mpr (u v).ne_zero
  have hr0 : Padic.valuation (TorusWeights.localNrd p (T.units r).val : ℚ_[p.val]) = 0 := by
    let e : localUnits (levelOrder ell hell N hN) p := ⟨z⁻¹ * (T.units r).val * z,
      (T.integral_iff z hz r).mpr hr⟩
    have he := val_localNorm_of_orderUnit hell hN p e
    change Padic.valuation (TorusWeights.localNrd p (z⁻¹ * (T.units r).val * z) :
      ℚ_[p.val]) = 0 at he
    simpa only [map_mul, map_inv, inv_mul_cancel_comm] using he
  have hrd : r * d = u := by simp [r]
  have hdiag : (TorusWeights.localNrd p (T.units d).val : ℚ_[p.val]) =
      (Algebra.norm ℚ (algebraMap (𝓞 F) F k) : ℚ_[p.val]) := by
    rw [T.diagonal_eq b]
    change ThetaJoin.reducedNorm _ _ (toLocal p.val (ι (algebraMap (𝓞 F) F k))) = _
    rw [norm_toLocal, nrd_embedding Q ι htrace]
  change Padic.valuation (TorusWeights.localNrd p (T.units u).val : ℚ_[p.val]) = _
  rw [← hrd, map_mul, Subgroup.coe_mul, map_mul, Units.val_mul,
    Padic.valuation_mul (Units.ne_zero _) (Units.ne_zero _), hr0, zero_add, hdiag, hJK]
  rw [show K = Ideal.span {k} from rfl, Ideal.absNorm_span_singleton,
    ← Algebra.coe_norm_int, Rat.cast_intCast, Padic.valuation_intCast, padicValInt,
    Nat.factorization_def _ p.prop]

set_option maxHeartbeats 1000000 in
/-- Reduced norm valuation on the normalized coprime representatives used
by the row. The partner primes are included. -/
theorem normalized_norm_valuation
    {ell N : ℕ} [Fact ell.Prime] (hell : ell % 4 = 3) (hN : 0 < N)
    (Q : QuadraticBasis F d) (ι : F →ₐ[ℚ] B (-1) (-(ell : ℚ)))
    (htrace : (ι (Q.model QuadraticAlgebra.omega)).re = 0)
    {x₀ : (B (-1) (-(ell : ℚ)))ˣ} {α : B (-1) (-(ell : ℚ))}
    (T : ∀ p, Nonempty (LocalTorusChart (levelOrder ell hell N hN) ι x₀ α p))
    (z : FiniteUnits (levelOrder ell hell N hN)) (hz : AdelicAdmissible α z)
    (m₀ : ℕ) (hm₀ : m₀ ≠ 0) (c : ClassGroup (𝓞 F)) (p : Prime) :
    Padic.valuation (TorusWeights.localNrd p
      ((T p).some.units (idelePrimeBlocks F (normalizedIdele m₀ hm₀ c) p)).val :
      ℚ_[p.val]) = ((Ideal.absNorm (coprimeIdeal m₀ hm₀ c).val).factorization p.val : ℤ) := by
  let J := coprimeIdeal m₀ hm₀ c
  have hJ := ((CST.conductorOrder F 1).mem_integralIdealsPrimeTo_conductorModulus_iff.mp J.prop).1
  by_cases hp : p.val ∣ m₀
  · have hcop := (exists_coprime_class m₀ hm₀ c).choose_spec.2
    have hnd : ¬ p.val ∣ Ideal.absNorm J.val :=
      fun hd => p.prop.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd hp)
    rw [(exists_normalized m₀ hm₀ c).choose_spec.2 p hp, map_one, Subgroup.coe_one,
      map_one, Units.val_one, Padic.valuation_one, Nat.factorization_eq_zero_of_not_dvd hnd,
      Nat.cast_zero]
  · exact block_norm_valuation hell hN Q ι htrace p (T p).some (z.val p) (hz p) _ J.val hJ
      (congrArg Units.val (exists_normalized m₀ hm₀ c).choose_spec.1)

end ZInQ.Manuscript.RC.O7Residual
