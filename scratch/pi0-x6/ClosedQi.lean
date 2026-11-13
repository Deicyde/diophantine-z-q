import ZInQKernel.HDecomp.QM.Leaves
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity

noncomputable section

namespace Pi0X6

open NumberField LeafQM LeafQM.AV

/-! ## The closed facts for `k₄ = ℚ(i) = ℚ(ζ₄)` -/

abbrev K4 := CyclotomicField 4 ℚ

instance : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : IsCyclotomicExtension {4} ℚ K4 := CyclotomicField.isCyclotomicExtension 4 ℚ

theorem hζ4 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 4 ℚ K4) 4 :=
  IsCyclotomicExtension.zeta_spec 4 ℚ K4

theorem zeta4_sq : (IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 = -1 := by
  have h := hζ4.pow_eq_one
  have h2 : (IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 ≠ 1 := by
    intro h2
    have := hζ4.pow_eq_one_iff_dvd 2
    rw [this] at h2
    norm_num at h2
  have : ((IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 - 1) *
      ((IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 this with h3 | h3
  · exact (h2 (sub_eq_zero.1 h3)).elim
  · exact eq_neg_of_add_eq_zero_left h3

instance : NumberField.IsTotallyComplex K4 :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) K4 (by norm_num)

theorem finrank_K4 : Module.finrank ℚ K4 = 2 := by
  rw [IsCyclotomicExtension.finrank K4 (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide

/-- `i := ζ₄ ∈ 𝓞 ℚ(ζ₄)`, with `i² = −1`. -/
def iInt : 𝓞 K4 := hζ4.toInteger

theorem alg_iInt : algebraMap (𝓞 K4) K4 iInt = IsCyclotomicExtension.zeta 4 ℚ K4 := rfl

theorem iInt_mul_self : iInt * iInt = ((-1 : ℤ) : 𝓞 K4) := by
  apply RingOfIntegers.coe_injective
  rw [map_mul, alg_iInt, map_intCast]; push_cast; rw [← pow_two, zeta4_sq]

/-- `ℤ[i] → 𝓞 ℚ(ζ₄)`, `a + bi ↦ a + bζ₄`. -/
def gaussToO : GaussianInt →+* 𝓞 K4 := Zsqrtd.lift ⟨iInt, iInt_mul_self⟩

theorem gaussToO_apply (z : GaussianInt) :
    gaussToO z = (z.re : 𝓞 K4) + (z.im : 𝓞 K4) * iInt := by
  simp [gaussToO, Zsqrtd.lift]

theorem gaussToO_bijective : Function.Bijective gaussToO := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    rw [gaussToO_apply] at hz
    have hK := congrArg (algebraMap (𝓞 K4) K4) hz
    rw [map_add, map_mul, alg_iInt, map_intCast, map_intCast, map_zero] at hK
    have him : z.im = 0 := by
      by_contra hb
      have hb' : ((z.im : ℚ) : K4) ≠ 0 := by exact_mod_cast hb
      have hζ : IsCyclotomicExtension.zeta 4 ℚ K4 = ((-(z.re : ℚ) / z.im : ℚ) : K4) := by
        push_cast
        field_simp
        linear_combination hK
      have := zeta4_sq
      rw [hζ] at this
      have h' : ((-(z.re : ℚ) / z.im) ^ 2 : ℚ) = -1 := by exact_mod_cast this
      nlinarith [sq_nonneg (-(z.re : ℚ) / z.im)]
    have hre : z.re = 0 := by
      rw [him] at hK
      simp at hK
      exact_mod_cast hK
    exact Zsqrtd.ext hre him
  · intro y
    let pb := hζ4.integralPowerBasis
    obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval y
    have hdim : pb.dim = 2 := by
      simp only [pb, IsPrimitiveRoot.integralPowerBasis_dim]; decide
    have hf1 : f.natDegree ≤ 1 := by omega
    obtain ⟨a, b, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hf1
    refine ⟨⟨b, a⟩, ?_⟩
    rw [gaussToO_apply, hf]
    simp only [map_add, map_mul, Polynomial.aeval_X,
      IsPrimitiveRoot.integralPowerBasis_gen, pb, iInt, eq_intCast, map_intCast]
    ring

/-- `ℤ[i] ≃ 𝓞 ℚ(ζ₄)`. -/
def gaussEquiv : GaussianInt ≃+* 𝓞 K4 := RingEquiv.ofBijective gaussToO gaussToO_bijective

theorem gaussEquiv_natCast (n : ℕ) : gaussEquiv (n : GaussianInt) = (n : 𝓞 K4) := map_natCast _ n

theorem prime_three_O4 : Prime (3 : 𝓞 K4) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 3).2 (by norm_num)
  have := (MulEquiv.prime_iff gaussEquiv.toMulEquiv).2 h
  have e3 : gaussEquiv.toMulEquiv ((3 : ℕ) : GaussianInt) = (3 : 𝓞 K4) := by
    change gaussEquiv ((3 : ℕ) : GaussianInt) = 3
    rw [map_natCast]; norm_num
  rwa [e3] at this

theorem not_prime_two_O4 : ¬ Prime (2 : 𝓞 K4) := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  intro h2
  have h := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 2).1
  have : Prime ((2 : ℕ) : GaussianInt) := by
    have := (MulEquiv.prime_iff gaussEquiv.symm.toMulEquiv).2 h2
    have e2 : gaussEquiv.symm.toMulEquiv (2 : 𝓞 K4) = ((2 : ℕ) : GaussianInt) := by
      change gaussEquiv.symm 2 = _
      rw [map_ofNat]; norm_num
    rwa [e2] at this
  have := h this
  norm_num at this

theorem inertCount6_K4 : inertCount6 K4 = 1 := by
  unfold inertCount6
  have h2 : ¬ (Ideal.span {(2 : 𝓞 K4)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact not_prime_two_O4
  have h3 : (Ideal.span {(3 : 𝓞 K4)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]; exact prime_three_O4
  simp [h2, h3]

/-- `R₄ = 𝓞 ℚ(ζ₄)` as a subring. -/
abbrev R4 : Subring K4 := (integralClosure ℤ K4).toSubring

theorem conductor_R4 : conductor R4 = 1 := AddSubgroup.relIndex_self _

theorem pic_R4 : Nat.card (CommRing.Pic R4) = 1 := by
  have e : GaussianInt ≃+* R4 := gaussEquiv.trans (RingEquiv.refl _)
  have : IsPrincipalIdealRing R4 := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have : Subsingleton (CommRing.Pic R4) := inferInstance
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

theorem zeta4_sq' : (IsCyclotomicExtension.zeta 4 ℚ K4) ^ 2 = (((-1 : ℚ)) : K4) := by
  rw [zeta4_sq]; push_cast; ring

end Pi0X6
