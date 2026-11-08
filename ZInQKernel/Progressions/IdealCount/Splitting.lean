import ZInQKernel.Progressions.IdealCount.PrimePower
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The splitting law in a quadratic field

Let `K` be a quadratic field, `α ∈ 𝓞 K` with `α ^ 2 = d` for a non-square integer `d`, and `p`
an odd prime not dividing `d`. Then `ε_p = (d / p)` (plan step 3.3, item 3).

The route avoids Kummer–Dedekind. Ideals of norm `p` are the kernels of the ring homomorphisms
`𝓞 K → ZMod p`, so `a_K(p)` counts these homomorphisms. With `t` the trace of `𝓞 K` over `ℤ`,
every `x ∈ 𝓞 K` satisfies `2 d x = d t(x) + t(α x) α` (`IdealCount.two_mul_mul_eq`), so a
homomorphism is determined by the image `r` of `α`, a square root of `d` mod `p`; conversely
`x ↦ (d t(x) + t(α x) r) / (2 d)` is a homomorphism for every such `r`. Hence
`a_K(p) = #{r : r ^ 2 = d} = 1 + (d / p)`.
-/

namespace ZInQ.Progressions

open NumberField Ideal Module

variable {K : Type*} [Field K] [NumberField K]

namespace IdealCount

/-! ### Ideals of prime norm are kernels of homomorphisms to `ZMod p` -/

theorem absNorm_ker (p : ℕ) (φ : 𝓞 K →+* ZMod p) : absNorm (RingHom.ker φ) = p := by
  rw [absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective φ)).toEquiv,
    Nat.card_zmod]

theorem idealCount_prime_eq_card_ringHom {p : ℕ} (hp : p.Prime) :
    idealCount K p = Nat.card (𝓞 K →+* ZMod p) := by
  refine (Nat.card_eq_of_bijective (fun φ : 𝓞 K →+* ZMod p ↦
    (⟨RingHom.ker φ, absNorm_ker p φ⟩ : {I : Ideal (𝓞 K) // absNorm I = p})) ⟨?_, ?_⟩).symm
  · intro φ ψ h
    exact ZMod.ringHom_eq_of_ker_eq φ ψ (congrArg Subtype.val h)
  · rintro ⟨I, hI⟩
    have hcard : Nat.card (𝓞 K ⧸ I) = p := by
      rw [← Submodule.cardQuot_apply, ← absNorm_apply, hI]
    have : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hp.ne_zero)
    let _ := Fintype.ofFinite (𝓞 K ⧸ I)
    let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ I) hp (by rw [Fintype.card_eq_nat_card, hcard])
    refine ⟨(e.symm : (𝓞 K ⧸ I) →+* ZMod p).comp (Ideal.Quotient.mk I), Subtype.ext ?_⟩
    change RingHom.ker _ = I
    rw [RingHom.ker_comp_of_injective _ e.symm.injective, Ideal.mk_ker]

/-! ### The trace identity -/

section field

variable {β : K} {d : ℤ}

theorem linearIndependent_one_sqrt (hβ : β ^ 2 = d) (hd : ¬ IsSquare d) :
    LinearIndependent ℚ ![(1 : K), β] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simpa using hst
  · exfalso
    apply hd
    rw [← Rat.isSquare_intCast_iff]
    refine ⟨-s / t, (algebraMap ℚ K).injective ?_⟩
    have hβ' : β = algebraMap ℚ K (-s / t) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have ht' : algebraMap ℚ K t ≠ 0 := by simpa using ht
      rw [map_div₀, map_neg, eq_div_iff ht']
      linear_combination hst
    rw [map_intCast, ← hβ, hβ', map_mul, sq]

theorem trace_one_eq_two (h2 : finrank ℚ K = 2) : Algebra.trace ℚ K 1 = 2 := by
  rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, h2]
  norm_num

theorem trace_sqrt_eq_zero (h2 : finrank ℚ K = 2) (hβ : β ^ 2 = d) (hd : ¬ IsSquare d) :
    Algebra.trace ℚ K β = 0 := by
  classical
  have hli := linearIndependent_one_sqrt hβ hd
  have hc : Fintype.card (Fin 2) = finrank ℚ K := by rw [Fintype.card_fin, h2]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have hb : ⇑b = ![1, β] := coe_basisOfLinearIndependentOfCardEqFinrank hli hc
  have h0 : β * b 0 = b 1 := by simp [hb]
  have h1 : β * b 1 = (d : ℚ) • b 0 := by
    simp [hb, ← sq, hβ, Algebra.smul_def]
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply,
    Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, h0,
    h1, b.repr_self, map_smul, b.repr_self]
  simp

theorem trace_sqrt_sq (h2 : finrank ℚ K = 2) (hβ : β ^ 2 = d) :
    Algebra.trace ℚ K (β * β) = 2 * d := by
  rw [← sq, hβ, ← map_intCast (algebraMap ℚ K), Algebra.trace_algebraMap, h2]
  simp

/-- In a quadratic field, `2 d y = d Tr(y) + Tr(β y) β` when `β ^ 2 = d` is not a square. -/
theorem two_mul_mul_eq_field (h2 : finrank ℚ K = 2) (hβ : β ^ 2 = d) (hd : ¬ IsSquare d)
    (y : K) : 2 * d * y = d * algebraMap ℚ K (Algebra.trace ℚ K y) +
      algebraMap ℚ K (Algebra.trace ℚ K (β * y)) * β := by
  classical
  have hli := linearIndependent_one_sqrt hβ hd
  have hc : Fintype.card (Fin 2) = finrank ℚ K := by rw [Fintype.card_fin, h2]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have hb : ⇑b = ![1, β] := coe_basisOfLinearIndependentOfCardEqFinrank hli hc
  obtain ⟨a, c, rfl⟩ : ∃ a c : ℚ, y = a • 1 + c • β := by
    refine ⟨b.repr y 0, b.repr y 1, ?_⟩
    conv_lhs => rw [← b.sum_repr y]
    simp [Fin.sum_univ_two, hb]
  have e1 : β * (a • 1 + c • β) = a • β + c • (β * β) := by
    rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one]
  have t1 : Algebra.trace ℚ K (a • 1 + c • β) = 2 * a := by
    rw [map_add, map_smul, map_smul, trace_one_eq_two h2, trace_sqrt_eq_zero h2 hβ hd,
      smul_eq_mul, smul_eq_mul]
    ring
  have t2 : Algebra.trace ℚ K (a • β + c • (β * β)) = 2 * c * d := by
    rw [map_add, map_smul, map_smul, trace_sqrt_eq_zero h2 hβ hd, trace_sqrt_sq h2 hβ,
      smul_eq_mul, smul_eq_mul]
    ring
  rw [e1, t1, t2]
  simp only [Algebra.smul_def, map_mul, map_ofNat, map_intCast, mul_one]
  ring

end field

variable {α : 𝓞 K} {d : ℤ}

theorem coe_trace_int' (x : 𝓞 K) :
    ((Algebra.trace ℤ (𝓞 K) x : ℤ) : K) = algebraMap ℚ K (Algebra.trace ℚ K (x : K)) := by
  rw [← Algebra.coe_trace_int, map_intCast]

omit [NumberField K] in
theorem coe_sq_eq (hα : α ^ 2 = d) : (α : K) ^ 2 = d := by
  have := congrArg (algebraMap (𝓞 K) K) hα
  rwa [map_pow, map_intCast] at this

/-- **The trace identity**: `2 d x = d t(x) + t(α x) α` for `x ∈ 𝓞 K`. -/
theorem two_mul_mul_eq (h2 : finrank ℚ K = 2) (hα : α ^ 2 = d) (hd : ¬ IsSquare d)
    (x : 𝓞 K) : 2 * d * x = d * Algebra.trace ℤ (𝓞 K) x +
      Algebra.trace ℤ (𝓞 K) (α * x) * α := by
  ext
  simp only [map_add, map_mul, map_ofNat, map_intCast]
  rw [← RingOfIntegers.coe_eq_algebraMap, coe_trace_int', coe_trace_int']
  exact two_mul_mul_eq_field h2 (coe_sq_eq hα) hd x

theorem trace_one_int (h2 : finrank ℚ K = 2) : Algebra.trace ℤ (𝓞 K) 1 = 2 := by
  have := Algebra.coe_trace_int (1 : 𝓞 K)
  rw [show ((1 : 𝓞 K) : K) = 1 from map_one _, trace_one_eq_two h2] at this
  exact_mod_cast this

theorem trace_sqrt_int (h2 : finrank ℚ K = 2) (hα : α ^ 2 = d) (hd : ¬ IsSquare d) :
    Algebra.trace ℤ (𝓞 K) α = 0 := by
  have := Algebra.coe_trace_int α
  rw [trace_sqrt_eq_zero h2 (coe_sq_eq hα) hd] at this
  exact_mod_cast this

theorem trace_sq_int (h2 : finrank ℚ K = 2) (hα : α ^ 2 = d) :
    Algebra.trace ℤ (𝓞 K) (α * α) = 2 * d := by
  have := Algebra.coe_trace_int (α * α)
  rw [show ((α * α : 𝓞 K) : K) = α * α from map_mul _ _ _,
    trace_sqrt_sq h2 (coe_sq_eq hα)] at this
  exact_mod_cast this

theorem eq_zero_of_add_mul_eq_zero (hα : α ^ 2 = d) (hd : ¬ IsSquare d) {u v : ℤ}
    (h : (u : 𝓞 K) + v * α = 0) : u = 0 ∧ v = 0 := by
  have h' : (u : ℚ) • (1 : K) + (v : ℚ) • (α : K) = 0 := by
    have := congrArg (algebraMap (𝓞 K) K) h
    simp only [map_add, map_mul, map_intCast, map_zero] at this
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_intCast, map_intCast]
    exact this
  have hli := linearIndependent_one_sqrt (coe_sq_eq hα) hd
  have := LinearIndependent.pair_iff.mp hli _ _ h'
  exact_mod_cast this

theorem trace_mul_identities (h2 : finrank ℚ K = 2) (hα : α ^ 2 = d) (hd : ¬ IsSquare d)
    (hd0 : d ≠ 0) (x y : 𝓞 K) :
    2 * d * Algebra.trace ℤ (𝓞 K) (x * y) =
        d * Algebra.trace ℤ (𝓞 K) x * Algebra.trace ℤ (𝓞 K) y +
          Algebra.trace ℤ (𝓞 K) (α * x) * Algebra.trace ℤ (𝓞 K) (α * y) ∧
      2 * Algebra.trace ℤ (𝓞 K) (α * (x * y)) =
        Algebra.trace ℤ (𝓞 K) x * Algebra.trace ℤ (𝓞 K) (α * y) +
          Algebra.trace ℤ (𝓞 K) (α * x) * Algebra.trace ℤ (𝓞 K) y := by
  set t := Algebra.trace ℤ (𝓞 K)
  have hx := two_mul_mul_eq h2 hα hd x
  have hy := two_mul_mul_eq h2 hα hd y
  have hxy := two_mul_mul_eq h2 hα hd (x * y)
  have key := eq_zero_of_add_mul_eq_zero hα hd
    (u := 2 * d * d * t (x * y) - d * d * t x * t y - d * t (α * x) * t (α * y))
    (v := 2 * d * t (α * (x * y)) - d * t x * t (α * y) - d * t (α * x) * t y) (by
      push_cast
      linear_combination (-2 * (d : 𝓞 K)) * hxy + (2 * d * y) * hx +
        (d * t x + t (α * x) * α) * hy + (t (α * x) * t (α * y) : 𝓞 K) * hα)
  constructor
  · apply mul_left_cancel₀ hd0
    linear_combination key.1
  · apply mul_left_cancel₀ hd0
    linear_combination key.2

/-! ### Homomorphisms to `ZMod p` and square roots of `d` -/

variable {p : ℕ} [Fact p.Prime]

/-- The homomorphism `𝓞 K → ZMod p` sending `α` to a square root `r` of `d`. -/
noncomputable def sqrtHom (h2 : finrank ℚ K = 2) (hα : α ^ 2 = d) (hd : ¬ IsSquare d)
    (h2d : (2 * d : ZMod p) ≠ 0) (r : ZMod p) (hr : r ^ 2 = d) : 𝓞 K →+* ZMod p where
  toFun x := (d * Algebra.trace ℤ (𝓞 K) x + Algebra.trace ℤ (𝓞 K) (α * x) * r) / (2 * d)
  map_one' := by
    rw [mul_one, trace_one_int h2, trace_sqrt_int h2 hα hd]
    push_cast
    rw [zero_mul, add_zero, mul_comm]
    exact div_self h2d
  map_mul' x y := by
    have hd0 : d ≠ 0 := by rintro rfl; simp at h2d
    obtain ⟨h1, h2'⟩ := trace_mul_identities h2 hα hd hd0 x y
    have h1' := congrArg (fun z : ℤ ↦ (z : ZMod p)) h1
    have h2'' := congrArg (fun z : ℤ ↦ (z : ZMod p)) h2'
    push_cast at h1' h2''
    rw [div_mul_div_comm, div_eq_div_iff h2d (mul_ne_zero h2d h2d)]
    linear_combination (2 * (d : ZMod p)) * ((d : ZMod p) * h1' + d * r * h2'' -
      (Algebra.trace ℤ (𝓞 K) (α * x) * Algebra.trace ℤ (𝓞 K) (α * y) : ZMod p) * hr)
  map_zero' := by simp
  map_add' x y := by
    simp only [mul_add, map_add, Int.cast_add]
    ring

theorem sqrtHom_apply_sqrt (h2 : finrank ℚ K = 2) (hα : α ^ 2 = d) (hd : ¬ IsSquare d)
    (h2d : (2 * d : ZMod p) ≠ 0) (r : ZMod p) (hr : r ^ 2 = d) :
    sqrtHom h2 hα hd h2d r hr α = r := by
  change (d * Algebra.trace ℤ (𝓞 K) α + Algebra.trace ℤ (𝓞 K) (α * α) * r) / (2 * d) = r
  rw [trace_sqrt_int h2 hα hd, trace_sq_int h2 hα, div_eq_iff h2d]
  push_cast
  ring

theorem card_ringHom_eq_card_sqrt (h2 : finrank ℚ K = 2) (hα : α ^ 2 = d) (hd : ¬ IsSquare d)
    (h2d : (2 * d : ZMod p) ≠ 0) :
    Nat.card (𝓞 K →+* ZMod p) = Nat.card {r : ZMod p // r ^ 2 = d} := by
  refine Nat.card_eq_of_bijective (fun φ ↦ ⟨φ α, by rw [← map_pow, hα, map_intCast]⟩) ⟨?_, ?_⟩
  · intro φ ψ h
    have h' : φ α = ψ α := congrArg Subtype.val h
    ext x
    have hφ := congrArg φ (two_mul_mul_eq h2 hα hd x)
    have hψ := congrArg ψ (two_mul_mul_eq h2 hα hd x)
    simp only [map_add, map_mul, map_intCast, map_ofNat] at hφ hψ
    apply mul_left_cancel₀ h2d
    rw [hφ, hψ, h']
  · rintro ⟨r, hr⟩
    exact ⟨sqrtHom h2 hα hd h2d r hr, Subtype.ext (sqrtHom_apply_sqrt h2 hα hd h2d r hr)⟩

end IdealCount

open IdealCount

/-- **The splitting law** (plan step 3.3, item 3): `a_K(p) = 1 + (d / p)`. -/
theorem idealCount_prime_eq_legendreSym (h2 : finrank ℚ K = 2) {α : 𝓞 K} {d : ℤ}
    (hα : α ^ 2 = d) (hd : ¬ IsSquare d) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : ¬ (p : ℤ) ∣ d) : (idealCount K p : ℤ) = legendreSym p d + 1 := by
  have h2d : (2 * d : ZMod p) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    · rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [idealCount_prime_eq_card_ringHom (Fact.out : p.Prime),
    card_ringHom_eq_card_sqrt h2 hα hd h2d, ← legendreSym.card_sqrts p hp2 d,
    Nat.card_eq_fintype_card, Set.toFinset_card]
  rfl

/-- **The splitting law** (plan step 3.3, item 3): `ε_p = (d / p)` for odd `p ∤ d`. -/
theorem localEps_eq_legendreSym (h2 : finrank ℚ K = 2) {α : 𝓞 K} {d : ℤ}
    (hα : α ^ 2 = d) (hd : ¬ IsSquare d) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : ¬ (p : ℤ) ∣ d) : localEps K p = legendreSym p d := by
  rw [localEps, idealCount_prime_eq_legendreSym h2 hα hd p hp2 hpd]
  ring

theorem idealCount_prime_pow_eq_legendreSym (h2 : finrank ℚ K = 2) {α : 𝓞 K} {d : ℤ}
    (hα : α ^ 2 = d) (hd : ¬ IsSquare d) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : ¬ (p : ℤ) ∣ d) (k : ℕ) :
    (idealCount K (p ^ k) : ℤ) = ∑ j ∈ Finset.range (k + 1), legendreSym p d ^ j := by
  rw [idealCount_prime_pow h2 Fact.out, localEps_eq_legendreSym h2 hα hd p hp2 hpd]

end ZInQ.Progressions
