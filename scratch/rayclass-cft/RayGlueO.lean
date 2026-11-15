import RayProof5

/-! # rayclass-cft, Part G1: the glue `RingOfIntegersGen` for `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)`, proved -/

set_option linter.all false

noncomputable section

namespace RayClassCFT

open NumberField ShimuraGlue.Ray

/-- Elements of `ℤ[ζ]` with `ζ² = pζ + q` are `a + bζ`. -/
theorem adjoin_quad {K : Type*} [CommRing K] (ζ : K) (p q : ℤ) (h : ζ * ζ = p * ζ + q) {x : K}
    (hx : x ∈ Algebra.adjoin ℤ {ζ}) : ∃ a b : ℤ, x = a + b * ζ := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact ⟨0, 1, by simp⟩
  | algebraMap n => exact ⟨n, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a * c + b * d * q, a * d + b * c + b * d * p, by
      push_cast; linear_combination (b * d : K) * h⟩

/-- A rational number integral over `ℤ` (in `k`) is an integer (copy of height-glue's
`exists_int_of_isIntegral`). -/
theorem exists_int_of_isIntegral {k : Type} [Field k] [NumberField k] {r : ℚ}
    (h : IsIntegral ℤ (r : k)) : ∃ n : ℤ, r = n := by
  have h' : IsIntegral ℤ r := by
    rw [← isIntegral_algebraMap_iff (A := ℚ) (B := k)]
    simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact ⟨n, by rw [← hn]; simp⟩

theorem ringOfIntegersGen_K4 : RingOfIntegersGen K4 y4 := by
  intro x
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K4
  obtain ⟨z, hz⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1
    (RingOfIntegers.isIntegral_coe x)
  have h2 : y4 * y4 = (0 : ℤ) * y4 + (-1 : ℤ) := by
    have := y4_rel; push_cast at this ⊢; linear_combination this
  obtain ⟨a, b, hab⟩ := adjoin_quad y4 0 (-1) h2 (z.2 : (z : K4) ∈ Algebra.adjoin ℤ {y4})
  exact ⟨a, b, by rw [← hab]; exact hz.symm⟩

theorem ringOfIntegersGen_K3 : RingOfIntegersGen K3 y3 := by
  intro x
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K3
  have h2 : IsCyclotomicExtension.zeta 3 ℚ K3 * IsCyclotomicExtension.zeta 3 ℚ K3 =
      (-1 : ℤ) * IsCyclotomicExtension.zeta 3 ℚ K3 + (-1 : ℤ) := by
    have := y3_rel; simp only [y3] at this; push_cast at this ⊢; linear_combination this
  obtain ⟨z, hz⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1
    (RingOfIntegers.isIntegral_coe x)
  obtain ⟨a, b, hab⟩ := adjoin_quad _ (-1) (-1) h2 z.2
  refine ⟨a, -b, ?_⟩
  have hz' : (x : K3) = (z : K3) := hz.symm
  rw [hz', hab]; simp [y3]

/-- Conjugation `√−6 ↦ −√−6` of `K24`. -/
def conj24 : K24 →ₐ[ℚ] K24 :=
  liftQuad finrank_K24 (not_rat_of_disc y24_rel (by norm_num)) y24_rel (-y24) (by
    have h := y24_rel
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    rw [zero_smul, add_zero, neg_mul_neg]
    have h6 : ((6 : ℚ) : K24) = (6 : ℚ) • (1 : K24) := by rw [Rat.smul_def, mul_one]
    rw [← h6]; exact h)

theorem ringOfIntegersGen_K24 : RingOfIntegersGen K24 y24 := by
  intro x
  have hy := not_rat_of_disc y24_rel (by norm_num)
  obtain ⟨r, s, hrs⟩ := exists_rat_repr finrank_K24 hy (x : K24)
  have hx : IsIntegral ℤ (x : K24) := RingOfIntegers.isIntegral_coe x
  have hcx : IsIntegral ℤ (conj24 x) := hx.map conj24.toRingHom.toIntAlgHom
  have hcv : conj24 (x : K24) = (r : K24) - s * y24 := by
    rw [hrs, conj24, liftQuad_apply]; rw [Rat.smul_def]; simp; ring
  have hyy : y24 * y24 = -6 := by
    have h := y24_rel; push_cast at h; linear_combination h
  -- trace, norm and `(x − x̄)·√−6` are rational and integral
  obtain ⟨m, hm⟩ : ∃ m : ℤ, 2 * r = m := by
    have h := hx.add hcx
    rw [hcv, hrs] at h
    have e : (r : K24) + s * y24 + ((r : K24) - s * y24) = ((2 * r : ℚ) : K24) := by push_cast; ring
    rw [e] at h
    exact exists_int_of_isIntegral h
  obtain ⟨n, hn⟩ : ∃ n : ℤ, r * r + 6 * (s * s) = n := by
    have h := hx.mul hcx
    rw [hcv, hrs] at h
    have e : ((r : K24) + s * y24) * ((r : K24) - s * y24) = ((r * r + 6 * (s * s) : ℚ) : K24) := by
      push_cast; linear_combination (-(s : K24) * s) * hyy
    rw [e] at h
    exact exists_int_of_isIntegral h
  obtain ⟨e, he⟩ : ∃ e : ℤ, -12 * s = e := by
    have hyi : IsIntegral ℤ y24 := ⟨Polynomial.X ^ 2 + Polynomial.C 6,
      Polynomial.monic_X_pow_add_C _ two_ne_zero, by
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
        rw [sq, hyy]; simp⟩
    have h := (hx.sub hcx).mul hyi
    rw [hcv, hrs] at h
    have e : ((r : K24) + s * y24 - ((r : K24) - s * y24)) * y24 = ((-12 * s : ℚ) : K24) := by
      push_cast; linear_combination (2 * (s : K24)) * hyy
    rw [e] at h
    exact exists_int_of_isIntegral h
  -- arithmetic: `6 ∣ e`, then parity
  have h24 : (e : ℚ) ^ 2 = 6 * (4 * n - m ^ 2) := by
    rw [← he, ← hn]; push_cast; rw [← hm]; ring
  have h24z : e ^ 2 = 6 * (4 * n - m ^ 2) := by exact_mod_cast h24
  have h2 : (2 : ℤ) ∣ e :=
    Int.prime_two.dvd_of_dvd_pow (n := 2) ⟨3 * (4 * n - m ^ 2), by rw [h24z]; ring⟩
  have h3 : (3 : ℤ) ∣ e :=
    Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨2 * (4 * n - m ^ 2), by rw [h24z]; ring⟩
  obtain ⟨f, hf⟩ : (6 : ℤ) ∣ e := by omega
  have hmf : m ^ 2 + 6 * f ^ 2 = 4 * n := by
    rw [hf] at h24z; nlinarith
  rcases Int.even_or_odd m with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
    rcases Int.even_or_odd f with ⟨b, hb⟩ | ⟨b, hb⟩
  · refine ⟨a, -b, ?_⟩
    rw [hrs]
    have hr : r = a := by
      have : (2 : ℚ) * r = a + a := by rw [hm, ha]; push_cast; ring
      linarith
    have hs : s = -b := by
      have : (-12 : ℚ) * s = 6 * (b + b) := by rw [he, hf, hb]; push_cast; ring
      linarith
    rw [hr, hs]; push_cast; ring
  all_goals (exfalso; subst ha hb; ring_nf at hmf; omega)

end RayClassCFT

namespace RayClassCFT

open ShimuraCFT ShimuraGlue.Ray

/-- **`RayClassCM` with the glue `RingOfIntegersGen` discharged.** -/
theorem rayClassCM_of2 (hL : ShimuraMainThmIDeligneY3AbU)
    (hMR : LeafQM.AV.R1UnivRigid.MumfordRigidityCore) (hCN : ClassNumberOneB)
    (hI4 : QHatIntegral K4) (hI3 : QHatIntegral K3) (hI24 : QHatIntegral K24)
    (hB : CMBaseChange) (hA : CMAnalytic) : RayClassCM :=
  rayClassCM_of hL hMR hCN hI4 hI3 hI24 hB hA ringOfIntegersGen_K4 ringOfIntegersGen_K3
    ringOfIntegersGen_K24

end RayClassCFT

#print axioms RayClassCFT.ringOfIntegersGen_K24
#print axioms RayClassCFT.rayClassCM_of2
