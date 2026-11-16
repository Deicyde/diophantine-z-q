/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Source.Definitions.Def_CerednikDrinfeld_ShimuraCurve
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_Rat_hilbertReciprocity_even_card_not_ternary_isotropic
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_Rat_exists_ternary_isotropic_of_forall_adicCompletion_of_pos

/-!
# W13 order bridge (2): `ℍ[ℚ, 2, -3]` is indefinite and ramified exactly at `2` and `3`

The vendored Anthropic-FLT predicate `ZInQ.Contrib.CloudW03NeronSurj.FLT.QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt 2 (-3) 2 3`
(`Def_CerednikDrinfeld_ShimuraCurve`) holds. Route (modelled on the upstream proof
`P2M/Sol/S_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_one_two.lean`):
reduce local division to anisotropy of `z² - 2x² + 3y²`; it is isotropic at every finite place
not over `2·3` (upstream `ZInQ.Contrib.CloudW03NeronSurj.FLT.Rat.exists_ternary_isotropic_adicCompletion_of_intCast_notMem`); the
anisotropic set is finite of even cardinality (upstream Hilbert reciprocity, the real place
being split); it is nonempty because the form has no nontrivial rational zero (upstream
Hasse–Minkowski for an indefinite form, plus a mod-3 descent proved here); and each of `2`, `3`
has a unique place above it, so the anisotropic set is exactly `{v₂, v₃}`.
-/

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura

/-- `z² + 3y² = 2x²` has no nontrivial integral solution (mod-3 descent). -/
theorem int_aniso : ∀ s : ℕ, ∀ z x y : ℤ, z.natAbs + x.natAbs + y.natAbs = s →
    z ^ 2 + 3 * y ^ 2 = 2 * x ^ 2 → z = 0 ∧ x = 0 ∧ y = 0 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro z x y hs h
  have m3 : ∀ a b : ZMod 3, a ^ 2 = 2 * b ^ 2 → a = 0 ∧ b = 0 := by decide
  have h3 : ((z : ZMod 3)) ^ 2 = 2 * (x : ZMod 3) ^ 2 := by
    have := congrArg (fun t : ℤ => (t : ZMod 3)) h
    push_cast at this
    rw [show (3 : ZMod 3) = 0 from rfl, zero_mul, add_zero] at this
    exact this
  obtain ⟨hz, hx⟩ := m3 _ _ h3
  have hz3 : (3 : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 3).mp hz
  have hx3 : (3 : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hx
  obtain ⟨z', rfl⟩ := hz3
  obtain ⟨x', rfl⟩ := hx3
  have hy3 : (3 : ℤ) ∣ y := by
    have h9 : 3 * y ^ 2 = 3 * (3 * (2 * x' ^ 2 - z' ^ 2)) := by linear_combination h
    have : (3 : ℤ) ∣ y ^ 2 := ⟨_, mul_left_cancel₀ (by norm_num) h9⟩
    exact Int.prime_three.dvd_of_dvd_pow this
  obtain ⟨y', rfl⟩ := hy3
  have h' : z' ^ 2 + 3 * y' ^ 2 = 2 * x' ^ 2 := by
    have h9 : 9 * (z' ^ 2 + 3 * y' ^ 2) = 9 * (2 * x' ^ 2) := by linear_combination h
    exact mul_left_cancel₀ (by norm_num) h9
  by_cases h0 : z' = 0 ∧ x' = 0 ∧ y' = 0
  · obtain ⟨rfl, rfl, rfl⟩ := h0; simp
  · exfalso
    have hpos : 0 < z'.natAbs + x'.natAbs + y'.natAbs := by
      by_contra hc
      apply h0
      omega
    have hlt : z'.natAbs + x'.natAbs + y'.natAbs < s := by
      rw [← hs]; simp only [Int.natAbs_mul]; norm_num; omega
    obtain ⟨a, b, c⟩ := ih _ hlt z' x' y' rfl h'
    exact h0 ⟨a, b, c⟩

/-- `z² - 2x² + 3y²` has no nontrivial rational zero. -/
theorem rat_aniso : ¬ ∃ z x y : ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
    z ^ 2 - 2 * x ^ 2 - (-3) * y ^ 2 = 0 := by
  rintro ⟨z, x, y, hne, h⟩
  apply hne
  set d : ℚ := ((z.den * x.den * y.den : ℕ) : ℚ)
  have hd : d ≠ 0 := by
    simp only [d]; exact_mod_cast (by positivity : z.den * x.den * y.den ≠ 0)
  have ez : z * d = (z.num * x.den * y.den : ℤ) := by
    simp only [d]; push_cast; rw [← Rat.mul_den_eq_num z]; ring
  have ex : x * d = (x.num * z.den * y.den : ℤ) := by
    simp only [d]; push_cast; rw [← Rat.mul_den_eq_num x]; ring
  have ey : y * d = (y.num * z.den * x.den : ℤ) := by
    simp only [d]; push_cast; rw [← Rat.mul_den_eq_num y]; ring
  set Z : ℤ := z.num * x.den * y.den
  set X : ℤ := x.num * z.den * y.den
  set Y : ℤ := y.num * z.den * x.den
  have hint : Z ^ 2 + 3 * Y ^ 2 = 2 * X ^ 2 := by
    have : ((Z ^ 2 + 3 * Y ^ 2 : ℤ) : ℚ) = ((2 * X ^ 2 : ℤ) : ℚ) := by
      push_cast; rw [← ez, ← ex, ← ey]; linear_combination d ^ 2 * h
    exact_mod_cast this
  obtain ⟨hZ, hX, hY⟩ := int_aniso _ Z X Y rfl hint
  refine ⟨?_, ?_, ?_⟩
  · have : z * d = 0 := by rw [ez, hZ]; simp
    exact (mul_eq_zero.mp this).resolve_right hd
  · have : x * d = 0 := by rw [ex, hX]; simp
    exact (mul_eq_zero.mp this).resolve_right hd
  · have : y * d = 0 := by rw [ey, hY]; simp
    exact (mul_eq_zero.mp this).resolve_right hd

/-- Exactly one height-one prime of `𝓞 ℚ` lies over a rational prime. -/
theorem eq_of_natCast_mem (p : ℕ) [Fact p.Prime] {w w' : HeightOneSpectrum (𝓞 ℚ)}
    (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) (hw' : (p : 𝓞 ℚ) ∈ w'.asIdeal) : w = w' := by
  let e := Rat.ringOfIntegersEquiv
  have key : ∀ u : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ u.asIdeal →
      u.asIdeal = (Ideal.span {(p : ℤ)}).comap (e : 𝓞 ℚ →+* ℤ) := by
    intro u hu
    have hmax : (u.asIdeal.comap (e.symm : ℤ →+* 𝓞 ℚ)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
    have hle : Ideal.span {(p : ℤ)} ≤ u.asIdeal.comap (e.symm : ℤ →+* 𝓞 ℚ) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show e.symm (p : ℤ) ∈ u.asIdeal
      rwa [map_natCast]
    have heq := (Int.ideal_span_isMaximal_of_prime p).eq_of_le hmax.ne_top hle
    rw [heq, Ideal.comap_comap]
    ext t
    simp
  have h1 := key w hw
  have h2 := key w' hw'
  cases w
  cases w'
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-- Local isotropy of `z² - 2x² + 3y²` at a finite place of `ℚ`. -/
def Iso (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
    z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) 2) * x ^ 2 -
      (algebraMap ℚ (v.adicCompletion ℚ) (-3)) * y ^ 2 = 0

theorem iso_of_not_mem (w : HeightOneSpectrum (𝓞 ℚ)) (h2 : ((2 : ℕ) : 𝓞 ℚ) ∉ w.asIdeal)
    (h3 : ((3 : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) : Iso w := by
  have hm : (((2 : ℤ)) : 𝓞 ℚ) ∉ w.asIdeal := by simpa using h2
  have hn : (((-3 : ℤ)) : 𝓞 ℚ) ∉ w.asIdeal := by
    intro h
    apply h3
    have := w.asIdeal.neg_mem_iff.mpr h
    push_cast at this
    simpa using this
  have h := ZInQ.Contrib.CloudW03NeronSurj.FLT.Rat.exists_ternary_isotropic_adicCompletion_of_intCast_notMem 2 (-3) w
    (by simpa using h2) hm hn
  simpa [Iso] using h

/-- **`ℍ[ℚ, 2, -3]` is indefinite and ramified exactly at `2` and `3`.** -/
theorem isIndefiniteRamifiedExactlyAt_two_negThree :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt (2 : ℚ) (-3) 2 3 := by
  refine ⟨Or.inl (by norm_num), fun v => ?_⟩
  have hK2 : ((2 : ℚ) : v.adicCompletion ℚ) ≠ 0 := by
    rw [← eq_ratCast (algebraMap ℚ (v.adicCompletion ℚ))]
    exact (map_ne_zero _).mpr (by norm_num)
  have hK3 : ((-3 : ℚ) : v.adicCompletion ℚ) ≠ 0 := by
    rw [← eq_ratCast (algebraMap ℚ (v.adicCompletion ℚ))]
    exact (map_ne_zero _).mpr (by norm_num)
  rw [ZInQ.Contrib.CloudW03NeronSurj.FLT.QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero,
    ZInQ.Contrib.CloudW03NeronSurj.FLT.QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero _ _ _ hK2 hK3]
  have hconv : (∀ z x y : v.adicCompletion ℚ,
      z ^ 2 - ((2 : ℚ) : v.adicCompletion ℚ) * x ^ 2 - ((-3 : ℚ) : v.adicCompletion ℚ) * y ^ 2 = 0 →
        z = 0 ∧ x = 0 ∧ y = 0) ↔ ¬ Iso v := by
    rw [Iso, eq_ratCast, eq_ratCast]
    constructor
    · rintro h ⟨z, x, y, hne, h0⟩
      exact hne (h z x y h0)
    · intro h z x y h0
      by_contra hne
      exact h ⟨z, x, y, hne, h0⟩
  rw [hconv]
  obtain ⟨S, hS, heven⟩ := ZInQ.Contrib.CloudW03NeronSurj.FLT.Rat.hilbertReciprocity_even_card_not_ternary_isotropic 2 (-3)
    (by norm_num) (by norm_num)
  have hS' : ∀ w, w ∈ S ↔ ¬ Iso w := hS
  simp only [show ¬((2 : ℚ) < 0 ∧ (-3 : ℚ) < 0) by norm_num, if_false, add_zero] at heven
  have hsub : ∀ w ∈ S, ((2 : ℕ) : 𝓞 ℚ) ∈ w.asIdeal ∨ ((3 : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
    intro w hw
    by_contra hc
    rw [not_or] at hc
    exact (hS' w).mp hw (iso_of_not_mem w hc.1 hc.2)
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hSe
    have hall : ∀ w : HeightOneSpectrum (𝓞 ℚ), Iso w := by
      intro w
      by_contra hw
      have := (hS' w).mpr hw
      rw [hSe] at this
      simp at this
    obtain ⟨z, x, y, hz, hzxy⟩ :=
      ZInQ.Contrib.CloudW03NeronSurj.FLT.Rat.exists_ternary_isotropic_of_forall_adicCompletion_of_pos 2 (-3) (by norm_num)
        (by norm_num) hall (Or.inl (by norm_num))
    exact rat_aniso ⟨z, x, y, hz, hzxy⟩
  -- a nonempty even set inside the fibres over `2` and `3`
  have card_le_one : ∀ (p : ℕ) [Fact p.Prime], (∀ w ∈ S, (p : 𝓞 ℚ) ∈ w.asIdeal) → S.card ≤ 1 := by
    intro p _ hp
    rw [Finset.card_le_one]
    intro a ha b hb
    exact eq_of_natCast_mem p (hp a ha) (hp b hb)
  have hcard : 1 < S.card := by
    rcases Nat.lt_or_ge 1 S.card with h | h
    · exact h
    · have h1 : S.card = 1 := le_antisymm h (Finset.card_pos.mpr hne)
      rw [h1] at heven
      exact absurd heven (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  constructor
  · intro hv
    have := hsub v ((hS' v).mpr hv)
    simpa using this
  · intro hv
    rw [← hS' v]
    by_contra hvS
    rcases hv with hv2 | hv3
    · have : ∀ w ∈ S, ((3 : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
        intro w hw
        rcases hsub w hw with h | h
        · exact absurd (eq_of_natCast_mem 2 h (by exact_mod_cast hv2) ▸ hw) hvS
        · exact h
      exact absurd (card_le_one 3 this) (by omega)
    · have : ∀ w ∈ S, ((2 : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
        intro w hw
        rcases hsub w hw with h | h
        · exact h
        · exact absurd (eq_of_natCast_mem 3 h (by exact_mod_cast hv3) ▸ hw) hvS
      exact absurd (card_le_one 2 this) (by omega)

end ZInQ.Contrib.CloudB2Shimura
