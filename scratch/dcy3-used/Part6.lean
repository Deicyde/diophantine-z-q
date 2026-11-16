import ZInQKernel.Contrib.OneProof.RayClassShimura

set_option linter.all false

noncomputable section

namespace DCY3Used

open LeafQM ShimuraCFT RayClassCFT IsDedekindDomain NumberField

abbrev K4 : Type := ShimuraGlue.Ray.K4
def c4 : K4 := ((1 : ℚ) : K4) + ((1 : ℚ) : K4) * y4

/-! ## The idele `s`: `1 + i` above 3, `1` elsewhere -/

theorem y4_sq : y4 * y4 = -1 := by
  have := y4_rel; push_cast at this; linear_combination this

theorem y4_integral : IsIntegral ℤ y4 :=
  (IsCyclotomicExtension.zeta_spec 4 ℚ K4).isIntegral (by norm_num)

def y4O : 𝓞 K4 := ⟨y4, y4_integral⟩

theorem y4O_coe : ((y4O : 𝓞 K4) : K4) = y4 := rfl
theorem y4O_alg : algebraMap (𝓞 K4) K4 y4O = y4 := rfl

theorem c4_ne : c4 ≠ 0 := by
  intro h
  have h2 : c4 * (1 - y4) = 2 := by rw [c4]; push_cast; linear_combination (-1 : K4) * y4_sq
  rw [h, zero_mul] at h2; norm_num at h2

variable (w : HeightOneSpectrum (𝓞 K4))

theorem v_eq (x : K4) : Valued.v (algebraMap K4 (w.adicCompletion K4) x) = w.valuation K4 x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem v_int_le (x : 𝓞 K4) : w.valuation K4 (x : K4) ≤ 1 := w.valuation_le_one x

theorem v_nat_eq_one (n : ℕ) (h : (n : 𝓞 K4) ∉ w.asIdeal) : w.valuation K4 (n : K4) = 1 := by
  have : (n : K4) = algebraMap (𝓞 K4) K4 n := (map_natCast _ n).symm
  rw [this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact h

theorem two_not_mem (h3 : (3 : 𝓞 K4) ∈ w.asIdeal) : ((2 : ℕ) : 𝓞 K4) ∉ w.asIdeal := by
  intro h2
  have : (1 : 𝓞 K4) ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem h3 h2; push_cast at this; norm_num at this; exact this
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem v_c4_le : w.valuation K4 c4 ≤ 1 := by
  have : c4 = ((1 + y4O : 𝓞 K4) : K4) := by rw [c4]; push_cast; simp only [y4O_coe, y4O_alg]; ring
  rw [this]; exact v_int_le w _

theorem v_c4_eq (h3 : (3 : 𝓞 K4) ∈ w.asIdeal) : w.valuation K4 c4 = 1 := by
  have h2 : c4 * (1 - y4) = ((2 : ℕ) : K4) := by rw [c4]; push_cast; linear_combination (-1 : K4) * y4_sq
  have hv := congrArg (w.valuation K4) h2
  rw [map_mul, v_nat_eq_one w 2 (two_not_mem w h3)] at hv
  have hb : w.valuation K4 (1 - y4) ≤ 1 := by
    have : (1 - y4 : K4) = ((1 - y4O : 𝓞 K4) : K4) := by push_cast; simp only [y4O_coe, y4O_alg]
    rw [this]; exact v_int_le w _
  have ha := v_c4_le w
  by_contra hne
  have hlt : w.valuation K4 c4 < 1 := lt_of_le_of_ne ha hne
  have : w.valuation K4 c4 * w.valuation K4 (1 - y4) < 1 :=
    lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt hb) le_rfl
  rw [hv] at this; exact lt_irrefl _ this

open Classical in
/-- The components of `s`. -/
def uf (w : HeightOneSpectrum (𝓞 K4)) : w.adicCompletion K4 :=
  if (3 : 𝓞 K4) ∈ w.asIdeal then algebraMap K4 _ c4 else 1

open Classical in
def uf' (w : HeightOneSpectrum (𝓞 K4)) : w.adicCompletion K4 :=
  if (3 : 𝓞 K4) ∈ w.asIdeal then algebraMap K4 _ c4⁻¹ else 1

theorem uf_mem : uf w ∈ w.adicCompletionIntegers K4 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  unfold uf; split_ifs with h
  · rw [v_eq]; exact v_c4_le w
  · simp

theorem uf'_mem : uf' w ∈ w.adicCompletionIntegers K4 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  unfold uf'; split_ifs with h
  · rw [v_eq, map_inv₀, v_c4_eq w h, inv_one]
  · simp

def u4 : FiniteAdeleRing (𝓞 K4) K4 := ⟨uf, Filter.Eventually.of_forall uf_mem⟩
def u4' : FiniteAdeleRing (𝓞 K4) K4 := ⟨uf', Filter.Eventually.of_forall uf'_mem⟩

theorem u4_mul : u4 * u4' = 1 := by
  apply FiniteAdeleRing.ext K4
  intro w
  show uf w * uf' w = 1
  unfold uf uf'; split_ifs with h
  · rw [← map_mul, mul_inv_cancel₀ c4_ne, map_one]
  · rw [one_mul]

theorem u4'_mul : u4' * u4 = 1 := by rw [mul_comm]; exact u4_mul

def u4U : (FiniteAdeleRing (𝓞 K4) K4)ˣ := ⟨u4, u4', u4_mul, u4'_mul⟩

/-- **The idele `s`**: `1 + i` at the place above 3, `1` at every other place (finite or infinite). -/
def s4 : IdeleGroup (𝓞 K4) K4 := IdeleGroup.ofFiniteIdele (𝓞 K4) K4 u4U

/-- `s ≡ 1 + i mod 3`: `u = c + 3b` with `b` integral. -/
def b4 : FiniteAdeleRing (𝓞 K4) K4 :=
  (u4 - algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) c4) * algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) (1 / 3)

theorem u4_eq : u4 = algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) c4 + 3 * b4 := by
  have h3 : (3 : FiniteAdeleRing (𝓞 K4) K4) * algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) (1 / 3) = 1 := by
    rw [show (3 : FiniteAdeleRing (𝓞 K4) K4) = algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) 3 from
        (map_ofNat _ 3).symm, ← map_mul]; norm_num
  calc u4 = algebraMap K4 _ c4 + (u4 - algebraMap K4 _ c4) * ((3 : FiniteAdeleRing (𝓞 K4) K4) *
        algebraMap K4 (FiniteAdeleRing (𝓞 K4) K4) (1 / 3)) := by rw [h3]; ring
    _ = algebraMap K4 _ c4 + 3 * b4 := by simp only [b4]; ring

theorem b4_mem : b4 w ∈ w.adicCompletionIntegers K4 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : b4 w = (uf w - algebraMap K4 (w.adicCompletion K4) c4) * algebraMap K4 _ (1 / 3) := rfl
  rw [e]
  unfold uf; split_ifs with h
  · simp
  · rw [← map_one (algebraMap K4 (w.adicCompletion K4)), ← map_sub, ← map_mul, v_eq, map_mul]
    have h1 : w.valuation K4 (1 - c4) ≤ 1 := by
      have : (1 - c4 : K4) = ((-y4O : 𝓞 K4) : K4) := by rw [c4]; push_cast; simp only [y4O_coe, y4O_alg]; ring
      rw [this]; exact v_int_le w _
    have h2 : w.valuation K4 (1 / 3) = 1 := by
      rw [one_div, map_inv₀]
      have : ((3 : ℕ) : 𝓞 K4) ∉ w.asIdeal := by exact_mod_cast h
      have h3 := v_nat_eq_one w 3 this
      push_cast at h3; rw [h3, inv_one]
    rw [h2, mul_one]; exact h1

end DCY3Used
