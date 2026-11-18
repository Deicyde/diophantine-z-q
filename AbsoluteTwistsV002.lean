import TwistedLValueV005
import ResidueSeriesV003

/-!
# A closed nonzero-twist supplier on the verified convergence half-plane

Normalization and the actual cuspidal coefficient convergence theorem supply
nonzero twists of both parities at every argument with real part greater than
half the weight plus one. Signed residue filtering and dominated convergence
produce the values; no Euler-product bound or desired L-value is a premise.
This half-plane does not contain argument one at weight two or argument two
at weight three. The critical conclusions below are restricted to weight at
least five.
-/

noncomputable section

open Complex Filter Matrix.SpecialLinearGroup CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Topology Classical

namespace CriticalTwists

/-- A common arithmetic level derived from the two translation divisibilities. -/
def twistLevel (N M : ℕ) : ℕ := M * Nat.lcm N M

instance twistLevel_neZero (N M : ℕ) [NeZero N] [NeZero M] : NeZero (twistLevel N M) :=
  ⟨Nat.mul_ne_zero (NeZero.ne M) (Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne M))⟩

instance addThree_neZero (r : ℕ) : NeZero (r + 3) := ⟨by omega⟩

/-- The first required level divisibility is derived, not supplied. -/
theorem twistLevel_dvd_NM (N M : ℕ) : N * M ∣ twistLevel N M := by
  change N * M ∣ M * Nat.lcm N M
  rw [mul_comm N M]
  exact Nat.mul_dvd_mul_left M (Nat.dvd_lcm_left N M)

/-- The second required level divisibility is derived, not supplied. -/
theorem twistLevel_dvd_MM (N M : ℕ) : M * M ∣ twistLevel N M :=
  Nat.mul_dvd_mul_left M (Nat.dvd_lcm_right N M)

variable {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ} {s : ℂ}

/-- The existing cusp-form twist at the explicitly derived common level. -/
def standardTwist (Φ : ZMod M → ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm ((Gamma1 (twistLevel N M)).map (mapGL ℝ)) k :=
  CuspForm.twist Φ (twistLevel_dvd_NM N M) (twistLevel_dvd_MM N M) f

/-- Its coefficients are the actual multiplier times the original coefficients. -/
theorem standardTwist_coeff (Φ : ZMod M → ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (standardTwist Φ f)).coeff n = Φ n * (qExpansion 1 f).coeff n :=
  CuspForm.qExpansion_twist_coeff Φ _ _ f n

/-- Actual cuspidal coefficient convergence on the verified half-plane. -/
theorem cuspCoefficient_hasSum (hk : 0 < k) (hs : (k : ℝ) / 2 + 1 < s.re)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    HasSum (fun n : ℕ => (qExpansion 1 f).coeff n / (n : ℂ) ^ s)
      (ModularForm.L hk f s) := by
  simpa using CuspForm.hasSum_L hk f hs

/-- A family of existing L-values of the actual signed twists. -/
def actualSignedL (hk : 0 < k) (s : ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (ε : ℂ) (r : ℕ) : ℂ :=
  ModularForm.L hk
    (standardTwist (M := r + 3) (residueIndicator 1 + ε • residueIndicator (-1)) f) s

/-- Binding the independent residue series to the existing continuation where its series converges. -/
theorem actualSignedL_eq_series (hk : 0 < k) (hs : (k : ℝ) / 2 + 1 < s.re)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (ε : ℂ) (r : ℕ) :
    actualSignedL hk s f ε r =
      signedResidueSeries (fun n : ℕ => (qExpansion 1 f).coeff n / (n : ℂ) ^ s) ε r := by
  unfold actualSignedL
  rw [← (cuspCoefficient_hasSum hk hs
    (standardTwist (M := r + 3) (residueIndicator 1 + ε • residueIndicator (-1)) f)).tsum_eq]
  unfold signedResidueSeries
  apply tsum_congr
  intro n
  rw [standardTwist_coeff]
  simp only [signedResidueMask, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Actual signed-twist L-values converge to the original first Fourier coefficient. -/
theorem actualSignedL_tendsto (hk : 0 < k) (hs : (k : ℝ) / 2 + 1 < s.re)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (ε : ℂ) :
    Tendsto (actualSignedL hk s f ε) atTop (𝓝 ((qExpansion 1 f).coeff 1)) := by
  have h := signedResidueSeries_tendsto
    (fun n : ℕ => (qExpansion 1 f).coeff n / (n : ℂ) ^ s)
    (cuspCoefficient_hasSum hk hs f).summable ε
  have hf : actualSignedL hk s f ε =
      signedResidueSeries (fun n : ℕ => (qExpansion 1 f).coeff n / (n : ℂ) ^ s) ε := by
    funext r
    exact actualSignedL_eq_series hk hs f ε r
  rw [hf]
  simpa only [Nat.cast_one, one_cpow, div_one] using h

/-- Normalization yields nonzero actual values, not merely a nonzero entire function. -/
theorem normalized_actualSignedL_eventually_ne_zero (F : HeckeRing.GL2.Newform N k)
    (hk : 0 < k) (hs : (k : ℝ) / 2 + 1 < s.re) (ε : ℂ) :
    ∀ᶠ r : ℕ in atTop, actualSignedL hk s F.toCuspForm ε r ≠ 0 := by
  have h := actualSignedL_tendsto hk hs F.toCuspForm ε
  rw [F.qExpansion_coeff_one] at h
  exact h.eventually (isOpen_compl_singleton.mem_nhds (by simp : (1 : ℂ) ∈ ({0} : Set ℂ)ᶜ))

/-- Character averaging extracts an even twist from a nonzero actual even residue value. -/
theorem exists_even_twist_of_residue_value (hk : 0 < k) (s : ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hn : ModularForm.L hk (standardTwist (M := M)
      (residueIndicator 1 + residueIndicator (-1)) f) s ≠ 0) :
    ∃ ψ : DirichletCharacter ℂ M, ψ.Even ∧ ModularForm.L hk (standardTwist ψ f) s ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have havg := even_twist_L_average hk s (1 : ZMod M) isUnit_one
    (twistLevel_dvd_NM N M) (twistLevel_dvd_MM N M) f
  simp only [ZMod.inv_one, map_one, one_mul] at havg
  have hz : (∑ ψ : DirichletCharacter ℂ M,
      if ψ.Even then ModularForm.L hk (standardTwist ψ f) s else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro ψ hψ
    by_cases he : ψ.Even
    · simp [he, hnone ψ he]
    · simp [he]
  change (M.totient : ℂ) / 2 * ModularForm.L hk
    (standardTwist (M := M) (residueIndicator 1 + residueIndicator (-1)) f) s =
      ∑ ψ : DirichletCharacter ℂ M,
        if ψ.Even then ModularForm.L hk (standardTwist ψ f) s else 0 at havg
  rw [hz] at havg
  have hfactor : (M.totient : ℂ) / 2 ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne M.totient)) two_ne_zero
  exact hn ((mul_eq_zero.mp havg).resolve_left hfactor)

/-- Character averaging extracts an odd twist from a nonzero actual odd residue value. -/
theorem exists_odd_twist_of_residue_value (hk : 0 < k) (s : ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hn : ModularForm.L hk (standardTwist (M := M)
      (residueIndicator 1 - residueIndicator (-1)) f) s ≠ 0) :
    ∃ ψ : DirichletCharacter ℂ M, ψ.Odd ∧ ModularForm.L hk (standardTwist ψ f) s ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have havg := odd_twist_L_average hk s (1 : ZMod M) isUnit_one
    (twistLevel_dvd_NM N M) (twistLevel_dvd_MM N M) f
  simp only [ZMod.inv_one, map_one, one_mul] at havg
  have hz : (∑ ψ : DirichletCharacter ℂ M,
      if ψ.Odd then ModularForm.L hk (standardTwist ψ f) s else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro ψ hψ
    by_cases he : ψ.Odd
    · simp [he, hnone ψ he]
    · simp [he]
  change (M.totient : ℂ) / 2 * ModularForm.L hk
    (standardTwist (M := M) (residueIndicator 1 - residueIndicator (-1)) f) s =
      ∑ ψ : DirichletCharacter ℂ M,
        if ψ.Odd then ModularForm.L hk (standardTwist ψ f) s else 0 at havg
  rw [hz] at havg
  have hfactor : (M.totient : ℂ) / 2 ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne M.totient)) two_ne_zero
  exact hn ((mul_eq_zero.mp havg).resolve_left hfactor)

/-- A closed supplier of nonzero opposite-parity twists on the actual convergence half-plane. -/
theorem exists_both_parity_twists_of_absConv (F : HeckeRing.GL2.Newform N k)
    (hk : 0 < k) (hs : (k : ℝ) / 2 + 1 < s.re) :
    ∃ r : ℕ, ∃ ξ ψ : DirichletCharacter ℂ (r + 3), ξ.Even ∧ ψ.Odd ∧
      (ξ * ψ) (-1) = -1 ∧
      ModularForm.L hk (standardTwist ξ F.toCuspForm) s *
        ModularForm.L hk (standardTwist ψ F.toCuspForm) s ≠ 0 := by
  obtain ⟨r, he, ho⟩ := ((normalized_actualSignedL_eventually_ne_zero F hk hs 1).and
    (normalized_actualSignedL_eventually_ne_zero F hk hs (-1))).exists
  have he' : ModularForm.L hk (standardTwist (M := r + 3)
      (residueIndicator 1 + residueIndicator (-1)) F.toCuspForm) s ≠ 0 := by
    simpa only [actualSignedL, one_smul] using he
  have ho' : ModularForm.L hk (standardTwist (M := r + 3)
      (residueIndicator 1 - residueIndicator (-1)) F.toCuspForm) s ≠ 0 := by
    simpa only [actualSignedL, neg_one_smul, sub_eq_add_neg] using ho
  obtain ⟨ξ, hξ, hnξ⟩ := exists_even_twist_of_residue_value hk s F.toCuspForm he'
  obtain ⟨ψ, hψ, hnψ⟩ := exists_odd_twist_of_residue_value hk s F.toCuspForm ho'
  refine ⟨r, ξ, ψ, hξ, hψ, ?_, mul_ne_zero hnξ hnψ⟩
  have hξval : ξ (-1) = 1 := hξ
  have hψval : ψ (-1) = -1 := hψ
  simp only [MulChar.mul_apply, hξval, hψval, one_mul]

/-- The critical argument belongs to this verified half-plane for weights at least five. -/
theorem exists_both_parity_twists_high_weight_critical (F : HeckeRing.GL2.Newform N k)
    (hk5 : 5 ≤ k) :
    ∃ r : ℕ, ∃ ξ ψ : DirichletCharacter ℂ (r + 3), ξ.Even ∧ ψ.Odd ∧
      (ξ * ψ) (-1) = -1 ∧
      ModularForm.L (by omega : 0 < k) (standardTwist ξ F.toCuspForm) ((k : ℂ) - 1) *
        ModularForm.L (by omega : 0 < k) (standardTwist ψ F.toCuspForm) ((k : ℂ) - 1) ≠ 0 := by
  have hk : 0 < k := by omega
  have hkr : (5 : ℝ) ≤ k := by exact_mod_cast hk5
  have hs : (k : ℝ) / 2 + 1 < ((k : ℂ) - 1).re := by
    simp only [Complex.sub_re, Complex.intCast_re, Complex.one_re]
    linarith
  exact exists_both_parity_twists_of_absConv F hk hs

end CriticalTwists
