import Mathlib
import ZInQKernel.Compiler.Precision.HeightConstant
import ZInQKernel.Hypotheses.JHeight

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-assembly/GlueAssembly.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# Step F2 of h-trust: `h(Φ(z)) ≤ 40 h(z) + 22` over Mathlib's Weil heights

`Φ(z) = 3779136 (∏ z_m)⁴ / (∑ z_m⁸)⁵` (N5 L920-932). The statement is about Mathlib's genuine
Weil height `Height.logHeight` on a field with admissible absolute values (number fields).
-/

namespace GlueAssembly

open MvPolynomial Height Real

/-- The two coordinates of `Φ`, as polynomials over `ℕ` in ten variables. -/
noncomputable def PhiNat : Fin 2 → MvPolynomial (Fin 10) ℕ :=
  ![C 3779136 * (∏ i, X i) ^ 4, (∑ i, X i ^ 8) ^ 5]

theorem PhiNat_homogeneous (j : Fin 2) : (PhiNat j).IsHomogeneous 40 := by
  fin_cases j
  · have h1 : (∏ i : Fin 10, (X i : MvPolynomial (Fin 10) ℕ)).IsHomogeneous 10 := by
      have := IsHomogeneous.prod (Finset.univ : Finset (Fin 10)) (fun i => (X i : MvPolynomial (Fin
          10) ℕ))
        (fun _ => 1) (fun i _ => isHomogeneous_X ℕ i)
      simpa using this
    have := (h1.pow 4).C_mul 3779136
    simpa [PhiNat] using this
  · have h1 : (∑ i : Fin 10, (X i : MvPolynomial (Fin 10) ℕ) ^ 8).IsHomogeneous 8 :=
      IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X_pow i 8)
    simpa [PhiNat] using h1.pow 5

/-- The sum of the coefficients of a polynomial over `ℕ` is its value at `1`. -/
theorem sum_coeff_eq_eval_one {σ : Type*} (P : MvPolynomial σ ℕ) :
    ∑ s ∈ P.support, P.coeff s = eval (fun _ => 1) P := by
  rw [eval_eq]; simp

theorem PhiNat_eval_one (j : Fin 2) : eval (fun _ => 1) (PhiNat j) ≤ 3779136 := by
  fin_cases j <;> simp [PhiNat]

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- `Φ`'s coordinates over `K`. -/
noncomputable def PhiK (K : Type*) [CommSemiring K] : Fin 2 → MvPolynomial (Fin 10) K :=
  fun j => map (Nat.castRingHom K) (PhiNat j)

theorem PhiK_eval (z : Fin 10 → K) :
    (fun j => (PhiK K j).eval z) = ![3779136 * (∏ i, z i) ^ 4, (∑ i, z i ^ 8) ^ 5] := by
  ext j; fin_cases j <;> simp [PhiK, PhiNat]

/-- Local bound at an absolute value: the `ℓ¹`-norm of the coefficients is at most the value at
`1` of the `ℕ`-polynomial. -/
theorem coeff_sum_le (v : AbsoluteValue K ℝ) (P : MvPolynomial (Fin 10) ℕ) :
    (AddMonoidAlgebra.coeff (map (Nat.castRingHom K) P)).sum (fun _ c => v c) ≤
      ((eval (fun _ => 1) P : ℕ) : ℝ) := by
  have e : (AddMonoidAlgebra.coeff (map (Nat.castRingHom K) P)).sum (fun _ c => v c) =
      ∑ s ∈ (map (Nat.castRingHom K) P).support, v ((map (Nat.castRingHom K) P).coeff s) := rfl
  rw [e, ← sum_coeff_eq_eval_one]
  push_cast
  calc ∑ s ∈ (map (Nat.castRingHom K) P).support, v ((map (Nat.castRingHom K) P).coeff s)
      ≤ ∑ s ∈ P.support, v ((map (Nat.castRingHom K) P).coeff s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (support_map_subset _ _)
          (fun _ _ _ => v.nonneg _)
    _ ≤ ∑ s ∈ P.support, (P.coeff s : ℝ) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [coeff_map]
        simpa using v.apply_nat_le_self (P.coeff s)

theorem mulHeightBound_PhiK_le :
    mulHeightBound (PhiK K) ≤ (3779136 : ℝ) ^ totalWeight K := by
  rw [mulHeightBound_eq]
  have hnon : (∏ᶠ v : AdmissibleAbsValues.nonarchAbsVal (K := K),
      ⨆ j, max (⨆ s : (PhiK K j).support, v.val ((PhiK K j).coeff s)) 1) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    have hv := AdmissibleAbsValues.isNonarchimedean v.val v.prop
    refine le_antisymm (ciSup_le fun j => max_le ?_ le_rfl) ?_
    · rcases isEmpty_or_nonempty (PhiK K j).support with h | h
      · simp
      refine ciSup_le fun s => ?_
      simp only [PhiK, coeff_map]
      exact hv.apply_natCast_le_one (map_zero_le v.val 1) (map_one v.val)
    · exact le_trans (le_max_right _ 1) (Finite.le_ciSup_of_le (0 : Fin 2) le_rfl)
  rw [hnon, mul_one]
  have hle : ∀ v ∈ AdmissibleAbsValues.archAbsVal (K := K),
      (⨆ j, (AddMonoidAlgebra.coeff (PhiK K j)).sum (fun _ c => v c)) ≤ (3779136 : ℝ) := by
    intro v _
    refine ciSup_le fun j => (coeff_sum_le v (PhiNat j)).trans ?_
    exact_mod_cast PhiNat_eval_one j
  calc (AdmissibleAbsValues.archAbsVal.map fun v =>
        ⨆ j, (AddMonoidAlgebra.coeff (PhiK K j)).sum (fun _ c => v c)).prod
      ≤ (AdmissibleAbsValues.archAbsVal.map fun _ => (3779136 : ℝ)).prod :=
        Multiset.prod_map_le_prod_map₀ _ _
          (fun v _ => Real.iSup_nonneg fun j => Finsupp.sum_nonneg' fun _ => v.nonneg _) hle
    _ = (3779136 : ℝ) ^ totalWeight K := by
        simp [totalWeight]

/-- **F2, relative form.** For `z ∈ K¹⁰` (any field with admissible absolute values), the
projective height of `[3779136 (∏ z_m)⁴ : (∑ z_m⁸)⁵]` is at most
`40 h_K(z) + n_K log 3779136`, `n_K` the total weight (`= [K:ℚ]` for number fields). -/
theorem logHeight_Phi_le (z : Fin 10 → K) :
    logHeight ![3779136 * (∏ i, z i) ^ 4, (∑ i, z i ^ 8) ^ 5] ≤
      40 * logHeight z + totalWeight K * log 3779136 := by
  have hp : ∀ j, (PhiK K j).IsHomogeneous 40 := fun j => (PhiNat_homogeneous j).map _
  have h := logHeight_eval_le hp z
  rw [PhiK_eval] at h
  have hB : log (max (mulHeightBound (PhiK K)) 1) ≤ totalWeight K * log 3779136 := by
    rw [← Real.log_pow]
    refine Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) ?_
    exact max_le mulHeightBound_PhiK_le (one_le_pow₀ (by norm_num))
  push_cast at h
  linarith

/-- **F2, affine form**: `h_K(Φ(z)) ≤ 40 h_K(z) + n_K log 3779136`, with `Φ(z)` the quotient. -/
theorem logHeight₁_Phi_le (z : Fin 10 → K) :
    logHeight₁ (3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5) ≤
      40 * logHeight z + totalWeight K * log 3779136 := by
  rw [logHeight₁_div_eq_logHeight]; exact logHeight_Phi_le z

end GlueAssembly


/-!
# Height of a rational number in a number field

`h_K(q) = [K:ℚ] · log max(|num q|, den q)` for `q ∈ ℚ` and a number field `K` (Mathlib's relative
height `Height.logHeight₁`). This is the invariance of the absolute height under finite
extension, for rational numbers.
-/

namespace GlueAssembly

open Height NumberField Real

variable {K : Type*} [Field K] [NumberField K]

theorem iSup_fin_two (f : Fin 2 → ℝ) : ⨆ i, f i = max (f 0) (f 1) := by
  refine le_antisymm (ciSup_le fun i => ?_) (max_le (Finite.le_ciSup_of_le 0 le_rfl)
    (Finite.le_ciSup_of_le 1 le_rfl))
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- At a finite place, a coprime pair of integers has maximal absolute value `1`. -/
theorem finitePlace_max_eq_one (v : FinitePlace K) {a b : ℤ} (hab : IsCoprime a b) :
    max (v (a : K)) (v (b : K)) = 1 := by
  have hv : IsNonarchimedean (v : K → ℝ) := FinitePlace.add_le v
  have H (n : ℤ) : v (n : K) ≤ 1 :=
    hv.apply_intCast_le_one (map_zero_le v 1) (map_one v) (map_neg_eq_map v)
  obtain ⟨s, t, hst⟩ := hab
  refine le_antisymm (max_le (H a) (H b)) ?_
  have h1 : (1 : ℝ) = v ((s : K) * a + (t : K) * b) := by
    have : ((s : K) * a + (t : K) * b) = ((s * a + t * b : ℤ) : K) := by push_cast; ring
    rw [this, hst]; simp
  rw [h1]
  refine (hv _ _).trans (max_le_max ?_ ?_)
  · rw [map_mul]; exact mul_le_of_le_one_left (apply_nonneg v _) (H s)
  · rw [map_mul]; exact mul_le_of_le_one_left (apply_nonneg v _) (H t)

/-- The multiplicative height over `K` of a coprime integer pair `[a : b]` is
`max(|a|, |b|)^[K:ℚ]`. -/
theorem mulHeight_intPair {a b : ℤ} (hab : IsCoprime a b) (hb : b ≠ 0) :
    mulHeight ![(a : K), (b : K)] = (max |(a : ℝ)| |(b : ℝ)|) ^ Module.finrank ℚ K := by
  have hx : ![(a : K), (b : K)] ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
    exact hb this
  rw [NumberField.mulHeight_eq hx]
  have hfin : (∏ᶠ v : FinitePlace K, ⨆ i, v (![(a : K), (b : K)] i)) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [iSup_fin_two]
    simpa using finitePlace_max_eq_one v hab
  rw [hfin, mul_one]
  have hinf : ∀ v : InfinitePlace K, (⨆ i, v (![(a : K), (b : K)] i)) = max |(a : ℝ)| |(b : ℝ)| :=
      by
    intro v
    rw [iSup_fin_two]
    simp [InfinitePlace.map_intCast, Int.norm_eq_abs]
  simp_rw [hinf]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

/-- **Height of a rational number in a number field.** `h_K(q) = [K:ℚ] · log max(|num|, den)`. -/
theorem logHeight₁_algebraMap_rat (q : ℚ) :
    logHeight₁ (algebraMap ℚ K q) =
      Module.finrank ℚ K * log (max |(q.num : ℝ)| (q.den : ℝ)) := by
  have hden : ((q.den : ℤ) : K) ≠ 0 := by exact_mod_cast q.den_nz
  have e : algebraMap ℚ K q = ((q.num : ℤ) : K) / ((q.den : ℤ) : K) := by
    conv_lhs => rw [← Rat.num_div_den q]
    simp
  rw [e, logHeight₁_div_eq_logHeight, logHeight_eq_log_mulHeight,
    mulHeight_intPair (Rat.isCoprime_num_den q) (by exact_mod_cast q.den_nz), Real.log_pow]
  congr 2
  push_cast
  rw [abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℝ) < q.den)]

end GlueAssembly


/-!
# E2-E4 and F3 arithmetic of N5 (h-trust steps E2, E3, E4, F3), and the CM-branch arithmetic

Real-number lemmas. Their hypotheses are the numerical outputs of the literature theorems
(Javanpeykar, Gaudron–Rémond Thm 1.4, Faltings' Lemma 5 with additivity, Bost, Pazuki); their
conclusions are N5's displayed bounds.
-/

namespace GlueAssembly

open Real ZInQ

/-! ### E3-E4: the non-CM transfer (N5 L868-905) -/

/-- **E3-E4 arithmetic, wk-h's form** (`scratch/wk-h/Arakelov.lean`, re-proved here). -/
theorem transfer_numerics {Q M hFJ g d L hA hZ : ℝ} (hQ : 10 ^ 12 ≤ Q) (hM : 1 ≤ M)
    (hg2 : 2 ≤ g) (hg : g ≤ Q ^ 3 * M ^ 4) (hd1 : 1 ≤ d) (hd : d ≤ Q * M)
    (hJ : hFJ ≤ Q ^ 13 * M ^ 24)
    (hL : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * log (14 * g) + log d +
      2 * log (max hFJ (max (log d) 1))))
    (hvar : hA + hZ ≤ hFJ + L / 2) (hZ : -(2 * g) ≤ hZ) :
    hA ≤ Q ^ 17 * M ^ 24 := by
  set P := Q * M ^ 4 with hPdef
  have hQ1 : (1 : ℝ) ≤ Q := le_trans (by norm_num) hQ
  have hM4 : (1 : ℝ) ≤ M ^ 4 := one_le_pow₀ hM
  have hP : (10 : ℝ) ^ 12 ≤ P := by
    calc (10 : ℝ) ^ 12 = 10 ^ 12 * 1 := by ring
      _ ≤ Q * M ^ 4 := by gcongr
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hlogP : log P ≤ P := le_trans (log_le_sub_one_of_pos hP0) (by linarith)
  have hl1 : log (14 * g) ≤ 4 * P := by
    have h14 : 14 * g ≤ P ^ 4 := by
      have hM12 : (1 : ℝ) ≤ M ^ 12 := one_le_pow₀ hM
      calc 14 * g ≤ 14 * (Q ^ 3 * M ^ 4) := by linarith
        _ ≤ Q * (Q ^ 3 * M ^ 4) * M ^ 12 := by
            have : (14 : ℝ) ≤ Q := le_trans (by norm_num) hQ
            have h0 : 0 ≤ Q ^ 3 * M ^ 4 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hM12 (mul_nonneg (by positivity : (0:ℝ) ≤ Q) h0)]
        _ = P ^ 4 := by rw [hPdef]; ring
    calc log (14 * g) ≤ log (P ^ 4) := log_le_log (by linarith) h14
      _ = 4 * log P := by rw [log_pow]; norm_num
      _ ≤ 4 * P := by linarith
  have hl2 : log d ≤ P := by
    have : d ≤ P := by
      calc d ≤ Q * M := hd
        _ ≤ Q * M ^ 4 := by
            gcongr
            calc M = M ^ 1 := (pow_one M).symm
              _ ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
    linarith [log_le_log (by linarith) this]
  have hl3 : log (max hFJ (max (log d) 1)) ≤ 13 * P := by
    have hY : max hFJ (max (log d) 1) ≤ P ^ 13 := by
      have hP13 : P ≤ P ^ 13 := le_self_pow₀ (by linarith) (by norm_num)
      have hQM : Q ^ 13 * M ^ 24 ≤ P ^ 13 := by
        rw [hPdef, mul_pow, ← pow_mul]
        gcongr
        · norm_num
      refine max_le (hJ.trans hQM) (max_le ?_ ?_)
      · linarith [log_le_sub_one_of_pos (by linarith : (0:ℝ) < d)]
      · linarith
    calc log (max hFJ (max (log d) 1)) ≤ log (P ^ 13) :=
          log_le_log (lt_of_lt_of_le one_pos (le_max_of_le_right (le_max_right _ _))) hY
      _ = 13 * log P := by rw [log_pow]; norm_num
      _ ≤ 13 * P := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hlog14 : 0 ≤ log (14 * g) := log_nonneg (by linarith)
  have hL' : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P)) := by
    refine hL.trans ?_
    gcongr
  have hg3 : g ^ 3 ≤ (Q ^ 3 * M ^ 4) ^ 3 := by gcongr
  have hg2' : g ^ 2 ≤ (Q ^ 3 * M ^ 4) ^ 2 := by gcongr
  have hL'' : L ≤ 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P) := by
    refine hL'.trans ?_
    have : 64 * g ^ 2 * (4 * P) + P + 2 * (13 * P) ≤
        64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P := by nlinarith
    have h0 : 0 ≤ 64 * g ^ 2 * (4 * P) + P + 2 * (13 * P) := by positivity
    calc 1024 * g ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P))
        ≤ 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P)) := by gcongr
      _ ≤ _ := by gcongr
  have hT : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P) ≤
      262144 * Q ^ 16 * M ^ 24 + 27648 * Q ^ 16 * M ^ 24 := by
    rw [hPdef]
    have hM8 : (1 : ℝ) ≤ M ^ 8 := one_le_pow₀ hM
    have hQ6 : (1 : ℝ) ≤ Q ^ 6 := one_le_pow₀ hQ1
    have e1 : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * (Q * M ^ 4))) =
        262144 * Q ^ 16 * M ^ 24 := by ring
    have e2 : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (27 * (Q * M ^ 4)) = 27648 * (Q ^ 10 * M ^ 16) := by ring
    have e3 : Q ^ 10 * M ^ 16 ≤ Q ^ 16 * M ^ 24 := by
      have : Q ^ 16 * M ^ 24 = (Q ^ 10 * M ^ 16) * (Q ^ 6 * M ^ 8) := by ring
      rw [this]
      have h0 : 0 ≤ Q ^ 10 * M ^ 16 := by positivity
      nlinarith [one_le_mul_of_one_le_of_one_le hQ6 hM8]
    nlinarith [e1, e2, e3]
  have hlow : Q ^ 3 * M ^ 4 ≤ Q ^ 16 * M ^ 24 := by
    have h1 : (1 : ℝ) ≤ Q ^ 13 := one_le_pow₀ hQ1
    have h2 : (1 : ℝ) ≤ M ^ 20 := one_le_pow₀ hM
    have : Q ^ 16 * M ^ 24 = (Q ^ 3 * M ^ 4) * (Q ^ 13 * M ^ 20) := by ring
    rw [this]
    have h0 : 0 ≤ Q ^ 3 * M ^ 4 := by positivity
    nlinarith [one_le_mul_of_one_le_of_one_le h1 h2]
  have hJ' : Q ^ 13 * M ^ 24 ≤ Q ^ 16 * M ^ 24 := by
    have : Q ^ 13 ≤ Q ^ 16 := pow_le_pow_right₀ hQ1 (by norm_num)
    gcongr
  have hfin : Q ^ 16 * M ^ 24 * 10 ^ 12 ≤ Q ^ 17 * M ^ 24 := by
    have : Q ^ 17 * M ^ 24 = Q ^ 16 * M ^ 24 * Q := by ring
    rw [this]; gcongr
  have hT0 : 0 ≤ Q ^ 16 * M ^ 24 := by positivity
  nlinarith

/-- **E2-E4 arithmetic from the level** (N5 L868-905): from the conductor bound `N ≤ QM²` (D5),
Javanpeykar's bound at `X₁(N)` (`h_F(J) ≤ 1.3·10⁷ N¹²`, `2 ≤ g ≤ N²`), `[L':ℚ] ≤ QM`, the
Gaudron–Rémond degree bound, Faltings' height variation with additivity, and Bost's lower bound
`h_F(Z) ≥ −(3/2)·dim Z` with `dim Z ≤ g`, conclude `h_F(A) ≤ Q¹⁷M²⁴`. -/
theorem transfer_of_level {Q M N g d hFJ L hA hZ : ℝ} (hQ : 10 ^ 12 ≤ Q) (hM : 1 ≤ M)
    (hN1 : 1 ≤ N) (hN : N ≤ Q * M ^ 2) (hJav : hFJ ≤ 13000000 * N ^ 12)
    (hg2 : 2 ≤ g) (hg : g ≤ N ^ 2) (hd1 : 1 ≤ d) (hd : d ≤ Q * M)
    (hL : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * log (14 * g) + log d +
      2 * log (max hFJ (max (log d) 1))))
    (hvar : hA + hZ ≤ hFJ + L / 2) (hBost : -(3 / 2) * g ≤ hZ) :
    hA ≤ Q ^ 17 * M ^ 24 := by
  have hQ1 : (1 : ℝ) ≤ Q := le_trans (by norm_num) hQ
  have hN0 : 0 ≤ N := by linarith
  have hN12 : N ^ 12 ≤ Q ^ 12 * M ^ 24 := by
    calc N ^ 12 ≤ (Q * M ^ 2) ^ 12 := by gcongr
      _ = Q ^ 12 * M ^ 24 := by ring
  have hJ : hFJ ≤ Q ^ 13 * M ^ 24 := by
    have h0 : 0 ≤ Q ^ 12 * M ^ 24 := by positivity
    calc hFJ ≤ 13000000 * N ^ 12 := hJav
      _ ≤ 13000000 * (Q ^ 12 * M ^ 24) := by gcongr
      _ ≤ Q * (Q ^ 12 * M ^ 24) := by gcongr; linarith
      _ = Q ^ 13 * M ^ 24 := by ring
  have hg' : g ≤ Q ^ 3 * M ^ 4 := by
    calc g ≤ N ^ 2 := hg
      _ ≤ (Q * M ^ 2) ^ 2 := by gcongr
      _ = Q ^ 2 * M ^ 4 := by ring
      _ ≤ Q ^ 3 * M ^ 4 := by
          have : Q ^ 2 ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
          gcongr
  exact transfer_numerics hQ hM hg2 hg' hd1 hd hJ hL hvar (by linarith)

/-! ### CM branch (N5 L581-631): `h_F(A) ≤ C_cm` -/

theorem log_two_mul_bcm_le {D : ℝ} (hD : 1 ≤ D) (n : ℕ) (hn : (n : ℝ) = 21000 * D ^ 2) :
    log (2 * (D ^ 2 * 3 ^ n + 1)) ≤ 2 + 2 * D + 42000 * D ^ 2 := by
  have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hD2 : (1 : ℝ) ≤ D ^ 2 := one_le_pow₀ hD
  have hle : 2 * (D ^ 2 * 3 ^ n + 1) ≤ 4 * (D ^ 2 * 3 ^ n) := by nlinarith
  have hpos : 0 < 2 * (D ^ 2 * 3 ^ n + 1) := by positivity
  have hlog4 : log 4 ≤ 2 := by
    have : (4 : ℝ) ≤ exp 2 := by
      have := add_one_le_exp (2 : ℝ)
      have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      have he := exp_one_gt_d9
      nlinarith
    calc log 4 ≤ log (exp 2) := log_le_log (by norm_num) this
      _ = 2 := log_exp 2
  have hlog3 : log 3 ≤ 2 := by
    have : (3 : ℝ) ≤ exp 2 := by
      have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      have he := exp_one_gt_d9
      nlinarith
    calc log 3 ≤ log (exp 2) := log_le_log (by norm_num) this
      _ = 2 := log_exp 2
  have hlogD : log D ≤ D := le_trans (log_le_sub_one_of_pos (by linarith)) (by linarith)
  calc log (2 * (D ^ 2 * 3 ^ n + 1)) ≤ log (4 * (D ^ 2 * 3 ^ n)) := log_le_log hpos hle
    _ = log 4 + 2 * log D + n * log 3 := by
        rw [log_mul (by norm_num) (by positivity), log_mul (by positivity) (by positivity),
          log_pow, log_pow]
        push_cast; ring
    _ ≤ 2 + 2 * D + 42000 * D ^ 2 := by
        rw [hn]
        have : 21000 * D ^ 2 * log 3 ≤ 21000 * D ^ 2 * 2 := by gcongr
        linarith

/-- **CM-branch arithmetic** (N5 L606-628): `h_F(E) ≤ B_cm`, `[L:ℚ] ≤ D`, Gaudron–Rémond with
source `E²` (`g = 2`: exponent `1024·2³ = 8192`, `(14·2)^{64·2²} = 28^{256}`), height variation
and additivity give `h_F(A) ≤ C_cm = 2B_cm + 4096(1028 + 5D + 84000D²)`. -/
theorem cm_numerics {D d hE L hA : ℝ} (n : ℕ) (hn : (n : ℝ) = 21000 * D ^ 2) (hD : 1 ≤ D)
    (hd1 : 1 ≤ d) (hd : d ≤ D) (hEB : hE ≤ D ^ 2 * 3 ^ n + 1)
    (hL : L ≤ 8192 * (256 * log 28 + log d + 2 * log (max (2 * hE) (max (log d) 1))))
    (hvar : hA ≤ 2 * hE + L / 2) :
    hA ≤ 2 * (D ^ 2 * 3 ^ n + 1) + 4096 * (1028 + 5 * D + 84000 * D ^ 2) := by
  set B := D ^ 2 * 3 ^ n + 1 with hB
  have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hD2 : D ≤ D ^ 2 := by nlinarith
  have hBD : D ≤ B := by rw [hB]; nlinarith
  have hlogd : log d ≤ D := le_trans (log_le_sub_one_of_pos (by linarith)) (by linarith)
  have hmax : max (2 * hE) (max (log d) 1) ≤ 2 * B :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  have hlogmax : log (max (2 * hE) (max (log d) 1)) ≤ 2 + 2 * D + 42000 * D ^ 2 :=
    (log_le_log (lt_of_lt_of_le one_pos (le_max_of_le_right (le_max_right _ _))) hmax).trans
      (log_two_mul_bcm_le hD n hn)
  have hlog28 : log 28 ≤ 4 := by
    have : (28 : ℝ) ≤ exp 4 := by
      have h4 : exp 4 = (exp 1) ^ 4 := by rw [← exp_nat_mul]; norm_num
      have he := exp_one_gt_d9
      rw [h4]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 4]
    calc log 28 ≤ log (exp 4) := log_le_log (by norm_num) this
      _ = 4 := log_exp 4
  have : L ≤ 8192 * (1028 + 5 * D + 84000 * D ^ 2) := by
    refine hL.trans ?_
    nlinarith
  linarith

/-! ### F3: Pazuki's bound in N5's normalization (N5 L934-947) -/

theorem log_sixteen_le : log (2 ^ 4 : ℝ) ≤ 3 := by
  have : (2 ^ 4 : ℝ) ≤ exp 3 := by
    have h3 : exp 3 = (exp 1) ^ 3 := by rw [← exp_nat_mul]; norm_num
    have he := exp_one_gt_d9
    rw [h3]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 3]
  calc log (2 ^ 4 : ℝ) ≤ log (exp 3) := log_le_log (by norm_num) this
    _ = 3 := log_exp 3

/-- **F3 arithmetic.** From Pazuki's Cor. 1.3(2) for `g = 2`, `r = 2` in the Deligne metric,
`h_Θ ≤ X_D/2 + C₂ log(X_D + 2)` with `X_D = max(1, h_F(A) + log π)` and
`C₂ = 1000·2⁴·(log 2⁴)⁵`, conclude `h ≤ 10⁴·2²⁴·max(1, h_F(A))`. -/
theorem pazuki_numerics {hz hA : ℝ}
    (hP : hz ≤ max 1 (hA + log π) / 2 +
      1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (max 1 (hA + log π) + 2)) :
    hz ≤ 10000 * 2 ^ 24 * max 1 hA := by
  set X := max 1 hA with hX
  set XD := max 1 (hA + log π) with hXD
  have hX1 : 1 ≤ X := le_max_left _ _
  have hlogpi : log π ≤ 2 := by
    have : π ≤ exp 2 := by
      have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      have he := exp_one_gt_d9
      have hpi := pi_lt_d2
      nlinarith
    calc log π ≤ log (exp 2) := log_le_log pi_pos this
      _ = 2 := log_exp 2
  have hXD1 : 1 ≤ XD := le_max_left _ _
  have hXD3 : XD ≤ 3 * X := by
    refine max_le (by linarith) ?_
    have : hA ≤ X := le_max_right _ _
    linarith
  have hlogXD : log (XD + 2) ≤ 2 * XD := by
    have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < XD + 2)
    linarith
  have hC0 : 0 ≤ log (2 ^ 4 : ℝ) := log_nonneg (by norm_num)
  have hC : (log (2 ^ 4 : ℝ)) ^ 5 ≤ 243 := by
    calc (log (2 ^ 4 : ℝ)) ^ 5 ≤ 3 ^ 5 := pow_le_pow_left₀ hC0 log_sixteen_le 5
      _ = 243 := by norm_num
  have hlog0 : 0 ≤ log (XD + 2) := log_nonneg (by linarith)
  have h1 : 1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (XD + 2) ≤ 1000 * 2 ^ 4 * 243 * (6 * X) := by
    have : log (XD + 2) ≤ 6 * X := by linarith
    gcongr
  have h2 : XD / 2 ≤ 3 * X / 2 := by linarith
  have h3 := hP.trans (add_le_add h2 h1)
  have h4 : 3 * X / 2 + 1000 * 2 ^ 4 * 243 * (6 * X) ≤ 10000 * 2 ^ 24 * X := by nlinarith
  exact h3.trans h4

end GlueAssembly

/-! F4 (from `scratch/glue-assembly/F4Copy.lean`): the copy of `JHeight.lean` is replaced by
an import of `ZInQKernel.Hypotheses.JHeight`; `SixContactMinAt S` is `SixContactMin` at
`S = Mult.S_mul` by `rfl`. -/

namespace GlueAssembly

open ZInQ ZInQ.JHeight

/-- `SixContactMin` at a prime set `S`; `SixContactMinAt Mult.S_mul` is `ZInQ.SixContactMin`
(`Hypotheses/HeightMin.lean`) by `rfl`. -/
def SixContactMinAt (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight u ≤ heightH6 (heightD : ℝ) * (contactSupport S u : ℝ) ^ 24


/-- `JHeightBound S → SixContactMinAt S` (as `sixContactMin_of_jHeightBound` in `JHeight.lean`). -/
theorem sixContactMinAt_of_jHeightBound {S : Finset ℕ} (hJ : JHeightBound S) :
    SixContactMinAt S := by
  intro u hu
  have h12 := twelve_mul_ratHeight_le u hu
  have hj := hJ u hu
  have hX : 1 ≤ heightX heightD := le_max_left _ _
  have hM : (1 : ℝ) ≤ (contactSupport S u : ℝ) ^ 24 :=
    one_le_pow₀ (by exact_mod_cast contactSupport_pos _ _)
  have hXM : 1 ≤ heightX heightD * (contactSupport S u : ℝ) ^ 24 :=
    one_le_mul_of_one_le_of_one_le hX hM
  rw [heightH6_eq]
  nlinarith

end GlueAssembly

/-!
# The assembly: from the numerical outputs of E2-E4, F1, F3 to `SixContactMinAt S`

`GlueOutputs S` is a conjunction, for every `u ∉ 𝒞`, of the numerical outputs that steps
A1-E1 (modularity half), E2-E4 (Javanpeykar, Gaudron–Rémond, Faltings, Bost), F1 (the theta
expression of `j`) and F3 (Pazuki) give. Lean checks the assembly: F2 (`logHeight_Phi_le`, over
Mathlib's Weil height), the invariance of the height of a rational number in a number field
(`logHeight₁_algebraMap_rat`), the E-arithmetic (`transfer_of_level`, `cm_numerics`), the
F3-arithmetic (`pazuki_numerics`), F4 (`twelve_mul_ratHeight_le`) and the final constant.

`GlueOutputs S` is NOT a faithful statement of the literature theorems: the abelian varieties and
their Faltings heights do not exist in Mathlib, so they appear only as real numbers with the
inequalities the theorems give. As a Lean Prop it is a height bound in disguise (wk-h §4.3).
What is faithful is the theta point: a genuine point of `K¹⁰` with its genuine Weil height.
-/

namespace GlueAssembly

open Real ZInQ ZInQ.JHeight Height

/-- A bundled number field. -/
structure NF where
  K : Type
  [fld : Field K]
  [nf : NumberField K]

attribute [instance] NF.fld NF.nf

/-- **Outputs of the non-CM transfer (A1-E1, E2, E3, E4)**, for `Q = Q_D`, `M = M_S(u)`, and
`hA` the stable Faltings height of `A`: a level `N` with `1 ≤ N ≤ QM²` (D5); `g = dim J₁(N)`
with `2 ≤ g ≤ N²` and `h_F(J₁(N)) ≤ 1.3·10⁷ N¹²` (Javanpeykar, `g, deg_B ≤ N²`); `d = [L':ℚ]`
with `1 ≤ d ≤ QM` (B3); `L = log deg φ` for the Gaudron–Rémond isogeny `J₁(N) → A × Z` (E1,
E3); `h_F(A) + h_F(Z) ≤ h_F(J₁(N)) + L/2` (Faltings' Lemma 5 and additivity) and
`h_F(Z) ≥ −(3/2)g` (Bost, `dim Z ≤ g`). -/
def NonCMOutput (Q M hA : ℝ) : Prop :=
  ∃ N g d hFJ L hZ : ℝ, 1 ≤ N ∧ N ≤ Q * M ^ 2 ∧ hFJ ≤ 13000000 * N ^ 12 ∧
    2 ≤ g ∧ g ≤ N ^ 2 ∧ 1 ≤ d ∧ d ≤ Q * M ∧
    L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * log (14 * g) + log d +
      2 * log (max hFJ (max (log d) 1))) ∧
    hA + hZ ≤ hFJ + L / 2 ∧ -(3 / 2) * g ≤ hZ

/-- **Outputs of the CM branch (N5 L581-628)**: `d = [L:ℚ] ≤ D`, `h_F(E) ≤ B_cm`, `L = log deg`
of the Gaudron–Rémond isogeny `E² → A`, and `h_F(A) ≤ 2h_F(E) + L/2`. -/
def CMOutput (hA : ℝ) : Prop :=
  ∃ d hE L : ℝ, 1 ≤ d ∧ d ≤ heightD ∧ hE ≤ heightBcm ∧
    L ≤ 8192 * (256 * log 28 + log d + 2 * log (max (2 * hE) (max (log d) 1))) ∧
    hA ≤ 2 * hE + L / 2

/-- **Output of F3 (Pazuki, Cor. 1.3(2), `g = r = 2`, Deligne metric)** for the absolute
sup-norm height `hz` of the even theta nulls. -/
def PazukiOutput (hz hA : ℝ) : Prop :=
  hz ≤ max 1 (hA + log π) / 2 +
    1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (max 1 (hA + log π) + 2)

/-- **The glue interface.** For every `u ∉ 𝒞`: a number field `K`, the ten even theta nulls
`z ∈ K¹⁰` of the QM surface `A` over `J(u)` (F1: `Φ(z) = J(u)`), the Faltings height `hA` of
`A`, Pazuki's bound for the absolute Weil height `h(z) = h_K(z)/[K:ℚ]` (F3), and the outputs of
either the non-CM transfer (at `Q = Q_D`, `M = M_S(u)`) or the CM branch. -/
def GlueOutputs (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet → ∃ (K : NF) (z : Fin 10 → K.K) (hA : ℝ),
    3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K.K (Jmap u) ∧
    PazukiOutput (logHeight z / Module.finrank ℚ K.K) hA ∧
    (NonCMOutput (heightQ heightD) (contactSupport S u) hA ∨ CMOutput hA)

/-- `Q_D ≥ D ≥ 10¹²`. -/
theorem heightQ_heightD_ge : (10 : ℝ) ^ 12 ≤ heightQ heightD := by
  have hD : (10 : ℝ) ^ 12 ≤ heightD := by
    exact_mod_cast ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  have hD1 : (1 : ℝ) ≤ heightD := le_trans (by norm_num) hD
  have hDpos : 0 < heightD := by
    have := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
    omega
  have hE : (1 : ℝ) ≤ heightE0 := by
    have : 1 ≤ heightE0 := by
      rw [ZInQ.Compiler.Precision.heightE0_eq]
      have hG : 0 < heightG0 := by unfold heightG0; norm_num
      have := Nat.mul_pos hDpos hG
      have := pow_pos this 2
      omega
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ (heightD : ℝ) * heightE0 := one_le_mul_of_one_le_of_one_le hD1 hE
  calc (10 : ℝ) ^ 12 ≤ heightD := hD
    _ = (heightD : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
    _ ≤ (heightD : ℝ) ^ ((heightD : ℝ) * heightE0) := rpow_le_rpow_of_exponent_le hD1 h1
    _ = heightQ heightD := rfl

/-- Casting `C_cm`'s defining equation, over variables (the kernel cannot unfold the constants;
see `ZInQKernel/Compiler/Precision/HeightConstant.lean`). -/
theorem cast_ccm {C B D : ℕ} (h : C = 2 * B + 4096 * (1028 + 5 * D + 84000 * D ^ 2)) :
    (C : ℝ) = 2 * (B : ℝ) + 4096 * (1028 + 5 * (D : ℝ) + 84000 * (D : ℝ) ^ 2) := by
  rw [h]; push_cast; ring

/-- The CM branch over variables: `h_F(A) ≤ C_cm` (applied to the constants through their
defining equations only). -/
theorem cm_branch_nat {D B C : ℕ} (hBe : B = D ^ 2 * 3 ^ (21000 * D ^ 2) + 1)
    (hCe : C = 2 * B + 4096 * (1028 + 5 * D + 84000 * D ^ 2)) (hD : 1 ≤ D) {d hE L hA : ℝ}
    (hd1 : 1 ≤ d) (hd : d ≤ D) (hEB : hE ≤ B)
    (hL : L ≤ 8192 * (256 * log 28 + log d + 2 * log (max (2 * hE) (max (log d) 1))))
    (hvar : hA ≤ 2 * hE + L / 2) : hA ≤ C := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hB : (B : ℝ) = (D : ℝ) ^ 2 * 3 ^ (21000 * D ^ 2) + 1 := by rw [hBe]; push_cast; ring
  have hnR : ((21000 * D ^ 2 : ℕ) : ℝ) = 21000 * (D : ℝ) ^ 2 := by push_cast; ring
  have hcm := cm_numerics (21000 * D ^ 2) hnR hD1 hd1 hd (hEB.trans (le_of_eq hB)) hL hvar
  rw [cast_ccm hCe, hB]
  exact hcm

theorem one_le_heightD_real : (1 : ℝ) ≤ heightD := by
  have : (10 : ℝ) ^ 12 ≤ heightD := by
    exact_mod_cast ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  linarith

/-- Non-CM half of the E-part: `max(1, h_F(A)) ≤ X(D)·M²⁴`. -/
theorem max_one_hA_le_noncm {M hA : ℝ} (hM : 1 ≤ M) (h : NonCMOutput (heightQ heightD) M hA) :
    hA ≤ heightX heightD * M ^ 24 := by
  obtain ⟨N, g, d, hFJ, L, hZ, hN1, hN, hJav, hg2, hg, hd1, hd, hL, hvar, hBost⟩ := h
  have h1 := transfer_of_level heightQ_heightD_ge hM hN1 hN hJav hg2 hg hd1 hd hL hvar hBost
  have hQX : heightQ heightD ^ 17 ≤ heightX heightD :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hM24 : 0 ≤ M ^ 24 := by positivity
  exact h1.trans (mul_le_mul_of_nonneg_right hQX hM24)

/-- CM half of the E-part. -/
theorem max_one_hA_le_cm {M hA : ℝ} (hM : 1 ≤ M) (h : CMOutput hA) :
    hA ≤ heightX heightD * M ^ 24 := by
  obtain ⟨d, hE, L, hd1, hd, hEB, hL, hvar⟩ := h
  have hDn : 1 ≤ heightD := le_trans (by norm_num) ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  have hcm := cm_branch_nat ZInQ.Compiler.Precision.heightBcm_eq
    ZInQ.Compiler.Precision.heightCcm_eq hDn hd1 hd hEB hL hvar
  have hCX : (heightCcm : ℝ) ≤ heightX heightD :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hX1 : 0 ≤ heightX heightD := le_trans zero_le_one (le_max_left _ _)
  have hM24 : 1 ≤ M ^ 24 := one_le_pow₀ hM
  calc hA ≤ heightCcm := hcm
    _ ≤ heightX heightD := hCX
    _ ≤ heightX heightD * M ^ 24 := le_mul_of_one_le_right hX1 hM24

/-- The E-part of the assembly: `max(1, h_F(A)) ≤ X(D)·M²⁴` in both branches (N5 L903-905). -/
theorem max_one_hA_le {M hA : ℝ} (hM : 1 ≤ M)
    (h : NonCMOutput (heightQ heightD) M hA ∨ CMOutput hA) :
    max 1 hA ≤ heightX heightD * M ^ 24 := by
  have hM24 : 1 ≤ M ^ 24 := one_le_pow₀ hM
  have hX1 : 1 ≤ heightX heightD := le_max_left _ _
  refine max_le (le_trans hX1 (le_mul_of_one_le_right (by linarith) hM24)) ?_
  rcases h with h | h
  · exact max_one_hA_le_noncm hM h
  · exact max_one_hA_le_cm hM h

theorem log_3779136_le : log 3779136 ≤ 16 := by
  have : (3779136 : ℝ) ≤ exp 16 := by
    have h : exp 16 = (exp 1) ^ 16 := by rw [← exp_nat_mul]; norm_num
    have he := exp_one_gt_d9
    rw [h]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 16]
  calc log 3779136 ≤ log (exp 16) := log_le_log (by norm_num) this
    _ = 16 := log_exp 16

/-- **F1 + F2 + invariance**: if `Φ(z) = j` for `j ∈ ℚ`, then
`h(j) ≤ 40·h_K(z)/[K:ℚ] + log 3779136`. -/
theorem ratHeight_le_of_theta {K : Type} [Field K] [NumberField K] (z : Fin 10 → K) (j : ℚ)
    (hF1 : 3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K j) :
    ratHeight j ≤ 40 * (logHeight z / Module.finrank ℚ K) + log 3779136 := by
  have h2 := logHeight₁_Phi_le z
  rw [hF1, logHeight₁_algebraMap_rat, NumberField.totalWeight_eq_finrank] at h2
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold ratHeight
  set n : ℝ := (Module.finrank ℚ K : ℝ)
  set L := log (max |(j.num : ℝ)| (j.den : ℝ))
  calc L = (n * L) / n := by field_simp
    _ ≤ (40 * logHeight z + n * log 3779136) / n := div_le_div_of_nonneg_right h2 hn.le
    _ = 40 * (logHeight z / n) + log 3779136 := by field_simp

/-- **The assembly.** `GlueOutputs S → JHeightBound S`. -/
theorem jHeightBound_of_glueOutputs {S : Finset ℕ} (h : GlueOutputs S) : JHeightBound S := by
  intro u hu
  obtain ⟨K, z, hA, hF1, hPaz, hE⟩ := h u hu
  have hM : (1 : ℝ) ≤ contactSupport S u := by exact_mod_cast contactSupport_pos S u
  set Y := heightX heightD * (contactSupport S u : ℝ) ^ 24 with hY
  have hXM : max 1 hA ≤ Y := max_one_hA_le hM hE
  have hz := pazuki_numerics hPaz
  have hj := ratHeight_le_of_theta z (Jmap u) hF1
  have hY1 : 1 ≤ Y := (le_max_left 1 hA).trans hXM
  have hlog := log_3779136_le
  have : ratHeight (Jmap u) ≤ (40 * 10000 * 2 ^ 24 + 22 : ℝ) * Y := by nlinarith
  rw [hY] at this
  linarith

/-- **H from the glue interface.** `GlueOutputs S → SixContactMinAt S`; at `S = Mult.S_mul`
the conclusion is `ZInQ.SixContactMin`. -/
theorem sixContactMinAt_of_glueOutputs {S : Finset ℕ} (h : GlueOutputs S) :
    SixContactMinAt S :=
  sixContactMinAt_of_jHeightBound (jHeightBound_of_glueOutputs h)

end GlueAssembly
