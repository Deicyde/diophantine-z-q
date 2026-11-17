import ZInQKernel.Contrib.OneProof.PanBerger
import ZInQKernel.Contrib.G9.KerTheta

/-!
# Sanity checks of pb-bypass's period rings and of `LocalIsPst` (task pb-sanity)

`ZInQKernel/Contrib/OneProof/PanBerger.lean` (task pb-bypass) defines `A_cris`, `B_cris^+`,
`log [ε]`, `B_cris`, `B_st = B_cris[u]` with its action of `G_{ℚ_p}`, and `LocalIsPst`, and splits
the research field `r11r12` into `PanPrinted` and `BergerPrinted`. Those two leaves are genuine only
if the definitions are not degenerate. This file proves, with no `sorry` (only `propext`, `Classical.choice`, `Quot.sound`):

* **Non-degeneracy.** `p^m · ∏ log [ε_i] ≠ 0` in `A_cris` for every finite family with
  `ε_i^♯ = 1`, `ε_i ≠ 1` (`pow_mul_prod_logOf_ne_zero`); hence `0 ∉ tMonoid`, and `B_cris^+`,
  `B_cris`, `B_st` are not the zero ring (`nontrivial_bcrisPlus`, `nontrivial_bcris`,
  `nontrivial_bst`); `log [ε]` is not nilpotent in `B_cris^+` (`logOf_not_isNilpotent`); such `ε`
  exist (`nonempty_tEps`, `ε = (1, ζ_p, ζ_{p²}, …)`); `ℚ_p → B_st` is injective. The argument uses
  only `A_inf`: `ker θ = (ξ)` (`Contrib/G9/KerTheta.lean`), `ξ`-adic separatedness of
  `A_inf`, the lattice bound `N! · A_cris^0 ⊆ A_inf + ξ^N A_inf[1/p]` and the leading
  coefficient under `θ[1/p]`.
* **The action.** `G_{ℚ_p}` acts on `B_cris` and on `B_st` by ring automorphisms (`bcrisAut`,
  `stAut`, group homomorphisms into the automorphism groups). For `B_st` the group law is the
  cocycle identity for `log [u_σ]` (`stAct_mul_iff`), which follows from the additivity of `log` on
  `{ε : ε^♯ = 1}` (`logAdditive : LogAdditive p`, proved through the truncated identity
  `L_M(a + b + ab) − L_M(a) − L_M(b)` in `ℚ[B][A]`: its coefficients vanish in total degree `≤ M`
  (a derivative argument) and, in the divided-power basis, are divisible by `N` when `M ≥ 2N + 1`).
  The monodromy variable is genuine: for every finite `K` some `σ ∈ G_K` moves `p♭`, so
  `σ(u) = u + c(σ)t ≠ u` and `u ∉ B_st^{G_K}` (`exists_stAct_X_ne`, `X_not_mem_bstInv`).
* **`K_0 ⊆ B_st^{G_K}`.** `A_inf → B_st` is injective and equivariant (`embW_injective`,
  `stAct_embW`); for a root of unity `μ ∈ K` of order prime to `p`, the Teichmüller lift `[μ♭]`
  lies in `B_st^{G_K}` and `1, [μ♭], …, [μ♭]^{d-1}` (`d = [ℚ_p(μ) : ℚ_p]`) are `ℚ_p`-linearly
  independent (`teichB_pow_mem_bstInv`, `linearIndependent_teichB`), so a finite-dimensional
  `B_st^{G_K}` has dimension `≥ [ℚ_p(μ) : ℚ_p]` (`natDegree_minpoly_le_finrank_bstInv`).
* **Semistable representations.** A representation trivial on `G_K` is semistable over `K`
  (`isSemistableOver_of_trivial`, any `K`), so representations with finite image on a finite `K`,
  the trivial `n`-dimensional representation (`localIsPst_one`) and the quadratic characters
  `σ ↦ σ(α)/α` (`isPst_quadChar`) are potentially semistable. A character with a unit period in
  `B_st` is semistable (`isSemistableOver_of_period`); so the quadratic character of a root of
  unity `β` of order prime to `p` with `β² ∈ ℚ_p` (for `p` odd and `β` of order `2(p − 1)`, the
  unramified quadratic character) is semistable over `ℚ_p` itself (`isSemistableOver_quadChar_teich`),
  and nontrivial when `β ∉ ℚ_p` (`quadChar_ne_one`).

Not proved (see `docs/research/pb-sanity.md`): `B_st^{G_K} ⊆ K_0` (in particular the finite
dimensionality of `B_st^{G_K}`, which `IsSemistableOver` needs to mean Fontaine's condition), and a
representation that fails `LocalIsPst`.
-/

noncomputable section

set_option maxHeartbeats 1000000

section LogPolySection

open Polynomial

namespace PBLogPoly

abbrev R := Polynomial ℚ
abbrev S := Polynomial R

/-- `κ j = (-1)^{j+1}/j`. -/
def κ (j : ℕ) : ℚ := (-1) ^ (j + 1) / j

/-- `L_M(Z) = Σ_{1 ≤ j ≤ M} κ_j Z^j`. -/
def LM (M : ℕ) (Z : S) : S := ∑ j ∈ Finset.Ico 1 (M + 1), C (C (κ j)) * Z ^ j

/-- `c = A(1 + B) + B`, i.e. `(1 + A)(1 + B) - 1`. -/
def cA : S := X * C (1 + X) + C X

/-- `F_M = L_M(c) - L_M(A) - L_M(B)`. -/
def FM (M : ℕ) : S := LM M cA - LM M X - LM M (C X)

theorem derivative_LM (M : ℕ) (Z : S) :
    derivative (LM M Z) = (∑ k ∈ Finset.range M, (-Z) ^ k) * derivative Z := by
  rw [LM, derivative_sum, Finset.sum_Ico_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [derivative_C_mul, derivative_pow]
  have hk : ((1 + k : ℕ) : S) * C (C (κ (1 + k))) = (-1) ^ k := by
    have : ((1 + k : ℕ) : ℚ) * κ (1 + k) = (-1) ^ k := by
      rw [κ]
      have h0 : ((1 + k : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
      ring
    have := congrArg (fun q : ℚ => (C (C q) : S)) this
    simpa [map_mul, map_pow, map_neg, map_one] using this
  rw [Nat.add_sub_cancel_left]
  calc C (C (κ (1 + k))) * (C ((1 + k : ℕ) : R) * Z ^ k * derivative Z)
      = (((1 + k : ℕ) : S) * C (C (κ (1 + k)))) * Z ^ k * derivative Z := by
        rw [show (C ((1 + k : ℕ) : R) : S) = ((1 + k : ℕ) : S) from map_natCast C _]
        ring
    _ = _ := by rw [hk]; ring

theorem geom_neg (M : ℕ) (z : S) :
    (1 + z) * ∑ k ∈ Finset.range M, (-z) ^ k = 1 - (-z) ^ M := by
  have := geom_sum_mul_neg (-z) M
  rw [mul_comm, ← this]
  ring

theorem key_identity (M : ℕ) :
    (1 + X) * derivative (FM M) = (-X) ^ M - (-cA) ^ M := by
  have hc : derivative cA = C (1 + X) := by
    simp [cA, derivative_mul]
  have h1 : (1 + X : S) * C (1 + X) = 1 + cA := by
    simp only [cA, map_add, map_one]
    ring
  rw [FM, derivative_sub, derivative_sub, derivative_LM, derivative_LM, derivative_LM, hc,
    derivative_X, derivative_C, mul_zero, sub_zero, mul_one, mul_sub]
  rw [show (1 + X : S) * ((∑ k ∈ Finset.range M, (-cA) ^ k) * C (1 + X)) =
    (1 + cA) * ∑ k ∈ Finset.range M, (-cA) ^ k by rw [← h1]; ring]
  rw [geom_neg, geom_neg]
  ring

/-- The coefficients of `c^k` in `A` are divisible by suitable powers of `B`. -/
theorem dvd_coeff_cA_pow (k : ℕ) : ∀ i, (X : R) ^ (k - i) ∣ (cA ^ k).coeff i := by
  induction k with
  | zero =>
    intro i
    rw [Nat.zero_sub, pow_zero]
    exact one_dvd _
  | succ k ih =>
    intro i
    rw [pow_succ, cA, mul_add, ← mul_assoc, coeff_add, coeff_mul_C, coeff_mul_C]
    refine dvd_add ?_ ?_
    · rcases i with _ | i
      · rw [coeff_mul_X_zero, zero_mul]
        exact dvd_zero _
      · rw [coeff_mul_X, show k + 1 - (i + 1) = k - i by omega]
        exact dvd_mul_of_dvd_left (ih i) _
    · have := ih i
      calc (X : R) ^ (k + 1 - i) ∣ (X : R) ^ (k - i) * X := by
            rw [← pow_succ]; exact pow_dvd_pow X (by omega)
        _ ∣ (cA ^ k).coeff i * X := mul_dvd_mul_right this _

theorem eval_zero_LM (M : ℕ) (Z : S) :
    eval 0 (LM M Z) = ∑ j ∈ Finset.Ico 1 (M + 1), C (κ j) * (eval 0 Z) ^ j := by
  simp [LM, eval_finsetSum]

theorem coeff_zero_FM (M : ℕ) : (FM M).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, FM, eval_sub, eval_sub, eval_zero_LM, eval_zero_LM, eval_zero_LM]
  have h1 : eval 0 cA = X := by simp [cA]
  rw [h1, eval_X, eval_C, sub_sub_cancel_left, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [zero_pow (by omega), mul_zero]

theorem dvd_coeff_rhs (M i : ℕ) : (X : R) ^ (M - i) ∣ ((-X) ^ M - (-cA) ^ M : S).coeff i := by
  rcases Nat.lt_or_ge i M with h | h
  · rw [coeff_sub, _root_.neg_pow (X : S), _root_.neg_pow (cA : S),
      show ((-1 : S) ^ M) = C ((-1) ^ M) by simp, coeff_C_mul_X_pow, coeff_C_mul]
    split_ifs with h'
    · omega
    · rw [zero_sub]
      exact (dvd_neg).mpr (dvd_mul_of_dvd_right (dvd_coeff_cA_pow M i) _)
  · rw [show M - i = 0 by omega, pow_zero]
    exact one_dvd _

/-- **Claim 1 (divisibility form).** `B^{M+1-i}` divides the coefficient of `A^i` in `F_M`. -/
theorem dvd_coeff_FM (M : ℕ) : ∀ i, (X : R) ^ (M + 1 - i) ∣ (FM M).coeff i := by
  intro i
  induction i with
  | zero => rw [coeff_zero_FM]; exact dvd_zero _
  | succ i ih =>
    have hid := congrArg (fun P : S => P.coeff i) (key_identity M)
    rw [add_mul, one_mul, coeff_add, coeff_derivative] at hid
    have hX : (X : R) ^ (M - i) ∣ (X * derivative (FM M)).coeff i := by
      rcases i with _ | i
      · rw [coeff_X_mul_zero]; exact dvd_zero _
      · rw [coeff_X_mul, coeff_derivative]
        refine dvd_mul_of_dvd_left ((pow_dvd_pow X (by omega)).trans ih) _
    have h2 : (X : R) ^ (M - i) ∣ (FM M).coeff (i + 1) * ((i : R) + 1) := by
      have : (FM M).coeff (i + 1) * ((i : R) + 1) =
          ((-X) ^ M - (-cA) ^ M : S).coeff i - (X * derivative (FM M)).coeff i := by
        rw [← hid]; ring
      rw [this]
      exact dvd_sub (dvd_coeff_rhs M i) hX
    have hu : IsUnit ((i : R) + 1) := by
      have : ((i : R) + 1) = C ((i : ℚ) + 1) := by simp
      rw [this]
      exact (Polynomial.isUnit_C).mpr (IsUnit.mk0 _ (by positivity))
    rw [show M + 1 - (i + 1) = M - i by omega]
    exact (hu.dvd_mul_right).mp h2

/-- **Claim 1.** The coefficient of `A^i B^s` in `F_M` vanishes for `i + s ≤ M`. -/
theorem coeff_FM_eq_zero (M i s : ℕ) (h : i + s ≤ M) : ((FM M).coeff i).coeff s = 0 := by
  obtain ⟨g, hg⟩ := dvd_coeff_FM M i
  rw [hg, coeff_X_pow_mul']
  split_ifs with h'
  · omega
  · rfl

/-! ### Divided-power integrality -/

/-- All coefficients of `F` in the basis `A^i B^s / (i! s!)` are integers. -/
def IsDPInt (F : S) : Prop :=
  ∀ i s, ∃ z : ℤ, (F.coeff i).coeff s * (i.factorial : ℚ) * (s.factorial : ℚ) = z

theorem isDPInt_add {F G : S} (hF : IsDPInt F) (hG : IsDPInt G) : IsDPInt (F + G) := by
  intro i s
  obtain ⟨a, ha⟩ := hF i s
  obtain ⟨b, hb⟩ := hG i s
  exact ⟨a + b, by rw [coeff_add, coeff_add, add_mul, add_mul, ha, hb]; push_cast; ring⟩

theorem isDPInt_neg {F : S} (hF : IsDPInt F) : IsDPInt (-F) := by
  intro i s
  obtain ⟨a, ha⟩ := hF i s
  exact ⟨-a, by rw [coeff_neg, coeff_neg, neg_mul, neg_mul, ha]; push_cast; ring⟩

theorem isDPInt_sum {ι : Type*} (t : Finset ι) (F : ι → S) (h : ∀ k ∈ t, IsDPInt (F k)) :
    IsDPInt (∑ k ∈ t, F k) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro i s; exact ⟨0, by simp⟩
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact isDPInt_add (h a (Finset.mem_insert_self a t))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem isDPInt_mul {F G : S} (hF : IsDPInt F) (hG : IsDPInt G) : IsDPInt (F * G) := by
  classical
  choose a ha using hF
  choose b hb using hG
  intro i s
  refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal i, ∑ y ∈ Finset.HasAntidiagonal.antidiagonal s,
    ((i.choose x.1 * s.choose y.1 : ℕ) : ℤ) * a x.1 y.1 * b x.2 y.2, ?_⟩
  rw [coeff_mul, finsetSum_coeff, Finset.sum_mul, Finset.sum_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  rw [coeff_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  have hxi : (i.factorial : ℚ) = (i.choose x.1 : ℚ) * x.1.factorial * x.2.factorial := by
    rw [← hx, Nat.choose_symm_add]
    have := Nat.add_choose_mul_factorial_mul_factorial x.1 x.2
    exact_mod_cast this.symm
  have hys : (s.factorial : ℚ) = (s.choose y.1 : ℚ) * y.1.factorial * y.2.factorial := by
    rw [← hy, Nat.choose_symm_add]
    have := Nat.add_choose_mul_factorial_mul_factorial y.1 y.2
    exact_mod_cast this.symm
  rw [← ha x.1 y.1, ← hb x.2 y.2, hxi, hys]
  ring

theorem isDPInt_C_C_int (z : ℤ) : IsDPInt (C (C (z : ℚ))) := by
  intro i s
  rw [coeff_C]
  split_ifs with hi
  · subst hi
    rw [coeff_C]
    split_ifs with hs
    · subst hs; exact ⟨z, by simp⟩
    · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

theorem isDPInt_one : IsDPInt 1 := by
  have := isDPInt_C_C_int 1
  simpa using this

/-- `γ_r(A) = A^r / r!`. -/
theorem isDPInt_dpowA (r : ℕ) : IsDPInt (C (C ((r.factorial : ℚ)⁻¹)) * X ^ r) := by
  intro i s
  rw [coeff_C_mul_X_pow]
  split_ifs with hi
  · subst hi
    rw [coeff_C]
    split_ifs with hs
    · subst hs
      exact ⟨1, by
        rw [Nat.factorial_zero, Nat.cast_one, mul_one,
          inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i)]; simp⟩
    · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

/-- `γ_k(B) = B^k / k!`. -/
theorem isDPInt_dpowB (k : ℕ) : IsDPInt (C (C ((k.factorial : ℚ)⁻¹) * X ^ k)) := by
  intro i s
  rw [coeff_C]
  split_ifs with hi
  · subst hi
    rw [coeff_C_mul_X_pow]
    split_ifs with hs
    · subst hs
      exact ⟨1, by
        rw [Nat.factorial_zero, Nat.cast_one, mul_one,
          inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero s)]; simp⟩
    · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

theorem isDPInt_C_one_add_X_pow (r : ℕ) : IsDPInt (C ((1 + X : R) ^ r)) := by
  intro i s
  rw [coeff_C]
  split_ifs with hi
  · subst hi
    rw [add_comm, coeff_X_add_one_pow]
    exact ⟨(r.choose s * s.factorial : ℕ), by push_cast; ring⟩
  · exact ⟨0, by simp⟩

/-- Divided binomial theorem: `(u + v)^j / j! = Σ_r u^r/r! · v^{j-r}/(j-r)!`. -/
theorem dpow_add_S (j : ℕ) (u v : S) :
    C (C ((j.factorial : ℚ)⁻¹)) * (u + v) ^ j =
      ∑ r ∈ Finset.range (j + 1), (C (C ((r.factorial : ℚ)⁻¹)) * u ^ r) *
        (C (C (((j - r).factorial : ℚ)⁻¹)) * v ^ (j - r)) := by
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have hc : ((j.choose r : ℕ) : S) * C (C ((j.factorial : ℚ)⁻¹)) =
      C (C ((r.factorial : ℚ)⁻¹)) * C (C (((j - r).factorial : ℚ)⁻¹)) := by
    rw [← map_natCast C, ← map_natCast C, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    have h := Nat.choose_mul_factorial_mul_factorial (show r ≤ j by omega)
    have h2 : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    have h3 : ((j - r).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j - r)
    have h4 : ((j.choose r : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (show r ≤ j by omega)).ne'
    rw [← h]
    push_cast
    field_simp
  calc C (C ((j.factorial : ℚ)⁻¹)) * (u ^ r * v ^ (j - r) * (j.choose r : S))
      = (((j.choose r : ℕ) : S) * C (C ((j.factorial : ℚ)⁻¹))) * (u ^ r * v ^ (j - r)) := by ring
    _ = _ := by rw [hc]; ring

/-- `γ_j(c) = c^j / j!` is divided-power integral. -/
theorem isDPInt_dpow_cA (j : ℕ) : IsDPInt (C (C ((j.factorial : ℚ)⁻¹)) * cA ^ j) := by
  rw [cA, dpow_add_S]
  apply isDPInt_sum
  intro r _
  apply isDPInt_mul
  · rw [mul_pow, ← map_pow, ← mul_assoc]
    exact isDPInt_mul (isDPInt_dpowA r) (isDPInt_C_one_add_X_pow r)
  · rw [← map_pow, ← map_mul]
    exact isDPInt_dpowB (j - r)

/-! ### Support of `c^k` -/

theorem cA_pow_succ (k : ℕ) : cA ^ (k + 1) = cA ^ k * X * C (1 + X) + cA ^ k * C X := by
  rw [pow_succ]; unfold cA; ring

theorem coeff_cA_pow_eq_zero (k : ℕ) : ∀ i s, (k < i ∨ k < s) → ((cA ^ k).coeff i).coeff s = 0 := by
  induction k with
  | zero =>
    intro i s h
    rw [pow_zero, coeff_one]
    split_ifs with hi
    · subst hi
      rw [coeff_one]
      split_ifs with hs
      · omega
      · rfl
    · rfl
  | succ k ih =>
    intro i s h
    rw [cA_pow_succ, coeff_add, coeff_mul_C, coeff_mul_C, coeff_add]
    rcases i with _ | i
    · rw [coeff_mul_X_zero, zero_mul, coeff_zero, zero_add]
      rcases s with _ | s
      · rw [coeff_mul_X_zero]
      · rw [coeff_mul_X]
        exact ih 0 s (by omega)
    · rw [coeff_mul_X, mul_add, mul_one, coeff_add]
      have h1 : ((cA ^ k).coeff i).coeff s = 0 := ih i s (by omega)
      have h2 : ((cA ^ k).coeff i * X).coeff s = 0 := by
        rcases s with _ | s
        · rw [coeff_mul_X_zero]
        · rw [coeff_mul_X]; exact ih i s (by omega)
      have h3 : ((cA ^ k).coeff (i + 1) * X).coeff s = 0 := by
        rcases s with _ | s
        · rw [coeff_mul_X_zero]
        · rw [coeff_mul_X]; exact ih (i + 1) s (by omega)
      rw [h1, h2, h3]
      ring

/-! ### High coefficients of `F_M` are divisible by `N` when `M ≥ 2N + 1` -/

theorem κ_eq (j : ℕ) (hj : 1 ≤ j) :
    κ j = (-1) ^ (j + 1) * ((j - 1).factorial : ℚ) * ((j.factorial : ℚ)⁻¹) := by
  have h := Nat.mul_factorial_pred (show j ≠ 0 by omega)
  have h1 : ((j - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (j : ℚ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  rw [κ, ← h]
  push_cast
  field_simp

theorem FM_eq_sum (M : ℕ) : FM M = ∑ j ∈ Finset.Ico 1 (M + 1),
    C (C ((-1) ^ (j + 1) * ((j - 1).factorial : ℚ))) *
      (C (C ((j.factorial : ℚ)⁻¹)) * cA ^ j - C (C ((j.factorial : ℚ)⁻¹)) * X ^ j -
        C (C ((j.factorial : ℚ)⁻¹) * X ^ j)) := by
  rw [FM, LM, LM, LM, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [κ_eq j hj.1]
  simp only [map_mul, map_pow]
  ring

theorem exists_sum_eq_mul (N : ℕ) (t : Finset ℕ) (f : ℕ → ℚ)
    (h : ∀ j ∈ t, ∃ z : ℤ, f j = N * z) : ∃ z : ℤ, ∑ j ∈ t, f j = N * z := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨z1, hz1⟩ := h a (Finset.mem_insert_self a t)
    obtain ⟨z2, hz2⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    exact ⟨z1 + z2, by rw [Finset.sum_insert ha, hz1, hz2]; push_cast; ring⟩

/-- **Claim 2.** If `M ≥ 2N + 1`, every coefficient of `F_M` in the basis `A^i B^s/(i! s!)` is
divisible by `N`. -/
theorem FM_coeff_dvd (N M : ℕ) (hN : 0 < N) (hNM : 2 * N + 1 ≤ M) (i s : ℕ) :
    ∃ z : ℤ, ((FM M).coeff i).coeff s * (i.factorial : ℚ) * (s.factorial : ℚ) = N * z := by
  by_cases hlow : i + s ≤ M
  · exact ⟨0, by rw [coeff_FM_eq_zero M i s hlow]; simp⟩
  push Not at hlow
  rw [FM_eq_sum, finsetSum_coeff, finsetSum_coeff, Finset.sum_mul, Finset.sum_mul]
  apply exists_sum_eq_mul
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [coeff_C_mul, coeff_C_mul]
  set G : S := C (C ((j.factorial : ℚ)⁻¹)) * cA ^ j - C (C ((j.factorial : ℚ)⁻¹)) * X ^ j -
    C (C ((j.factorial : ℚ)⁻¹) * X ^ j) with hG
  have hGint : IsDPInt G := by
    rw [hG, sub_eq_add_neg, sub_eq_add_neg]
    refine isDPInt_add (isDPInt_add (isDPInt_dpow_cA j) (isDPInt_neg (isDPInt_dpowA j)))
      (isDPInt_neg (isDPInt_dpowB j))
  obtain ⟨w, hw⟩ := hGint i s
  by_cases hjN : N + 1 ≤ j
  · obtain ⟨e, he⟩ := Nat.dvd_factorial hN (show N ≤ j - 1 by omega)
    refine ⟨(-1) ^ (j + 1) * e * w, ?_⟩
    rw [show (-1) ^ (j + 1) * ((j - 1).factorial : ℚ) * (G.coeff i).coeff s * (i.factorial : ℚ) *
        (s.factorial : ℚ) = (-1) ^ (j + 1) * ((j - 1).factorial : ℚ) *
          ((G.coeff i).coeff s * (i.factorial : ℚ) * (s.factorial : ℚ)) by ring, hw, he]
    push_cast
    ring
  · have h1 : ((C (C ((j.factorial : ℚ)⁻¹)) * cA ^ j : S).coeff i).coeff s = 0 := by
      rw [coeff_C_mul, coeff_C_mul, coeff_cA_pow_eq_zero j i s (by omega), mul_zero]
    have h2 : ((C (C ((j.factorial : ℚ)⁻¹)) * X ^ j : S).coeff i).coeff s = 0 := by
      rw [coeff_C_mul_X_pow]
      split_ifs with hij
      · rw [coeff_C]
        split_ifs with hs0
        · omega
        · rfl
      · rfl
    have h3 : ((C (C ((j.factorial : ℚ)⁻¹) * X ^ j) : S).coeff i).coeff s = 0 := by
      rw [coeff_C]
      split_ifs with hi0
      · rw [coeff_C_mul_X_pow]
        split_ifs with hsj
        · omega
        · rfl
      · rfl
    have hG0 : (G.coeff i).coeff s = 0 := by
      rw [hG, coeff_sub, coeff_sub, coeff_sub, coeff_sub, h1, h2, h3, sub_zero, sub_zero]
    exact ⟨0, by rw [hG0]; simp⟩

end PBLogPoly

end LogPolySection

namespace HDec
namespace PkgI4
namespace PanBergerSplit

open Ideal

variable (p : ℕ) [Fact p.Prime]



/-- An element of `𝓞_ℂ_p♭` divisible by every power of `p♭` is zero. -/
theorem tilt_eq_zero_of_dvd (ϖ : PreTilt 𝓞_ℂ_[p] p) (hϖ : ϖ.untilt = p) (c : PreTilt 𝓞_ℂ_[p] p)
    (h : ∀ n, ϖ ^ n ∣ c) : c = 0 := by
  have h0 : c.untilt = 0 := by
    apply IsHausdorff.haus' (I := span {(p : 𝓞_ℂ_[p])})
    intro n
    obtain ⟨d, rfl⟩ := h n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, map_mul, map_pow, hϖ]
    exact dvd_mul_right _ _
  apply Perfection.ext
  intro n
  change PreTilt.coeff n c = PreTilt.coeff n 0
  rw [← ZInQ.Contrib.G9.BdrKer.Cp.mk_root, map_zero]
  have : ZInQ.Contrib.G9.BdrKer.Cp.root c n ^ p ^ n = 0 := by
    rw [ZInQ.Contrib.G9.BdrKer.Cp.root_pow, h0]
  rw [pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at this
  rw [this, map_zero]

/-- `p` is regular modulo `ξ^n` in `A_inf`. -/
theorem mem_xi_pow_of_p_mul (n : ℕ) : ∀ a : Ainf p,
    (p : Ainf p) * a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} → a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := by
  induction n with
  | zero => intro a _; rw [pow_zero, Ideal.span_singleton_one]; trivial
  | succ n ih =>
    intro a ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    have hθ : theta p a = 0 := by
      apply ZInQ.Contrib.G9.BdrKer.Cp.p_regular p
      have := congrArg (theta p) hc
      rw [map_mul, map_mul, map_pow, map_natCast] at this
      rw [← this]
      have hx : theta p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
        rw [← RingHom.mem_ker]
        change (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
        rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
        exact Ideal.mem_span_singleton_self _
      rw [hx, zero_pow (Nat.succ_ne_zero n), mul_zero]
    have ha' : a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p)} := by
      rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
      exact hθ
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.mp ha'
    have hξ : (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ≠ 0 := ZInQ.Contrib.G9.BdrKer.Cp.xi_ne_zero p
    have h2 : (p : Ainf p) * a' = c * (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n := by
      apply mul_left_cancel₀ hξ
      linear_combination hc.symm
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (ih a' (Ideal.mem_span_singleton'.mpr ⟨c, h2.symm⟩))
    exact Ideal.mem_span_singleton'.mpr ⟨d, by rw [← hd, pow_succ]; ring⟩

theorem mem_xi_pow_of_p_pow_mul (n e : ℕ) (a : Ainf p)
    (h : (p : Ainf p) ^ e * a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n}) : a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := by
  induction e generalizing a with
  | zero => simpa using h
  | succ e ih =>
    apply ih
    apply mem_xi_pow_of_p_mul
    rw [pow_succ] at h
    simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- `A_inf` is `ξ`-adically separated on non-zero elements. -/
theorem exists_not_mem_xi_pow (x : Ainf p) (hx : x ≠ 0) : ∃ n, x ∉ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := by
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x hx
  by_contra hcon
  push Not at hcon
  apply hb
  have hb' : ∀ n, b ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := fun n => mem_xi_pow_of_p_pow_mul p n m b (hcon n)
  have h0 : WittVector.constantCoeff (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = -(ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) := by
    rw [ZInQ.Contrib.G9.BdrKer.Cp.xi, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
    simp
  apply tilt_eq_zero_of_dvd p (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p)
    (ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat p)
  intro n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hb' n)
  have := congrArg WittVector.constantCoeff hc
  rw [map_mul, map_pow, h0] at this
  refine ⟨(-1) ^ n * WittVector.constantCoeff c, ?_⟩
  change b.coeff 0 = _
  rw [← WittVector.constantCoeff_apply, ← this, neg_pow]
  ring

/-- Every non-zero `x ∈ A_inf` is `ξ^s · w` with `θ(w) ≠ 0`. -/
theorem eq_xi_pow_mul (x : Ainf p) (hx : x ≠ 0) :
    ∃ (s : ℕ) (w : Ainf p), x = (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ s * w ∧ theta p w ≠ 0 := by
  classical
  have hex := exists_not_mem_xi_pow p x hx
  let N := Nat.find hex
  have hN : x ∉ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ N} := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0; apply hN; rw [h0, pow_zero, Ideal.span_singleton_one]; trivial
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hxM : x ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ M} := by
    have := Nat.find_min hex (show M < N by omega)
    push Not at this
    exact this
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hxM
  refine ⟨M, w, by rw [← hw, mul_comm], fun hθ => hN ?_⟩
  have : w ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p)} := by
    rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]; exact hθ
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp this
  rw [hM, ← hw]
  exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [Nat.succ_eq_add_one, pow_succ]; ring⟩

theorem teich_sub_one_ne_zero {ε : PreTilt 𝓞_ℂ_[p] p} (hne : ε ≠ 1) :
    WittVector.teichmuller p ε - 1 ≠ 0 := by
  intro h
  apply hne
  have h1 : WittVector.teichmuller p ε = 1 := sub_eq_zero.mp h
  have := congrArg (fun w => WittVector.coeff w 0) h1
  simpa [WittVector.teichmuller_coeff_zero] using this

/-- `ι(a) ∈ ξ^k A_inf[1/p]` implies `a ∈ ξ^k A_inf`. -/
theorem mem_xi_pow_of_algebraMap (k : ℕ) (a : Ainf p)
    (h : algebraMap (Ainf p) (AinfP p) a ∈ span {algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ k}) :
    a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ k} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : Ainf p)) y
  obtain ⟨e, he⟩ := s.2
  apply mem_xi_pow_of_p_pow_mul p k e
  have hinj := IsLocalization.injective (AinfP p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (ZInQ.Contrib.G9.BdrKer.Cp.witt_p_ne_zero p))
  have : (p : Ainf p) ^ e * a = b * (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ k := by
    apply hinj
    have hs := IsLocalization.mk'_spec (AinfP p) b s
    simp only at he
    dsimp only at hy
    rw [map_mul, map_mul, map_pow, ← hy, ← hs, ← he]
    simp only [map_pow]
    ring
  exact Ideal.mem_span_singleton'.mpr ⟨b, this.symm⟩

/-! ### The lattice bound: `N! · A_cris^0 ⊆ A_inf + ξ^N A_inf[1/p]` -/

section Lattice

variable (N : ℕ)

/-- `ξ^N A_inf[1/p]`. -/
abbrev xiIdeal : Ideal (AinfP p) := span {algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ N}

/-- `A_inf[1/p] / ξ^N`. -/
abbrev Qn := AinfP p ⧸ xiIdeal p N

/-- The class of `ξ^i / i!`. -/
def latGen (i : ℕ) : Qn p N :=
  Ideal.Quotient.mk _ (qpToLoc p ((i.factorial : ℚ_[p])⁻¹) * algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i)

/-- The `A_inf`-span of the classes of `ξ^i / i!`. -/
def latG : Submodule (Ainf p) (Qn p N) := Submodule.span (Ainf p) (Set.range (latGen p N))

theorem algebraMap_Qn (a : Ainf p) :
    algebraMap (Ainf p) (Qn p N) a = Ideal.Quotient.mk _ (algebraMap (Ainf p) (AinfP p) a) := rfl

theorem smul_Qn (r : Ainf p) (q : Qn p N) : r • q = algebraMap (Ainf p) (Qn p N) r * q :=
  Algebra.smul_def r q

theorem latGen_mul (i j : ℕ) :
    latGen p N i * latGen p N j = ((i + j).choose j : Ainf p) • latGen p N (i + j) := by
  rw [smul_Qn, latGen, latGen, latGen, algebraMap_Qn, ← map_mul, ← map_mul]
  congr 1
  have key : ((i + j).choose j : ℚ_[p]) * ((i + j).factorial : ℚ_[p])⁻¹ =
      (i.factorial : ℚ_[p])⁻¹ * (j.factorial : ℚ_[p])⁻¹ := by
    have h := Nat.add_choose_mul_factorial_mul_factorial i j
    have hi : (i.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hj : (j.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hij : ((i + j).factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i + j)
    field_simp
    rw [← h]
    push_cast
    ring
  have hc : algebraMap (Ainf p) (AinfP p) ((i + j).choose j : Ainf p) =
      qpToLoc p ((i + j).choose j : ℚ_[p]) := by
    rw [map_natCast, map_natCast]
  rw [hc, pow_add]
  calc qpToLoc p (i.factorial : ℚ_[p])⁻¹ * algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i *
        (qpToLoc p (j.factorial : ℚ_[p])⁻¹ * algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ j)
      = qpToLoc p ((i.factorial : ℚ_[p])⁻¹ * (j.factorial : ℚ_[p])⁻¹) *
        (algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i * algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ j) := by
        rw [map_mul]; ring
    _ = _ := by rw [← key, map_mul]; ring

theorem latG_mul_mem {x y : Qn p N} (hx : x ∈ latG p N) (hy : y ∈ latG p N) :
    x * y ∈ latG p N := by
  have h1 : latG p N * latG p N ≤ latG p N := by
    rw [latG, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show latGen p N i * latGen p N j ∈ latG p N
    rw [latGen_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i + j, rfl⟩)
  exact h1 (Submodule.mul_mem_mul hx hy)

theorem latGen_zero : latGen p N 0 = 1 := by
  rw [latGen, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, inv_one, map_one, map_one]

/-- The subring of `A_inf[1/p]` of elements whose class lies in `latG`. -/
def latSub : Subring (AinfP p) where
  carrier := {z | Ideal.Quotient.mk (xiIdeal p N) z ∈ latG p N}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
    exact latG_mul_mem p N ha hb
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one]
    rw [← latGen_zero]
    exact Submodule.subset_span ⟨0, rfl⟩
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact Submodule.add_mem _ ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact Submodule.zero_mem _
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, map_neg] at ha ⊢
    exact Submodule.neg_mem _ ha

theorem acris0_le_latSub : Acris0 p ≤ latSub p N := by
  rw [Acris0, Subring.closure_le]
  rintro z (⟨a, rfl⟩ | ⟨n, x, hx, rfl⟩)
  · show Ideal.Quotient.mk _ _ ∈ latG p N
    rw [← algebraMap_Qn, Algebra.algebraMap_eq_smul_one, ← latGen_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · have hx' : x ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p)} := by
      rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]; exact hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
    show Ideal.Quotient.mk _ _ ∈ latG p N
    have : Ideal.Quotient.mk (xiIdeal p N) (dpow p n (b * (ZInQ.Contrib.G9.BdrKer.Cp.xi p))) = b ^ n • latGen p N n := by
      rw [smul_Qn, latGen, algebraMap_Qn, ← map_mul, dpow]
      congr 1
      rw [map_mul, mul_pow, map_pow]
      ring
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

theorem latGen_eq_zero {i : ℕ} (hi : N ≤ i) : latGen p N i = 0 := by
  rw [latGen, Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.mul_mem_left
  rw [Ideal.mem_span_singleton']
  exact ⟨algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ (i - N), by rw [← pow_add]; congr 1; omega⟩

theorem latG_bound {q : Qn p N} (hq : q ∈ latG p N) :
    ∃ a : Ainf p, (N.factorial : Qn p N) * q = algebraMap (Ainf p) (Qn p N) a := by
  induction hq using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    by_cases hi : N ≤ i
    · exact ⟨0, by rw [latGen_eq_zero p N hi, mul_zero, map_zero]⟩
    · obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial (show i ≤ N by omega)
      refine ⟨(c : Ainf p) * (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i, ?_⟩
      rw [algebraMap_Qn, latGen, ← map_natCast (Ideal.Quotient.mk (xiIdeal p N)), ← map_mul]
      congr 1
      have hi0 : (i.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
      have e1 : (N.factorial : AinfP p) * qpToLoc p (i.factorial : ℚ_[p])⁻¹ = (c : AinfP p) := by
        rw [← map_natCast (qpToLoc p), ← map_mul, hc]
        push_cast
        rw [mul_comm (i.factorial : ℚ_[p]), mul_assoc, mul_inv_cancel₀ hi0, mul_one, map_natCast]
      rw [map_mul, map_natCast, map_pow, ← e1]
      ring
  | zero => exact ⟨0, by rw [mul_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [mul_add, ha, hb, map_add]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨r * a, ?_⟩
    rw [smul_Qn, mul_left_comm, ha, map_mul]

end Lattice

/-! ### `p^m · ∏ log [ε_i] ≠ 0` in `A_cris` -/

/-- The `ε` with `ε^♯ = 1`, `ε ≠ 1` (those whose `log [ε]` are inverted in `B_cris`). -/
abbrev TEps := {ε : PreTilt 𝓞_ℂ_[p] p // PreTilt.untilt ε = 1 ∧ ε ≠ 1}

/-- `log [ε] ∈ A_cris`. -/
def logOf (e : TEps p) : Acris p := logT p (theta_teich_sub_one p e.2.1)

/-- `Σ_{1 ≤ j ≤ M} (-1)^{j+1} x^{j-1}/j`, so that the partial log sum is `x · Vsum`. -/
def Vsum (x : Ainf p) (M : ℕ) : AinfP p :=
  ∑ j ∈ Finset.Ico 1 (M + 1), (-1) ^ (j + 1) * ((j - 1).factorial : AinfP p) *
    (qpToLoc p ((j.factorial : ℚ_[p])⁻¹) * algebraMap (Ainf p) (AinfP p) x ^ (j - 1))

theorem logPartialVal_eq (x : Ainf p) (M : ℕ) :
    logPartialVal p x M = algebraMap (Ainf p) (AinfP p) x * Vsum p x M := by
  rw [logPartialVal, Vsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [logTerm, dpow, Nat.add_sub_cancel, pow_succ]
  ring

theorem thetaP_algebraMap (a : Ainf p) :
    fontaineThetaInvertP 𝓞_ℂ_[p] p (algebraMap (Ainf p) (AinfP p) a) =
      algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p])) (theta p a) :=
  IsLocalization.Away.lift_eq (p : Ainf p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : 𝓞_ℂ_[p])) a

theorem thetaP_Vsum {x : Ainf p} (hx : theta p x = 0) {M : ℕ} (hM : 1 ≤ M) :
    fontaineThetaInvertP 𝓞_ℂ_[p] p (Vsum p x M) = 1 := by
  have h0 : fontaineThetaInvertP 𝓞_ℂ_[p] p (algebraMap (Ainf p) (AinfP p) x) = 0 := by
    rw [thetaP_algebraMap, hx, map_zero]
  rw [Vsum, map_sum, Finset.sum_eq_single 1]
  · simp
  · intro j hj hj1
    rw [Finset.mem_Ico] at hj
    simp only [map_mul, map_pow, h0, zero_pow (show j - 1 ≠ 0 by omega), mul_zero]
  · intro h; exfalso; apply h; rw [Finset.mem_Ico]; omega

theorem algebraMap_O_injective :
    Function.Injective (algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p]))) :=
  IsLocalization.injective _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p))

theorem natCast_O_ne_zero {k : ℕ} (hk : k ≠ 0) : (k : 𝓞_ℂ_[p]) ≠ 0 := by
  intro h
  have h1 : ((k : 𝓞_ℂ_[p]) : ℂ_[p]) = 0 := by rw [h]; rfl
  push_cast at h1
  exact hk (by exact_mod_cast h1)

theorem theta_xi : theta p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
  rw [← RingHom.mem_ker]
  change (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
  exact Ideal.mem_span_singleton_self _

theorem prod_logPartialVal_decomp (l : List (TEps p)) (s : TEps p → ℕ) (w : TEps p → Ainf p)
    (hsw : ∀ e : TEps p, WittVector.teichmuller p e.1 - 1 = (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ s e * w e) (M : ℕ) :
    (l.map fun e => logPartialVal p (WittVector.teichmuller p e.1 - 1) M).prod =
      algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ (l.map s).sum * algebraMap (Ainf p) (AinfP p) (l.map w).prod *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) M).prod := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [ih, logPartialVal_eq, hsw e]
    simp only [map_mul, map_pow, pow_add]
    ring

/-- `A_inf → A_cris^0`. -/
def ainfToAcris0 : Ainf p →+* Acris0 p :=
  (algebraMap (Ainf p) (AinfP p)).codRestrict (Acris0 p) (algebraMap_mem p)

theorem coe_ainfToAcris0 (y : Ainf p) :
    (ainfToAcris0 p y : AinfP p) = algebraMap (Ainf p) (AinfP p) y := rfl

/-- The image of `y ∈ A_inf` in `A_cris`. -/
def ofAinf (y : Ainf p) : Acris p :=
  algebraMap (Acris0 p) (Acris p) (ainfToAcris0 p y)

theorem ofAinf_eq (y : Ainf p) : ofAinf p y = AdicCompletion.of (Ideal.span {(p : Acris0 p)})
    (Acris0 p) (ainfToAcris0 p y) := by
  rw [ofAinf]
  erw [AdicCompletion.algebraMap_apply]

theorem evalₐ_ofAinf (y : Ainf p) (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n (ofAinf p y) =
      Ideal.Quotient.mk _ (ainfToAcris0 p y) := by
  rw [ofAinf_eq, AdicCompletion.evalₐ_of]

theorem ofAinf_one : ofAinf p 1 = 1 := by
  rw [ofAinf, map_one, map_one]

/-- Level `n` of a relation `p^m · ∏ log [ε_i] · y = 0` in `A_cris`. -/
theorem exists_of_eval_eq_zero (l : List (TEps p)) (m : ℕ) (y : Ainf p) (n : ℕ)
    (hP : (p : Acris p) ^ m * (l.map (logOf p)).prod * ofAinf p y = 0) :
    ∃ z : Acris0 p, (z : AinfP p) * (p : AinfP p) ^ n = (p : AinfP p) ^ m *
        (l.map fun e => logPartialVal p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod *
        algebraMap (Ainf p) (AinfP p) y := by
  rw [← Nat.cast_pow] at hP
  have hev := congrArg (AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n) hP
  rw [map_zero, map_mul, map_mul, map_natCast, map_list_prod, List.map_map,
    evalₐ_ofAinf] at hev
  have hfac : (AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n) ∘ logOf p =
      fun e => Ideal.Quotient.mk _ (logPartial p (theta_teich_sub_one p e.2.1) (p ^ n)) :=
    funext fun e => evalₐ_logT p _ n
  rw [hfac] at hev
  have hP' : Ideal.Quotient.mk ((span {(p : Acris0 p)}) ^ n)
      (l.map fun e => logPartial p (theta_teich_sub_one p e.2.1) (p ^ n)).prod =
      (l.map fun e => Ideal.Quotient.mk ((span {(p : Acris0 p)}) ^ n)
        (logPartial p (theta_teich_sub_one p e.2.1) (p ^ n))).prod := by
    rw [map_list_prod, List.map_map]
    rfl
  have hPv : ((l.map fun e => logPartial p (theta_teich_sub_one p e.2.1) (p ^ n)).prod :
      AinfP p) = (l.map fun e => logPartialVal p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod := by
    rw [← (Acris0 p).coe_subtype, map_list_prod, List.map_map]
    rfl
  rw [← hP'] at hev
  generalize hyA : ainfToAcris0 p y = yA at hev
  have hyv : (yA : AinfP p) = algebraMap (Ainf p) (AinfP p) y := by rw [← hyA]; rfl
  have hmem : (((p ^ m : ℕ) : Acris0 p) *
      (l.map fun e => logPartial p (theta_teich_sub_one p e.2.1) (p ^ n)).prod * yA) ∈
      (span {(p : Acris0 p)}) ^ n := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_mul, map_natCast]
    exact hev
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  have := congrArg (fun x : Acris0 p => (x : AinfP p)) hz
  simp only [Subring.coe_mul, Subring.coe_pow] at this
  rw [hPv, hyv, show ((((p ^ m : ℕ) : Acris0 p)) : AinfP p) = (p : AinfP p) ^ m by simp] at this
  exact this

/-- **Main lemma.** For every finite family of `ε_i` with `ε_i^♯ = 1`, `ε_i ≠ 1`, every `m` and
every `y ≠ 0` in `A_inf`, `p^m · ∏ log [ε_i] · y ≠ 0` in `A_cris`. -/
theorem pow_mul_prod_logOf_mul_ne_zero (l : List (TEps p)) (m : ℕ) (y : Ainf p) (hy : y ≠ 0) :
    (p : Acris p) ^ m * (l.map (logOf p)).prod * ofAinf p y ≠ 0 := by
  classical
  have hdec : ∀ e : TEps p, ∃ (s : ℕ) (w : Ainf p),
      WittVector.teichmuller p e.1 - 1 = (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ s * w ∧ theta p w ≠ 0 :=
    fun e => eq_xi_pow_mul p _ (teich_sub_one_ne_zero p e.2.2)
  choose s w hsw hw using hdec
  obtain ⟨s0, wy, hy0, hwy⟩ := eq_xi_pow_mul p y hy
  set X := algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) with hX
  have hX0 : X ≠ 0 := ZInQ.Contrib.G9.BdrKer.Cp.xi'_ne_zero p
  set S := s0 + (l.map s).sum with hS
  set N := S + 1 with hN
  set Wt := wy * (l.map w).prod with hWt
  have hdecomp : ∀ M : ℕ,
      (l.map fun e => logPartialVal p (WittVector.teichmuller p e.1 - 1) M).prod *
        algebraMap (Ainf p) (AinfP p) y
      = X ^ S * algebraMap (Ainf p) (AinfP p) Wt *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) M).prod := by
    intro M
    rw [prod_logPartialVal_decomp p l s w hsw M, hy0, hS, hWt]
    simp only [map_mul, map_pow, pow_add]
    ring
  set c : 𝓞_ℂ_[p] := (N.factorial : 𝓞_ℂ_[p]) * (p : 𝓞_ℂ_[p]) ^ m * theta p Wt with hc
  have hc0 : c ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (natCast_O_ne_zero p (Nat.factorial_ne_zero N))
      (pow_ne_zero _ (ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p))) ?_
    rw [hWt, map_mul, map_list_prod, List.map_map]
    refine mul_ne_zero hwy ?_
    intro h0
    rw [List.prod_eq_zero_iff] at h0
    obtain ⟨e, _, he⟩ := List.mem_map.mp h0
    exact hw e he
  intro hP
  have key : ∀ n : ℕ, ∃ a' : Ainf p, c = (p : 𝓞_ℂ_[p]) ^ n * theta p a' := by
    intro n
    obtain ⟨z, hzAP⟩ := exists_of_eval_eq_zero p l m y n hP
    -- the lattice
    obtain ⟨a, ha⟩ := latG_bound p N (acris0_le_latSub p N z.2)
    rw [algebraMap_Qn, ← map_natCast (Ideal.Quotient.mk (xiIdeal p N)), ← map_mul,
      Ideal.Quotient.eq, Ideal.mem_span_singleton'] at ha
    obtain ⟨w0, hw0⟩ := ha
    -- the main identity in `A_inf[1/p]`
    have hmain : (N.factorial : AinfP p) * (p : AinfP p) ^ m * X ^ S *
        algebraMap (Ainf p) (AinfP p) Wt *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod =
        (p : AinfP p) ^ n * (algebraMap (Ainf p) (AinfP p) a + w0 * X ^ N) := by
      have h1 := congrArg (fun y => (N.factorial : AinfP p) * y) hzAP
      simp only [mul_assoc] at h1
      rw [hdecomp] at h1
      have h2 : (N.factorial : AinfP p) * (z : AinfP p) =
          algebraMap (Ainf p) (AinfP p) a + w0 * X ^ N := by
        rw [← hX] at hw0
        linear_combination -hw0
      linear_combination -h1 + (p : AinfP p) ^ n * h2
    -- `a ∈ ξ^S A_inf`
    have haS : a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ S} := by
      apply mem_xi_pow_of_p_pow_mul p S n
      apply mem_xi_pow_of_algebraMap
      rw [Ideal.mem_span_singleton']
      refine ⟨(N.factorial : AinfP p) * (p : AinfP p) ^ m *
        algebraMap (Ainf p) (AinfP p) Wt *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod -
        (p : AinfP p) ^ n * w0 * X, ?_⟩
      simp only [map_mul, map_pow, map_natCast]
      rw [hN, pow_succ] at hmain
      linear_combination hmain
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.mp haS
    refine ⟨a', ?_⟩
    have hcancel : (N.factorial : AinfP p) * (p : AinfP p) ^ m *
        algebraMap (Ainf p) (AinfP p) Wt *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod =
        (p : AinfP p) ^ n * (algebraMap (Ainf p) (AinfP p) a' + w0 * X) := by
      apply mul_left_cancel₀ (pow_ne_zero S hX0)
      rw [hN, pow_succ] at hmain
      simp only [map_mul, map_pow] at hmain ⊢
      linear_combination hmain
    have hθ := congrArg (fontaineThetaInvertP 𝓞_ℂ_[p] p) hcancel
    have hV : fontaineThetaInvertP 𝓞_ℂ_[p] p
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod = 1 := by
      rw [map_list_prod, List.map_map]
      apply List.prod_eq_one
      intro y hy
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hy
      exact thetaP_Vsum p (theta_teich_sub_one p e.2.1) (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
    have hXθ : fontaineThetaInvertP 𝓞_ℂ_[p] p X = 0 := by
      rw [hX, thetaP_algebraMap, theta_xi, map_zero]
    simp only [map_mul, map_add, map_pow, map_natCast, hV, hXθ, thetaP_algebraMap, mul_zero,
      add_zero, mul_one] at hθ
    apply algebraMap_O_injective p
    rw [hc]
    simp only [map_mul, map_pow, map_natCast] at hθ ⊢
    linear_combination hθ
  apply hc0
  apply IsHausdorff.haus' (I := span {(p : 𝓞_ℂ_[p])})
  intro n
  obtain ⟨a', ha'⟩ := key n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ha']
  exact dvd_mul_right _ _

/-- **Main lemma**, `y = 1`: `p^m · ∏ log [ε_i] ≠ 0` in `A_cris`. -/
theorem pow_mul_prod_logOf_ne_zero (l : List (TEps p)) (m : ℕ) :
    (p : Acris p) ^ m * (l.map (logOf p)).prod ≠ 0 := by
  have := pow_mul_prod_logOf_mul_ne_zero p l m 1 one_ne_zero
  rwa [ofAinf_one, mul_one] at this

/-! ### Consequences: `B_cris^+`, `B_cris`, `B_st` are not zero; `t` is not nilpotent -/

/-- Every element of `tMonoid` is the image of a finite product of `log [ε_i]`. -/
theorem exists_list_of_mem_tMonoid {y : BcrisPlus p} (hy : y ∈ tMonoid p) :
    ∃ l : List (TEps p), y = algebraMap (Acris p) (BcrisPlus p) (l.map (logOf p)).prod := by
  induction hy using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨ε, h, hne, rfl⟩ := hx
    exact ⟨[⟨ε, h, hne⟩], by rw [List.map_singleton, List.prod_singleton]; rfl⟩
  | one => exact ⟨[], by rw [List.map_nil, List.prod_nil, map_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l₁, rfl⟩ := hx
    obtain ⟨l₂, rfl⟩ := hy
    exact ⟨l₁ ++ l₂, by rw [List.map_append, List.prod_append, map_mul]⟩

theorem algebraMap_prod_logOf_ne_zero (l : List (TEps p)) :
    algebraMap (Acris p) (BcrisPlus p) (l.map (logOf p)).prod ≠ 0 := by
  intro h
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : Acris p)) (BcrisPlus p) _).mp h
  exact pow_mul_prod_logOf_ne_zero p l k hk

/-- **`0 ∉ tMonoid`**: no product of the `log [ε]` is zero in `B_cris^+`. -/
theorem zero_notMem_tMonoid : (0 : BcrisPlus p) ∉ tMonoid p := fun h => by
  obtain ⟨l, hl⟩ := exists_list_of_mem_tMonoid p h
  exact algebraMap_prod_logOf_ne_zero p l hl.symm

/-- **`B_cris^+ ≠ 0`.** -/
instance nontrivial_bcrisPlus : Nontrivial (BcrisPlus p) :=
  nontrivial_of_ne 1 0 (by simpa using algebraMap_prod_logOf_ne_zero p [])

/-- **`B_cris ≠ 0`.** -/
instance nontrivial_bcris : Nontrivial (Bcris p) := by
  refine nontrivial_of_ne 1 0 fun h => ?_
  have h' : algebraMap (BcrisPlus p) (Bcris p) 1 = 0 := by rw [map_one]; exact h
  obtain ⟨⟨m, hm⟩, hm1⟩ := (IsLocalization.map_eq_zero_iff (tMonoid p) (Bcris p) _).mp h'
  rw [mul_one] at hm1
  exact zero_notMem_tMonoid p (hm1 ▸ hm)

/-- **`B_st ≠ 0`.** -/
instance nontrivial_bst : Nontrivial (Bst p) := inferInstance

/-- `ℚ_p → B_st` is injective (so `ℚ_p ⊆ B_st^{G_K}` is a genuine subspace). -/
theorem algebraMap_qp_bst_injective : Function.Injective (algebraMap ℚ_[p] (Bst p)) :=
  (algebraMap ℚ_[p] (Bst p)).injective

/-- **`log [ε]` is not nilpotent in `B_cris^+`** (for `ε^♯ = 1`, `ε ≠ 1`). -/
theorem logOf_not_isNilpotent (e : TEps p) :
    ¬ IsNilpotent (algebraMap (Acris p) (BcrisPlus p) (logOf p e)) := by
  rintro ⟨k, hk⟩
  apply algebraMap_prod_logOf_ne_zero p (List.replicate k e)
  rw [List.map_replicate, List.prod_replicate, map_pow, hk]

/-- `log [ε] ≠ 0` in `A_cris`. -/
theorem logOf_ne_zero (e : TEps p) : logOf p e ≠ 0 := by
  have := pow_mul_prod_logOf_ne_zero p [e] 0
  simpa using this

/-- The image of `log [ε]` in `B_cris` is a unit, and `B_cris ≠ 0`, so it is non-zero. -/
theorem isUnit_logOf_bcris (e : TEps p) :
    IsUnit (algebraMap (BcrisPlus p) (Bcris p) (algebraMap (Acris p) (BcrisPlus p) (logOf p e))) :=
  IsLocalization.map_units (Bcris p)
    (⟨_, Submonoid.subset_closure ⟨e.1, e.2.1, e.2.2, rfl⟩⟩ : tMonoid p)

theorem logOf_bcris_ne_zero (e : TEps p) :
    algebraMap (BcrisPlus p) (Bcris p) (algebraMap (Acris p) (BcrisPlus p) (logOf p e)) ≠ 0 :=
  (isUnit_logOf_bcris p e).ne_zero

/-! ### There is an `ε` with `ε^♯ = 1`, `ε ≠ 1` (so `t` exists) -/

open ZInQ.Contrib.G9.BdrKer.Cp in
/-- If the components of `x ∈ 𝓞_ℂ_p♭` are the classes of a compatible system `c` of `p`-th
power roots, then `x^♯ = c 0`. -/
theorem untilt_eq_of_coeff (c : ℕ → 𝓞_ℂ_[p]) (hc : ∀ m, c (m + 1) ^ p = c m) (x : PreTilt 𝓞_ℂ_[p] p)
    (hx : ∀ m, PreTilt.coeff m x = Ideal.Quotient.mk _ (c m)) : x.untilt = c 0 := by
  have hpow : ∀ k, c k ^ p ^ k = c 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hc, ih]
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : 𝓞_ℂ_[p])})]
  intro n
  rw [SModEq.sub_mem, ZInQ.Contrib.G9.BdrKer.mem_span_pow_iff']
  have h1 : root x n - c n ∈ span {(p : 𝓞_ℂ_[p])} := by
    rw [← Ideal.Quotient.eq, mk_root, hx]
  have h2 := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.mp h1) n
  rw [root_pow, hpow] at h2
  obtain ⟨d, hd⟩ := h2
  exact ⟨p * d, by rw [hd]; ring⟩

open ZInQ.Contrib.G9.BdrKer.Cp in
theorem root_eq_of_coeff (c : ℕ → 𝓞_ℂ_[p]) (hc : ∀ m, c (m + 1) ^ p = c m) (x : PreTilt 𝓞_ℂ_[p] p)
    (hx : ∀ m, PreTilt.coeff m x = Ideal.Quotient.mk _ (c m)) (n : ℕ) : root x n = c n := by
  have := untilt_eq_of_coeff p (fun m => c (m + n)) (fun m => by
    simpa [Nat.add_right_comm] using hc (m + n)) (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) x)
    (fun m => by rw [PreTilt.coeff_iterate_frobeniusEquiv_symm, hx])
  simpa [ZInQ.Contrib.G9.BdrKer.Cp.root] using this

/-- A compatible system `1, ζ_p, ζ_{p²}, …` of `p`-power roots of unity in `ℂ_p`. -/
noncomputable def zetaSeq (ζ : ℂ_[p]) : ℕ → ℂ_[p]
  | 0 => 1
  | 1 => ζ
  | n + 2 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (zetaSeq ζ (n + 1))
      (Fact.out : p.Prime).pos)

theorem zetaSeq_succ_pow (ζ : ℂ_[p]) (hζ : ζ ^ p = 1) (n : ℕ) :
    zetaSeq p ζ (n + 1) ^ p = zetaSeq p ζ n := by
  rcases n with _ | n
  · simpa [zetaSeq] using hζ
  · exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (zetaSeq p ζ (n + 1))
      (Fact.out : p.Prime).pos)

theorem zetaSeq_pow (ζ : ℂ_[p]) (hζ : ζ ^ p = 1) (n : ℕ) : zetaSeq p ζ n ^ p ^ n = 1 := by
  induction n with
  | zero => simp [zetaSeq]
  | succ n ih => rw [pow_succ', pow_mul, zetaSeq_succ_pow p ζ hζ, ih]

theorem norm_zetaSeq_le (ζ : ℂ_[p]) (hζ : ζ ^ p = 1) (n : ℕ) : ‖zetaSeq p ζ n‖ ≤ 1 := by
  have h := congrArg norm (zetaSeq_pow p ζ hζ n)
  rw [norm_pow, norm_one] at h
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _
    (Fact.out : p.Prime).ne_zero)).mp h).le

/-- **There is `ε ∈ 𝓞_ℂ_p♭` with `ε^♯ = 1` and `ε ≠ 1`**: `ε = (1, ζ_p, ζ_{p²}, …)`. -/
theorem nonempty_tEps : Nonempty (TEps p) := by
  have hdeg : (Polynomial.cyclotomic p ℂ_[p]).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime (Fact.out : p.Prime)]
    have := (Fact.out : p.Prime).two_le
    exact_mod_cast (show p - 1 ≠ 0 by omega)
  obtain ⟨ζ, hroot⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot ζ p :=
    (Polynomial.isRoot_cyclotomic_iff_charZero (Fact.out : p.Prime).pos).mp hroot
  have hζ : ζ ^ p = 1 := hprim.pow_eq_one
  have hζ1 : ζ ≠ 1 := hprim.ne_one (Fact.out : p.Prime).one_lt
  let c : ℕ → 𝓞_ℂ_[p] := fun n => ⟨zetaSeq p ζ n,
    (ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mpr (norm_zetaSeq_le p ζ hζ n)⟩
  have hc : ∀ m, c (m + 1) ^ p = c m := fun m =>
    Subtype.ext (by simpa [c] using zetaSeq_succ_pow p ζ hζ m)
  let ε : PreTilt 𝓞_ℂ_[p] p := ⟨fun n => Ideal.Quotient.mk _ (c n), fun n => by
    rw [← map_pow, hc]⟩
  have hx : ∀ m, PreTilt.coeff m ε = Ideal.Quotient.mk _ (c m) := fun m => rfl
  refine ⟨⟨ε, ?_, ?_⟩⟩
  · rw [untilt_eq_of_coeff p c hc ε hx]
    exact Subtype.ext (by simp [c, zetaSeq])
  · intro h1
    have h2 := root_eq_of_coeff p c hc ε hx 1
    rw [h1] at h2
    apply hζ1
    have h3 : ZInQ.Contrib.G9.BdrKer.Cp.root (1 : PreTilt 𝓞_ℂ_[p] p) 1 = 1 := by
      simp [ZInQ.Contrib.G9.BdrKer.Cp.root]
    rw [h3] at h2
    have := congrArg Subtype.val h2
    simpa [c, zetaSeq] using this.symm

/-- So `tMonoid` contains a non-unit generator and `B_cris^+ → B_cris` inverts `t ≠ 0`. -/
theorem exists_t : ∃ e : TEps p, logOf p e ≠ 0 ∧
    ¬ IsNilpotent (algebraMap (Acris p) (BcrisPlus p) (logOf p e)) := by
  obtain ⟨e⟩ := nonempty_tEps p
  exact ⟨e, logOf_ne_zero p e, logOf_not_isNilpotent p e⟩

/-! ### The action of `G_{ℚ_p}`: a group action by ring automorphisms on `B_cris` -/

section Action

theorem cpAct_mul (σ τ : GQp p) (x : ℂ_[p]) : cpAct p (σ * τ) x = cpAct p σ (cpAct p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_cpAct p _) ((continuous_cpAct p σ).comp (continuous_cpAct p τ))
  | ih a => rw [cpAct_coe, cpAct_coe, cpAct_coe, AlgEquiv.mul_apply]

theorem cpAct_one (x : ℂ_[p]) : cpAct p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_cpAct p _) continuous_id
  | ih a => rw [cpAct_coe, AlgEquiv.one_apply]

theorem oAct_mul (σ τ : GQp p) : oAct p (σ * τ) = (oAct p σ).comp (oAct p τ) :=
  RingHom.ext fun x => Subtype.ext (cpAct_mul p σ τ x)

theorem oAct_one : oAct p 1 = RingHom.id _ :=
  RingHom.ext fun x => Subtype.ext (cpAct_one p x)

theorem flatAct_mul (σ τ : GQp p) (x : PreTilt 𝓞_ℂ_[p] p) :
    flatAct p (σ * τ) x = flatAct p σ (flatAct p τ x) := by
  apply Perfection.ext
  intro n
  rw [DR.coeff_preTiltMap, DR.coeff_preTiltMap, DR.coeff_preTiltMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ p n x)
  rw [← hy]
  change Ideal.Quotient.mk _ (oAct p (σ * τ) y) = Ideal.Quotient.mk _ (oAct p σ (oAct p τ y))
  rw [oAct_mul]
  rfl

theorem flatAct_one (x : PreTilt 𝓞_ℂ_[p] p) : flatAct p 1 x = x := by
  apply Perfection.ext
  intro n
  rw [DR.coeff_preTiltMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ p n x)
  rw [← hy]
  change Ideal.Quotient.mk _ (oAct p 1 y) = Ideal.Quotient.mk _ y
  rw [oAct_one]
  rfl

theorem wittMap_flatAct_mul (σ τ : GQp p) (w : Ainf p) :
    WittVector.map (flatAct p (σ * τ)) w =
      WittVector.map (flatAct p σ) (WittVector.map (flatAct p τ) w) := by
  ext n
  rw [WittVector.map_coeff, WittVector.map_coeff, WittVector.map_coeff, flatAct_mul]

theorem wittMap_flatAct_one (w : Ainf p) : WittVector.map (flatAct p 1) w = w := by
  ext n
  rw [WittVector.map_coeff, flatAct_one]

theorem locAct_mul (σ τ : GQp p) : locAct p (σ * τ) = (locAct p σ).comp (locAct p τ) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p))
  ext w
  simp only [RingHom.comp_apply, locAct_algebraMap, wittMap_flatAct_mul]

theorem locAct_one : locAct p 1 = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p))
  ext w
  simp only [RingHom.comp_apply, locAct_algebraMap, wittMap_flatAct_one, RingHom.id_apply]

theorem acris0Act_mul (σ τ : GQp p) (x : Acris0 p) :
    acris0Act p (σ * τ) x = acris0Act p σ (acris0Act p τ x) :=
  Subtype.ext (by
    change locAct p (σ * τ) x = locAct p σ (locAct p τ x)
    rw [locAct_mul]; rfl)

theorem acris0Act_one (x : Acris0 p) : acris0Act p 1 x = x :=
  Subtype.ext (by
    change locAct p 1 x = x
    rw [locAct_one]; rfl)

theorem adicMap_comp' {A : Type*} [CommRing A] (J : Ideal A) (g g' g'' : A →+* A)
    (hg : J ≤ J.comap g) (hg' : J ≤ J.comap g') (hg'' : J ≤ J.comap g'')
    (h : ∀ a, g'' a = g' (g a)) (x : AdicCompletion J A) :
    DR.adicMap J J g'' hg'' x = DR.adicMap J J g' hg' (DR.adicMap J J g hg x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [DR.adicMap_evalₐ, DR.adicMap_evalₐ]
  simp only [DR.adicMapAux, RingHom.comp_apply]
  erw [DR.adicMap_evalₐ]
  simp only [DR.adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, h]

theorem adicMap_id' {A : Type*} [CommRing A] (J : Ideal A) (g : A →+* A)
    (hg : J ≤ J.comap g) (h : ∀ a, g a = a) (x : AdicCompletion J A) :
    DR.adicMap J J g hg x = x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [DR.adicMap_evalₐ]
  simp only [DR.adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rw [Ideal.quotientMap_mk, h]

theorem acrisAct_mul (σ τ : GQp p) (x : Acris p) :
    acrisAct p (σ * τ) x = acrisAct p σ (acrisAct p τ x) :=
  adicMap_comp' _ _ _ _ _ _ _ (acris0Act_mul p σ τ) x

theorem acrisAct_one (x : Acris p) : acrisAct p 1 x = x :=
  adicMap_id' _ _ _ (acris0Act_one p) x

theorem bcrisPlusAct_mul (σ τ : GQp p) :
    bcrisPlusAct p (σ * τ) = (bcrisPlusAct p σ).comp (bcrisPlusAct p τ) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Acris p))
  ext a
  simp only [RingHom.comp_apply, bcrisPlusAct_algebraMap, acrisAct_mul]

theorem bcrisPlusAct_one : bcrisPlusAct p 1 = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Acris p))
  ext a
  simp only [RingHom.comp_apply, bcrisPlusAct_algebraMap, acrisAct_one, RingHom.id_apply]

theorem bcrisAct_mul (σ τ : GQp p) :
    bcrisAct p (σ * τ) = (bcrisAct p σ).comp (bcrisAct p τ) := by
  apply IsLocalization.ringHom_ext (tMonoid p)
  ext a
  simp only [RingHom.comp_apply, bcrisAct_algebraMap, bcrisPlusAct_mul]

theorem bcrisAct_one : bcrisAct p 1 = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (tMonoid p)
  ext a
  simp only [RingHom.comp_apply, bcrisAct_algebraMap, bcrisPlusAct_one, RingHom.id_apply]

theorem bcrisAct_mul_apply (σ τ : GQp p) (x : Bcris p) :
    bcrisAct p (σ * τ) x = bcrisAct p σ (bcrisAct p τ x) := by
  rw [bcrisAct_mul]; rfl

theorem bcrisAct_inv_apply (σ : GQp p) (x : Bcris p) : bcrisAct p σ⁻¹ (bcrisAct p σ x) = x := by
  rw [← bcrisAct_mul_apply, inv_mul_cancel, bcrisAct_one]; rfl

theorem bcrisAct_apply_inv (σ : GQp p) (x : Bcris p) : bcrisAct p σ (bcrisAct p σ⁻¹ x) = x := by
  rw [← bcrisAct_mul_apply, mul_inv_cancel, bcrisAct_one]; rfl

/-- **`G_{ℚ_p}` acts on `B_cris` by ring automorphisms** (a group homomorphism into
`Aut(B_cris)`), fixing `ℚ_p`. -/
def bcrisAut : GQp p →* (Bcris p ≃+* Bcris p) where
  toFun σ := RingEquiv.ofRingHom (bcrisAct p σ) (bcrisAct p σ⁻¹)
    (RingHom.ext fun x => bcrisAct_apply_inv p σ x) (RingHom.ext fun x => bcrisAct_inv_apply p σ x)
  map_one' := RingEquiv.ext fun x => by
    change bcrisAct p 1 x = x
    rw [bcrisAct_one]; rfl
  map_mul' σ τ := RingEquiv.ext fun x => bcrisAct_mul_apply p σ τ x

theorem bcrisAut_apply (σ : GQp p) (x : Bcris p) : bcrisAut p σ x = bcrisAct p σ x := rfl

/-! ### The action on `B_st = B_cris[u]` -/

theorem stAct_X (σ : GQp p) :
    stAct p σ Polynomial.X = Polynomial.X + Polynomial.C (logU p σ) :=
  Polynomial.eval₂_X _ _

/-- The inverse of `stAct σ`. -/
def stActInv (σ : GQp p) : Bst p →+* Bst p :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (bcrisAct p σ⁻¹))
    (Polynomial.X - Polynomial.C (bcrisAct p σ⁻¹ (logU p σ)))

theorem stActInv_comp (σ : GQp p) : (stActInv p σ).comp (stAct p σ) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, stAct_C, stActInv, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, bcrisAct_inv_apply, RingHom.id_apply]
  · simp only [RingHom.comp_apply, stAct_X, stActInv, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.id_apply]
    ring

theorem stAct_comp_inv (σ : GQp p) : (stAct p σ).comp (stActInv p σ) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, stActInv, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, stAct_C, bcrisAct_apply_inv, RingHom.id_apply]
  · simp only [RingHom.comp_apply, stActInv, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, map_sub, stAct_X, stAct_C,
      bcrisAct_apply_inv, RingHom.id_apply]
    ring

/-- **Each `σ ∈ G_{ℚ_p}` acts on `B_st` by a ring automorphism** (unconditionally). -/
def stEquiv (σ : GQp p) : Bst p ≃+* Bst p :=
  RingEquiv.ofRingHom (stAct p σ) (stActInv p σ) (stAct_comp_inv p σ) (stActInv_comp p σ)

theorem stEquiv_apply (σ : GQp p) (x : Bst p) : stEquiv p σ x = stAct p σ x := rfl

theorem stAct_bijective (σ : GQp p) : Function.Bijective (stAct p σ) :=
  (stEquiv p σ).bijective

/-- `log [ε] = 0` when `[ε] - 1 = 0`, i.e. `log [1] = 0`. -/
theorem logT_of_eq_zero {x : Ainf p} (hx : theta p x = 0) (h0 : x = 0) : logT p hx = 0 := by
  subst h0
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_logT, map_zero]
  have : logPartial p hx (p ^ n) = 0 := by
    apply Subtype.ext
    change logPartialVal p 0 (p ^ n) = 0
    rw [logPartialVal]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    simp only [logTerm, dpow, map_zero, zero_pow (show j ≠ 0 by omega), mul_zero]
  rw [this, map_zero]

theorem pFlat_untilt : PreTilt.untilt (pFlat p) = (p : 𝓞_ℂ_[p]) :=
  Classical.epsilon_spec (p := fun x : PreTilt 𝓞_ℂ_[p] p => PreTilt.untilt x = (p : 𝓞_ℂ_[p]))
    ⟨ZInQ.Contrib.G9.BdrKer.Cp.pFlat p, ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat p⟩

theorem untilt_zero' : PreTilt.untilt (0 : PreTilt 𝓞_ℂ_[p] p) = 0 :=
  untilt_eq_of_coeff p (fun _ => 0) (fun _ => zero_pow (Fact.out : p.Prime).ne_zero) 0
    (fun m => by rw [map_zero, map_zero])

theorem pFlat_ne_zero : pFlat p ≠ 0 := by
  intro h
  have := pFlat_untilt p
  rw [h, untilt_zero'] at this
  exact ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p this.symm

theorem uSigma_spec (σ : GQp p) : uSigma p σ * pFlat p = flatAct p σ (pFlat p) := by
  apply Classical.epsilon_spec (p := fun u => u * pFlat p = flatAct p σ (pFlat p))
  -- existence: `σ♭(p♭)/p♭`, via `𝓞_ℂ_p♭` being a valuation-type domain: use `dvd_of_coeff_zero`
  have hu : PreTilt.untilt (flatAct p σ (pFlat p)) = (p : 𝓞_ℂ_[p]) := by
    rw [DR.untilt_preTiltMap, pFlat_untilt, map_natCast]
  obtain ⟨d, hd⟩ := ZInQ.Contrib.G9.BdrKer.Cp.dvd_of_coeff_zero p (pFlat p) (pFlat_untilt p)
    (flatAct p σ (pFlat p)) (by
      rw [← PreTilt.mk_untilt_eq_coeff_zero, hu, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _)
  exact ⟨d, by rw [hd, mul_comm]⟩

theorem untilt_uSigma (σ : GQp p) : PreTilt.untilt (uSigma p σ) = 1 := by
  have h := congrArg PreTilt.untilt (uSigma_spec p σ)
  rw [map_mul, DR.untilt_preTiltMap, pFlat_untilt, map_natCast] at h
  have hp := ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p
  exact mul_right_cancel₀ hp (by rw [h, one_mul])

theorem uSigma_one : uSigma p 1 = 1 := by
  have h := uSigma_spec p 1
  rw [flatAct_one] at h
  exact mul_right_cancel₀ (pFlat_ne_zero p) (by rw [h, one_mul])

theorem uSigma_mul (σ τ : GQp p) : uSigma p (σ * τ) = flatAct p σ (uSigma p τ) * uSigma p σ := by
  apply mul_right_cancel₀ (pFlat_ne_zero p)
  rw [uSigma_spec, flatAct_mul, ← uSigma_spec p τ, map_mul, ← uSigma_spec p σ]
  ring

/-- `logU σ` is the image of `log [u_σ]` (the `else` branch never occurs). -/
theorem logU_eq (σ : GQp p) : logU p σ = algebraMap (BcrisPlus p) (Bcris p)
    (algebraMap (Acris p) (BcrisPlus p) (logT p (theta_teich_sub_one p (untilt_uSigma p σ)))) := by
  rw [logU, dite_eq_left_of_eq_true (eq_true (untilt_uSigma p σ))]

theorem logU_one : logU p 1 = 0 := by
  rw [logU_eq, logT_of_eq_zero p _ (by rw [uSigma_one, map_one, sub_self]), map_zero, map_zero]

/-- **`1 ∈ G_{ℚ_p}` acts trivially on `B_st`.** -/
theorem stAct_one : stAct p 1 = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro b; rw [stAct_C, bcrisAct_one]; rfl
  · rw [stAct_X, logU_one, map_zero, add_zero]; rfl

/-- **The group law on `B_st` is exactly the cocycle identity for `σ ↦ log [u_σ]`.** -/
theorem stAct_mul_iff (σ τ : GQp p) :
    stAct p (σ * τ) = (stAct p σ).comp (stAct p τ) ↔
      logU p (σ * τ) = logU p σ + bcrisAct p σ (logU p τ) := by
  constructor
  · intro h
    have hX := congrArg (fun φ : Bst p →+* Bst p => φ Polynomial.X) h
    simp only [RingHom.comp_apply, stAct_X, map_add, stAct_C] at hX
    have := congrArg (Polynomial.coeff · 0) hX
    simpa [add_comm] using this
  · intro h
    apply Polynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, stAct_C, bcrisAct_mul_apply]
    · simp only [RingHom.comp_apply, stAct_X, map_add, stAct_C, h]
      ring

/-- **`log` is additive on `{ε : ε^♯ = 1}`** (Fontaine; `log [xy] = log [x] + log [y]` in
`A_cris`). Standard (the formal identity `log((1+a)(1+b)) = log(1+a) + log(1+b)` with divided
powers); not proved here. It is the only missing input for the group law of `stAct`. -/
def LogAdditive : Prop :=
  ∀ (x y : PreTilt 𝓞_ℂ_[p] p) (hx : PreTilt.untilt x = 1) (hy : PreTilt.untilt y = 1)
    (hxy : PreTilt.untilt (x * y) = 1),
    logT p (theta_teich_sub_one p hxy) =
      logT p (theta_teich_sub_one p hx) + logT p (theta_teich_sub_one p hy)

theorem logT_congr {x y : Ainf p} (hx : theta p x = 0) (hy : theta p y = 0) (h : x = y) :
    logT p hx = logT p hy := by
  subst h; rfl

theorem logU_mul (hL : LogAdditive p) (σ τ : GQp p) :
    logU p (σ * τ) = logU p σ + bcrisAct p σ (logU p τ) := by
  have h1 : PreTilt.untilt (flatAct p σ (uSigma p τ)) = 1 := by
    rw [DR.untilt_preTiltMap, untilt_uSigma, map_one]
  have h2 : PreTilt.untilt (flatAct p σ (uSigma p τ) * uSigma p σ) = 1 := by
    rw [map_mul, h1, untilt_uSigma, one_mul]
  rw [logU_eq, logU_eq, logU_eq, bcrisAct_algebraMap, bcrisPlusAct_algebraMap,
    acrisAct_logT p σ _ (by rw [theta_wittMap, theta_teich_sub_one p (untilt_uSigma p τ),
      map_zero])]
  have e1 : logT p (theta_teich_sub_one p (untilt_uSigma p (σ * τ))) =
      logT p (theta_teich_sub_one p h2) :=
    logT_congr p _ _ (by rw [uSigma_mul])
  have e2 : logT p (by rw [theta_wittMap, theta_teich_sub_one p (untilt_uSigma p τ), map_zero] :
        theta p (WittVector.map (flatAct p σ) (WittVector.teichmuller p (uSigma p τ) - 1)) = 0) =
      logT p (theta_teich_sub_one p h1) :=
    logT_congr p _ _ (by rw [map_sub, map_one, WittVector.map_teichmuller])
  rw [e1, e2, hL _ _ h1 (untilt_uSigma p σ) h2, RingHom.map_add, RingHom.map_add, add_comm]

/-- **Given `LogAdditive`, `G_{ℚ_p}` acts on `B_st` by ring automorphisms** (group law). -/
theorem stAct_mul (hL : LogAdditive p) (σ τ : GQp p) :
    stAct p (σ * τ) = (stAct p σ).comp (stAct p τ) :=
  (stAct_mul_iff p σ τ).mpr (logU_mul p hL σ τ)

end Action

/-! ### Potentially trivial representations are potentially semistable -/

section Pst

variable {n : ℕ}

theorem finrank_fun_eq {W : Type} [AddCommGroup W] [Module ℚ_[p] W] (N : ℕ) :
    Module.finrank ℚ_[p] (Fin N → W) = N * Module.finrank ℚ_[p] W := by
  rw [Module.finrank, rank_pi, Cardinal.sum_const', Cardinal.toNat_mul, Cardinal.mk_fin,
    Cardinal.toNat_natCast]
  rfl

theorem finrank_linearMap_eq {V W : Type} [AddCommGroup V] [Module ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V] [AddCommGroup W] [Module ℚ_[p] W] :
    Module.finrank ℚ_[p] (V →ₗ[ℚ_[p]] W) =
      Module.finrank ℚ_[p] V * Module.finrank ℚ_[p] W := by
  let b := Module.finBasis ℚ_[p] V
  rw [← (b.constr ℚ_[p]).finrank_eq, finrank_fun_eq]

/-- **A representation trivial on `G_K` is semistable over `K`** (for every `K`, with no
finiteness hypothesis): `D_st,K ≅ Hom(V, B_st^{G_K})`. -/
theorem isSemistableOver_of_trivial (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    {E : Type} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (ρ : GQp p →* GL (Fin n) E) (h : ∀ σ ∈ K.fixingSubgroup, ρ σ = 1) :
    IsSemistableOver p K ρ := by
  let F : dstSpace p K ρ →ₗ[ℚ_[p]] ((Fin n → E) →ₗ[ℚ_[p]] bstInv p K) :=
    { toFun := fun φ => LinearMap.codRestrict (bstInv p K)
        (φ : (Fin n → E) →ₗ[ℚ_[p]] Bst p) (fun v σ hσ => by
          have := φ.2 σ hσ v
          rw [h σ hσ, Units.val_one, Matrix.one_mulVec] at this
          exact this.symm)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let G : ((Fin n → E) →ₗ[ℚ_[p]] bstInv p K) →ₗ[ℚ_[p]] dstSpace p K ρ :=
    { toFun := fun ψ => ⟨(bstInv p K).subtype ∘ₗ ψ, fun σ hσ v => by
          rw [h σ hσ, Units.val_one, Matrix.one_mulVec]
          exact ((ψ v).2 σ hσ).symm⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L : dstSpace p K ρ ≃ₗ[ℚ_[p]] ((Fin n → E) →ₗ[ℚ_[p]] bstInv p K) :=
    LinearEquiv.ofLinearMap F G (LinearMap.ext fun ψ => LinearMap.ext fun v => rfl)
      (LinearMap.ext fun φ => Subtype.ext (LinearMap.ext fun v => rfl))
  rw [IsSemistableOver, L.finrank_eq, finrank_linearMap_eq, finrank_fun_eq, mul_comm]

/-- **A representation trivial on `G_K` for a finite `K` is potentially semistable.** -/
theorem isPst_of_trivial_on {E : Type} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (ρ : GQp p →* GL (Fin n) E) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (h : ∀ σ ∈ K.fixingSubgroup, ρ σ = 1) : IsPst p ρ :=
  ⟨K, inferInstance, isSemistableOver_of_trivial p K ρ h⟩

/-- The trivial `n`-dimensional `ℚ̄_p`-representation satisfies `LocalIsPst`. -/
theorem localIsPst_one (n : ℕ) : LocalIsPst p n 1 := by
  refine ⟨⊥, inferInstance, 1, fun σ => by simp, ?_⟩
  exact isPst_of_trivial_on p 1 ⊥ fun _ _ => rfl

/-! #### Quadratic characters -/

variable {p} in
theorem gqp_apply_sq_root {α : PadicAlgCl p} {c : ℚ_[p]} (hα : α ^ 2 = algebraMap ℚ_[p] _ c)
    (σ : GQp p) : σ α = α ∨ σ α = -α := by
  have h : (σ α - α) * (σ α + α) = 0 := by
    have : σ α ^ 2 = α ^ 2 := by rw [← map_pow, hα, AlgEquiv.commutes]
    linear_combination this
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- The quadratic character `σ ↦ σ(α)/α ∈ {±1}` of `α ∈ ℚ̄_p^×` with `α² ∈ ℚ_p`
(unramified when `α²` is a non-square unit, `p` odd). -/
def quadChar {α : PadicAlgCl p} {c : ℚ_[p]} (hα : α ^ 2 = algebraMap ℚ_[p] _ c) (h0 : α ≠ 0) :
    GQp p →* GL (Fin 1) ℚ_[p] where
  toFun σ := haveI := Classical.propDecidable; if σ α = α then 1 else -1
  map_one' := by simp
  map_mul' σ τ := by
    classical
    have hne : -α ≠ α := fun h => h0 (by
      have : (2 : PadicAlgCl p) * α = 0 := by linear_combination -h
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero)
    have hmul : (σ * τ) α = σ (τ α) := rfl
    rcases gqp_apply_sq_root hα τ with hτ | hτ
    · rw [hmul, hτ]; simp
    · rcases gqp_apply_sq_root hα σ with hσ | hσ
      · rw [hmul, hτ, map_neg, hσ]; simp [hne]
      · rw [hmul, hτ, map_neg, hσ, neg_neg]; simp [hne]

/-- **Every quadratic character of `G_{ℚ_p}` of the form `σ(α)/α` is potentially semistable**
(it is trivial on `G_{ℚ_p(α)}`). -/
theorem isPst_quadChar {α : PadicAlgCl p} {c : ℚ_[p]} (hα : α ^ 2 = algebraMap ℚ_[p] _ c)
    (h0 : α ≠ 0) : IsPst p (quadChar p hα h0) := by
  have hint : IsIntegral ℚ_[p] α := Algebra.IsIntegral.isIntegral α
  have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {α}) :=
    IntermediateField.adjoin.finiteDimensional hint
  refine isPst_of_trivial_on p _ (IntermediateField.adjoin ℚ_[p] {α}) fun σ hσ => ?_
  have : σ α = α := hσ ⟨α, IntermediateField.mem_adjoin_simple_self ℚ_[p] α⟩
  simp [quadChar, this]

end Pst

/-! ### `K_0 ⊆ B_st^{G_K}`: Teichmüller lifts of roots of unity of order prime to `p` -/

section K0

/-- `A_inf → B_st` (through `A_cris^0`, `A_cris`, `B_cris^+`, `B_cris`). -/
def embW : Ainf p →+* Bst p :=
  Polynomial.C.comp ((algebraMap (BcrisPlus p) (Bcris p)).comp
    ((algebraMap (Acris p) (BcrisPlus p)).comp ((algebraMap (Acris0 p) (Acris p)).comp
      (ainfToAcris0 p))))

theorem acris0Act_ainfToAcris0 (σ : GQp p) (w : Ainf p) :
    acris0Act p σ (ainfToAcris0 p w) = ainfToAcris0 p (WittVector.map (flatAct p σ) w) :=
  Subtype.ext (locAct_algebraMap p σ w)

theorem stAct_embW (σ : GQp p) (w : Ainf p) :
    stAct p σ (embW p w) = embW p (WittVector.map (flatAct p σ) w) := by
  simp only [embW, RingHom.comp_apply, stAct_C, bcrisAct_algebraMap, bcrisPlusAct_algebraMap,
    acrisAct_algebraMap, acris0Act_ainfToAcris0]

/-- **`A_inf → B_st` is injective** (by the main lemma with a factor `y ∈ A_inf`). -/
theorem embW_injective : Function.Injective (embW p) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra hne
  have h1 : algebraMap (BcrisPlus p) (Bcris p) (algebraMap (Acris p) (BcrisPlus p) (ofAinf p w))
      = 0 := Polynomial.C_eq_zero.mp hw
  obtain ⟨⟨s, hs⟩, hs0⟩ := (IsLocalization.map_eq_zero_iff (tMonoid p) (Bcris p) _).mp h1
  obtain ⟨l, rfl⟩ := exists_list_of_mem_tMonoid p hs
  rw [← map_mul] at hs0
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : Acris p)) (BcrisPlus p) _).mp hs0
  apply pow_mul_prod_logOf_mul_ne_zero p l k w hne
  rw [mul_assoc]
  exact hk

theorem embW_zpToW (z : ℤ_[p]) :
    embW p (zpToW p z) = algebraMap ℚ_[p] (Bst p) (algebraMap ℤ_[p] ℚ_[p] z) := by
  rw [Polynomial.algebraMap_apply]
  change _ = Polynomial.C (qpToBcris p (algebraMap ℤ_[p] ℚ_[p] z))
  rw [qpToBcris, RingHom.comp_apply, qpToBcrisPlus, IsLocalization.lift_eq]
  rfl

/-- For `σ ∈ G_{ℚ_p}` fixing `μ ∈ ℚ̄_p`, `σ` fixes `μ ∈ 𝓞_ℂ_p`. -/
theorem oAct_of_fixed (σ : GQp p) {μ : PadicAlgCl p} (hσ : σ μ = μ) (hμ : (μ : ℂ_[p]) ∈ 𝓞_ℂ_[p]) :
    oAct p σ ⟨(μ : ℂ_[p]), hμ⟩ = ⟨(μ : ℂ_[p]), hμ⟩ :=
  Subtype.ext (by
    change cpAct p σ (μ : ℂ_[p]) = (μ : ℂ_[p])
    rw [cpAct_coe, hσ])

variable {μ : PadicAlgCl p} {m : ℕ}

theorem norm_root_of_unity (hm0 : 0 < m) (hμ : μ ^ m = 1) : ‖(μ : ℂ_[p])‖ = 1 := by
  have h := congrArg norm hμ
  rw [norm_pow, norm_one] at h
  rw [PadicComplex.norm_extends]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').mp h

theorem mem_O_of_root_of_unity (hm0 : 0 < m) (hμ : μ ^ m = 1) : (μ : ℂ_[p]) ∈ 𝓞_ℂ_[p] :=
  (ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mpr (norm_root_of_unity p hm0 hμ).le

theorem exists_pow_p_mul_eq (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m) :
    ∃ q : ℕ, μ ^ (p * q) = μ := by
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · obtain ⟨q, -, hq⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    refine ⟨q, ?_⟩
    rw [← Nat.div_add_mod (p * q) m, pow_add, pow_mul, hμ, one_pow, one_mul, hq, pow_one]
  · have : m = 1 := by omega
    subst this
    rw [pow_one] at hμ
    exact ⟨0, by rw [hμ, one_pow]⟩

/-- The Teichmüller representative `μ♭ = (μ, μ^{1/p}, …)`, `μ^{1/p^n} = μ^{q^n}` (`pq ≡ 1 mod m`). -/
noncomputable def muFlat (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m) : PreTilt 𝓞_ℂ_[p] p :=
  ⟨fun n => Ideal.Quotient.mk _ ((⟨(μ : ℂ_[p]), mem_O_of_root_of_unity p hm0 hμ⟩ : 𝓞_ℂ_[p]) ^
      (Classical.choose (exists_pow_p_mul_eq p hm0 hμ hcop)) ^ n), fun n => by
    rw [← map_pow]
    congr 1
    set q := Classical.choose (exists_pow_p_mul_eq p hm0 hμ hcop)
    have hq : (⟨(μ : ℂ_[p]), mem_O_of_root_of_unity p hm0 hμ⟩ : 𝓞_ℂ_[p]) ^ (p * q) =
        ⟨(μ : ℂ_[p]), mem_O_of_root_of_unity p hm0 hμ⟩ := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow]
      rw [PadicComplex.coe_eq, ← map_pow]
      exact congrArg _ (Classical.choose_spec (exists_pow_p_mul_eq p hm0 hμ hcop))
    rw [← pow_mul, pow_succ, mul_assoc, mul_comm q p, mul_comm, pow_mul, hq]⟩

theorem untilt_muFlat (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m) :
    PreTilt.untilt (muFlat p hm0 hμ hcop) = ⟨(μ : ℂ_[p]), mem_O_of_root_of_unity p hm0 hμ⟩ := by
  set q := Classical.choose (exists_pow_p_mul_eq p hm0 hμ hcop)
  set μO : 𝓞_ℂ_[p] := ⟨(μ : ℂ_[p]), mem_O_of_root_of_unity p hm0 hμ⟩
  have hq : μO ^ (p * q) = μO := by
    apply Subtype.ext
    simp only [μO, SubmonoidClass.coe_pow]
    rw [PadicComplex.coe_eq, ← map_pow]
    exact congrArg _ (Classical.choose_spec (exists_pow_p_mul_eq p hm0 hμ hcop))
  have := untilt_eq_of_coeff p (fun n => μO ^ q ^ n) (fun n => by
    rw [← pow_mul, pow_succ, mul_assoc, mul_comm q p, mul_comm, pow_mul, hq])
    (muFlat p hm0 hμ hcop) (fun n => rfl)
  simpa using this

theorem flatAct_muFlat (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m) (σ : GQp p)
    (hσ : σ μ = μ) : flatAct p σ (muFlat p hm0 hμ hcop) = muFlat p hm0 hμ hcop := by
  set q := Classical.choose (exists_pow_p_mul_eq p hm0 hμ hcop)
  set μO : 𝓞_ℂ_[p] := ⟨(μ : ℂ_[p]), mem_O_of_root_of_unity p hm0 hμ⟩ with hμO
  apply Perfection.ext
  intro n
  rw [DR.coeff_preTiltMap]
  change DR.modPMap p (oAct p σ) (Ideal.Quotient.mk _ (μO ^ q ^ n)) =
    Ideal.Quotient.mk _ (μO ^ q ^ n)
  rw [DR.modPMap, Ideal.quotientMap_mk, map_pow, hμO, oAct_of_fixed p σ hσ]

/-- The image of `[μ♭]` in `B_st`. -/
noncomputable def teichB (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m) : Bst p :=
  embW p (WittVector.teichmuller p (muFlat p hm0 hμ hcop))

/-- `[μ♭] ∈ B_st^{G_K}` when `μ ∈ K`. -/
theorem teichB_pow_mem_bstInv (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : μ ∈ K) (i : ℕ) :
    teichB p hm0 hμ hcop ^ i ∈ bstInv p K := by
  intro σ hσ
  have hσμ : σ μ = μ := hσ ⟨μ, hK⟩
  rw [map_pow, teichB, stAct_embW, WittVector.map_teichmuller, flatAct_muFlat p hm0 hμ hcop σ hσμ]

/-- `θ ∘ (ℤ_p → A_inf)` is the inclusion `ℤ_p ⊆ ℂ_p`. -/
theorem coe_theta_zpToW (z : ℤ_[p]) :
    ((theta p (zpToW p z) : 𝓞_ℂ_[p]) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] z) := by
  set f : ℤ_[p] →+* ℂ_[p] := ((PadicComplexInt p).subtype).comp ((theta p).comp (zpToW p)) with hf
  set g : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p]) with hg
  have hfn : ∀ u, ‖f u‖ ≤ 1 := fun u =>
    ZInQ.Contrib.G9.BdrKer.Cp.norm_le_one p (theta p (zpToW p u))
  have hgn : ∀ u, ‖g u‖ ≤ 1 := fun u => by
    simp only [hg, RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
      PadicComplex.norm_extends, PadicAlgCl.norm_extends, PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one u
  have key : ∀ n : ℕ, ‖f z - g z‖ ≤ 2 * ‖(p : ℂ_[p])‖ ^ n := by
    intro n
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n z)
    have hz : z = (PadicInt.appr z n : ℤ_[p]) + u * (p : ℤ_[p]) ^ n := by rw [hu]; ring
    rw [hz, map_add, map_add, map_natCast, map_natCast, add_sub_add_left_eq_sub, map_mul,
      map_mul, map_pow, map_pow, map_natCast, map_natCast, ← sub_mul, norm_mul, norm_pow,
      mul_comm]
    have hb : ‖f u - g u‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hfn u, hgn u])
    have hpn := pow_nonneg (norm_nonneg (p : ℂ_[p])) n
    nlinarith
  have h0 : f z - g z = 0 := by
    by_contra hne
    have hpos : 0 < ‖f z - g z‖ := norm_pos_iff.mpr hne
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ‖f z - g z‖ / 2 by linarith)
      (ZInQ.Contrib.G9.PkgI4.Cp.norm_p_lt_one p)
    have := key n
    linarith
  exact sub_eq_zero.mp h0

/-- **`K_0 ⊆ B_st^{G_K}` (dimension form).** For a root of unity `μ ∈ K` of order prime to `p`,
the powers `1, [μ♭], …, [μ♭]^{d-1}` (`d = [ℚ_p(μ) : ℚ_p]`) are `ℚ_p`-linearly independent
elements of `B_st^{G_K}`. The maximal unramified subextension `K_0` of a finite `K` is `ℚ_p(μ)`
for such a `μ` (Serre, *Local Fields*, IV §4; UNVERIFIED), so `dim_{ℚ_p} B_st^{G_K} ≥ [K_0 : ℚ_p]`
whenever `B_st^{G_K}` is finite-dimensional. -/
theorem linearIndependent_teichB (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m) :
    LinearIndependent ℚ_[p]
      (fun i : Fin (minpoly ℚ_[p] μ).natDegree => teichB p hm0 hμ hcop ^ (i : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set T0 := WittVector.teichmuller p (muFlat p hm0 hμ hcop) with hT0
  obtain ⟨⟨_, k, rfl⟩, hb⟩ :=
    IsLocalization.exist_integer_multiples (Submonoid.powers (p : ℤ_[p])) Finset.univ g
  choose z hz using fun j => hb j (Finset.mem_univ j)
  -- the relation in `A_inf`
  have h1 : embW p (∑ j, zpToW p (z j) * T0 ^ (j : ℕ)) = 0 := by
    rw [map_sum]
    simp only [map_mul, map_pow, embW_zpToW, hz]
    have : ∀ j, algebraMap ℚ_[p] (Bst p) ((p : ℤ_[p]) ^ k • g j) * embW p T0 ^ (j : ℕ) =
        algebraMap ℚ_[p] (Bst p) (algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ k)) *
          (g j • teichB p hm0 hμ hcop ^ (j : ℕ)) := fun j => by
      rw [Algebra.smul_def (g j), Algebra.smul_def, map_mul, teichB]
      ring
    simp only [this, ← Finset.mul_sum, hg, mul_zero]
  have h2 := embW_injective p (h1.trans (map_zero _).symm)
  -- apply `θ` and pass to `ℂ_p`
  have h3 := congrArg (fun w => ((theta p w : 𝓞_ℂ_[p]) : ℂ_[p])) h2
  simp only [map_sum, map_mul, map_pow, map_zero, ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum,
    MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_theta_zpToW] at h3
  have hθT : ((theta p T0 : 𝓞_ℂ_[p]) : ℂ_[p]) = (μ : ℂ_[p]) := by
    rw [hT0, theta, WittVector.fontaineTheta_teichmuller, untilt_muFlat]
  rw [hθT] at h3
  -- linear independence of the powers of `μ` over `ℚ_p`
  have hli := linearIndependent_pow (K := ℚ_[p]) (μ : ℂ_[p])
  have hmin : minpoly ℚ_[p] (μ : ℂ_[p]) = minpoly ℚ_[p] μ := by
    rw [PadicComplex.coe_eq]
    exact minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p])
      (algebraMap (PadicAlgCl p) ℂ_[p]).injective μ
  rw [hmin] at hli
  rw [Fintype.linearIndependent_iff] at hli
  have h4 := hli (fun j => algebraMap ℤ_[p] ℚ_[p] (z j)) (by
    simpa only [Algebra.smul_def] using h3) i
  rw [hz i, Algebra.smul_def, mul_eq_zero] at h4
  rcases h4 with h4 | h4
  · exfalso
    rw [map_pow, map_natCast] at h4
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h4
  · exact h4

/-- Hence, if `B_st^{G_K}` is finite-dimensional (Fontaine: it is `K_0`), its dimension is at least
`[ℚ_p(μ) : ℚ_p]` for every root of unity `μ ∈ K` of order prime to `p`. -/
theorem natDegree_minpoly_le_finrank_bstInv (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : μ ∈ K)
    [FiniteDimensional ℚ_[p] (bstInv p K)] :
    (minpoly ℚ_[p] μ).natDegree ≤ Module.finrank ℚ_[p] (bstInv p K) := by
  have hli : LinearIndependent ℚ_[p] (fun i : Fin (minpoly ℚ_[p] μ).natDegree =>
      (⟨teichB p hm0 hμ hcop ^ (i : ℕ), teichB_pow_mem_bstInv p hm0 hμ hcop K hK i⟩ :
        bstInv p K)) :=
    LinearIndependent.of_comp (bstInv p K).subtype (linearIndependent_teichB p hm0 hμ hcop)
  simpa using hli.fintype_card_le_finrank

end K0


/-! ### `u = log [p♭]` is not `G_{ℚ_p}`-invariant -/

section UNotInvariant

theorem preTiltMap_frobeniusEquiv_symm (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (y : PreTilt 𝓞_ℂ_[p] p) :
    DR.preTiltMap p f ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm y) =
      (frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm (DR.preTiltMap p f y) := by
  apply (frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow, ← frobenius_def,
    ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

open ZInQ.Contrib.G9.BdrKer.Cp in
theorem root_preTiltMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : PreTilt 𝓞_ℂ_[p] p) (n : ℕ) :
    root (DR.preTiltMap p f x) n = f (root x n) := by
  rw [root, root, ← DR.untilt_preTiltMap]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      preTiltMap_frobeniusEquiv_symm]

/-- A `p`-th root of `p` in `ℚ̄_p` is not in `ℚ_p`. -/
theorem not_mem_range_of_pow_eq_p {a : PadicAlgCl p} (ha : a ^ p = (p : PadicAlgCl p)) :
    a ∉ Set.range (algebraMap ℚ_[p] (PadicAlgCl p)) := by
  rintro ⟨c, rfl⟩
  have hc : c ^ p = (p : ℚ_[p]) := by
    apply (algebraMap ℚ_[p] (PadicAlgCl p)).injective
    rw [map_pow, ha, map_natCast]
  have hv := congrArg Padic.valuation hc
  rw [Padic.valuation_pow, Padic.valuation_p] at hv
  have h2 := (Fact.out : p.Prime).two_le
  have : (p : ℤ) * c.valuation = 1 := hv
  have h3 : (2 : ℤ) ≤ p := by exact_mod_cast h2
  rcases lt_trichotomy c.valuation 0 with h | h | h <;> nlinarith

/-- **Some `σ ∈ G_{ℚ_p}` moves `p♭`**, i.e. `u_σ ≠ 1`. -/
theorem exists_uSigma_ne_one : ∃ σ : GQp p, uSigma p σ ≠ 1 := by
  set r := ZInQ.Contrib.G9.BdrKer.Cp.root (pFlat p) 1 with hr
  have hrp : r ^ p = (p : 𝓞_ℂ_[p]) := by
    have := ZInQ.Contrib.G9.BdrKer.Cp.root_pow (pFlat p) 1
    rw [pow_one, pFlat_untilt] at this
    exact this
  -- `r` comes from `ℚ̄_p`
  set f : Polynomial (PadicAlgCl p) := Polynomial.X ^ p - Polynomial.C (p : PadicAlgCl p) with hf
  have hf0 : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (Fact.out : p.Prime).pos _
  have hroot : (f.map (algebraMap (PadicAlgCl p) ℂ_[p])).IsRoot (r : ℂ_[p]) := by
    simp only [hf, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      map_natCast]
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hrp
    simp only [SubmonoidClass.coe_pow] at this
    rw [this]
    simp
  obtain ⟨a, ha⟩ := (IsAlgClosed.splits f).mem_range_of_isRoot hf0 hroot
  have hap : a ^ p = (p : PadicAlgCl p) := by
    apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
    rw [map_pow, ha, map_natCast]
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hrp
    simpa using this
  -- some `σ` moves `a`
  obtain ⟨σ, hσ⟩ : ∃ σ : GQp p, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact not_mem_range_of_pow_eq_p p hap
      ((InfiniteGalois.mem_range_algebraMap_iff_fixed a).mpr hcon)
  refine ⟨σ, fun h1 => hσ ?_⟩
  have h2 : flatAct p σ (pFlat p) = pFlat p := by
    rw [← uSigma_spec, h1, one_mul]
  have h3 := root_preTiltMap p (oAct p σ) (pFlat p) 1
  change ZInQ.Contrib.G9.BdrKer.Cp.root (flatAct p σ (pFlat p)) 1 = _ at h3
  rw [h2, ← hr] at h3
  have h4 := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) h3
  change (r : ℂ_[p]) = cpAct p σ (r : ℂ_[p]) at h4
  rw [← ha] at h4
  have h5 : ((σ a : PadicAlgCl p) : ℂ_[p]) = (a : ℂ_[p]) :=
    (cpAct_coe p σ a).symm.trans h4.symm
  exact (algebraMap (PadicAlgCl p) ℂ_[p]).injective h5

/-- **`u` is not `G_{ℚ_p}`-invariant**: some `σ` has `σ(u) = u + c(σ)t` with `c(σ)t ≠ 0`. So the
monodromy part of `B_st` is genuine (with a trivial action on `u`, `B_st^{G_K}` would contain
`B_cris^{G_K}[u]` and be infinite-dimensional, which would make `IsSemistableOver` degenerate). -/
theorem exists_stAct_X_ne : ∃ σ : GQp p, stAct p σ Polynomial.X ≠ Polynomial.X := by
  obtain ⟨σ, hσ⟩ := exists_uSigma_ne_one p
  refine ⟨σ, fun h => ?_⟩
  rw [stAct_X, add_eq_left, Polynomial.C_eq_zero, logU_eq] at h
  exact logOf_bcris_ne_zero p ⟨uSigma p σ, untilt_uSigma p σ, hσ⟩ h

theorem X_not_mem_bstInv_bot : (Polynomial.X : Bst p) ∉ bstInv p ⊥ := by
  intro h
  obtain ⟨σ, hσ⟩ := exists_stAct_X_ne p
  exact hσ (h σ (fun x => by
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp x.2
    change σ x.1 = x.1
    rw [← hc, AlgEquiv.commutes]))

end UNotInvariant

/-! ### A character with a unit period is semistable; the unramified quadratic character -/

section Period

/-- **A one-dimensional representation with a unit period is semistable over `K`**: if `b ∈ B_st` is
a unit with `σ(b) = χ(σ) b` for `σ ∈ G_K`, then `D_st,K(χ) ≅ B_st^{G_K}` (`φ ↦ φ(1) b⁻¹`). -/
theorem isSemistableOver_of_period (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (χ : GQp p →* GL (Fin 1) ℚ_[p]) (b : Bst p) (hbu : IsUnit b)
    (hb : ∀ σ ∈ K.fixingSubgroup,
      stAct p σ b = ((χ σ : Matrix (Fin 1) (Fin 1) ℚ_[p]) 0 0) • b) :
    IsSemistableOver p K χ := by
  obtain ⟨u, rfl⟩ := hbu
  let e : Fin 1 → ℚ_[p] := fun _ => 1
  have hv : ∀ v : Fin 1 → ℚ_[p], v = v 0 • e := fun v => by ext k; fin_cases k; simp [e]
  have hmv : ∀ (σ : GQp p) (v : Fin 1 → ℚ_[p]),
      Matrix.mulVec (χ σ : Matrix (Fin 1) (Fin 1) ℚ_[p]) v =
        ((χ σ : Matrix (Fin 1) (Fin 1) ℚ_[p]) 0 0) • v := fun σ v => by
    ext k; fin_cases k; simp [Matrix.mulVec, dotProduct]
  have hinvu : ∀ σ ∈ K.fixingSubgroup, stAct p σ (u⁻¹ : (Bst p)ˣ) =
      ((χ σ : Matrix (Fin 1) (Fin 1) ℚ_[p]) 0 0)⁻¹ • ((u⁻¹ : (Bst p)ˣ) : Bst p) := by
    intro σ hσ
    have hc0 : ((χ σ : Matrix (Fin 1) (Fin 1) ℚ_[p]) 0 0) ≠ 0 := by
      intro h0
      have := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℚ_[p] => M 0 0) (χ σ).mul_inv
      simp only [Matrix.mul_apply, Fin.sum_univ_one, h0, zero_mul, Matrix.one_apply_eq] at this
      exact zero_ne_one this
    have h1 : stAct p σ (u : Bst p) * stAct p σ ((u⁻¹ : (Bst p)ˣ) : Bst p) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hb σ hσ, smul_mul_assoc] at h1
    set c := ((χ σ : Matrix (Fin 1) (Fin 1) ℚ_[p]) 0 0)
    have h2 : (u : Bst p) * stAct p σ ((u⁻¹ : (Bst p)ˣ) : Bst p) = c⁻¹ • (1 : Bst p) := by
      have := congrArg (c⁻¹ • ·) h1
      simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
      exact this
    calc stAct p σ ((u⁻¹ : (Bst p)ˣ) : Bst p)
        = (((u⁻¹ : (Bst p)ˣ) : Bst p) * u) * stAct p σ ((u⁻¹ : (Bst p)ˣ) : Bst p) := by
          rw [Units.inv_mul, one_mul]
      _ = ((u⁻¹ : (Bst p)ˣ) : Bst p) * ((u : Bst p) * stAct p σ ((u⁻¹ : (Bst p)ˣ) : Bst p)) :=
          mul_assoc _ _ _
      _ = c⁻¹ • ((u⁻¹ : (Bst p)ˣ) : Bst p) := by rw [h2, mul_smul_comm, mul_one]
  let F : dstSpace p K χ →ₗ[ℚ_[p]] bstInv p K :=
    { toFun := fun φ => ⟨(φ : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] Bst p) e * ((u⁻¹ : (Bst p)ˣ) : Bst p),
        fun σ hσ => by
          have h := φ.2 σ hσ e
          rw [hmv, map_smul] at h
          rw [map_mul, ← h, hinvu σ hσ, smul_mul_smul_comm]
          have hc0 : ((χ σ : Matrix (Fin 1) (Fin 1) ℚ_[p]) 0 0) ≠ 0 := by
            intro h0
            have := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℚ_[p] => M 0 0) (χ σ).mul_inv
            simp only [Matrix.mul_apply, Fin.sum_univ_one, h0, zero_mul,
              Matrix.one_apply_eq] at this
            exact zero_ne_one this
          rw [mul_inv_cancel₀ hc0, one_smul]⟩
      map_add' := fun φ ψ => Subtype.ext (by
        change ((φ + ψ : dstSpace p K χ) : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] Bst p) e * _ = _ * _ + _ * _
        rw [Submodule.coe_add, LinearMap.add_apply, add_mul])
      map_smul' := fun c φ => Subtype.ext (by
        change ((c • φ : dstSpace p K χ) : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] Bst p) e * _ = c • (_ * _)
        rw [Submodule.coe_smul, LinearMap.smul_apply, smul_mul_assoc]) }
  let G : bstInv p K →ₗ[ℚ_[p]] dstSpace p K χ :=
    { toFun := fun c => ⟨(LinearMap.proj (R := ℚ_[p]) (φ := fun _ : Fin 1 => ℚ_[p]) 0).smulRight
          ((c : Bst p) * (u : Bst p)), fun σ hσ v => by
        simp only [LinearMap.smulRight_apply, LinearMap.proj_apply, hmv, Pi.smul_apply,
          smul_eq_mul, stAct_smul, map_mul, c.2 σ hσ, hb σ hσ, mul_smul_comm, smul_smul,
          mul_comm (v 0)]⟩
      map_add' := fun a b => Subtype.ext (LinearMap.ext fun v => by
        change v 0 • (((a + b : bstInv p K) : Bst p) * (u : Bst p)) =
          v 0 • ((a : Bst p) * u) + v 0 • ((b : Bst p) * u)
        rw [Submodule.coe_add, add_mul, smul_add])
      map_smul' := fun c a => Subtype.ext (LinearMap.ext fun v => by
        change v 0 • (((c • a : bstInv p K) : Bst p) * (u : Bst p)) = c • (v 0 • ((a : Bst p) * u))
        rw [Submodule.coe_smul, smul_mul_assoc, smul_comm]) }
  let L : dstSpace p K χ ≃ₗ[ℚ_[p]] bstInv p K :=
    LinearEquiv.ofLinearMap F G
      (LinearMap.ext fun c => Subtype.ext (by
        change ((1 : ℚ_[p]) • ((c : Bst p) * u)) * ((u⁻¹ : (Bst p)ˣ) : Bst p) = c
        rw [one_smul, mul_assoc, Units.mul_inv, mul_one]))
      (LinearMap.ext fun φ => Subtype.ext (LinearMap.ext fun v => by
        change v 0 • ((φ : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] Bst p) e * ((u⁻¹ : (Bst p)ˣ) : Bst p) *
          (u : Bst p)) = (φ : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] Bst p) v
        rw [mul_assoc, Units.inv_mul, mul_one, ← map_smul, ← hv v]))
  rw [IsSemistableOver, L.finrank_eq, Module.finrank_self, mul_one, mul_one]

end Period

section QuadPeriod

variable {μ : PadicAlgCl p} {m : ℕ}

theorem iterate_frob_symm_mul (n : ℕ) (x y : PreTilt 𝓞_ℂ_[p] p) :
    ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) (x * y) =
      ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) x *
        ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

theorem iterate_frob_symm_one (n : ℕ) :
    ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) (1 : PreTilt 𝓞_ℂ_[p] p) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_one]

open ZInQ.Contrib.G9.BdrKer.Cp in
theorem root_mul (x y : PreTilt 𝓞_ℂ_[p] p) (n : ℕ) : root (x * y) n = root x n * root y n := by
  rw [root, root, root, iterate_frob_symm_mul, map_mul]

open ZInQ.Contrib.G9.BdrKer.Cp in
theorem root_pow' (x : PreTilt 𝓞_ℂ_[p] p) (k n : ℕ) : root (x ^ k) n = root x n ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, root, iterate_frob_symm_one, map_one]
  | succ k ih => rw [pow_succ, root_mul, ih, pow_succ]

open ZInQ.Contrib.G9.BdrKer.Cp in
/-- **Uniqueness of Teichmüller representatives**: two `m`-th roots of unity of `𝓞_ℂ_p♭` (`p ∤ m`)
with the same `♯` are equal. -/
theorem eq_of_pow_eq_one_of_untilt (hm0 : 0 < m) (hcop : p.Coprime m) {x y : PreTilt 𝓞_ℂ_[p] p}
    (hx : x ^ m = 1) (hy : y ^ m = 1) (h : PreTilt.untilt x = PreTilt.untilt y) : x = y := by
  set z := x * y ^ (m - 1) with hz
  have hym : y ^ (m - 1) * y = 1 := by rw [← pow_succ, Nat.sub_add_cancel hm0, hy]
  have hzm : z ^ m = 1 := by rw [hz, mul_pow, hx, one_mul, ← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have hzu : PreTilt.untilt z = 1 := by
    rw [hz, map_mul, h, ← map_mul, mul_comm, hym, map_one]
  have hz1 : z = 1 := by
    apply Perfection.ext
    intro n
    change PreTilt.coeff n z = PreTilt.coeff n 1
    rw [← mk_root, map_one]
    have h1 : root z n ^ p ^ n = 1 := by rw [root_pow, hzu]
    have h2 : root z n ^ m = 1 := by
      rw [← root_pow', hzm, root, iterate_frob_symm_one, map_one]
    have h3 : root z n ^ (Nat.gcd (p ^ n) m) = 1 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rw [Nat.Coprime.pow_left n hcop, pow_one] at h3
    rw [h3, map_one]
  calc x = z * y := by rw [hz, mul_assoc, hym, mul_one]
    _ = y := by rw [hz1, one_mul]

theorem muFlat_pow_eq_one (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m) :
    muFlat p hm0 hμ hcop ^ m = 1 := by
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (muFlat p hm0 hμ hcop ^ m) = PreTilt.coeff n 1
  rw [map_pow, map_one]
  change (Ideal.Quotient.mk _ (_ ^ _)) ^ m = 1
  rw [← map_pow, ← pow_mul, mul_comm, pow_mul]
  have : (⟨(μ : ℂ_[p]), mem_O_of_root_of_unity p hm0 hμ⟩ : 𝓞_ℂ_[p]) ^ m = 1 := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [PadicComplex.coe_eq, ← map_pow, hμ, map_one]
  rw [this, one_pow, map_one]

theorem isUnit_teichB (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m) :
    IsUnit (teichB p hm0 hμ hcop) := by
  refine IsUnit.of_pow_eq_one (n := m) ?_ hm0.ne'
  rw [teichB, ← map_pow, ← map_pow, muFlat_pow_eq_one, map_one, map_one]

/-- **The quadratic character of a root of unity of order prime to `p` is semistable over `ℚ_p`**
(crystalline), with period `[β♭]`. For `p` odd and `β` a primitive `2(p−1)`-th root of unity this is
the unramified quadratic character (STANDARD; not needed here). -/
theorem isSemistableOver_quadChar_teich (hm0 : 0 < m) (hμ : μ ^ m = 1) (hcop : p.Coprime m)
    {c : ℚ_[p]} (hc : μ ^ 2 = algebraMap ℚ_[p] _ c) (h0 : μ ≠ 0) :
    IsSemistableOver p ⊥ (quadChar p hc h0) := by
  classical
  refine isSemistableOver_of_period p ⊥ _ (teichB p hm0 hμ hcop) (isUnit_teichB p hm0 hμ hcop)
    fun σ _ => ?_
  rcases gqp_apply_sq_root hc σ with hσ | hσ
  · have hχ : ((quadChar p hc h0 σ : Matrix (Fin 1) (Fin 1) ℚ_[p]) 0 0) = 1 := by
      simp [quadChar, hσ]
    rw [hχ, one_smul, teichB, stAct_embW, WittVector.map_teichmuller,
      flatAct_muFlat p hm0 hμ hcop σ hσ]
  · have hne : -μ ≠ μ := fun h => h0 (by
      have : (2 : PadicAlgCl p) * μ = 0 := by linear_combination -h
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero)
    have hχ : ((quadChar p hc h0 σ : Matrix (Fin 1) (Fin 1) ℚ_[p]) 0 0) = -1 := by
      simp [quadChar, hσ, hne]
    rw [hχ, neg_one_smul, teichB, stAct_embW, WittVector.map_teichmuller]
    set x := muFlat p hm0 hμ hcop with hx
    -- `μ²` is fixed, so `(σ♭ x)² = x²`
    have hμ2 : (μ ^ 2) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hμ, one_pow]
    have hsq : x ^ 2 = muFlat p hm0 hμ2 hcop := by
      apply eq_of_pow_eq_one_of_untilt p hm0 hcop
      · rw [← pow_mul, mul_comm, pow_mul, muFlat_pow_eq_one, one_pow]
      · exact muFlat_pow_eq_one p hm0 hμ2 hcop
      · rw [map_pow, hx, untilt_muFlat, untilt_muFlat]
        apply Subtype.ext
        simp only [SubmonoidClass.coe_pow]
        rw [PadicComplex.coe_eq, PadicComplex.coe_eq, ← map_pow]
    have hfix2 : flatAct p σ (x ^ 2) = x ^ 2 := by
      rw [hsq, flatAct_muFlat p hm0 hμ2 hcop σ (by rw [hc, AlgEquiv.commutes])]
    have hW : (WittVector.teichmuller p (flatAct p σ x)) ^ 2 =
        (WittVector.teichmuller p x) ^ 2 := by
      rw [← map_pow, ← map_pow, ← map_pow, hfix2]
    have hsplit : (WittVector.teichmuller p (flatAct p σ x) - WittVector.teichmuller p x) *
        (WittVector.teichmuller p (flatAct p σ x) + WittVector.teichmuller p x) = 0 := by
      linear_combination hW
    rcases mul_eq_zero.mp hsplit with h1 | h1
    · exfalso
      have h2 : flatAct p σ x = x := by
        have := congrArg (fun w => WittVector.coeff w 0) (sub_eq_zero.mp h1)
        simpa [WittVector.teichmuller_coeff_zero] using this
      have h3 := congrArg PreTilt.untilt h2
      rw [DR.untilt_preTiltMap, hx, untilt_muFlat] at h3
      have h4 := congrArg Subtype.val h3
      change cpAct p σ (μ : ℂ_[p]) = (μ : ℂ_[p]) at h4
      rw [cpAct_coe, hσ] at h4
      exact hne ((algebraMap (PadicAlgCl p) ℂ_[p]).injective h4)
    · rw [eq_neg_of_add_eq_zero_left h1, map_neg]

end QuadPeriod

/-! ### `LogAdditive` -/

section LogAdd

/-- `ℚ → A_inf[1/p]`. -/
def qQ : ℚ →+* AinfP p := (qpToLoc p).comp (algebraMap ℚ ℚ_[p])

/-- Evaluation `ℚ[B][A] → A_inf[1/p]`, `A ↦ a`, `B ↦ b`. -/
def evS (a b : Ainf p) : PBLogPoly.S →+* AinfP p :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (qQ p) (algebraMap (Ainf p) (AinfP p) b))
    (algebraMap (Ainf p) (AinfP p) a)

theorem evS_X (a b : Ainf p) : evS p a b Polynomial.X = algebraMap (Ainf p) (AinfP p) a := by
  simp [evS]

theorem evS_C_X (a b : Ainf p) :
    evS p a b (Polynomial.C Polynomial.X) = algebraMap (Ainf p) (AinfP p) b := by
  simp [evS]

theorem evS_C_C (a b : Ainf p) (q : ℚ) :
    evS p a b (Polynomial.C (Polynomial.C q)) = qQ p q := by
  simp [evS]

theorem evS_cA (a b : Ainf p) : evS p a b PBLogPoly.cA =
    algebraMap (Ainf p) (AinfP p) (a * (1 + b) + b) := by
  simp [evS, PBLogPoly.cA]

theorem evS_LM (a b : Ainf p) (M : ℕ) (Z : PBLogPoly.S) :
    evS p a b (PBLogPoly.LM M Z) =
      ∑ j ∈ Finset.Ico 1 (M + 1), qQ p (PBLogPoly.κ j) * (evS p a b Z) ^ j := by
  simp only [PBLogPoly.LM, map_sum, map_mul, map_pow, evS_C_C]

theorem logPartialVal_eq_qQ (z : Ainf p) (M : ℕ) : logPartialVal p z M =
    ∑ j ∈ Finset.Ico 1 (M + 1), qQ p (PBLogPoly.κ j) * (algebraMap (Ainf p) (AinfP p) z) ^ j := by
  rw [logPartialVal]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  have e : algebraMap ℚ ℚ_[p] ((-1) ^ (j + 1) * ((j - 1).factorial : ℚ) * ((j.factorial : ℚ))⁻¹)
      = (-1) ^ (j + 1) * ((j - 1).factorial : ℚ_[p]) * ((j.factorial : ℚ_[p]))⁻¹ := by
    simp
  rw [logTerm, dpow, PBLogPoly.κ_eq j hj.1, qQ, RingHom.comp_apply, e, map_mul, map_mul, map_pow,
    map_neg, map_one, map_natCast]
  ring

theorem evS_FM (a b : Ainf p) (M : ℕ) :
    evS p a b (PBLogPoly.FM M) = logPartialVal p (a * (1 + b) + b) M - logPartialVal p a M -
      logPartialVal p b M := by
  rw [PBLogPoly.FM, map_sub, map_sub, evS_LM, evS_LM, evS_LM, evS_cA, evS_X, evS_C_X,
    logPartialVal_eq_qQ, logPartialVal_eq_qQ, logPartialVal_eq_qQ]

/-- The elements `p^n · y`, `y ∈ A_cris^0`, of `A_inf[1/p]`. -/
def pMul (n : ℕ) (w : AinfP p) : Prop := ∃ y ∈ Acris0 p, w = (p : AinfP p) ^ n * y

theorem pMul_sum (n : ℕ) {ι : Type*} (t : Finset ι) (f : ι → AinfP p)
    (h : ∀ k ∈ t, pMul p n (f k)) : pMul p n (∑ k ∈ t, f k) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, Subring.zero_mem _, by simp⟩
  | insert a t ha ih =>
    obtain ⟨y1, hy1, e1⟩ := h a (Finset.mem_insert_self a t)
    obtain ⟨y2, hy2, e2⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    exact ⟨y1 + y2, Subring.add_mem _ hy1 hy2, by rw [Finset.sum_insert ha, e1, e2]; ring⟩

theorem pow_eq_qQ_mul_dpow (i : ℕ) (z : Ainf p) :
    (algebraMap (Ainf p) (AinfP p) z) ^ i = qQ p (i.factorial : ℚ) * dpow p i z := by
  rw [dpow, qQ, RingHom.comp_apply, map_natCast, ← mul_assoc,
    ← map_mul, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i), map_one, one_mul]

/-- **Evaluation of a polynomial whose divided-power coefficients are divisible by `p^n`.** -/
theorem evS_pMul (n : ℕ) {a b : Ainf p} (ha : theta p a = 0) (hb : theta p b = 0)
    (F : PBLogPoly.S)
    (hF : ∀ i s, ∃ z : ℤ, (F.coeff i).coeff s * (i.factorial : ℚ) * (s.factorial : ℚ) =
      ((p ^ n : ℕ) : ℚ) * z) :
    pMul p n (evS p a b F) := by
  rw [evS, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  apply pMul_sum
  intro i _
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range, Finset.sum_mul]
  apply pMul_sum
  intro s _
  obtain ⟨z, hz⟩ := hF i s
  refine ⟨(z : AinfP p) * (dpow p i a * dpow p s b),
    Subring.mul_mem _ (intCast_mem _ _) (Subring.mul_mem _ (dpow_mem p i ha) (dpow_mem p s hb)), ?_⟩
  rw [pow_eq_qQ_mul_dpow, pow_eq_qQ_mul_dpow]
  have : qQ p ((F.coeff i).coeff s) * (qQ p (s.factorial : ℚ) * dpow p s b) *
      (qQ p (i.factorial : ℚ) * dpow p i a) =
      qQ p ((F.coeff i).coeff s * (i.factorial : ℚ) * (s.factorial : ℚ)) *
        (dpow p i a * dpow p s b) := by
    rw [map_mul, map_mul]; ring
  rw [this, hz, map_mul, map_natCast, map_intCast]
  push_cast
  ring

/-- The tail of the logarithm series beyond `p^n` lies in `p^n A_cris^0`. -/
theorem logPartialVal_sub_pMul {z : Ainf p} (hz : theta p z = 0) (n M : ℕ) (hM : p ^ n ≤ M) :
    pMul p n (logPartialVal p z M - logPartialVal p z (p ^ n)) := by
  rw [logPartialVal, logPartialVal,
    ← Finset.sum_Ico_consecutive _ (show 1 ≤ p ^ n + 1 by omega) (show p ^ n + 1 ≤ M + 1 by omega),
    add_sub_cancel_left]
  apply pMul_sum
  intro j hj
  rw [Finset.mem_Ico] at hj
  obtain ⟨y, hy⟩ := logTerm_eq_pow_mul p hz (show p ^ n ≤ j - 1 by omega)
  exact ⟨y, y.2, hy⟩

/-- **`LogAdditive` holds.** -/
theorem logAdditive : LogAdditive p := by
  intro x y hx hy hxy
  set a := WittVector.teichmuller p x - 1 with ha
  set b := WittVector.teichmuller p y - 1 with hb
  have hab : WittVector.teichmuller p (x * y) - 1 = a * (1 + b) + b := by
    rw [ha, hb, map_mul]; ring
  have hθa : theta p a = 0 := theta_teich_sub_one p hx
  have hθb : theta p b = 0 := theta_teich_sub_one p hy
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [map_add, evalₐ_logT, evalₐ_logT, evalₐ_logT, ← map_add, Ideal.Quotient.eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  -- work in `A_inf[1/p]` with `M = 2 p^n + 1`
  set M := 2 * p ^ n + 1 with hM
  have hpn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have h0 : pMul p n (evS p a b (PBLogPoly.FM M)) :=
    evS_pMul p n hθa hθb _ (PBLogPoly.FM_coeff_dvd (p ^ n) M hpn le_rfl)
  rw [evS_FM] at h0
  have hc : theta p (a * (1 + b) + b) = 0 := by rw [← hab]; exact theta_teich_sub_one p hxy
  have h1 := logPartialVal_sub_pMul p hc n M (by omega)
  have h2 := logPartialVal_sub_pMul p hθa n M (by omega)
  have h3 := logPartialVal_sub_pMul p hθb n M (by omega)
  obtain ⟨y0, hy0, e0⟩ := h0
  obtain ⟨y1, hy1, e1⟩ := h1
  obtain ⟨y2, hy2, e2⟩ := h2
  obtain ⟨y3, hy3, e3⟩ := h3
  refine ⟨⟨y0 - y1 + y2 + y3, by
    exact Subring.add_mem _ (Subring.add_mem _ (Subring.sub_mem _ hy0 hy1) hy2) hy3⟩, ?_⟩
  apply Subtype.ext
  change (y0 - y1 + y2 + y3) * (p : AinfP p) ^ n =
    logPartialVal p (WittVector.teichmuller p (x * y) - 1) (p ^ n) -
      (logPartialVal p (WittVector.teichmuller p x - 1) (p ^ n) +
        logPartialVal p (WittVector.teichmuller p y - 1) (p ^ n))
  rw [hab]
  linear_combination e1 - e0 - e2 - e3

/-- **`G_{ℚ_p}` acts on `B_st` by ring automorphisms** (group homomorphism `GQp p →* Aut(B_st)`). -/
def stAut : GQp p →* (Bst p ≃+* Bst p) where
  toFun σ := stEquiv p σ
  map_one' := RingEquiv.ext fun x => by
    change stAct p 1 x = x
    rw [stAct_one]; rfl
  map_mul' σ τ := RingEquiv.ext fun x => by
    change stAct p (σ * τ) x = stAct p σ (stAct p τ x)
    rw [stAct_mul p (logAdditive p)]; rfl

end LogAdd

/-! ### `u ∉ B_st^{G_K}` for every finite `K`; nontriviality of the quadratic characters -/

section UNotInvariantK

/-- `‖a‖^{deg} = ‖(minpoly a)(0)‖` in `ℚ̄_p` (Mathlib's spectral norm). -/
theorem norm_pow_natDegree_minpoly (a : PadicAlgCl p) :
    ‖a‖ ^ (minpoly ℚ_[p] a).natDegree = ‖(minpoly ℚ_[p] a).coeff 0‖ := by
  have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (L := PadicAlgCl p) a
  rw [PadicAlgCl.spectralNorm_eq] at h
  have hd : (minpoly ℚ_[p] a).natDegree ≠ 0 :=
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral a)).ne'
  rw [h, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hd]

/-- A `p^n`-th root of `p` in `ℚ̄_p` has degree divisible by `p^n` over `ℚ_p`. -/
theorem pow_dvd_natDegree_minpoly {a : PadicAlgCl p} (n : ℕ) (ha : a ^ p ^ n = (p : PadicAlgCl p)) :
    p ^ n ∣ (minpoly ℚ_[p] a).natDegree := by
  set d := (minpoly ℚ_[p] a).natDegree with hd
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at ha
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) ha.symm
  set c0 := (minpoly ℚ_[p] a).coeff 0 with hc0
  have hc0ne : c0 ≠ 0 := minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral a) ha0
  have h1 := norm_pow_natDegree_minpoly p a
  have h2 : ‖a‖ ^ p ^ n = (p : ℝ)⁻¹ := by
    rw [← norm_pow, ha, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends,
      Padic.norm_p]
  have h3 : ‖c0‖ ^ p ^ n = ((p : ℝ)⁻¹) ^ d := by
    rw [hc0, ← h1, ← pow_mul, mul_comm, pow_mul, h2]
  rw [Padic.norm_eq_zpow_neg_valuation hc0ne] at h3
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h4 : ((p : ℝ) ^ (-c0.valuation)) ^ ((p ^ n : ℕ) : ℤ) = ((p : ℝ) ^ (-1 : ℤ)) ^ (d : ℤ) := by
    rw [zpow_natCast, zpow_natCast, h3, zpow_neg_one]
  rw [← zpow_mul, ← zpow_mul] at h4
  have h5 := zpow_right_injective₀ (by positivity : (0 : ℝ) < p) hp1.ne' h4
  have h6 : (d : ℤ) = c0.valuation * ((p ^ n : ℕ) : ℤ) := by linarith
  have h7 : ((p ^ n : ℕ) : ℤ) ∣ (d : ℤ) := ⟨c0.valuation, by rw [h6]; ring⟩
  exact Int.natCast_dvd_natCast.mp h7

/-- **For every finite `K`, some `σ ∈ G_K` moves `p♭`.** -/
theorem exists_mem_fixingSubgroup_uSigma_ne_one (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] : ∃ σ ∈ K.fixingSubgroup, uSigma p σ ≠ 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank ℚ_[p] K < p ^ n :=
    ⟨Module.finrank ℚ_[p] K, Nat.lt_pow_self (Fact.out : p.Prime).one_lt⟩
  set r := ZInQ.Contrib.G9.BdrKer.Cp.root (pFlat p) n with hr
  have hrp : r ^ p ^ n = (p : 𝓞_ℂ_[p]) := by
    rw [hr, ZInQ.Contrib.G9.BdrKer.Cp.root_pow, pFlat_untilt]
  set f : Polynomial (PadicAlgCl p) := Polynomial.X ^ p ^ n - Polynomial.C (p : PadicAlgCl p) with hf
  have hf0 : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) _
  have hroot : (f.map (algebraMap (PadicAlgCl p) ℂ_[p])).IsRoot (r : ℂ_[p]) := by
    simp only [hf, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      map_natCast]
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hrp
    simp only [SubmonoidClass.coe_pow] at this
    rw [this]
    simp
  obtain ⟨a, ha⟩ := (IsAlgClosed.splits f).mem_range_of_isRoot hf0 hroot
  have hap : a ^ p ^ n = (p : PadicAlgCl p) := by
    apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
    rw [map_pow, ha, map_natCast]
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hrp
    simpa using this
  -- `a ∉ K` by degrees
  have haK : a ∉ K := by
    intro haK
    have hint : IsIntegral ℚ_[p] a := Algebra.IsIntegral.isIntegral a
    have hle : IntermediateField.adjoin ℚ_[p] {a} ≤ K :=
      IntermediateField.adjoin_simple_le_iff.mpr haK
    have h1 : (minpoly ℚ_[p] a).natDegree ≤ Module.finrank ℚ_[p] K := by
      rw [← IntermediateField.adjoin.finrank hint]
      exact IntermediateField.finrank_le_of_le_right hle
    have h2 := Nat.le_of_dvd (minpoly.natDegree_pos hint) (pow_dvd_natDegree_minpoly p n hap)
    omega
  -- some `σ ∈ G_K` moves `a`
  obtain ⟨σ, hσK, hσ⟩ : ∃ σ ∈ K.fixingSubgroup, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    apply haK
    rw [← InfiniteGalois.fixedField_fixingSubgroup K]
    exact fun σ => hcon σ.1 σ.2
  refine ⟨σ, hσK, fun h1 => hσ ?_⟩
  have h2 : flatAct p σ (pFlat p) = pFlat p := by
    rw [← uSigma_spec, h1, one_mul]
  have h3 := root_preTiltMap p (oAct p σ) (pFlat p) n
  change ZInQ.Contrib.G9.BdrKer.Cp.root (flatAct p σ (pFlat p)) n = _ at h3
  rw [h2, ← hr] at h3
  have h4 := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) h3
  change (r : ℂ_[p]) = cpAct p σ (r : ℂ_[p]) at h4
  rw [← ha] at h4
  have h5 : ((σ a : PadicAlgCl p) : ℂ_[p]) = (a : ℂ_[p]) :=
    (cpAct_coe p σ a).symm.trans h4.symm
  exact (algebraMap (PadicAlgCl p) ℂ_[p]).injective h5

/-- **`u ∉ B_st^{G_K}` for every finite `K`**: the monodromy variable is not invariant under any
open subgroup, as Fontaine's theory requires. -/
theorem X_not_mem_bstInv (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    (Polynomial.X : Bst p) ∉ bstInv p K := by
  intro h
  obtain ⟨σ, hσK, hσ⟩ := exists_mem_fixingSubgroup_uSigma_ne_one p K
  have := h σ hσK
  rw [stAct_X, add_eq_left, Polynomial.C_eq_zero, logU_eq] at this
  exact logOf_bcris_ne_zero p ⟨uSigma p σ, untilt_uSigma p σ, hσ⟩ this

/-- The quadratic character `σ ↦ σ(α)/α` is nontrivial when `α ∉ ℚ_p`. -/
theorem quadChar_ne_one {α : PadicAlgCl p} {c : ℚ_[p]} (hα : α ^ 2 = algebraMap ℚ_[p] _ c)
    (h0 : α ≠ 0) (hnot : α ∉ Set.range (algebraMap ℚ_[p] (PadicAlgCl p))) :
    quadChar p hα h0 ≠ 1 := by
  classical
  intro h1
  obtain ⟨σ, hσ⟩ : ∃ σ : GQp p, σ α ≠ α := by
    by_contra hcon
    push Not at hcon
    exact hnot ((InfiniteGalois.mem_range_algebraMap_iff_fixed α).mpr hcon)
  have h2 := congrArg (fun χ : GQp p →* GL (Fin 1) ℚ_[p] =>
    ((χ σ : Matrix (Fin 1) (Fin 1) ℚ_[p]) 0 0)) h1
  simp [quadChar, hσ] at h2
  norm_num at h2

end UNotInvariantK

/-! ### Summary -/

/-- **Summary of the unconditional sanity checks** of pb-bypass's definitions. -/
theorem panBerger_definitions_nondegenerate :
    Nontrivial (BcrisPlus p) ∧ Nontrivial (Bcris p) ∧ Nontrivial (Bst p) ∧
      (0 : BcrisPlus p) ∉ tMonoid p ∧
      (∃ e : TEps p, logOf p e ≠ 0 ∧
        ¬ IsNilpotent (algebraMap (Acris p) (BcrisPlus p) (logOf p e))) ∧
      Function.Injective (algebraMap ℚ_[p] (Bst p)) ∧
      (∀ σ : GQp p, Function.Bijective (stAct p σ)) ∧ stAct p 1 = RingHom.id _ ∧
      (∀ σ τ : GQp p, bcrisAct p (σ * τ) = (bcrisAct p σ).comp (bcrisAct p τ)) ∧
      LogAdditive p ∧
      (∀ σ τ : GQp p, stAct p (σ * τ) = (stAct p σ).comp (stAct p τ)) ∧
      (∃ σ : GQp p, stAct p σ Polynomial.X ≠ Polynomial.X) ∧
      (∀ n : ℕ, LocalIsPst p n 1) :=
  ⟨inferInstance, inferInstance, inferInstance, zero_notMem_tMonoid p, exists_t p,
    algebraMap_qp_bst_injective p, stAct_bijective p, stAct_one p, bcrisAct_mul p,
    logAdditive p, stAct_mul p (logAdditive p), exists_stAct_X_ne p, localIsPst_one p⟩

end PanBergerSplit
end PkgI4
end HDec
