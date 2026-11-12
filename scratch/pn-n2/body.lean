/-! ### Lemma N2: helpers (prefix `n2_`) -/

theorem n2_div_mod8 {m q a c : ℕ} (hq : q ∣ m) (hm : m % 8 = a) (hc : q % 8 = c)
    (hc' : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) : m / q % 8 = (a * c) % 8 := by
  have h : m % 8 = (m / q % 8) * (q % 8) % 8 := by
    conv_lhs => rw [← Nat.div_mul_cancel hq]
    exact Nat.mul_mod _ _ _
  have hx : m / q % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [hm, hc] at h
  subst hm hc
  rcases hc' with hb | hb | hb | hb <;> rw [hb] at h ⊢ <;>
    interval_cases hr : m / q % 8 <;> omega

theorem n2_mod8_mul {m q : ℕ} (hq : q ∣ m) : (q % 8) * (m / q % 8) % 8 = m % 8 := by
  conv_rhs => rw [← Nat.mul_div_cancel' hq]
  exact (Nat.mul_mod _ _ _).symm

/-- The ring `ℤ[i]/(2)`. -/
abbrev n2_R : Type := GaussianInt ⧸ Ideal.span {(2 : GaussianInt)}

abbrev n2_π : GaussianInt →+* n2_R := Ideal.Quotient.mk _

theorem n2_two : (2 : n2_R) = 0 := by
  rw [show (2 : n2_R) = n2_π 2 from (map_ofNat n2_π 2).symm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem n2_neg (x : n2_R) : -x = x :=
  neg_eq_iff_add_eq_zero.mpr (by rw [← two_mul, n2_two, zero_mul])

/-- The class of `i` in `ℤ[i]/(2)`. -/
def n2_I : n2_R := n2_π gi

/-- The class of `ε(d₀, d₁)` modulo 2, from the classes `a = d₀ % 8`, `c = d₁ % 8`. -/
def n2_epsR (a c : ℕ) : n2_R := if a = 5 ∧ c = 3 then n2_I else 1

/-- `φ(d, e)` modulo 2, from `a = d % 8`, `b = e % 8`. -/
def n2_phi (a b : ℕ) : n2_R := if a = 7 ∧ b = 5 then n2_I else 1

theorem n2_eps {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) {x y : ℕ} (hxy : x * y ∣ n)
    (hx : x % 8 = 5 ∨ x % 8 = 7) (hy : y % 8 = 1 ∨ y % 8 = 3) :
    n2_π (G.ε x y) = n2_epsR (x % 8) (y % 8) := by
  by_cases h53 : x % 8 = 5 ∧ y % 8 = 3
  · rw [n2_epsR, ite_eq_left h53, n2_I]
    rcases G.eps_53 x y hxy h53.1 h53.2 with h | h <;> simp [h, n2_neg]
  · rw [n2_epsR, ite_eq_right h53]
    have : x % 8 = 5 ∧ y % 8 = 1 ∨ x % 8 = 7 ∧ y % 8 = 1 ∨ x % 8 = 7 ∧ y % 8 = 3 := by omega
    rcases G.eps_pm1 x y hxy this with h | h <;> simp [h, n2_neg]

/-- `κ(q) = ε(d/q, q) φ(d/q, e)` modulo 2 takes the same value at `q` and `m/q` (`m = d/e`). -/
theorem n2_kappa {a b c c' x x' : ℕ} (ha : a = 5 ∨ a = 7) (hb : b = 5 ∨ b = 7)
    (hc : c = 1 ∨ c = 3) (hc' : c' = 1 ∨ c' = 3) (hx : x = a * c % 8) (hx' : x' = a * c' % 8)
    (h : c * c' % 8 = a * b % 8) :
    n2_epsR x c * n2_phi x b = n2_epsR x' c' * n2_phi x' b := by
  subst hx hx'
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hc' with rfl | rfl <;> revert h <;> norm_num [n2_epsR, n2_phi]

/-- The surviving term: `ε(e, d/e) ≡ φ(d, e)`. -/
theorem n2_last {a b : ℕ} (ha : a = 5 ∨ a = 7) (hb : b = 5 ∨ b = 7) :
    n2_epsR b (a * b % 8) * n2_phi b b = n2_phi a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [n2_epsR, n2_phi]

/-- The coefficient of `Z(e)` in `P(d)`, defined by the recursion of TYZ §3.1. -/
def n2_c (ε : ℕ → ℕ → GaussianInt) (L : ℕ → ℤ) (e : ℕ) : ℕ → GaussianInt
  | d => (if e = d then 1 else 0) -
      ∑ q ∈ (d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3))).attach,
        (ε (d / q) q * (L q : GaussianInt)) * n2_c ε L e (d / q)
decreasing_by
  have h := q.2
  simp only [Finset.mem_filter, Nat.mem_divisors] at h
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h.1.2) h.2.1

theorem n2_c_eq (ε : ℕ → ℕ → GaussianInt) (L : ℕ → ℤ) (e d : ℕ) :
    n2_c ε L e d = (if e = d then 1 else 0) -
      ∑ q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
        (ε (d / q) q * (L q : GaussianInt)) * n2_c ε L e (d / q) := by
  rw [n2_c]
  congr 1
  exact Finset.sum_attach _ (fun q => (ε (d / q) q * (L q : GaussianInt)) * n2_c ε L e (d / q))

theorem n2_mem_Q {n d q : ℕ} (hd : d ∈ n.divisors) (hcl : d % 8 = 5 ∨ d % 8 = 7)
    (hq : q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3))) :
    q ∣ d ∧ 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3) ∧ d / q < d ∧ d / q ∈ n.divisors ∧
      (d / q % 8 = 5 ∨ d / q % 8 = 7) := by
  simp only [Finset.mem_filter, Nat.mem_divisors] at hq
  obtain ⟨⟨hqd, hd0⟩, hq1, hq8⟩ := hq
  refine ⟨hqd, hq1, hq8, Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hq1, ?_, ?_⟩
  · rw [Nat.mem_divisors] at hd ⊢
    exact ⟨(Nat.div_dvd_of_dvd hqd).trans hd.1, hd.2⟩
  · rcases hcl with h | h <;> rcases hq8 with h' | h' <;>
      rw [n2_div_mod8 hqd h h' (by omega)] <;> norm_num

/-- `P(d) = Σ_e c_d(e) Z(e)` over the fixed index set `e ∣ n`, `e ≡ 5, 7`. -/
theorem n2_P_eq {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) :
    ∀ d ∈ n.divisors, (d % 8 = 5 ∨ d % 8 = 7) →
      G.P d = ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
        n2_c G.ε L e d • G.Z e := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd hcl
  have hdE : d ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7) :=
    Finset.mem_filter.mpr ⟨hd, hcl⟩
  rw [G.recursion d hd hcl]
  have hstep : ∀ q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
      (G.ε (d / q) q * (L q : GaussianInt)) • G.P (d / q) =
        ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
          ((G.ε (d / q) q * (L q : GaussianInt)) * n2_c G.ε L e (d / q)) • G.Z e := by
    intro q hq
    obtain ⟨-, -, -, hlt, hdn, hcl'⟩ := n2_mem_Q hd hcl hq
    rw [ih (d / q) hlt hdn hcl', Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← mul_smul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  conv_rhs => enter [2, e]; rw [n2_c_eq]
  simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', hdE, ite_true]

/-- `e ∣ d/q ↔ q ∣ d/e` for divisors `e, q` of `d`. -/
theorem n2_dvd_iff {d e q : ℕ} (he : e ∣ d) (hq : q ∣ d) : e ∣ d / q ↔ q ∣ d / e := by
  rw [Nat.dvd_div_iff_mul_dvd hq, Nat.dvd_div_iff_mul_dvd he, mul_comm]

/-- **The inductive identity**: `c_d(e) ≡ φ(d, e) 𝓛(d/e)` modulo `2ℤ[i]` (and `c_d(e) ≡ 0` if
`e ∤ d`). -/
theorem n2_c_mod {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) (hsq : Squarefree n) (hL1 : L 1 = 1)
    {e : ℕ} (he : e % 8 = 5 ∨ e % 8 = 7) :
    ∀ d ∈ n.divisors, (d % 8 = 5 ∨ d % 8 = 7) →
      n2_π (n2_c G.ε L e d) =
        if e ∣ d then n2_phi (d % 8) (e % 8) * ((L (d / e) : ℤ) : n2_R) else 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd hcl
  have hd0 : d ≠ 0 := by omega
  have he0 : e ≠ 0 := by omega
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  rw [n2_c_eq, map_sub, map_sum]
  have hterm : ∀ q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
      n2_π ((G.ε (d / q) q * (L q : GaussianInt)) * n2_c G.ε L e (d / q)) =
        if e ∣ d / q then n2_epsR (d / q % 8) (q % 8) * ((L q : ℤ) : n2_R) *
          (n2_phi (d / q % 8) (e % 8) * ((L (d / q / e) : ℤ) : n2_R)) else 0 := by
    intro q hq
    obtain ⟨hqd, -, hq8, hlt, hdqn, hcl'⟩ := n2_mem_Q hd hcl hq
    rw [map_mul, map_mul, n2_eps G (by rw [Nat.div_mul_cancel hqd]; exact hdn) hcl' hq8,
      map_intCast, ih (d / q) hlt hdqn hcl']
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm]
  by_cases hed : e ∣ d
  swap
  · have hne : e ≠ d := by rintro rfl; exact hed dvd_rfl
    rw [ite_eq_right hed, ite_eq_right hne, map_zero, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [ite_eq_right]
    intro h
    exact hed (h.trans (Nat.div_dvd_of_dvd (n2_mem_Q hd hcl hq).1))
  rw [ite_eq_left hed]
  by_cases hee : e = d
  · subst hee
    rw [ite_eq_left rfl, map_one, Nat.div_self (Nat.pos_of_ne_zero he0), hL1, Finset.sum_eq_zero,
      sub_zero, n2_phi, ite_eq_right (by omega), Int.cast_one, one_mul]
    intro q hq
    obtain ⟨hqd, hq1, -, -, -, -⟩ := n2_mem_Q hd hcl hq
    rw [ite_eq_right]
    intro h
    have hpos : 0 < e / q := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hqd) (by omega)
    have h1 := Nat.le_of_dvd hpos h
    have h2 := Nat.div_lt_self (Nat.pos_of_ne_zero he0) hq1
    omega
  rw [ite_eq_right hee, map_zero, zero_sub, n2_neg]
  obtain ⟨m, hm⟩ : ∃ m, d / e = m := ⟨_, rfl⟩
  rw [hm]
  have hdem : e * m = d := by rw [← hm]; exact Nat.mul_div_cancel' hed
  have hm1 : 1 < m := by
    rcases (show m = 0 ∨ m = 1 ∨ 1 < m by omega) with h | h | h
    · subst h; omega
    · subst h; omega
    · exact h
  have hm0 : m ≠ 0 := by omega
  have hmd : m ∣ d := Dvd.intro_left e hdem
  have hdme : d / m = e := Nat.div_eq_of_eq_mul_left (by omega) hdem.symm
  have hm8 : m % 8 = d % 8 * (e % 8) % 8 := by
    rw [← hm]; exact n2_div_mod8 hed rfl rfl (by omega)
  have hm13 : m % 8 = 1 ∨ m % 8 = 3 := by
    rw [hm8]; rcases hcl with h | h <;> rcases he with h' | h' <;> rw [h, h'] <;> norm_num
  have hmQ : m ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)) := by
    rw [Finset.mem_filter, Nat.mem_divisors]; exact ⟨⟨hmd, hd0⟩, hm1, hm13⟩
  have hdiv : ∀ q, q ∣ m → d / q / e = m / q := fun q _ => by
    rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul, hm]
  rw [← Finset.add_sum_erase _ _ hmQ]
  have hrest : ∑ q ∈ (d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3))).erase m,
      (if e ∣ d / q then n2_epsR (d / q % 8) (q % 8) * ((L q : ℤ) : n2_R) *
          (n2_phi (d / q % 8) (e % 8) * ((L (d / q / e) : ℤ) : n2_R)) else 0) = 0 := by
    refine Finset.sum_involution (fun q _ => if e ∣ d / q then m / q else q) ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨hqm, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, hq1, hq8, -, -, hcl'⟩ := n2_mem_Q hd hcl hqQ
      by_cases h : e ∣ d / q
      · have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
        have hq'd : m / q ∣ d := (Nat.div_dvd_of_dvd hqm').trans hmd
        have h' : e ∣ d / (m / q) := by
          rw [n2_dvd_iff hed hq'd, hm]; exact Nat.div_dvd_of_dvd hqm'
        simp only [h, h', ↓reduceIte]
        rw [hdiv q hqm', hdiv (m / q) (Nat.div_dvd_of_dvd hqm'), Nat.div_div_self hqm' hm0]
        have hq'8 : m / q % 8 = 1 ∨ m / q % 8 = 3 := by
          rcases hm13 with h1 | h1 <;> rcases hq8 with h2 | h2 <;>
            rw [n2_div_mod8 hqm' h1 h2 (by omega)] <;> norm_num
        have hk := n2_kappa hcl he hq8 hq'8 (n2_div_mod8 hqd rfl rfl (by omega))
          (n2_div_mod8 hq'd rfl rfl (by omega)) (by rw [n2_mod8_mul hqm', hm8])
        linear_combination (((L q : ℤ) : n2_R) * ((L (m / q) : ℤ) : n2_R)) * hk +
          (n2_epsR (d / (m / q) % 8) (m / q % 8) * n2_phi (d / (m / q) % 8) (e % 8) *
            ((L q : ℤ) : n2_R) * ((L (m / q) : ℤ) : n2_R)) * n2_two
      · simp only [h, ↓reduceIte, add_zero]
    · intro q hq hf
      obtain ⟨hqm, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, hq1, -, -, -, -⟩ := n2_mem_Q hd hcl hqQ
      have h : e ∣ d / q := by
        by_contra h; apply hf; simp only [h, ↓reduceIte]
      have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
      simp only [h, ↓reduceIte]
      intro heq
      have hmqq : q * q = m := by
        conv_rhs => rw [← Nat.div_mul_cancel hqm', heq]
      have hu := hsq q (by rw [hmqq]; exact hmd.trans hdn)
      rw [Nat.isUnit_iff] at hu
      omega
    · intro q hq
      obtain ⟨hqm, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, hq1, hq8, -, -, -⟩ := n2_mem_Q hd hcl hqQ
      by_cases h : e ∣ d / q
      · have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
        simp only [h, ↓reduceIte]
        refine Finset.mem_erase.mpr ⟨(Nat.div_lt_self (by omega) hq1).ne, ?_⟩
        rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨(Nat.div_dvd_of_dvd hqm').trans hmd, hd0⟩, ?_, ?_⟩
        · obtain ⟨k, hk⟩ := id hqm'
          rw [hk, Nat.mul_div_cancel_left _ (by omega : 0 < q)]
          rcases k with _ | _ | k
          · simp at hk; omega
          · simp at hk; omega
          · omega
        · rcases hm13 with h1 | h1 <;> rcases hq8 with h2 | h2 <;>
            rw [n2_div_mod8 hqm' h1 h2 (by omega)] <;> norm_num
      · simp only [h, ↓reduceIte]; exact hq
    · intro q hq
      obtain ⟨-, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, -, -, -, -, -⟩ := n2_mem_Q hd hcl hqQ
      by_cases h : e ∣ d / q
      · have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
        have hq'd : m / q ∣ d := (Nat.div_dvd_of_dvd hqm').trans hmd
        have h' : e ∣ d / (m / q) := by
          rw [n2_dvd_iff hed hq'd, hm]; exact Nat.div_dvd_of_dvd hqm'
        simp only [h, h', ↓reduceIte]
        exact Nat.div_div_self hqm' hm0
      · simp only [h, ↓reduceIte]
  rw [hrest, add_zero]
  simp only [hdme, dvd_rfl, ↓reduceIte, Nat.div_self (Nat.pos_of_ne_zero he0), hL1, Int.cast_one,
    mul_one]
  rw [hm8]
  linear_combination ((L m : ℤ) : n2_R) * n2_last hcl he
