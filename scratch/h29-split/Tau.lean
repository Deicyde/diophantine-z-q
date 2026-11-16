import ZInQKernel.Contrib.TYZDecomp.Leaves

/-! h29-split: `TYZTauExists` from the three-square statement (test file; definitions copied from
`TYZLemma29Mod2.lean` §5). -/

noncomputable section

namespace ZInQ.Contrib.TYZDecomp.H29Split

open ZInQ.RouteK.Rank5b NumberField
open scoped Quaternion

def IsHurwitz (q : ℍ[ℚ]) : Prop :=
  ∃ a b c d e : ℤ, q = ⟨a - e / 2, b + e / 2, c + e / 2, d + e / 2⟩

abbrev sqrtNeg (n : ℕ) : QNeg n := QuadraticAlgebra.omega

def AdmissibleTau (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) : Prop :=
  (∀ x : 𝓞 (QNeg n), IsHurwitz (τ (x : QNeg n))) ∧
    (n % 8 = 1 → ∃ a b c : ℤ, (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 ∧ 4 ∣ c ∧
      τ (sqrtNeg n) = ⟨0, (a : ℚ), (b : ℚ), (c : ℚ)⟩)

def TYZTauExists : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∃ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ

/-- **Legendre's three-square theorem with the Jones–Pall refinement, as cited by TYZ (L533)**. -/
def LegendreJonesPall : Prop :=
  ∀ n : ℕ, Squarefree n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∃ a b c : ℤ, (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 ∧ (n % 8 = 1 → 4 ∣ c)

/-- The pure quaternion `ai + bj + ck`. -/
def pq (a b c : ℤ) : ℍ[ℚ] := ⟨0, a, b, c⟩

theorem pq_mul_self {n : ℕ} {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) :
    pq a b c * pq a b c = (-(n : ℚ)) • (1 : ℍ[ℚ]) + (0 : ℚ) • pq a b c := by
  have hq : (n : ℚ) = (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 := by exact_mod_cast h
  apply Quaternion.ext <;>
    simp [pq, hq] <;> ring

/-- `τ : K_n → B`, `√−n ↦ ai + bj + ck`. -/
def tauOf (n : ℕ) {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) : QNeg n →ₐ[ℚ] ℍ[ℚ] :=
  QuadraticAlgebra.lift ⟨pq a b c, pq_mul_self h⟩

theorem tauOf_apply (n : ℕ) {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) (x : QNeg n) :
    tauOf n h x = ⟨x.re, x.im * a, x.im * b, x.im * c⟩ := by
  rw [tauOf, QuadraticAlgebra.lift_apply_apply]
  apply Quaternion.ext <;> simp [pq, Algebra.smul_def]

/-- Integral elements of `ℚ(√−n)` have integral trace and norm. -/
theorem trace_norm_int {n : ℕ} [NeZero n] (x : 𝓞 (QNeg n)) :
    (∃ m : ℤ, (m : ℚ) = 2 * (x : QNeg n).re) ∧
      ∃ N : ℤ, (N : ℚ) = (x : QNeg n).re ^ 2 + n * (x : QNeg n).im ^ 2 := by
  have hx : IsIntegral ℤ (x : QNeg n) := x.2
  have hs : IsIntegral ℤ (star (x : QNeg n)) :=
    hx.map ((starRingEnd (QNeg n)).toIntAlgHom)
  have h1 : (x : QNeg n) + star (x : QNeg n) = algebraMap ℚ (QNeg n) (2 * (x : QNeg n).re) := by
    rw [QuadraticAlgebra.algebraMap_eq]
    ext <;> simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, QuadraticAlgebra.re_C, QuadraticAlgebra.im_C] <;> ring
  have h2 : (x : QNeg n) * star (x : QNeg n) =
      algebraMap ℚ (QNeg n) ((x : QNeg n).re ^ 2 + n * (x : QNeg n).im ^ 2) := by
    rw [QuadraticAlgebra.algebraMap_eq]
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, QuadraticAlgebra.re_C, QuadraticAlgebra.im_C] <;> ring
  have i1 : IsIntegral ℤ (2 * (x : QNeg n).re) := by
    have := hx.add hs
    rw [h1] at this
    exact isIntegral_algebraMap_iff.mp this
  have i2 : IsIntegral ℤ ((x : QNeg n).re ^ 2 + n * (x : QNeg n).im ^ 2) := by
    have := hx.mul hs
    rw [h2] at this
    exact isIntegral_algebraMap_iff.mp this
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp i1
  obtain ⟨N, hN⟩ := IsIntegrallyClosed.isIntegral_iff.mp i2
  exact ⟨⟨m, by simpa using hm⟩, ⟨N, by simpa using hN⟩⟩

/-- `n w² ∈ ℤ` with `n` squarefree forces `w ∈ ℤ`. -/
theorem int_of_sqfree_mul_sq {n : ℕ} (hn : Squarefree n) {w : ℚ} {k : ℤ}
    (h : (n : ℚ) * w ^ 2 = k) : ∃ z : ℤ, (z : ℚ) = w := by
  have hden : (w.den : ℚ) ≠ 0 := by exact_mod_cast w.den_nz
  have hw : w = w.num / w.den := (Rat.num_div_den w).symm
  have key : (n : ℤ) * w.num ^ 2 = k * (w.den : ℤ) ^ 2 := by
    have : (n : ℚ) * (w.num : ℚ) ^ 2 = k * (w.den : ℚ) ^ 2 := by
      rw [hw] at h
      field_simp at h
      linarith
    exact_mod_cast this
  have hcop : IsCoprime ((w.den : ℤ) ^ 2) (w.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact w.reduced
  have hd : (w.den : ℤ) ^ 2 ∣ (n : ℤ) * w.num ^ 2 := ⟨k, by rw [key]; ring⟩
  have hd2 : (w.den : ℤ) ^ 2 ∣ (n : ℤ) := hcop.dvd_of_dvd_mul_right hd
  have hd3 : w.den * w.den ∣ n := by
    have : ((w.den * w.den : ℕ) : ℤ) ∣ (n : ℤ) := by push_cast; rwa [← sq]
    exact_mod_cast this
  have h1 : w.den = 1 := Nat.isUnit_iff.mp (hn _ hd3)
  exact ⟨w.num, by rw [hw, h1]; simp⟩

theorem parity_one {m V N k : ℤ} (h : 4 * N = m ^ 2 + (8 * k + 1) * V ^ 2) :
    (∃ s, m = 2 * s) ∧ ∃ t, V = 2 * t := by
  rcases Int.even_or_odd' m with ⟨s, rfl | rfl⟩ <;> rcases Int.even_or_odd' V with ⟨t, rfl | rfl⟩
  · exact ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
  all_goals (exfalso; ring_nf at h; omega)

theorem parity_three {m V N k : ℤ} (h : 4 * N = m ^ 2 + (8 * k + 3) * V ^ 2) :
    ((∃ s, m = 2 * s) ∧ ∃ t, V = 2 * t) ∨ ((∃ s, m = 2 * s + 1) ∧ ∃ t, V = 2 * t + 1) := by
  rcases Int.even_or_odd' m with ⟨s, rfl | rfl⟩ <;> rcases Int.even_or_odd' V with ⟨t, rfl | rfl⟩
  · exact Or.inl ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
  · exfalso; ring_nf at h; omega
  · exfalso; ring_nf at h; omega
  · exact Or.inr ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩

theorem odd_of_three {a b c k : ℤ} (h : 8 * k + 3 = a ^ 2 + b ^ 2 + c ^ 2) :
    (∃ a', a = 2 * a' + 1) ∧ (∃ b', b = 2 * b' + 1) ∧ ∃ c', c = 2 * c' + 1 := by
  rcases Int.even_or_odd' a with ⟨a', rfl | rfl⟩ <;> rcases Int.even_or_odd' b with ⟨b', rfl | rfl⟩ <;>
    rcases Int.even_or_odd' c with ⟨c', rfl | rfl⟩
  all_goals first
    | exact ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩
    | (exfalso; ring_nf at h; omega)

/-- **Glue: the explicit `τ` is admissible.** -/
theorem admissible_tauOf {n : ℕ} [NeZero n] (hsq : Squarefree n) (hcl : n % 8 = 1 ∨ n % 8 = 3)
    {a b c : ℤ} (h : (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2) (h4 : n % 8 = 1 → 4 ∣ c) :
    AdmissibleTau n (tauOf n h) := by
  refine ⟨fun x => ?_, fun hn => ⟨a, b, c, h, h4 hn, ?_⟩⟩
  · obtain ⟨⟨m, hm⟩, ⟨N, hN⟩⟩ := trace_norm_int x
    set u := (x : QNeg n).re with hu
    set v := (x : QNeg n).im with hv
    have hV : (n : ℚ) * (2 * v) ^ 2 = ((4 * N - m ^ 2 : ℤ) : ℚ) := by
      push_cast; rw [hN, hm]; ring
    obtain ⟨V, hVv⟩ := int_of_sqfree_mul_sq hsq hV
    have hEq : 4 * N = m ^ 2 + (n : ℤ) * V ^ 2 := by
      have : ((4 * N : ℤ) : ℚ) = ((m ^ 2 + (n : ℤ) * V ^ 2 : ℤ) : ℚ) := by
        push_cast; rw [hN, hm, hVv]; ring
      exact_mod_cast this
    have hk : (n : ℤ) = 8 * ((n / 8 : ℕ) : ℤ) + ((n % 8 : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod n 8).symm
    rw [tauOf_apply]
    have hev : (∃ s, m = 2 * s) ∧ (∃ t, V = 2 * t) → IsHurwitz ⟨u, v * a, v * b, v * c⟩ := by
      rintro ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
      have hus : u = s := by push_cast at hm; linarith
      have hvt : v = t := by push_cast at hVv; linarith
      refine ⟨s, t * a, t * b, t * c, 0, ?_⟩
      apply Quaternion.ext <;> simp [hus, hvt]
    rcases hcl with h1 | h3
    · rw [h1] at hk
      push_cast at hk
      rw [hk] at hEq
      exact hev (parity_one hEq)
    · rw [h3] at hk
      push_cast at hk
      rw [hk] at hEq
      rcases parity_three hEq with he | ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
      · exact hev he
      · rw [hk] at h
        obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := odd_of_three h
        have hus : u = s + 1 / 2 := by push_cast at hm; linarith
        have hvt : v = t + 1 / 2 := by push_cast at hVv; linarith
        refine ⟨s + 1, 2 * t * a' + t + a', 2 * t * b' + t + b', 2 * t * c' + t + c', 1, ?_⟩
        have e1 : (x : QNeg n).re = s + 1 / 2 := hu ▸ hus
        have e2 : (x : QNeg n).im = t + 1 / 2 := hv ▸ hvt
        rw [e1, e2]
        apply Quaternion.ext <;> simp <;> ring
  · rw [tauOf_apply]
    apply Quaternion.ext <;> simp [sqrtNeg]

/-- **`TYZTauExists` from the three-square statement.** -/
theorem tyzTauExists_of_legendreJonesPall (h : LegendreJonesPall) : TYZTauExists := by
  intro n _ hsq hcl
  obtain ⟨a, b, c, habc, h4⟩ := h n hsq hcl
  exact ⟨tauOf n habc, admissible_tauOf hsq hcl habc h4⟩

end ZInQ.Contrib.TYZDecomp.H29Split

#print axioms ZInQ.Contrib.TYZDecomp.H29Split.tyzTauExists_of_legendreJonesPall
