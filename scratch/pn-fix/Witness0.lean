import ZInQKernel.RouteK.PropN

noncomputable section

namespace ZInQ.PropN
namespace Witness

open ZInQ.Literature ZInQ.RouteK.Rank5b

/-- `Pw L` reads `L` only on the classes `1, 3 (mod 8)`. -/
theorem Pw_congr {L L' : ℕ → ℤ} (h : ∀ q, (q % 8 = 1 ∨ q % 8 = 3) → L q = L' q) :
    Pw L = Pw L' := by
  funext d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rw [Pw_eq, Pw_eq L']
    congr 1
    refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd₁
    rw [h d₁ hd₁.2.2, ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero hd₁.1.2) hd₁.2.1)]

/-- The points `Pw L d` have zero torsion component. -/
theorem Pw_fst (L : ℕ → ℤ) (d : ℕ) : (Pw L d).1 = 0 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rw [Pw_eq, Prod.fst_sub, Prod.fst_sum]
    simp only [Prod.smul_fst, Zw, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun d₁ hd₁ => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd₁
    rw [ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero hd₁.1.2) hd₁.2.1), smul_zero]

/-- The correction term of the recursion at `n`: `Pw L n = Zw n − Sw L n`. -/
def Sw (L : ℕ → ℤ) (n : ℕ) : Mw :=
  ∑ q ∈ n.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
    (epsW (n / q) q * (L q : GaussianInt)) • Pw L (n / q)

theorem Pw_eq_sub (L : ℕ → ℤ) (n : ℕ) : Pw L n = Zw n - Sw L n := Pw_eq L n

theorem Sw_fst (L : ℕ → ℤ) (n : ℕ) : (Sw L n).1 = 0 := by
  rw [Sw, Prod.fst_sum]
  exact Finset.sum_eq_zero fun q _ => by rw [Prod.smul_fst, Pw_fst, smul_zero]

/-- `Φ = λ ∘ pr₂`, where `λ = Σ_e v_e c_e`; `βw x + x = (2 x.1 + Φ x, 0)`. -/
def Φw : Mw →+ Tq :=
  (Finsupp.linearCombination GaussianInt cw).toAddMonoidHom.comp
    (AddMonoidHom.snd Tq (ℕ →₀ GaussianInt))

theorem Φw_Zw (e : ℕ) : Φw (Zw e) = cw e := by
  simp [Φw, Zw, Finsupp.linearCombination_single]

/-- The key identity for `beta_five` at `e = n`: with `a = Σ_{e≡5} L(n/e) g(e)` and
`N = Σ_{e≡7} L(n/e) g(e)` both even, `Φ(Sw L n) ∈ g(n) τ(1−i) + ℤ τ(2)` in `Tq`. -/
theorem Φw_Sw {L : ℕ → ℤ} {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) (hL1 : L 1 = 1)
    (h5 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0))
    (h7 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0)) :
    ∃ k : ℤ, Φw (Sw L n) = (gNat n : ℤ) • Ideal.Quotient.mk _ (⟨1, -1⟩ : GaussianInt) +
      k • Ideal.Quotient.mk (Ideal.span {twoTwoI}) (2 : GaussianInt) := by
  classical
  have hn1 : n ≠ 1 := by omega
  set L' := Function.update L n 1 with hL'
  have hL'n : L' n ≠ 0 := by simp [hL']
  have hL'1 : L' 1 = 1 := by rw [hL', Function.update_of_ne (Ne.symm hn1), hL1]
  obtain ⟨X, hX⟩ := lemmaN2 (witnessData L' n hL'n) hn hsq hL'1
  have hPw : Pw L' = Pw L :=
    Pw_congr fun q hq => by rw [hL', Function.update_of_ne (by omega)]
  set Xw : Mw := X with hXw
  have hX' : Pw L' n = ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
      L' (n / e) • Zw e + (2 : ℤ) • Xw := hX
  clear_value Xw
  rw [hPw, Pw_eq_sub] at hX'
  clear hX
  have hX := hX'
  have hΦ := congrArg Φw hX
  simp only [map_sub, map_add, map_sum, map_zsmul, Φw_Zw] at hΦ
  -- the coefficients `L'(n/e) = L(n/e)` (`n/e < n`)
  have hcoef : ∀ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7), L' (n / e) = L (n / e) := by
    intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    rw [hL', Function.update_of_ne]
    exact (Nat.div_lt_self (by omega) (by omega)).ne
  rw [Finset.sum_congr rfl fun e he => by rw [hcoef e he]] at hΦ
  set F5 := n.divisors.filter (fun e => e % 8 = 5) with hF5
  set F7 := n.divisors.filter (fun e => e % 8 = 7) with hF7
  have hsplit : n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7) = F5 ∪ F7 :=
    Finset.filter_or _ _ _
  have hdisj : Disjoint F5 F7 :=
    Finset.disjoint_filter.2 (fun _ _ h1 h2 => by omega)
  set a := ∑ e ∈ F5, L (n / e) * (gNat e : ℤ) with ha
  set N := ∑ e ∈ F7, L (n / e) * (gNat e : ℤ) with hN
  let mk := Ideal.Quotient.mk (Ideal.span {twoTwoI})
  have hs5 : ∑ e ∈ F5, L (n / e) • cw e = mk (a • (⟨1, -1⟩ : GaussianInt)) := by
    rw [map_zsmul, ha, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hF5, Finset.mem_filter] at he
    rw [cw, ite_eq_left he.2, smul_smul]
  have hs7 : ∑ e ∈ F7, L (n / e) • cw e = mk (N • (1 : GaussianInt)) := by
    rw [map_zsmul, hN, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hF7, Finset.mem_filter] at he
    rw [cw, ite_eq_right (by omega), smul_smul]
  rw [hsplit, Finset.sum_union hdisj, hs5, hs7] at hΦ
  have hcwn : cw n = mk ((gNat n : ℤ) • (⟨1, -1⟩ : GaussianInt)) := by
    rw [cw, ite_eq_left hn, map_zsmul]
  rw [hcwn] at hΦ
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (Φw Xw)
  rw [← hx] at hΦ
  obtain ⟨a₁, ha₁⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp h5
  obtain ⟨N₁, hN₁⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd N 2).mp h7
  refine ⟨-N₁ - x.re + x.im, ?_⟩
  have hS : Φw (Sw L n) = mk ((gNat n : ℤ) • (⟨1, -1⟩ : GaussianInt) - a • (⟨1, -1⟩ : GaussianInt)
      - N • (1 : GaussianInt) - (2 : ℤ) • x) := by
    rw [map_sub, map_sub, map_sub, map_zsmul _ (2 : ℤ) x]
    rw [← sub_eq_zero] at hΦ ⊢
    rw [← neg_eq_zero, ← hΦ]; abel
  rw [hS, ← map_zsmul, ← map_zsmul, ← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨⟨-x.im, a₁⟩, ?_⟩
  ext <;> simp [twoTwoI, ha₁, hN₁] <;> ring

/-- The witness for `L n = 0` (`rv-pn-encoding` F1): as `witnessData`, but `Z n := Sw L n` and
`P n := 0`. It needs the two parities of `finalStep`'s conclusion, for `beta_five` at `e = n`. -/
def witnessData₀ (L : ℕ → ℤ) (n : ℕ) (hn : n % 8 = 5) (hsq : Squarefree n) (hL1 : L 1 = 1)
    (h5 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0))
    (h7 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0)) : GenusData L n where
  M := Mw
  Z := Function.update Zw n (Sw L n)
  P := Function.update (Pw L) n 0
  ε := epsW
  eps_53 := (witnessData (Function.update L n 1) n (by simp)).eps_53
  eps_pm1 := (witnessData (Function.update L n 1) n (by simp)).eps_pm1
  recursion := by
    intro d hd _
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hn0 : n ≠ 0 := by omega
    -- `P (d / d₁) = Pw L (d / d₁)`, since `d / d₁ < d ≤ n`
    have hsum : ∀ d₁ ∈ d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3)),
        (epsW (d / d₁) d₁ * (L d₁ : GaussianInt)) • Function.update (Pw L) n 0 (d / d₁) =
        (epsW (d / d₁) d₁ * (L d₁ : GaussianInt)) • Pw L (d / d₁) := by
      intro d₁ hd₁
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd₁
      rw [Function.update_of_ne]
      exact ((Nat.div_lt_self (Nat.pos_of_ne_zero hd₁.1.2) hd₁.2.1).trans_le
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn)).ne
    rw [Finset.sum_congr rfl hsum]
    by_cases hdn' : d = n
    · subst hdn'
      rw [Function.update_self, Function.update_self]
      exact (sub_self _).symm
    · rw [Function.update_of_ne hdn', Function.update_of_ne hdn']
      exact Pw_eq L d
  torsion_of_zero := by
    intro _
    rw [Function.update_self]
    exact IsOfFinAddOrder.zero
  τ := τw
  τ_eq_zero := (witnessData (Function.update L n 1) n (by simp)).τ_eq_zero
  tors_mem_range := (witnessData (Function.update L n 1) n (by simp)).tors_mem_range
  β := βw
  β_τ := (witnessData (Function.update L n 1) n (by simp)).β_τ
  beta_five := by
    intro e he h5e
    by_cases hen : e = n
    · subst hen
      rw [Function.update_self]
      obtain ⟨k, hk⟩ := Φw_Sw hn hsq hL1 h5 h7
      refine ⟨k, ?_⟩
      have hΦ : (βw (Sw L e) + Sw L e) = (Φw (Sw L e), 0) := by
        refine Prod.ext ?_ ?_
        · simp only [βw, Prod.fst_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Sw_fst, zero_add,
            add_zero]
          rfl
        · show -(Sw L e).2 + (Sw L e).2 = 0
          exact neg_add_cancel _
      rw [hΦ, hk]
      ext <;> simp [τw]
    · rw [Function.update_of_ne hen]
      exact (witnessData (Function.update L n 1) n (by simp)).beta_five e he h5e
  beta_seven := by
    intro e he h7e
    rw [Function.update_of_ne (by omega)]
    exact (witnessData (Function.update L n 1) n (by simp)).beta_seven e he h7e

/-- **`GenusData`'s content for `L n = 0` is exactly the conclusion of Proposition N's final step**
(`rv-pn-encoding` F1): for squarefree `n ≡ 5 (mod 8)` with `L 1 = 1` and `L n = 0`, `GenusData L n`
is inhabited if and only if `Σ_{e≡5} L(n/e) g(e)` and `Σ_{e≡7} L(n/e) g(e)` are even. -/
theorem genusData_nonempty_iff_parities (L : ℕ → ℤ) (n : ℕ) (hn : n % 8 = 5) (hsq : Squarefree n)
    (hL1 : L 1 = 1) (hL : L n = 0) :
    Nonempty (GenusData L n) ↔
      ((((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) :
        ZMod 2) = 0) ∧
      (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) :
        ZMod 2) = 0)) := by
  constructor
  · rintro ⟨G⟩
    obtain ⟨X, hX⟩ := lemmaN2 G hn hsq hL1
    exact finalStep G hn hL hX
  · rintro ⟨h5, h7⟩
    exact ⟨witnessData₀ L n hn hsq hL1 h5 h7⟩

/-- **Consistency of `GenusData` when `L n = 0`**: for squarefree `n ≡ 5 (mod 8)` with `L 1 = 1`,
`L n = 0` and the two parities of `finalStep`'s conclusion, `GenusData L n` is inhabited. -/
theorem genusData_nonempty_of_parities (L : ℕ → ℤ) (n : ℕ) (hn : n % 8 = 5) (hsq : Squarefree n)
    (hL1 : L 1 = 1) (hL : L n = 0)
    (h5 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0))
    (h7 : (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) :
      ZMod 2) = 0)) :
    Nonempty (GenusData L n) :=
  (genusData_nonempty_iff_parities L n hn hsq hL1 hL).mpr ⟨h5, h7⟩

end Witness
end ZInQ.PropN
