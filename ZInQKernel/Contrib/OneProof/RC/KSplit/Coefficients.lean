import Mathlib

/-!
# Lane RC3: the coefficient calculation behind the mod-eight contradiction (App G)

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:app-nonempty-seeds`, proof, tex 10319–10481.
Under the assumed absence of a nonempty `K`-split unit seed, Elliot's computation at a fresh good
`K`-split prime `p` shows `H_{p}[p³] ∈ 2𝒪_coef` and then `a_p ≡ p + 1 (mod 8)`.

Half-integral-weight forms, Hecke operators and the Galois traces `t(φ)`, `d(φ)` do not exist in
Mathlib. The forms enter here through their `q`-expansions (functions `ℕ → L` into the coefficient
field `L`, a field of characteristic zero, with the coefficient ring `𝒪 = 𝒪_coef` a subring), and
every property of the operators that the computation uses is a hypothesis, named after the
manuscript with its tex lines and kind:

* `ShellRecurrence` — the good `T(p²)` formula `(E.12)` (tex 8156–8161), `PRINT` (Shimura's
  formula for `T(p²)` on half-integral weight; the manuscript cites it as "the standard good
  `T(p²)` formula"), here as an interface on the coefficient sequence;
* the normalization `a(1) = 1` (tex 10291–10292, 10460) and the positive-twist character convention
  `ψ/η = χ_{−1}`, i.e. `ψ(p) = η(p)(−1/p)` (tex 10361, 10457), `ELLIOT`;
* integrality of `H` (`(O.11)`, tex 10342, 9626–9632), `ELLIOT`;
* `(G.4a)`, `(G.4b)` and `v₂ a(pp') ≥ 3` (tex 10345–10352, 10388–10406, 10448–10450), the
  no-seed inputs, `ELLIOT`;
* the trace identity `(t(φ)f)[p²] = f[p³] + (d(φ)f)[p]` (tex 10327–10330), the scalar action of
  `d(φ)` on the blocks `θB, θΘ₁, θΘ_{p}` with `δ_B = δ_p` (tex 10355–10379), and the good Hecke
  formula at the fresh prime `p'` (tex 10437–10441), `ELLIOT`.

From these, everything Elliot computes is `PROVED` here:
* `shell_p_sq`, `shell_p_four`: `a(p²) = η(p)(a_p − 1)`, `a(p⁴) = η(p)²{a_p(a_p − 1) − p}`
  (tex 10458–10463);
* `Bp_p`, `Bp_p_cube`: `B[p] = η(p)(a_p − 2)/2`, `B[p³] = η(p)²((a_p − 1)² − p)/2`
  (tex 10464–10468);
* `unaryTheta_*`: only `Θ_{p}` contributes at `p³`, with coefficient `η(p)p` (tex 10469–10470), and
  `Θ₁[p] = 0`, `Θ_{p}[p] = 1` (tex 10380, 10421–10422);
* `Hp_p_cube`: **`H_{p}[p³] = η(p)²(a_p − 1)(a_p − p − 1)/4`** (tex 10471–10474);
* `Hp_p`, `Hp_p_sq_mul`: `H[p] = 0` (tex 10380) and
  `H[p²p'] = (a(p³p') − η(p)a(pp'))/4 = η(p)(a_p − 1)a(pp')/4` (tex 10442–10446);
* `thetaMul_sub_self_inTwoO`: `(G.4d)` (tex 10430–10436);
* `dphi_expansion`, `dphi_p_inTwoO_of_G4ab`, `dphi_eq_det_identity`, `dphi_p_inTwoO_of_det`:
  the exact expansion `(G.4c)` and both of Elliot's arguments for `(d(φ)f)[p] ∈ 2𝒪`
  (tex 10374–10428);
* `Hp_p_cube_inTwoO`: `H[p³] ∈ 2𝒪` (tex 10451–10452);
* `cong_eight_of_inTwoO`, `cong_eight_of_mem_ideal`: since the phase is a unit and `a_p − 1` is odd,
  `a_p ≡ p + 1 (mod 8)` (tex 10477–10480), from `H[p³] ∈ 2𝒪` or from `H[p³]` zero in the residue
  field (`H[p³] ∈ 𝔪`);
* `NoSeedTraceData` and `NoSeedTraceData.cong_eight`: the whole chain at one prime.
-/

namespace ZInQ.Manuscript.RC.KSplit

open Finset

variable {L : Type*} [Field L]

/-! ### Membership in `2𝒪` -/

/-- `z ∈ 2𝒪`: `z = 2x` with `x` in the coefficient ring `𝒪` ("congruences modulo the ideal
`2𝒪_coef` before passage to the residue field", tex 10332–10333). -/
def InTwoO (O : Subring L) (z : L) : Prop := ∃ x ∈ O, z = 2 * x

namespace InTwoO

variable {O : Subring L}

theorem zero : InTwoO O 0 := ⟨0, O.zero_mem, by ring⟩

theorem two_mul {x : L} (hx : x ∈ O) : InTwoO O (2 * x) := ⟨x, hx, rfl⟩

theorem add {y z : L} (hy : InTwoO O y) (hz : InTwoO O z) : InTwoO O (y + z) := by
  obtain ⟨a, ha, rfl⟩ := hy
  obtain ⟨b, hb, rfl⟩ := hz
  exact ⟨a + b, O.add_mem ha hb, by ring⟩

theorem neg {z : L} (hz : InTwoO O z) : InTwoO O (-z) := by
  obtain ⟨a, ha, rfl⟩ := hz
  exact ⟨-a, O.neg_mem ha, by ring⟩

theorem sub {y z : L} (hy : InTwoO O y) (hz : InTwoO O z) : InTwoO O (y - z) := by
  rw [sub_eq_add_neg]; exact hy.add hz.neg

theorem mul_left {c z : L} (hc : c ∈ O) (hz : InTwoO O z) : InTwoO O (c * z) := by
  obtain ⟨a, ha, rfl⟩ := hz
  exact ⟨c * a, O.mul_mem hc ha, by ring⟩

theorem mul_right {c z : L} (hc : c ∈ O) (hz : InTwoO O z) : InTwoO O (z * c) := by
  rw [mul_comm]; exact hz.mul_left hc

theorem sum {ι : Type*} (s : Finset ι) {f : ι → L} (hf : ∀ i ∈ s, InTwoO O (f i)) :
    InTwoO O (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem mem {z : L} (hz : InTwoO O z) : z ∈ O := by
  obtain ⟨a, ha, rfl⟩ := hz
  exact O.mul_mem (by simp) ha

end InTwoO

/-! ### The `q`-expansions -/

/-- **Multiplication by the ordinary theta series** `θ = Σ_{j ∈ ℤ} q^{j²} = 1 + 2Σ_{j>0} q^{j²}`
on `q`-expansions (tex 10408, 10433): `(θX)[N] = X[N] + 2 Σ_{0 < j² ≤ N} X[N − j²]`. -/
def thetaMul (X : ℕ → L) (N : ℕ) : L :=
  X N + 2 * ∑ j ∈ Icc 1 (Nat.sqrt N), X (N - j ^ 2)

/-- **The unary series** `Θ_J = Σ_{m > 0, (m, S) = 1} η(m) m q^{J m²}` with `i = 0`
(tex 9618–9621; "`η` is odd, so the unary correction uses `i = 0`", tex 10458–10459). Here `S` is
the product of the support primes and `η` gives the character values. -/
def unaryTheta (η : ℕ → L) (S J n : ℕ) : L :=
  ∑ m ∈ (range (n + 1)).filter (fun m => 0 < m ∧ Nat.Coprime m S ∧ J * m ^ 2 = n), η m * m

/-- **`B_{p} = (U_p − η(p)V_p)g/2`** with inherited depth zero (tex 10338, 10464):
`B[n] = (a(pn) − η(p)a(n/p))/2`, the second term present only for `p ∣ n`. -/
def Bp (a : ℕ → L) (ηp : L) (p n : ℕ) : L :=
  (a (p * n) - ηp * (if p ∣ n then a (n / p) else 0)) / 2

/-- **`H_{p} = (B − b₁Θ₁ − b_pΘ_{p})/2`** with `b₁ = B[1]`, `b_p = B[p]` (tex 10340, `(O.11)`). -/
def Hp (a η : ℕ → L) (S p n : ℕ) : L :=
  (Bp a (η p) p n - Bp a (η p) p 1 * unaryTheta η S 1 n -
    Bp a (η p) p p * unaryTheta η S p n) / 2

/-- **The good `T(p²)` formula `(E.12)` at the prime `p`** (tex 8156–8161; `PRINT` interface:
Shimura's `T(p²)` formula for half-integral weight, as the manuscript uses it):
`a(p²n) = {η(p)a_p − ψ(p)(−n/p)}a(n) − pη(p)²a(n/p²)` for every `n`, with `a(n/p²) = 0` unless
`p² ∣ n`. -/
def ShellRecurrence (a : ℕ → L) (ηp ψp : L) (ap : ℤ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ n : ℕ, a (p ^ 2 * n) = (ηp * (ap : L) - ψp * ((legendreSym p (-(n : ℤ)) : ℤ) : L)) * a n -
    (p : L) * ηp ^ 2 * (if p ^ 2 ∣ n then a (n / p ^ 2) else 0)

/-! ### Unary series values -/

section Unary

variable (η : ℕ → L) (S : ℕ)

theorem unaryTheta_eq_zero {J n : ℕ} (h : ∀ m, 0 < m → J * m ^ 2 ≠ n) :
    unaryTheta η S J n = 0 := by
  unfold unaryTheta
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Finset.mem_filter] at hm
  exact absurd hm.2.2.2 (h m hm.2.1)

theorem unaryTheta_eq_single {J n m₀ : ℕ} (hJ : 0 < J) (hm₀ : 0 < m₀) (hcop : Nat.Coprime m₀ S)
    (heq : J * m₀ ^ 2 = n) (huniq : ∀ m, 0 < m → J * m ^ 2 = n → m = m₀) :
    unaryTheta η S J n = η m₀ * m₀ := by
  unfold unaryTheta
  have hmem : m₀ ∈ (range (n + 1)).filter (fun m => 0 < m ∧ Nat.Coprime m S ∧ J * m ^ 2 = n) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hm₀, hcop, heq⟩
    have : m₀ ≤ J * m₀ ^ 2 := by
      calc m₀ ≤ m₀ ^ 2 := by nlinarith
        _ ≤ J * m₀ ^ 2 := Nat.le_mul_of_pos_left _ hJ
    omega
  rw [Finset.sum_eq_single_of_mem m₀ hmem]
  intro m hm hne
  rw [Finset.mem_filter] at hm
  exact absurd (huniq m hm.2.1 hm.2.2.2) hne

variable {p : ℕ} (hp : p.Prime)
include hp

/-- `Θ₁[p] = 0`: `p` is not a square (tex 10380, 10421). -/
theorem unaryTheta_one_p : unaryTheta η S 1 p = 0 := by
  refine unaryTheta_eq_zero η S fun m _ hm => ?_
  rw [one_mul] at hm
  exact (Nat.prime_iff.mp hp).not_isSquare ⟨m, by rw [← hm, sq]⟩

/-- `Θ_{p}[p] = η(1) · 1` (tex 10380). -/
theorem unaryTheta_p_p : unaryTheta η S p p = η 1 * 1 := by
  have h := unaryTheta_eq_single η S (J := p) (n := p) (m₀ := 1) hp.pos one_pos
    (Nat.coprime_one_left S) (by ring) (fun m hm h => by
      have : m ^ 2 = 1 := by
        have := hp.pos
        nlinarith
      simpa using this)
  rw [h, Nat.cast_one]

/-- `Θ₁[p³] = 0`: `p³` is not a square (tex 10469). -/
theorem unaryTheta_one_p_cube : unaryTheta η S 1 (p ^ 3) = 0 := by
  refine unaryTheta_eq_zero η S fun m _ hm => ?_
  rw [one_mul] at hm
  -- `p ∣ m`, write `m = p t`, then `t² = p`, impossible
  have hpm : p ∣ m := hp.dvd_of_dvd_pow (n := 2) ⟨p ^ 2, by rw [hm]; ring⟩
  obtain ⟨t, rfl⟩ := hpm
  have : t ^ 2 = p := by
    have h' : p ^ 2 * t ^ 2 = p ^ 2 * p := by rw [← mul_pow, hm]; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h'
  exact (Nat.prime_iff.mp hp).not_isSquare ⟨t, by rw [← this, sq]⟩

/-- **Only `Θ_{p}` contributes at `p³`, with coefficient `η(p)p`** (tex 10469–10470), for `p`
outside the support. -/
theorem unaryTheta_p_p_cube (hpS : Nat.Coprime p S) : unaryTheta η S p (p ^ 3) = η p * p := by
  refine unaryTheta_eq_single η S hp.pos hp.pos hpS (by ring) fun m _ hm => ?_
  have : m ^ 2 = p ^ 2 := by
    have h' : p * m ^ 2 = p * p ^ 2 := by rw [hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos h'
  exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) this

omit hp in
/-- `Θ_{p}[p − j²] = 0` for `0 < j² < p`: the index is positive and smaller than `p`
(tex 10388–10389). -/
theorem unaryTheta_p_sub {j : ℕ} (hj : 0 < j) (hjp : j ^ 2 ≤ p) :
    unaryTheta η S p (p - j ^ 2) = 0 := by
  refine unaryTheta_eq_zero η S fun m hm h => ?_
  have h1 : p ≤ p * m ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have h2 : 0 < j ^ 2 := by positivity
  omega

/-- Neither unary series has support at `p²p'` (tex 10442). -/
theorem unaryTheta_p_sq_mul {p' : ℕ} (hp' : p'.Prime) (hne : p' ≠ p) :
    unaryTheta η S 1 (p ^ 2 * p') = 0 ∧ unaryTheta η S p (p ^ 2 * p') = 0 := by
  constructor
  · refine unaryTheta_eq_zero η S fun m _ hm => ?_
    rw [one_mul] at hm
    -- `p' ∣ m`, so `p'² ∣ p²p'`, so `p' ∣ p²`
    have hpm : p' ∣ m := hp'.dvd_of_dvd_pow (n := 2) ⟨p ^ 2, by rw [hm]; ring⟩
    obtain ⟨t, rfl⟩ := hpm
    have h' : p' * (p' * t ^ 2) = p' * p ^ 2 := by rw [← mul_assoc, ← sq, ← mul_pow, hm]; ring
    have h'' : p' * t ^ 2 = p ^ 2 := Nat.eq_of_mul_eq_mul_left hp'.pos h'
    have : p' ∣ p := hp'.dvd_of_dvd_pow (n := 2) ⟨t ^ 2, h''.symm⟩
    exact hne ((Nat.prime_dvd_prime_iff_eq hp' hp).mp this)
  · refine unaryTheta_eq_zero η S fun m _ hm => ?_
    have h' : m ^ 2 = p * p' := by
      have : p * m ^ 2 = p * (p * p') := by rw [hm]; ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    have hpm : p ∣ m := hp.dvd_of_dvd_pow (n := 2) ⟨p', by rw [h']⟩
    obtain ⟨t, rfl⟩ := hpm
    have h'' : p * t ^ 2 = p' := by
      have : p * (p * t ^ 2) = p * p' := by rw [← h']; ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    have : p ∣ p' := ⟨t ^ 2, h''.symm⟩
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hp').mp this).symm

end Unary

/-! ### The recurrence values and the coefficients of `B`, `H` -/

section Coefficients

variable {a : ℕ → L} {ηp ψp : L} {ap : ℤ} {p : ℕ} [hp : Fact p.Prime]

/-- `(−1/p)² = 1` and `(−p²/p) = 0`. -/
theorem legendreSym_neg_one_sq : legendreSym p (-1) ^ 2 = 1 := by
  refine legendreSym.sq_one p ?_
  intro h
  have : ((1 : ℤ) : ZMod p) = 0 := by rw [← neg_eq_zero]; exact_mod_cast h
  simp at this

/-- **`a(p²) = η(p)(a_p − 1)`** (`PROVED` from `(E.12)` at `n = 1`; tex 10458–10462: with `a(1) = 1`
and `κ = (ψ/η)(p)(−1/p) = 1`). -/
theorem shell_p_sq (hrec : ShellRecurrence a ηp ψp ap p) (ha1 : a 1 = 1)
    (hψ : ψp = ηp * ((legendreSym p (-1) : ℤ) : L)) :
    a (p ^ 2) = ηp * ((ap : L) - 1) := by
  have h := hrec 1
  have hnd : ¬ p ^ 2 ∣ 1 := fun h' =>
    (Nat.one_lt_pow (by norm_num) hp.out.one_lt).ne' (Nat.dvd_one.mp h')
  rw [mul_one, ite_eq_right hnd, ha1, Nat.cast_one, hψ] at h
  have hsq : ((legendreSym p (-1) : ℤ) : L) * ((legendreSym p (-1) : ℤ) : L) = 1 := by
    rw [← Int.cast_mul, ← sq, legendreSym_neg_one_sq, Int.cast_one]
  rw [h]
  linear_combination (-ηp) * hsq

/-- **`a(p⁴) = η(p)²{a_p(a_p − 1) − p}`** (`PROVED` from `(E.12)` at `n = p²`; tex 10462). -/
theorem shell_p_four (hrec : ShellRecurrence a ηp ψp ap p) (ha1 : a 1 = 1)
    (hψ : ψp = ηp * ((legendreSym p (-1) : ℤ) : L)) :
    a (p ^ 4) = ηp ^ 2 * ((ap : L) * ((ap : L) - 1) - p) := by
  have h := hrec (p ^ 2)
  have hleg : legendreSym p (-((p ^ 2 : ℕ) : ℤ)) = 0 := by
    rw [legendreSym.eq_zero_iff]; push_cast; simp
  rw [hleg, ite_eq_left dvd_rfl, Nat.div_self (pow_pos hp.out.pos 2), ha1,
    shell_p_sq hrec ha1 hψ, show p ^ 2 * p ^ 2 = p ^ 4 by ring] at h
  rw [h]; push_cast; ring

omit hp in
/-- `b₁ = B[1] = a(p)/2` (tex 10339). -/
theorem Bp_one (hp1 : p ≠ 1) : Bp a ηp p 1 = a p / 2 := by
  unfold Bp
  rw [ite_eq_right (fun h => hp1 (Nat.dvd_one.mp h)), mul_one]; ring

/-- **`B_{p}[p] = η(p)(a_p − 2)/2`** (`PROVED`; tex 10466). -/
theorem Bp_p (hrec : ShellRecurrence a ηp ψp ap p) (ha1 : a 1 = 1)
    (hψ : ψp = ηp * ((legendreSym p (-1) : ℤ) : L)) :
    Bp a ηp p p = ηp * ((ap : L) - 2) / 2 := by
  unfold Bp
  rw [ite_eq_left dvd_rfl, Nat.div_self hp.out.pos, ha1, ← sq, shell_p_sq hrec ha1 hψ]
  ring

/-- **`B_{p}[p³] = η(p)²((a_p − 1)² − p)/2`** (`PROVED`; tex 10467). -/
theorem Bp_p_cube (hrec : ShellRecurrence a ηp ψp ap p) (ha1 : a 1 = 1)
    (hψ : ψp = ηp * ((legendreSym p (-1) : ℤ) : L)) :
    Bp a ηp p (p ^ 3) = ηp ^ 2 * (((ap : L) - 1) ^ 2 - p) / 2 := by
  unfold Bp
  rw [ite_eq_left (dvd_pow_self p (by norm_num)),
    show p ^ 3 / p = p ^ 2 by rw [pow_succ, Nat.mul_div_cancel _ hp.out.pos],
    show p * p ^ 3 = p ^ 4 by ring, shell_p_four hrec ha1 hψ, shell_p_sq hrec ha1 hψ]
  ring

end Coefficients

section H

variable {a η : ℕ → L} {ψp : L} {ap : ℤ} {S p : ℕ} [hp : Fact p.Prime]

/-- **The coefficient behind the mod-eight contradiction** (`PROVED`; tex 10469–10474):
`H_{p}[p³] = η(p)²(a_p − 1)(a_p − p − 1)/4`. -/
theorem Hp_p_cube [CharZero L] (hrec : ShellRecurrence a (η p) ψp ap p) (ha1 : a 1 = 1)
    (hψ : ψp = η p * ((legendreSym p (-1) : ℤ) : L)) (hpS : Nat.Coprime p S) :
    Hp a η S p (p ^ 3) = η p ^ 2 * ((ap : L) - 1) * ((ap : L) - p - 1) / 4 := by
  unfold Hp
  rw [unaryTheta_one_p_cube η S hp.out, unaryTheta_p_p_cube η S hp.out hpS,
    Bp_p_cube hrec ha1 hψ, Bp_p hrec ha1 hψ]
  ring

/-- **`H[p] = 0`** (`PROVED`; tex 10380: `B[p] = b_p`, `Θ_{p}[p] = 1`, `Θ₁[p] = 0`), given
`η(1) = 1`. -/
theorem Hp_p (hη1 : η 1 = 1) : Hp a η S p p = 0 := by
  unfold Hp
  rw [unaryTheta_one_p η S hp.out, unaryTheta_p_p η S hp.out, hη1]
  ring

/-- **`H[p²p'] = η(p)(a_p − 1)a(pp')/4`** (`PROVED`; tex 10442–10446): neither unary series has
support at `p²p'`, and the recurrence at `p ∣ pp'` has `κ = 0`, so
`H[p²p'] = (a(p³p') − η(p)a(pp'))/4`. -/
theorem Hp_p_sq_mul [CharZero L] (hrec : ShellRecurrence a (η p) ψp ap p) {p' : ℕ}
    (hp' : p'.Prime) (hne : p' ≠ p) :
    Hp a η S p (p ^ 2 * p') = η p * ((ap : L) - 1) * a (p * p') / 4 := by
  have hr := hrec (p * p')
  have hleg : legendreSym p (-((p * p' : ℕ) : ℤ)) = 0 := by
    rw [legendreSym.eq_zero_iff]; push_cast; simp
  have hnd : ¬ p ^ 2 ∣ p * p' := by
    rintro ⟨c, hc⟩
    have : p * p' = p * (p * c) := by rw [hc]; ring
    have h' : p' = p * c := Nat.eq_of_mul_eq_mul_left hp.out.pos this
    exact hne ((Nat.prime_dvd_prime_iff_eq hp.out hp').mp ⟨c, h'⟩).symm
  rw [hleg, ite_eq_right hnd, Int.cast_zero, mul_zero, sub_zero, mul_zero, sub_zero] at hr
  obtain ⟨h1, h2⟩ := unaryTheta_p_sq_mul η S hp.out hp' hne
  unfold Hp Bp
  rw [h1, h2, ite_eq_left (Dvd.intro (p * p') (by ring)),
    show p ^ 2 * p' / p = p * p' by
      rw [show p ^ 2 * p' = p * (p * p') by ring, Nat.mul_div_cancel_left _ hp.out.pos],
    show p * (p ^ 2 * p') = p ^ 2 * (p * p') by ring, hr]
  ring

end H

/-! ### `(G.4d)` and `(G.4c)` -/

section Trace

variable {O : Subring L}

/-- **`(G.4d)`** (`PROVED`; tex 10430–10436): if `H` is integral then
`f[N] = (θH)[N] ≡ H[N] (mod 2𝒪)` for every `N`. -/
theorem thetaMul_sub_self_inTwoO {X : ℕ → L} (hX : ∀ n, X n ∈ O) (N : ℕ) :
    InTwoO O (thetaMul X N - X N) :=
  ⟨∑ j ∈ Icc 1 (Nat.sqrt N), X (N - j ^ 2), O.sum_mem fun j _ => hX _, by
    unfold thetaMul; ring⟩

/-- Multiplication by `θ` is linear. -/
theorem thetaMul_linear (X Y Z : ℕ → L) (c₁ c₂ : L) (N : ℕ) :
    thetaMul (fun n => (X n - c₁ * Y n - c₂ * Z n) / 2) N =
      (thetaMul X N - c₁ * thetaMul Y N - c₂ * thetaMul Z N) / 2 := by
  unfold thetaMul
  have hs : ∑ j ∈ Icc 1 (Nat.sqrt N),
        (X (N - j ^ 2) - c₁ * Y (N - j ^ 2) - c₂ * Z (N - j ^ 2)) / 2 =
      ((∑ j ∈ Icc 1 (Nat.sqrt N), X (N - j ^ 2)) -
        c₁ * (∑ j ∈ Icc 1 (Nat.sqrt N), Y (N - j ^ 2)) -
        c₂ * (∑ j ∈ Icc 1 (Nat.sqrt N), Z (N - j ^ 2))) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.mul_sum]
  beta_reduce
  rw [hs]; ring

/-- The values of a unary series lie in `𝒪` when the character values do. -/
theorem unaryTheta_mem {η : ℕ → L} (hηO : ∀ m, η m ∈ O) (S J n : ℕ) :
    unaryTheta η S J n ∈ O :=
  O.sum_mem fun m _ => O.mul_mem (hηO m) (natCast_mem O m)

/-- **The scalar action of `d(φ)` on the three weight-two blocks** (interface, `ELLIOT`;
tex 10355–10357 and 10408–10411): `d(φ)` acts on `θB, θΘ₁, θΘ_{p}` by `δ_B, δ₁, δ_p`, and by
linearity `d(φ)f = (δ_B θB − δ₁ b₁ θΘ₁ − δ_p b_p θΘ_{p})/2` for `f = θH`. -/
def DphiBlocks (df a η : ℕ → L) (S p : ℕ) (δB δ1 δp : L) : Prop :=
  ∀ n, df n = (δB * thetaMul (Bp a (η p) p) n -
    δ1 * Bp a (η p) p 1 * thetaMul (unaryTheta η S 1) n -
    δp * Bp a (η p) p p * thetaMul (unaryTheta η S p) n) / 2

variable {a η df : ℕ → L} {S p : ℕ} {δB δ1 δp : L}

/-- **The exact expansion `(G.4c)`** (`PROVED`; tex 10408–10422): there is no `Θ₁[p]` term since
`p` is not a square, and `Θ_{p}[p] = 1`. -/
theorem dphi_expansion [CharZero L] (hp : p.Prime) (hη1 : η 1 = 1)
    (hdf : DphiBlocks df a η S p δB δ1 δp) :
    df p = (δB * Bp a (η p) p p - δp * Bp a (η p) p p) / 2 +
      ∑ j ∈ Icc 1 (Nat.sqrt p), (δB * Bp a (η p) p (p - j ^ 2) -
        δ1 * Bp a (η p) p 1 * unaryTheta η S 1 (p - j ^ 2) -
        δp * Bp a (η p) p p * unaryTheta η S p (p - j ^ 2)) := by
  rw [hdf p]
  unfold thetaMul
  rw [unaryTheta_one_p η S hp, unaryTheta_p_p η S hp, hη1, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **`(d(φ)f)[p] ∈ 2𝒪` by the direct expansion** (`PROVED`; tex 10423–10428): the first line of
`(G.4c)` vanishes since `B[p] = b_p` and `δ_B = δ_p`; every summand of the second line is even by
`(G.4a)`, `(G.4b)` and the vanishing of `Θ_{p}[p − j²]`. -/
theorem dphi_p_inTwoO_of_G4ab [CharZero L] (hp : p.Prime) (hη1 : η 1 = 1) (hηO : ∀ m, η m ∈ O)
    (hdf : DphiBlocks df a η S p δB δ1 δp) (hδB : δB ∈ O) (hδ1 : δ1 ∈ O) (hBp : δB = δp)
    (hG4a : InTwoO O (Bp a (η p) p 1))
    (hG4b : ∀ j ∈ Icc 1 (Nat.sqrt p), InTwoO O (Bp a (η p) p (p - j ^ 2))) :
    InTwoO O (df p) := by
  rw [dphi_expansion hp hη1 hdf, hBp, sub_self, zero_div, zero_add]
  refine InTwoO.sum _ fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  have hjp : j ^ 2 ≤ p := by
    have := Nat.le_sqrt.mp hj.2
    rwa [sq]
  rw [unaryTheta_p_sub η S (by omega) hjp, mul_zero, sub_zero]
  refine InTwoO.sub ((hG4b j (Finset.mem_Icc.mpr hj)).mul_left (hBp ▸ hδB)) ?_
  rw [mul_assoc]
  exact (hG4a.mul_right (unaryTheta_mem hηO S 1 _)).mul_left hδ1

/-- **The determinant identity** (`PROVED`; tex 10374–10379): with `δ_B = δ_p`,
`d(φ)f = δ_p f + ((δ_p − δ₁)b₁/2) θΘ₁` exactly, for `f = θH`. -/
theorem dphi_eq_det_identity [CharZero L] (hdf : DphiBlocks df a η S p δB δ1 δp) (hBp : δB = δp)
    (n : ℕ) :
    df n = δp * thetaMul (Hp a η S p) n +
      (δp - δ1) * Bp a (η p) p 1 / 2 * thetaMul (unaryTheta η S 1) n := by
  have hH : Hp a η S p = fun n => (Bp a (η p) p n - Bp a (η p) p 1 * unaryTheta η S 1 n -
      Bp a (η p) p p * unaryTheta η S p n) / 2 := rfl
  rw [hdf n, hH, thetaMul_linear, hBp]
  ring

/-- **`(d(φ)f)[p] ∈ 2𝒪` from the determinant identity** (`PROVED`; tex 10380–10386): `f[p]` is
even since `H[p] = 0` and `H` is integral, `θΘ₁[p]` is even, `δ_p − δ₁ ∈ 2𝒪`, and only the
ordinary integrality of `b₁` is used. -/
theorem dphi_p_inTwoO_of_det [CharZero L] (hp : p.Prime) (hη1 : η 1 = 1) (hηO : ∀ m, η m ∈ O)
    (hdf : DphiBlocks df a η S p δB δ1 δp) (hBp : δB = δp) (hδp : δp ∈ O)
    (hδdiff : InTwoO O (δp - δ1)) (hb1 : Bp a (η p) p 1 ∈ O) (hH : ∀ n, Hp a η S p n ∈ O) :
    InTwoO O (df p) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [dphi_eq_det_identity hdf hBp p]
  refine InTwoO.add ?_ ?_
  · -- `f[p] = (f[p] − H[p]) + H[p]` with `H[p] = 0`
    have hf : thetaMul (Hp a η S p) p = (thetaMul (Hp a η S p) p - Hp a η S p p) := by
      rw [Hp_p hη1, sub_zero]
    rw [hf]
    exact (thetaMul_sub_self_inTwoO hH p).mul_left hδp
  · obtain ⟨u, hu, hdiff⟩ := hδdiff
    have hθ : thetaMul (unaryTheta η S 1) p = (thetaMul (unaryTheta η S 1) p -
        unaryTheta η S 1 p) := by rw [unaryTheta_one_p η S hp, sub_zero]
    rw [hdiff, hθ, show 2 * u * Bp a (η p) p 1 / 2 = u * Bp a (η p) p 1 by ring]
    exact (thetaMul_sub_self_inTwoO (unaryTheta_mem hηO S 1) p).mul_left (O.mul_mem hu hb1)

/-- **`H[p³] ∈ 2𝒪`** (`PROVED`; tex 10437–10452): the trace identity at `p²`, `(G.4c)`, `(G.4d)`,
the good Hecke formula at the fresh prime `p'`, and `H[p²p'] = η(p)(a_p − 1)a(pp')/4` with
`v₂ a(pp') ≥ 3`. -/
theorem Hp_p_cube_inTwoO [CharZero L] [Fact p.Prime] {ψp : L} {ap : ℤ}
    (hrec : ShellRecurrence a (η p) ψp ap p)
    {p' : ℕ} (hp' : p'.Prime) (hne : p' ≠ p) (hH : ∀ n, Hp a η S p n ∈ O) (hηp : η p ∈ O)
    {tf : ℕ → L} (htrace : tf (p ^ 2) = thetaMul (Hp a η S p) (p ^ 3) + df p)
    (hHecke : InTwoO O (tf (p ^ 2) - thetaMul (Hp a η S p) (p ^ 2 * p')))
    (hdfp : InTwoO O (df p)) (hpp' : ∃ y ∈ O, a (p * p') = 8 * y) :
    InTwoO O (Hp a η S p (p ^ 3)) := by
  obtain ⟨y, hy, hay⟩ := hpp'
  have hH2 : InTwoO O (Hp a η S p (p ^ 2 * p')) := by
    rw [Hp_p_sq_mul hrec hp' hne, hay]
    refine ⟨η p * ((ap : L) - 1) * y, O.mul_mem (O.mul_mem hηp
      (O.sub_mem (intCast_mem O ap) O.one_mem)) hy, by ring⟩
  have e : Hp a η S p (p ^ 3) =
      -(thetaMul (Hp a η S p) (p ^ 3) - Hp a η S p (p ^ 3)) +
        (tf (p ^ 2) - thetaMul (Hp a η S p) (p ^ 2 * p')) +
        (thetaMul (Hp a η S p) (p ^ 2 * p') - Hp a η S p (p ^ 2 * p')) +
        Hp a η S p (p ^ 2 * p') - df p := by
    rw [htrace]; ring
  rw [e]
  exact ((((thetaMul_sub_self_inTwoO hH _).neg.add hHecke).add
    (thetaMul_sub_self_inTwoO hH _)).add hH2).sub hdfp

end Trace

/-! ### The mod-eight deduction -/

section ModEight

variable {O : Subring L}

/-- `a_p − 1` is odd when `p` is odd and `4 ∣ a_p − p − 1`. -/
theorem odd_ap_sub_one {ap : ℤ} {p : ℕ} (hp_odd : Odd p) {q : ℤ} (hq : ap - p - 1 = 4 * q) :
    Odd (ap - 1) := by
  obtain ⟨r, hr⟩ := hp_odd
  exact ⟨2 * q + r, by push_cast [hr] at hq ⊢; linarith⟩

/-- **The mod-eight deduction, from `H[p³] ∈ 2𝒪`** (`PROVED`; tex 10477–10480: "Since its phase
is a unit and `a_p − 1` is odd, it follows that `a_p ≡ p + 1 (mod 8)`"). Here `𝒪` does not contain
`1/2` (the coefficient ring has residue characteristic two), the phase `η(p)` is a unit of `𝒪`,
and `4 ∣ a_p − p − 1` (full rational two-torsion, tex 10475–10476) makes the coefficient
`η(p)²(a_p − 1)(a_p − p − 1)/4` an actual integer division. -/
theorem cong_eight_of_inTwoO [CharZero L] (hhalf : (2 : L)⁻¹ ∉ O) {ηp : L} (hηinv : ηp⁻¹ ∈ O)
    (hη0 : ηp ≠ 0) {ap : ℤ} {p : ℕ} (hp_odd : Odd p) (h4 : (4 : ℤ) ∣ ap - p - 1)
    (hH : InTwoO O (ηp ^ 2 * ((ap : L) - 1) * ((ap : L) - p - 1) / 4)) :
    (8 : ℤ) ∣ ap - p - 1 := by
  have h2 : (2 : L) ≠ 0 := two_ne_zero
  obtain ⟨q, hq⟩ := h4
  obtain ⟨x, hx, hxe⟩ := hH
  have hqL : (ap : L) - p - 1 = 4 * q := by exact_mod_cast hq
  have hηη : ηp⁻¹ ^ 2 * ηp ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hη0, one_pow]
  -- the integer `m = (a_p − 1) q` is `2 · (η⁻² x)`
  have hm : (((ap - 1) * q : ℤ) : L) = 2 * (ηp⁻¹ ^ 2 * x) := by
    have h1 : ηp ^ 2 * (((ap - 1) * q : ℤ) : L) = 2 * x := by
      rw [← hxe, hqL]; push_cast; ring
    linear_combination (ηp⁻¹ ^ 2) * h1 - (((ap - 1) * q : ℤ) : L) * hηη
  have heven : Even ((ap - 1) * q) := by
    by_contra hodd
    obtain ⟨t, ht⟩ := Int.not_even_iff_odd.mp hodd
    apply hhalf
    have h1 : (1 : L) = 2 * (ηp⁻¹ ^ 2 * x - t) := by
      have h' := hm; rw [ht] at h'; push_cast at h'; linear_combination h'
    have h3 : ηp⁻¹ ^ 2 * x - t = (2 : L)⁻¹ := by
      rw [← mul_right_inj' h2, ← h1, mul_inv_cancel₀ h2]
    rw [← h3]
    exact O.sub_mem (O.mul_mem (O.pow_mem hηinv 2) hx) (intCast_mem O t)
  rcases Int.even_mul.mp heven with h | ⟨r, hr⟩
  · exact absurd h (Int.not_even_iff_odd.mpr (odd_ap_sub_one hp_odd hq))
  · exact ⟨r, by rw [hq, hr]; ring⟩

/-- **The mod-eight deduction, from `H[p³]` zero in the residue field** (`PROVED`; tex 10478–10480:
"the trace identity makes this coefficient zero in the residue field"): the same conclusion when
`H[p³]` lies in a proper ideal `I` of `𝒪` containing `2` (e.g. the maximal ideal). -/
theorem cong_eight_of_mem_ideal [CharZero L] (I : Ideal O) (h2I : (2 : O) ∈ I)
    (hI1 : (1 : O) ∉ I) {ηp : L} (hηinv : ηp⁻¹ ∈ O) (hη0 : ηp ≠ 0) {ap : ℤ} {p : ℕ}
    (hp_odd : Odd p) (h4 : (4 : ℤ) ∣ ap - p - 1)
    (hH : ∃ x ∈ I, (x : L) = ηp ^ 2 * ((ap : L) - 1) * ((ap : L) - p - 1) / 4) :
    (8 : ℤ) ∣ ap - p - 1 := by
  obtain ⟨q, hq⟩ := h4
  obtain ⟨x, hx, hxe⟩ := hH
  have hqL : (ap : L) - p - 1 = 4 * q := by exact_mod_cast hq
  have hηη : ηp⁻¹ ^ 2 * ηp ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hη0, one_pow]
  set u : O := ⟨ηp⁻¹ ^ 2, O.pow_mem hηinv 2⟩
  have hmI : (((ap - 1) * q : ℤ) : O) ∈ I := by
    have hux : (((ap - 1) * q : ℤ) : O) = u * x := by
      apply Subtype.ext
      show (((ap - 1) * q : ℤ) : L) = ηp⁻¹ ^ 2 * (x : L)
      rw [hxe, hqL]
      push_cast
      linear_combination (-(((ap : L) - 1) * q)) * hηη
    rw [hux]; exact I.mul_mem_left u hx
  have heven : Even ((ap - 1) * q) := by
    by_contra hodd
    obtain ⟨t, ht⟩ := Int.not_even_iff_odd.mp hodd
    apply hI1
    have h1 : (1 : O) = (((ap - 1) * q : ℤ) : O) - 2 * (t : O) := by
      rw [ht]; push_cast; ring
    rw [h1]
    exact I.sub_mem hmI (I.mul_mem_right _ h2I)
  rcases Int.even_mul.mp heven with h | ⟨r, hr⟩
  · exact absurd h (Int.not_even_iff_odd.mpr (odd_ap_sub_one hp_odd hq))
  · exact ⟨r, by rw [hq, hr]; ring⟩

end ModEight

/-! ### The inputs `(G.4a)`, `(G.4b)` and the transported bound, from Elliot's lower bounds -/

section Inputs

variable {O : Subring L} {a : ℕ → L} {ηp : L} {p : ℕ}

/-- `B[n] = a(pn)/2` when `p ∤ n`: the `V_p` term is zero (`PROVED`; tex 10397–10398). -/
theorem Bp_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : Bp a ηp p n = a (p * n) / 2 := by
  unfold Bp; rw [ite_eq_right hn, mul_zero, sub_zero]

/-- **`(G.4a)` from the improved bound** (`PROVED`; tex 10345–10352): "if `p` lies in the
coefficient filter, the improved bound is `v₂ a(p) ≥ 2`; otherwise the actual filter gives
`a(p) = 0`". Either
way `b₁ = a(p)/2 ∈ 2𝒪`. The two alternatives are the `ELLIOT` inputs. -/
theorem G4a_of_improved_bound [CharZero L] (hp1 : p ≠ 1) (h : (∃ y ∈ O, a p = 4 * y) ∨ a p = 0) :
    InTwoO O (Bp a ηp p 1) := by
  rw [Bp_one hp1]
  rcases h with ⟨y, hy, hay⟩ | h0
  · exact ⟨y, hy, by rw [hay]; ring⟩
  · rw [h0, zero_div]; exact InTwoO.zero

/-- **`(G.4b)` from the support sieve, the shell recurrences and the lower bound** (`PROVED`;
tex 10388–10406): for `n = p − j²`, `p ∤ n`, so `B[n] = a(pn)/2`; either the coprimality sieve
makes the coefficient zero, or `n = rm²` and the integral shell recurrences give
`a(pn) = c · a(pr)` with `c ∈ 𝒪`, where `a(pr) ∈ 4𝒪` if `r > 1` (`v₂ a(pr) ≥ ω(pr) ≥ 2`, or zero
off the filter), and `a(pn) = c · a(p)` with `a(p)/2 = b₁ ∈ 2𝒪` (`(G.4a)`) if `r = 1`. The three
alternatives are the `ELLIOT` inputs. -/
theorem G4b_of_shell [CharZero L] {n : ℕ} (hn : ¬ p ∣ n)
    (h : a (p * n) = 0 ∨ (∃ c ∈ O, ∃ y ∈ O, a (p * n) = c * (4 * y)) ∨
      (∃ c ∈ O, a (p * n) = c * a p ∧ InTwoO O (a p / 2))) :
    InTwoO O (Bp a ηp p n) := by
  rw [Bp_of_not_dvd hn]
  rcases h with h0 | ⟨c, hc, y, hy, h⟩ | ⟨c, hc, h, hb⟩
  · rw [h0, zero_div]; exact InTwoO.zero
  · exact ⟨c * y, O.mul_mem hc hy, by rw [h]; ring⟩
  · rw [h, mul_div_assoc]; exact hb.mul_left hc

end Inputs

/-- **The transported lower bound** (`PROVED`; tex 10296–10314): from the Waldspurger comparison
`v₂ a_new(D) = v₂ a_old(d_k D) − v₂ a_old(d_k)` (`ELLIOT`, through `(E.10)`–`(E.11)`), the old
lower bound `v₂ a_old(d) ≥ ω(d) + δ` at `d = d_k D`, the old unit condition
`v₂ a_old(d_k) = ω(d_k) + δ`, and `ω(d_k D) = ω(d_k) + ω(D)` for coprime `d_k, D`, it follows that
`v₂ a_new(D) ≥ ω(D)`. Valuations of nonzero coefficients are integers here; a zero coefficient
satisfies the bound trivially. -/
theorem transport_lower_bound (vnew vold : ℕ → ℤ) (δ : ℤ) {dk D : ℕ} (hcop : Nat.Coprime dk D)
    (hW : vnew D = vold (dk * D) - vold dk)
    (hlow : (ArithmeticFunction.cardDistinctFactors (dk * D) : ℤ) + δ ≤ vold (dk * D))
    (hunit : vold dk = ArithmeticFunction.cardDistinctFactors dk + δ) :
    (ArithmeticFunction.cardDistinctFactors D : ℤ) ≤ vnew D := by
  rw [ArithmeticFunction.cardDistinctFactors_mul hcop] at hlow
  push_cast at hlow
  omega

/-! ### The whole chain at one prime -/

/-- **The no-seed data at a fresh good `K`-split prime `p`** (tex 10319–10481): the transported
even source (coefficients `a`, characters `η`, `ψ(p)`, support `S`), its `ELLIOT`/`PRINT`
properties,
and the Galois-trace data `t(φ)f`, `d(φ)f` with the fresh prime `p'`. Fields:
* `ha1`: normalization at index one (tex 10291–10292);
* `hrec`: `(E.12)` at `p` (tex 8156–8161, `PRINT` interface);
* `hψ`: `ψ/η = χ_{−1}` at `p` (positive twist convention, tex 10361, 10457);
* `hη1`, `hηO`, `hηinv`, `hη0`: the character values are integral, `η(1) = 1`, the phase `η(p)` is a
  unit;
* `hpS`: `p` is outside the support; `hhalf`: `1/2 ∉ 𝒪_coef`;
* `hH`: `H` is integral (`(O.11)`, tex 10342);
* `p'`, `hp'`, `hp'p`: the fresh prime `p' ≠ p` (tex 10437–10439);
* `htrace`: the trace identity at `p²` (tex 10327–10330);
* `hHecke`: the good Hecke formula at `p'` (tex 10439–10441);
* `δB`, `δ1`, `δp`, `hδB`, `hδ1`, `hδBp`, `hdf`: the scalar action of `d(φ)` (tex 10355–10368);
* `hG4a`, `hG4b`, `hpp'`: the no-seed inputs `(G.4a)`, `(G.4b)`, `v₂ a(pp') ≥ 3`
  (tex 10345–10352, 10388–10406, 10448–10450). -/
structure NoSeedTraceData (O : Subring L) (p : ℕ) [Fact p.Prime] (ap : ℤ) where
  a : ℕ → L
  η : ℕ → L
  ψp : L
  S : ℕ
  ha1 : a 1 = 1
  hrec : ShellRecurrence a (η p) ψp ap p
  hψ : ψp = η p * ((legendreSym p (-1) : ℤ) : L)
  hη1 : η 1 = 1
  hηO : ∀ m, η m ∈ O
  hηinv : (η p)⁻¹ ∈ O
  hη0 : η p ≠ 0
  hpS : Nat.Coprime p S
  hhalf : (2 : L)⁻¹ ∉ O
  hH : ∀ n, Hp a η S p n ∈ O
  p' : ℕ
  hp' : p'.Prime
  hp'p : p' ≠ p
  tf : ℕ → L
  df : ℕ → L
  htrace : tf (p ^ 2) = thetaMul (Hp a η S p) (p ^ 3) + df p
  hHecke : InTwoO O (tf (p ^ 2) - thetaMul (Hp a η S p) (p ^ 2 * p'))
  δB : L
  δ1 : L
  δp : L
  hδB : δB ∈ O
  hδ1 : δ1 ∈ O
  hδBp : δB = δp
  hdf : DphiBlocks df a η S p δB δ1 δp
  hG4a : InTwoO O (Bp a (η p) p 1)
  hG4b : ∀ j ∈ Icc 1 (Nat.sqrt p), InTwoO O (Bp a (η p) p (p - j ^ 2))
  hpp' : ∃ y ∈ O, a (p * p') = 8 * y

/-- **Under the no-seed data, `a_p ≡ p + 1 (mod 8)`** (`PROVED` from the fields; tex 10319–10481):
`(G.4c)`, then `H[p³] ∈ 2𝒪`, then `H[p³] = η(p)²(a_p − 1)(a_p − p − 1)/4`, then the mod-eight
deduction. The hypothesis `4 ∣ a_p − p − 1` is the full rational two-torsion congruence
(tex 10475–10476; `four_dvd_card` for the curve). -/
theorem NoSeedTraceData.cong_eight [CharZero L] {O : Subring L} {p : ℕ} [hp : Fact p.Prime] {ap : ℤ}
    (D : NoSeedTraceData O p ap) (hp2 : p ≠ 2) (h4 : (4 : ℤ) ∣ ap - p - 1) :
    (8 : ℤ) ∣ ap - p - 1 := by
  have hdfp := dphi_p_inTwoO_of_G4ab hp.out D.hη1 D.hηO D.hdf D.hδB D.hδ1 D.hδBp D.hG4a D.hG4b
  have h3 := Hp_p_cube_inTwoO D.hrec D.hp' D.hp'p D.hH (D.hηO p) D.htrace D.hHecke hdfp D.hpp'
  rw [Hp_p_cube D.hrec D.ha1 D.hψ D.hpS] at h3
  exact cong_eight_of_inTwoO D.hhalf D.hηinv D.hη0 (hp.out.odd_of_ne_two hp2) h4 h3

end ZInQ.Manuscript.RC.KSplit
