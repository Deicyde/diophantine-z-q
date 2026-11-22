import ZInQKernel.Contrib.CloudR2CM.SerreTate.SerreRigidity

/-!
# Proof of Serre's lemma on the Tate module

Let `T = T_ℓ(M)`. Write `z ∈ ℓ^r T` for `∃ y, z = ℓ^r • y`. The two coordinate facts used are:
`ℓ^r T` is contained in the kernel of the `r`-th coordinate (so `⋂ ℓ^r T = 0`), and `T` has
no `ℓ`-torsion. For `g` with `g ≡ 1 mod ℓ^s`, `D = g - 1`, induction on `j` gives
`g^j ≡ 1 (mod ℓ^s)`, `g^j - 1 - jD ≡ 0 (mod ℓ^{2s})` and
`g^j - 1 - jD - C(j,2) D² ≡ 0 (mod ℓ^{3s})`. If `g^q = 1` with `q` prime, then
`g ≡ 1 (mod ℓ^{s+1})`: for `q ≠ ℓ` by Bézout, for `q = ℓ` by cancelling `ℓ`, using the first
order if `s ≥ 2` and the second order (with `ℓ ∣ C(ℓ,2)`) if `ℓ ≥ 3`; `ℓ^k ≥ 3` makes one of
these hold. Hence `g = 1`. A general finite order reduces to prime order by strong induction.
-/

set_option autoImplicit false

noncomputable section

namespace HDec.CMSerreTate

namespace SerreLemmaTateAux

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type} [AddCommGroup M]

/-- `z ∈ ℓ ^ r T_ℓ(M)`. -/
def InPow (r : ℕ) (z : _root_.PkgI3.Tate.T ℓ M) : Prop :=
  ∃ y : _root_.PkgI3.Tate.T ℓ M, z = ((ℓ : ℤ_[ℓ]) ^ r) • y

theorem inPow_zero (r : ℕ) : InPow r (0 : _root_.PkgI3.Tate.T ℓ M) :=
  ⟨0, (smul_zero _).symm⟩

theorem inPow_add {r : ℕ} {a b : _root_.PkgI3.Tate.T ℓ M} (ha : InPow r a) (hb : InPow r b) :
    InPow r (a + b) := by
  obtain ⟨y₁, rfl⟩ := ha
  obtain ⟨y₂, rfl⟩ := hb
  exact ⟨y₁ + y₂, (smul_add _ _ _).symm⟩

theorem inPow_neg {r : ℕ} {a : _root_.PkgI3.Tate.T ℓ M} (ha : InPow r a) : InPow r (-a) := by
  obtain ⟨y, rfl⟩ := ha
  exact ⟨-y, (smul_neg _ _).symm⟩

theorem inPow_sub {r : ℕ} {a b : _root_.PkgI3.Tate.T ℓ M} (ha : InPow r a) (hb : InPow r b) :
    InPow r (a - b) := by
  rw [sub_eq_add_neg]
  exact inPow_add ha (inPow_neg hb)

theorem inPow_smul {r : ℕ} (c : ℤ_[ℓ]) {a : _root_.PkgI3.Tate.T ℓ M} (ha : InPow r a) :
    InPow r (c • a) := by
  obtain ⟨y, rfl⟩ := ha
  exact ⟨c • y, smul_comm c _ y⟩

theorem inPow_mono {r r' : ℕ} (h : r ≤ r') {a : _root_.PkgI3.Tate.T ℓ M} (ha : InPow r' a) :
    InPow r a := by
  obtain ⟨y, rfl⟩ := ha
  refine ⟨((ℓ : ℤ_[ℓ]) ^ (r' - r)) • y, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_of_le h]

theorem inPow_ell_smul {r : ℕ} {a : _root_.PkgI3.Tate.T ℓ M} (ha : InPow r a) :
    InPow (r + 1) ((ℓ : ℤ_[ℓ]) • a) := by
  obtain ⟨y, rfl⟩ := ha
  exact ⟨y, by rw [smul_smul, ← pow_succ']⟩

/-- `ℓ^r T` lies in the kernel of the `r`-th coordinate. -/
theorem coord_eq_zero {r : ℕ} {z : _root_.PkgI3.Tate.T ℓ M} (h : InPow r z) : z.1 r = 0 := by
  obtain ⟨y, rfl⟩ := h
  rw [_root_.PkgI3.Tate.smul_apply]
  have h0 : PadicInt.toZModPow r ((ℓ : ℤ_[ℓ]) ^ r) = 0 := by
    rw [map_pow, map_natCast]; exact_mod_cast ZMod.natCast_self (ℓ ^ r)
  rw [h0, ZMod.val_zero, zero_smul]

/-- Separation: `⋂ ℓ^r T = 0`. -/
theorem eq_zero_of_forall {z : _root_.PkgI3.Tate.T ℓ M} (h : ∀ r, InPow r z) : z = 0 :=
  Subtype.ext (funext fun n ↦ coord_eq_zero (h n))

/-- `T` has no `ℓ`-torsion. -/
theorem eq_zero_of_ell_smul {w : _root_.PkgI3.Tate.T ℓ M} (h : (ℓ : ℤ_[ℓ]) • w = 0) : w = 0 := by
  have hn : ∀ n, w.1 n = 0 := by
    intro n
    have h1 : _root_.PkgI3.Tate.smulSeq (ℓ : ℤ_[ℓ]) w.1 (n + 1) = ℓ • w.1 (n + 1) :=
      _root_.PkgI3.Tate.smulSeq_congr w.2 (n + 1) (by rw [map_natCast])
    have h2 : _root_.PkgI3.Tate.smulSeq (ℓ : ℤ_[ℓ]) w.1 (n + 1) = 0 :=
      congrArg (fun v : _root_.PkgI3.Tate.T ℓ M ↦ v.1 (n + 1)) h
    rw [← w.2.2 n, ← h1, h2]
  exact Subtype.ext (funext hn)

/-- Cancelling `ℓ`. -/
theorem inPow_of_ell_smul {r : ℕ} {u : _root_.PkgI3.Tate.T ℓ M}
    (h : InPow (r + 1) ((ℓ : ℤ_[ℓ]) • u)) : InPow r u := by
  obtain ⟨y, hy⟩ := h
  refine ⟨y, sub_eq_zero.mp (eq_zero_of_ell_smul ?_)⟩
  rw [smul_sub, hy, smul_smul, ← pow_succ', sub_self]

/-- A linear map with values in `ℓ^a T` maps `ℓ^r T` into `ℓ^(r+a) T`. -/
theorem inPow_map {a r : ℕ}
    (P : _root_.PkgI3.Tate.T ℓ M →ₗ[ℤ_[ℓ]] _root_.PkgI3.Tate.T ℓ M)
    (hP : ∀ y, InPow a (P y)) {z : _root_.PkgI3.Tate.T ℓ M} (hz : InPow r z) :
    InPow (r + a) (P z) := by
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨u, hu⟩ := hP w
  exact ⟨u, by rw [map_smul, hu, smul_smul, ← pow_add]⟩

variable {g : _root_.PkgI3.Tate.T ℓ M →ₗ[ℤ_[ℓ]] _root_.PkgI3.Tate.T ℓ M} {s : ℕ}

/-- `g ≡ 1` implies `g ^ j ≡ 1`. -/
theorem order0 (hg : ∀ y, InPow s (g y - y)) (j : ℕ) : ∀ y, InPow s ((g ^ j) y - y) := by
  induction j with
  | zero =>
    intro y
    rw [pow_zero, Module.End.one_apply, sub_self]
    exact inPow_zero s
  | succ j ih =>
    intro y
    have e : (g ^ (j + 1)) y - y = ((g ^ j) (g y) - g y) + (g y - y) := by
      rw [pow_succ, Module.End.mul_apply]; abel
    rw [e]
    exact inPow_add (ih (g y)) (hg y)

/-- First order: `g ^ j - 1 - j (g - 1) ≡ 0 mod ℓ^(2s)`. -/
theorem order1 (hg : ∀ y, InPow s (g y - y)) (j : ℕ) :
    ∀ x, InPow (s + s) ((g ^ j) x - x - (j : ℤ_[ℓ]) • (g x - x)) := by
  induction j with
  | zero =>
    intro x
    simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_smul, sub_self]
    exact inPow_zero _
  | succ j ih =>
    intro x
    have h2 : InPow (s + s) ((g ^ j) (g x - x) - (g x - x)) :=
      inPow_map (g ^ j - 1) (fun y ↦ order0 hg j y) (hg x)
    have e : (g ^ (j + 1)) x - x - ((j + 1 : ℕ) : ℤ_[ℓ]) • (g x - x) =
        ((g ^ j) x - x - (j : ℤ_[ℓ]) • (g x - x)) + ((g ^ j) (g x - x) - (g x - x)) := by
      rw [pow_succ, Module.End.mul_apply, map_sub (g ^ j) (g x) x, Nat.cast_add, Nat.cast_one,
        add_smul, one_smul]
      abel
    rw [e]
    exact inPow_add (ih x) h2

/-- Second order: `g ^ j - 1 - j D - C(j,2) D² ≡ 0 mod ℓ^(3s)`, `D = g - 1`. -/
theorem order2 (hg : ∀ y, InPow s (g y - y)) (j : ℕ) :
    ∀ x, InPow (s + (s + s)) ((g ^ j) x - x - (j : ℤ_[ℓ]) • (g x - x) -
      ((j.choose 2 : ℕ) : ℤ_[ℓ]) • (g (g x - x) - (g x - x))) := by
  induction j with
  | zero =>
    intro x
    rw [Nat.choose_eq_zero_of_lt (by norm_num : 0 < 2)]
    simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_smul, sub_self]
    exact inPow_zero _
  | succ j ih =>
    intro x
    have h2 : InPow (s + (s + s)) ((g ^ j) (g x - x) - (g x - x) -
        (j : ℤ_[ℓ]) • (g (g x - x) - (g x - x))) :=
      inPow_map (g ^ j - 1 - (j : ℤ_[ℓ]) • (g - 1)) (fun y ↦ order1 hg j y) (hg x)
    have hc : (j + 1).choose 2 = j + j.choose 2 := by
      have h := Nat.choose_succ_succ' j 1
      rw [Nat.choose_one_right] at h
      exact h
    have e : (g ^ (j + 1)) x - x - ((j + 1 : ℕ) : ℤ_[ℓ]) • (g x - x) -
        (((j + 1).choose 2 : ℕ) : ℤ_[ℓ]) • (g (g x - x) - (g x - x)) =
        ((g ^ j) x - x - (j : ℤ_[ℓ]) • (g x - x) -
          ((j.choose 2 : ℕ) : ℤ_[ℓ]) • (g (g x - x) - (g x - x))) +
        ((g ^ j) (g x - x) - (g x - x) - (j : ℤ_[ℓ]) • (g (g x - x) - (g x - x))) := by
      rw [pow_succ, Module.End.mul_apply, map_sub (g ^ j) (g x) x, hc, Nat.cast_add,
        Nat.cast_add, Nat.cast_one, add_smul, add_smul, one_smul]
      abel
    rw [e]
    exact inPow_add (ih x) h2

/-- The lifting step for an element of prime order. -/
theorem step {q : ℕ} (hq : q.Prime) (hgq : g ^ q = 1) (hs : 1 ≤ s) (hs2 : 2 ≤ s ∨ 3 ≤ ℓ)
    (hg : ∀ y, InPow s (g y - y)) (x : _root_.PkgI3.Tate.T ℓ M) : InPow (s + 1) (g x - x) := by
  have hℓ : ℓ.Prime := Fact.out
  by_cases hql : q = ℓ
  · have h0 : (g ^ ℓ) x - x = 0 := by rw [hql] at hgq; rw [hgq, Module.End.one_apply, sub_self]
    apply inPow_of_ell_smul
    rcases hs2 with h2s | hl3
    · have h1 := order1 hg ℓ x
      rw [h0, zero_sub] at h1
      have h3 := inPow_neg h1
      rw [neg_neg] at h3
      exact inPow_mono (by omega) h3
    · have h1 := order2 hg ℓ x
      rw [h0] at h1
      obtain ⟨m, hm⟩ := hℓ.dvd_choose_self (by norm_num : 2 ≠ 0) (by omega : 2 < ℓ)
      have hD2 : InPow (s + s + 1)
          ((ℓ : ℤ_[ℓ]) • (g (g x - x) - (g x - x))) :=
        inPow_ell_smul (inPow_map (g - 1) hg (hg x))
      have hC : InPow (s + s + 1)
          (((ℓ.choose 2 : ℕ) : ℤ_[ℓ]) • (g (g x - x) - (g x - x))) := by
        rw [hm, Nat.cast_mul, mul_comm, mul_smul]
        exact inPow_smul _ hD2
      have e : (ℓ : ℤ_[ℓ]) • (g x - x) =
          -(0 - (ℓ : ℤ_[ℓ]) • (g x - x) - ((ℓ.choose 2 : ℕ) : ℤ_[ℓ]) •
            (g (g x - x) - (g x - x))) -
          ((ℓ.choose 2 : ℕ) : ℤ_[ℓ]) • (g (g x - x) - (g x - x)) := by
        abel
      rw [e]
      exact inPow_sub (inPow_neg (inPow_mono (by omega) h1)) (inPow_mono (by omega) hC)
  · have h0 : (g ^ q) x - x = 0 := by rw [hgq, Module.End.one_apply, sub_self]
    have h1 := order1 hg q x
    rw [h0, zero_sub] at h1
    have h3 := inPow_neg h1
    rw [neg_neg] at h3
    have h4 : InPow (s + 1) ((q : ℤ_[ℓ]) • (g x - x)) := inPow_mono (by omega) h3
    have hcop : Nat.Coprime q (ℓ ^ (s + 1)) :=
      ((Nat.coprime_primes hq hℓ).mpr hql).pow_right (s + 1)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hab' : (a : ℤ_[ℓ]) * (q : ℤ_[ℓ]) + (b : ℤ_[ℓ]) * ((ℓ : ℤ_[ℓ]) ^ (s + 1)) = 1 := by
      exact_mod_cast hab
    have e : g x - x = (a : ℤ_[ℓ]) • ((q : ℤ_[ℓ]) • (g x - x)) +
        (b : ℤ_[ℓ]) • (((ℓ : ℤ_[ℓ]) ^ (s + 1)) • (g x - x)) := by
      rw [smul_smul, smul_smul, ← add_smul, hab', one_smul]
    rw [e]
    exact inPow_add (inPow_smul _ h4) (inPow_smul _ ⟨g x - x, rfl⟩)

/-- Serre's lemma for an element of prime order. -/
theorem eq_one_of_prime {q k : ℕ} (hq : q.Prime) (hgq : g ^ q = 1) (hk : 3 ≤ ℓ ^ k)
    (hg : ∀ y, InPow k (g y - y)) : g = 1 := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hk; omega
    · exact h
  have hcond : ∀ t, k ≤ t → 2 ≤ t ∨ 3 ≤ ℓ := by
    intro t ht
    rcases Nat.lt_or_ge t 2 with h | h
    · right
      have hk' : k = 1 := by omega
      rw [hk', pow_one] at hk
      exact hk
    · left; exact h
  have key : ∀ t, k ≤ t → ∀ y, InPow t (g y - y) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hg
    | succ t hkt ih => exact fun y ↦ step hq hgq (by omega) (hcond t hkt) ih y
  apply LinearMap.ext
  intro y
  rw [Module.End.one_apply]
  have hz : g y - y = 0 :=
    eq_zero_of_forall fun n ↦ inPow_mono (Nat.le_add_right n k) (key (n + k) (by omega) y)
  exact sub_eq_zero.mp hz

/-- Serre's lemma for any finite order, by strong induction on the order. -/
theorem eq_one_of_pow {k : ℕ} (hk : 3 ≤ ℓ ^ k) (hg : ∀ y, InPow k (g y - y)) :
    ∀ n, 0 < n → g ^ n = 1 → g = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hgn
    by_cases h1 : n = 1
    · rw [h1, pow_one] at hgn
      exact hgn
    · obtain ⟨q, hq, m, rfl⟩ := Nat.exists_prime_and_dvd h1
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hgm : (g ^ m) ^ q = 1 := by
        rw [← pow_mul, mul_comm]
        exact hgn
      have h2 : g ^ m = 1 := eq_one_of_prime hq hgm hk (order0 hg m)
      exact ih m (lt_of_lt_of_le (by omega : m < 2 * m) (Nat.mul_le_mul hq.two_le le_rfl)) hm h2

end SerreLemmaTateAux

/-- **Serre's lemma, Tate-module form**, proved. -/
theorem serreLemmaTate_proof : SerreLemmaTate := by
  unfold SerreLemmaTate
  intro ℓ _ k hk M _ f hfin hf
  obtain ⟨n, hn, hfn⟩ := hfin
  exact SerreLemmaTateAux.eq_one_of_pow hk hf n hn hfn

end HDec.CMSerreTate
