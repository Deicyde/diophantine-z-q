import ZInQKernel.Contrib.PoleRC.QClass
import ZInQKernel.Contrib.PoleRC.SimulLinAlg

/-!
# Arithmetic of the simultaneous construction (S12 lines 554–567 and 692–703)

* `kmat_mulVec_eq`: the matrix `Kmat ℓ` of `Matrix.lean` is the operator `kOp` of
  `SimulLinAlg.lean` for the symbol table `L j i = [q_j/q_i]` on the support `ℓ.primeFactors`.
* `matrixConditions_of`: `MatrixConditions ℓ β` from the operator statements.
* `lsym_prod`: `Σ_{q ∈ S} [q/p] = [∏ S/p]` (multiplicativity of the Legendre symbol).
* `sum_sgn_primeFactors`, `sum_lam_primeFactors`: S12 `(par:fixed-symbol-sums)`.
* `exists_prime_lsym`: a prime in a prescribed class modulo `12` with prescribed Legendre
  symbols modulo finitely many primes `> 3` (S12 lines 692–703: CRT and Dirichlet).
-/

namespace ZInQ.Manuscript.PoleRC.Simul

open Finset Matrix

/-- The symbol table `L j i = [q_j/q_i]`. -/
noncomputable def L : ℕ → ℕ → ZMod 2 := fun j i => lsym (j : ℤ) i

/-- Extension by zero of a vector on `Supp ℓ`. -/
noncomputable def ext (ℓ : ℕ) (v : Supp ℓ → ZMod 2) : ℕ → ZMod 2 :=
  fun q => if h : q ∈ ℓ.primeFactors then v ⟨q, h⟩ else 0

theorem ext_val (ℓ : ℕ) (v : Supp ℓ → ZMod 2) (i : Supp ℓ) : ext ℓ v i = v i := by
  simp [ext, i.2]

/-- **The bridge**: `(Kmat ℓ v)_i = Σ_{j ≠ i} [q_j/q_i](v_j + v_i)`. -/
theorem kmat_mulVec_eq (ℓ : ℕ) (v : Supp ℓ → ZMod 2) (i : Supp ℓ) :
    (Kmat ℓ *ᵥ v) i = kOp L ℓ.primeFactors (ext ℓ v) i := by
  classical
  have hmap : ((Finset.univ : Finset (Supp ℓ)).erase i).map (Function.Embedding.subtype _) =
      ℓ.primeFactors.erase i := by
    ext q
    simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨fun h => hj (Subtype.ext h), j.2⟩
    · rintro ⟨hq, hqP⟩; exact ⟨⟨q, hqP⟩, fun h => hq (congrArg Subtype.val h), rfl⟩
  unfold kOp
  rw [← hmap, Finset.sum_map]
  simp only [Function.Embedding.coe_subtype, ext_val]
  simp only [mulVec, dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h1 : ∀ j ∈ (Finset.univ : Finset (Supp ℓ)).erase i, Kmat ℓ i j * v j = L j i * v j :=
    fun j hj => by simp [Kmat, L, Ne.symm (Finset.ne_of_mem_erase hj)]
  rw [Finset.sum_congr rfl h1]
  simp only [Kmat, L, if_true]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **`MatrixConditions ℓ β` from the operator statements** on `P = ℓ.primeFactors`, with the
indicator `e = 1_{supp β}`. -/
theorem matrixConditions_of {ℓ β : ℕ} (hβ : β ≠ 0)
    (hB0 : ∃ q ∈ ℓ.primeFactors, q ∣ β) (hB1 : ∃ q ∈ ℓ.primeFactors, ¬ q ∣ β)
    (hKe : ∀ i ∈ ℓ.primeFactors,
      kOp L ℓ.primeFactors (fun j => if j ∈ β.primeFactors then 1 else 0) i = 0)
    (hker : ∀ v : ℕ → ZMod 2, (∀ i ∈ ℓ.primeFactors, kOp L ℓ.primeFactors v i = 0) →
      ∃ c d : ZMod 2, ∀ i ∈ ℓ.primeFactors, v i = c + d * (if i ∈ β.primeFactors then 1 else 0))
    (him : ∀ u : ℕ → ZMod 2, ¬ ∀ i ∈ ℓ.primeFactors, kOp L ℓ.primeFactors u i = lsym 3 i) :
    MatrixConditions ℓ β := by
  classical
  -- on `P`, `q ∈ supp β ↔ q ∣ β`
  have hmem : ∀ q ∈ ℓ.primeFactors, (q ∈ β.primeFactors ↔ q ∣ β) := fun q hq => by
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h => ⟨(Nat.mem_primeFactors.mp hq).1, h, hβ⟩⟩
  have hextB : ∀ q ∈ ℓ.primeFactors,
      ext ℓ (oneB ℓ β) q = if q ∈ β.primeFactors then 1 else 0 := fun q hq => by
    simp only [ext, dif_pos hq, oneB]
    by_cases h : q ∣ β
    · rw [if_pos h, if_pos ((hmem q hq).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((hmem q hq).mp h'))]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq, hqβ⟩ := hB0
    intro h
    have := congrFun h ⟨q, hq⟩
    simp only [oneB, if_pos hqβ, Pi.zero_apply] at this
    exact one_ne_zero this
  · obtain ⟨q, hq, hqβ⟩ := hB1
    intro h
    have := congrFun h ⟨q, hq⟩
    simp only [oneB, if_neg hqβ, Pi.one_apply] at this
    exact zero_ne_one this
  · funext i
    rw [kmat_mulVec_eq, Pi.zero_apply, kOp_congr L _ i.2 hextB]
    exact hKe i i.2
  · intro v hv
    obtain ⟨c, d, hcd⟩ := hker (ext ℓ v) fun i hi => by
      have := congrFun hv ⟨i, hi⟩
      rwa [kmat_mulVec_eq] at this
    have hvi : ∀ i : Supp ℓ, v i = c + d * oneB ℓ β i := fun i => by
      have h := hcd i i.2
      rw [ext_val] at h
      rw [h, oneB]
      by_cases hi : (i : ℕ) ∣ β
      · rw [if_pos ((hmem i i.2).mpr hi), if_pos hi]
      · rw [if_neg (fun h' => hi ((hmem i i.2).mp h')), if_neg hi]
    rcases sim_cases c with rfl | rfl <;> rcases sim_cases d with rfl | rfl
    · left; funext i; rw [hvi]; simp
    · right; right; left; funext i; rw [hvi]; simp
    · right; left; funext i; rw [hvi]; simp
    · right; right; right; funext i; rw [hvi]; simp
  · intro u hu
    refine him (ext ℓ u) fun i hi => ?_
    have := congrFun hu ⟨i, hi⟩
    rwa [kmat_mulVec_eq] at this

/-! ### Legendre symbols -/

theorem lsym_one (q : ℕ) : lsym 1 q = 0 := lsym_of_isSquare ⟨1, by rw [Int.cast_one, mul_one]⟩

theorem lsym_natCast_congr {a b : ℕ} {q : ℕ} (h : (a : ZMod q) = b) :
    lsym (a : ℤ) q = lsym (b : ℤ) q := by
  exact lsym_congr (by rw [Int.cast_natCast, Int.cast_natCast, h])

/-- **Multiplicativity**: `[∏ S/p] = Σ_{q ∈ S} [q/p]` for `S` prime to `p`. -/
theorem lsym_prod (p : ℕ) [Fact p.Prime] (S : Finset ℕ) (hS : ∀ q ∈ S, ¬ p ∣ q) :
    lsym ((∏ q ∈ S, q : ℕ) : ℤ) p = ∑ q ∈ S, lsym (q : ℤ) p := by
  induction S using Finset.induction_on with
  | empty => simpa using lsym_one p
  | insert a S haS ih =>
    rw [Finset.prod_insert haS, Finset.sum_insert haS, Nat.cast_mul]
    have hS' : ∀ q ∈ S, ¬ p ∣ q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have ha : ((a : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact hS a (Finset.mem_insert_self _ _)
    have hP : (((∏ q ∈ S, q : ℕ) : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => (Prime.dvd_finsetProd_iff (Nat.Prime.prime Fact.out) _).mp h |>.elim
        fun q ⟨hq, hpq⟩ => hS' q hq hpq
    rw [lsym_mul p ha hP, ih hS']

/-- `[x/p] = 0` from `IsSquare (x : ZMod p)` for a natural `x`. -/
theorem lsym_natCast_of_isSquare {x p : ℕ} (h : IsSquare (x : ZMod p)) : lsym (x : ℤ) p = 0 :=
  lsym_of_isSquare (by simpa using h)

/-- The sum of `[x/p]` over the primes `x` of a squarefree `N` prime to `p` is `[N/p]`. -/
theorem sum_lsym_primeFactors (p : ℕ) [Fact p.Prime] {N : ℕ} (hN : Squarefree N)
    (hpN : ¬ p ∣ N) : ∑ q ∈ N.primeFactors, lsym (q : ℤ) p = lsym (N : ℤ) p := by
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hN]
  rw [lsym_prod p _ fun q hq h => hpN (h.trans (Nat.dvd_of_mem_primeFactors hq))]

/-- The parity of the number of primes `≡ 3 (mod 4)` of an odd squarefree `N`. -/
theorem card_mod_four (N : ℕ) (hN : Squarefree N) (h2 : N % 2 = 1) :
    ((N.primeFactors.filter (fun q => q % 4 = 3)).card : ZMod 2) =
      if N % 4 = 3 then 1 else 0 := by
  have hprod : ∏ q ∈ N.primeFactors, q = N := Nat.prod_primeFactors_of_squarefree hN
  have hq : ∀ q ∈ N.primeFactors, (q : ZMod 4) = if q % 4 = 3 then -1 else 1 := by
    intro q hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hq2 : q % 2 = 1 := by
      rcases (Nat.prime_of_mem_primeFactors hq).eq_two_or_odd with h | h
      · rw [h] at hqd; omega
      · exact h
    rw [← ZMod.natCast_mod q 4]
    have : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  have hZ : (N : ZMod 4) = (-1) ^ (N.primeFactors.filter (fun q => q % 4 = 3)).card := by
    conv_lhs => rw [← hprod]
    push_cast
    rw [Finset.prod_congr rfl hq, Finset.prod_ite, Finset.prod_const_one, mul_one,
      Finset.prod_const]
  set k := (N.primeFactors.filter (fun q => q % 4 = 3)).card
  have hN4 : N % 4 = 1 ∨ N % 4 = 3 := by omega
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow] at hZ
    rw [(ZMod.natCast_eq_zero_iff_even).mpr he]
    have : N % 4 = 1 := by
      have := (ZMod.natCast_eq_natCast_iff' N 1 4).mp (by rw [hZ]; simp)
      simpa using this
    rw [if_neg (by omega)]
  · rw [ho.neg_one_pow] at hZ
    rw [ZMod.natCast_eq_one_iff_odd.mpr ho]
    have : N % 4 = 3 := by
      have h3 : (N : ZMod 4) = ((3 : ℕ) : ZMod 4) := by rw [hZ]; decide
      simpa using (ZMod.natCast_eq_natCast_iff' N 3 4).mp h3
    rw [if_pos this]

/-- The parity of the number of primes `≡ 2 (mod 3)` of a squarefree `N` prime to `3`. -/
theorem card_mod_three (N : ℕ) (hN : Squarefree N) (h3 : N % 3 ≠ 0) :
    ((N.primeFactors.filter (fun q => q % 3 = 2)).card : ZMod 2) =
      if N % 3 = 2 then 1 else 0 := by
  have hprod : ∏ q ∈ N.primeFactors, q = N := Nat.prod_primeFactors_of_squarefree hN
  have hq : ∀ q ∈ N.primeFactors, (q : ZMod 3) = if q % 3 = 2 then -1 else 1 := by
    intro q hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hq3 : q % 3 ≠ 0 := by
      intro h; have : 3 ∣ N := (Nat.dvd_of_mod_eq_zero h).trans hqd; omega
    rw [← ZMod.natCast_mod q 3]
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  have hZ : (N : ZMod 3) = (-1) ^ (N.primeFactors.filter (fun q => q % 3 = 2)).card := by
    conv_lhs => rw [← hprod]
    push_cast
    rw [Finset.prod_congr rfl hq, Finset.prod_ite, Finset.prod_const_one, mul_one,
      Finset.prod_const]
  set k := (N.primeFactors.filter (fun q => q % 3 = 2)).card
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow] at hZ
    rw [(ZMod.natCast_eq_zero_iff_even).mpr he]
    have : N % 3 = 1 := by
      have := (ZMod.natCast_eq_natCast_iff' N 1 3).mp (by rw [hZ]; simp)
      simpa using this
    rw [if_neg (by omega)]
  · rw [ho.neg_one_pow] at hZ
    rw [ZMod.natCast_eq_one_iff_odd.mpr ho]
    have : N % 3 = 2 := by
      have h2 : (N : ZMod 3) = ((2 : ℕ) : ZMod 3) := by rw [hZ]; decide
      simpa using (ZMod.natCast_eq_natCast_iff' N 2 3).mp h2
    rw [if_pos this]

/-- **S12 `(par:fixed-symbol-sums)`, the `s`-sum**: `Σ_{q ∣ N} [−1/q] = [N ≡ 3 (mod 4)]`. -/
theorem sum_sgn_primeFactors (N : ℕ) (hN : Squarefree N) (h2 : N % 2 = 1) :
    ∑ q ∈ N.primeFactors, lsym (-1) q = if N % 4 = 3 then 1 else 0 := by
  have h : ∀ q ∈ N.primeFactors, lsym (-1) q = if q % 4 = 3 then 1 else 0 := by
    intro q hq
    have := Fact.mk (Nat.prime_of_mem_primeFactors hq)
    exact lsym_neg_one q
  rw [Finset.sum_congr rfl h, Finset.sum_boole, card_mod_four N hN h2]

/-- **S12 `(par:fixed-symbol-sums)`, the `λ`-sum**: `Σ_{q ∣ N} [3/q] = [N ≡ 2 (mod 3)] +
[N ≡ 3 (mod 4)]` (reciprocity with `3`, S12 line 556). -/
theorem sum_lam_primeFactors (N : ℕ) (hN : Squarefree N) (h2 : N % 2 = 1) (h3 : N % 3 ≠ 0) :
    ∑ q ∈ N.primeFactors, lsym 3 q =
      (if N % 3 = 2 then 1 else 0) + (if N % 4 = 3 then 1 else 0) := by
  have h : ∀ q ∈ N.primeFactors, lsym 3 q =
      (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have := Fact.mk hqp
    have hqd := Nat.dvd_of_mem_primeFactors hq
    refine lsym_three q ?_ ?_
    · rcases hqp.eq_two_or_odd with h | h
      · rw [h] at hqd; omega
      · exact h
    · intro h; rw [h] at hqd; omega
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
    card_mod_three N hN h3, card_mod_four N hN h2]

/-! ### Realization by a prime (S12 lines 692–703) -/

/-- A residue with a prescribed Legendre symbol modulo an odd prime. -/
theorem exists_residue (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (τ : ZMod 2) :
    ∃ a : ℕ, ¬ q ∣ a ∧ lsym (a : ℤ) q = τ := by
  have := Fact.mk hq
  rcases sim_cases τ with rfl | rfl
  · exact ⟨1, fun h => hq.one_lt.ne' (Nat.dvd_one.mp h), by simpa using lsym_one q⟩
  · obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
    refine ⟨x.val, fun h => hx ?_, lsym_of_not_isSquare (by simpa using hx)⟩
    have : (x.val : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [ZMod.natCast_zmod_val] at this
    rw [this]; exact ⟨0, by simp⟩

/-- **The realization step** (S12 lines 692–703): a prime `p` in the class of `r` modulo `12`
with prescribed Legendre symbols `[p/q] = τ q` modulo every prime `q > 3` of a finite set `Q`.
Each symbol is imposed by a nonzero residue modulo `q`; the Chinese remainder theorem gives a
reduced class modulo `12 ∏ Q`; Dirichlet's theorem gives a prime in it. -/
theorem exists_prime_lsym (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ 3 < q) {r : ℕ}
    (hr : Nat.Coprime r 12) (τ : ℕ → ZMod 2) :
    ∃ p : ℕ, p.Prime ∧ p % 12 = r % 12 ∧ ∀ q ∈ Q, ¬ q ∣ p ∧ lsym (p : ℤ) q = τ q := by
  classical
  have hres : ∀ q ∈ Q, ∃ a : ℕ, ¬ q ∣ a ∧ lsym (a : ℤ) q = τ q := fun q hq =>
    exists_residue q (hQ q hq).1 (by have := (hQ q hq).2; omega) (τ q)
  choose! a ha using hres
  -- CRT modulo the primes of `Q`
  have hs : ∀ q ∈ Q, id q ≠ 0 := fun q hq => (hQ q hq).1.ne_zero
  have pp : Set.Pairwise (Q : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro q hq q' hq' hne
    exact (Nat.coprime_primes (hQ q hq).1 (hQ q' hq').1).mpr hne
  obtain ⟨k₁, hk₁⟩ := Nat.chineseRemainderOfFinset a id Q hs pp
  set N := ∏ q ∈ Q, q with hN
  have hcop12 : Nat.Coprime 12 N := by
    refine Nat.Coprime.prod_right fun q hq => ?_
    have hqp := (hQ q hq).1
    have hq3 := (hQ q hq).2
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hqp]
    intro h
    have : q ∣ 2 ^ 2 * 3 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hqp).mp this with h' | h'
    · have := Nat.Prime.dvd_of_dvd_pow hqp h'
      have := Nat.le_of_dvd (by norm_num) this; omega
    · have := Nat.le_of_dvd (by norm_num) h'; omega
  obtain ⟨k, hk12, hkN⟩ := Nat.chineseRemainder hcop12 r k₁
  have hkq : ∀ q ∈ Q, k ≡ a q [MOD q] := fun q hq =>
    (Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem _ hq) hkN).trans (hk₁ q hq)
  have hkcop : Nat.Coprime k (12 * N) := by
    refine Nat.Coprime.mul_right ?_ (Nat.Coprime.prod_right fun q hq => ?_)
    · show Nat.gcd k 12 = 1
      rw [Nat.ModEq.gcd_eq hk12]; exact hr
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hQ q hq).1]
      intro h
      exact (ha q hq).1 ((Nat.modEq_zero_iff_dvd.mp
        ((hkq q hq).symm.trans (Nat.modEq_zero_iff_dvd.mpr h))))
  have hpos : 0 < 12 * N := Nat.mul_pos (by norm_num)
    (Finset.prod_pos fun q hq => (hQ q hq).1.pos)
  have : NeZero (12 * N) := ⟨hpos.ne'⟩
  obtain ⟨p, -, hp, hpk⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime k (12 * N)).mpr hkcop) 0
  have hpk' : p ≡ k [MOD 12 * N] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hpk
  refine ⟨p, hp, ?_, fun q hq => ?_⟩
  · exact (Nat.ModEq.of_dvd (Dvd.intro N rfl) hpk').trans hk12
  · have hpq : p ≡ a q [MOD q] :=
      (Nat.ModEq.of_dvd ((Finset.dvd_prod_of_mem _ hq).trans (Dvd.intro_left 12 rfl)) hpk').trans
        (hkq q hq)
    refine ⟨fun h => (ha q hq).1 ?_, ?_⟩
    · exact Nat.modEq_zero_iff_dvd.mp (hpq.symm.trans (Nat.modEq_zero_iff_dvd.mpr h))
    · rw [lsym_natCast_congr ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hpq)]
      exact (ha q hq).2

end ZInQ.Manuscript.PoleRC.Simul
