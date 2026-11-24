import ZInQKernel.Contrib.OneProof.PoleS12.Convert

/-!
# Realizing prescribed Legendre symbols by primes (S12 L668–679)

ELLIOT (supplement S12, lines 668–679): "Choose the auxiliary primes successively. At each step,
specify the type modulo 12 and the Legendre symbols modulo every already fixed prime … The
Chinese remainder theorem gives a reduced residue class, and Dirichlet's theorem supplies
infinitely many primes in it."

* `exists_prime_lsym`: CRT (`Nat.chineseRemainderOfFinset`) and Dirichlet
  (`Nat.forall_exists_prime_gt_and_modEq`, in Mathlib).
* `exists_aux_primes`: the `|B| − 1` auxiliary primes of type `(0, 0)` (`≡ 1 mod 12`) with the
  cross-block columns `e_b + e_{b*}` (tex L1041–1044, S12 L606–618).
-/

namespace ZInQ.Manuscript.PoleS12

open Finset ZInQ.Manuscript.PoleRC

/-- A prime different from `2` and `3`. -/
def Odd3 (q : ℕ) : Prop := q.Prime ∧ q % 2 = 1 ∧ q ≠ 3

theorem odd3_of_mod12 {q : ℕ} (hq : q.Prime) (h : q % 12 = 1 ∨ q % 12 = 7 ∨ q % 12 = 5 ∨
    q % 12 = 11) : Odd3 q :=
  ⟨hq, by omega, by rintro rfl; omega⟩

theorem squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [prod_insert hps, Nat.squarefree_mul_iff]
    refine ⟨Nat.Coprime.prod_right fun q hq => ?_, (hs p (mem_insert_self _ _)).squarefree,
      ih fun q hq => hs q (mem_insert_of_mem hq)⟩
    exact (Nat.coprime_primes (hs p (mem_insert_self _ _)) (hs q (mem_insert_of_mem hq))).mpr
      (fun h => hps (h ▸ hq))

theorem lsym_one (q : ℕ) : lsym 1 q = 0 := lsym_of_isSquare ⟨1, by simp⟩

/-- A residue prime to `q` with a prescribed symbol. -/
theorem exists_residue (q : ℕ) (hq : q.Prime) (hq2 : q % 2 = 1) (e : ZMod 2) :
    ∃ g : ℕ, ¬ q ∣ g ∧ lsym (g : ℤ) q = e := by
  have := Fact.mk hq
  rcases z2_cases e with rfl | rfl
  · exact ⟨1, fun h => hq.one_lt.ne' (Nat.dvd_one.mp h), by simpa using lsym_one q⟩
  · obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod q)
      (by rw [ZMod.ringChar_zmod_n]; omega)
    have hcast : ((a.val : ℤ) : ZMod q) = a := by simp
    refine ⟨a.val, fun h => ha ?_, lsym_of_not_isSquare (by rw [hcast]; exact ha)⟩
    have : a = 0 := by
      rw [← ZMod.natCast_zmod_val a, ZMod.natCast_eq_zero_iff]; exact h
    rw [this]; exact ⟨0, by simp⟩

theorem lsym_congr_nat {p g q : ℕ} (h : (p : ZMod q) = (g : ZMod q)) :
    lsym (p : ℤ) q = lsym (g : ℤ) q := by
  exact lsym_congr (by simp only [Int.cast_natCast, h])

/-- **CRT and Dirichlet** (S12 L672–679): a prime outside a finite set, in a prescribed reduced
class modulo `12`, with prescribed symbols modulo finitely many primes `≠ 2, 3`. -/
theorem exists_prime_lsym (r : ℕ) (hr : Nat.Coprime r 12) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, Odd3 q) (e : ℕ → ZMod 2) (F : Finset ℕ) :
    ∃ p, p.Prime ∧ p % 12 = r % 12 ∧ p ∉ F ∧ ∀ q ∈ Q, lsym (p : ℤ) q = e q := by
  classical
  choose g hg using fun q (hq : q ∈ Q) => exists_residue q (hQ q hq).1 (hQ q hq).2.1 (e q)
  let a : ℕ → ℕ := fun i => if h : i ∈ Q then g i h else r
  have h12 : (12 : ℕ) ∉ Q := fun h => by
    have := (hQ 12 h).1; norm_num at this
  have hs : ∀ i ∈ insert 12 Q, (id i : ℕ) ≠ 0 := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · norm_num
    · exact (hQ i hi).1.ne_zero
  have hcop12 : ∀ q ∈ Q, Nat.Coprime 12 q := by
    intro q hq
    obtain ⟨hqp, hq2, hq3⟩ := hQ q hq
    rw [Nat.coprime_comm, hqp.coprime_iff_not_dvd]
    intro h
    have h2 : q ∣ 2 * 2 * 3 := h
    rcases (Nat.Prime.dvd_mul hqp).mp h2 with h | h
    · rcases (Nat.Prime.dvd_mul hqp).mp h with h | h <;>
      · have := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp h; omega
    · exact hq3 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).mp h)
  have pp : Set.Pairwise (↑(insert 12 Q) : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro i hi j hj hij
    simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hi hj
    simp only [Function.onFun, id]
    rcases hi with rfl | hi <;> rcases hj with rfl | hj
    · exact absurd rfl hij
    · exact hcop12 j hj
    · exact (hcop12 i hi).symm
    · exact (Nat.coprime_primes (hQ i hi).1 (hQ j hj).1).mpr hij
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset a id (insert 12 Q) hs pp
  have hk12 : k ≡ r [MOD 12] := by
    have := hk 12 (mem_insert_self _ _)
    simpa [a, h12] using this
  have hkq : ∀ q (hq : q ∈ Q), k ≡ g q hq [MOD q] := by
    intro q hq
    have := hk q (mem_insert_of_mem hq)
    simpa [a, hq] using this
  have hkM : Nat.Coprime k (∏ i ∈ insert 12 Q, i) := by
    refine Nat.Coprime.prod_right fun i hi => ?_
    rcases mem_insert.mp hi with rfl | hi
    · rw [Nat.Coprime, hk12.gcd_eq]; exact hr
    · rw [Nat.Coprime, (hkq i hi).gcd_eq, ← Nat.Coprime, Nat.coprime_comm,
        (hQ i hi).1.coprime_iff_not_dvd]
      exact (hg i hi).1
  have hM : (∏ i ∈ insert 12 Q, i) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i hi => hs i hi
  obtain ⟨p, hpF, hp, hpk⟩ := Nat.forall_exists_prime_gt_and_modEq (F.sup id) hM hkM
  have hpi : ∀ i ∈ insert 12 Q, p ≡ k [MOD i] := fun i hi =>
    Nat.ModEq.of_dvd (dvd_prod_of_mem _ hi) hpk
  refine ⟨p, hp, (hpi 12 (mem_insert_self _ _)).trans hk12, fun hpF' => ?_, fun q hq => ?_⟩
  · have := le_sup (f := id) hpF'
    simp only [id] at this
    omega
  · rw [← (hg q hq).2]
    apply lsym_congr_nat
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      ((hpi q (mem_insert_of_mem hq)).trans (hkq q hq))

/-- Reciprocity when one prime is `≡ 1 (mod 4)`: `[q/p] = [p/q]`. -/
theorem lsym_recip_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1)
    (hq2 : q % 2 = 1) (hpq : p ≠ q) : lsym (q : ℤ) p = lsym (p : ℤ) q := by
  have := Fact.mk hp
  have := Fact.mk hq
  rw [lsym_recip q p hq2 (by omega) (Ne.symm hpq), lsym_neg_one p, if_neg (by omega), mul_zero,
    add_zero]

/-- **The auxiliary primes of type `(0,0)`** (tex L1041–1044; S12 L567–571, L606–618): for each
`b ∈ T` a prime `g b ≡ 1 (mod 12)` outside `B ∪ J`, with `[g b/b'] = [b' = b] + [b' = b*]` on
`B` (the column `e_b + e_{b*}`), `[g b/j] = 0` on `J`, and vanishing mutual symbols. -/
theorem exists_aux_primes (B J : Finset ℕ) (bs : ℕ) (hB : ∀ q ∈ B, Odd3 q)
    (hJ : ∀ q ∈ J, Odd3 q) (hBJ : Disjoint B J) (T : Finset ℕ) :
    ∃ g : ℕ → ℕ, (∀ b ∈ T, (g b).Prime ∧ g b % 12 = 1 ∧ g b ∉ B ∧ g b ∉ J ∧
      (∀ b' ∈ B, lsym (g b : ℤ) b' = (if b' = b then 1 else 0) + (if b' = bs then 1 else 0)) ∧
      (∀ j ∈ J, lsym (g b : ℤ) j = 0)) ∧ Set.InjOn g T ∧
      (∀ b ∈ T, ∀ b'' ∈ T, b'' ≠ b → lsym (g b'' : ℤ) (g b) = 0) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨id, fun b hb => absurd hb (notMem_empty b), fun _ h => absurd h (notMem_empty _),
      fun b hb => absurd hb (notMem_empty b)⟩
  | insert b T hbT ih =>
    obtain ⟨g, hg, hinj, hmut⟩ := ih
    have hQ : ∀ q ∈ B ∪ J ∪ T.image g, Odd3 q := by
      intro q hq
      rcases mem_union.mp hq with hq | hq
      · rcases mem_union.mp hq with hq | hq
        · exact hB q hq
        · exact hJ q hq
      · obtain ⟨b'', hb'', rfl⟩ := mem_image.mp hq
        exact odd3_of_mod12 (hg b'' hb'').1 (Or.inl (hg b'' hb'').2.1)
    obtain ⟨p, hp, hp12, hpF, hpe⟩ := exists_prime_lsym 1 (by norm_num) (B ∪ J ∪ T.image g) hQ
      (fun q => if q ∈ B then (if q = b then 1 else 0) + (if q = bs then 1 else 0) else 0)
      (B ∪ J ∪ T.image g)
    have hpB : p ∉ B := fun h => hpF (mem_union_left _ (mem_union_left _ h))
    have hpJ : p ∉ J := fun h => hpF (mem_union_left _ (mem_union_right _ h))
    have hpT : ∀ b'' ∈ T, g b'' ≠ p := fun b'' hb'' h =>
      hpF (mem_union_right _ (h ▸ mem_image_of_mem g hb''))
    have hupd : ∀ b'' ∈ T, Function.update g b p b'' = g b'' := fun b'' hb'' =>
      Function.update_of_ne (fun h => hbT (by rw [← h]; exact hb'')) _ _
    have hpq : ∀ b'' ∈ T, lsym (p : ℤ) (g b'') = 0 := by
      intro b'' hb''
      rw [hpe _ (mem_union_right _ (mem_image_of_mem g hb'')), if_neg (hg b'' hb'').2.2.1]
    have hqp : ∀ b'' ∈ T, lsym (g b'' : ℤ) p = 0 := by
      intro b'' hb''
      rw [lsym_recip_one hp (hg b'' hb'').1 (by omega)
        (by have := (hg b'' hb'').2.1; omega) (Ne.symm (hpT b'' hb''))]
      exact hpq b'' hb''
    refine ⟨Function.update g b p, fun b' hb' => ?_, ?_, ?_⟩
    · rcases mem_insert.mp hb' with hb'b | hb'
      · rw [hb'b, Function.update_self]
        refine ⟨hp, by omega, hpB, hpJ, fun b'' hb'' => ?_, fun j hj => ?_⟩
        · rw [hpe _ (mem_union_left _ (mem_union_left _ hb'')), if_pos hb'']
        · rw [hpe _ (mem_union_left _ (mem_union_right _ hj)),
            if_neg (disjoint_right.mp hBJ hj)]
      · rw [hupd b' hb']; exact hg b' hb'
    · intro x hx y hy hxy
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hx hy
      rcases hx with hxb | hx <;> rcases hy with hyb | hy
      · rw [hxb, hyb]
      · rw [hxb, Function.update_self, hupd y hy] at hxy; exact absurd hxy.symm (hpT y hy)
      · rw [hyb, Function.update_self, hupd x hx] at hxy; exact absurd hxy (hpT x hx)
      · rw [hupd x hx, hupd y hy] at hxy; exact hinj hx hy hxy
    · intro x hx y hy hyx
      rcases mem_insert.mp hx with hxb | hx <;> rcases mem_insert.mp hy with hyb | hy
      · exact absurd (hyb.trans hxb.symm) hyx
      · rw [hxb, Function.update_self, hupd y hy]; exact hqp y hy
      · rw [hyb, Function.update_self, hupd x hx]; exact hpq x hx
      · rw [hupd x hx, hupd y hy]; exact hmut x hx y hy hyx

end ZInQ.Manuscript.PoleS12
