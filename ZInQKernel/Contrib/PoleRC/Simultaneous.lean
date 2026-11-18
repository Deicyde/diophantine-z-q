import ZInQKernel.Contrib.PoleRC.SimulArith

/-!
# The simultaneous construction: a proof of `MatrixRealization` (S12 lines 543–703)

Elliot's construction (`diophantine_zq.tex` lines 1033–1060, retained source S12
`parity-frozen-4eaee875.tex`, Lemma `par:simultaneous-matrices`), with `B = supp β`,
`J = supp θ`, `d = ω(β)`:

* slots (S12 570–574): `d − 1` primes `p_b ≡ 1 (mod 12)` (type `(s, λ) = (0, 0)`), indexed by
  `b ∈ B ∖ {b_d}`, and one prime `q₀ ≡ 7 (mod 12)` (type `(1, 1)`);
* symbols (S12 633–641): `[p_b/q] = [q/p_b] = C_{q, p_b}` with `C`-column `e_b + e_{b_d}`
  (the manuscript's "columns `e_i + e_d`", line 1045), all other symbols incident with the
  `p_b` zero, `[q₀/q_b] = Σ_{i ∈ I} C_{b i}`, `[q₀/p_b] = 0`, and the `q₀`–`J` symbols free;
* `K♯ = K + λaᵗ`, `a = e_{q₀} + e_{b*}` with `b* = b_d` (S12 585–625; `SimulLinAlg.lean`);
* the deleted matrix on `B ∪ I` is `[[A, C], [Cᵗ, 0]]`, nonsingular (S12 651–672);
* on `B ∪ I ∪ J` the free `q₀`–`J` bits toggle the `J`-diagonal; one assignment makes the
  deleted matrix nonsingular, and it does not change the smaller matrix (S12 674–688);
* the primes are realized successively, `q₀` last, by reciprocity, CRT and Dirichlet
  (S12 692–703; `exists_prime_lsym`).

Main results: `matrixRealization : MatrixRealization` and
`simultaneousConstruction_of_dimThree : DimThreeCount → SimultaneousConstruction`.
-/

namespace ZInQ.Manuscript.PoleRC.Simul

open Finset

theorem squarefree_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S haS ih =>
    rw [Finset.prod_insert haS, Nat.squarefree_mul_iff]
    have ha := hS a (Finset.mem_insert_self _ _)
    refine ⟨Nat.Coprime.prod_right fun q hq => (Nat.coprime_primes ha
      (hS q (Finset.mem_insert_of_mem hq))).mpr (fun h => haS (h ▸ hq)), ha.squarefree,
      ih fun p hp => hS p (Finset.mem_insert_of_mem hp)⟩

theorem lsym_neg_one_of_mod12_one {p : ℕ} (hp : p.Prime) (h : p % 12 = 1) : lsym (-1) p = 0 := by
  have := Fact.mk hp
  rw [lsym_neg_one, if_neg (by omega)]

theorem lsym_three_of_mod12_one {p : ℕ} (hp : p.Prime) (h : p % 12 = 1) : lsym 3 p = 0 := by
  have := Fact.mk hp
  rw [lsym_three p (by omega) (by omega), if_neg (by omega), if_neg (by omega), add_zero]

theorem lsym_neg_one_of_mod12_seven {p : ℕ} (hp : p.Prime) (h : p % 12 = 7) :
    lsym (-1) p = 1 := by
  have := Fact.mk hp
  rw [lsym_neg_one, if_pos (by omega)]

/-- **The `I`-slots, chosen successively** (S12 lines 570–574, 633–635, 692–700): for each
`b ∈ T` a prime `p_b ≡ 1 (mod 12)`, outside `B ∪ J`, with `[p_b/q] = [q = b] + [q = b_d]` for
`q ∈ B`, `[p_b/q_j] = 0` for `j ∈ J`, and `[p_b/p_{b'}] = 0` for the other slots. -/
theorem exists_Iprimes (Bs J : Finset ℕ) (hBJ : ∀ q ∈ Bs ∪ J, q.Prime ∧ 3 < q)
    (hdisj : Disjoint Bs J) (bd : ℕ) (T : Finset ℕ) :
    ∃ pI : ℕ → ℕ,
      (∀ b ∈ T, (pI b).Prime ∧ pI b % 12 = 1 ∧ pI b ∉ Bs ∪ J ∧
        (∀ q ∈ Bs, lsym (pI b : ℤ) q = (if q = b then 1 else 0) + (if q = bd then 1 else 0)) ∧
        (∀ j ∈ J, lsym (pI b : ℤ) j = 0)) ∧
      (∀ b ∈ T, ∀ b' ∈ T, pI b = pI b' → b = b') ∧
      (∀ b ∈ T, ∀ b' ∈ T, b ≠ b' → lsym (pI b : ℤ) (pI b') = 0) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨id, by simp, by simp, by simp⟩
  | insert b T hbT ih =>
    obtain ⟨pI, h1, h2, h3⟩ := ih
    set Q := Bs ∪ J ∪ T.image pI with hQdef
    have hQ : ∀ q ∈ Q, q.Prime ∧ 3 < q := by
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact hBJ q hq
      · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hq
        have h := h1 b' hb'
        have := h.1.two_le
        exact ⟨h.1, by have := h.2.1; omega⟩
    obtain ⟨p, hp, hp12, hpQ⟩ := exists_prime_lsym Q hQ (r := 1) (by norm_num)
      (fun q => if q ∈ Bs then (if q = b then 1 else 0) + (if q = bd then 1 else 0) else 0)
    have hpQ' : ∀ q ∈ Q, p ≠ q := fun q hq h => (hpQ q hq).1 (h ▸ dvd_rfl)
    -- the new slot against an old one
    have hnew_old : ∀ b' ∈ T, lsym (p : ℤ) (pI b') = 0 := by
      intro b' hb'
      have hm : pI b' ∈ Q := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb')
      rw [(hpQ _ hm).2]
      have : pI b' ∉ Bs := fun h => (h1 b' hb').2.2.1 (Finset.mem_union_left _ h)
      simp [this]
    have hold_new : ∀ b' ∈ T, lsym (pI b' : ℤ) p = 0 := by
      intro b' hb'
      have hm : pI b' ∈ Q := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb')
      have := Fact.mk hp
      have := Fact.mk (h1 b' hb').1
      rw [lsym_recip (pI b') p (by have := (h1 b' hb').2.1; omega) (by simp at hp12; omega)
        (Ne.symm (hpQ' _ hm)), lsym_neg_one_of_mod12_one (h1 b' hb').1 (h1 b' hb').2.1, zero_mul,
        add_zero]
      exact hnew_old b' hb'
    refine ⟨Function.update pI b p, ?_, ?_, ?_⟩
    · intro b'' hb''
      rcases Finset.mem_insert.mp hb'' with rfl | hb''T
      · rw [Function.update_self]
        refine ⟨hp, by simpa using hp12, fun h => hpQ' p (Finset.mem_union_left _ h) rfl, ?_, ?_⟩
        · intro q hq
          rw [(hpQ q (Finset.mem_union_left _ (Finset.mem_union_left _ hq))).2, if_pos hq]
        · intro j hj
          have hjB : j ∉ Bs := fun h => Finset.disjoint_left.mp hdisj h hj
          rw [(hpQ j (Finset.mem_union_left _ (Finset.mem_union_right _ hj))).2, if_neg hjB]
      · have hne : b'' ≠ b := fun h => hbT (h ▸ hb''T)
        rw [Function.update_of_ne hne]
        exact h1 b'' hb''T
    · intro b1 hb1 b2 hb2 heq
      rcases Finset.mem_insert.mp hb1 with rfl | hb1T <;>
        rcases Finset.mem_insert.mp hb2 with rfl | hb2T
      · rfl
      · have hne : b2 ≠ b1 := fun h => hbT (h ▸ hb2T)
        rw [Function.update_self, Function.update_of_ne hne] at heq
        exact absurd heq (hpQ' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb2T)))
      · have hne : b1 ≠ b2 := fun h => hbT (h ▸ hb1T)
        rw [Function.update_self, Function.update_of_ne hne] at heq
        exact absurd heq.symm (hpQ' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb1T)))
      · have hne1 : b1 ≠ b := fun h => hbT (h ▸ hb1T)
        have hne2 : b2 ≠ b := fun h => hbT (h ▸ hb2T)
        rw [Function.update_of_ne hne1, Function.update_of_ne hne2] at heq
        exact h2 b1 hb1T b2 hb2T heq
    · intro b1 hb1 b2 hb2 hne
      rcases Finset.mem_insert.mp hb1 with rfl | hb1T <;>
        rcases Finset.mem_insert.mp hb2 with rfl | hb2T
      · exact absurd rfl hne
      · have hne' : b2 ≠ b1 := fun h => hbT (h ▸ hb2T)
        rw [Function.update_self, Function.update_of_ne hne']
        exact hnew_old b2 hb2T
      · have hne' : b1 ≠ b2 := fun h => hbT (h ▸ hb1T)
        rw [Function.update_self, Function.update_of_ne hne']
        exact hold_new b1 hb1T
      · have hne1 : b1 ≠ b := fun h => hbT (h ▸ hb1T)
        have hne2 : b2 ≠ b := fun h => hbT (h ▸ hb2T)
        rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact h3 b1 hb1T b2 hb2T hne

/-- **The matrix conditions on one support** `P = {q₀} ∪ P'`, `B ∪ I ⊆ P' ⊆ B ∪ I ∪ J`, from the
nonsingularity of the deleted matrix (S12 lines 585–650): `K1_B = 0` row by row (S12 643–650),
then `ker K♯ = ⟨1⟩` and the rank-one reduction. -/
theorem matrixConditions_of_slots {ℓ β : ℕ} (hβ0 : β ≠ 0) (Bs : Finset ℕ)
    (hBs : Bs = β.primeFactors) (bd : ℕ) (hbd : bd ∈ Bs) (pI : ℕ → ℕ) (Is : Finset ℕ)
    (hIs : Is = (Bs.erase bd).image pI) (P' : Finset ℕ) (q0 : ℕ)
    (hBP : Bs ⊆ P') (hIP : ∀ b ∈ Bs.erase bd, pI b ∈ P')
    (hIB : ∀ b ∈ Bs.erase bd, pI b ∉ Bs)
    (hinj : ∀ b ∈ Bs.erase bd, ∀ b' ∈ Bs.erase bd, pI b = pI b' → b = b')
    (hq0 : q0 ∉ P') (hℓ : ℓ.primeFactors = insert q0 P')
    (hN : NonsingOn (dOp L P' (fun j => L q0 j) (fun i => lsym 3 i) bd) P')
    (hcol : ∀ b ∈ Bs.erase bd, ∀ j ∈ P', j ≠ pI b →
      L j (pI b) = (if j = b then 1 else 0) + (if j = bd then 1 else 0))
    (hrow : ∀ b ∈ Bs.erase bd, ∀ j ∈ Bs,
      L (pI b) j = (if j = b then 1 else 0) + (if j = bd then 1 else 0))
    (hcrossB : ∀ i ∈ Bs, ∑ j ∈ P' \ (Bs ∪ Is), L j i = 0)
    (hcrossJ : ∀ i ∈ P' \ (Bs ∪ Is), ∑ j ∈ Bs, L j i = 0)
    (hq0B : ∀ i ∈ Bs, L q0 i = ∑ b ∈ Bs.erase bd, L (pI b) i)
    (hrecq0 : ∀ j ∈ Bs, L j q0 = L q0 j + lsym (-1) j)
    (hsB : ∑ j ∈ Bs, lsym (-1) j = 0) :
    MatrixConditions ℓ β := by
  classical
  have hmemI : ∀ j, j ∈ Is ↔ ∃ b ∈ Bs.erase bd, pI b = j := fun j => by
    rw [hIs, Finset.mem_image]
  have hsumI : ∀ f : ℕ → ZMod 2, ∑ j ∈ Is, f j = ∑ b ∈ Bs.erase bd, f (pI b) := fun f => by
    rw [hIs]; exact Finset.sum_image fun b hb b' hb' h => hinj b hb b' hb' h
  have hBP' : Bs ⊆ insert q0 P' := hBP.trans (Finset.subset_insert _ _)
  have hq0nB : q0 ∉ Bs := fun h => hq0 (hBP h)
  -- `Σ_{b ∈ B} Σ_{i ∈ I} C_{b i} = 0`: each column of `C` has two entries
  have hCsum : ∑ j ∈ Bs, ∑ b ∈ Bs.erase bd, L (pI b) j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [Finset.sum_congr rfl (hrow b hb), Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', if_pos (Finset.mem_of_mem_erase hb), if_pos hbd, sim_add_self]
  -- `K1_B = 0` (S12 lines 643–650)
  have hKe : ∀ i ∈ insert q0 P', kOp L (insert q0 P') (fun j => if j ∈ Bs then 1 else 0) i = 0 := by
    intro i hi
    rw [kOp_ind L _ hBP' i]
    by_cases hiB : i ∈ Bs
    · -- a `B` row: the `I` and `q₀` terms cancel, the `J` sum is zero
      rw [if_pos hiB]
      have h1 : insert q0 P' \ Bs = insert q0 (P' \ Bs) := by
        ext j; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h | h, hj⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hj⟩
        · rintro (h | ⟨h, hj⟩)
          · exact ⟨Or.inl h, h ▸ hq0nB⟩
          · exact ⟨Or.inr h, hj⟩
      have hsub : Is ⊆ P' \ Bs := by
        intro j hj
        obtain ⟨b, hb, rfl⟩ := (hmemI j).mp hj
        exact Finset.mem_sdiff.mpr ⟨hIP b hb, hIB b hb⟩
      have h2 : (P' \ Bs) \ Is = P' \ (Bs ∪ Is) := by
        ext j; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
      rw [h1, Finset.sum_insert (fun h => hq0 (Finset.mem_sdiff.mp h).1),
        ← Finset.sum_sdiff hsub, h2, hcrossB i hiB, zero_add, hsumI, hq0B i hiB, sim_add_self]
    · rw [if_neg hiB]
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · -- the `q₀` row: the total of `C` plus `Σ_B s`
        rw [Finset.sum_congr rfl hrecq0, Finset.sum_add_distrib, hsB, add_zero,
          Finset.sum_congr rfl hq0B, hCsum]
      · by_cases hiI : i ∈ Is
        · -- an `I` row: a column sum of `C`
          obtain ⟨b, hb, rfl⟩ := (hmemI i).mp hiI
          have : ∀ j ∈ Bs, L j (pI b) = (if j = b then 1 else 0) + (if j = bd then 1 else 0) :=
            fun j hj => hcol b hb j (hBP hj) (fun h => hIB b hb (h ▸ hj))
          rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq',
            Finset.sum_ite_eq', if_pos (Finset.mem_of_mem_erase hb), if_pos hbd, sim_add_self]
        · -- a `J` row: `β` is a square there
          exact hcrossJ i (Finset.mem_sdiff.mpr ⟨hi', by simp [hiB, hiI]⟩)
  -- `ker K♯ = ⟨1⟩` and the rank-one reduction (S12 585–625)
  have hM := deleted_of_nonsing L P' hq0 (fun i => lsym 3 i) (hBP hbd) hN
  have hker := sharp_ker_of_deleted L (insert q0 P') (fun i => lsym 3 i) q0 bd hM
  obtain ⟨hK, hI⟩ := target_of_sharp_ker L (insert q0 P') (fun i => lsym 3 i)
    (fun j => if j ∈ Bs then 1 else 0) q0 bd
    (hBP' hbd) (by simp [hq0nB]) (by simp [hbd]) hKe hker
  have hq0ℓ : q0 ∈ ℓ.primeFactors := by rw [hℓ]; exact Finset.mem_insert_self _ _
  have hbdℓ : bd ∈ ℓ.primeFactors := by rw [hℓ]; exact hBP' hbd
  rw [← hℓ] at hKe hK hI
  subst hBs
  refine matrixConditions_of hβ0 ⟨bd, hbdℓ, Nat.dvd_of_mem_primeFactors hbd⟩
    ⟨q0, hq0ℓ, fun h => hq0nB
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq0ℓ, h, hβ0⟩)⟩ hKe ?_ hI
  intro v hv
  exact ⟨v q0, v q0 + v bd, hK v hv⟩

/-- **`MatrixRealization`** (`diophantine_zq.tex` lines 1033–1060; S12 Lemma
`par:simultaneous-matrices`, lines 543–703). -/
theorem matrixRealization : MatrixRealization := by
  classical
  intro β θ hβ hθ hβ24 hθ24 hcop hβsq hθsq
  have hβ0 : β ≠ 0 := by omega
  have hθ0 : θ ≠ 0 := by omega
  obtain ⟨Bs, hBs⟩ : ∃ Bs : Finset ℕ, Bs = β.primeFactors := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ, J = θ.primeFactors := ⟨_, rfl⟩
  have hmemB : ∀ q, q ∈ Bs ↔ q.Prime ∧ q ∣ β := fun q => by
    rw [hBs, Nat.mem_primeFactors]; exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hβ0⟩⟩
  have hmemJ : ∀ q, q ∈ J ↔ q.Prime ∧ q ∣ θ := fun q => by
    rw [hJ, Nat.mem_primeFactors]; exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hθ0⟩⟩
  have hBJp : ∀ q ∈ Bs ∪ J, q.Prime ∧ 3 < q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨hqp, hqd⟩ := (hmemB q).mp hq
      refine ⟨hqp, ?_⟩
      by_contra h
      have h2 := hqp.two_le
      interval_cases q <;> omega
    · obtain ⟨hqp, hqd⟩ := (hmemJ q).mp hq
      refine ⟨hqp, ?_⟩
      by_contra h
      have h2 := hqp.two_le
      interval_cases q <;> omega
  have hdisj : Disjoint Bs J := by
    rw [Finset.disjoint_left]
    intro q hqB hqJ
    obtain ⟨hqp, hqβ⟩ := (hmemB q).mp hqB
    have hc : Nat.Coprime q θ := Nat.Coprime.coprime_dvd_left hqβ hcop
    exact hqp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc ((hmemJ q).mp hqJ).2)
  obtain ⟨bd, hbd⟩ : Bs.Nonempty := by rw [hBs]; exact Nat.nonempty_primeFactors.mpr (by omega)
  -- the `I`-slots
  obtain ⟨pI, hpI, hinj, hII⟩ := exists_Iprimes Bs J hBJp hdisj bd (Bs.erase bd)
  obtain ⟨Is, hIs⟩ : ∃ Is : Finset ℕ, Is = (Bs.erase bd).image pI := ⟨_, rfl⟩
  have hmemI : ∀ j, j ∈ Is ↔ ∃ b ∈ Bs.erase bd, pI b = j := fun j => by
    rw [hIs, Finset.mem_image]
  have hpIs : ∀ b ∈ Bs.erase bd, pI b ∈ Is := fun b hb => (hmemI _).mpr ⟨b, hb, rfl⟩
  have hIB : ∀ b ∈ Bs.erase bd, pI b ∉ Bs := fun b hb h =>
    (hpI b hb).2.2.1 (Finset.mem_union_left _ h)
  have hIJ : ∀ b ∈ Bs.erase bd, pI b ∉ J := fun b hb h =>
    (hpI b hb).2.2.1 (Finset.mem_union_right _ h)
  have hdisjBI : Disjoint Bs Is := by
    rw [Finset.disjoint_left]
    intro q hqB hqI
    obtain ⟨b, hb, rfl⟩ := (hmemI q).mp hqI
    exact hIB b hb hqB
  have hdisjIJ : Disjoint Is J := by
    rw [Finset.disjoint_left]
    intro q hqI hqJ
    obtain ⟨b, hb, rfl⟩ := (hmemI q).mp hqI
    exact hIJ b hb hqJ
  have hP01 : Bs ∪ Is ⊆ Bs ∪ Is ∪ J := Finset.subset_union_left
  have hP1p : ∀ q ∈ Bs ∪ Is ∪ J, q.Prime ∧ 3 < q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · rcases Finset.mem_union.mp hq with hq | hq
      · exact hBJp q (Finset.mem_union_left _ hq)
      · obtain ⟨b, hb, rfl⟩ := (hmemI q).mp hq
        have h := hpI b hb
        have := h.1.two_le
        exact ⟨h.1, by have := h.2.1; omega⟩
    · exact hBJp q (Finset.mem_union_right _ hq)
  -- the symbols of the `I`-slots against the whole support (S12 633–635)
  have hLI : ∀ b ∈ Bs.erase bd, ∀ j ∈ Bs ∪ Is ∪ J, j ≠ pI b →
      lsym (pI b : ℤ) j = (if j = b then 1 else 0) + (if j = bd then 1 else 0) := by
    intro b hb j hj hjb
    rcases Finset.mem_union.mp hj with hj | hjJ
    · rcases Finset.mem_union.mp hj with hjB | hjI
      · exact (hpI b hb).2.2.2.1 j hjB
      · obtain ⟨b', hb', rfl⟩ := (hmemI j).mp hjI
        have hbb' : b ≠ b' := fun h => hjb (h ▸ rfl)
        rw [hII b hb b' hb' hbb']
        have h1 : pI b' ≠ b := fun h => hIB b' hb' (by rw [h]; exact Finset.mem_of_mem_erase hb)
        have h2 : pI b' ≠ bd := fun h => hIB b' hb' (by rw [h]; exact hbd)
        rw [if_neg h1, if_neg h2, add_zero]
    · have hjB : j ∉ Bs := fun h => Finset.disjoint_left.mp hdisj h hjJ
      rw [(hpI b hb).2.2.2.2 j hjJ,
        if_neg (fun h : j = b => hjB (by rw [h]; exact Finset.mem_of_mem_erase hb)),
        if_neg (fun h : j = bd => hjB (by rw [h]; exact hbd)), add_zero]
  -- reciprocity: `[q/p_b] = [p_b/q]` since `p_b ≡ 1 (mod 4)` (S12 line 634)
  have hcol1 : ∀ b ∈ Bs.erase bd, ∀ j ∈ Bs ∪ Is ∪ J, j ≠ pI b →
      L j (pI b) = (if j = b then 1 else 0) + (if j = bd then 1 else 0) := by
    intro b hb j hj hjb
    have hp := (hpI b hb).1
    have hjp := (hP1p j hj).1
    have := Fact.mk hp
    have := Fact.mk hjp
    have hj3 := (hP1p j hj).2
    have hb12 := (hpI b hb).2.1
    simp only [L]
    rw [lsym_recip j (pI b) (by rcases hjp.eq_two_or_odd with h | h <;> omega) (by omega) hjb,
      lsym_neg_one_of_mod12_one hp hb12, mul_zero, add_zero]
    exact hLI b hb j hj hjb
  have hrow : ∀ b ∈ Bs.erase bd, ∀ j ∈ Bs,
      L (pI b) j = (if j = b then 1 else 0) + (if j = bd then 1 else 0) :=
    fun b hb j hj => (hpI b hb).2.2.2.1 j hj
  have hlamI : ∀ b ∈ Bs.erase bd, lsym 3 (pI b) = 0 := fun b hb =>
    lsym_three_of_mod12_one (hpI b hb).1 (hpI b hb).2.1
  have hlam : ∑ i ∈ Bs, lsym 3 i = 1 := by
    rw [hBs, sum_lam_primeFactors β hβ (by omega) (by omega), if_pos (by omega), if_neg (by omega),
      add_zero]
  have hsB : ∑ j ∈ Bs, lsym (-1) j = 0 := by
    rw [hBs, sum_sgn_primeFactors β hβ (by omega), if_neg (by omega)]
  -- the cross-symbol sums (S12 `(par:cross-symbol-sums)`)
  have hcrossB : ∀ i ∈ Bs, ∑ j ∈ J, L j i = 0 := by
    intro i hi
    obtain ⟨hip, hiβ⟩ := (hmemB i).mp hi
    have := Fact.mk hip
    have hiθ : ¬ i ∣ θ := fun h => Finset.disjoint_left.mp hdisj hi ((hmemJ i).mpr ⟨hip, h⟩)
    simp only [L]
    rw [hJ, sum_lsym_primeFactors i hθ hiθ]
    exact lsym_natCast_of_isSquare (hθsq i hip hiβ)
  have hcrossJ : ∀ i ∈ J, ∑ j ∈ Bs, L j i = 0 := by
    intro i hi
    obtain ⟨hip, hiθ⟩ := (hmemJ i).mp hi
    have := Fact.mk hip
    have hiβ : ¬ i ∣ β := fun h => Finset.disjoint_left.mp hdisj ((hmemB i).mpr ⟨hip, h⟩) hi
    simp only [L]
    rw [hBs, sum_lsym_primeFactors i hβ hiβ]
    exact lsym_natCast_of_isSquare (hβsq i hip hiθ)
  have hsd1 : (Bs ∪ Is ∪ J) \ (Bs ∪ Is) = J := by
    ext j; simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact absurd h h'
      · exact h
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (h' | h')
      · exact Finset.disjoint_left.mp hdisj h' h
      · exact Finset.disjoint_left.mp hdisjIJ h' h
  have hsd0 : (Bs ∪ Is) \ (Bs ∪ Is) = ∅ := Finset.sdiff_self _
  -- the fixed `q₀`-symbols `y₀` (S12 lines 636–639) and the block on `B ∪ I` inside `B ∪ I ∪ J`
  obtain ⟨y0, hy0⟩ : ∃ y0 : ℕ → ZMod 2,
      y0 = fun j => if j ∈ Bs then ∑ b ∈ Bs.erase bd, L (pI b) j else 0 := ⟨_, rfl⟩
  have hblock : NonsingOn (dOp L (Bs ∪ Is ∪ J) y0 (fun i => lsym 3 i) bd) (Bs ∪ Is) :=
    block_nonsing L (Bs ∪ Is ∪ J) Bs bd bd pI y0 (fun i => lsym 3 i) Is hIs
      (Finset.subset_union_left.trans Finset.subset_union_left) hbd hbd
      (fun b hb => Finset.mem_union_left _ (Finset.mem_union_right _ (hpIs b hb)))
      hIB hinj hcol1 hrow (fun b hb => by simp [hy0, hIB b hb]) hlamI
      (fun i hi => by simp [hy0, hi])
      (fun i hi => by rw [hsd1]; exact hcrossB i hi) hlam
  -- the toggles on the `J`-diagonal (S12 677–688)
  obtain ⟨t, ht, hnt⟩ := toggle (dOp L (Bs ∪ Is ∪ J) y0 (fun i => lsym 3 i) bd)
    (dOp_add L _ y0 _ bd) hblock J (Finset.disjoint_left.mpr fun q hq hqJ => by
      rcases Finset.mem_union.mp hq with h | h
      · exact Finset.disjoint_left.mp hdisj h hqJ
      · exact Finset.disjoint_left.mp hdisjIJ h hqJ)
  -- `q₀`, last (S12 692–703)
  obtain ⟨q0, hq0, hq012, hq0Q⟩ := exists_prime_lsym (Bs ∪ Is ∪ J) hP1p (r := 7) (by norm_num)
    (fun j => y0 j + t j)
  have hq012' : q0 % 12 = 7 := by simpa using hq012
  have hq0P1 : q0 ∉ Bs ∪ Is ∪ J := fun h => (hq0Q q0 h).1 dvd_rfl
  have hq0P0 : q0 ∉ Bs ∪ Is := fun h => hq0P1 (hP01 h)
  have hLq0 : ∀ j ∈ Bs ∪ Is ∪ J, L q0 j = y0 j + t j := fun j hj => (hq0Q j hj).2
  have hq0B : ∀ i ∈ Bs, L q0 i = ∑ b ∈ Bs.erase bd, L (pI b) i := by
    intro i hi
    have hiJ : i ∉ J := fun h => Finset.disjoint_left.mp hdisj hi h
    rw [hLq0 i (Finset.mem_union_left _ (Finset.mem_union_left _ hi)), ht i hiJ, add_zero, hy0]
    simp [hi]
  have hrecq0 : ∀ j ∈ Bs, L j q0 = L q0 j + lsym (-1) j := by
    intro j hj
    have hjp := ((hmemB j).mp hj).1
    have := Fact.mk hjp
    have := Fact.mk hq0
    have hj3 := (hBJp j (Finset.mem_union_left _ hj)).2
    simp only [L]
    rw [lsym_recip j q0 (by rcases hjp.eq_two_or_odd with h | h <;> omega) (by omega)
      (fun h => hq0P1 (h ▸ Finset.mem_union_left _ (Finset.mem_union_left _ hj))),
      lsym_neg_one_of_mod12_seven hq0 hq012', mul_one]
  -- the parameter `n = β ∏ p_b q₀`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ∏ p ∈ insert q0 (Bs ∪ Is), p := ⟨_, rfl⟩
  have hP0p : ∀ p ∈ insert q0 (Bs ∪ Is), p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hq0
    · exact (hP1p p (hP01 hp)).1
  have hθprod : θ = ∏ p ∈ J, p := by rw [hJ]; exact (Nat.prod_primeFactors_of_squarefree hθ).symm
  have hβprod : β = ∏ p ∈ Bs, p := by rw [hBs]; exact (Nat.prod_primeFactors_of_squarefree hβ).symm
  have hdisj0J : Disjoint (insert q0 (Bs ∪ Is)) J := by
    rw [Finset.disjoint_left]
    intro q hq hqJ
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hq0P1 (Finset.mem_union_right _ hqJ)
    · rcases Finset.mem_union.mp hq with h | h
      · exact Finset.disjoint_left.mp hdisj h hqJ
      · exact Finset.disjoint_left.mp hdisjIJ h hqJ
  have hnθ : n * θ = ∏ p ∈ insert q0 (Bs ∪ Is ∪ J), p := by
    rw [hn, hθprod, ← Finset.prod_union hdisj0J, Finset.insert_union]
  have hP1pr : ∀ p ∈ insert q0 (Bs ∪ Is ∪ J), p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hq0
    · exact (hP1p p hp).1
  have hnf : n.primeFactors = insert q0 (Bs ∪ Is) := by rw [hn]; exact Nat.primeFactors_prod hP0p
  have hnθf : (n * θ).primeFactors = insert q0 (Bs ∪ Is ∪ J) := by
    rw [hnθ]; exact Nat.primeFactors_prod hP1pr
  -- the deleted matrices are nonsingular on both supports
  have hN0 : NonsingOn (dOp L (Bs ∪ Is) (fun j => L q0 j) (fun i => lsym 3 i) bd) (Bs ∪ Is) :=
    block_nonsing L (Bs ∪ Is) Bs bd bd pI (fun j => L q0 j) (fun i => lsym 3 i) Is hIs
      Finset.subset_union_left hbd hbd (fun b hb => Finset.mem_union_right _ (hpIs b hb))
      hIB hinj (fun b hb j hj hjb => hcol1 b hb j (hP01 hj) hjb) hrow
      (fun b hb => by
        rw [hLq0 _ (hP01 (Finset.mem_union_right _ (hpIs b hb))), ht _ (hIJ b hb), hy0]
        simp [hIB b hb])
      hlamI hq0B (fun i _ => by rw [hsd0, Finset.sum_empty]) hlam
  have hN1 : NonsingOn (dOp L (Bs ∪ Is ∪ J) (fun j => L q0 j) (fun i => lsym 3 i) bd)
      (Bs ∪ Is ∪ J) := by
    refine hnt.congr fun v i hi => ?_
    simp only [dOp]
    rw [hLq0 i hi]; ring
  refine ⟨n, by rw [hn]; exact Finset.prod_pos fun p hp => (hP0p p hp).pos, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnθ]; exact squarefree_prod_primes _ hP1pr
  · -- `n ≡ 11 (mod 12)`: `7 · 5 · 1 ≡ 11`
    have h12 : (n : ZMod 12) = 11 := by
      have hI1 : ∀ p ∈ Is, (p : ZMod 12) = 1 := by
        intro p hp
        obtain ⟨b, hb, rfl⟩ := (hmemI p).mp hp
        have := (hpI b hb).2.1
        rw [← ZMod.natCast_mod, this]; rfl
      rw [hn, Finset.prod_insert hq0P0, Finset.prod_union hdisjBI, ← hβprod]
      push_cast
      rw [Finset.prod_congr rfl hI1, Finset.prod_const_one, mul_one, ← ZMod.natCast_mod q0,
        hq012', ← ZMod.natCast_mod β, show β % 12 = 5 by omega]
      rfl
    have := (ZMod.natCast_eq_natCast_iff' n 11 12).mp (by rw [h12]; rfl)
    simpa using this
  · rw [hn, hβprod]
    exact Finset.prod_dvd_prod_of_subset _ _ _
      (Finset.subset_union_left.trans (Finset.subset_insert _ _))
  · exact matrixConditions_of_slots hβ0 Bs hBs bd hbd pI Is hIs (Bs ∪ Is) q0
      Finset.subset_union_left (fun b hb => Finset.mem_union_right _ (hpIs b hb)) hIB hinj
      hq0P0 hnf hN0 (fun b hb j hj hjb => hcol1 b hb j (hP01 hj) hjb) hrow
      (fun i _ => by rw [hsd0, Finset.sum_empty])
      (fun i hi => by rw [hsd0] at hi; exact absurd hi (Finset.notMem_empty _)) hq0B hrecq0 hsB
  · exact matrixConditions_of_slots hβ0 Bs hBs bd hbd pI Is hIs (Bs ∪ Is ∪ J) q0
      (Finset.subset_union_left.trans Finset.subset_union_left)
      (fun b hb => Finset.mem_union_left _ (Finset.mem_union_right _ (hpIs b hb)))
      hIB hinj hq0P1 hnθf hN1 hcol1 hrow
      (fun i hi => by rw [hsd1]; exact hcrossB i hi)
      (fun i hi => by rw [hsd1] at hi; exact hcrossJ i hi) hq0B hrecq0 hsB

/-- **The simultaneous construction from the dimension-three count.** -/
theorem simultaneousConstruction_of_dimThree (hD : DimThreeCount) : SimultaneousConstruction :=
  simultaneousConstruction_of matrixRealization hD

end ZInQ.Manuscript.PoleRC.Simul
