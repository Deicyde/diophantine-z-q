import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_prime_pow

/-! # flt-cqj: cyclic subgroups of order `N` of `(ℤ/N)²` (counting glue)

`#{a ∈ (ℤ/N)² | ord a = N} = ψ(N) φ(N)` and hence a finite abelian group `G ≅ (ℤ/N)²` has exactly `ψ(N)`
cyclic subgroups of order `N` (`ψ` = FLT's `ModularCurve.dedekindPsi`). -/

open Finset

namespace FltCqj

/-- In `ℤ/n`, the elements of order dividing `d ∣ n` number `d`. -/
theorem card_addOrderOf_dvd_zmod (n d : ℕ) [NeZero n] (hd : d ∣ n) :
    #{x : ZMod n | addOrderOf x ∣ d} = d := by
  classical
  have hd0 : d ≠ 0 := fun h => NeZero.ne n (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have hsplit : #{x : ZMod n | addOrderOf x ∣ d} =
      ∑ e ∈ d.divisors, #{x : ZMod n | addOrderOf x = e} := by
    rw [card_eq_sum_card_fiberwise (f := fun x => addOrderOf x) (t := d.divisors)]
    · refine sum_congr rfl fun e he => ?_
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro h; exact ⟨h ▸ (Nat.mem_divisors.mp he).1, h⟩
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
      exact Nat.mem_divisors.mpr ⟨hx, hd0⟩
  rw [hsplit]
  have hcard : Fintype.card (ZMod n) = n := ZMod.card n
  calc ∑ e ∈ d.divisors, #{x : ZMod n | addOrderOf x = e}
      = ∑ e ∈ d.divisors, Nat.totient e := by
        refine sum_congr rfl fun e he => ?_
        exact IsAddCyclic.card_addOrderOf_eq_totient
          (by rw [hcard]; exact Nat.dvd_trans (Nat.mem_divisors.mp he).1 hd)
    _ = d := Nat.sum_totient d

/-- In `(ℤ/n)²`, the elements of order dividing `d ∣ n` number `d²`. -/
theorem card_addOrderOf_dvd_sq (n d : ℕ) [NeZero n] (hd : d ∣ n) :
    #{a : ZMod n × ZMod n | addOrderOf a ∣ d} = d * d := by
  classical
  have : ({a : ZMod n × ZMod n | addOrderOf a ∣ d} : Finset _) =
      ({x : ZMod n | addOrderOf x ∣ d} : Finset _) ×ˢ ({x : ZMod n | addOrderOf x ∣ d} : Finset _) := by
    ext ⟨x, y⟩
    simp [Prod.addOrderOf_mk, Nat.lcm_dvd_iff]
  rw [this, card_product, card_addOrderOf_dvd_zmod n d hd]

/-- `J(N) = #{a ∈ (ℤ/N)² | ord a = N}`. -/
noncomputable def J (N : ℕ) : ℕ := Nat.card {a : ZMod N × ZMod N // addOrderOf a = N}

theorem J_eq_card (N : ℕ) [NeZero N] : J N = #{a : ZMod N × ZMod N | addOrderOf a = N} := by
  classical
  rw [J, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- `J(p^k) = p^{2k} - p^{2(k-1)}`, in the form `J(p^k) + (p^{k-1})² = (p^k)²`. -/
theorem J_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    J (p ^ k) + p ^ (k - 1) * p ^ (k - 1) = p ^ k * p ^ k := by
  classical
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [J_eq_card, ← card_addOrderOf_dvd_sq (p ^ k) (p ^ (k - 1)) (pow_dvd_pow p (Nat.sub_le k 1))]
  have htot : #(univ : Finset (ZMod (p ^ k) × ZMod (p ^ k))) = p ^ k * p ^ k := by
    rw [card_univ, Fintype.card_prod, ZMod.card]
  rw [← htot, ← card_union_of_disjoint]
  · congr 1
    ext a
    simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
    have hdvd : addOrderOf a ∣ p ^ k := by
      refine addOrderOf_dvd_of_nsmul_eq_zero (Prod.ext ?_ ?_)
      · rw [Prod.smul_fst, Prod.fst_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      · rw [Prod.smul_snd, Prod.snd_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rcases Nat.lt_or_ge j k with h | h
    · right; rw [hj']; exact pow_dvd_pow p (by omega)
    · left; rw [hj', le_antisymm hj h]
  · rw [disjoint_filter]
    intro a _ h1 h2
    rw [h1, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h2
    omega

/-- Orders of elements of `(ℤ/n)²` divide `n`. -/
theorem addOrderOf_dvd_sq (n : ℕ) (a : ZMod n × ZMod n) : addOrderOf a ∣ n := by
  refine addOrderOf_dvd_of_nsmul_eq_zero (Prod.ext ?_ ?_)
  · rw [Prod.smul_fst, Prod.fst_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · rw [Prod.smul_snd, Prod.snd_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- For `x ∣ m`, `y ∣ n` with `m, n` coprime and positive: `lcm x y = m n ↔ x = m ∧ y = n`. -/
theorem lcm_eq_mul_iff {m n x y : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) (hx : x ∣ m)
    (hy : y ∣ n) : x.lcm y = m * n ↔ x = m ∧ y = n := by
  constructor
  · intro hl
    have hc : x.Coprime y := (h.coprime_dvd_left hx).coprime_dvd_right hy
    rw [hc.lcm_eq_mul] at hl
    have hxm := Nat.le_of_dvd hm hx
    have hyn := Nat.le_of_dvd hn hy
    have hx0 : 0 < x := Nat.pos_of_dvd_of_pos hx hm
    have hy0 : 0 < y := Nat.pos_of_dvd_of_pos hy hn
    constructor
    · by_contra hne
      have : x * y < m * n := Nat.mul_lt_mul_of_lt_of_le (lt_of_le_of_ne hxm hne) hyn hn
      omega
    · by_contra hne
      have : x * y < m * n := Nat.mul_lt_mul_of_le_of_lt hxm (lt_of_le_of_ne hyn hne) hm
      omega
  · rintro ⟨rfl, rfl⟩
    exact h.lcm_eq_mul

/-- `J` is multiplicative (Chinese remainder theorem). -/
theorem J_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) : J (m * n) = J m * J n := by
  let c : ZMod (m * n) ≃+ ZMod m × ZMod n := (ZMod.chineseRemainder h).toAddEquiv
  let e : ZMod (m * n) × ZMod (m * n) ≃+ (ZMod m × ZMod m) × (ZMod n × ZMod n) :=
    (c.prodCongr c).trans (AddEquiv.prodProdProdComm _ _ _ _)
  have h1 : J (m * n) =
      Nat.card {b : (ZMod m × ZMod m) × (ZMod n × ZMod n) // addOrderOf b = m * n} :=
    Nat.card_congr (e.toEquiv.subtypeEquiv fun a => by
      simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, AddEquiv.addOrderOf_eq])
  have h2 : Nat.card {b : (ZMod m × ZMod m) × (ZMod n × ZMod n) // addOrderOf b = m * n} =
      Nat.card ({x : ZMod m × ZMod m // addOrderOf x = m} × {y : ZMod n × ZMod n // addOrderOf y = n}) :=
    Nat.card_congr ((Equiv.subtypeEquivRight fun b => by
      rw [Prod.addOrderOf]
      exact lcm_eq_mul_iff hm hn h (addOrderOf_dvd_sq m b.1) (addOrderOf_dvd_sq n b.2)).trans
      Equiv.subtypeProdEquivProd)
  rw [h1, h2, Nat.card_prod, J, J]

/-- `J(N) = ψ(N) φ(N)` for `N > 0`. -/
theorem J_eq (N : ℕ) (hN : 0 < N) : J N = ModularCurve.dedekindPsi N * N.totient := by
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    have hp' : p.Prime := hp
    have hJ := J_prime_pow p k hp' hk
    rw [ModularCurve.dedekindPsi_prime_pow p k hp' hk.ne', Nat.totient_prime_pow hp' hk]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hJ ⊢
    rw [pow_succ] at hJ ⊢
    have hp1 : 1 ≤ p := hp'.one_lt.le
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith [hJ]
  | zero => omega
  | one => simp [J, ModularCurve.dedekindPsi_one]
  | coprime a b ha hb hab iha ihb =>
    rw [J_mul a b (by omega) (by omega) hab, iha (by omega), ihb (by omega),
      ModularCurve.dedekindPsi_mul_of_coprime a b hab, Nat.totient_mul hab]
    ring

/-- Two elements with the same finite order, one in the cyclic subgroup of the other, generate the
same subgroup. -/
theorem zmultiples_eq_of_mem {G : Type*} [AddGroup G] [Finite G] {a b : G}
    (hb : b ∈ AddSubgroup.zmultiples a) (h : addOrderOf b = addOrderOf a) :
    AddSubgroup.zmultiples b = AddSubgroup.zmultiples a :=
  AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr hb)
    (by rw [Nat.card_zmultiples, Nat.card_zmultiples, h])

/-- **Cyclic subgroups of order `N` versus elements of order `N`**: in a finite abelian group,
`#{cyclic H of order N} · φ(N) = #{a | ord a = N}`. -/
theorem ncard_cyclic_mul_totient {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (N : ℕ) :
    {H : AddSubgroup G | IsAddCyclic H ∧ Nat.card H = N}.ncard * N.totient =
      #{a : G | addOrderOf a = N} := by
  classical
  set A : Finset G := univ.filter fun a : G => addOrderOf a = N with hA
  have himg : {H : AddSubgroup G | IsAddCyclic H ∧ Nat.card H = N} =
      ↑(A.image AddSubgroup.zmultiples) := by
    ext H
    simp only [Set.mem_ofPred_eq, coe_image, Set.mem_image, hA, coe_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hc, hcard⟩
      obtain ⟨g, hg⟩ := hc.exists_generator
      have hog : addOrderOf (g : G) = N := by
        rw [AddSubgroup.addOrderOf_coe, addOrderOf_eq_card_of_forall_mem_zmultiples hg, hcard]
      refine ⟨g, hog, AddSubgroup.eq_of_le_of_card_ge
        (AddSubgroup.zmultiples_le.mpr g.2) ?_⟩
      rw [Nat.card_zmultiples, hog, hcard]
    · rintro ⟨a, ha, rfl⟩
      exact ⟨inferInstance, by rw [Nat.card_zmultiples, ha]⟩
  rw [himg, Set.ncard_coe_finset, card_eq_sum_card_image AddSubgroup.zmultiples A]
  rw [sum_const_nat (m := N.totient)]
  intro H hH
  obtain ⟨a0, ha0, rfl⟩ := mem_image.mp hH
  have ha0' : addOrderOf a0 = N := (mem_filter.mp ha0).2
  have hcardH : Fintype.card (AddSubgroup.zmultiples a0) = N := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zmultiples, ha0']
  have htot : #{x : AddSubgroup.zmultiples a0 | addOrderOf x = N} = N.totient :=
    IsAddCyclic.card_addOrderOf_eq_totient (by rw [hcardH])
  rw [← htot, ← card_map ⟨Subtype.val, Subtype.val_injective⟩]
  congr 1
  ext y
  simp only [mem_filter, hA, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hy, hz⟩
    refine ⟨⟨y, hz ▸ AddSubgroup.mem_zmultiples y⟩, ?_, rfl⟩
    rw [← AddSubgroup.addOrderOf_coe]; exact hy
  · rintro ⟨x, hx, rfl⟩
    have hx' : addOrderOf (x : G) = N := by rw [AddSubgroup.addOrderOf_coe]; exact hx
    exact ⟨hx', zmultiples_eq_of_mem x.2 (hx'.trans ha0'.symm)⟩

/-- **`(ℤ/N)²` has `ψ(N)` cyclic subgroups of order `N`.** -/
theorem ncard_cyclic_sq (N : ℕ) [NeZero N] :
    {H : AddSubgroup (ZMod N × ZMod N) | IsAddCyclic H ∧ Nat.card H = N}.ncard =
      ModularCurve.dedekindPsi N := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h := ncard_cyclic_mul_totient (G := ZMod N × ZMod N) N
  rw [← J_eq_card, J_eq N hN] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr hN) h

end FltCqj
