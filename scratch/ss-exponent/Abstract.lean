import Mathlib

/-! Test file for the abstract group lemma (merged into SSExponent.lean once it compiles). -/

namespace ZInQ.Contrib.SSExponent

section Abstract

variable {G : Type*} [AddCommGroup G]

theorem iterate_nsmul (f : G →+ G) (k c : ℕ) (x : G) : f^[k] (c • x) = c • f^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_nsmul, ih]

theorem iterate_zero (f : G →+ G) (k : ℕ) : f^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_zero, ih]

/-- `ker f^[n]` as an additive subgroup. -/
def kerIt (f : G →+ G) (n : ℕ) : AddSubgroup G where
  carrier := {x | f^[n] x = 0}
  zero_mem' := iterate_zero f n
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [show f^[n] (a + b) = f^[n] a + f^[n] b from iterate_map_add f n a b, ha, hb, add_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [show f^[n] (-a) = -f^[n] a from iterate_map_neg f n a, ha, neg_zero]

theorem mem_kerIt (f : G →+ G) (n : ℕ) (x : G) : x ∈ kerIt f n ↔ f^[n] x = 0 := Iff.rfl

theorem kerIt_mono (f : G →+ G) (n : ℕ) : kerIt f n ≤ kerIt f (n + 1) := by
  intro x hx
  rw [mem_kerIt] at *
  rw [Function.iterate_succ_apply', hx, map_zero]

theorem kerIt_stab (f : G →+ G) {n : ℕ} (h : kerIt f n = kerIt f (n + 1)) (r : ℕ) :
    kerIt f (n + r) = kerIt f (n + r + 1) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    apply le_antisymm (kerIt_mono f _)
    intro x hx
    rw [mem_kerIt, show n + (r + 1) + 1 = (n + r + 1) + 1 by omega, Function.iterate_succ_apply]
      at hx
    have : f x ∈ kerIt f (n + r) := by rw [ih]; exact hx
    rw [mem_kerIt, show n + (r + 1) = (n + r) + 1 by omega, Function.iterate_succ_apply]
    exact this

/-- **Abstract supersingular exponent.** A finite abelian group `G` with an involution `π` and an
automorphism `i` with `i² = −1`, `π i = −i π`, all of whose `π`-fixed subgroups have order dividing
`N = 2^v m` (`m` odd), is killed by `N`. -/
theorem nsmul_eq_zero_of_frob [Finite G] (π i : G →+ G) (v m : ℕ) (hm : Odd m)
    (hππ : ∀ Q, π (π Q) = Q) (hii : ∀ Q, i (i Q) = -Q) (hπi : ∀ Q, π (i Q) = -(i (π Q)))
    (hA : ∀ S : AddSubgroup G, (∀ Q ∈ S, π Q = Q) → Nat.card S ∣ 2 ^ v * m) :
    ∀ P : G, (2 ^ v * m) • P = 0 := by
  set N := 2 ^ v * m with hN
  have hinj : Function.Injective i := by
    intro a b hab
    have := congrArg i hab
    rw [hii, hii] at this
    exact neg_injective this
  -- fixed points are killed by `N`
  have hfix : ∀ Q, π Q = Q → N • Q = 0 := by
    intro Q hQ
    have h1 := hA (AddSubgroup.zmultiples Q) (by
      intro R hR
      obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR
      simp [map_zsmul, hQ])
    rw [Nat.card_zmultiples] at h1
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp h1
  -- the weak exponent `2N`
  have hweak : ∀ P : G, (2 * N) • P = 0 := by
    intro P
    have h1 : N • (P + π P) = 0 := by
      apply hfix
      rw [map_add, hππ, add_comm]
    have h2 : N • (P - π P) = 0 := by
      have hQ2 : N • i (P - π P) = 0 := by
        apply hfix
        rw [hπi, map_sub, hππ, ← neg_sub, map_neg, neg_neg]
      rw [← map_nsmul] at hQ2
      exact hinj (hQ2.trans (map_zero i).symm)
    calc (2 * N) • P = N • (P + π P) + N • (P - π P) := by
          rw [mul_comm, mul_nsmul', ← nsmul_add]; congr 1; abel
      _ = 0 := by rw [h1, h2, add_zero]
  -- `j = 1 + i`, `j² = 2 i`
  set j : G →+ G := AddMonoidHom.id G + i with hj
  have hjj : ∀ Q : G, j (j Q) = 2 • i Q := by
    intro Q
    simp only [hj, AddMonoidHom.add_apply, AddMonoidHom.id_apply, map_add, hii]
    rw [two_nsmul]; abel
  have hj2 : ∀ (n : ℕ) (Q : G), j^[2 * n] Q = 2 ^ n • i^[n] Q := by
    intro n
    induction n with
    | zero => intro Q; simp
    | succ n ih =>
      intro Q
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, Function.iterate_add_apply,
        show j^[2] Q = j (j Q) from rfl, hjj, iterate_nsmul, ih, Function.iterate_succ_apply,
        smul_smul, pow_succ']
  have hinjv : ∀ n, Function.Injective i^[n] := fun n => hinj.iterate n
  have hK : ∀ (n : ℕ) (x : G), x ∈ kerIt j (2 * n) ↔ 2 ^ n • x = 0 := by
    intro n x
    rw [mem_kerIt, hj2, ← iterate_nsmul]
    constructor
    · intro h; exact hinjv n (by rw [h, iterate_zero])
    · intro h; rw [h, iterate_zero]
  -- the `2^{v+1}`-torsion has order `≤ 2^{2v}`
  set M := kerIt j (2 * (v + 1)) with hMdef
  let MA : AddSubgroup G :=
    { carrier := {x | 2 ^ (v + 1) • x = 0 ∧ π x = x}
      zero_mem' := by simp
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by rw [nsmul_add, ha1, hb1, add_zero], by rw [map_add, ha2, hb2]⟩
      neg_mem' := by
        rintro a ⟨ha1, ha2⟩
        exact ⟨by rw [smul_neg, ha1, neg_zero], by rw [map_neg, ha2]⟩ }
  let MB : AddSubgroup G :=
    { carrier := {x | 2 ^ (v + 1) • x = 0 ∧ π x = -x}
      zero_mem' := by simp
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by rw [nsmul_add, ha1, hb1, add_zero], by rw [map_add, ha2, hb2, neg_add]⟩
      neg_mem' := by
        rintro a ⟨ha1, ha2⟩
        exact ⟨by rw [smul_neg, ha1, neg_zero], by rw [map_neg, ha2]⟩ }
  have hMA : Nat.card MA ∣ 2 ^ v := by
    have h1 : Nat.card MA ∣ 2 ^ v * m := hA MA (fun Q hQ => hQ.2)
    have hcop : Nat.Coprime (Nat.card MA) m := by
      apply Nat.coprime_of_dvd
      intro q hq hqA hqm
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hqA
      have h2 : 2 ^ (v + 1) • x = 0 := Subtype.ext x.2.1
      have h3 : q ∣ 2 ^ (v + 1) := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero h2
      have h4 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h3)
      subst h4
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hqm)
    exact hcop.dvd_of_dvd_mul_right h1
  have hMB : Nat.card MB ≤ Nat.card MA := by
    refine Nat.card_le_card_of_injective (fun x => ⟨i x.1, ?_, ?_⟩) ?_
    · rw [← map_nsmul, x.2.1, map_zero]
    · rw [hπi, x.2.2, map_neg, neg_neg]
    · intro a b hab
      exact Subtype.ext (hinj (congrArg Subtype.val hab))
  have hM : Nat.card M ≤ 2 ^ (2 * v) := by
    let f : M →+ G := (AddMonoidHom.id G - π).comp M.subtype
    have hrange : f.range ≤ MB := by
      rintro _ ⟨x, rfl⟩
      have hx : 2 ^ (v + 1) • (x : G) = 0 := (hK (v + 1) x).mp x.2
      refine ⟨?_, ?_⟩
      · simp only [f, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
          AddSubgroup.coe_subtype]
        rw [nsmul_sub, hx, ← map_nsmul, hx, map_zero, sub_zero]
      · simp only [f, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
          AddSubgroup.coe_subtype]
        rw [map_sub, hππ, neg_sub]
    have hker : Nat.card f.ker ≤ Nat.card MA := by
      refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, ?_, ?_⟩) ?_
      · exact (hK (v + 1) x.1.1).mp x.1.2
      · have := x.2
        rw [AddMonoidHom.mem_ker] at this
        simp only [f, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
          AddSubgroup.coe_subtype] at this
        exact (sub_eq_zero.mp this).symm
      · intro a b hab
        have h := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h)
    have h1 := AddSubgroup.card_ker_mul_card_range f
    have h2 : Nat.card f.range ≤ Nat.card MB := AddSubgroup.card_le_of_le hrange
    have hMA' : Nat.card MA ≤ 2 ^ v := Nat.le_of_dvd (by positivity) hMA
    calc Nat.card M = Nat.card f.ker * Nat.card f.range := h1.symm
      _ ≤ 2 ^ v * 2 ^ v := Nat.mul_le_mul (hker.trans hMA') (h2.trans (hMB.trans hMA'))
      _ = 2 ^ (2 * v) := by rw [← pow_add, two_mul]
  -- the chain `ker j^n` stabilizes by `n = 2v`
  have key : kerIt j (2 * v) = M := by
    by_contra hne
    have hlt : ∀ n, n ≤ 2 * v → kerIt j n < kerIt j (n + 1) := by
      intro n hn
      refine lt_of_le_of_ne (kerIt_mono j n) (fun h => hne ?_)
      have e1 := kerIt_stab j h (2 * v - n)
      have e2 := kerIt_stab j h (2 * v - n + 1)
      rw [show n + (2 * v - n) = 2 * v by omega] at e1
      rw [show n + (2 * v - n + 1) = 2 * v + 1 by omega] at e2
      rw [hMdef, show 2 * (v + 1) = 2 * v + 1 + 1 by ring, ← e2, e1]
    have hcard : ∀ n, n ≤ 2 * v + 1 → 2 ^ n ≤ Nat.card (kerIt j n) := by
      intro n
      induction n with
      | zero => intro _; rw [pow_zero]; exact Nat.card_pos
      | succ n ih =>
        intro hn
        have h1 := hlt n (by omega)
        have h2 := AddSubgroup.card_dvd_of_le h1.le
        have h3 := AddSubgroup.card_lt_of_lt h1
        obtain ⟨c, hc⟩ := h2
        have hc2 : 2 ≤ c := by
          have h4 : Nat.card (kerIt j n) * 1 < Nat.card (kerIt j n) * c := by
            rw [mul_one, ← hc]; exact h3
          exact Nat.lt_of_mul_lt_mul_left h4
        rw [pow_succ, hc]
        exact Nat.mul_le_mul (ih (by omega)) hc2
    have h1 := hcard (2 * v + 1) le_rfl
    have h2 : Nat.card (kerIt j (2 * v + 1)) ≤ Nat.card M := by
      apply AddSubgroup.card_le_of_le
      rw [hMdef, show 2 * (v + 1) = 2 * v + 1 + 1 by ring]
      exact kerIt_mono j _
    have h3 : 2 ^ (2 * v) < 2 ^ (2 * v + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  intro P
  have h1 : 2 ^ (v + 1) • (m • P) = 0 := by
    rw [smul_smul, pow_succ, mul_comm (2 ^ v) 2, mul_assoc, ← hN]; exact hweak P
  have h2 : m • P ∈ kerIt j (2 * v) := by rw [key, hMdef, hK]; exact h1
  rw [hK] at h2
  rw [hN, ← smul_smul]
  exact h2

end Abstract

end ZInQ.Contrib.SSExponent
