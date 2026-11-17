import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.DivisionsMain

/-!
# Lane RC12-odd: (O.9) and (O.11) as statements; the fresh reading; the omission coefficient

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-coefficient-rules`:
* (O.9) (tex 9570–9584) — `O9`;
* (O.11) (tex 9618–9636) — `O11_cong`, `O11_offJ`, `O11_theta`;
* the fresh coefficient-one reading `B_U[q] = 2^{−n_U} a(uq)`, `H_U[q] = 2^{−n_U−1} a(uq)`
  (tex 9681–9687) — `TL_fresh`, `theta_index_ne_fresh`;
* the omission coefficient `H_U[pr] ≡ η(p) C_p(vr) 2^{−n_V−1} a(vr)`, an equality before reduction
  for the even source (tex 9905–9918) — `TL_omission`.
All statements are PROVED.
-/

namespace ZInQ.Manuscript.RC.Odd

variable {R : Type*} [CommRing R]

/-- `∏_{p∈U}(U_p − η(p)V_p)` applied to `a`, for a list `U` of primes (by `Top_comm` the result
depends only on the set when the primes are distinct). -/
def TL (χ : ℕ → R) : List ℕ → (ℕ → R) → (ℕ → R)
  | [], a => a
  | p :: L, a => Top p (χ p) (TL χ L a)

@[simp] theorem TL_nil (χ : ℕ → R) (a : ℕ → R) : TL χ [] a = a := rfl
@[simp] theorem TL_cons (χ : ℕ → R) (p : ℕ) (L : List ℕ) (a : ℕ → R) :
    TL χ (p :: L) a = Top p (χ p) (TL χ L a) := rfl

variable {T δ : ℕ} {χ : ℕ → R} {G : ℕ → Prop} {ap : ℕ → ℤ} {a : ℕ → R}

/-- The base: one good prime (tex 9562–9566, 9598–9599). -/
theorem SourceHyp.single (H : SourceHyp T δ χ G ap a) {q : ℕ} (hq : G q) {n : ℕ} (hn : n ≠ 0)
    (hqn : q ∉ oddPart n) (t : ℕ) :
    (2 : R) ^ (min T (δ + (oddPart n).card + 1)) ∣ a (n * (q ^ t) ^ 2) - χ q ^ t * a n := by
  obtain ⟨ε, hε, hrec⟩ := H.recur q hq
  have : Fact q.Prime := ⟨H.prime q hq⟩
  obtain ⟨k, n'', hqn'', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q (H.prime q hq).ne_one
  have hn'' : n'' ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [oddPart_pow_even_mul (H.prime q hq) hn'' hqn'']
    have hidx : q ^ (2 * s) * n'' * (q ^ t) ^ 2 = q ^ (2 * (s + t)) * n'' := by ring
    rw [hidx, rec_even hrec hqn'' (s + t), rec_even hrec hqn'' s]
    have hκ := legendreSym_neg_eq_one_or hqn'' hε
    have ho1 := odd_shell_kappa_unit hκ (H.odd q hq) (H.ap_mod q hq) (s + t)
    have ho2 := odd_shell_kappa_unit hκ (H.odd q hq) (H.ap_mod q hq) s
    set κ := ε * legendreSym q (-(n'' : ℤ))
    have hev : Even (shell (ap q) q κ (s + t) - shell (ap q) q κ s) := Odd.sub_odd ho1 ho2
    have hexp : χ q ^ (s + t) * (shell (ap q) q κ (s + t) : R) * a n'' -
        χ q ^ t * (χ q ^ s * (shell (ap q) q κ s : R) * a n'') =
        χ q ^ (s + t) * (((shell (ap q) q κ (s + t) - shell (ap q) q κ s : ℤ) : R) * a n'') := by
      push_cast; ring
    rw [hexp]
    exact dvd_mul_of_dvd_right (two_pow_dvd_of_le (by omega)
      (two_pow_dvd_intCast_even_mul hev (H.depth n''))) _
  · exfalso; apply hqn
    rw [oddPart_pow_odd_mul (H.prime q hq) hn'' hqn'']
    exact Finset.mem_insert_self _ _

/-- **PROVED.** The invariant holds for the source itself (`U = ∅`). -/
theorem SourceHyp.divInv (H : SourceHyp T δ χ G ap a) : DivInv T δ χ G ∅ a := by
  refine ⟨H.zero, fun n => by simpa using H.depth n, ?_⟩
  intro n m hn hm hgood hcop
  simp only [Finset.sdiff_empty, Finset.card_empty, add_zero]
  simp only [Finset.sdiff_empty] at hcop
  have key : ∀ m, m ≠ 0 → (∀ q ∈ m.primeFactors, G q) → ∀ n, n ≠ 0 →
      (∀ q ∈ oddPart n, ¬ q ∣ m) →
      (2 : R) ^ (min T (δ + (oddPart n).card + 1)) ∣ a (n * m ^ 2) - χ m * a n := by
    intro m
    induction m using Nat.recOnPrimePow with
    | zero => intro h; exact absurd rfl h
    | one => intro _ _ n _ _; simp [H.one]
    | prime_pow_mul m₁ q t hq hqm₁ ht ih =>
      intro hm hgood n hn hcop
      have hm₁ : m₁ ≠ 0 := by rintro rfl; simp at hm
      have hqG : G q := hgood q (by
        rw [Nat.primeFactors_mul (pow_ne_zero _ hq.ne_zero) hm₁, Nat.primeFactors_prime_pow
          (by omega) hq]
        simp)
      have hqn : q ∉ oddPart n := fun h' =>
        hcop q h' (dvd_mul_of_dvd_left (dvd_pow_self q (by omega)) _)
      have hidx : n * (q ^ t * m₁) ^ 2 = (n * (q ^ t) ^ 2) * m₁ ^ 2 := by ring
      have hnq : n * (q ^ t) ^ 2 ≠ 0 := mul_ne_zero hn (pow_ne_zero _ (pow_ne_zero _ hq.ne_zero))
      have h1 := ih hm₁ (fun r hr => hgood r (by
        rw [Nat.primeFactors_mul (pow_ne_zero _ hq.ne_zero) hm₁]
        exact Finset.mem_union_right _ hr)) (n * (q ^ t) ^ 2) hnq (by
        intro r hr hrm
        rw [oddPart_mul_sq hn (pow_ne_zero _ hq.ne_zero)] at hr
        exact hcop r hr (dvd_mul_of_dvd_right hrm _))
      rw [oddPart_mul_sq hn (pow_ne_zero _ hq.ne_zero)] at h1
      have h2 := H.single hqG hn hqn t
      rw [hidx, H.mul, H.pow]
      have : a (n * (q ^ t) ^ 2 * m₁ ^ 2) - χ q ^ t * χ m₁ * a n =
          (a (n * (q ^ t) ^ 2 * m₁ ^ 2) - χ m₁ * a (n * (q ^ t) ^ 2)) +
          χ m₁ * (a (n * (q ^ t) ^ 2) - χ q ^ t * a n) := by ring
      rw [this]
      exact dvd_add h1 (dvd_mul_of_dvd_right h2 _)
  exact key m hm hgood n hn hcop

/-- **PROVED.** The invariant after `∏_{p∈U}(U_p − η(p)V_p)` for a list `U` of distinct good
primes, together with the twisted recurrence at every other good prime. -/
theorem SourceHyp.divInv_TL (H : SourceHyp T δ χ G ap a) (L : List ℕ) (hnd : L.Nodup)
    (hL : ∀ p ∈ L, G p) :
    DivInv T δ χ G L.toFinset (TL χ L a) ∧
      ∀ q (hq : G q), q ∉ L → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        @RecAt R _ q ⟨H.prime q hq⟩ (χ q) ε (ap q) (TL χ L a) := by
  induction L with
  | nil => exact ⟨by simpa using H.divInv, fun q hq _ => by simpa using H.recur q hq⟩
  | cons p L ih =>
    have hpL : p ∉ L := (List.nodup_cons.mp hnd).1
    obtain ⟨hinv, hrecs⟩ := ih (List.nodup_cons.mp hnd).2 (fun q hq => hL q (by simp [hq]))
    have hpG : G p := hL p (by simp)
    have : Fact p.Prime := ⟨H.prime p hpG⟩
    obtain ⟨ε, hε, hrec⟩ := hrecs p hpG hpL
    refine ⟨?_, ?_⟩
    · rw [List.toFinset_cons, TL_cons]
      exact hinv.step (by simpa using hpL) (H.odd p hpG) hε (H.ap_mod p hpG) hrec H.mul H.one
    · intro q hq hqpL
      have hqL : q ∉ L := fun h' => hqpL (by simp [h'])
      have hqp : p ≠ q := fun e => hqpL (by simp [e])
      obtain ⟨εq, hεq, hrecq⟩ := hrecs q hq hqL
      have : Fact q.Prime := ⟨H.prime q hq⟩
      refine ⟨εq * legendreSym q p, ?_, ?_⟩
      · have hpq : ¬ q ∣ p := fun h' =>
          hqp ((Nat.prime_dvd_prime_iff_eq (H.prime q hq) (H.prime p hpG)).mp h').symm
        have := legendreSym_neg_eq_one_or (n := p) hpq hεq
        have hneg : legendreSym q (-(p : ℤ)) = legendreSym q (-1) * legendreSym q p := by
          rw [← legendreSym.mul]; ring_nf
        have h0 : ((p : ℤ) : ZMod q) ≠ 0 := by
          intro h0; apply hpq
          exact Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h0)
        rcases legendreSym.eq_one_or_neg_one q h0 with h | h <;> rcases hεq with rfl | rfl <;>
          simp [h]
      · rw [TL_cons]; exact hrecq.top hqp (χ p)

/-- **(O.9) (tex 9570–9584), PROVED.** For a list `U` of distinct good primes, at every Fourier
index `n`: `2^{min T (δ + |U| + ω(r))} ∣ (∏_{p∈U}(U_p − η(p)V_p) g)[n]`, where
`ω(r) = #(oddPart n ∖ U)` counts the primes of the squarefree kernel `J r` of `n` outside `U`
(so `v₂ B_U[Jrm²] ≥ ω(r)` with `n_U = δ + |U|`, truncated at `T` for an odd stage). -/
theorem O9 (H : SourceHyp T δ χ G ap a) (L : List ℕ) (hnd : L.Nodup) (hL : ∀ p ∈ L, G p)
    (n : ℕ) : (2 : R) ^ (min T (δ + L.length + (oddPart n \ L.toFinset).card)) ∣ TL χ L a n := by
  have := (H.divInv_TL L hnd hL).1.bound n
  rwa [List.toFinset_card_of_nodup hnd] at this

/-- **(O.11), the shell congruence (tex 9626–9627), PROVED.** In matching parity, for `n = J m₁²`
with `J ⊆ U` (i.e. `oddPart n ⊆ U`) and every good `m`:
`B_U[n m²] − η(m) B_U[n] ∈ 2𝒪`, undivided: `2^{min T (n_U + 1)}` divides the difference. -/
theorem O11_cong (H : SourceHyp T δ χ G ap a) (L : List ℕ) (hnd : L.Nodup) (hL : ∀ p ∈ L, G p)
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hJ : oddPart n ⊆ L.toFinset)
    (hgood : ∀ q ∈ m.primeFactors, G q) :
    (2 : R) ^ (min T (δ + L.length + 1)) ∣ TL χ L a (n * m ^ 2) - χ m * TL χ L a n := by
  have hsd : oddPart n \ L.toFinset = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hJ
  have := (H.divInv_TL L hnd hL).1.cong n m hn hm hgood (by simp [hsd])
  rwa [hsd, Finset.card_empty, add_zero, List.toFinset_card_of_nodup hnd] at this

/-- **(O.11), off the unary support (tex 9628–9632), PROVED.** If the squarefree kernel of `n` is
not contained in `U`, then `ω(r) ≥ 1` and `2^{min T (n_U + 1)} ∣ (∏(U_p − η(p)V_p) g)[n]`. -/
theorem O11_offJ (H : SourceHyp T δ χ G ap a) (L : List ℕ) (hnd : L.Nodup) (hL : ∀ p ∈ L, G p)
    {n : ℕ} (hJ : ¬ oddPart n ⊆ L.toFinset) :
    (2 : R) ^ (min T (δ + L.length + 1)) ∣ TL χ L a n := by
  have hpos : 0 < (oddPart n \ L.toFinset).card := by
    rw [Finset.card_pos]
    obtain ⟨q, hq, hqL⟩ := Finset.not_subset.mp hJ
    exact ⟨q, Finset.mem_sdiff.mpr ⟨hq, hqL⟩⟩
  exact two_pow_dvd_of_le (by omega) (O9 H L hnd hL n)

/-- **(O.11), integrality of `H_U = (B_U − ∑_J B_U[J] Θ_J)/2` (tex 9618–9632), PROVED.** For the
unary series `Θ_J = ∑ η(m) χ_{−4}(m)^i m q^{J m²}`, whose coefficient `θ(m)` at `J m²` is an odd
integer times `η(m)`: at every index `J m²` (`J ⊆ U`, `m` good) the undivided numerator of `H_U` is
divisible by `2^{min T (n_U + 1)}`. -/
theorem O11_theta (H : SourceHyp T δ χ G ap a) (L : List ℕ) (hnd : L.Nodup)
    (hL : ∀ p ∈ L, G p) (θ : ℕ → ℤ) (hθ : ∀ m, Odd m → Odd (θ m))
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hmodd : Odd m) (hJ : oddPart n ⊆ L.toFinset)
    (hgood : ∀ q ∈ m.primeFactors, G q) :
    (2 : R) ^ (min T (δ + L.length + 1)) ∣
      TL χ L a (n * m ^ 2) - TL χ L a n * (χ m * (θ m : R)) := by
  have h1 := O11_cong H L hnd hL hn hm hJ hgood
  have h2 := O9 H L hnd hL n
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hJ, Finset.card_empty, add_zero] at h2
  have hev : Even (1 - θ m) := Odd.sub_odd odd_one (hθ m hmodd)
  have : TL χ L a (n * m ^ 2) - TL χ L a n * (χ m * (θ m : R)) =
      (TL χ L a (n * m ^ 2) - χ m * TL χ L a n) +
        ((1 - θ m : ℤ) : R) * (χ m * TL χ L a n) := by push_cast; ring
  rw [this]
  exact dvd_add h1 (two_pow_dvd_of_le (by omega)
    (two_pow_dvd_intCast_even_mul hev (dvd_mul_of_dvd_right h2 _)))

/-- **The fresh reading (tex 9681–9686), PROVED.** For an index `n` prime to every `p ∈ U`:
`(∏_{p∈U}(U_p − η(p)V_p) g)[n] = a(u n)`, `u = ∏_{p∈U} p` (every term containing a `V_p` vanishes);
so `B_U[q] = 2^{−n_U} a(uq)` at a fresh prime `q`. -/
theorem TL_fresh (χ : ℕ → R) (a : ℕ → R) (L : List ℕ) (hL : ∀ p ∈ L, p.Prime) (hnd : L.Nodup)
    {n : ℕ} (hn : ∀ p ∈ L, ¬ p ∣ n) : TL χ L a n = a (L.prod * n) := by
  induction L generalizing n with
  | nil => simp
  | cons p L ih =>
    have hp : p.Prime := hL p (by simp)
    rw [TL_cons, Top_of_not_dvd _ (hn p (by simp)), ih (fun q hq => hL q (by simp [hq]))
      (List.nodup_cons.mp hnd).2]
    · rw [List.prod_cons]; ring_nf
    · intro q hq hqd
      have hqp : q ≠ p := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hq)
      rcases (Nat.Prime.dvd_mul (hL q (by simp [hq]))).mp hqd with h | h
      · exact hqp ((Nat.prime_dvd_prime_iff_eq (hL q (by simp [hq])) hp).mp h)
      · exact hn q (by simp [hq]) h

/-- **PROVED (tex 9682–9683).** No unary index `J m²` with `J ⊆ U` equals a fresh prime `q ∉ U`:
`oddPart (J m²) ⊆ U` fails at `q`. -/
theorem theta_index_ne_fresh {q : ℕ} (hq : q.Prime) {U : Finset ℕ} (hqU : q ∉ U) :
    ¬ oddPart q ⊆ U := by
  intro h
  apply hqU
  apply h
  rw [mem_oddPart, hq.factorization_self]
  exact odd_one

/-- **The omission coefficient (tex 9905–9916), PROVED.** For `U = {p} ∪ V` (`p` applied last),
a fresh prime `r` (prime to `p` and to `V`): the coefficient at `pr` is
`(∏_{U}(U_p − η(p)V_p) g)[pr] = η(p) (a_p − (ψ/η)(p)(−vr/p) − 1) a(vr) = η(p)·2C_p(vr)·a(vr)`,
an equality before reduction; dividing by `2^{n_U + 1} = 2^{n_V + 2}` gives
`H_U[pr] = η(p) C_p(vr) 2^{−n_V−1} a(vr)`. -/
theorem TL_omission (χ : ℕ → R) (a : ℕ → R) {p : ℕ} [hp : Fact p.Prime] {ε app : ℤ}
    (hrec : RecAt p (χ p) ε app a) (V : List ℕ) (hV : ∀ q ∈ V, q.Prime) (hnd : V.Nodup)
    (hpV : p ∉ V) {r : ℕ} (hpr : ¬ p ∣ r) (hVr : ∀ q ∈ V, ¬ q ∣ r) :
    TL χ (p :: V) a (p * r) =
      χ p * ((app - ε * legendreSym p (-((V.prod * r : ℕ) : ℤ)) - 1 : ℤ) : R) * a (V.prod * r) := by
  have hp0 : 0 < p := hp.out.pos
  have hcopV : ∀ q ∈ V, ¬ q ∣ p := fun q hq h' =>
    hpV (((Nat.prime_dvd_prime_iff_eq (hV q hq) hp.out).mp h') ▸ hq)
  have hpVr : ¬ p ∣ V.prod * r := by
    intro h'
    rcases (Nat.Prime.dvd_mul hp.out).mp h' with h1 | h1
    · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_prod_iff hp.out.prime).mp h1
      exact hcopV q hq (by rw [(Nat.prime_dvd_prime_iff_eq hp.out (hV q hq)).mp hpq])
    · exact hpr h1
  rw [TL_cons]
  simp only [Top]
  rw [divCoeff_mul_left _ hp0]
  rw [TL_fresh χ a V hV hnd hVr, TL_fresh χ a V hV hnd (by
    intro q hq hqd
    rcases (Nat.Prime.dvd_mul (hV q hq)).mp hqd with h1 | h1
    · exact hcopV q hq h1
    · rcases (Nat.Prime.dvd_mul (hV q hq)).mp h1 with h2 | h2
      · exact hcopV q hq h2
      · exact hVr q hq h2)]
  rw [show V.prod * (p * (p * r)) = p ^ 2 * (V.prod * r) by ring, hrec (V.prod * r),
    divCoeff_of_not_dvd a (not_sq_dvd_of_not_dvd hpVr)]
  push_cast; ring

end ZInQ.Manuscript.RC.Odd
