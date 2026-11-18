import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Types
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Basic

/-!
# Lane RC24: Frobenius data over `G_ℚ = Aut(ℚ̄/ℚ)`

Manuscript `diophantine_zq.tex`, Appendix F: Chebotarev and continuity (tex 9666–9668), the
elementary quadratic quotient (tex 9745–9750), and the reading of an added vertex (tex 9936–9942:
"`χ(gφ) = χ(g)χ(φ) = χ(Fr_q)χ(Fr_p)`. For a fixed-support character this is the product of the
two vertex labels. For the character of a third vertex `r ∈ V`, it adds the two bits `(r/q)` and
`(r/p)` in `𝔽₂`"); Definition `ex:sec7-typed-graph` (tex 2015–2041: the type of a prime records
its values under the fixed quadratic characters and its unit squareclasses; the residue bits
`z_vw` read `(p_v/p_w)`).

This file supplies the genuine Galois-theoretic data behind these readings.

* `Zbar`: the algebraic integers `ℤ̄ ⊂ ℚ̄`, with the restriction action of `G_ℚ`.
* `IsFrobAt σ q`: `σ ∈ G_ℚ` is an arithmetic Frobenius element at a maximal ideal of `ℤ̄` above
  `q` (Mathlib's `IsArithFrobAt`). `frobeniusExists` (PROVED): Frobenius elements exist at every
  prime, from Mathlib's surjectivity of the decomposition group of a profinite group onto the
  automorphism group of the residue extension, applied to the Frobenius `x ↦ x^q` of `ℤ̄/Q`.
* `sqrtChar d`: the quadratic character of `ℚ(√d)`. A Frobenius element at an odd prime `q ∤ d`
  reads the Legendre symbol `(d/q)` (`sqrtChar_of_isFrobAt`, Euler's criterion); the vertex
  character of `ℚ(√s^*)` reads the residue bit `(q/s)` (`bitChar_of_isFrobAt`, reciprocity).
* `cycChar m`: the mod-`m` cyclotomic character (Mathlib's `modularCyclotomicCharacter`); a
  Frobenius element at `q ∤ m` acts on `μ_m` by `q` (`cycChar_of_isFrobAt`).
* `typChar m`: the type character `G_ℚ → (ℤ/m)ˣ/squares`; a Frobenius element at `q` reads the
  type of `q` (`typChar_of_isFrobAt`).
* Products (tex 9936–9942): at `gφ`, with `g`, `φ` Frobenius elements at `q`, `p`, the characters
  add the two bits, respectively the two types (`sqrtChar_mul_of_isFrobAt`,
  `bitChar_mul_of_isFrobAt`, `typChar_mul_of_isFrobAt`, `cycChar_mul_of_isFrobAt`).
* Further facts: `sqrtChar` is multiplicative in `d` and trivial on squares (`sqrtChar_mul`,
  `sqrtChar_sq`, `sqrtChar_mul_sq`, `sqrtChar_zero`); conjugates of Frobenius elements are
  Frobenius elements (`IsFrobAt.conj`); a Frobenius element at `q` reads the sign coordinate
  `ε_q` and the splitting character of `K = ℚ(√k)` through the type of `q`
  (`signChar_typChar_of_isFrobAt`, `sqrtChar_eq_kChar_of_isFrobAt`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.PrintsArith

/-! ### The algebraic integers and the Galois action -/

/-- The ring `ℤ̄` of algebraic integers of `ℚ̄` (definition; the Frobenius elements `Fr_q` of
tex 9936–9942 are defined through the primes of `ℤ̄`). -/
abbrev Zbar : Type := integralClosure ℤ Qbar

/-- `G_ℚ` acts on `ℤ̄` by restriction (definition: Mathlib's action of a group on an integral
closure, `σ • x = σ x`; an automorphism maps algebraic integers to algebraic integers). -/
instance instMulSemiringActionZbar : MulSemiringAction GalQ Zbar := inferInstance

/-- The action of `G_ℚ` on `ℤ̄` is `ℤ`-linear (PROVED, GLUE). -/
instance instSMulCommClassZbar : SMulCommClass GalQ ℤ Zbar := inferInstance

/-- The action on `ℤ̄` is the restriction of the action on `ℚ̄` (PROVED, GLUE). -/
theorem coe_smul_Zbar (σ : GalQ) (x : Zbar) : ((σ • x : Zbar) : Qbar) = σ (x : Qbar) := rfl

/-- **`σ ∈ G_ℚ` is an arithmetic Frobenius element at the rational prime `q`**: there is a maximal
ideal `Q` of `ℤ̄` above `q` with `σ x ≡ x^{|ℤ/(Q ∩ ℤ)|} = x^q (mod Q)` for every `x ∈ ℤ̄` (Mathlib's
`IsArithFrobAt`; definition, the element `Fr_q` of tex 9936–9942). -/
def IsFrobAt (σ : GalQ) (q : ℕ) : Prop :=
  ∃ Q : Ideal Zbar, Q.IsMaximal ∧ ((q : ℤ) : Zbar) ∈ Q ∧ IsArithFrobAt ℤ σ Q

/-- **Existence of Frobenius elements in `G_ℚ`** at every rational prime (definition of the
proposition; PROVED below as `frobeniusExists`, from the surjectivity of the decomposition group
of a prime of `ℤ̄` onto the automorphism group of its residue field extension, Mathlib's
`Ideal.Quotient.stabilizerHom_surjective_of_profinite`). -/
def FrobeniusExists : Prop := ∀ q : ℕ, q.Prime → ∃ σ : GalQ, IsFrobAt σ q

/-- A maximal ideal of `ℤ̄` containing the prime `q` lies over `qℤ` (PROVED, GLUE). -/
theorem under_eq_span_of_isMaximal {Q : Ideal Zbar} (hQ : Q.IsMaximal) {q : ℕ} (hq : q.Prime)
    (hqQ : ((q : ℤ) : Zbar) ∈ Q) : Q.under ℤ = Ideal.span {(q : ℤ)} := by
  have := Fact.mk hq
  refine ((Int.ideal_span_isMaximal_of_prime q).eq_of_le (Ideal.comap_ne_top _ hQ.ne_top)
    ?_).symm
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, eq_intCast]
  exact hqQ

/-- The residue ring of `ℤ` under such a `Q` has `q` elements (PROVED, GLUE). -/
theorem card_quot_under_of_isMaximal {Q : Ideal Zbar} (hQ : Q.IsMaximal) {q : ℕ} (hq : q.Prime)
    (hqQ : ((q : ℤ) : Zbar) ∈ Q) : Nat.card (ℤ ⧸ Q.under ℤ) = q := by
  rw [under_eq_span_of_isMaximal hQ hq hqQ,
    Nat.card_congr (Int.quotientSpanNatEquivZMod q).toEquiv, Nat.card_zmod]

/-- An integer lies in such a `Q` iff `q` divides it (PROVED, GLUE). -/
theorem intCast_mem_iff_of_isMaximal {Q : Ideal Zbar} (hQ : Q.IsMaximal) {q : ℕ} (hq : q.Prime)
    (hqQ : ((q : ℤ) : Zbar) ∈ Q) (a : ℤ) : ((a : ℤ) : Zbar) ∈ Q ↔ (q : ℤ) ∣ a := by
  have h := under_eq_span_of_isMaximal hQ hq hqQ
  rw [← Ideal.mem_span_singleton, ← h, Ideal.under_def, Ideal.mem_comap, eq_intCast]

/-- **The Frobenius congruence** `σ x ≡ x^q (mod Q)` (PROVED, GLUE: `|ℤ/(Q ∩ ℤ)| = q`). -/
theorem IsFrobAt.exists_congr {σ : GalQ} {q : ℕ} (hq : q.Prime) (hσ : IsFrobAt σ q) :
    ∃ Q : Ideal Zbar, Q.IsMaximal ∧ ((q : ℤ) : Zbar) ∈ Q ∧ ∀ x : Zbar, σ • x - x ^ q ∈ Q := by
  obtain ⟨Q, hQ, hqQ, hF⟩ := hσ
  refine ⟨Q, hQ, hqQ, fun x => ?_⟩
  have := hF x
  rwa [card_quot_under_of_isMaximal hQ hq hqQ] at this

/-! ### Quadratic characters -/

/-- A chosen square root of `d` in `ℚ̄` (definition; `ℚ̄` is algebraically closed). -/
def sqrtQbar (d : ℤ) : Qbar := (IsAlgClosed.exists_pow_nat_eq (d : Qbar) (n := 2) two_pos).choose

/-- `(√d)² = d` (PROVED). -/
theorem sqrtQbar_sq (d : ℤ) : sqrtQbar d ^ 2 = (d : Qbar) :=
  (IsAlgClosed.exists_pow_nat_eq (d : Qbar) (n := 2) two_pos).choose_spec

/-- `σ(√d) = ±√d` (PROVED, GLUE). -/
theorem galQ_sqrtQbar (σ : GalQ) (d : ℤ) :
    σ (sqrtQbar d) = sqrtQbar d ∨ σ (sqrtQbar d) = -sqrtQbar d := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, sqrtQbar_sq, map_intCast]

/-- In characteristic zero, `-x ≠ x` for `x ≠ 0` (PROVED, GLUE). -/
theorem neg_ne_self_Qbar {x : Qbar} (hx : x ≠ 0) : -x ≠ x := by
  intro h
  apply hx
  have h2 : (2 : Qbar) * x = 0 := by
    rw [two_mul]; nth_rewrite 1 [← h]; exact neg_add_cancel x
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- `√d ≠ 0` for `d ≠ 0` (PROVED, GLUE). -/
theorem sqrtQbar_ne_zero {d : ℤ} (hd : d ≠ 0) : sqrtQbar d ≠ 0 := by
  intro h
  have h2 := sqrtQbar_sq d
  rw [h, zero_pow two_ne_zero] at h2
  exact hd (Int.cast_eq_zero.mp h2.symm)

/-- **The character of `ℚ(√d)`**: `σ ↦ 0` if `σ` fixes `√d` and `1` otherwise (written
multiplicatively; definition, the quadratic characters `χ` of tex 9936–9942). It is a
homomorphism because `σ(√d) = ±√d`. -/
def sqrtChar (d : ℤ) : GalQ →* Multiplicative (ZMod 2) where
  toFun σ := if σ (sqrtQbar d) = sqrtQbar d then 1 else Multiplicative.ofAdd 1
  map_one' := ite_eq_left rfl
  map_mul' σ τ := by
    simp only [AlgEquiv.mul_apply]
    by_cases hτ : τ (sqrtQbar d) = sqrtQbar d
    · simp only [hτ, ↓reduceIte, mul_one]
    · have hτ' : τ (sqrtQbar d) = -sqrtQbar d := (galQ_sqrtQbar τ d).resolve_left hτ
      have hs0 : sqrtQbar d ≠ 0 := fun h => hτ (by rw [hτ', h, neg_zero])
      by_cases hσ : σ (sqrtQbar d) = sqrtQbar d
      · simp only [hτ', map_neg, hσ, neg_ne_self_Qbar hs0, ↓reduceIte, one_mul]
      · have hσ' : σ (sqrtQbar d) = -sqrtQbar d := (galQ_sqrtQbar σ d).resolve_left hσ
        simp only [hτ', map_neg, hσ', neg_neg, neg_ne_self_Qbar hs0, ↓reduceIte]
        rfl

/-- The defining formula of `sqrtChar` (PROVED, GLUE). -/
theorem sqrtChar_apply (d : ℤ) (σ : GalQ) :
    sqrtChar d σ = if σ (sqrtQbar d) = sqrtQbar d then 1 else Multiplicative.ofAdd 1 := rfl

/-- `χ_d(σ) = 0` iff `σ` fixes `√d` (PROVED; the hypothesis `d ≠ 0` is not needed for this
definition, both sides hold for `d = 0`). -/
theorem sqrtChar_eq_one_iff (d : ℤ) (hd : d ≠ 0) (σ : GalQ) :
    sqrtChar d σ = 1 ↔ σ (sqrtQbar d) = sqrtQbar d := by
  have _ := hd
  rw [sqrtChar_apply]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

/-- `√d` is an algebraic integer (PROVED, GLUE). -/
theorem isIntegral_sqrtQbar (d : ℤ) : IsIntegral ℤ (sqrtQbar d) := by
  refine IsIntegral.of_pow (n := 2) two_pos ?_
  rw [sqrtQbar_sq]
  simpa using (isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := d))

/-- **Frobenius fixes `√d` iff `d` is a square mod `q`** (PROVED): with `t = √d ∈ ℤ̄` and
`q = 2k + 1`, `σ t ≡ t^q = d^k t ≡ (d/q) t (mod Q)` by Euler's criterion, `σ t = ±t`, and
`2t ∉ Q` because `(2t)² = 4d` and `q ∤ 4d`. -/
theorem galQ_sqrtQbar_eq_iff_of_isFrobAt {σ : GalQ} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {d : ℤ} (hd : ¬ (q : ℤ) ∣ d) (hσ : IsFrobAt σ q) :
    σ (sqrtQbar d) = sqrtQbar d ↔ IsSquare ((d : ℤ) : ZMod q) := by
  have := Fact.mk hq
  obtain ⟨Q, hQ, hqQ, hF⟩ := hσ.exists_congr hq
  have hmem := intCast_mem_iff_of_isMaximal hQ hq hqQ
  set t : Zbar := ⟨sqrtQbar d, isIntegral_sqrtQbar d⟩ with ht
  have ht2 : t ^ 2 = ((d : ℤ) : Zbar) := Subtype.ext (by simp [t, sqrtQbar_sq])
  have hσt : σ • t = t ∨ σ • t = -t := by
    rcases galQ_sqrtQbar σ d with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hfix : σ (sqrtQbar d) = sqrtQbar d ↔ σ • t = t :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  -- `2√d ∉ Q`
  have h2t : t + t ∉ Q := by
    intro h
    have h4 : ((4 * d : ℤ) : Zbar) ∈ Q := by
      have e : (t + t) * (t + t) = ((4 * d : ℤ) : Zbar) := by
        have e' : (t + t) * (t + t) = 4 * t ^ 2 := by ring
        rw [e', ht2]; push_cast; ring
      rw [← e]; exact Q.mul_mem_left _ h
    rw [hmem] at h4
    rcases Int.Prime.dvd_mul' hq h4 with h' | h'
    · have h4' : q ∣ 2 ^ 2 := by exact_mod_cast h'
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h4'))
    · exact hd h'
  have hd0 : ((d : ℤ) : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hodd : q = 2 * (q / 2) + 1 := by
    have := hq.eq_two_or_odd.resolve_left hq2; omega
  have htq : t ^ q = ((d ^ (q / 2) : ℤ) : Zbar) * t := by
    calc t ^ q = t ^ (2 * (q / 2) + 1) := by rw [← hodd]
      _ = (t ^ 2) ^ (q / 2) * t := by rw [pow_succ, pow_mul]
      _ = _ := by rw [ht2]; push_cast; ring
  rw [hfix]
  constructor
  · intro hfixt
    by_contra hsq
    have he : ((d : ZMod q)) ^ (q / 2) = -1 :=
      (ZMod.pow_div_two_eq_neg_one_or_one q hd0).resolve_left
        (fun h => hsq ((ZMod.euler_criterion q hd0).mpr h))
    have hdiv : (q : ℤ) ∣ d ^ (q / 2) + 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [he, neg_add_cancel]
    have h2 : t ^ q + t ∈ Q := by
      rw [htq]
      have e : ((d ^ (q / 2) : ℤ) : Zbar) * t + t = ((d ^ (q / 2) + 1 : ℤ) : Zbar) * t := by
        push_cast; ring
      rw [e]; exact Q.mul_mem_right _ ((hmem _).mpr hdiv)
    have h3 := Q.add_mem (hF t) h2
    have e : σ • t - t ^ q + (t ^ q + t) = σ • t + t := by abel
    rw [e, hfixt] at h3
    exact h2t h3
  · intro hsq
    have he : ((d : ZMod q)) ^ (q / 2) = 1 := (ZMod.euler_criterion q hd0).mp hsq
    have hdiv : (q : ℤ) ∣ d ^ (q / 2) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [he, sub_self]
    have h2 : t ^ q - t ∈ Q := by
      rw [htq]
      have e : ((d ^ (q / 2) : ℤ) : Zbar) * t - t = ((d ^ (q / 2) - 1 : ℤ) : Zbar) * t := by
        push_cast; ring
      rw [e]; exact Q.mul_mem_right _ ((hmem _).mpr hdiv)
    have h3 := Q.add_mem (hF t) h2
    rw [sub_add_sub_cancel] at h3
    rcases hσt with h | h
    · exact h
    · exfalso
      apply h2t
      have e : t + t = -(σ • t - t) := by rw [h]; ring
      rw [e]; exact Q.neg_mem h3

/-- **Frobenius reads the Legendre symbol** (Euler's criterion): if `σ` is a Frobenius element at
an odd prime `q ∤ d`, then `σ(√d) = (d/q) √d` (PROVED; tex 9936–9942, tex 2033–2034). -/
theorem sqrtChar_of_isFrobAt {σ : GalQ} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {d : ℤ}
    (hd : ¬ (q : ℤ) ∣ d) (hσ : IsFrobAt σ q) :
    sqrtChar d σ = Multiplicative.ofAdd (legBit d q) := by
  rw [sqrtChar_apply, legBit]
  by_cases hsq : IsSquare ((d : ℤ) : ZMod q)
  · rw [ite_eq_left ((galQ_sqrtQbar_eq_iff_of_isFrobAt hq hq2 hd hσ).mpr hsq), ite_eq_left hsq]
    rfl
  · rw [ite_eq_right (fun h => hsq ((galQ_sqrtQbar_eq_iff_of_isFrobAt hq hq2 hd hσ).mp h)),
      ite_eq_right hsq]

/-- The signed prime `s^* = (−1)^{(s−1)/2} s` (definition). -/
def sstar (s : ℕ) : ℤ := (-1) ^ (s / 2) * (s : ℤ)

/-- Reciprocity in the form `(s^*/q) = (q/s)` for distinct odd primes (PROVED, quadratic
reciprocity and the first supplement; tex 2037–2041). -/
theorem legBit_sstar {q s : ℕ} (hq : q.Prime) (hs : s.Prime) (hq2 : q ≠ 2) (hs2 : s ≠ 2)
    (hqs : q ≠ s) : legBit (sstar s) q = legBit q s := by
  have := Fact.mk hq
  have := Fact.mk hs
  apply legBit_congr
  have hso : s % 2 = 1 := hs.eq_two_or_odd.resolve_left hs2
  have hqo : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  have hs0 : ((s : ℤ) : ZMod q) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hqs ((Nat.prime_dvd_prime_iff_eq hq hs).mp h)
  rcases (by omega : s % 4 = 1 ∨ s % 4 = 3) with h4 | h4
  · have e : sstar s = s := by
      unfold sstar
      rw [Even.neg_one_pow (⟨s / 4, by omega⟩ : Even (s / 2)), one_mul]
    rw [e, Int.cast_natCast, Int.cast_natCast]
    exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h4 hq2).symm
  · have e : sstar s = -s := by
      unfold sstar
      rw [Odd.neg_one_pow (⟨s / 4, by omega⟩ : Odd (s / 2)), neg_one_mul]
    rw [e]
    have hneg : ((-(s : ℤ) : ℤ) : ZMod q) ≠ 0 := by
      rw [Int.cast_neg, neg_ne_zero]; exact hs0
    have hleg : legendreSym q (-(s : ℤ)) = legendreSym q (-1) * legendreSym q s := by
      rw [← legendreSym.mul, neg_one_mul]
    rw [← legendreSym.eq_one_iff q hneg, hleg, legendreSym.at_neg_one hq2, Int.cast_natCast]
    rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with hq4 | hq4
    · rw [ZMod.χ₄_nat_one_mod_four hq4, one_mul, legendreSym.eq_one_iff q hs0, Int.cast_natCast]
      exact ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hq4 hs2
    · rw [ZMod.χ₄_nat_three_mod_four hq4, neg_one_mul, neg_eq_iff_eq_neg,
        legendreSym.eq_neg_one_iff q, Int.cast_natCast,
        ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hq4 h4 hqs, not_not]

/-- **The bit character `χ_s` reads `(q/s)` at a Frobenius element at `q`** (PROVED;
tex 9938–9942). -/
theorem bitChar_of_isFrobAt {σ : GalQ} {q s : ℕ} (hq : q.Prime) (hs : s.Prime) (hq2 : q ≠ 2)
    (hs2 : s ≠ 2) (hqs : q ≠ s) (hσ : IsFrobAt σ q) :
    sqrtChar (sstar s) σ = Multiplicative.ofAdd (legBit q s) := by
  have hd : ¬ (q : ℤ) ∣ sstar s := by
    intro h
    have h' : (q : ℤ) ∣ (s : ℤ) := by
      unfold sstar at h
      rcases neg_one_pow_eq_or ℤ (s / 2) with e | e
      · rwa [e, one_mul] at h
      · rwa [e, neg_one_mul, dvd_neg] at h
    exact hqs ((Nat.prime_dvd_prime_iff_eq hq hs).mp (Int.natCast_dvd_natCast.mp h'))
  rw [sqrtChar_of_isFrobAt hq hq2 hd hσ, legBit_sstar hq hs hq2 hs2 hqs]

/-! ### The cyclotomic character and the type character -/

/-- `ℚ̄` contains `m` distinct `m`-th roots of unity (PROVED, GLUE). -/
theorem natCard_rootsOfUnity_Qbar (m : ℕ) [NeZero m] : Nat.card (rootsOfUnity m Qbar) = m :=
  HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar m

/-- The mod-`m` cyclotomic character of `G_ℚ` (definition: Mathlib's
`modularCyclotomicCharacter` of `ℚ̄`). -/
def cycChar (m : ℕ) [NeZero m] : GalQ →* (ZMod m)ˣ :=
  (modularCyclotomicCharacter Qbar (natCard_rootsOfUnity_Qbar m)).comp
    (MulSemiringAction.toRingAut GalQ Qbar)

/-- `σ ζ = ζ^{χ(σ)}` for every `m`-th root of unity `ζ` (PROVED). -/
theorem cycChar_spec (m : ℕ) [NeZero m] (σ : GalQ) (ζ : Qbar) (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ ((cycChar m σ : (ZMod m)ˣ) : ZMod m).val := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne m)] at hζ
    exact zero_ne_one hζ
  have hmem : Units.mk0 ζ hζ0 ∈ rootsOfUnity m Qbar := by
    rw [mem_rootsOfUnity]; ext; simp [hζ]
  exact modularCyclotomicCharacter.spec Qbar (natCard_rootsOfUnity_Qbar m)
    (MulSemiringAction.toRingAut GalQ Qbar σ) hmem

/-- **Frobenius acts on `μ_m` by `q`** (PROVED; Mathlib's `IsArithFrobAt.apply_of_pow_eq_one`
at a primitive `m`-th root of unity, `m ∉ Q` since `q ∤ m`). -/
theorem cycChar_of_isFrobAt (m : ℕ) [NeZero m] {σ : GalQ} {q : ℕ} (hq : q.Prime)
    (hqm : Nat.Coprime q m) (hσ : IsFrobAt σ q) :
    ((cycChar m σ : (ZMod m)ˣ) : ZMod m) = (q : ZMod m) := by
  obtain ⟨Q, hQ, hqQ, hF⟩ := hσ
  have hcard := card_quot_under_of_isMaximal hQ hq hqQ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar m
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  set z : Zbar := ⟨ζ, hζ.isIntegral hm0⟩ with hz_def
  have hz : z ^ m = 1 := Subtype.ext (by simp [z, hζ.pow_eq_one])
  have hmQ : ((m : ℕ) : Zbar) ∉ Q := by
    intro h
    have h' : (((m : ℕ) : ℤ) : Zbar) ∈ Q := by exact_mod_cast h
    rw [intCast_mem_iff_of_isMaximal hQ hq hqQ, Int.natCast_dvd_natCast] at h'
    have h'' : q ∣ Nat.gcd q m := Nat.dvd_gcd dvd_rfl h'
    rw [hqm] at h''
    exact hq.one_lt.ne' (Nat.dvd_one.mp h'')
  have h1 := hF.apply_of_pow_eq_one hz hmQ
  rw [hcard] at h1
  have h2 : σ ζ = ζ ^ q := congrArg Subtype.val h1
  have h3 := cycChar_spec m σ ζ hζ.pow_eq_one
  rw [h2] at h3
  set c : ZMod m := ((cycChar m σ : (ZMod m)ˣ) : ZMod m) with hc
  have h4 : ζ ^ (q % m) = ζ ^ c.val := by
    rw [← h3, ← Nat.mod_add_div q m, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one,
      Nat.mod_add_div]
  have h5 : q % m = c.val := hζ.pow_inj (Nat.mod_lt _ hm0) (ZMod.val_lt c) h4
  rw [← ZMod.natCast_zmod_val c, ← h5, ZMod.natCast_mod]

/-- **The type character** `G_ℚ → (ℤ/m)ˣ/squares` (definition: the cyclotomic character followed
by the squareclass map `sqMk`; tex 2015–2025). -/
def typChar (m : ℕ) [NeZero m] : GalQ →* Multiplicative (SqClass m) where
  toFun σ := Multiplicative.ofAdd (sqMk (cycChar m σ))
  map_one' := by
    rw [map_one]
    rfl
  map_mul' σ τ := by
    rw [map_mul]
    rfl

/-- The defining formula of `typChar` (PROVED, GLUE). -/
theorem typChar_apply (m : ℕ) [NeZero m] (σ : GalQ) :
    typChar m σ = Multiplicative.ofAdd (sqMk (cycChar m σ)) := rfl

/-- **Frobenius reads the type** (PROVED; tex 2017–2020, 9936–9940). -/
theorem typChar_of_isFrobAt (m : ℕ) [NeZero m] {σ : GalQ} {q : ℕ} (hq : q.Prime)
    (hqm : Nat.Coprime q m) (hσ : IsFrobAt σ q) :
    typChar m σ = Multiplicative.ofAdd (sqClassOf m q) := by
  have hu : IsUnit (((q : ℤ) : ZMod m)) := by
    rw [Int.cast_natCast]; exact (ZMod.unitOfCoprime q hqm).isUnit
  have hc : cycChar m σ = hu.unit :=
    Units.ext (by rw [IsUnit.unit_spec, cycChar_of_isFrobAt m hq hqm hσ, Int.cast_natCast])
  rw [typChar_apply, hc, sqClassOf, dite_eq_left hu]

/-! ### Existence of Frobenius elements -/

/-- Every rational prime lies under a maximal ideal of `ℤ̄` (PROVED, GLUE: going up for the
integral extension `ℤ ⊂ ℤ̄`). -/
theorem exists_isMaximal_of_prime {q : ℕ} (hq : q.Prime) :
    ∃ Q : Ideal Zbar, Q.IsMaximal ∧ ((q : ℤ) : Zbar) ∈ Q := by
  have := Fact.mk hq
  have hP := Int.ideal_span_isMaximal_of_prime q
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := Zbar)
    (Ideal.span {(q : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker, eq_intCast] at hx
      have hx' : ((x : ℤ) : Qbar) = 0 := by
        have := congrArg Subtype.val hx
        simpa using this
      rw [Int.cast_eq_zero.mp hx']
      exact Ideal.zero_mem _)
  refine ⟨Q, hQ, ?_⟩
  have : (q : ℤ) ∈ Q.under ℤ := by rw [hQP]; exact Ideal.mem_span_singleton_self _
  rwa [Ideal.under_def, Ideal.mem_comap, eq_intCast] at this

/-- The `G_ℚ`-invariants of `ℤ̄` are `ℤ` (PROVED, GLUE: `ℚ̄^{G_ℚ} = ℚ` since `ℚ̄/ℚ` is Galois, and
`ℤ` is integrally closed). -/
instance instIsInvariantZbar : Algebra.IsInvariant ℤ Zbar GalQ where
  isInvariant b hb := by
    have hfix : ∀ σ : GalQ, σ (b : Qbar) = b := fun σ => congrArg Subtype.val (hb σ)
    obtain ⟨r, hr⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (b : Qbar)).mpr hfix
    have hint : IsIntegral ℤ r := by
      have h1 : IsIntegral ℤ (algebraMap ℚ Qbar r) := by rw [hr]; exact b.2
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ Qbar)
        (algebraMap ℚ Qbar).injective).mp h1
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨n, Subtype.ext ?_⟩
    rw [← hr, ← hn]
    simp

/-- **A Frobenius element exists at every maximal ideal `Q` of `ℤ̄` above `q`** (PROVED): the
`q`-power map is an automorphism of `ℤ̄/Q` over `ℤ/qℤ` (injective in characteristic `q`;
surjective since every element of `ℤ̄` has a `q`-th root in `ℤ̄`), and the decomposition group
of `Q` in the profinite group `G_ℚ` surjects onto the automorphisms of `ℤ̄/Q` over `ℤ/qℤ`
(Mathlib's `Ideal.Quotient.stabilizerHom_surjective_of_profinite`, with `ℤ̄` discrete: stabilizers
are open in the Krull topology). -/
theorem exists_isArithFrobAt {Q : Ideal Zbar} (hQ : Q.IsMaximal) {q : ℕ} (hq : q.Prime)
    (hqQ : ((q : ℤ) : Zbar) ∈ Q) : ∃ σ : GalQ, IsArithFrobAt ℤ σ Q := by
  have := Fact.mk hq
  have := hQ.isPrime
  set P : Ideal ℤ := Q.under ℤ with hP
  have : Q.LiesOver P := ⟨rfl⟩
  have : CharP (Zbar ⧸ Q) q := (CharP.charP_iff_prime_eq_zero hq).mpr (by
      rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
      exact_mod_cast hqQ)
  have : ExpChar (Zbar ⧸ Q) q := ExpChar.prime hq
  have hsurj : Function.Surjective (frobenius (Zbar ⧸ Q) q) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (x : Qbar) hq.pos
    have hri : IsIntegral ℤ r := IsIntegral.of_pow hq.pos (by rw [hr]; exact x.2)
    refine ⟨Ideal.Quotient.mk Q ⟨r, hri⟩, ?_⟩
    rw [frobenius_def, ← map_pow]
    congr 1
    exact Subtype.ext (by simp [hr])
  have hbij : Function.Bijective (frobenius (Zbar ⧸ Q) q) := ⟨frobenius_inj _ q, hsurj⟩
  let φ : (Zbar ⧸ Q) ≃ₐ[ℤ ⧸ P] (Zbar ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (frobenius (Zbar ⧸ Q) q) hbij) (fun r => by
        obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective r
        have e : algebraMap (ℤ ⧸ P) (Zbar ⧸ Q) (Ideal.Quotient.mk P n) = (n : Zbar ⧸ Q) :=
          eq_intCast ((algebraMap (ℤ ⧸ P) (Zbar ⧸ Q)).comp (Ideal.Quotient.mk P)) n
        rw [e, RingEquiv.ofBijective_apply, map_intCast])
  let _ : TopologicalSpace Zbar := ⊥
  have : DiscreteTopology Zbar := ⟨rfl⟩
  have : ContinuousSMul GalQ Zbar := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) (x : Qbar) using 1
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := GalQ) P Q φ
  refine ⟨σ, fun x => ?_⟩
  rw [← Ideal.Quotient.eq, card_quot_under_of_isMaximal hQ hq hqQ, map_pow]
  have := DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)
  rw [Ideal.Quotient.stabilizerHom_apply] at this
  exact this

/-- **Frobenius elements exist in `G_ℚ` at every rational prime** (PROVED: `FrobeniusExists`,
from `exists_isMaximal_of_prime` and `exists_isArithFrobAt`). -/
theorem frobeniusExists : FrobeniusExists := by
  intro q hq
  obtain ⟨Q, hQ, hqQ⟩ := exists_isMaximal_of_prime hq
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt hQ hq hqQ
  exact ⟨σ, Q, hQ, hqQ, hσ⟩

/-! ### Further facts on the quadratic characters -/

/-- The character of `d = 0` is trivial (PROVED). -/
theorem sqrtChar_zero : sqrtChar 0 = 1 := by
  ext σ
  have h0 : sqrtQbar 0 = 0 := by
    have h := sqrtQbar_sq 0
    rw [Int.cast_zero] at h
    exact (pow_eq_zero_iff two_ne_zero).mp h
  rw [sqrtChar_apply, h0, map_zero, ite_eq_left rfl, MonoidHom.one_apply]

/-- **The character of a square is trivial** (PROVED): `√(c²) = ±c` is rational. -/
theorem sqrtChar_sq (c : ℤ) : sqrtChar (c ^ 2) = 1 := by
  ext σ
  have h : sqrtQbar (c ^ 2) = (c : Qbar) ∨ sqrtQbar (c ^ 2) = -(c : Qbar) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [sqrtQbar_sq]; push_cast; ring)
  have hfix : σ (sqrtQbar (c ^ 2)) = sqrtQbar (c ^ 2) := by
    rcases h with h | h <;> rw [h] <;> simp only [map_neg, map_intCast]
  rw [sqrtChar_apply, ite_eq_left hfix, MonoidHom.one_apply]

/-- **The quadratic character is multiplicative in `d`** (PROVED): `χ_{ab} = χ_a χ_b` for
`a, b ≠ 0`, since `√(ab) = ±√a √b`. -/
theorem sqrtChar_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sqrtChar (a * b) = sqrtChar a * sqrtChar b := by
  ext σ
  rw [MonoidHom.mul_apply]
  have hu0 := sqrtQbar_ne_zero ha
  have hv0 := sqrtQbar_ne_zero hb
  have huv0 : sqrtQbar a * sqrtQbar b ≠ 0 := mul_ne_zero hu0 hv0
  have hw : sqrtQbar (a * b) = sqrtQbar a * sqrtQbar b ∨
      sqrtQbar (a * b) = -(sqrtQbar a * sqrtQbar b) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by
      rw [sqrtQbar_sq, mul_pow, sqrtQbar_sq, sqrtQbar_sq]; push_cast; ring)
  have key : σ (sqrtQbar (a * b)) = sqrtQbar (a * b) ↔
      σ (sqrtQbar a) * σ (sqrtQbar b) = sqrtQbar a * sqrtQbar b := by
    rcases hw with h | h <;> rw [h] <;> simp only [map_mul, map_neg, neg_inj]
  rw [sqrtChar_apply, sqrtChar_apply, sqrtChar_apply]
  rcases galQ_sqrtQbar σ a with hu | hu <;> rcases galQ_sqrtQbar σ b with hv | hv
  · rw [ite_eq_left (key.mpr (by rw [hu, hv])), ite_eq_left hu, ite_eq_left hv, mul_one]
  · have hne : ¬ σ (sqrtQbar (a * b)) = sqrtQbar (a * b) := by
      rw [key, hu, hv, mul_neg]; exact neg_ne_self_Qbar huv0
    have hv' : ¬ σ (sqrtQbar b) = sqrtQbar b := by rw [hv]; exact neg_ne_self_Qbar hv0
    rw [ite_eq_right hne, ite_eq_left hu, ite_eq_right hv', one_mul]
  · have hne : ¬ σ (sqrtQbar (a * b)) = sqrtQbar (a * b) := by
      rw [key, hu, hv, neg_mul]; exact neg_ne_self_Qbar huv0
    have hu' : ¬ σ (sqrtQbar a) = sqrtQbar a := by rw [hu]; exact neg_ne_self_Qbar hu0
    rw [ite_eq_right hne, ite_eq_right hu', ite_eq_left hv, mul_one]
  · have hfix : σ (sqrtQbar (a * b)) = sqrtQbar (a * b) := by
      rw [key, hu, hv, neg_mul_neg]
    have hu' : ¬ σ (sqrtQbar a) = sqrtQbar a := by rw [hu]; exact neg_ne_self_Qbar hu0
    have hv' : ¬ σ (sqrtQbar b) = sqrtQbar b := by rw [hv]; exact neg_ne_self_Qbar hv0
    rw [ite_eq_left hfix, ite_eq_right hu', ite_eq_right hv']
    rfl

/-- The character only depends on the squareclass of `d` (PROVED). -/
theorem sqrtChar_mul_sq {d c : ℤ} (hd : d ≠ 0) (hc : c ≠ 0) :
    sqrtChar (d * c ^ 2) = sqrtChar d := by
  rw [sqrtChar_mul hd (pow_ne_zero 2 hc), sqrtChar_sq, mul_one]

/-! ### Reading at a product of Frobenius elements (tex 9936–9942) -/

/-- **`χ(gφ) = χ(Fr_q)χ(Fr_p)`** for the character of `ℚ(√d)` (PROVED; tex 9936–9942): at the
product of Frobenius elements at odd primes `q`, `p` not dividing `d`, the character adds the two
bits `(d/q)` and `(d/p)` in `𝔽₂`. -/
theorem sqrtChar_mul_of_isFrobAt {g φ : GalQ} {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hq2 : q ≠ 2) (hp2 : p ≠ 2) {d : ℤ} (hdq : ¬ (q : ℤ) ∣ d) (hdp : ¬ (p : ℤ) ∣ d)
    (hg : IsFrobAt g q) (hφ : IsFrobAt φ p) :
    sqrtChar d (g * φ) = Multiplicative.ofAdd (legBit d q + legBit d p) := by
  rw [map_mul, sqrtChar_of_isFrobAt hq hq2 hdq hg, sqrtChar_of_isFrobAt hp hp2 hdp hφ, ofAdd_add]

/-- **The character of a third vertex `r` at `gφ` adds the two bits** (PROVED; tex 9938–9942):
for Frobenius elements `g` at `q` and `φ` at `p`, the vertex character of `ℚ(√r^*)` takes the
value `(q/r) + (p/r)` in `𝔽₂`. -/
theorem bitChar_mul_of_isFrobAt {g φ : GalQ} {q p r : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hr : r.Prime) (hq2 : q ≠ 2) (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hqr : q ≠ r) (hpr : p ≠ r)
    (hg : IsFrobAt g q) (hφ : IsFrobAt φ p) :
    sqrtChar (sstar r) (g * φ) = Multiplicative.ofAdd (legBit q r + legBit p r) := by
  rw [map_mul, bitChar_of_isFrobAt hq hr hq2 hr2 hqr hg, bitChar_of_isFrobAt hp hr hp2 hr2 hpr hφ,
    ofAdd_add]

/-- **The type character at `gφ` adds the two types** (PROVED; tex 9936–9940: "For a
fixed-support character this is the product of the two vertex labels"). -/
theorem typChar_mul_of_isFrobAt (m : ℕ) [NeZero m] {g φ : GalQ} {q p : ℕ} (hq : q.Prime)
    (hp : p.Prime) (hqm : Nat.Coprime q m) (hpm : Nat.Coprime p m) (hg : IsFrobAt g q)
    (hφ : IsFrobAt φ p) :
    typChar m (g * φ) = Multiplicative.ofAdd (sqClassOf m q + sqClassOf m p) := by
  rw [map_mul, typChar_of_isFrobAt m hq hqm hg, typChar_of_isFrobAt m hp hpm hφ, ofAdd_add]

/-- **The cyclotomic character at `gφ` is `qp`** (PROVED; tex 9936–9940). -/
theorem cycChar_mul_of_isFrobAt (m : ℕ) [NeZero m] {g φ : GalQ} {q p : ℕ} (hq : q.Prime)
    (hp : p.Prime) (hqm : Nat.Coprime q m) (hpm : Nat.Coprime p m) (hg : IsFrobAt g q)
    (hφ : IsFrobAt φ p) :
    ((cycChar m (g * φ) : (ZMod m)ˣ) : ZMod m) = (q : ZMod m) * p := by
  rw [map_mul, Units.val_mul, cycChar_of_isFrobAt m hq hqm hg, cycChar_of_isFrobAt m hp hpm hφ]

/-! ### Conjugation and the readings of the type data -/

open scoped Pointwise in
/-- **Conjugates of a Frobenius element at `q` are Frobenius elements at `q`** (PROVED; Mathlib's
`IsArithFrobAt.conj`: `τστ⁻¹` is a Frobenius element at `τQ`). -/
theorem IsFrobAt.conj {σ : GalQ} {q : ℕ} (hσ : IsFrobAt σ q) (τ : GalQ) :
    IsFrobAt (τ * σ * τ⁻¹) q := by
  obtain ⟨Q, hQ, hqQ, hF⟩ := hσ
  refine ⟨τ • Q, ?_, ?_, hF.conj τ⟩
  · rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _
      (MulSemiringAction.toRingAut GalQ Zbar τ).symm.surjective
  · rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have e : τ⁻¹ • ((q : ℤ) : Zbar) = ((q : ℤ) : Zbar) := Subtype.ext (by
      rw [coe_smul_Zbar]; simp)
    rw [e]
    exact hqQ

/-- **Frobenius reads the sign coordinate** `ε_q = (q − 1)/2 mod 2` of the type (PROVED;
tex 2038–2039, by `signChar_sqClassOf`). -/
theorem signChar_typChar_of_isFrobAt (m : ℕ) [NeZero m] (h4 : 4 ∣ m) {σ : GalQ} {q : ℕ}
    (hq : q.Prime) (hqm : Nat.Coprime q m) (hσ : IsFrobAt σ q) :
    signChar m h4 (Multiplicative.toAdd (typChar m σ)) = ((q / 2 : ℕ) : ZMod 2) := by
  rw [typChar_of_isFrobAt m hq hqm hσ, toAdd_ofAdd, signChar_sqClassOf h4 hq hqm]

/-- Two elements of `𝔽₂` with the same vanishing are equal (PROVED, GLUE). -/
theorem zmod2_eq_of_eq_zero_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  revert a b
  decide

/-- **At Frobenius elements, the character of `K = ℚ(√k)` is read off the type** (PROVED;
tex 2015–2021, 9936–9940: a fixed-support character is a function of the vertex label): for
`4|k| ∣ m` and a Frobenius element `σ` at a prime `q ∤ m`, `χ_k(σ)` is `kChar` of the type of
`σ`. -/
theorem sqrtChar_eq_kChar_of_isFrobAt (m : ℕ) [NeZero m] {k : ℤ} (hk : 4 * k.natAbs ∣ m)
    {σ : GalQ} {q : ℕ} (hq : q.Prime) (hqm : Nat.Coprime q m) (hσ : IsFrobAt σ q) :
    sqrtChar k σ = Multiplicative.ofAdd (kChar m k hk (Multiplicative.toAdd (typChar m σ))) := by
  have := Fact.mk hq
  have h4m : 4 ∣ m := (dvd_mul_right 4 k.natAbs).trans hk
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hqm
      ((show (2 : ℕ) ∣ 4 by norm_num).trans h4m)
  have hdk : ¬ (q : ℤ) ∣ k := by
    intro h
    have h1 : q ∣ k.natAbs := Int.natCast_dvd.mp h
    have h2 : q ∣ m := h1.trans ((dvd_mul_left _ 4).trans hk)
    have h3 : q ∣ Nat.gcd q m := Nat.dvd_gcd dvd_rfl h2
    rw [hqm] at h3
    exact hq.one_lt.ne' (Nat.dvd_one.mp h3)
  rw [sqrtChar_of_isFrobAt hq hq2 hdk hσ, typChar_of_isFrobAt m hq hqm hσ, toAdd_ofAdd]
  congr 1
  have hk0 : ((k : ℤ) : ZMod q) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have key : kChar m k hk (sqClassOf m q) = 0 ↔ legBit k q = 0 := by
    rw [kChar_sqClassOf_eq_zero_iff hk hq hqm, ← jacobiSym.legendreSym.to_jacobiSym,
      legendreSym.eq_one_iff q hk0]
    unfold legBit
    split_ifs with h
    · exact iff_of_true h rfl
    · exact iff_of_false h (by decide)
  exact (zmod2_eq_of_eq_zero_iff key).symm

end ZInQ.Manuscript.RC.AddressGenuine
