import ZInQKernel.RouteK.PropN

/-!
# A canonical integer witness for the TYZ input encoding

This module does not assert `TYZInputs`. It constructs the elementary part of an
existential witness, using the already proved `lemmaN1_core` with exactly its
unordered divisor conventions. On classes 1 and 3, the witness lifts `Lam` from
`ZMod 2` to integers. On class 5, its value is 1 exactly when at least one of the
two existing genus sums is nonzero, and 0 otherwise. Every other value is 0.

The class-5 choice records the *minimum* analytic continuation obligation forced
by `GenusData`: if both sums vanish, the existing zero-value witness is available.
No continuation is constructed here, and no literature premise is assumed.
-/

noncomputable section

namespace ZInQ.PropN.TYZEquivalence

open ZInQ.Literature ZInQ.RouteK.Rank5b

/-- A simultaneous integer witness, with the parity solution on classes 1/3 and
only parity-forced nonzero values on class 5. Values outside those classes are 0. -/
def canonicalL (m : ℕ) : ℤ :=
  if m % 8 = 1 ∨ m % 8 = 3 then ((Lam m).val : ℤ)
  else if m % 8 = 5 ∧ (T5aCl m ≠ 0 ∨ T5bCl m ≠ 0) then 1 else 0

/-- The parity lift is exact, including `m = 1`. No squarefreeness is needed for
this identity about the chosen representative. -/
theorem canonicalL_cast {m : ℕ} (hm : m % 8 = 1 ∨ m % 8 = 3) :
    (canonicalL m : ZMod 2) = Lam m := by
  rw [canonicalL, ite_eq_left hm, Int.cast_natCast, ZMod.natCast_zmod_val]

@[simp] theorem canonicalL_zero : canonicalL 0 = 0 := by
  norm_num [canonicalL]

@[simp] theorem canonicalL_one : canonicalL 1 = 1 := by
  norm_num [canonicalL, part_Lam_one, ZMod.val_one]

/-- Class-5 values are nonzero precisely on the support of the two genus sums.
This does not assert that the original TYZ integer function has this value. -/
theorem canonicalL_ne_zero_iff {n : ℕ} (hn : n % 8 = 5) :
    canonicalL n ≠ 0 ↔ T5aCl n ≠ 0 ∨ T5bCl n ≠ 0 := by
  have h13 : ¬ (n % 8 = 1 ∨ n % 8 = 3) := by omega
  rw [canonicalL, ite_eq_right h13]
  by_cases h : T5aCl n ≠ 0 ∨ T5bCl n ≠ 0
  · rw [ite_eq_left ⟨hn, h⟩]
    exact iff_of_true one_ne_zero h
  · rw [ite_eq_right (fun h' => h h'.2)]
    exact iff_of_false (by simp) h

/-- No values on the other residue classes enter the chosen witness. -/
theorem canonicalL_eq_zero_of_other {n : ℕ}
    (h13 : ¬ (n % 8 = 1 ∨ n % 8 = 3)) (h5 : n % 8 ≠ 5) :
    canonicalL n = 0 := by
  simp [canonicalL, h13, h5]

/-- The chosen integer lift satisfies exactly the frozen convolution predicate.
The class-1 sum retains `d*d < m`; the class-3 sum retains its distinguished
class-1 divisor. In particular no ordered replacement of the first sum is used. -/
theorem canonicalL_lemmaTwoEight : LemmaTwoEight canonicalL := by
  constructor
  · intro m hsq hm1 hm
    calc
      (((∑ d ∈ m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m),
          canonicalL d * canonicalL (m / d) : ℤ) : ZMod 2)) =
          ∑ d ∈ m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m),
            Lam d * Lam (m / d) := by
        push_cast
        refine Finset.sum_congr rfl fun d hd => ?_
        obtain ⟨hdm, hd8, -⟩ := Finset.mem_filter.mp hd
        have hq : m / d % 8 = 1 := by
          simpa using div_mod8_of (Nat.dvd_of_mem_divisors hdm) hm hd8 (Or.inl rfl)
        rw [canonicalL_cast (Or.inl hd8), canonicalL_cast (Or.inl hq)]
      _ = (gNat m : ZMod 2) := lemmaN1_core.2.1 m hsq hm1 hm
  · intro m hsq hm
    calc
      (((∑ d ∈ m.divisors.filter (fun d => d % 8 = 1),
          canonicalL (m / d) * canonicalL d : ℤ) : ZMod 2)) =
          ∑ d ∈ m.divisors.filter (fun d => d % 8 = 1),
            Lam (m / d) * Lam d := by
        push_cast
        refine Finset.sum_congr rfl fun d hd => ?_
        obtain ⟨hdm, hd8⟩ := Finset.mem_filter.mp hd
        have hq : m / d % 8 = 3 := by
          simpa using div_mod8_of (Nat.dvd_of_mem_divisors hdm) hm hd8 (Or.inl rfl)
        rw [canonicalL_cast (Or.inr hq), canonicalL_cast (Or.inl hd8)]
      _ = (gNat m : ZMod 2) := lemmaN1_core.2.2 m hsq hm

/-- Under the frozen convolution and normalization, both integer weighted parities
are the existing `Lam` weighted parities. Dividing by a divisor is exact and
preserves squarefreeness; its residue is 1 or 3 in precisely the two cases used. -/
theorem weightedParity_eq_lam {L : ℕ → ℤ} (hL1 : L 1 = 1) (h28 : LemmaTwoEight L)
    {n c : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) (hc : c = 5 ∨ c = 7) :
    (((∑ e ∈ n.divisors.filter (fun e => e % 8 = c),
        L (n / e) * (gNat e : ℤ) : ℤ) : ZMod 2)) =
      ∑ e ∈ n.divisors.filter (fun e => e % 8 = c), Lam (n / e) * (gNat e : ZMod 2) := by
  push_cast
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨heD, he8⟩ := Finset.mem_filter.mp he
  have hen : e ∣ n := Nat.dvd_of_mem_divisors heD
  have hq : n / e % 8 = 1 ∨ n / e % 8 = 3 := by
    rw [div_mod8_of hen hn he8 (by omega)]
    rcases hc with rfl | rfl <;> norm_num
  rw [lemmaN1 hL1 h28 (n / e) (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hen)) hq]

/-- A version of the existing witness criterion stated directly in the two
existing unordered genus sums. This is an equivalence about the encoding,
not a proof of either analytic or arithmetic literature input. -/
theorem genusData_nonempty_iff_genusSums {L : ℕ → ℤ} (hL1 : L 1 = 1)
    (h28 : LemmaTwoEight L) {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) (hLn : L n = 0) :
    Nonempty (GenusData L n) ↔ T5aCl n = 0 ∧ T5bCl n = 0 := by
  rw [Witness.genusData_nonempty_iff_parities L n hn hsq hL1 hLn,
    weightedParity_eq_lam hL1 h28 hn hsq (Or.inl rfl),
    weightedParity_eq_lam hL1 h28 hn hsq (Or.inr rfl),
    (matching hn hsq).1, (matching hn hsq).2]

/-- The canonical `L` always carries `GenusData` on the required domain. The
nonzero branch uses the free-plus-torsion witness; the zero branch uses the
parity witness. This theorem supplies no I7 continuation. -/
theorem canonicalL_genusData {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    Nonempty (GenusData canonicalL n) := by
  by_cases hLn : canonicalL n = 0
  · apply (genusData_nonempty_iff_genusSums canonicalL_one canonicalL_lemmaTwoEight hn hsq hLn).mpr
    have hrows : ¬ (T5aCl n ≠ 0 ∨ T5bCl n ≠ 0) :=
      fun h => (canonicalL_ne_zero_iff hn).mpr h hLn
    constructor <;> by_contra h
    · exact hrows (Or.inl h)
    · exact hrows (Or.inr h)
  · exact Witness.genusData_nonempty canonicalL n hLn

end ZInQ.PropN.TYZEquivalence
