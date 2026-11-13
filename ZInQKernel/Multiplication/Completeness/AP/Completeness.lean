import ZInQKernel.Multiplication.Completeness.AP.SlopeCompleteness
import ZInQKernel.Multiplication.Top.Exact
import ZInQKernel.Assembly.Top

/-!
# Completeness and the assembly from the slope representation under field 2′

`SlopeRepresentationAP` is `SlopeRepresentation` with `GoodSlope 0` replaced by
`GoodSlopeAP 0` (field 2′). It is implied by `SlopeRepresentation`
(`slopeRepresentationAP_of_slopeRepresentation`), and it is all that completeness needs: the
chain `slopes_of_int` → `completeness_core` → `multiply_complete` → `multiplication_exact` →
`exists_value_relation_iff` → `assembly` is repeated here with `slope_complete_AP` in place of
`slope_complete`; the proofs are otherwise those of the originals.
-/

namespace ZInQ.Mult

open Syntax

/-- **(SR′) Slope representation under field 2′**: every integer is a sum of three rationals
satisfying `GoodSlopeAP 0`. -/
def SlopeRepresentationAP : Prop :=
  ∀ A : ℤ, ∃ t : Fin 3 → ℚ, ∑ j, t j = A ∧ ∀ j, GoodSlopeAP 0 (t j)

theorem slopeRepresentationAP_of_slopeRepresentation (h : SlopeRepresentation) :
    SlopeRepresentationAP := fun A => by
  obtain ⟨t, hs, hg⟩ := h A
  exact ⟨t, hs, fun j => (hg j).goodSlopeAP⟩

/-- Every integer is a sum of three slopes satisfying `Slope(·, ℓ₀; c_*, c_* n₁, c_* n₂, c_* n₁n₂)`. -/
theorem slopes_of_int_AP (hPC : PoleCompleteness) (h22 : SlopeRepresentationAP)
    (n₁ n₂ A : ℤ) :
    ∃ t : Fin 3 → ℚ, ∑ l, t l = A ∧
      ∀ l, SlopePred (t l) Syntax.ell (certShifts ![n₁, n₂, n₁ * n₂]) := by
  obtain ⟨t, hsum, hgood⟩ := h22 A
  exact ⟨t, hsum, fun l => slope_complete_AP hPC n₁ n₂ (hgood l)⟩

/-- **The witnesses of the height certificate for a true triple.** With `n = (a, b, ab)` there
are integers `b_i ≥ 1` and `a_{ij}` with `b_i x_{ij} = a_{ij}`, where `x_{i0}, x_{i1}` are the
coordinates `1, 2` of the code `ι(n_i)`, and each of the nine integers `a_{ij}, b_i` is a sum of
three slopes satisfying the slope predicate. -/
theorem completeness_core_AP (hPC : PoleCompleteness) (h22 : SlopeRepresentationAP)
    (a b : ℤ) :
    ∃ (B : Fin 3 → ℕ) (A : Fin 3 → Fin 2 → ℤ),
      (∀ i, 0 < B i) ∧
      (∀ i, (B i : ℚ) * iota (![a, b, a * b] i) 1 = A i 0 ∧
        (B i : ℚ) * iota (![a, b, a * b] i) 2 = A i 1) ∧
      (∀ i k, ∃ t : Fin 3 → ℚ, ∑ l, t l = A i k ∧
        ∀ l, SlopePred (t l) Syntax.ell (certShifts ![a, b, a * b])) ∧
      (∀ i, ∃ t : Fin 3 → ℚ, ∑ l, t l = B i ∧
        ∀ l, SlopePred (t l) Syntax.ell (certShifts ![a, b, a * b])) := by
  choose B hB A₀ A₁ hA₀ hA₁ using fun i : Fin 3 =>
    exists_common_den (iota (![a, b, a * b] i) 1) (iota (![a, b, a * b] i) 2)
  refine ⟨B, fun i => ![A₀ i, A₁ i], hB, fun i => ⟨hA₀ i, hA₁ i⟩, fun i k => ?_, fun i => ?_⟩
  · obtain ⟨t, ht, hs⟩ := slopes_of_int_AP hPC h22 a b (![A₀ i, A₁ i] k)
    exact ⟨t, ht, hs⟩
  · obtain ⟨t, ht, hs⟩ := slopes_of_int_AP hPC h22 a b (B i)
    exact ⟨t, by rw [ht]; simp, hs⟩

/-- **Completeness of the multiplication template**, from the slope representation under
field 2′. -/
theorem multiply_complete_AP (hPC : PoleCompleteness) (h22 : SlopeRepresentationAP) (a b : ℤ) :
    (multiplyTemplate specConstructors FixedConst.cstar.value FixedConst.ell.value
      FixedConst.T.value).Rel (codes3 (iota a) (iota b) (iota (a * b))) := by
  rw [FixedConst.value_cstar, FixedConst.value_ell, FixedConst.value_T]
  rw [multiply_rel_iff specConstructors _ _ _ spec_scalar_cstar_rel_iff]
  refine ⟨![a, b, a * b], rfl, rfl, rfl, ?_, guard_true_triple specConstructors _ rfl a b⟩
  obtain ⟨B, A, hB, hBA, hA, hBs⟩ := completeness_core_AP hPC h22 a b
  have hc : (![(Syntax.cstar : ℤ), Syntax.cstar * (![a, b, a * b] : Fin 3 → ℤ) 0,
      Syntax.cstar * (![a, b, a * b] : Fin 3 → ℤ) 1, Syntax.cstar * (![a, b, a * b] : Fin 3 → ℤ) 2]
      : Fin 4 → ℤ) = certShifts ![a, b, a * b] := rfl
  have hℓ : (((Syntax.ell : ℕ) : ℤ) : ℚ) = (Syntax.ell : ℚ) := Int.cast_natCast _
  rw [hc, hℓ]
  have hY : ∀ i : Fin 3, (![iota a, iota b, iota (a * b)] : Fin 3 → Fin 5 → ℚ) i =
      iota ((![a, b, a * b] : Fin 3 → ℤ) i) := by
    intro i; fin_cases i <;> rfl
  refine ⟨fun i k => (A i k : ℚ), fun i => (B i : ℚ), fun i => ⟨?_, ?_, ?_⟩, fun k => ?_⟩
  · show (B i : ℚ) ≠ 0
    exact_mod_cast (hB i).ne'
  · rw [hY]; exact (hBA i).1
  · rw [hY]; exact (hBA i).2
  · have sum3 : ∀ s : Fin 3 → ℚ, ∑ l, s l = s 0 + s 1 + s 2 := fun s => Fin.sum_univ_three s
    fin_cases k <;> simp only [nineQ] <;>
    first
      | (obtain ⟨s, hs, hsl⟩ := hA 0 0; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hA 0 1; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hBs 0; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hA 1 0; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hA 1 1; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hBs 1; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hA 2 0; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hA 2 1; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)
      | (obtain ⟨s, hs, hsl⟩ := hBs 2; exact ⟨s, by rw [← sum3]; simpa using hs, hsl⟩)

/-- **Correctness of the multiplication template** (input M), from SR′. -/
theorem multiplication_exact_AP (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : SlopeRepresentationAP) :
    Translation.MultiplicationExact Syntax.specConstructors FixedConst.cstar.value
      FixedConst.ell.value FixedConst.T.value := by
  intro Y₁ Y₂ Y₃
  constructor
  · exact multiply_sound hH Y₁ Y₂ Y₃
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    exact multiply_complete_AP hPC h22 a b

end ZInQ.Mult

namespace ZInQ.Assembly

open Syntax Compiler.Precision Compiler.Universal

/-- **The exact ordinary-value relation, projected**, under H, PC and SR′. -/
theorem exists_value_relation_iff_AP (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : Mult.SlopeRepresentationAP) (t : ℚ) :
    (∃ N : Fin 5 → ℚ, ValueRel N t) ↔ ∃ z : ℤ, (z : ℚ) = t :=
  have hM := Mult.multiplication_exact_AP hH hPC h22
  exists_value_relation_iff_of hH hPC hM (close_sound hM) (close_complete hM) t

/-- **The target statement** for `P_*`, under H, PC, SR′ and the addition and multiplication
bound of the universal halting circuit. The polynomial is the same `specPstar c₃` as in
`assembly`. -/
theorem assembly_AP (hB : Compiler.NodeCheck.HaltingAddMulBound) (hH : SixContactMin)
    (hPC : PoleCompleteness) (h22 : Mult.SlopeRepresentationAP) : FrozenTarget :=
  ⟨specPstar (c3 : ℤ), Pstar_spec_of hB (exists_value_relation_iff_AP hH hPC h22)⟩

end ZInQ.Assembly
