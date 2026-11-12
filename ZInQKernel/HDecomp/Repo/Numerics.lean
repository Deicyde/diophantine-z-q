import ZInQKernel.Hypotheses.Height

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-repo/Numerics.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-repo, steps A3, A5 and A8: the numerical bookkeeping

* `a3_numerals`: `4·|(𝒪/3𝒪)^*| = 4·72 ≤ 4·81 = 324`, and `|Γ'| = 4·72/2 = 144 = 2⁴3²`
  (N5 L436-441; h-b1 M3). The count `|(𝒪/3𝒪)^*| = 72` is `GlueRepo.A1.card_units_mod3`.
* `splitting_degree_le`: a separable polynomial over `ℚ` of degree `≤ 324` has splitting field of
  degree `≤ 324! = F₀` (N5 L524-526: `[K:ℚ] ≤ F₀`).
* `a8_rank`, `a8_degree`, `a8_field`: `r ≤ 16F₀²` and `[EK:ℚ] ≤ [K:ℚ]·[E:ℚ] ≤ F₀·3^{r²} ≤ D`
  (N5 L544-555), for variables `F₀`, `D = F₀·3^{256F₀⁴}` (the bodies of `ZInQ.heightF0`,
  `ZInQ.heightD`; the kernel cannot unfold those constants, see `HeightConstant.lean`).
-/

open ZInQ Module Polynomial

namespace GlueRepo.Numerics

theorem a3_numerals : 4 * 72 ≤ 4 * 81 ∧ 4 * 81 = 324 ∧ 4 * 72 / 2 = 144 ∧ 144 = 2 ^ 4 * 3 ^ 2 := by
  norm_num

/-- `[K:ℚ] ≤ F₀`: the Galois group of a separable polynomial of degree `≤ 324` embeds in the
permutations of its roots. -/
theorem splitting_degree_le (f : ℚ[X]) (hs : f.Separable) (hd : f.natDegree ≤ 324) :
    finrank ℚ f.SplittingField ≤ Nat.factorial 324 := by
  rw [← Polynomial.Gal.card_of_separable hs]
  have : Fact ((f.map (algebraMap ℚ f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  calc Nat.card f.Gal ≤ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
        Nat.card_le_card_of_injective _ (Polynomial.Gal.galActionHom_injective f _)
    _ = (Nat.card (f.rootSet f.SplittingField)).factorial := Nat.card_perm
    _ ≤ Nat.factorial 324 := by
        apply Nat.factorial_le
        rw [Nat.card_coe_set_eq]
        exact (Polynomial.ncard_rootSet_le f _).trans hd

/-- `r ≤ 16F₀²`: `W₀ = Res_{K/ℚ} A` has `[K:ℚ]² ≤ F₀²` ordered Hom groups between conjugates,
each of rank `≤ 4·dim·dim = 16` (Mumford §19 Thm 3). Stated for a variable `F₀` (the kernel
must not evaluate `324!`); apply with `F₀ = ZInQ.heightF0`. -/
theorem a8_rank {F0 d r : ℕ} (hd : d ≤ F0) (hr : r ≤ d ^ 2 * (4 * 2 * 2)) :
    r ≤ 16 * F0 ^ 2 := by
  calc r ≤ d ^ 2 * (4 * 2 * 2) := hr
    _ ≤ F0 ^ 2 * 16 := Nat.mul_le_mul (Nat.pow_le_pow_left hd 2) (by norm_num)
    _ = 16 * F0 ^ 2 := by ring

/-- `F₀·3^{r²} ≤ D` when `r ≤ 16F₀²`, for `D = F₀·3^{256F₀⁴}` (`ZInQ.heightD`'s body). -/
theorem a8_degree {F0 D k e r : ℕ} (hD : D = F0 * 3 ^ (256 * F0 ^ 4)) (hk : k ≤ F0)
    (he : e ≤ 3 ^ (r ^ 2)) (hr : r ≤ 16 * F0 ^ 2) : k * e ≤ D := by
  rw [hD]
  have h2 : r ^ 2 ≤ 256 * F0 ^ 4 :=
    calc r ^ 2 ≤ (16 * F0 ^ 2) ^ 2 := Nat.pow_le_pow_left hr 2
      _ = 256 * F0 ^ 4 := by ring
  calc k * e ≤ F0 * 3 ^ (r ^ 2) := Nat.mul_le_mul hk he
    _ ≤ F0 * 3 ^ (256 * F0 ^ 4) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h2)

/-- `[L:ℚ] ≤ D` for the Hom field `L = EK` (N5 L554-555). -/
theorem a8_field {M : Type*} [Field M] [Algebra ℚ M] (E K : IntermediateField ℚ M)
    {F0 D r : ℕ} (hD : D = F0 * 3 ^ (256 * F0 ^ 4))
    (hK : finrank ℚ K ≤ F0) (hE : finrank ℚ E ≤ 3 ^ (r ^ 2))
    (hr : r ≤ 16 * F0 ^ 2) : finrank ℚ ↥(E ⊔ K) ≤ D :=
  (IntermediateField.finrank_sup_le E K).trans (by rw [mul_comm]; exact a8_degree hD hK hE hr)

end GlueRepo.Numerics

