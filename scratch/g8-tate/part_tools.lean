import Prefix
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.Classification

/-! # g8-tate, part 1: two tools

* `G8Tate.exists_complex_equiv`: `ℂ ≃+* ℚ̄_ℓ` (Steinitz: both are algebraically closed of
  characteristic `0` and cardinality `𝔠`). It transports `G7Data`'s `ℂ^×`-valued cochain `β` to a
  `ℚ̄_ℓ`-valued one with the same kernel, so that local-data's and local-glue's lemmas on
  `ℚ̄_ℓ`-valued cochains apply to it. (local-glue's `kerWild_of_g7Data` assumed an injective
  `ι : ℂ^× →* ℚ̄_ℓ^×`; this supplies one.)
* `G8Tate.exists_finGal_tame`: a finite `E ⊆ ℚ̄_p` with `[E:ℚ_p] < p` lies in a finite Galois `F`
  with `p ∤ e(F/ℚ_p)` (the Galois closure; its group embeds in `S_n`, `n < p`).
-/

noncomputable section

namespace G8Tate

open Cardinal LadicCond

/-- `#ℚ_p ≤ 𝔠`: `x ↦ (rational approximations of x within 1/(n+1))` is injective into `ℕ → ℚ`. -/
theorem padic_card_le (p : ℕ) [Fact p.Prime] : #ℚ_[p] ≤ 𝔠 := by
  have hex : ∀ x : ℚ_[p], ∀ n : ℕ, ∃ r : ℚ, ‖x - r‖ < 1 / ((n : ℝ) + 1) :=
    fun x n => Padic.rat_dense p x (by positivity)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hpos)
    have h1 := hf x n
    have h2 := hf y n
    rw [hxy] at h1
    have h3 : ‖x - y‖ ≤ ‖x - (f y n : ℚ_[p])‖ + ‖y - (f y n : ℚ_[p])‖ := by
      calc ‖x - y‖ = ‖(x - (f y n : ℚ_[p])) - (y - (f y n : ℚ_[p]))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  calc #ℚ_[p] ≤ #(ℕ → ℚ) := mk_le_of_injective hinj
    _ = 𝔠 := by
      rw [← power_def, Cardinal.mkRat, mk_nat, aleph0_power_aleph0]

/-- `#ℚ̄_ℓ = 𝔠`. -/
theorem padicAlgCl_card (ℓ : ℕ) [Fact ℓ.Prime] : #(PadicAlgCl ℓ) = 𝔠 := by
  apply le_antisymm
  · calc #(PadicAlgCl ℓ) ≤ max #ℚ_[ℓ] ℵ₀ :=
          Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[ℓ] (PadicAlgCl ℓ)
      _ ≤ 𝔠 := max_le (padic_card_le ℓ) aleph0_le_continuum
  · calc 𝔠 ≤ #ℚ_[ℓ] := continuum_le_cardinal_of_nontriviallyNormedField _
      _ ≤ #(PadicAlgCl ℓ) := mk_le_of_injective (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective

/-- **`ℂ ≃+* ℚ̄_ℓ` (proved; Steinitz, Mathlib's `IsAlgClosed.ringEquiv_of_equiv_of_charZero`).** -/
theorem exists_complex_equiv (ℓ : ℕ) [Fact ℓ.Prime] : Nonempty (ℂ ≃+* PadicAlgCl ℓ) := by
  have : CharZero (PadicAlgCl ℓ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective
  exact IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [mk_complex]; exact aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [mk_complex, padicAlgCl_card]))

variable {p : ℕ} [Fact p.Prime]

/-- **A finite `E ⊆ ℚ̄_p` with `[E:ℚ_p] < p` lies in a finite Galois `F` with `p ∤ e(F/ℚ_p)`
(proved).** `F` is the splitting field in `ℚ̄_p` of the minimal polynomial `f` of a primitive
element of `E` (as in local-data's `exists_finGal_ramCard_le`); `Gal(F/ℚ_p)` embeds in the
permutations of the `≤ deg f < p` roots, so `[F:ℚ_p] ∣ m!` with `m < p`, and the inertia group
(`ramCard_zero_eq`) is a subgroup. -/
theorem exists_finGal_tame {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E < p) :
    ∃ F : Fld p, IsFinGal F ∧ E ≤ F ∧ ¬ p ∣ ramCard F 0 := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[p] E
  set a : Kbar p := (α : Kbar p) with ha
  have hint : IsIntegral ℚ_[p] a := (IsIntegral.of_finite ℚ_[p] α).map E.val
  set f := minpoly ℚ_[p] a with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero hint
  have hsplit : (f.map (algebraMap ℚ_[p] (Kbar p))).Splits := IsAlgClosed.splits _
  set F : Fld p := IntermediateField.adjoin ℚ_[p] (f.rootSet (Kbar p)) with hFdef
  have : Polynomial.IsSplittingField ℚ_[p] F f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have : FiniteDimensional ℚ_[p] F := Polynomial.IsSplittingField.finiteDimensional F f
  have hsep : f.Separable := minpoly.irreducible hint |>.separable
  have : IsGalois ℚ_[p] F := IsGalois.of_separable_splitting_field hsep
  have hdeg : f.natDegree < p := by
    have h1 : (minpoly ℚ_[p] α).natDegree ≤ Module.finrank ℚ_[p] E := minpoly.natDegree_le _
    rw [IntermediateField.minpoly_eq] at h1
    exact lt_of_le_of_lt h1 hE
  have hdvdF : ¬ p ∣ Module.finrank ℚ_[p] F := by
    rw [(Polynomial.IsSplittingField.algEquiv F f).toLinearEquiv.finrank_eq,
      ← Polynomial.Gal.card_of_separable hsep]
    have : Fact ((f.map (algebraMap ℚ_[p] f.SplittingField)).Splits) :=
      ⟨Polynomial.SplittingField.splits f⟩
    have h1 : Nat.card f.Gal ∣ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
      Subgroup.card_dvd_of_injective _ (Polynomial.Gal.galActionHom_injective f _)
    rw [Nat.card_perm] at h1
    intro hp
    have h2 := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp (hp.trans h1)
    rw [Nat.card_coe_set_eq] at h2
    have h3 := Polynomial.ncard_rootSet_le f f.SplittingField
    exact absurd (lt_of_le_of_lt (h2.trans h3) hdeg) (lt_irrefl p)
  have hEF : E ≤ F := by
    intro y hy
    have h1 : (⟨y, hy⟩ : E) ∈ IntermediateField.adjoin ℚ_[p] {α} := by rw [hα]; trivial
    have h2 : y ∈ (IntermediateField.adjoin ℚ_[p] {α}).map E.val :=
      ⟨⟨y, hy⟩, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    have hroot : a ∈ f.rootSet (Kbar p) := by
      rw [Polynomial.mem_rootSet]
      exact ⟨hf0, minpoly.aeval ℚ_[p] a⟩
    have hle : IntermediateField.adjoin ℚ_[p] {E.val α} ≤ F :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.subset_adjoin _ _ hroot)
    exact hle h2
  have hFG : IsFinGal F := ⟨inferInstance, inferInstance⟩
  refine ⟨F, hFG, hEF, fun hp => hdvdF ?_⟩
  have : Normal ℚ_[p] F := hFG.2.to_normal
  rw [G15Ram.ramCard_zero_eq F hFG] at hp
  refine hp.trans ?_
  rw [← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_subgroup_dvd_card _

end G8Tate

end

#print axioms G8Tate.exists_complex_equiv
#print axioms G8Tate.exists_finGal_tame
