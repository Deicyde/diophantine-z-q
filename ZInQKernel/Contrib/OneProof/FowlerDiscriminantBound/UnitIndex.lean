import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ActualReadings
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-! The two unit-index estimates for the order in Cox's conductor formula. -/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

private theorem torsion_eq_top_of_imaginary_quadratic [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) : NumberField.Units.torsion K = ⊤ := by
  have hd := IsTotallyComplex.finrank (K := K)
  rw [hK] at hd
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by omega
  have hr : NumberField.Units.rank K = 0 := by
    rw [NumberField.Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, hc]
  rw [Subgroup.eq_top_iff']
  intro u
  obtain ⟨⟨ζ, e⟩, hu, _⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
  have : IsEmpty (Fin (NumberField.Units.rank K)) := by rw [hr]; infer_instance
  simp only [Finset.prod_of_isEmpty, mul_one] at hu
  exact hu ▸ ζ.property

private theorem exists_primitive_torsionOrder :
    ∃ ζ : K, IsPrimitiveRoot ζ (NumberField.Units.torsionOrder K) := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := NumberField.Units.torsion K)
  refine ⟨((ζ : (𝓞 K)ˣ) : K), IsPrimitiveRoot.coe_coe_iff.mpr ?_⟩
  rw [IsPrimitiveRoot.iff_orderOf, Subgroup.orderOf_coe, hζ]
  rfl

private theorem totient_le_finrank_of_primitive {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : n.totient ≤ Module.finrank ℚ K := by
  have := hζ.adjoin_isCyclotomicExtension ℚ
  rw [← IsCyclotomicExtension.finrank (Algebra.adjoin ℚ ({ζ} : Set K))
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))]
  exact Submodule.finrank_le (Algebra.adjoin ℚ ({ζ} : Set K)).toSubmodule

private theorem even_eq_two_four_or_six {n : ℕ} (hn : 0 < n) (he : Even n)
    (hφ : n.totient ≤ 2) : n = 2 ∨ n = 4 ∨ n = 6 := by
  obtain ⟨m, hm⟩ := he.two_dvd
  by_cases hm₁ : m = 1
  · exact Or.inl (by omega)
  obtain ⟨p, hp, hpm⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hm₁
  have hp₂ : 2 * p ∣ n := hm ▸ Nat.mul_dvd_mul_left 2 hpm
  have hpn : p ∣ n := dvd_trans (dvd_mul_left p 2) hp₂
  have hφp := Nat.le_of_dvd (Nat.totient_pos.mpr hn) (Nat.totient_dvd_of_dvd hpn)
  rw [Nat.totient_prime hp] at hφp
  have := hp.two_le
  have hp₂₃ : p = 2 ∨ p = 3 := by omega
  have hφ₂ : (2 * p).totient = 2 := by
    rcases hp₂₃ with rfl | rfl <;> decide
  have hφn : n.totient = 2 := by
    have h := Nat.le_of_dvd (Nat.totient_pos.mpr hn) (Nat.totient_dvd_of_dvd hp₂)
    omega
  have heq := Even.eq_of_totient_eq_totient hp₂ (even_two.mul_right p) (hφ₂.trans hφn.symm)
  rcases hp₂₃ with rfl | rfl <;> omega

private theorem torsionOrder_eq_two_four_or_six (hK : Module.finrank ℚ K = 2) :
    NumberField.Units.torsionOrder K = 2 ∨ NumberField.Units.torsionOrder K = 4 ∨
      NumberField.Units.torsionOrder K = 6 := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_torsionOrder (K := K)
  exact even_eq_two_four_or_six (NumberField.Units.torsionOrder_pos K)
    (NumberField.Units.even_torsionOrder K) (hK ▸ totient_le_finrank_of_primitive hζ)

private theorem cyclotomic_of_primitive_of_totient_eq_finrank {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hn : n.totient = Module.finrank ℚ K) :
    IsCyclotomicExtension {n} ℚ K := by
  let A := Algebra.adjoin ℚ ({ζ} : Set K)
  have : IsCyclotomicExtension {n} ℚ A := hζ.adjoin_isCyclotomicExtension ℚ
  have hA : Module.finrank ℚ A = Module.finrank ℚ K :=
    (IsCyclotomicExtension.finrank A
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))).trans hn
  have htop : A = ⊤ := by
    apply Subalgebra.toSubmodule_injective
    rw [Algebra.top_toSubmodule]
    exact Submodule.eq_top_of_finrank_eq hA
  rw [IsCyclotomicExtension.iff_adjoin_eq_top]
  refine ⟨?_, ?_⟩
  · intro m hm _
    rw [Set.mem_singleton_iff.mp hm]
    exact ⟨ζ, hζ⟩
  · apply top_unique
    rw [← htop]
    exact Algebra.adjoin_mono (by simpa using And.intro (NeZero.ne n) hζ.pow_eq_one)

private theorem torsionOrder_eq_two_of_discr (hK : Module.finrank ℚ K = 2)
    (h₃ : NumberField.discr K ≠ -3) (h₄ : NumberField.discr K ≠ -4) :
    NumberField.Units.torsionOrder K = 2 := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_torsionOrder (K := K)
  rcases torsionOrder_eq_two_four_or_six hK with h | h | h
  · exact h
  · rw [h] at hζ
    have : IsCyclotomicExtension {4} ℚ K :=
      cyclotomic_of_primitive_of_totient_eq_finrank hζ
        ((by decide : Nat.totient 4 = 2).trans hK.symm)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hd := IsCyclotomicExtension.Rat.discr_prime_pow_succ 2 1 K
    exact (h₄ (by simpa using hd)).elim
  · rw [h] at hζ
    have hξ : IsPrimitiveRoot (ζ ^ 2) 3 := hζ.pow_of_dvd (p := 2) (by decide) (by decide)
    have : IsCyclotomicExtension {3} ℚ K :=
      cyclotomic_of_primitive_of_totient_eq_finrank hξ
        ((by decide : Nat.totient 3 = 2).trans hK.symm)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hd := IsCyclotomicExtension.Rat.discr_prime 3 K
    exact (h₃ (by simpa using hd)).elim

private noncomputable def torsionEquivUnits [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) :
    NumberField.Units.torsion K ≃ (𝓞 K)ˣ :=
  Equiv.ofBijective Subtype.val
    ⟨Subtype.val_injective, fun u ↦ ⟨⟨u, by rw [torsion_eq_top_of_imaginary_quadratic hK]; trivial⟩,
      rfl⟩⟩

private theorem two_le_card_orderUnitsImage [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (O : NumberFieldOrder K) :
    2 ≤ Nat.card (Units.map O.toRingOfIntegers.val.toMonoidHom).range := by
  have : Finite (𝓞 K)ˣ := Finite.of_equiv _ (torsionEquivUnits hK)
  let H := (Units.map O.toRingOfIntegers.val.toMonoidHom).range
  have hm : (-1 : (𝓞 K)ˣ) ∈ H := ⟨-1, Units.map_neg_one O.toRingOfIntegers.val⟩
  let f : Bool → H := fun b ↦ if b then ⟨-1, hm⟩ else 1
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b <;> try rfl
    all_goals
      have he := congrArg (fun u : H ↦ ((u : (𝓞 K)ˣ) : K)) hab
      norm_num [f] at he
  change 2 ≤ Nat.card H
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using Nat.card_le_card_of_injective f hf

private theorem unitIndex_mul_two_le_torsionOrder [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K) :
    quadraticOrderUnitIndex O * 2 ≤ NumberField.Units.torsionOrder K := by
  calc
    quadraticOrderUnitIndex O * 2 ≤ quadraticOrderUnitIndex O *
        Nat.card (Units.map O.toRingOfIntegers.val.toMonoidHom).range :=
      Nat.mul_le_mul_left _ (two_le_card_orderUnitsImage hK O)
    _ = Nat.card (𝓞 K)ˣ := (Units.map O.toRingOfIntegers.val.toMonoidHom).range.index_mul_card
    _ = NumberField.Units.torsionOrder K := Nat.card_congr (torsionEquivUnits hK).symm

/-- The unit index of any order in an imaginary quadratic number field is at most three. -/
theorem quadraticOrderUnitIndex_le_three [IsTotallyComplex K] (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) : quadraticOrderUnitIndex O ≤ 3 := by
  have hi := unitIndex_mul_two_le_torsionOrder hK O
  rcases torsionOrder_eq_two_four_or_six hK with h | h | h <;> omega

/-- Outside discriminants `-3` and `-4`, every maximal-order unit comes from the given order. -/
theorem quadraticOrderUnitIndex_eq_one [IsTotallyComplex K] (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) (h₃ : NumberField.discr K ≠ -3)
    (h₄ : NumberField.discr K ≠ -4) : quadraticOrderUnitIndex O = 1 := by
  have ht := torsionOrder_eq_two_of_discr hK h₃ h₄
  have hcard : Nat.card (𝓞 K)ˣ = 2 := (Nat.card_congr (torsionEquivUnits hK).symm).trans ht
  have hup := unitIndex_mul_two_le_torsionOrder hK O
  have hi := (Units.map O.toRingOfIntegers.val.toMonoidHom).range.index_mul_card
  change quadraticOrderUnitIndex O * _ = _ at hi
  by_contra hn
  have hz : quadraticOrderUnitIndex O = 0 := by omega
  simp [hz, hcard] at hi

end HDec.CMBranch.FowlerArithmetic
