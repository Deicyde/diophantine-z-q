module

public import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.GenusPrincipalReduction
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Tactic

/-! Principal ramified products are distinguished by a square class of maximal-order units. -/

public section

namespace HDec.CMBranch.FowlerArithmetic

open NumberField

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

private theorem unit_mem_torsion (hk : Module.finrank ℚ K = 2) (u : (𝓞 K)ˣ) :
    u ∈ NumberField.Units.torsion K := by
  have hdim := IsTotallyComplex.finrank (K := K)
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by omega
  have hr : NumberField.Units.rank K = 0 := by
    rw [NumberField.Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, hc]
  let : IsEmpty (Fin (NumberField.Units.rank K)) := by rw [hr]; infer_instance
  obtain ⟨⟨ζ, v⟩, h, _⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
  simp only [Finset.prod_of_isEmpty, mul_one] at h
  exact h.symm ▸ ζ.property

private theorem nat_isSquare_of_field_sq (hk : Module.finrank ℚ K = 2) {m : ℕ} {x : K}
    (hx : x ^ 2 = (m : K)) : IsSquare m := by
  obtain ⟨r, hr⟩ := exists_rat_of_sq_nonneg_rat hk (q := (m : ℚ)) (by positivity)
    (by simpa using hx)
  have hsq : r ^ 2 = (m : ℚ) := (algebraMap ℚ K).injective (by simpa [map_pow, hr] using hx)
  exact Rat.isSquare_natCast_iff.mp ⟨r, by simpa [pow_two] using hsq.symm⟩

/-- If a squarefree principal product squares to the integer product times a unit,
its square class of units determines the product. This also handles the two exceptional
unit groups without assuming that every unit is a sign. -/
theorem card_le_two_of_squarefree_unit_relations (hk : Module.finrank ℚ K = 2)
    {A : Type*} (m : A → ℕ) (hm : Function.Injective m) (hs : ∀ a, Squarefree (m a))
    (h : ∀ a, ∃ (x : K) (u : (𝓞 K)ˣ), x ^ 2 = (m a : K) * (u : 𝓞 K)) :
    Nat.card A ≤ 2 := by
  classical
  choose x u hx using h
  let T := NumberField.Units.torsion K
  let v : A → T := fun a => ⟨u a, unit_mem_torsion hk (u a)⟩
  let H : Subgroup T := (powMonoidHom 2 : T →* T).range
  let f : A → T ⧸ H := fun a => QuotientGroup.mk (v a)
  have hf : Function.Injective f := by
    intro a b hab
    have hv : v a / v b ∈ H := QuotientGroup.eq_iff_div_mem.mp hab
    obtain ⟨c, hc⟩ := hv
    have hc' : c ^ 2 * v b = v a := by
      change c ^ 2 = v a / v b at hc
      simp [hc]
    let e : T →* K := ((algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))).comp
      T.subtype
    have hca : e c ^ 2 * e (v b) = e (v a) := by simpa only [map_mul, map_pow] using congrArg e hc'
    have hcx (i : A) : x i ^ 2 = (m i : K) * e (v i) := hx i
    have hnz (z : T) : e z ≠ 0 := by
      change (((z : (𝓞 K)ˣ) : 𝓞 K) : K) ≠ 0
      exact RingOfIntegers.coe_ne_zero_iff.mpr (by simp)
    have hxy : (x a * x b / (e c * e (v b))) ^ 2 = ((m a * m b : ℕ) : K) := by
      rw [div_pow, mul_pow, hcx, hcx, ← hca, Nat.cast_mul, mul_pow]
      field_simp [hnz]
    have hsq := nat_isSquare_of_field_sq hk hxy
    exact hm (Nat.dvd_antisymm ((hs a).dvd_of_isSquare_mul hsq)
      ((hs b).dvd_of_isSquare_mul (mul_comm (m a) (m b) ▸ hsq)))
  have hcard := Nat.card_le_card_of_injective f hf
  change Nat.card A ≤ H.index at hcard
  change Nat.card A ≤ (powMonoidHom 2 : T →* T).range.index at hcard
  rw [IsCyclic.index_powMonoidHom_range] at hcard
  exact hcard.trans (Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right _ _))

/-- The actual class number is divisible by the required genus factor once the kernel
of the ramified ideal map is shown to have squarefree principal products. -/
theorem classNumber_genus_dvd_of_principal_unit_squares
    (hk : Module.finrank ℚ K = 2)
    (f : Multiplicative (↥(NumberField.discr K).natAbs.primeFactors → ZMod 2) →*
      ClassGroup (𝓞 K))
    (m : f.ker → ℕ) (hm : Function.Injective m) (hs : ∀ a, Squarefree (m a))
    (h : ∀ a, ∃ (x : K) (u : (𝓞 K)ˣ), x ^ 2 = (m a : K) * (u : 𝓞 K)) :
    2 ^ ((NumberField.discr K).natAbs.primeFactors.card - 1) ∣ classNumber K := by
  have hd := pow_pred_card_dvd_of_card_ker_le_two f
    (card_le_two_of_squarefree_unit_relations hk m hm hs h)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card] at hd
  exact hd

end HDec.CMBranch.FowlerArithmetic
