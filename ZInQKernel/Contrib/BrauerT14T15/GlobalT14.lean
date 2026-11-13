import ZInQKernel.Contrib.BrauerT14T15.BaseChange2
import ZInQKernel.Contrib.BrauerT14T15.LocalT15
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SecondInequality

/-!
# Leaf T14 (I6.2a′, I6.2b′) from Tau Ceti's global Brauer theory

`PkgI6.BrauerHasse2C` and `PkgI6.BrauerReciprocity2C` (`ZInQKernel/HDecomp/Conductor/I6Base.lean`)
are the `2`-torsion of the Albert–Brauer–Hasse–Noether sequence for `ℚ` on continuous cochains.
This file derives them from the corresponding statements on Tau Ceti's `Br ℚ`:

* `brauerHasse2C_of_injective`: from the Hasse principle `Function.Injective (brLocalization ℚ)`;
* `brauerReciprocity2C_of_sum`: from the sum formula `sumLocalInv ℚ (brLocalization ℚ x) = 0`.

The vendored Tau Ceti (oct16) proves both only conditionally, from the vanishing of `H¹` of the
idele class formation, which it in turn derives from the Kummer case of the second inequality
(`TauCeti.ClassFieldTheory.subsingleton_h1_globalFormation_of_forall_index_le`).  So:

* `brauerHasse2C_of_kummerIndexBound`, `brauerReciprocity2C_of_kummerIndexBound`: T14a′ and T14b′
  from the single Prop `KummerIndexBound`: for a cyclic extension `L/F` of number fields of prime
  degree `p` with `μ_p ⊂ F`, `[C_F : N_{L/F} C_L] ≤ p` (Milne, *Class Field Theory*, VII §6,
  the Kummer case of the second inequality; Neukirch, *ANT*, VI §4; locators UNVERIFIED).
-/

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

namespace ZInQ.Contrib.BrauerT14T15

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory PkgI6 IsDedekindDomain NumberField

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ### Places of `ℚ` -/

/-- Base change to `ℚ_[p]` and to the adic completion at the corresponding place vanish together. -/
lemma brBaseChange_adicCompletion_eq_zero_iff (v : HeightOneSpectrum (𝓞 ℚ)) (x : Br ℚ) :
    brBaseChange ℚ (v.adicCompletion ℚ) x = 0 ↔
      brBaseChange ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] x = 0 := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  exact ⟨brBaseChange_eq_zero_of_algHom e.toAlgEquiv.toAlgHom,
    brBaseChange_eq_zero_of_algHom e.toAlgEquiv.symm.toAlgHom⟩

lemma isReal_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]; exact Rat.isReal_infinitePlace

/-- Base change to `ℝ` and to the completion at the infinite place vanish together. -/
lemma brBaseChange_infinite_eq_zero_iff (w : InfinitePlace ℚ) (x : Br ℚ) :
    brBaseChange ℚ w.Completion x = 0 ↔ brBaseChange ℚ ℝ x = 0 := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat w)
  exact ⟨brBaseChange_eq_zero_of_algHom e.toRingHom.toRatAlgHom,
    brBaseChange_eq_zero_of_algHom e.symm.toRingHom.toRatAlgHom⟩

/-! ### T14a′ from the Hasse principle -/

/-- **T14a′ (`PkgI6.BrauerHasse2C`) from the Hasse principle for `Br ℚ`.** -/
theorem brauerHasse2C_of_injective (hH : Function.Injective (brLocalization ℚ)) :
    BrauerHasse2C := by
  intro ε hε hR hP
  rw [← brClass_eq_zero_iff ε hε]
  apply hH
  rw [map_zero]
  refine Prod.ext (DFinsupp.ext fun v => ?_) (funext fun w => ?_)
  · rw [brLocalization_fst_apply, Prod.fst_zero, DFinsupp.zero_apply,
      brBaseChange_adicCompletion_eq_zero_iff, brBaseChange_brClass_eq_zero_iff]
    exact hP _
  · rw [brLocalization_snd_apply, Prod.snd_zero, Pi.zero_apply,
      brBaseChange_infinite_eq_zero_iff, brBaseChange_brClass_eq_zero_iff]
    exact hR

/-! ### The Kummer-case hypothesis -/

/-- **The Kummer case of the second inequality of global class field theory**: for a Galois
extension `L/F` of number fields of prime degree `p` such that `F` contains the `p`-th roots of
unity, the norm group `N_{L/F}(C_L)` has index at most `p` in the idele class group `C_F`
(Milne, *Class Field Theory*, VII, §6; UNVERIFIED locator).  This is exactly the hypothesis of
Tau Ceti's `subsingleton_h1_globalFormation_of_forall_index_le`. -/
def KummerIndexBound : Prop :=
  ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [IsGalois F L] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p],
    Module.finrank F L = p → (GlobalNumberFields.ideleClassNormMap F L).range.index ≤ p

lemma brLocalization_injective_of_kummerIndexBound (h : KummerIndexBound) (K : Type) [Field K]
    [NumberField K] : Function.Injective (brLocalization K) :=
  brLocalization_injective_of_subsingleton_h1_globalFormation K
    (fun V => subsingleton_h1_globalFormation_of_forall_index_le (K := K) h _)

/-- **Leaf T14a′ (`PkgI6.BrauerHasse2C`) from the Kummer case of the second inequality.** -/
theorem brauerHasse2C_of_kummerIndexBound (h : KummerIndexBound) : BrauerHasse2C :=
  brauerHasse2C_of_injective (brLocalization_injective_of_kummerIndexBound h ℚ)

/-! ### T14b′ from the sum formula -/

lemma even_of_nsmul_half_eq_zero (n : ℕ) (h : n • ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 0) :
    Even n := by
  rw [← AddCircle.coe_nsmul] at h
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp h
  simp only [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
  have h2 : ((2 * k : ℤ) : ℚ) = (n : ℤ) := by push_cast; linarith
  have h3 : (2 * k : ℤ) = n := by exact_mod_cast h2
  exact ⟨k.toNat, by omega⟩

lemma two_nsmul_brClass (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2)
    (hε : IsCocycle2 ε) : 2 • brClass ε hε = 0 := by
  rw [brClass, ← map_nsmul, ← map_nsmul]
  have : (2 • (⟨_, sgn_mem_Z2 (isCocycle2_toSep hε)⟩ :
      Z2 (AbsoluteGaloisGroup ℚ) (UnitsCoeff ℚ))) = 0 := by
    apply Subtype.ext
    funext q
    rw [AddSubgroup.coe_nsmul]
    change 2 • sgn ℚ (toSep ε q.1 q.2) = 0
    rw [← map_nsmul, two_nsmul]
    generalize toSep ε q.1 q.2 = a
    have : a + a = 0 := by fin_cases a <;> decide
    rw [this, map_zero]
  rw [this, map_zero, map_zero]

/-- A nonzero `2`-torsion element of `ℚ/ℤ` is `1/2`. -/
lemma eq_half_of_two_torsion {y : AddCircle (1 : ℚ)} (h2 : 2 • y = 0) (h0 : y ≠ 0) :
    y = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) :=
  (addCircle_two_torsion y h2).resolve_left h0

/-- **T14b′ (`PkgI6.BrauerReciprocity2C`) from the sum formula for `Br ℚ`.** -/
theorem brauerReciprocity2C_of_sum (hS : ∀ x : Br ℚ, sumLocalInv ℚ (brLocalization ℚ x) = 0) :
    BrauerReciprocity2C := by
  classical
  intro ε hε
  set x := brClass ε hε with hxdef
  have hx2 := two_nsmul_brClass ε hε
  set S := brauerSupport ℚ x
  -- The set of primes where `ε` is locally nontrivial is the image of the support of `x`.
  have hA : {p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
      ¬ IsCoboundary2 (resC ℚ_[(p : ℕ)] ε)} =
      Rat.HeightOneSpectrum.primesEquiv '' (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    ext p
    obtain ⟨v, rfl⟩ := Rat.HeightOneSpectrum.primesEquiv.surjective p
    rw [Set.mem_image_equiv, Equiv.symm_apply_apply, Finset.mem_coe, mem_brauerSupport,
      Set.mem_setOf_eq, ne_eq, finiteInvAt_eq_zero_iff, brBaseChange_adicCompletion_eq_zero_iff,
      brBaseChange_brClass_eq_zero_iff]
  rw [hA]
  refine ⟨(S.finite_toSet.image _), ?_⟩
  rw [Set.ncard_image_of_injective _ (Rat.HeightOneSpectrum.primesEquiv).injective,
    Set.ncard_coe_finset]
  apply even_of_nsmul_half_eq_zero
  have hsum := hS x
  rw [sumLocalInv_eq_sum ℚ _ (S := S) (fun v hv => by
    rw [brLocalization_fst_apply, ← finiteInvAt_eq_zero_iff]
    exact finiteInvAt_eq_zero_of_notMem_brauerSupport ℚ hv)] at hsum
  have hfin : ∑ v ∈ S, invMap (v.adicCompletion ℚ) ((brLocalization ℚ x).1 v) =
      S.card • ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
    rw [← Finset.sum_const]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [brLocalization_fst_apply]
    refine eq_half_of_two_torsion ?_ ?_
    · rw [← map_nsmul, ← map_nsmul, hx2, map_zero, map_zero]
    · exact (mem_brauerSupport ℚ).mp hv
  have hinf : ∑ w, infiniteInvMap w ((brLocalization ℚ x).2 w) =
      (if IsCoboundary2 (resC ℝ ε) then 0 else 1) • ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
    rw [Fintype.sum_unique, brLocalization_snd_apply,
      infiniteInvMap_of_isReal _ (isReal_rat _), AddMonoidHom.comp_apply]
    set y := realInv ((brCongr (InfinitePlace.Completion.ringEquivRealOfIsReal
      (isReal_rat (default : InfinitePlace ℚ)))).toAddMonoidHom
        (brBaseChange ℚ (default : InfinitePlace ℚ).Completion x)) with hy
    have hiff : y = 0 ↔ IsCoboundary2 (resC ℝ ε) := by
      rw [← brBaseChange_brClass_eq_zero_iff ℝ ε hε, ← hxdef,
        ← brBaseChange_infinite_eq_zero_iff (default : InfinitePlace ℚ), hy,
        map_eq_zero_iff _ realInv_injective, AddEquiv.coe_toAddMonoidHom,
        AddEquivClass.map_eq_zero_iff]
    split_ifs with hc
    · rw [zero_smul]; exact hiff.mpr hc
    · rw [one_smul]
      refine eq_half_of_two_torsion ?_ (fun h => hc (hiff.mp h))
      rw [hy, ← map_nsmul, ← map_nsmul, ← map_nsmul, hx2, map_zero, map_zero, map_zero]
  rw [hfin, hinf, ← add_smul] at hsum
  exact hsum

/-- **Leaf T14b′ (`PkgI6.BrauerReciprocity2C`) from the Kummer case of the second inequality.** -/
theorem brauerReciprocity2C_of_kummerIndexBound (h : KummerIndexBound) : BrauerReciprocity2C :=
  brauerReciprocity2C_of_sum fun x =>
    sumLocalInv_brLocalization_eq_zero_of_brLocalization_injective ℚ
      (fun E _ _ _ => brLocalization_injective_of_kummerIndexBound h E) x

end ZInQ.Contrib.BrauerT14T15
