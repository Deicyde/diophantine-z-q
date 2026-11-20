import ZInQKernel.Contrib.OneProof.RC.O7Character.Basis
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Genus
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.RayClass.Exact
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant

/-! The elementary conductor-one descent for tex 8215–8217 and 9182–9193. -/

noncomputable section

open scoped NumberField
open NumberField
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.O7Character

open O7Actual

variable {F : Type} [Field F] [NumberField F]

private theorem principal_norm_formula {d : ℤ} (Q : QuadraticBasis F d)
    (hneg : d < 0) (α : 𝓞 F) :
    ∃ a b : ℤ, 4 * (Ideal.absNorm (Ideal.span {α}) : ℤ) = a ^ 2 - d * b ^ 2 := by
  obtain ⟨i, j, hij⟩ := Q.spans α
  let z : QuadraticAlgebra ℚ (d : ℚ) 0 := ⟨(i : ℚ) + (j : ℚ) / 2, (j : ℚ) / 2⟩
  have hz : Q.model z = (α : F) := by
    rw [hij]
    have hform : z = algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (i : ℚ) +
        ((j : ℚ) / 2) • ((1 : QuadraticAlgebra ℚ (d : ℚ) 0) + QuadraticAlgebra.omega) := by
      apply QuadraticAlgebra.ext <;>
        simp [z, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    rw [hform, map_add, Q.model.commutes, Algebra.smul_def, map_mul, Q.model.commutes,
      map_add, map_one]
    simp only [eq_ratCast (algebraMap ℚ F), Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
    ring
  have hn : 4 * Algebra.norm ℤ α = (2 * i + j) ^ 2 - d * j ^ 2 := by
    have hnorm : Algebra.norm ℚ z = z.norm :=
      QuadraticAlgebra.det_toLinearMap_eq_norm z
    have he := Algebra.norm_eq_of_algEquiv Q.model z
    rw [hz, ← Algebra.coe_norm_int, hnorm, QuadraticAlgebra.norm_def] at he
    have h : 4 * ((Algebra.norm ℤ α : ℤ) : ℚ) =
        (2 * (i : ℚ) + j) ^ 2 - (d : ℚ) * (j : ℚ) ^ 2 := by
      dsimp [z] at he
      rw [he]
      ring
    exact_mod_cast h
  have hp : 0 ≤ Algebra.norm ℤ α := by
    have := mul_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg j)
    nlinarith [sq_nonneg (2 * i + j)]
  refine ⟨2 * i + j, j, ?_⟩
  rwa [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg hp]

private theorem chiD_principal {d hstar : ℤ} (Q : QuadraticBasis F d) (hneg : d < 0)
    (hdvd : hstar ∣ d) (hodd : Odd hstar) (α : 𝓞 F)
    (hcop : (Ideal.absNorm (Ideal.span {α})).Coprime hstar.natAbs) :
    chiD hstar (Ideal.absNorm (Ideal.span {α})) = 1 := by
  obtain ⟨a, b, he⟩ := principal_norm_formula Q hneg α
  have hmod : 4 * (Ideal.absNorm (Ideal.span {α}) : ℤ) ≡ a ^ 2 [ZMOD hstar.natAbs] := by
    apply Int.modEq_iff_dvd.mpr
    rw [Int.natAbs_dvd, he, sub_sub_cancel]
    exact dvd_mul_of_dvd_left hdvd _
  have heq := jacobiSym.mod_left' hmod
  rw [jacobiSym.mul_left, jacobiSym.at_four (Int.natAbs_odd.mpr hodd), one_mul] at heq
  change jacobiSym _ _ = 1
  rw [heq]
  apply jacobiSym.sq_one'
  by_contra ha
  let : NeZero hstar.natAbs := ⟨fun h => by
    have hz : hstar = 0 := Int.natAbs_eq_zero.mp h
    simp [hz] at hodd⟩
  have hz := jacobiSym.eq_zero_iff_not_coprime.mpr ha
  have hnonzero : jacobiSym ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℤ) hstar.natAbs ≠ 0 :=
    jacobiSym.ne_zero (by exact (Int.gcd_natCast_natCast _ _).trans hcop.gcd_eq_one)
  exact hnonzero (by rw [heq, jacobiSym.pow_left, hz]; norm_num)

private theorem exists_picClass_coprime (c : ℕ) (hc : c ≠ 0)
    (t : Pic (conductorOrder F 1)) :
    ∃ J : integralIdealsPrimeTo (conductorOrder F 1).conductorModulus,
      (conductorOrder F 1).picClass J = t ∧ (Ideal.absNorm J.val).Coprime c := by
  let O := conductorOrder F 1
  let 𝔪 : Modulus F :=
    ⟨Ideal.span {(c : 𝓞 F)}, by simpa [Ideal.span_singleton_eq_bot] using hc, ∅⟩
  have hO : O = maximalNumberFieldOrder F := by
    ext x
    constructor
    · exact fun hx => conductorOrderSubalgebra_le_integralClosure F 1 hx
    · intro hx
      refine ⟨0, ⟨x, hx⟩, ?_⟩
      simp only [Int.cast_zero, zero_add, Nat.cast_one, one_mul]
      rfl
  have hdiv : O.conductorModulus ∣ 𝔪 := by
    rw [hO, conductorModulus_maximalNumberFieldOrder]
    exact Modulus.one_dvd _
  obtain ⟨r, hr⟩ := O.rayClassToPic_surjective t
  obtain ⟨u, hu⟩ := classMap_surjective hdiv r
  obtain ⟨I, rfl⟩ := idealClass_surjective 𝔪 u
  refine ⟨integralIdealsPrimeToInclusion hdiv I, ?_, ?_⟩
  · rw [← O.rayClassToPic_idealClass, ← classMap_idealClass, hu, hr]
  · change (Ideal.absNorm I.val).Coprime c
    refine Nat.coprime_of_dvd fun p hp hpI hpc => ?_
    obtain ⟨P, hP, hPp, hPI⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I.val hpI
    have hcP : (c : 𝓞 F) ∈ P := by
      have hz : (c : ℤ) ∈ P.under ℤ := hPp ▸
        (Ideal.mem_span_singleton.mpr (Int.natCast_dvd.mpr hpc))
      simpa using hz
    have hIcop := (Modulus.isCoprimeTo_iff_sup_eq_top.mp
      (Modulus.mem_integralIdealsPrimeTo.mp I.prop)).2
    exact hP.ne_top (top_unique (hIcop ▸ sup_le (Ideal.le_of_dvd hPI)
      ((Ideal.span_singleton_le_iff_mem _).mpr hcP)))

/-- The Jacobi symbol of the ideal norm descends to the actual conductor-one
Picard group for a negative discriminant `D * hstar ≡ 1 mod 8`. In
particular this applies to all `D > 1` in the odd filter. -/
theorem normCharacterDescent {D hstar : ℤ} (h₂ : Module.finrank ℚ F = 2)
    (hdisc : discr F = D * hstar) (hneg : D * hstar < 0) (height : (D * hstar) % 8 = 1) :
    NormCharacterDescent F hstar := by
  classical
  let O := conductorOrder F 1
  let S : Submonoid (integralIdealsPrimeTo O.conductorModulus) :=
    { carrier := {J | (Ideal.absNorm J.val).Coprime hstar.natAbs}
      one_mem' := by change (Ideal.absNorm 1).Coprime _; simp
      mul_mem' := fun {I J} hI hJ => by
        change (Ideal.absNorm (I.val * J.val)).Coprime _
        rw [map_mul]
        exact (Nat.coprime_mul_iff_left.mpr ⟨hI, hJ⟩) }
  let π := O.picClass.comp S.subtype
  have hπ : Function.Surjective π := by
    intro t
    obtain ⟨J, hJ, hc⟩ := exists_picClass_coprime hstar.natAbs
      (by simpa using (show hstar ≠ 0 by rintro rfl; simp at hneg)) t
    exact ⟨⟨J, hc⟩, hJ⟩
  have hv (J : S) : IsUnit (chiD hstar (Ideal.absNorm J.val.val)) := by
    change IsUnit (jacobiSym (Ideal.absNorm J.val.val : ℤ) hstar.natAbs)
    have hcop : (Ideal.absNorm J.val.val).Coprime hstar.natAbs := J.prop
    have hs := jacobiSym.sq_one (a := (Ideal.absNorm J.val.val : ℤ)) (b := hstar.natAbs)
      (by exact (Int.gcd_natCast_natCast _ _).trans hcop.gcd_eq_one)
    exact isUnit_iff_exists_inv.mpr ⟨_, by simpa [sq] using hs⟩
  let ψ : S →* ℤˣ :=
    { toFun := fun J => (hv J).unit
      map_one' := by apply Units.ext; simp [chiD]
      map_mul' := fun I J => by
        apply Units.ext
        simp only [IsUnit.unit_spec, Units.val_mul]
        change chiD hstar (Ideal.absNorm (I.val.val * J.val.val)) = _
        simp [chiD, jacobiSym.mul_left] }
  have hker (J : S) (hJ : π J = 1) : ψ J = 1 := by
    obtain ⟨α, _, hα⟩ := (O.picClass_eq_one_iff J.val).mp hJ
    have hcop : (Ideal.absNorm J.val.val).Coprime hstar.natAbs := J.prop
    rw [hα] at hcop
    have hodd : Odd hstar := by
      have h := Int.odd_iff.mpr (show (D * hstar) % 2 = 1 by omega)
      exact (Int.odd_mul.mp h).2
    apply Units.ext
    change (↑((hv J).unit) : ℤ) = 1
    rw [IsUnit.unit_spec, hα]
    have Q : QuadraticBasis F (D * hstar) := by
      simpa only [neg_neg] using (quadraticBasis (m := -hstar) h₂
        (by simpa only [neg_neg] using hdisc) (by simpa only [neg_neg] using hneg)
        (by rw [neg_neg]; omega))
    exact chiD_principal Q hneg (dvd_mul_left _ _) hodd α hcop
  have hf (I J : S) (hIJ : π I = π J) : ψ I = ψ J := by
    obtain ⟨M, hM⟩ := hπ (π I)⁻¹
    have h1 := hker (I * M) (by rw [map_mul, hM, mul_inv_cancel])
    have h2 := hker (J * M) (by rw [map_mul, ← hIJ, hM, mul_inv_cancel])
    rw [map_mul] at h1 h2
    exact mul_right_cancel (h1.trans h2.symm)
  let rep (t : Pic O) : S := (hπ t).choose
  have hrep (t : Pic O) : π (rep t) = t := (hπ t).choose_spec
  let χ : Pic O →* ℤˣ :=
    { toFun := fun t => ψ (rep t)
      map_one' := hker _ (hrep _)
      map_mul' := fun t u => (hf (rep (t * u)) (rep t * rep u)
        (by rw [hrep, map_mul, hrep, hrep])).trans (map_mul ψ _ _) }
  refine ⟨χ, fun J hJ => ?_⟩
  let J' : S := ⟨J, hJ⟩
  have he : χ (O.picClass J) = ψ J' := hf _ _ (hrep _)
  rw [he]
  exact IsUnit.unit_spec (hv J')

end ZInQ.Manuscript.RC.O7Character
