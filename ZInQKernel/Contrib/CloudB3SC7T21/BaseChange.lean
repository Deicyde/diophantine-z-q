/-
Portions of this file (`exists_semilocal_coeffs`) are adapted from Tau Ceti:
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSE-TauCeti.
Authors of the adapted portion: The Tau Ceti contributors

Adaptation: `exists_semilocal_coeffs` retains the integral-components specialization
of `exists_semilocalHom_sum_tmul_eq` from Tau Ceti revision
5a01f5fe3621126cccf9ba22e700493cbc7b7156. The surrounding original project proof
is reused from f597c34cd6f6a43e076138209c638c47978753f5; imports are relocated.
-/
import ZInQKernel.Contrib.CloudB3SC7T21.Local

/-!
# t21-proof: `τ̂(Ô_K)` is integral at every place

Task t21-proof. For `a ∈ Ô_{K}` (`K = ℚ(√−n)`), the component of `τ̂(a) ∈ ℍ[𝔸ᶠ_ℚ]` at a place `w`
is a `ℤ_p`-combination of the `τ(b_i)`, `b_i` the integral basis of `𝓞 K`. The proof follows Tau
Ceti's surjectivity proof of the finite-adele base change (`FiniteBaseChange.lean`): the private
lemma `exists_semilocalHom_sum_tmul_eq` is reproduced here (`exists_semilocal_coeffs`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open ZInQ.Contrib.TYZDecomp.H29Split IsDedekindDomain NumberField TauCeti.GlobalNumberFields TauCeti
open IsDedekindDomain.HeightOneSpectrum
open scoped Quaternion TensorProduct FiniteAdeleExtension AdicCompletionExtension
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

/-- Tau Ceti's `exists_semilocalHom_sum_tmul_eq` (private in `FiniteBaseChange.lean`), integral
case: integral components above `v` are the semilocal image of `∑ c_i ⊗ b_i` with `c_i ∈ 𝒪_v`. -/
theorem exists_semilocal_coeffs (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K))
    (z : (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) →
      w.1.adicCompletion L) (hz : ∀ w, z w ∈ w.1.adicCompletionIntegers L) :
    ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → v.adicCompletion K,
      semilocalHom L v (∑ i, c i ⊗ₜ[K] (RingOfIntegers.basis L i : L)) = z ∧
      ∀ i, c i ∈ v.adicCompletionIntegers K := by
  classical
  let b := RingOfIntegers.basis L
  obtain ⟨ζ, hζ⟩ := (integralSemilocalEquiv L v).surjective fun w ↦ ⟨z w, hz w⟩
  have hspan : Submodule.span (v.adicCompletionIntegers K)
      (Set.range fun i ↦ (1 : v.adicCompletionIntegers K) ⊗ₜ[𝓞 K] b i) = ⊤ := by
    have h := Submodule.baseChange_span (R := 𝓞 K) (v.adicCompletionIntegers K) (Set.range b)
    rw [Submodule.span_eq_top_of_span_eq_top ℤ (𝓞 K) _ b.span_eq, Submodule.baseChange_top,
      ← Set.range_comp] at h
    exact h.symm
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    (hspan ▸ Submodule.mem_top : ζ ∈ Submodule.span _ _)
  refine ⟨fun i ↦ c i, ?_, fun i ↦ (c i).2⟩
  have h := integralSemilocalEquiv_fieldCompatibility ζ
  rw [hζ, ← hc, map_sum] at h
  simp_rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    integralSemilocalToField_tmul, coe_semilocalEquiv] at h
  exact h

/-- The integral basis of `𝓞 K`, in `K = ℚ(√−n)`. -/
abbrev bK (n : ℕ) [NeZero n] (i : Module.Free.ChooseBasisIndex ℤ (𝓞 (QNeg n))) : QNeg n :=
  (RingOfIntegers.basis (QNeg n) i : QNeg n)

theorem pe_mem_Zp (w : HeightOneSpectrum (𝓞 ℚ)) {x : w.adicCompletion ℚ}
    (hx : x ∈ w.adicCompletionIntegers ℚ) : ‖pe w x‖ ≤ 1 :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn w).mapsTo hx

theorem ev_mem_Zp_of_integral (w : HeightOneSpectrum (𝓞 ℚ)) {a : AQ}
    (ha : a ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ) : ‖ev w a‖ ≤ 1 :=
  pe_mem_Zp w (ha w)

/-- **`τ̂(a)` for `a ∈ Ô_K` is integral at `w`**: a `ℤ_p`-combination of the `τ(b_i)`. -/
theorem tauHat_integral (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ])
    {a : FiniteAdeleRing (𝓞 (QNeg n)) (QNeg n)}
    (ha : a ∈ FiniteAdeleRing.integralAdeles (𝓞 (QNeg n)) (QNeg n))
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 (QNeg n)) → ℚ_[Pw w], (∀ i, ‖c i‖ ≤ 1) ∧
      piQ w (tauHat n τ a) = ∑ i, c i • qp (Pw w : ℕ) (τ (bK n i)) := by
  classical
  let e := finiteAdeleBaseChangeAlgEquiv ℚ (QNeg n)
  set t := e.symm a with ht
  let B := (integralBasis (QNeg n)).baseChange AQ
  have hb : ∀ i, integralBasis (QNeg n) i = bK n i := fun i => integralBasis_apply _ i
  have htsum : t = ∑ i, B.repr t i ⊗ₜ[ℚ] bK n i := by
    conv_lhs => rw [← B.sum_repr t]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, hb]
  -- the coefficients are integral at `w`
  have hint : ∀ i, B.repr t i w ∈ w.adicCompletionIntegers ℚ := by
    intro i
    let z : (w' : {w' : HeightOneSpectrum (𝓞 (QNeg n)) // w'.asIdeal.LiesOver w.asIdeal}) →
        w'.1.adicCompletion (QNeg n) := fun w' => a w'.1
    obtain ⟨c, hcz, hci⟩ := exists_semilocal_coeffs ℚ (QNeg n) w z (fun w' => ha w'.1)
    let f := (FiniteAdeleRing.proj ℚ w).toAlgHom.toLinearMap
    let T := TensorProduct.map f (LinearMap.id : QNeg n →ₗ[ℚ] QNeg n)
    have hea : finiteAdeleBaseChangeHom ℚ (QNeg n) t = a := by
      rw [ht, ← finiteAdeleBaseChangeAlgEquiv_toAlgHom, AlgEquiv.toAlgHom_eq_coe]
      exact e.apply_symm_apply a
    have h1 : semilocalHom (QNeg n) w (T t) = z := by
      funext w'
      rw [← finiteAdeleBaseChangeHom_apply ℚ (QNeg n) t w w', hea]
    have h2 : T t = ∑ j, c j ⊗ₜ[ℚ] (RingOfIntegers.basis (QNeg n) j : QNeg n) :=
      semilocalHom_injective (QNeg n) w (h1.trans hcz.symm)
    let Bw := (integralBasis (QNeg n)).baseChange (w.adicCompletion ℚ)
    have hcoord : ∀ s : AQ ⊗[ℚ] QNeg n, Bw.repr (T s) i = B.repr s i w := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp only [T, TensorProduct.map_tmul, LinearMap.id_apply, B, Bw,
          Module.Basis.baseChange_repr_tmul]
        exact (f.map_smul ((integralBasis (QNeg n)).repr y i) x).symm.trans
          (FiniteAdeleRing.proj_apply w _)
      | add x y hx hy =>
        simp only [map_add, Finsupp.add_apply, hx, hy]
        rfl
    have h3 : Bw.repr (∑ j, c j ⊗ₜ[ℚ] (RingOfIntegers.basis (QNeg n) j : QNeg n)) i = c i := by
      simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
      simp_rw [← integralBasis_apply, Bw, Module.Basis.baseChange_repr_tmul,
        Module.Basis.repr_self, Finsupp.single_apply]
      simp
    rw [← hcoord, h2, h3]
    exact hci i
  refine ⟨fun i => ev w (B.repr t i), fun i => pe_mem_Zp w (hint i), ?_⟩
  have htau : tauHat n τ a = ∑ i, B.repr t i • qι (τ (bK n i)) := by
    simp only [tauHat, RingHom.coe_comp, Function.comp_apply]
    change (AlgHom.liftEquiv ℚ AQ (QNeg n) ℍ[AQ] ((qι).comp τ)) t = _
    conv_lhs => rw [htsum]
    rw [map_sum]
    rfl
  rw [htau, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, piQ_algebraMap, piQ_qι, Quaternion.coe_mul_eq_smul]

end ZInQ.Contrib.T21Proof
