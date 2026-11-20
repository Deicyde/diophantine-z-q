/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime (git blob 2962c592cb0ac70f6a1ebe41f2d11e2162115b9a, sha256 a09caf63be6474a73a2ee8917ed9b0c28d78d9cf113c5c12527c50959e2c9736).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CuspidalClass
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_transcendental_jqModC
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_coeffEmb_jq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_full_eq_of_prime
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_le
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqNModC
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_cuspZeroBar_ne_cuspInftyBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_isCusp_cuspZeroBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_isCusp_cuspInftyBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace AlgebraicCurve
end AlgebraicCurve
namespace IntermediateField
end IntermediateField

namespace P2MW.S_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open _root_.ModularCurve hiding dedekindPsi_prime
open _root_.AlgebraicCurve
open _root_.IntermediateField
open scoped Polynomial

noncomputable section

namespace DegAux



variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem prime' : ℓ.Prime := Fact.out

theorem dedekindPsi_prime : dedekindPsi ℓ = ℓ + 1 := by
  have hℓ : ℓ.Prime := Fact.out
  rw [dedekindPsi, hℓ.divisors, Finset.filter_true_of_mem, Finset.sum_pair hℓ.one_lt.ne, Nat.div_one,
    Nat.div_self hℓ.pos, add_comm]
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact squarefree_one
  · exact hℓ.squarefree

def jb : modularFunctionFieldBar ℓ := ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full ℓ)⟩

theorem coe_jb : (jb ℓ : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := coeffEmb_jq (AlgebraicClosure ℚ)

theorem bar_eq_restrictScalars :
    modularFunctionFieldBar ℓ = ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯).restrictScalars (AlgebraicClosure ℚ) := by
  have hℓ : ℓ.Prime := Fact.out
  show laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull ℓ) = _
  rw [full_eq_of_prime hℓ, laurentBaseChange_modularFunctionField]
  exact (adjoin_simple_adjoin_simple (AlgebraicClosure ℚ) (jqModC (AlgebraicClosure ℚ)) (jqNModC (AlgebraicClosure ℚ) ℓ)).symm

def σa : RatFunc (AlgebraicClosure ℚ) ≃ₐ[(AlgebraicClosure ℚ)] (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯ :=
  RatFunc.algEquivOfTranscendental (jqModC (AlgebraicClosure ℚ)) (transcendental_jqModC (AlgebraicClosure ℚ))

theorem coe_σa_X : ((σa (RatFunc.X : RatFunc (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) :=
  RatFunc.algEquivOfTranscendental_X (jqModC (AlgebraicClosure ℚ)) (transcendental_jqModC (AlgebraicClosure ℚ))

theorem mem_bar_iff (x : LaurentSeries (AlgebraicClosure ℚ)) :
    x ∈ modularFunctionFieldBar ℓ ↔ x ∈ (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯ := by
  rw [bar_eq_restrictScalars ℓ, mem_restrictScalars]

def jTr : ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯) ≃+* modularFunctionFieldBar ℓ where
  toFun x := ⟨x, (mem_bar_iff ℓ _).mpr x.2⟩
  invFun y := ⟨y, (mem_bar_iff ℓ _).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private theorem transfer_subfield_coe
    {E : Type*} [Field E] (S T : Subfield E)
    (h : ∀ x : E, x ∈ S ↔ x ∈ T) (x : S) :
    (({ toFun := fun a => ⟨a, (h a).mp a.2⟩
        invFun := fun a => ⟨a, (h a).mpr a.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl } : S ≃+* T) x : E) = x := by
  rfl -- [port] opaque generic coercion rule, same underlying map

theorem coe_jTr (x : (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯) :
    ((jTr ℓ x : modularFunctionFieldBar ℓ) : LaurentSeries (AlgebraicClosure ℚ)) = x := by
  exact transfer_subfield_coe
    ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯).toSubfield
    (modularFunctionFieldBar ℓ).toSubfield
    (fun x => (mem_bar_iff ℓ x).symm) x -- [port] do not normalize concrete subtype-transfer proof

def φ : RatFunc (AlgebraicClosure ℚ) →+* modularFunctionFieldBar ℓ :=
  (jTr ℓ).toRingHom.comp
    ((algebraMap ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯) ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯)).comp (σa).toRingEquiv.toRingHom)

theorem φ_apply (x : RatFunc (AlgebraicClosure ℚ)) :
    φ ℓ x = jTr ℓ (algebraMap ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯) ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯) (σa x)) := rfl

theorem coe_algebraMap_tower (y : (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯) :
    ((algebraMap ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯) ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯) y : (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯) :
      LaurentSeries (AlgebraicClosure ℚ)) = y := rfl

theorem coe_φ (x : RatFunc (AlgebraicClosure ℚ)) :
    ((φ ℓ x : modularFunctionFieldBar ℓ) : LaurentSeries (AlgebraicClosure ℚ)) = (σa x : LaurentSeries (AlgebraicClosure ℚ)) := by
  rw [φ_apply, coe_jTr, coe_algebraMap_tower]

private theorem same_value_preserves_constants
    {K A B : Type*} [Field K] [Field A] [Field B]
    [Algebra K A] [Algebra K B] (f : A →+* B)
    {E : Type*} [Field E] [Algebra K E]
    (i : A →ₐ[K] E) (j : B →ₐ[K] E)
    (hf : ∀ x : A, j (f x) = i x) (k : K) :
    f (algebraMap K A k) = algebraMap K B k := by
  apply j.injective
  change j (f (algebraMap K A k)) = j (algebraMap K B k)
  rw [hf, i.commutes, j.commutes] -- [port] generic same-value equation instead of concrete subtype reduction

theorem φ_algebraMap (k : (AlgebraicClosure ℚ)) : φ ℓ (algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) k) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ) k := by
  exact same_value_preserves_constants
    (φ ℓ) ((((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯).val).comp (σa).toAlgHom)
    ((modularFunctionFieldBar ℓ).val)
    (fun x => coe_φ ℓ x) k -- [port] same original map and scalar-field structures

theorem φ_X : φ ℓ (RatFunc.X : RatFunc (AlgebraicClosure ℚ)) = jb ℓ := by
  apply Subtype.ext
  rw [coe_φ, coe_jb, coe_σa_X]

abbrev algRatFunc : Algebra (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ) := (φ ℓ).toAlgebra

attribute [local instance] algRatFunc

theorem algebraMap_eq : algebraMap (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ) = φ ℓ := rfl

theorem isScalarTower_ratFunc : IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ) :=
  IsScalarTower.of_algebraMap_eq fun k => (φ_algebraMap ℓ k).symm

attribute [local instance] isScalarTower_ratFunc

theorem he_compat :
    (algebraMap (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ)).comp
        (σa.symm.toRingEquiv : (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯ ≃+* RatFunc (AlgebraicClosure ℚ)).toRingHom
      = (jTr ℓ).toRingHom.comp (algebraMap ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯) ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯)) := by
  apply RingHom.ext
  intro y
  show φ ℓ (σa.symm y) = jTr ℓ (algebraMap _ _ y)
  rw [φ_apply, AlgEquiv.apply_symm_apply]

theorem finite_ratFunc : Module.Finite (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree ℓ hℓ.squarefree hℓ.one_lt
  haveI := finiteDimensional_adjoin_jqNModC (AlgebraicClosure ℚ) data
  exact Module.Finite.of_equiv_equiv (σa.symm.toRingEquiv : (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯ ≃+* RatFunc (AlgebraicClosure ℚ)) (jTr ℓ)
    (he_compat ℓ)

attribute [local instance] finite_ratFunc

theorem finrank_le : Module.finrank (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ) ≤ ℓ + 1 := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree ℓ hℓ.squarefree hℓ.one_lt
  rw [← Algebra.finrank_eq_of_equiv_equiv (σa.symm.toRingEquiv : (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯ ≃+* RatFunc (AlgebraicClosure ℚ)) (jTr ℓ)
    (he_compat ℓ), ← dedekindPsi_prime ℓ]
  exact finrank_adjoin_jqNModC_le (AlgebraicClosure ℚ) data

theorem isSeparable_ratFunc : Algebra.IsSeparable (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ) :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

attribute [local instance] isSeparable_ratFunc

theorem restrict_eq_of_isCusp (u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ)) (hu : IsCusp (jb ℓ) u) :
    u.restrict (RatFunc (AlgebraicClosure ℚ)) = (cuspInftyBar ℓ).restrict (RatFunc (AlgebraicClosure ℚ)) := by
  have key : ∀ u' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ), IsCusp (jb ℓ) u' →
      ∀ p : IsDedekindDomain.HeightOneSpectrum (AlgebraicClosure ℚ)[X],
        u'.restrict (RatFunc (AlgebraicClosure ℚ)) ≠ Place.ofHeightOneSpectrum p := by
    intro u' hu' p heq
    apply hu'
    have hX : (RatFunc.X : RatFunc (AlgebraicClosure ℚ)) ∈ (u'.restrict (RatFunc (AlgebraicClosure ℚ))).toValuationSubring := by
      rw [heq, Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff,
        ← RatFunc.algebraMap_X]
      exact p.valuation_le_one _
    rw [Place.mem_restrict_iff, algebraMap_eq, φ_X] at hX
    exact hX
  exact RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum (key u hu)
    (key _ (isCusp_cuspInftyBar ℓ))

theorem e_infty : ((cuspInftyBar ℓ).ramificationIndex (RatFunc (AlgebraicClosure ℚ)) : ℤ) = 1 ∧
    ((cuspInftyBar ℓ).restrict (RatFunc (AlgebraicClosure ℚ))).ord RatFunc.X = -1 := by
  have h := (cuspInftyBar ℓ).ord_restrict (F := RatFunc (AlgebraicClosure ℚ)) RatFunc.X
  rw [algebraMap_eq, φ_X] at h
  have hj : (cuspInftyBar ℓ).ord (jb ℓ) = -1 := ord_cuspInftyBar_coeffEmb_jq ℓ
  rw [hj] at h
  have epos : (0 : ℤ) < (cuspInftyBar ℓ).ramificationIndex (RatFunc (AlgebraicClosure ℚ)) := by
    exact_mod_cast (cuspInftyBar ℓ).ramificationIndex_pos (F := RatFunc (AlgebraicClosure ℚ))
  have h1 : ((cuspInftyBar ℓ).ramificationIndex (RatFunc (AlgebraicClosure ℚ)) : ℤ) *
      (-((cuspInftyBar ℓ).restrict (RatFunc (AlgebraicClosure ℚ))).ord RatFunc.X) = 1 := by linarith
  have he := Int.eq_one_of_mul_eq_one_right epos.le h1
  refine ⟨he, ?_⟩
  rw [he, one_mul] at h1
  linarith

theorem e_zero (hw : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ)) :
    ((cuspZeroBar ℓ).ramificationIndex (RatFunc (AlgebraicClosure ℚ)) : ℤ) = ℓ := by
  have h := (cuspZeroBar ℓ).ord_restrict (F := RatFunc (AlgebraicClosure ℚ)) RatFunc.X
  rw [algebraMap_eq, φ_X, restrict_eq_of_isCusp ℓ _ (isCusp_cuspZeroBar ℓ hw), (e_infty ℓ).2] at h
  have hj : (cuspZeroBar ℓ).ord (jb ℓ) = -ℓ := ord_cuspZeroBar_coeffEmb_jq ℓ hw
  rw [hj] at h
  linarith

theorem eq_cuspInftyBar_or_eq_cuspZeroBar (hw : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ))
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ)) (hc : IsCusp (jb ℓ) w) :
    w = cuspInftyBar ℓ ∨ w = cuspZeroBar ℓ := by
  classical
  by_contra hnot
  have h1 : w ≠ cuspInftyBar ℓ := fun h => hnot (Or.inl h)
  have h2 : w ≠ cuspZeroBar ℓ := fun h => hnot (Or.inr h)
  have hℓ : ℓ.Prime := Fact.out
  have hne : cuspZeroBar ℓ ≠ cuspInftyBar ℓ := cuspZeroBar_ne_cuspInftyBar ℓ hw hℓ.one_lt
  have r0 := restrict_eq_of_isCusp ℓ _ (isCusp_cuspZeroBar ℓ hw)
  have rw' := restrict_eq_of_isCusp ℓ _ hc
  have hS : ∀ u ∈ ({cuspInftyBar ℓ, cuspZeroBar ℓ, w} : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ))),
      u.restrict (RatFunc (AlgebraicClosure ℚ)) = (cuspInftyBar ℓ).restrict (RatFunc (AlgebraicClosure ℚ)) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · rfl
    · exact r0
    · exact rw'
  have hsum := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank _ _ hS
  rw [Finset.sum_insert (by simp [hne.symm, Ne.symm h1]), Finset.sum_insert (by simp [Ne.symm h2]),
    Finset.sum_singleton] at hsum
  have hrank : (Module.finrank (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ) : ℤ) ≤ ℓ + 1 := by
    exact_mod_cast finrank_le ℓ
  have e1 := (e_infty ℓ).1
  have e0 := e_zero ℓ hw
  have ew : (1 : ℤ) ≤ w.ramificationIndex (RatFunc (AlgebraicClosure ℚ)) := by
    exact_mod_cast w.ramificationIndex_pos (F := RatFunc (AlgebraicClosure ℚ))
  have f1 : (1 : ℤ) ≤ (cuspInftyBar ℓ).inertiaDeg (RatFunc (AlgebraicClosure ℚ)) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc (AlgebraicClosure ℚ)) (cuspInftyBar ℓ)
  have f0 : (1 : ℤ) ≤ (cuspZeroBar ℓ).inertiaDeg (RatFunc (AlgebraicClosure ℚ)) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc (AlgebraicClosure ℚ)) (cuspZeroBar ℓ)
  have fw : (1 : ℤ) ≤ w.inertiaDeg (RatFunc (AlgebraicClosure ℚ)) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc (AlgebraicClosure ℚ)) w
  have p0 : (ℓ : ℤ) ≤ ((cuspZeroBar ℓ).ramificationIndex (RatFunc (AlgebraicClosure ℚ)) : ℤ) *
      ((cuspZeroBar ℓ).inertiaDeg (RatFunc (AlgebraicClosure ℚ)) : ℤ) := by
    rw [e0]; nlinarith
  have pw : (1 : ℤ) ≤ (w.ramificationIndex (RatFunc (AlgebraicClosure ℚ)) : ℤ) * (w.inertiaDeg (RatFunc (AlgebraicClosure ℚ)) : ℤ) :=
    one_le_mul_of_one_le_of_one_le ew fw
  rw [e1, one_mul] at hsum
  linarith

theorem le_finrank : ℓ + 1 ≤ Module.finrank (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ) := by
  classical
  have hw := isFrickeAutFull_frickeInvolutionFull_prime ℓ
  have hℓ : ℓ.Prime := Fact.out
  have hne : cuspZeroBar ℓ ≠ cuspInftyBar ℓ := cuspZeroBar_ne_cuspInftyBar ℓ hw hℓ.one_lt
  have r0 := restrict_eq_of_isCusp ℓ _ (isCusp_cuspZeroBar ℓ hw)
  have hS : ∀ u ∈ ({cuspInftyBar ℓ, cuspZeroBar ℓ} : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ))),
      u.restrict (RatFunc (AlgebraicClosure ℚ)) = (cuspInftyBar ℓ).restrict (RatFunc (AlgebraicClosure ℚ)) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · rfl
    · exact r0
  have hsum := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank _ _ hS
  rw [Finset.sum_insert (by simp [hne.symm]), Finset.sum_singleton] at hsum
  have e1 := (e_infty ℓ).1
  have e0 := e_zero ℓ hw
  have f1 : (1 : ℤ) ≤ (cuspInftyBar ℓ).inertiaDeg (RatFunc (AlgebraicClosure ℚ)) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc (AlgebraicClosure ℚ)) (cuspInftyBar ℓ)
  have f0 : (1 : ℤ) ≤ (cuspZeroBar ℓ).inertiaDeg (RatFunc (AlgebraicClosure ℚ)) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc (AlgebraicClosure ℚ)) (cuspZeroBar ℓ)
  have p0 : (ℓ : ℤ) ≤ ((cuspZeroBar ℓ).ramificationIndex (RatFunc (AlgebraicClosure ℚ)) : ℤ) *
      ((cuspZeroBar ℓ).inertiaDeg (RatFunc (AlgebraicClosure ℚ)) : ℤ) := by
    rw [e0]; nlinarith
  rw [e1, one_mul] at hsum
  have : ((ℓ + 1 : ℕ) : ℤ) ≤ (Module.finrank (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ) : ℤ) := by
    push_cast; linarith
  exact_mod_cast this

theorem finrank_tower_eq : Module.finrank ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯) ((AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯⟮jqNModC (AlgebraicClosure ℚ) ℓ⟯) =
    Module.finrank (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar ℓ) :=
  Algebra.finrank_eq_of_equiv_equiv (σa.symm.toRingEquiv : (AlgebraicClosure ℚ)⟮jqModC (AlgebraicClosure ℚ)⟯ ≃+* RatFunc (AlgebraicClosure ℚ)) (jTr ℓ) (he_compat ℓ)

end DegAux

open DegAux in

theorem solution (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))) (IntermediateField.adjoin (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))) ({jqNModC (AlgebraicClosure ℚ) ℓ} : Set (LaurentSeries (AlgebraicClosure ℚ)))) = ℓ + 1 := by
  apply le_antisymm
  · have hℓ : ℓ.Prime := Fact.out
    obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree ℓ hℓ.squarefree hℓ.one_lt
    simpa [DegAux.dedekindPsi_prime ℓ] using finrank_adjoin_jqNModC_le (AlgebraicClosure ℚ) data
  · have h := DegAux.le_finrank ℓ
    rw [← DegAux.finrank_tower_eq ℓ] at h
    exact h
