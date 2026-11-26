import ZInQKernel.Contrib.OneProof.ShimuraSteps

/-! # Rational intertwining for Shimura's quotient -/

noncomputable section

namespace ShimuraSteps.Quotient

open scoped TensorProduct
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar R16Thm1

/-- Rational homomorphisms, in the same tensor order as `AbVar.End0`. -/
abbrev Hom0 (J A : AbVar ℚ) := ℚ ⊗[ℤ] AbVar.Hom J A

/-- The canonical map from integral to rational homomorphisms. -/
def hom0Inclusion (J A : AbVar ℚ) : AbVar.Hom J A →ₗ[ℤ] Hom0 J A :=
  TensorProduct.mk ℤ ℚ (AbVar.Hom J A) 1

variable {J A B : AbVar ℚ}

private def compLinear : AbVar.Hom J A →ₗ[ℤ] AbVar.Hom A B →ₗ[ℤ] AbVar.Hom J B :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => AddMonoidHom.toIntLinearMap
        { toFun := fun g => comp f g
          map_zero' := Hom.ext' (by simp)
          map_add' := fun g g' => Hom.ext' (by simp [MonObj.comp_mul]) }
      map_zero' := LinearMap.ext fun g => Hom.ext' (by simp)
      map_add' := fun f f' => LinearMap.ext fun g => Hom.ext' (by simp [MonObj.mul_comp]) }

/-- Composition in `Hom⁰` is the scalar extension of composition. In particular,
postcomposition by a rational endomorphism acts on rational homomorphisms. -/
def comp0 : Hom0 J A →ₗ[ℚ] Hom0 A B →ₗ[ℚ] Hom0 J B :=
  TensorProduct.curry <|
    (TensorProduct.AlgebraTensorModule.lTensor ℚ ℚ (TensorProduct.lift compLinear)).comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange ℤ ℚ
        (AbVar.Hom J A) (AbVar.Hom A B)).symm.toLinearMap

@[simp] theorem comp0_tmul (r s : ℚ) (f : AbVar.Hom J A) (g : AbVar.Hom A B) :
    comp0 (r ⊗ₜ[ℤ] f) (s ⊗ₜ[ℤ] g) = (r * s) ⊗ₜ[ℤ] comp f g := by
  change (TensorProduct.AlgebraTensorModule.lTensor ℚ ℚ (TensorProduct.lift compLinear))
    ((TensorProduct.AlgebraTensorModule.distribBaseChange ℤ ℚ
      (AbVar.Hom J A) (AbVar.Hom A B)).symm ((r ⊗ₜ f) ⊗ₜ (s ⊗ₜ g))) = _
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
  rfl

/-- The canonical map is injective by torsion-freeness of integral homomorphisms. -/
theorem hom0Inclusion_injective (J A : AbVar ℚ) :
    Function.Injective (hom0Inclusion J A) := by
  let S := nonZeroDivisors ℤ
  let T := hom0Inclusion J A
  let : IsLocalizedModule S T :=
    IsLocalization.tensorProduct_isLocalizedModule S ℚ
  intro f g h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S T).mp h
  change (c : ℤ) • f = (c : ℤ) • g at hc
  have hz : (c : ℤ) • (f - g) = 0 := by rw [smul_sub, hc, sub_self]
  have hp : 0 < (c : ℤ).natAbs :=
    Int.natAbs_pos.mpr (nonZeroDivisors.ne_zero c.property)
  apply sub_eq_zero.mp
  apply hom_nsmul_eq_zero _ hp
  rw [← natCast_zsmul]
  rcases Int.natAbs_eq (c : ℤ) with h' | h'
  · rwa [← h']
  · have hn := congrArg Neg.neg h'
    rw [neg_neg] at hn
    rw [← hn, neg_smul, hz, neg_zero]

/-- Every rational homomorphism has a positive integral denominator. -/
theorem hom0_exists_positive_denominator (x : Hom0 J A) :
    ∃ (m : ℕ) (e : AbVar.Hom J A), 0 < m ∧ m • x = (1 : ℚ) ⊗ₜ[ℤ] e := by
  let S := nonZeroDivisors ℤ
  let T := hom0Inclusion J A
  let : IsLocalizedModule S T :=
    IsLocalization.tensorProduct_isLocalizedModule S ℚ
  obtain ⟨⟨e, c⟩, hc⟩ := IsLocalizedModule.surj S T x
  change (c : ℤ) • x = T e at hc
  have hp : 0 < (c : ℤ).natAbs :=
    Int.natAbs_pos.mpr (nonZeroDivisors.ne_zero c.property)
  rcases Int.natAbs_eq (c : ℤ) with h' | h'
  · refine ⟨_, e, hp, ?_⟩
    rw [← natCast_zsmul, ← h']
    exact hc
  · refine ⟨_, -e, hp, ?_⟩
    have hn := congrArg Neg.neg h'
    rw [neg_neg] at hn
    change (c : ℤ).natAbs • x = T (-e)
    rw [← natCast_zsmul, ← hn, neg_smul, hc, map_neg]

/-- A positive integer acts injectively on the rational Hom space. -/
theorem hom0_nsmul_cancel {m : ℕ} (hm : 0 < m) {v w : Hom0 J A}
    (h : m • v = m • w) : v = w := by
  have hq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h' : (m : ℚ) • v = (m : ℚ) • w := by
    simpa only [Nat.cast_smul_eq_nsmul] using h
  simpa only [smul_smul, inv_mul_cancel₀ hq, one_smul] using
    congrArg (fun z => (m : ℚ)⁻¹ • z) h'

/-- Every positive denominator representing `x` gives the same test:
the cleared integral equation holds exactly when the rational equation holds. -/
theorem cleared_hecke_iff {ν : AbVar.Hom J A} {t : AbVar.End J} {x : A.End0}
    {m : ℕ} {e : AbVar.End A} (hm : 0 < m) (hx : m • x = hom0Inclusion A A e) :
    m • comp t ν = comp ν e ↔
      hom0Inclusion J A (comp t ν) = comp0 (hom0Inclusion J A ν) x := by
  have hcomp : m • comp0 (hom0Inclusion J A ν) x = hom0Inclusion J A (comp ν e) := by
    rw [← map_nsmul, hx]
    change comp0 ((1 : ℚ) ⊗ₜ[ℤ] ν) ((1 : ℚ) ⊗ₜ[ℤ] e) =
      (1 : ℚ) ⊗ₜ[ℤ] comp ν e
    rw [comp0_tmul, _root_.one_mul]
  constructor
  · intro h
    apply hom0_nsmul_cancel hm
    rw [← map_nsmul, h, hcomp]
  · intro h
    apply hom0Inclusion_injective J A
    rw [map_nsmul, h, hcomp]

/-- `HeckeCompat` is exactly `ν ∘ t = x ∘ ν` in the rational Hom space. -/
theorem heckeCompat_iff_rational (ν : AbVar.Hom J A) (t : AbVar.End J) (x : A.End0) :
    HeckeCompat ν t x ↔
      hom0Inclusion J A (comp t ν) = comp0 (hom0Inclusion J A ν) x := by
  constructor
  · rintro ⟨m, e, hm, hx, h⟩
    exact (cleared_hecke_iff hm hx).mp h
  · intro h
    obtain ⟨m, e, hm, hx⟩ := hom0_exists_positive_denominator x
    exact ⟨m, e, hm, hx, (cleared_hecke_iff hm hx).mpr h⟩

end ShimuraSteps.Quotient
