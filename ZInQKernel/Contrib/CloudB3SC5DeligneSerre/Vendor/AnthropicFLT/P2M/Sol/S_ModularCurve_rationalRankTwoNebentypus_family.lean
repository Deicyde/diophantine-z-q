/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_rationalRankTwoNebentypus_family (git blob 97a5360060d7910e8c5da08f8d1accf17d0e9e5b, sha256 c069e3fb7edd86461fe4d077f0e778f90206b9050dc0e82a8a6c59b76af3c80e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_nonempty_basis_fin_two_rationalTateModule_jH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeDiamondCommuteBar

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
namespace HahnSeries
end HahnSeries
namespace CongruenceSubgroup
end CongruenceSubgroup
namespace UpperHalfPlane
end UpperHalfPlane

namespace P2MW.S_ModularCurve_rationalRankTwoNebentypus_family

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open IsDedekindDomain

namespace X1RankTwo

open _root_.ModularCurve hiding IsCusp
open _root_.AlgebraicCurve
open _root_.IntermediateField
open _root_.HahnSeries
open _root_.CongruenceSubgroup
open _root_.UpperHalfPlane

open scoped MatrixGroups ModularForm

section PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]

theorem coeffMap_qExpandG {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem coeffEmb_qExpandG (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpandG _ n x

variable (L) in
theorem laurentBaseChange_monoG {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem qExpand_mem_laurentBaseChangeG {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
    [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L n x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [← coeffEmb_qExpandG]
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (ℓ : ℕ) [NeZero ℓ]

abbrev bot : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ Γ

abbrev top : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 (M * ℓ))

variable (L) in
def heckeAlphaG :
    laurentBaseChange L (qExpFunctionFieldC ℚ Γ) →ₐ[L]
      laurentBaseChange L (qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 (M * ℓ))) :=
  IntermediateField.inclusion (laurentBaseChange_monoG L (qExpFunctionFieldC_mono ℚ inf_le_left))

def HeckeBetaGDefined : Prop :=
  ∀ y ∈ qExpFunctionFieldC ℚ Γ, qExpand ℚ ℓ y ∈ qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 (M * ℓ))

variable (L) in
def heckeBetaGRingHomOf (h : HeckeBetaGDefined M Γ ℓ) :
    laurentBaseChange L (qExpFunctionFieldC ℚ Γ) →+*
      laurentBaseChange L (qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 (M * ℓ))) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChangeG ℓ h x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)

variable (L) in
def heckeBetaGOf (h : HeckeBetaGDefined M Γ ℓ) :
    laurentBaseChange L (qExpFunctionFieldC ℚ Γ) →ₐ[L]
      laurentBaseChange L (qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 (M * ℓ))) :=
  { heckeBetaGRingHomOf L M Γ ℓ h with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

open Classical in
variable (L) in
def heckeBetaG :
    laurentBaseChange L (qExpFunctionFieldC ℚ Γ) →ₐ[L]
      laurentBaseChange L (qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 (M * ℓ))) :=
  if h : HeckeBetaGDefined M Γ ℓ then heckeBetaGOf L M Γ ℓ h else heckeAlphaG L M Γ ℓ

variable (L) in
def HeckeAlphaGIntegral : Prop :=
  (heckeAlphaG L M Γ ℓ).toRingHom.IsIntegral

variable (L) in
def HeckeBetaGIntegral : Prop :=
  (heckeBetaG L M Γ ℓ).toRingHom.IsIntegral

variable {M Γ ℓ}

def heckePic0G (hα : HeckeAlphaGIntegral L M Γ ℓ) (hβ : HeckeBetaGIntegral L M Γ ℓ)
    [HasPrincipalDivisors L (laurentBaseChange L (qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 (M * ℓ))))]
    (hFI : FundamentalIdentityAlong L (heckeBetaG L M Γ ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaG L M Γ ℓ))
    (hN : NormFormulaAlong L (heckeAlphaG L M Γ ℓ) hfin) :
    Pic0 L (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) →+
      Pic0 L (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) :=
  Pic0.correspondence (heckeBetaG L M Γ ℓ) (heckeAlphaG L M Γ ℓ) hβ hα hFI hfin hN

variable (L M Γ ℓ)

def HeckeInputsG : Prop :=
  ∃ (_ : HeckeBetaGDefined M Γ ℓ) (_ : HeckeAlphaGIntegral L M Γ ℓ) (hβ : HeckeBetaGIntegral L M Γ ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 (M * ℓ)))))
    (hfin : FiniteAlong L (heckeAlphaG L M Γ ℓ)),
    FundamentalIdentityAlong L (heckeBetaG L M Γ ℓ) hβ ∧
      NormFormulaAlong L (heckeAlphaG L M Γ ℓ) hfin

open Classical in
def heckeOperatorG :
    Pic0 L (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) →+
      Pic0 L (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) :=
  if h : HeckeInputsG L M Γ ℓ then
    haveI := h.snd.snd.snd.fst
    heckePic0G h.snd.fst h.snd.snd.fst h.snd.snd.snd.snd.snd.1 h.snd.snd.snd.snd.fst
      h.snd.snd.snd.snd.snd.2
  else 0

section Diamond

variable (M : ℕ) (Γ : Subgroup SL(2, ℤ))

def IsDiamondAutG (d : (ZMod M)ˣ)
    (σ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) ≃ₐ[AlgebraicClosure ℚ]
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∃ y : LaurentSeries ℚ, y ∈ qExpFunctionFieldC ℚ Γ ∧
        ((σ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
            laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :
            LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y ∧
        coeffMap (algebraMap ℚ ℂ) y *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))

def diamondAutG (d : (ZMod M)ˣ) :
    laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) ≃ₐ[AlgebraicClosure ℚ]
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) :=
  haveI := Classical.dec (∃ σ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)
      ≃ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ),
    IsDiamondAutG M Γ d σ)
  if h : ∃ σ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)
      ≃ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ),
      IsDiamondAutG M Γ d σ
  then h.choose else AlgEquiv.refl

def diamondGBar (d : (ZMod M)ˣ) :
    Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) →+
      Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
  DistribSMul.toAddMonoidHom _ (SemilinearAut.ofAlgAut (diamondAutG M Γ d))

variable (S : Set ℕ)

def genOpG : CohCarrier.Gen M S →
    (Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) →+
      Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorG (AlgebraicClosure ℚ) M Γ ℓ
  | .U q hq _ => haveI : NeZero q := ⟨hq.ne_zero⟩; heckeOperatorG (AlgebraicClosure ℚ) M Γ q
  | .dia d => diamondGBar M Γ d

variable (p : ℕ) [Fact p.Prime]

def tateGenOpG (g : CohCarrier.Gen M S) :
    Module.End ℤ_[p] (TateModule p
      (Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))) :=
  TateModule.rep p _ (AddMonoid.End _) (genOpG M Γ S g)

def HeckeDiamondInputsG : Prop :=
  (∀ ℓ : ℕ, ∀ hℓ : ℓ.Prime, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      HeckeInputsG (AlgebraicClosure ℚ) M Γ ℓ) ∧
    ∀ d : (ZMod M)ˣ, ∃ σ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)
      ≃ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ),
      IsDiamondAutG M Γ d σ

end Diamond

section Motive

variable (M p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ))

abbrev JG : Type :=
  Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))

def RankTwoPkg : Prop :=
  HeckeDiamondInputsG M Γ →
    Nonempty (Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : CohCarrier.Gen M ((∅ : Finset ℕ) : Set ℕ) =>
          (tateGenOpG M Γ ((∅ : Finset ℕ) : Set ℕ) p g).baseChange ℚ_[p]))
      (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (JG Γ)))) ∧
    ∀ (b : Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : CohCarrier.Gen M ((∅ : Finset ℕ) : Set ℕ) =>
          (tateGenOpG M Γ ((∅ : Finset ℕ) : Set ℕ) p g).baseChange ℚ_[p]))
      (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (JG Γ))))
      {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (_ : ℓ ≠ p)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime ℓ)
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (_ : A.IsFrobeniusAt σ ℓ),
      (tateGenOpG M Γ ((∅ : Finset ℕ) : Set ℕ) p (CohCarrier.Gen.dia
          (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange ℚ_[p] *
        (↑((b.repr ((TateModule.rep p (JG Γ) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ).baseChange ℚ_[p] (b 0))) 0 *
              (b.repr ((TateModule.rep p (JG Γ) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ).baseChange ℚ_[p] (b 1))) 1 -
            (b.repr ((TateModule.rep p (JG Γ) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ).baseChange ℚ_[p] (b 1))) 0 *
              (b.repr ((TateModule.rep p (JG Γ) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ).baseChange ℚ_[p] (b 0))) 1) :
          Module.End ℚ_[p] (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (JG Γ)))) =
        (ℓ : Module.End ℚ_[p] (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (JG Γ))))

end Motive

example (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ) (σ) :
    IsDiamondAutHBar M H d σ ↔ IsDiamondAutG M (CohCarrier.GammaH M H) d σ := Iff.rfl

example (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ) :
    diamondHBar M H d = diamondGBar M (CohCarrier.GammaH M H) d := rfl

example (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime] (g : CohCarrier.Gen M S) :
    tateGenOpH M H S p g = tateGenOpG M (CohCarrier.GammaH M H) S p g := by
  cases g <;> rfl

example (H : Subgroup (ZMod M)ˣ) :
    HeckeDiamondInputsHAll M H ↔ HeckeDiamondInputsG M (CohCarrier.GammaH M H) := Iff.rfl

theorem rankTwoPkg_gammaH (p : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    RankTwoPkg M p (CohCarrier.GammaH M H) := by
  intro hin
  exact ⟨ModularCurve.nonempty_basis_fin_two_rationalTateModule_jH M p H ∅ hin,
    fun b ℓ hℓ hℓM hℓp A hA σ hσ =>
      ModularCurve.diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH M p H ∅ hin b hℓ
        (by simp) hℓM hℓp A hA σ hσ⟩

theorem rankTwoPkg_gamma1 (p : ℕ) [Fact p.Prime] [NeZero M] : RankTwoPkg M p (Gamma1 M) := by
  rw [← ModularCurve.GammaH_bot M]
  exact rankTwoPkg_gammaH M p ⊥

example (H : Subgroup (ZMod M)ˣ) :
    HeckeInputsHAlong L M H ℓ ↔ HeckeInputsG L M (CohCarrier.GammaH M H) ℓ := Iff.rfl

example : HeckeInputsOneAlong L M ℓ ↔ HeckeInputsG L M (Gamma1 M) ℓ := Iff.rfl

example (H : Subgroup (ZMod M)ˣ) :
    heckeOperatorHAlong L M H ℓ = heckeOperatorG L M (CohCarrier.GammaH M H) ℓ := rfl

example : heckeOperatorOneAlong L M ℓ = heckeOperatorG L M (Gamma1 M) ℓ := rfl

example (H : Subgroup (ZMod M)ˣ) :
    JH M H = Pic0 (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := rfl

example : JOne M = Pic0 (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma1 M))) := rfl

section InputsOne

variable {M : ℕ}

theorem isDiamondAutG_diamondAutBar (hin : HeckeDiamondInputsAll M) {d : ℕ} (hd : d.Coprime M) :
    IsDiamondAutG M (Gamma1 M) (ZMod.unitOfCoprime d hd) (diamondAutBar M d) := by
  obtain ⟨hex, hex'⟩ := hin.2 d hd
  have hda : IsDiamondAut M d (diamondAut M d) := isDiamondAut_diamondAut hex
  have hbc : IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) (diamondAutBar M d) :=
    isBaseChangeAutOf_baseChangeAut hex'
  intro k f g pf pg hf hg hg0 γ hγ h00
  refine ⟨((diamondAut M d ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
      div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : x1FunctionField M) : LaurentSeries ℚ),
    SetLike.coe_mem _, hbc ⟨_, div_mem_qExpFunctionFieldC f g hf hg hg0⟩, ?_⟩
  have h00' : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    rw [h00, ZMod.coe_unitOfCoprime]
  exact hda.2 k f g pf pg hf hg hg0 γ hγ h00'

theorem unitOfCoprime_val [NeZero M] (u : (ZMod M)ˣ) :
    ZMod.unitOfCoprime (u : ZMod M).val (ZMod.val_coe_unit_coprime u) = u :=
  Units.ext (ZMod.natCast_zmod_val _)

theorem heckeDiamondInputsG_gamma1 [NeZero M] (hin : HeckeDiamondInputsAll M) :
    HeckeDiamondInputsG M (Gamma1 M) := by
  refine ⟨fun ℓ hℓ => hin.1 ⟨ℓ, hℓ⟩, fun u => ⟨diamondAutBar M (u : ZMod M).val, ?_⟩⟩
  have h := isDiamondAutG_diamondAutBar hin (ZMod.val_coe_unit_coprime u)
  rwa [unitOfCoprime_val] at h

end InputsOne

section Unique

open scoped Manifold Pointwise

variable {M : ℕ}

theorem conj_T_mem_Gamma1 (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    γ * ModularGroup.T * γ⁻¹ ∈ Gamma1 M := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  have hdet : ((γ 0 0 : ℤ) : ZMod M) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod M)) h
  rw [Gamma1_mem]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    ModularGroup.coe_T, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · linear_combination hdet - ((γ 0 0 : ℤ) : ZMod M) * hc
  · linear_combination hdet + ((γ 0 0 : ℤ) : ZMod M) * hc
  · linear_combination (-((γ 1 0 : ℤ) : ZMod M)) * hc

theorem mapGL_T : Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T =
    Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom_apply]

theorem one_mem_strictPeriods_conj [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (1 : ℝ) ∈ (ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹ •
      ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    inv_inv, ConjAct.toConjAct_smul]
  refine ⟨γ * ModularGroup.T * γ⁻¹, conj_T_mem_Gamma1 γ hγ, ?_⟩
  rw [map_mul, map_mul, map_inv, mapGL_T]
  rfl

theorem periodic_slash [NeZero M] {k : ℤ} (g : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    Function.Periodic ((⇑g ∣[k] (γ : GL (Fin 2) ℝ)) ∘ ofComplex) ((1 : ℝ) : ℂ) := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex
    (ModularForm.translate g (γ : GL (Fin 2) ℝ)) (one_mem_strictPeriods_conj γ hγ)
  first | simpa [ModularForm.coe_translate] using this | (simp only [ModularForm.coe_translate] at this; simpa using this) | (intro x; simpa [ModularForm.coe_translate] using this x)

theorem isBoundedAtImInfty_slash [NeZero M] {k : ℤ}
    (g : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (⇑g ∣[k] (γ : GL (Fin 2) ℝ)) := by
  have hc : IsCusp ((γ : GL (Fin 2) ℝ) • OnePoint.infty)
      ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr (isCusp_SL2Z_iff'.mpr ⟨γ, rfl⟩)
  exact (OnePoint.isBoundedAt_iff rfl).mp (g.bdd_at_cusps' hc)

theorem qExpansion_slash_ne_zero [NeZero M] {k : ℤ}
    (g : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k) {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) ≠ 0 := by
  intro h0
  have h1 : qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ)) = 0 :=
    HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero])
  have h2 : (⇑g ∣[k] (γ : GL (Fin 2) ℝ)) = 0 :=
    (qExpansion_eq_zero_iff one_pos (periodic_slash g γ hγ)
      (g.holo'.slash k _) (isBoundedAtImInfty_slash g γ)).mp h1
  have h3 : (⇑g : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ℍ → ℂ => F ∣[k] ((γ : GL (Fin 2) ℝ)⁻¹)) h2
    simpa [← SlashAction.slash_mul] using this
  have h4 : pg = 0 := by
    have h := hg
    rw [IsIntegralQExp, h3, qExpansion_zero] at h
    exact PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective (by rw [h, map_zero])
  exact hg0 (by rw [h4, intSeriesC_zero])

variable {L : Type*} [Field L] [Algebra ℚ L]

theorem algEquiv_ext_of_coeffEmb {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
    {σ σ' : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀}
    (h : ∀ (y : LaurentSeries ℚ) (hy : y ∈ F₀),
      σ ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ =
        σ' ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩) : σ = σ' := by
  apply AlgEquiv.ext
  rintro ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact h y hy
  | algebraMap c =>
      have : (⟨algebraMap L (LaurentSeries L) c, IntermediateField.algebraMap_mem _ c⟩ :
          laurentBaseChange L F₀) = algebraMap L (laurentBaseChange L F₀) c := rfl
      rw [this, AlgEquiv.commutes, AlgEquiv.commutes]
  | add x y hx hy ihx ihy =>
      have : (⟨x + y, add_mem hx hy⟩ : laurentBaseChange L F₀) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add, ihx, ihy]
  | inv x hx ihx =>
      have : (⟨x⁻¹, inv_mem hx⟩ : laurentBaseChange L F₀) = ⟨x, hx⟩⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihx]
  | mul x y hx hy ihx ihy =>
      have : (⟨x * y, mul_mem hx hy⟩ : laurentBaseChange L F₀) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, ihx, ihy]

theorem coeffEmb_algebraMap (a : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) a) = algebraMap L (LaurentSeries L) (algebraMap ℚ L a) := by
  rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single,
    ← algebraMap_laurentSeries_eq_single]

theorem algEquiv_ext_of_ratios {Γ : Subgroup SL(2, ℤ)}
    {σ σ' : laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ≃ₐ[L]
      laurentBaseChange L (qExpFunctionFieldC ℚ Γ)}
    (h : ∀ (y : LaurentSeries ℚ) (hy : y ∈ intFormRatiosC ℚ Γ),
      σ ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L (intFormRatiosC_subset ℚ Γ hy)⟩ =
        σ' ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L (intFormRatiosC_subset ℚ Γ hy)⟩) :
    σ = σ' := by
  refine algEquiv_ext_of_coeffEmb (fun y hy => ?_)
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap a =>
      have : (⟨coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) a),
          coeffEmb_mem_laurentBaseChange L (IntermediateField.algebraMap_mem _ a)⟩ :
            laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) =
          algebraMap L (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) (algebraMap ℚ L a) :=
        Subtype.ext (coeffEmb_algebraMap a)
      rw [this, AlgEquiv.commutes, AlgEquiv.commutes]
  | add x y hx hy ihx ihy =>
      have : (⟨coeffEmb L (x + y), coeffEmb_mem_laurentBaseChange L (add_mem hx hy)⟩ :
          laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) =
          ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩ +
            ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ := Subtype.ext (map_add _ _ _)
      rw [this, map_add, map_add, ihx, ihy]
  | inv x hx ihx =>
      have : (⟨coeffEmb L x⁻¹, coeffEmb_mem_laurentBaseChange L (inv_mem hx)⟩ :
          laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) =
          ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩⁻¹ := Subtype.ext (map_inv₀ _ _)
      rw [this, map_inv₀, map_inv₀, ihx]
  | mul x y hx hy ihx ihy =>
      have : (⟨coeffEmb L (x * y), coeffEmb_mem_laurentBaseChange L (mul_mem hx hy)⟩ :
          laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) =
          ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩ *
            ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ := Subtype.ext (map_mul _ _ _)
      rw [this, map_mul, map_mul, ihx, ihy]

theorem exists_gamma0_apply_eq [NeZero M] (u : (ZMod M)ˣ) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (u : ZMod M) := by
  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective M u⁻¹
  refine ⟨γ.1, γ.2, ?_⟩
  have := congrArg (fun v : (ZMod M)ˣ => ((v⁻¹ : (ZMod M)ˣ) : ZMod M)) hγ
  first | simpa using this | (simp at this; exact this) | exact this

theorem isDiamondAutG_unique [NeZero M] {u : (ZMod M)ˣ}
    {σ σ' : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma1 M))
      ≃ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma1 M))}
    (h : IsDiamondAutG M (Gamma1 M) u σ) (h' : IsDiamondAutG M (Gamma1 M) u σ') : σ = σ' := by
  obtain ⟨γ, hγ, h00⟩ := exists_gamma0_apply_eq u
  refine algEquiv_ext_of_ratios (fun y hy => ?_)
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
  obtain ⟨y1, -, h1, e1⟩ := h k f g pf pg hf hg hg0 γ hγ h00
  obtain ⟨y2, -, h2, e2⟩ := h' k f g pf pg hf hg hg0 γ hγ h00
  have hS := qExpansion_slash_ne_zero g hg hg0 γ hγ
  have h12 : y1 = y2 := by
    have hc : coeffMap (algebraMap ℚ ℂ) y1 = coeffMap (algebraMap ℚ ℂ) y2 :=
      mul_right_cancel₀ hS (e1.trans e2.symm)
    ext n
    have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) hc
    simpa [coeffMap_coeff] using this
  subst h12
  exact Subtype.ext (h1.trans h2.symm)

theorem baseChangeAut_refl (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) :
    baseChangeAut L (AlgEquiv.refl : F₀ ≃ₐ[ℚ] F₀) = AlgEquiv.refl := by
  have hex : ∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀,
      IsBaseChangeAutOf L (AlgEquiv.refl : F₀ ≃ₐ[ℚ] F₀) σ := ⟨AlgEquiv.refl, fun _ => rfl⟩
  have hσ := isBaseChangeAutOf_baseChangeAut hex
  refine algEquiv_ext_of_coeffEmb (fun y hy => Subtype.ext ?_)
  exact hσ ⟨y, hy⟩

end Unique

section OneSpelling

variable (M : ℕ)

def diamondOneG (u : (ZMod M)ˣ) : JOne M →+ JOne M :=
  DistribSMul.toAddMonoidHom (JOne M)
    (SemilinearAut.ofAlgAut (K := AlgebraicClosure ℚ) (F := x1FunctionFieldBar M)
      (diamondAutG M (Gamma1 M) u))

variable (S : Set ℕ)

def genOpOne : CohCarrier.Gen M S → (JOne M →+ JOne M)
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ
  | .U q hq _ => haveI : NeZero q := ⟨hq.ne_zero⟩; heckeOperatorOneAlong (AlgebraicClosure ℚ) M q
  | .dia d => diamondOneG M d

variable (p : ℕ) [Fact p.Prime]

def genV (g : CohCarrier.Gen M S) : Module.End ℚ_[p] (RationalTateModule p (JOne M)) :=
  rationalGaloisRep p (JOne M) (AddMonoid.End (JOne M)) (genOpOne M S g)

def RankTwoPkgOne : Prop :=
    Nonempty (Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range (genV M ((∅ : Finset ℕ) : Set ℕ) p)))
      (RationalTateModule p (JOne M))) ∧
    ∀ (b : Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range (genV M ((∅ : Finset ℕ) : Set ℕ) p)))
      (RationalTateModule p (JOne M)))
      {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (_ : ℓ ≠ p)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime ℓ)
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (_ : A.IsFrobeniusAt σ ℓ),
      genV M ((∅ : Finset ℕ) : Set ℕ) p (CohCarrier.Gen.dia
          (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))) *
        (↑((b.repr (rationalGaloisRep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ (b 0))) 0 *
              (b.repr (rationalGaloisRep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ (b 1))) 1 -
            (b.repr (rationalGaloisRep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ (b 1))) 0 *
              (b.repr (rationalGaloisRep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ (b 0))) 1) :
          Module.End ℚ_[p] (RationalTateModule p (JOne M))) =
        (ℓ : Module.End ℚ_[p] (RationalTateModule p (JOne M)))

theorem rankTwoPkgOne_of_rankTwoPkg (h : RankTwoPkg M p (Gamma1 M))
    (hin : HeckeDiamondInputsG M (Gamma1 M)) : RankTwoPkgOne M p :=
  h hin

end OneSpelling

section Identify

variable {M : ℕ}

theorem diamondAutBar_eq [NeZero M] (hin : HeckeDiamondInputsAll M) {d : ℕ} (hd : d.Coprime M) :
    diamondAutBar M d = diamondAutG M (Gamma1 M) (ZMod.unitOfCoprime d hd) := by
  have h1 := isDiamondAutG_diamondAutBar hin hd
  have hex : ∃ σ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma1 M))
      ≃ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma1 M)),
      IsDiamondAutG M (Gamma1 M) (ZMod.unitOfCoprime d hd) σ := ⟨_, h1⟩
  have h2 : IsDiamondAutG M (Gamma1 M) (ZMod.unitOfCoprime d hd)
      (diamondAutG M (Gamma1 M) (ZMod.unitOfCoprime d hd)) := by
    rw [diamondAutG, dif_pos hex]
    exact hex.choose_spec
  exact isDiamondAutG_unique h1 h2

theorem diamondOneG_unitOfCoprime_apply [NeZero M] (hin : HeckeDiamondInputsAll M) {d : ℕ}
    (hd : d.Coprime M) (x : JOne M) :
    diamondOneG M (ZMod.unitOfCoprime d hd) x = diamondOneBar M d x := by
  rw [diamondOneBar_apply, diamondAutBar_eq hin hd]
  rfl

theorem diamondOneBar_of_not_coprime {d : ℕ} (hd : ¬ d.Coprime M) (x : JOne M) :
    diamondOneBar M d x = x := by
  rw [diamondOneBar_apply, diamondAutBar, diamondAut_of_not_coprime hd, baseChangeAut_refl]
  have h1 : SemilinearAut.ofAlgAut (AlgEquiv.refl : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ]
      x1FunctionFieldBar M) = 1 := map_one _
  rw [h1, one_smul]

attribute [local instance] ModularCurve.heckeModuleOneBar

variable (p : ℕ) [Fact p.Prime]

theorem rep_heckeGenOne (hcomm : HeckeDiamondCommuteBar M) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    TateModule.rep p (JOne M) HeckeAlgOne (heckeGenOne ⟨ℓ, hℓ⟩) =
      TateModule.rep p (JOne M) (AddMonoid.End (JOne M))
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ) := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  simp only [TateModule.rep_apply]
  rw [heckeModuleOneBar_heckeGenOne_smul hcomm]
  rfl

theorem rep_diamondGen_of_coprime [NeZero M] (hin : HeckeDiamondInputsAll M)
    (hcomm : HeckeDiamondCommuteBar M) {d : ℕ} (hd : d.Coprime M) :
    TateModule.rep p (JOne M) HeckeAlgOne (diamondGen d) =
      TateModule.rep p (JOne M) (AddMonoid.End (JOne M)) (diamondOneG M (ZMod.unitOfCoprime d hd)) := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  simp only [TateModule.rep_apply]
  rw [heckeModuleOneBar_diamondGen_smul hcomm]
  exact (diamondOneG_unitOfCoprime_apply hin hd _).symm

theorem rep_diamondGen_of_not (hcomm : HeckeDiamondCommuteBar M) {d : ℕ} (hd : ¬ d.Coprime M) :
    TateModule.rep p (JOne M) HeckeAlgOne (diamondGen d) = 1 := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  simp only [TateModule.rep_apply]
  rw [heckeModuleOneBar_diamondGen_smul hcomm]
  exact diamondOneBar_of_not_coprime hd _

theorem genV_T (hcomm : HeckeDiamondCommuteBar M)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ ((∅ : Finset ℕ) : Set ℕ)) (hℓM : ¬ ℓ ∣ M) :
    genV M ((∅ : Finset ℕ) : Set ℕ) p (.T ℓ hℓ hℓS hℓM)
      = rationalHeckeRepOne p (JOne M) (heckeGenOne ⟨ℓ, hℓ⟩) := by
  rw [rationalHeckeRepOne_apply, tateHeckeRepOne_apply, rep_heckeGenOne p hcomm ℓ hℓ]
  rfl

theorem genV_U (hcomm : HeckeDiamondCommuteBar M) (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) :
    genV M ((∅ : Finset ℕ) : Set ℕ) p (.U q hq hqM)
      = rationalHeckeRepOne p (JOne M) (heckeGenOne ⟨q, hq⟩) := by
  rw [rationalHeckeRepOne_apply, tateHeckeRepOne_apply, rep_heckeGenOne p hcomm q hq]
  rfl

theorem genV_dia [NeZero M] (hin : HeckeDiamondInputsAll M) (hcomm : HeckeDiamondCommuteBar M)
    {d : ℕ} (hd : d.Coprime M) :
    genV M ((∅ : Finset ℕ) : Set ℕ) p (.dia (ZMod.unitOfCoprime d hd))
      = rationalHeckeRepOne p (JOne M) (diamondGen d) := by
  rw [rationalHeckeRepOne_apply, tateHeckeRepOne_apply, rep_diamondGen_of_coprime p hin hcomm hd]
  rfl

theorem rationalHeckeRepOne_diamondGen_of_not (hcomm : HeckeDiamondCommuteBar M) {d : ℕ}
    (hd : ¬ d.Coprime M) : rationalHeckeRepOne p (JOne M) (diamondGen d) = 1 := by
  rw [rationalHeckeRepOne_apply, tateHeckeRepOne_apply, rep_diamondGen_of_not p hcomm hd]
  exact LinearMap.baseChange_one _ _

theorem rationalHeckeRepOne_C_mem (a : ℤ)
    (S : Subalgebra ℚ_[p] (Module.End ℚ_[p] (RationalTateModule p (JOne M)))) :
    rationalHeckeRepOne p (JOne M) (MvPolynomial.C a) ∈ S := by
  have h1 : rationalHeckeRepOne p (JOne M) (MvPolynomial.C a) =
      (a : Module.End ℚ_[p] (RationalTateModule p (JOne M))) :=
    eq_intCast ((rationalHeckeRepOne p (JOne M)).comp MvPolynomial.C) a
  rw [h1]
  exact intCast_mem _ a

theorem adjoin_genV_le [NeZero M] (hin : HeckeDiamondInputsAll M) (hcomm : HeckeDiamondCommuteBar M) :
    Algebra.adjoin ℚ_[p] (Set.range (genV M ((∅ : Finset ℕ) : Set ℕ) p))
      ≤ rationalHeckeAlgebraOne p (JOne M) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨g, rfl⟩
  rw [SetLike.mem_coe]
  cases g with
  | T ℓ hℓ hℓS hℓM =>
      rw [genV_T p hcomm ℓ hℓ hℓS hℓM]
      exact rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p _ _
  | U q hq hqM =>
      rw [genV_U p hcomm q hq hqM]
      exact rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p _ _
  | dia u =>
      rw [← unitOfCoprime_val u, genV_dia p hin hcomm (ZMod.val_coe_unit_coprime u)]
      exact rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p _ _

theorem rationalHeckeRepOne_heckeGenOne_mem (hcomm : HeckeDiamondCommuteBar M) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    rationalHeckeRepOne p (JOne M) (heckeGenOne ⟨ℓ, hℓ⟩) ∈
      Algebra.adjoin ℚ_[p] (Set.range (genV M ((∅ : Finset ℕ) : Set ℕ) p)) := by
  by_cases hℓM : ℓ ∣ M
  · rw [← genV_U p hcomm ℓ hℓ hℓM]
    exact Algebra.subset_adjoin ⟨.U ℓ hℓ hℓM, rfl⟩
  · rw [← genV_T p hcomm ℓ hℓ (by simp) hℓM]
    exact Algebra.subset_adjoin ⟨.T ℓ hℓ (by simp) hℓM, rfl⟩

theorem rationalHeckeRepOne_diamondGen_mem [NeZero M] (hin : HeckeDiamondInputsAll M)
    (hcomm : HeckeDiamondCommuteBar M) (d : ℕ) :
    rationalHeckeRepOne p (JOne M) (diamondGen d) ∈
      Algebra.adjoin ℚ_[p] (Set.range (genV M ((∅ : Finset ℕ) : Set ℕ) p)) := by
  by_cases hd : d.Coprime M
  · rw [← genV_dia p hin hcomm hd]
    exact Algebra.subset_adjoin ⟨.dia (ZMod.unitOfCoprime d hd), rfl⟩
  · rw [rationalHeckeRepOne_diamondGen_of_not p hcomm hd]
    exact one_mem _

theorem le_adjoin_genV [NeZero M] (hin : HeckeDiamondInputsAll M) (hcomm : HeckeDiamondCommuteBar M) :
    rationalHeckeAlgebraOne p (JOne M) ≤
      Algebra.adjoin ℚ_[p] (Set.range (genV M ((∅ : Finset ℕ) : Set ℕ) p)) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨t, rfl⟩
  rw [SetLike.mem_coe]
  induction t using MvPolynomial.induction_on with
  | C a => exact rationalHeckeRepOne_C_mem p a _
  | add f g hf hg =>
      rw [map_add]
      exact add_mem hf hg
  | mul_X f i hf =>
      rw [map_mul]
      refine mul_mem hf ?_
      rcases i with ⟨ℓ, hℓ⟩ | d
      · exact rationalHeckeRepOne_heckeGenOne_mem p hcomm ℓ hℓ
      · exact rationalHeckeRepOne_diamondGen_mem p hin hcomm d

theorem adjoin_genV_eq [NeZero M] (hin : HeckeDiamondInputsAll M) (hcomm : HeckeDiamondCommuteBar M) :
    Algebra.adjoin ℚ_[p] (Set.range (genV M ((∅ : Finset ℕ) : Set ℕ) p))
      = rationalHeckeAlgebraOne p (JOne M) :=
  le_antisymm (adjoin_genV_le p hin hcomm) (le_adjoin_genV p hin hcomm)

theorem coe_rationalDiamondOne_eq [NeZero M] (hin : HeckeDiamondInputsAll M)
    (hcomm : HeckeDiamondCommuteBar M) {ℓ : ℕ} (hℓ : ℓ.Coprime M) :
    ((rationalDiamondOne p (JOne M) ℓ : rationalHeckeAlgebraOne p (JOne M)) :
        Module.End ℚ_[p] (RationalTateModule p (JOne M))) =
      genV M ((∅ : Finset ℕ) : Set ℕ) p (.dia (ZMod.unitOfCoprime ℓ hℓ)) := by
  rw [coe_rationalDiamondOne, genV_dia p hin hcomm hℓ]

end Identify

section Assembly

attribute [local instance] ModularCurve.heckeModuleOneBar

variable {M : ℕ} [NeZero M] (p : ℕ) [Fact p.Prime]

theorem key (hin : HeckeDiamondInputsAll M) (hcomm : HeckeDiamondCommuteBar M)
    (S : Subalgebra ℚ_[p] (Module.End ℚ_[p] (RationalTateModule p (JOne M))))
    (b : Module.Basis (Fin 2) S (RationalTateModule p (JOne M)))
    (hdet : ∀ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (_ : ℓ ≠ p)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime ℓ)
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (_ : A.IsFrobeniusAt σ ℓ),
      genV M ((∅ : Finset ℕ) : Set ℕ) p (CohCarrier.Gen.dia
          (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))) *
        (↑((b.repr (rationalGaloisRep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ (b 0))) 0 *
              (b.repr (rationalGaloisRep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ (b 1))) 1 -
            (b.repr (rationalGaloisRep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ (b 1))) 0 *
              (b.repr (rationalGaloisRep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
                σ (b 0))) 1) :
          Module.End ℚ_[p] (RationalTateModule p (JOne M))) =
        (ℓ : Module.End ℚ_[p] (RationalTateModule p (JOne M))))
    (hS : S = rationalHeckeAlgebraOne p (JOne M)) :
    RationalRankTwoNebentypus M p := by
  subst hS
  refine ⟨b, fun ℓ hℓ hℓMp A hA σ hσ => ?_⟩
  have hℓM : ¬ ℓ ∣ M := fun h => hℓMp (dvd_mul_of_dvd_left h p)
  have hℓp : ℓ ≠ p := fun h => hℓMp (h ▸ dvd_mul_left p M)
  have h := hdet hℓ hℓM hℓp A hA σ hσ
  apply Subtype.ext
  refine (Subalgebra.coe_mul _ _ _).trans ?_
  refine (congrArg (· * _)
    (coe_rationalDiamondOne_eq p hin hcomm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))).trans ?_
  exact h.trans (map_natCast (rationalHeckeAlgebraOne p (JOne M)).val ℓ).symm

theorem main (M p : ℕ) (hM : 0 < M) (hp : p.Prime) :
    haveI : Fact p.Prime := ⟨hp⟩
    ModularCurve.RationalRankTwoNebentypus M p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  have hin := ModularCurve.heckeDiamondInputsAll M
  have hcomm := ModularCurve.heckeDiamondCommuteBar M
  obtain ⟨⟨b⟩, hdet⟩ :=
    rankTwoPkgOne_of_rankTwoPkg M p (rankTwoPkg_gamma1 M p) (heckeDiamondInputsG_gamma1 hin)
  exact key p hin hcomm _ b (fun hℓ hℓM hℓp A hA σ hσ => hdet b hℓ hℓM hℓp A hA σ hσ)
    (adjoin_genV_eq p hin hcomm)

end Assembly

end X1RankTwo

theorem solution :
    ∀ (M p : ℕ) (hM : 0 < M) (hp : p.Prime),
      haveI : Fact p.Prime := ⟨hp⟩
      letI := ModularCurve.heckeModuleOneBar M
      ModularCurve.RationalRankTwoNebentypus M p :=
  fun M p hM hp => X1RankTwo.main M p hM hp

end
