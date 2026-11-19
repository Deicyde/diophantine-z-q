/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup (git blob daf0bef80110f42a6bb5148969a84a36971f8d89, sha256 2d0477de2e2ffb6ace887dc7ad2d098daf2e84a74c24d53091352d9beedce476).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve
end P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve
namespace P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49
end P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49
namespace P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR
end P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR

namespace P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace ModularCurve
export _root_.ModularCurve (Period.parabolicHoms Period.mem_parabolicHoms_iff finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup)
namespace Ws49
namespace RankR
open _root_.ModularCurve

section Quot

variable {Γ : Type*} [Group Γ] (P : Set Γ)

abbrev Q : Type _ := Abelianization (Γ ⧸ Subgroup.normalClosure P)

def π : Γ →* Q P := Abelianization.of.comp (QuotientGroup.mk' (Subgroup.normalClosure P))

theorem π_apply_of_mem {s : Γ} (hs : s ∈ P) : π P s = 1 := by
  simp only [π, MonoidHom.coe_comp, Function.comp_apply]
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff s).mpr (Subgroup.subset_normalClosure hs),
    map_one]

theorem π_surjective : Function.Surjective (π P) :=
  (QuotientGroup.mk_surjective.comp (QuotientGroup.mk'_surjective _))

scoped instance fg_Q [Group.FG Γ] : Group.FG (Q P) := Group.fg_of_surjective (π_surjective P)

scoped instance addFG_Q [Group.FG Γ] : AddGroup.FG (Additive (Q P)) := inferInstance

def mulChar {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R) : Γ →* Multiplicative R :=
  MonoidHom.toAdditiveLeft.symm φ

@[scoped simp] theorem mulChar_apply {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R) (γ : Γ) :
    mulChar φ γ = Multiplicative.ofAdd (φ (Additive.ofMul γ)) := rfl

theorem normalClosure_le_ker {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R)
    (hφ : ∀ s ∈ P, φ (Additive.ofMul s) = 0) : Subgroup.normalClosure P ≤ (mulChar φ).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  intro s hs
  rw [SetLike.mem_coe, MonoidHom.mem_ker, mulChar_apply, hφ s hs]
  rfl

def liftHom {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R)
    (hφ : ∀ s ∈ P, φ (Additive.ofMul s) = 0) : Additive (Q P) →+ R :=
  MonoidHom.toAdditiveLeft
    (Abelianization.lift (QuotientGroup.lift _ (mulChar φ) (normalClosure_le_ker P φ hφ)))

theorem liftHom_π {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R)
    (hφ : ∀ s ∈ P, φ (Additive.ofMul s) = 0) (γ : Γ) :
    liftHom P φ hφ (Additive.ofMul (π P γ)) = φ (Additive.ofMul γ) := by
  unfold liftHom π
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  show Multiplicative.toAdd ((Abelianization.lift _) (Abelianization.of _)) = _
  rw [Abelianization.lift_apply_of, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  rfl

def pullHom {R : Type*} [AddCommGroup R] (ψ : Additive (Q P) →+ R) : Additive Γ →+ R :=
  ψ.comp (MonoidHom.toAdditive (π P))

@[scoped simp] theorem pullHom_apply {R : Type*} [AddCommGroup R] (ψ : Additive (Q P) →+ R) (γ : Γ) :
    pullHom P ψ (Additive.ofMul γ) = ψ (Additive.ofMul (π P γ)) := rfl

theorem pullHom_apply' {R : Type*} [AddCommGroup R] (ψ : Additive (Q P) →+ R) (x : Additive Γ) :
    pullHom P ψ x = ψ (Additive.ofMul (π P (Additive.toMul x))) := rfl

theorem pullHom_apply_of_mem {R : Type*} [AddCommGroup R] (ψ : Additive (Q P) →+ R) {s : Γ}
    (hs : s ∈ P) : pullHom P ψ (Additive.ofMul s) = 0 := by
  rw [pullHom_apply, π_apply_of_mem P hs, ofMul_one, map_zero]

theorem pullHom_liftHom {R : Type*} [AddCommGroup R] (φ : Additive Γ →+ R)
    (hφ : ∀ s ∈ P, φ (Additive.ofMul s) = 0) : pullHom P (liftHom P φ hφ) = φ :=
  AddMonoidHom.ext fun γ => liftHom_π P φ hφ (Additive.toMul γ)

theorem liftHom_pullHom {R : Type*} [AddCommGroup R] (ψ : Additive (Q P) →+ R) :
    liftHom P (pullHom P ψ) (fun s hs => pullHom_apply_of_mem P ψ hs) = ψ := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨γ, hγ⟩ := π_surjective P (Additive.toMul x)
  have hx : x = Additive.ofMul (π P γ) := by rw [hγ]; rfl
  rw [hx, liftHom_π, pullHom_apply]

theorem pullHom_injective {R : Type*} [AddCommGroup R] :
    Function.Injective (pullHom P (R := R)) := fun a b h => by
  rw [← liftHom_pullHom P a, ← liftHom_pullHom P b]
  simp only [h]

end Quot

end ModularCurve.Ws49.RankR
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve

end
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR

noncomputable section

open scoped MatrixGroups

namespace ModularCurve
export _root_.ModularCurve (Period.parabolicHoms Period.mem_parabolicHoms_iff finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup)
namespace Ws49
namespace RankR
open _root_.ModularCurve

section Char

variable {A : Type*} [AddCommGroup A]
variable (R : Type*) [CommRing R] [IsAddTorsionFree R]

theorem hom_eq_zero_of_finite {T : Type*} [AddCommGroup T] [Finite T] (f : T →+ R) : f = 0 := by
  ext t
  have hn : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have h : (Nat.card T) • f t = 0 := by
    rw [← map_nsmul, card_nsmul_eq_zero', map_zero]
  rw [AddMonoidHom.zero_apply]
  exact IsAddTorsionFree.eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all _ _) (by simpa using h)

variable {R}

def evalAt {ι : Type*} (a : ι → A) : (A →+ R) →ₗ[R] (ι → R) where
  toFun f i := f (a i)
  map_add' f g := by funext i; rfl
  map_smul' c f := by funext i; simp

@[scoped simp] theorem evalAt_apply {ι : Type*} (a : ι → A) (f : A →+ R) (i : ι) : evalAt a f i = f (a i) := rfl

def charEquiv {n : ℕ} {T : Type*} [AddCommGroup T] [Finite T] (e : A ≃+ (Fin n →₀ ℤ) × T) :
    (A →+ R) ≃ₗ[R] (Fin n → R) := by
  refine LinearEquiv.ofBijective (evalAt fun i => e.symm (Finsupp.single i 1, 0)) ⟨?_, ?_⟩
  ·
    intro f g hfg
    have key : ∀ h : A →+ R, (∀ i, h (e.symm (Finsupp.single i 1, 0)) = 0) → h = 0 := by
      intro h hh

      have hT : (h.comp e.symm.toAddMonoidHom).comp (AddMonoidHom.inr (Fin n →₀ ℤ) T) = 0 :=
        hom_eq_zero_of_finite R _
      have hZ : (h.comp e.symm.toAddMonoidHom).comp (AddMonoidHom.inl (Fin n →₀ ℤ) T) = 0 := by
        apply Finsupp.addHom_ext
        intro i m
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inl_apply,
          AddMonoidHom.zero_apply]
        have : (Finsupp.single i m, (0 : T)) = m • (Finsupp.single i (1 : ℤ), (0 : T)) := by
          rw [Prod.smul_mk, smul_zero, Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [this, AddEquiv.coe_toAddMonoidHom, map_zsmul, map_zsmul, hh i, smul_zero]
      have hsum : h.comp e.symm.toAddMonoidHom = 0 := by
        ext ⟨x, t⟩
        have : ((x, t) : (Fin n →₀ ℤ) × T) = AddMonoidHom.inl _ _ x + AddMonoidHom.inr _ _ t := by simp
        rw [this, map_add, ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply, hZ, hT]
        simp
      ext a
      have := congrArg (fun φ : (Fin n →₀ ℤ) × T →+ R => φ (e a)) hsum
      simpa using this
    have h0 := key (f - g) (fun i => by
      have := congrFun hfg i
      simp only [evalAt_apply] at this
      simp [this])
    exact sub_eq_zero.mp h0
  ·
    intro c
    let ψZ : (Fin n →₀ ℤ) →+ R := Finsupp.liftAddHom fun i => (zmultiplesHom R (c i) : ℤ →+ R)
    let ψ : (Fin n →₀ ℤ) × T →+ R := ψZ.comp (AddMonoidHom.fst _ _)
    refine ⟨ψ.comp e.toAddMonoidHom, ?_⟩
    funext i
    simp [ψ, ψZ, evalAt_apply]

theorem finrank_char_eq {n : ℕ} {T : Type*} [AddCommGroup T] [Finite T] (e : A ≃+ (Fin n →₀ ℤ) × T)
    [StrongRankCondition R] : Module.finrank R (A →+ R) = n := by
  rw [(charEquiv (R := R) e).finrank_eq, Module.finrank_fin_fun]

end Char
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR

section Vanishing

variable {Γ : Type*} [Group Γ] (P : Set Γ)
variable (R : Type*) [CommRing R]

def vanishing : Submodule R (Additive Γ →+ R) where
  carrier := {φ | ∀ s ∈ P, φ (Additive.ofMul s) = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ s hs
    show φ _ + ψ _ = 0
    rw [hφ s hs, hψ s hs, add_zero]
  smul_mem' := by
    intro c φ hφ s hs
    show c • φ _ = 0
    rw [hφ s hs, smul_zero]

variable {P R}

theorem mem_vanishing_iff {φ : Additive Γ →+ R} : φ ∈ vanishing P R ↔ ∀ s ∈ P, φ (Additive.ofMul s) = 0 :=
  Iff.rfl

variable (P R)

def vanishingEquiv : vanishing P R ≃ₗ[R] (Additive (Q P) →+ R) where
  toFun φ := liftHom P φ.1 φ.2
  invFun ψ := ⟨pullHom P ψ, fun s hs => pullHom_apply_of_mem P ψ hs⟩
  left_inv φ := Subtype.ext (pullHom_liftHom P φ.1 φ.2)
  right_inv ψ := liftHom_pullHom P ψ
  map_add' φ ψ := by
    apply pullHom_injective P
    rw [pullHom_liftHom]
    refine AddMonoidHom.ext fun γ => ?_
    rw [pullHom_apply', AddMonoidHom.add_apply, liftHom_π, liftHom_π]
    rfl
  map_smul' c φ := by
    apply pullHom_injective P
    rw [pullHom_liftHom]
    refine AddMonoidHom.ext fun γ => ?_
    rw [RingHom.id_apply, pullHom_apply', AddMonoidHom.smul_apply, liftHom_π]
    rfl

theorem exists_forall_finrank_vanishing_eq [Group.FG Γ] :
    ∃ r : ℕ, ∀ (R : Type) [CommRing R] [IsAddTorsionFree R] [StrongRankCondition R],
      Module.finrank R (vanishing P R) = r := by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive (Q P))
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) := by
    classical
    haveI : ∀ i, Fintype (ZMod (p i ^ e i)) := fun i => ZMod.fintype _
    exact Finite.of_equiv (Π₀ i, ZMod (p i ^ e i)) (Equiv.refl _)
  refine ⟨n, fun R _ _ _ => ?_⟩
  rw [(vanishingEquiv P R).finrank_eq]
  exact finrank_char_eq f

end Vanishing
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR

section Parabolic

variable (Γ : Subgroup SL(2, ℤ))

def parabolicSet : Set Γ := {γ | ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4}

theorem parabolicHoms_eq_vanishing (R : Type*) [CommRing R] :
    ModularCurve.Period.parabolicHoms R Γ R = vanishing (parabolicSet Γ) R := by
  ext φ
  rw [ModularCurve.Period.mem_parabolicHoms_iff, mem_vanishing_iff]
  rfl

scoped instance fg_SL2Z : Group.FG SL(2, ℤ) := by
  rw [Group.fg_iff]
  exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

scoped instance fg_of_finiteIndex [Γ.FiniteIndex] : Group.FG Γ := inferInstance

theorem finrank_real_parabolicHoms_eq_finrank_int [Γ.FiniteIndex] :
    Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) =
      Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) := by
  obtain ⟨r, hr⟩ := exists_forall_finrank_vanishing_eq (parabolicSet Γ)
  rw [parabolicHoms_eq_vanishing, parabolicHoms_eq_vanishing, hr ℝ, hr ℤ]

end Parabolic
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR

end ModularCurve.Ws49.RankR
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR

end
open scoped _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49 _root_.P2MW.S_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.ModularCurve.Ws49.RankR

open scoped MatrixGroups in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) ≤
      2 * Module.finrank ℂ (CuspForm Γ 2) := by
  haveI : Γ.FiniteIndex := hΓ.finiteIndex
  rw [ModularCurve.Ws49.RankR.finrank_real_parabolicHoms_eq_finrank_int]
  exact ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup Γ hΓ
