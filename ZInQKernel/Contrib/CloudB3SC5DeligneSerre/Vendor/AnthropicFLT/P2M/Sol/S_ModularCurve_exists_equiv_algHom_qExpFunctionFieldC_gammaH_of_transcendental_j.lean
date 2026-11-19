/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j (git blob fa9cd11fd261307244bc4877b94ab9e9d4ff1b9b, sha256 f248cbe249a601278ae183765b3e4bc97c3a94247374f7944df9f69086892c92).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHDiamondModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j.P2MKcDH
end P2MW.S_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j.P2MKcDH

namespace P2MW.S_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve
open scoped MatrixGroups

noncomputable section

namespace P2MKcDH

section Orb

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {M : ℕ} [NeZero M]

theorem nsmul_eq_mod_nsmul {P : A} (hP : M • P = 0) (n : ℕ) : n • P = (n % M) • P := by
  conv_lhs => rw [← Nat.mod_add_div n M, add_nsmul, mul_nsmul, hP, nsmul_zero, add_zero]

theorem val_natCast_nsmul {P : A} (hP : M • P = 0) (n : ℕ) : ((n : ZMod M).val) • P = n • P := by
  rw [ZMod.val_natCast, ← nsmul_eq_mod_nsmul hP]

theorem val_mul_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u * v).val • P = u.val • (v.val • P) := by
  rw [ZMod.val_mul, ← nsmul_eq_mod_nsmul hP, mul_nsmul']

theorem val_add_nsmul {P : A} (hP : M • P = 0) (u v : ZMod M) :
    (u + v).val • P = u.val • P + v.val • P := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul hP, add_nsmul]

theorem val_neg_nsmul {P : A} (hP : M • P = 0) (u : ZMod M) : (-u).val • P = -(u.val • P) := by
  have h : (-u + u).val • P = 0 := by rw [neg_add_cancel, ZMod.val_zero, zero_nsmul]
  rw [val_add_nsmul hP] at h
  exact eq_neg_of_add_eq_zero_left h

theorem val_one_nsmul {P : A} (hP : M • P = 0) : (1 : ZMod M).val • P = P := by
  have := val_natCast_nsmul hP 1
  rwa [Nat.cast_one, one_nsmul] at this

theorem val_neg_one_nsmul {P : A} (hP : M • P = 0) : (-1 : ZMod M).val • P = -P := by
  rw [val_neg_nsmul hP, val_one_nsmul hP]

theorem nsmul_of_addOrderOf_eq {P : A} (hP : addOrderOf P = M) : M • P = 0 := by
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

theorem nsmul_val_nsmul_eq_zero {P : A} (hP : M • P = 0) (u : ZMod M) : M • (u.val • P) = 0 := by
  rw [nsmul_left_comm, hP, nsmul_zero]

theorem addOrderOf_units_smul {P : A} (hP : addOrderOf P = M) (u : (ZMod M)ˣ) :
    addOrderOf ((u : ZMod M).val • P) = M := by
  have hP0 := nsmul_of_addOrderOf_eq hP
  refine Nat.dvd_antisymm ?_ ?_
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    exact nsmul_val_nsmul_eq_zero hP0 _
  · have h1 : addOrderOf ((u : ZMod M).val • P) • ((u : ZMod M).val • P) = 0 :=
      addOrderOf_nsmul_eq_zero _
    have h2 : ((u⁻¹ : (ZMod M)ˣ) : ZMod M).val • ((u : ZMod M).val • P) = P := by
      rw [← val_mul_nsmul hP0, ← Units.val_mul, inv_mul_cancel, Units.val_one, val_one_nsmul hP0]
    have := congrArg (fun T => ((u⁻¹ : (ZMod M)ˣ) : ZMod M).val • T) h1
    simp only [nsmul_zero] at this
    rw [nsmul_left_comm, h2] at this
    have key : addOrderOf P ∣ addOrderOf ((u : ZMod M).val • P) :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr this
    rwa [hP] at key

theorem addOrderOf_map_eq {φ : A →+ B} (hφ : Function.Injective φ) {P : A}
    (hP : addOrderOf P = M) : addOrderOf (φ P) = M := by
  rw [addOrderOf_injective φ hφ, hP]

theorem addOrderOf_neg_eq {P : A} (hP : addOrderOf P = M) : addOrderOf (-P) = M := by
  rw [addOrderOf_neg, hP]

variable (H : Subgroup (ZMod M)ˣ)

abbrev orb (P : A) : Set A :=
  {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}

abbrev XH (A : Type*) [AddCommGroup A] (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Type _ :=
  {s : Set A // ∃ P : A, addOrderOf P = M ∧ s = orb H P}

theorem neg_one_mem_Hpm : (-1 : (ZMod M)ˣ) ∈ H ⊔ Subgroup.zpowers (-1) :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem mem_Hpm_of_mem {u : (ZMod M)ˣ} (hu : u ∈ H) : u ∈ H ⊔ Subgroup.zpowers (-1) :=
  Subgroup.mem_sup_left hu

theorem mem_orb_self {P : A} (hP : M • P = 0) : P ∈ orb H P :=
  ⟨1, Subgroup.one_mem _, by rw [Units.val_one, val_one_nsmul hP]⟩

theorem orb_eq_of_mem {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : orb H T = orb H P := by
  obtain ⟨u, hu, rfl⟩ := hT
  ext W
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v * u, Subgroup.mul_mem _ hv hu, ?_⟩
    rw [Units.val_mul, val_mul_nsmul hP]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w * u⁻¹, Subgroup.mul_mem _ hw (Subgroup.inv_mem _ hu), ?_⟩
    rw [← val_mul_nsmul hP, ← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem neg_mem_orb {P : A} (hP : M • P = 0) {T : A} (hT : T ∈ orb H P) : -T ∈ orb H P := by
  obtain ⟨u, hu, rfl⟩ := hT
  refine ⟨-1 * u, Subgroup.mul_mem _ (neg_one_mem_Hpm H) hu, ?_⟩
  rw [Units.val_mul, val_mul_nsmul hP, Units.val_neg, Units.val_one,
    val_neg_one_nsmul (nsmul_val_nsmul_eq_zero hP _)]

theorem image_orb (m : A →+ B) (P : A) : m '' orb H P = orb H (m P) := by
  ext W
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [map_nsmul]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : ZMod M).val • P, ⟨u, hu, rfl⟩, by rw [map_nsmul]⟩

theorem eq_or_eq_of_mem_zpowers_neg_one {b : (ZMod M)ˣ} (hb : b ∈ Subgroup.zpowers (-1 : (ZMod M)ˣ)) :
    b = 1 ∨ b = -1 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rcases Int.even_or_odd n with hn | hn
  · exact Or.inl hn.neg_one_zpow
  · exact Or.inr hn.neg_one_zpow

theorem exists_of_mem_Hpm {u : (ZMod M)ˣ} (hu : u ∈ H ⊔ Subgroup.zpowers (-1)) :
    ∃ h ∈ H, u = h ∨ u = h * (-1) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
  rcases eq_or_eq_of_mem_zpowers_neg_one hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

variable {H}

theorem XH.ext' {s s' : XH A M H} (h : s.1 = s'.1) : s = s' := Subtype.ext h

end Orb

section Groups

variable (M : ℕ) [NeZero M]

theorem exists_gamma0_diag (h : (ZMod M)ˣ) :
    ∃ γ : CongruenceSubgroup.Gamma0 M,
      (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (h : ZMod M) ∧
      (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ((h⁻¹ : (ZMod M)ˣ) : ZMod M) := by
  set a : ℤ := ((h : ZMod M).val : ℤ) with ha
  set d : ℤ := (((h⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) with hd
  have hcast_a : ((a : ℤ) : ZMod M) = (h : ZMod M) := by
    rw [ha, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcast_d : ((d : ℤ) : ZMod M) = ((h⁻¹ : (ZMod M)ˣ) : ZMod M) := by
    rw [hd, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hdvd : (M : ℤ) ∣ a * d - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [Int.cast_sub, Int.cast_mul, hcast_a, hcast_d, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Int.cast_one, sub_self]
  obtain ⟨b, hb⟩ := hdvd
  have hdet : Matrix.det !![a, b; (M : ℤ), d] = 1 := by
    rw [Matrix.det_fin_two_of]
    linarith
  refine ⟨⟨⟨!![a, b; (M : ℤ), d], hdet⟩, ?_⟩, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp
  · simpa using hcast_a
  · simpa using hcast_d

theorem val_gamma0Units_inv (γ : CongruenceSubgroup.Gamma0 M) :
    (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) = (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) :=
  rfl

theorem gamma0Units_mem_of_mem {H : Subgroup (ZMod M)ˣ} (γ : CongruenceSubgroup.Gamma0 M)
    (hγ : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H) : CohCarrier.gamma0Units M γ ∈ H := by
  obtain ⟨hA, h⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  exact h

theorem mem_GammaH_of_gamma0Units_mem {H : Subgroup (ZMod M)ˣ} (γ : CongruenceSubgroup.Gamma0 M)
    (hγ : CohCarrier.gamma0Units M γ ∈ H) : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H :=
  CohCarrier.mem_GammaH_iff.mpr ⟨γ.2, hγ⟩

theorem gamma0Units_eq_of_entry (γ : CongruenceSubgroup.Gamma0 M) (u : (ZMod M)ˣ)
    (h : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = (u : ZMod M)) : CohCarrier.gamma0Units M γ = u := by
  ext
  rw [CohCarrier.val_gamma0Units]
  exact h

scoped instance finiteIndex_GammaH (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem SL_mem_zpowers_neg_one_iff (n : SL(2, ℤ)) :
    n ∈ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ n = 1 ∨ n = -1 := by
  constructor
  · intro hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rcases Int.even_or_odd k with hk | hk
    · exact Or.inl hk.neg_one_zpow
    · exact Or.inr hk.neg_one_zpow
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

scoped instance normal_zpowers_neg_one : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rcases (SL_mem_zpowers_neg_one_iff n).mp hn with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · rw [mul_neg_one, neg_mul, mul_inv_cancel]; exact Subgroup.mem_zpowers _

theorem mem_or_neg_mem_of_mem_sup (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ))
    (h : σ ∈ Γ ⊔ Subgroup.zpowers (-1)) : σ ∈ Γ ∨ -σ ∈ Γ := by
  have h' : σ ∈ ((Γ ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := h
  rw [Subgroup.mul_normal] at h'
  obtain ⟨γ, hγ, n, hn, rfl⟩ := h'
  rcases (SL_mem_zpowers_neg_one_iff n).mp hn with rfl | rfl
  · exact Or.inl (by simpa using hγ)
  · exact Or.inr (by simpa using hγ)

end Groups

section Torsor

theorem finite_and_natCard_le_of_mk_le {X : Type*} {n : ℕ} (h : Cardinal.mk X ≤ n) :
    Finite X ∧ Nat.card X ≤ n := by
  have hfin : Cardinal.mk X < Cardinal.aleph0 := lt_of_le_of_lt h Cardinal.natCast_lt_aleph0
  haveI : Finite X := Cardinal.lt_aleph0_iff_finite.mp hfin
  refine ⟨this, ?_⟩
  have := Cardinal.toNat_le_toNat h Cardinal.natCast_lt_aleph0
  first | exact this | simpa [Nat.card] using this

theorem finite_and_natCard_algHom_le (L F Ω : Type*) [Field L] [Field F] [Field Ω] [Algebra L F]
    [Algebra L Ω] [FiniteDimensional L F] :
    Finite (F →ₐ[L] Ω) ∧ Nat.card (F →ₐ[L] Ω) ≤ Module.finrank L F := by
  have h := cardinalMk_algHom L F Ω
  rw [Module.finrank_linearMap_self L Ω F] at h
  exact finite_and_natCard_le_of_mk_le h

variable {G F Ω : Type*} [Group G] [Fintype G] [Field F] [Field Ω] [MulSemiringAction G F]
  [FaithfulSMul G F]

theorem exists_smul_of_forall_fixed (ψ ψ' : F →+* Ω)
    (h : ∀ y : F, (∀ g : G, g • y = y) → ψ' y = ψ y) :
    ∃ g : G, ∀ y : F, ψ' y = ψ (g • y) := by
  classical
  set L := FixedPoints.subfield G F with hL
  letI : Algebra L Ω := (ψ.comp L.subtype).toAlgebra
  have hmemL : ∀ y : L, ∀ g : G, g • (y : F) = y := fun y g => y.2 g

  let toA : G → (F →ₐ[L] Ω) := fun g =>
    { (ψ.comp (MulSemiringAction.toRingHom G F g) : F →+* Ω) with
      commutes' := fun c => by
        show ψ (g • (c : F)) = ψ (c : F)
        rw [hmemL c g] }
  have htoA : ∀ g y, toA g y = ψ (g • y) := fun g y => rfl
  have hinj : Function.Injective toA := by
    intro g g' hgg'
    apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
    intro y
    have := congrArg (fun φ : F →ₐ[L] Ω => φ y) hgg'
    simp only [htoA] at this
    exact ψ.injective this

  let ψ'A : F →ₐ[L] Ω :=
    { ψ' with
      commutes' := fun c => by
        show ψ' (c : F) = ψ (c : F)
        exact h c (hmemL c) }

  obtain ⟨hfin, hcard⟩ := finite_and_natCard_algHom_le L F Ω
  haveI := hfin
  have hLF : Module.finrank L F = Fintype.card G := FixedPoints.finrank_eq_card G F
  have hle : Nat.card (F →ₐ[L] Ω) ≤ Nat.card G := by
    rw [Nat.card_eq_fintype_card (α := G), ← hLF]; exact hcard
  have hbij : Function.Bijective toA := hinj.bijective_of_nat_card_le hle
  obtain ⟨g, hg⟩ := hbij.2 ψ'A
  refine ⟨g, fun y => ?_⟩
  have := congrArg (fun φ : F →ₐ[L] Ω => φ y) hg
  simp only [htoA] at this
  exact this.symm

end Torsor

section Count

variable {K F Ω : Type*} [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]

def eqLocus (ψ ψ₀ : F →ₐ[K] Ω) : IntermediateField K F where
  carrier := {y | ψ y = ψ₀ y}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, map_mul, ha, hb]
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, map_add, ha, hb]
  zero_mem' := by simp
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq]
    rw [AlgHom.commutes, AlgHom.commutes]
  inv_mem' a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv₀, map_inv₀, ha]

theorem apply_eq_of_mem_adjoin {ψ ψ₀ : F →ₐ[K] Ω} {x : F} (hx : ψ x = ψ₀ x) {y : F}
    (hy : y ∈ IntermediateField.adjoin K ({x} : Set F)) : ψ y = ψ₀ y := by
  have hle : IntermediateField.adjoin K ({x} : Set F) ≤ eqLocus ψ ψ₀ :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  exact hle hy

theorem finite_and_natCard_normalised_le (x : F) (c : Ω)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    Finite {ψ : F →ₐ[K] Ω // ψ x = c} ∧
      Nat.card {ψ : F →ₐ[K] Ω // ψ x = c} ≤
        Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F := by
  classical
  by_cases hne : Nonempty {ψ : F →ₐ[K] Ω // ψ x = c}
  swap
  · rw [not_nonempty_iff] at hne
    haveI := hne
    exact ⟨Finite.of_subsingleton, by simp⟩
  obtain ⟨⟨ψ₀, hψ₀⟩⟩ := hne
  set L := IntermediateField.adjoin K ({x} : Set F) with hL
  letI : Algebra L Ω := ((ψ₀ : F →+* Ω).comp (algebraMap L F)).toAlgebra
  let ι : {ψ : F →ₐ[K] Ω // ψ x = c} → (F →ₐ[L] Ω) := fun ψ =>
    { (ψ.1 : F →+* Ω) with
      commutes' := fun r => by
        show ψ.1 (r : F) = ψ₀ (r : F)
        exact apply_eq_of_mem_adjoin (ψ.2.trans hψ₀.symm) r.2 }
  have hι : Function.Injective ι := by
    intro ψ ψ' h
    apply Subtype.ext
    apply AlgHom.ext
    intro y
    exact congrArg (fun φ : F →ₐ[L] Ω => φ y) h
  obtain ⟨hfin, hcard⟩ := finite_and_natCard_algHom_le L F Ω
  haveI := hfin
  exact ⟨Finite.of_injective ι hι, (Nat.card_le_card_of_injective ι hι).trans hcard⟩

end Count

section Descent

variable {K : Type*} [Field K] {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ)

def Fb (K : Type*) [Field K] (M : ℕ) : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)

def FH (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (CohCarrier.GammaH M H)

theorem Fb_eq : Fb K M = qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) := rfl

theorem FH_eq : FH K M H = qExpFunctionFieldC K (CohCarrier.GammaH M H) := rfl

scoped instance instFieldFb : Field (Fb K M) := inferInstance
scoped instance instAlgebraFb : Algebra K (Fb K M) := inferInstance
scoped instance instFieldFH : Field (FH K M H) := inferInstance
scoped instance instAlgebraFH : Algebra K (FH K M H) := inferInstance

theorem FH_le_Fb : FH K M H ≤ Fb K M :=
  qExpFunctionFieldC_mono K (ModularCurve.GammaH_mono bot_le)

def incl : FH K M H →ₐ[K] Fb K M := IntermediateField.inclusion (FH_le_Fb H)

theorem coe_incl (y : FH K M H) : ((incl H y : Fb K M) : LaurentSeries K) = y :=
  IntermediateField.coe_inclusion (FH_le_Fb H) y

def xb (x : FH K M H) : Fb K M := ⟨(x : LaurentSeries K), FH_le_Fb H x.2⟩

theorem incl_x (x : FH K M H) : incl H x = xb H x := rfl

variable {Ω : Type*} [Field Ω] [Algebra K Ω] {Pt : Type*} [AddCommGroup Pt]
variable (x : FH K M H) (c : Ω)
variable (ρ : CongruenceSubgroup.Gamma0 M →* (Fb K M ≃ₐ[K] Fb K M))
variable (Ψ : {P : Pt // addOrderOf P = M} → {ψ : Fb K M →ₐ[K] Ω // ψ (xb H x) = c})

def res (ψ : Fb K M →ₐ[K] Ω) : FH K M H →ₐ[K] Ω := ψ.comp (incl H)

theorem res_apply (ψ : Fb K M →ₐ[K] Ω) (y : FH K M H) : res H ψ y = ψ (incl H y) := rfl

def pt (s : XH Pt M H) : {P : Pt // addOrderOf P = M} := ⟨s.2.choose, s.2.choose_spec.1⟩

theorem pt_spec (s : XH Pt M H) : s.1 = orb H (pt H s).1 := s.2.choose_spec.2

def PhiFun (s : XH Pt M H) : {φ : FH K M H →ₐ[K] Ω // φ x = c} :=
  ⟨res H (Ψ (pt H s)).1, by rw [res_apply, incl_x]; exact (Ψ (pt H s)).2⟩

theorem PhiFun_val (s : XH Pt M H) : (PhiFun H x c Ψ s).1 = res H (Ψ (pt H s)).1 := rfl

variable (hρH : ∀ y : Fb K M, (y : LaurentSeries K) ∈ FH K M H ↔
  ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ y = y)
variable (hdia : ∀ (γ : CongruenceSubgroup.Gamma0 M) (P P' : {P : Pt // addOrderOf P = M}),
  P'.1 = ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M).val) • P.1 →
    ((Ψ P').1 : Fb K M →ₐ[K] Ω) = ((Ψ P).1 : Fb K M →ₐ[K] Ω).comp (ρ γ : Fb K M →ₐ[K] Fb K M))
variable (hneg : ∀ P P' : {P : Pt // addOrderOf P = M}, P'.1 = -P.1 → Ψ P' = Ψ P)
variable (hfib : ∀ P P' : {P : Pt // addOrderOf P = M}, Ψ P' = Ψ P → P'.1 = P.1 ∨ P'.1 = -P.1)

include hρH in

theorem rho_incl (γ : CongruenceSubgroup.Gamma0 M) (hγ : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H)
    (y : FH K M H) : ρ γ (incl H y) = incl H y :=
  (hρH (incl H y)).mp (by rw [coe_incl]; exact y.2) γ hγ

include hρH hdia in

theorem res_eq_of_unit (h : (ZMod M)ˣ) (hh : h ∈ H) (P P' : {P : Pt // addOrderOf P = M})
    (hP' : P'.1 = ((h : ZMod M).val) • P.1) : res H (Ψ P').1 = res H (Ψ P).1 := by
  obtain ⟨γ, hγa, hγd⟩ := exists_gamma0_diag M h
  have hγH : (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H :=
    mem_GammaH_of_gamma0Units_mem M γ
      (by rw [gamma0Units_eq_of_entry M γ h⁻¹ hγd]; exact H.inv_mem hh)
  have key := hdia γ P P' (by rw [hP', hγa])
  apply AlgHom.ext
  intro y
  rw [res_apply, res_apply, key, AlgHom.comp_apply, AlgEquiv.coe_algHom, rho_incl H ρ hρH γ hγH]

include hρH hdia hneg in

theorem res_eq_of_mem_orb (P P' : {P : Pt // addOrderOf P = M}) (hmem : P'.1 ∈ orb H P.1) :
    res H (Ψ P').1 = res H (Ψ P).1 := by
  obtain ⟨u, hu, hP'⟩ := hmem
  obtain ⟨h, hh, huh⟩ := exists_of_mem_Hpm H hu
  have hP0 := nsmul_of_addOrderOf_eq P.2
  rcases huh with rfl | rfl
  · exact res_eq_of_unit H x c ρ Ψ hρH hdia u hh P P' hP'
  · let Pm : {P : Pt // addOrderOf P = M} := ⟨-P.1, addOrderOf_neg_eq P.2⟩
    have hPm : P'.1 = ((h : ZMod M).val) • Pm.1 := by
      rw [hP', Units.val_mul, val_mul_nsmul hP0, Units.val_neg, Units.val_one, val_neg_one_nsmul hP0]
    rw [res_eq_of_unit H x c ρ Ψ hρH hdia h hh Pm P' hPm, hneg P Pm rfl]

include hρH hdia hneg in

theorem PhiFun_spec (P : {P : Pt // addOrderOf P = M}) (s : XH Pt M H) (hs : s.1 = orb H P.1) :
    (PhiFun H x c Ψ s).1 = res H (Ψ P).1 := by
  rw [PhiFun_val]
  apply res_eq_of_mem_orb H x c ρ Ψ hρH hdia hneg
  have h1 : orb H (pt H s).1 = orb H P.1 := (pt_spec H s).symm.trans hs
  have h2 := mem_orb_self H (nsmul_of_addOrderOf_eq (pt H s).2)
  rwa [h1] at h2

include hρH hdia hneg in

theorem PhiFun_natural (m : Pt →+ Pt) (hm : Function.Injective m) (τ : Ω →ₐ[K] Ω)
    (hΨ : ∀ P P' : {P : Pt // addOrderOf P = M}, P'.1 = m P.1 →
      ((Ψ P').1 : Fb K M →ₐ[K] Ω) = τ.comp (Ψ P).1)
    (s s' : XH Pt M H) (hs : s'.1 = m '' s.1) :
    ((PhiFun H x c Ψ s').1 : FH K M H →ₐ[K] Ω) = τ.comp (PhiFun H x c Ψ s).1 := by
  set P := pt H s with hP
  let Pm : {P : Pt // addOrderOf P = M} := ⟨m P.1, addOrderOf_map_eq hm P.2⟩
  have hs' : s'.1 = orb H Pm.1 := by rw [hs, pt_spec H s, image_orb]
  rw [PhiFun_spec H x c ρ Ψ hρH hdia hneg Pm s' hs', hΨ P Pm rfl, PhiFun_val]
  rfl

def GH : Subgroup (Fb K M ≃ₐ[K] Fb K M) :=
  ((CohCarrier.GammaH M H).comap (CongruenceSubgroup.Gamma0 M).subtype).map ρ

theorem mem_GH_iff (g : Fb K M ≃ₐ[K] Fb K M) :
    g ∈ GH H ρ ↔ ∃ γ : CongruenceSubgroup.Gamma0 M,
      (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H ∧ ρ γ = g := by
  simp only [GH, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]

variable (hρbot : ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M ⊥ → ρ γ = 1)

include hρbot in

theorem finite_range : Finite (ρ.range) := by
  let N : Subgroup (CongruenceSubgroup.Gamma0 M) :=
    (CohCarrier.GammaH M ⊥).subgroupOf (CongruenceSubgroup.Gamma0 M)
  haveI : N.FiniteIndex := inferInstance
  have hN : N ≤ ρ.ker := by
    intro γ hγ
    rw [MonoidHom.mem_ker]
    exact hρbot γ (Subgroup.mem_subgroupOf.mp hγ)
  haveI : ρ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hN
  haveI : Finite (CongruenceSubgroup.Gamma0 M ⧸ ρ.ker) := Subgroup.finite_quotient_of_finiteIndex
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv

include hρbot in
theorem finite_GH : Finite (GH H ρ) := by
  haveI := finite_range ρ hρbot
  exact Finite.of_injective (Subgroup.inclusion (Subgroup.map_le_range ρ _))
    (Subgroup.inclusion_injective _)

theorem actGH_smul (g : GH H ρ) (y : Fb K M) : g • y = (g : Fb K M ≃ₐ[K] Fb K M) y := rfl

include hρH in
theorem forall_smul_eq_iff (y : Fb K M) :
    (∀ g : GH H ρ, g • y = y) ↔ (y : LaurentSeries K) ∈ FH K M H := by
  rw [hρH y]
  constructor
  · intro h γ hγ
    have := h ⟨ρ γ, (mem_GH_iff H ρ _).mpr ⟨γ, hγ, rfl⟩⟩
    rwa [actGH_smul] at this
  · intro h g
    obtain ⟨γ, hγ, hg⟩ := (mem_GH_iff H ρ _).mp g.2
    rw [actGH_smul, ← hg]
    exact h γ hγ

include hρH hdia hneg hfib hρbot in

theorem PhiFun_injective : Function.Injective (PhiFun H x c Ψ) := by
  intro s s' hss'
  haveI := finite_GH H ρ hρbot
  letI : Fintype (GH H ρ) := Fintype.ofFinite _
  set P := pt H s with hP
  set P' := pt H s' with hP'
  have hres : res H (Ψ P').1 = res H (Ψ P).1 := by
    rw [← PhiFun_val, ← PhiFun_val, hss']

  have hagree : ∀ y : Fb K M, (∀ g : GH H ρ, g • y = y) →
      ((Ψ P').1 : Fb K M →+* Ω) y = ((Ψ P).1 : Fb K M →+* Ω) y := by
    intro y hy
    have hyH : (y : LaurentSeries K) ∈ FH K M H := (forall_smul_eq_iff H ρ hρH y).mp hy
    have hyy : incl H ⟨(y : LaurentSeries K), hyH⟩ = y :=
      Subtype.ext ((coe_incl H ⟨(y : LaurentSeries K), hyH⟩).trans
        (rfl : (((⟨(y : LaurentSeries K), hyH⟩ : FH K M H) : LaurentSeries K)) = (y : LaurentSeries K)))
    have := congrArg (fun φ : FH K M H →ₐ[K] Ω => φ ⟨(y : LaurentSeries K), hyH⟩) hres
    simp only [res_apply, hyy] at this
    exact this
  obtain ⟨g, hg⟩ := exists_smul_of_forall_fixed ((Ψ P).1 : Fb K M →+* Ω) ((Ψ P').1 : Fb K M →+* Ω) hagree
  obtain ⟨γ, hγH, hγg⟩ := (mem_GH_iff H ρ _).mp g.2

  set a : (ZMod M)ˣ := (CohCarrier.gamma0Units M γ)⁻¹ with ha
  have haH : a ∈ H := H.inv_mem (gamma0Units_mem_of_mem M γ hγH)
  let Pa : {P : Pt // addOrderOf P = M} := ⟨((a : ZMod M).val) • P.1, addOrderOf_units_smul P.2 a⟩
  have hPa : ((Ψ Pa).1 : Fb K M →ₐ[K] Ω) = ((Ψ P).1 : Fb K M →ₐ[K] Ω).comp (ρ γ : Fb K M →ₐ[K] Fb K M) :=
    hdia γ P Pa rfl
  have hP'a : ((Ψ P').1 : Fb K M →ₐ[K] Ω) = ((Ψ P).1 : Fb K M →ₐ[K] Ω).comp (ρ γ : Fb K M →ₐ[K] Fb K M) := by
    apply AlgHom.ext
    intro y
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, hγg]
    exact hg y
  have hΨeq : Ψ P' = Ψ Pa := Subtype.ext (hP'a.trans hPa.symm)
  have hP0 := nsmul_of_addOrderOf_eq P.2
  have hmemA : Pa.1 ∈ orb H P.1 := ⟨a, mem_Hpm_of_mem H haH, rfl⟩
  have hmem : P'.1 ∈ orb H P.1 := by
    rcases hfib Pa P' hΨeq with h1 | h1
    · rw [h1]; exact hmemA
    · rw [h1]; exact neg_mem_orb H hP0 hmemA
  apply XH.ext'
  rw [pt_spec H s, pt_spec H s', ← hP, ← hP']
  exact (orb_eq_of_mem H hP0 hmem).symm

end Descent

end P2MKcDH
open scoped _root_.P2MW.S_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j.P2MKcDH

universe u v in

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (H : Subgroup (ZMod M)ˣ)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) (hx : (x : LaurentSeries K) = jqModC K)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2) :
    ∃ Φ : {s : Set (E.baseChange Ω).toAffine.Point // ∃ P : (E.baseChange Ω).toAffine.Point,
            addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} ≃
        {ψ : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω // ψ x = algebraMap k Ω E.j},
      ∀ (σ : Ω ≃ₐ[k] Ω)
        (s s' : {s : Set (E.baseChange Ω).toAffine.Point // ∃ P : (E.baseChange Ω).toAffine.Point,
            addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}}),
        s'.1 = (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) '' s.1 →
          ((Φ s').1 : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Φ s).1 := by
  classical

  have hMk : (M : k) ≠ 0 := fun h => hM <| (algebraMap K k).injective (by
    rw [map_natCast, map_zero]; exact h)

  have hxb : ((P2MKcDH.xb H x : P2MKcDH.Fb K M) : LaurentSeries K) = jqModC K :=
    (Subtype.coe_mk _ _).trans hx

  obtain ⟨Ψ, hnat, hdia, hneg, hfib⟩ :=
    ModularCurve.exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j
      K M hM (P2MKcDH.xb H x) hxb k Ω E hE hfull

  obtain ⟨ρ, hρ, hρfix⟩ :=
    ModularCurve.exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff K M hM
  have hρbot : ∀ γ : CongruenceSubgroup.Gamma0 M,
      (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M ⊥ → ρ γ = 1 := fun γ hγ =>
    AlgEquiv.ext fun y => (hρfix ⊥ y).mp y.2 γ hγ
  have hρH := hρfix H
  have hdia' := hdia ρ hρ

  have hinj := P2MKcDH.PhiFun_injective H x (algebraMap k Ω E.j) ρ Ψ hρH hdia' hneg hfib hρbot

  obtain ⟨hfd, hdeg⟩ :=
    ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
      (CohCarrier.GammaH M H) (translation_mem_GammaH M H)
      (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)) le_sup_left
      (fun γ hγ => P2MKcDH.mem_or_neg_mem_of_mem_sup _ γ hγ) x hx
  haveI := hfd
  obtain ⟨hfinNE, hcardNE⟩ :=
    P2MKcDH.finite_and_natCard_normalised_le (K := K) x (algebraMap k Ω E.j)
  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq
    E M hMk hfull
  have hcardX := AddCommGroup.natCard_torsionOrbit_gammaH_eq_index M H e
  haveI : (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).FiniteIndex :=
    Subgroup.finiteIndex_of_le le_sup_left
  have hidx : (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  haveI : Finite (P2MKcDH.XH (E.baseChange Ω).toAffine.Point M H) :=
    Nat.finite_of_card_ne_zero (by rw [hcardX]; exact hidx)
  haveI : Finite {φ : P2MKcDH.FH K M H →ₐ[K] Ω // φ x = algebraMap k Ω E.j} := hfinNE
  have hle : Nat.card {φ : P2MKcDH.FH K M H →ₐ[K] Ω // φ x = algebraMap k Ω E.j} ≤
      Nat.card (P2MKcDH.XH (E.baseChange Ω).toAffine.Point M H) := by
    rw [hcardX]
    exact hcardNE.trans hdeg
  have hbij := hinj.bijective_of_nat_card_le hle
  refine ⟨Equiv.ofBijective _ hbij, fun σ s s' hs => ?_⟩
  exact P2MKcDH.PhiFun_natural H x (algebraMap k Ω E.j) ρ Ψ hρH hdia' hneg
    (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω))
    (WeierstrassCurve.Affine.Point.map_injective (σ : Ω →ₐ[k] Ω))
    ((σ : Ω →ₐ[k] Ω).restrictScalars K) (hnat σ) s s' hs

end
open scoped _root_.P2MW.S_ModularCurve_exists_equiv_algHom_qExpFunctionFieldC_gammaH_of_transcendental_j.P2MKcDH
