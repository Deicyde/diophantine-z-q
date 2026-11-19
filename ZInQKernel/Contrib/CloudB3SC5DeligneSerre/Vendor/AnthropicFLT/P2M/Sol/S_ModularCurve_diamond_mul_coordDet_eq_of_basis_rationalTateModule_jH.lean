/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH (git blob b594745d4f5e2ad7df6fa0bd83b60f8e8df952fa, sha256 10f711221e2f0d08ae81f40c5e0bae7de4e17a2a7d8b3958824e2978f2059117).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeOperatorHAlong_comm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeOperatorHAlong_diamondHBar_comm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_diamondHBar_mul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_galois_smul_genOpH_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH

open scoped TensorProduct

set_option autoImplicit false

namespace WeilDetPkg

section Poly

open scoped IsMulCommutative

variable {K A' : Type} [Field K] [Ring A'] [Algebra K A'] (S : Subalgebra K A') [IsMulCommutative S]

theorem det_smul_identity (x c00 c01 c10 c11 : S) :
    c00 * (x * c11) - c01 * (x * c10) = x * (c00 * c11 - c10 * c01) := by
  ring

theorem sub_mul_right_comm (D d s : S) (ℓ : ℕ) :
    (D * d - ℓ) * s = D * s * d - ℓ * s := by
  ring

end Poly

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T]

abbrev V (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] : Type :=
  ℚ_[p] ⊗[ℤ_[p]] T

noncomputable abbrev bc (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] :
    Module.End ℤ_[p] T →ₐ[ℤ_[p]] Module.End ℚ_[p] (V p T) :=
  Module.End.baseChangeHom ℤ_[p] ℚ_[p] T

theorem bc_apply (f : Module.End ℤ_[p] T) : bc p T f = f.baseChange ℚ_[p] := rfl

variable {ι₀ : Type} (A : ι₀ → Module.End ℤ_[p] T)

noncomputable def R (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T]
    (A : ι₀ → Module.End ℤ_[p] T) : Subalgebra ℚ_[p] (Module.End ℚ_[p] (V p T)) :=
  Algebra.adjoin ℚ_[p] (Set.range fun g : ι₀ => (A g).baseChange ℚ_[p])

theorem bc_mem_R (i : ι₀) : bc p T (A i) ∈ R p T A :=
  Algebra.subset_adjoin ⟨i, rfl⟩

theorem isMulCommutative_R (hA : ∀ (g g' : ι₀) (x : T), A g (A g' x) = A g' (A g x)) :
    IsMulCommutative (R p T A) := by
  refine Algebra.isMulCommutative_adjoin ℚ_[p] ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
  show bc p T (A i) * bc p T (A j) = bc p T (A j) * bc p T (A i)
  rw [← map_mul, ← map_mul]
  congr 1
  exact LinearMap.ext fun x => hA i j x

theorem mul_comm_R [IsMulCommutative (R p T A)] (r s : R p T A) : r * s = s * r :=
  IsMulCommutative.is_comm.comm r s

variable (φ : Module.End ℤ_[p] T)

theorem commute_bc (hφ : ∀ (g : ι₀) (x : T), φ (A g x) = A g (φ x))
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) : r * bc p T φ = bc p T φ * r := by
  have hle : R p T A ≤ Subalgebra.centralizer ℚ_[p] {bc p T φ} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩ _ rfl
    show bc p T φ * bc p T (A i) = bc p T (A i) * bc p T φ
    rw [← map_mul, ← map_mul]
    congr 1
    exact LinearMap.ext fun x => hφ i x
  exact ((Subalgebra.mem_centralizer_iff ℚ_[p]).mp (hle hr) _ rfl).symm

variable (B : V p T →ₗ[ℚ_[p]] V p T →ₗ[ℚ_[p]] ℚ_[p])

theorem B_swap (halt : ∀ v, B v v = 0) (x y : V p T) : B x y = -B y x := by
  have h := halt (x + y)
  rw [LinearMap.map_add₂, map_add, map_add, halt x, halt y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem bal_R [IsMulCommutative (R p T A)]
    (hbal : ∀ (g : ι₀) (x y : V p T), B (bc p T (A g) x) y = B x (bc p T (A g) y))
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) : ∀ x y : V p T, B (r x) y = B x (r y) := by
  induction hr using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact hbal g
  | algebraMap a =>
    intro x y
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearMap.map_smul₂, map_smul]
  | add f g _ _ ihf ihg =>
    intro x y
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.map_add₂, map_add, ihf, ihg]
  | mul f g hf hg ihf ihg =>
    intro x y
    have hc : f * g = g * f := congrArg Subtype.val (mul_comm_R A (⟨f, hf⟩ : R p T A) ⟨g, hg⟩)
    conv_rhs => rw [hc]
    rw [Module.End.mul_apply, Module.End.mul_apply, ihf, ihg]

theorem B_self_R [IsMulCommutative (R p T A)] (halt : ∀ v, B v v = 0)
    (hbal : ∀ (g : ι₀) (x y : V p T), B (bc p T (A g) x) y = B x (bc p T (A g) y))
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) (x : V p T) : B x (r x) = 0 := by
  have h1 : B x (r x) = -B (r x) x := B_swap B halt x (r x)
  rw [bal_R A B hbal hr] at h1
  have h2 : B x (r x) + B x (r x) = 0 := add_eq_zero_iff_eq_neg.mpr h1
  rwa [add_self_eq_zero] at h2

variable (b : Module.Basis (Fin 2) (R p T A) (V p T))

noncomputable def lam (r : R p T A) : ℚ_[p] := B (b 0) ((r : Module.End ℚ_[p] (V p T)) (b 1))

theorem lam_neg (r : R p T A) : lam A B b (-r) = -lam A B b r := by
  simp only [lam, Subalgebra.coe_neg, LinearMap.neg_apply, map_neg]

theorem lam_sub (r s : R p T A) : lam A B b (r - s) = lam A B b r - lam A B b s := by
  simp only [lam, Subalgebra.coe_sub, LinearMap.sub_apply, map_sub]

theorem lam_natCast_mul (n : ℕ) (r : R p T A) : lam A B b (n * r) = (n : ℚ_[p]) * lam A B b r := by
  simp only [lam, Subalgebra.coe_mul, Module.End.mul_apply]
  have : ((n : R p T A) : Module.End ℚ_[p] (V p T)) = (n : Module.End ℚ_[p] (V p T)) :=
    map_natCast (R p T A).val n
  rw [this, Module.End.natCast_apply, map_nsmul, nsmul_eq_mul]

theorem expand (v : V p T) :
    v = (b.repr v 0 : Module.End ℚ_[p] (V p T)) (b 0) + (b.repr v 1 : Module.End ℚ_[p] (V p T)) (b 1) := by
  conv_lhs => rw [← b.sum_repr v]
  rw [Fin.sum_univ_two]
  rfl

section Comb

variable [IsMulCommutative (R p T A)]
  (halt : ∀ v, B v v = 0)
  (hbal : ∀ (g : ι₀) (x y : V p T), B (bc p T (A g) x) y = B x (bc p T (A g) y))

include hbal in
theorem B_coe_coe (r s : R p T A) (x y : V p T) :
    B ((r : Module.End ℚ_[p] (V p T)) x) ((s : Module.End ℚ_[p] (V p T)) y)
      = B x (((r * s : R p T A) : Module.End ℚ_[p] (V p T)) y) := by
  rw [bal_R A B hbal r.2, Subalgebra.coe_mul, Module.End.mul_apply]

include halt hbal in

theorem B_coe_same (r s : R p T A) (i : Fin 2) :
    B ((r : Module.End ℚ_[p] (V p T)) (b i)) ((s : Module.End ℚ_[p] (V p T)) (b i)) = 0 := by
  rw [B_coe_coe A B hbal]
  exact B_self_R A B halt hbal (r * s).2 (b i)

include hbal in

theorem B_coe_b0_b1 (r s : R p T A) :
    B ((r : Module.End ℚ_[p] (V p T)) (b 0)) ((s : Module.End ℚ_[p] (V p T)) (b 1))
      = lam A B b (r * s) := by
  rw [B_coe_coe A B hbal]; rfl

include halt hbal in

theorem B_coe_b1_b0 (r s : R p T A) :
    B ((r : Module.End ℚ_[p] (V p T)) (b 1)) ((s : Module.End ℚ_[p] (V p T)) (b 0))
      = -lam A B b (r * s) := by
  rw [B_coe_coe A B hbal, B_swap B halt, bal_R A B hbal (r * s).2]; rfl

include halt hbal in

theorem B_comb (r s t u : R p T A) :
    B ((r : Module.End ℚ_[p] (V p T)) (b 0) + (s : Module.End ℚ_[p] (V p T)) (b 1))
        ((t : Module.End ℚ_[p] (V p T)) (b 0) + (u : Module.End ℚ_[p] (V p T)) (b 1))
      = lam A B b (r * u - s * t) := by
  rw [LinearMap.map_add₂, map_add, map_add, B_coe_same A B b halt hbal, B_coe_b0_b1 A B b hbal,
    B_coe_b1_b0 A B b halt hbal, B_coe_same A B b halt hbal, zero_add, add_zero, ← sub_eq_add_neg,
    lam_sub]

end Comb

section Opaque

variable [IsMulCommutative (R p T A)]
variable (F : Module.End ℚ_[p] (V p T))
  (hF : ∀ r : R p T A, (r : Module.End ℚ_[p] (V p T)) * F = F * r)

noncomputable def detF : R p T A :=
  b.repr (F (b 0)) 0 * b.repr (F (b 1)) 1 - b.repr (F (b 1)) 0 * b.repr (F (b 0)) 1

omit [IsMulCommutative (R p T A)] in
include hF in
theorem F_coe_apply (r : R p T A) (v : V p T) :
    F ((r : Module.End ℚ_[p] (V p T)) v) = (r : Module.End ℚ_[p] (V p T)) (F v) := by
  rw [← Module.End.mul_apply, ← hF, Module.End.mul_apply]

variable (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
  (hbal : ∀ (g : ι₀) (x y : V p T), B (bc p T (A g) x) y = B x (bc p T (A g) y))

include hF halt hbal in

theorem B_F_coe_b0_F_b1 (x : R p T A) :
    B (F ((x : Module.End ℚ_[p] (V p T)) (b 0))) (F (b 1)) = lam A B b (x * detF A b F) := by
  have h0 := expand A b (F (b 0))
  have h1 := expand A b (F (b 1))
  have e : (x : Module.End ℚ_[p] (V p T)) (F (b 1))
      = ((x * b.repr (F (b 1)) 0 : R p T A) : Module.End ℚ_[p] (V p T)) (b 0)
        + ((x * b.repr (F (b 1)) 1 : R p T A) : Module.End ℚ_[p] (V p T)) (b 1) := by
    conv_lhs => rw [h1]
    rw [map_add, Subalgebra.coe_mul, Subalgebra.coe_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [F_coe_apply A F hF, bal_R A B hbal x.2, e]
  conv_lhs => rw [h0]
  rw [B_comb A B b halt hbal, det_smul_identity (R p T A)]
  rfl

variable (Dr : R p T A) (ℓ : ℕ)
  (hsim : ∀ x y : V p T,
    B ((Dr : Module.End ℚ_[p] (V p T)) (F x)) (F y) = (ℓ : ℚ_[p]) * B x y)

noncomputable def rObs : R p T A := Dr * detF A b F - ℓ

include hF halt hbal hsim in

theorem lam_rObs_mul (s : R p T A) : lam A B b (rObs A b F Dr ℓ * s) = 0 := by
  have h := hsim ((s : Module.End ℚ_[p] (V p T)) (b 0)) (b 1)

  have hl : B ((Dr : Module.End ℚ_[p] (V p T)) (F ((s : Module.End ℚ_[p] (V p T)) (b 0)))) (F (b 1))
      = lam A B b (Dr * s * detF A b F) := by
    have e : (Dr : Module.End ℚ_[p] (V p T)) (F ((s : Module.End ℚ_[p] (V p T)) (b 0)))
        = F (((Dr * s : R p T A) : Module.End ℚ_[p] (V p T)) (b 0)) := by
      rw [← F_coe_apply A F hF, Subalgebra.coe_mul, Module.End.mul_apply]
    rw [e, B_F_coe_b0_F_b1 A B b F hF halt hbal]

  have hr' : (ℓ : ℚ_[p]) * B ((s : Module.End ℚ_[p] (V p T)) (b 0)) (b 1) = lam A B b (ℓ * s) := by
    rw [lam_natCast_mul, bal_R A B hbal s.2]; rfl
  rw [hl, hr'] at h
  have h2 : lam A B b (Dr * s * detF A b F - ℓ * s) = 0 := by rw [lam_sub, h, sub_self]
  rw [rObs, sub_mul_right_comm (R p T A) Dr (detF A b F) s ℓ, h2]

include hF halt hnd hbal hsim in

theorem rObs_b1 : (rObs A b F Dr ℓ : Module.End ℚ_[p] (V p T)) (b 1) = 0 := by
  refine hnd _ fun w => ?_
  have hw := expand A b w
  conv_lhs => rw [hw]
  rw [map_add, B_coe_b1_b0 A B b halt hbal, B_coe_same A B b halt hbal,
    lam_rObs_mul A B b F hF halt hbal Dr ℓ hsim, neg_zero, add_zero]

include hF halt hnd hbal hsim in

theorem rObs_b0 : (rObs A b F Dr ℓ : Module.End ℚ_[p] (V p T)) (b 0) = 0 := by
  refine hnd _ fun w => ?_
  have hw := expand A b w
  conv_lhs => rw [hw]
  rw [map_add, B_coe_same A B b halt hbal, B_coe_b0_b1 A B b hbal,
    lam_rObs_mul A B b F hF halt hbal Dr ℓ hsim, add_zero]

include hF halt hnd hbal hsim in

theorem coe_rObs : (rObs A b F Dr ℓ : Module.End ℚ_[p] (V p T)) = 0 := by
  refine LinearMap.ext fun v => ?_
  set r := rObs A b F Dr ℓ
  have hv := expand A b v
  have hc0 : (r : Module.End ℚ_[p] (V p T)) * (b.repr v 0 : Module.End ℚ_[p] (V p T))
      = (b.repr v 0 : Module.End ℚ_[p] (V p T)) * r :=
    congrArg Subtype.val (mul_comm_R A r (b.repr v 0))
  have hc1 : (r : Module.End ℚ_[p] (V p T)) * (b.repr v 1 : Module.End ℚ_[p] (V p T))
      = (b.repr v 1 : Module.End ℚ_[p] (V p T)) * r :=
    congrArg Subtype.val (mul_comm_R A r (b.repr v 1))
  rw [hv, map_add, ← Module.End.mul_apply, hc0, Module.End.mul_apply,
    rObs_b0 A B b F hF halt hnd hbal Dr ℓ hsim, map_zero, zero_add, ← Module.End.mul_apply, hc1,
    Module.End.mul_apply, rObs_b1 A B b F hF halt hnd hbal Dr ℓ hsim, map_zero,
    LinearMap.zero_apply]

include hF halt hnd hbal hsim in

theorem coe_mul_detF :
    (Dr : Module.End ℚ_[p] (V p T)) * (detF A b F : Module.End ℚ_[p] (V p T))
      = (ℓ : Module.End ℚ_[p] (V p T)) := by
  have h := coe_rObs A B b F hF halt hnd hbal Dr ℓ hsim
  rw [rObs, Subalgebra.coe_sub, Subalgebra.coe_mul, sub_eq_zero] at h
  rw [h]
  exact map_natCast (R p T A).val ℓ

end Opaque

theorem main [IsMulCommutative (R p T A)]
    (halt : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hbal : ∀ (g : ι₀) (x y : V p T), B (bc p T (A g) x) y = B x (bc p T (A g) y))
    (hφ : ∀ (g : ι₀) (x : T), φ (A g x) = A g (φ x))
    (g₀ : ι₀) (ℓ : ℕ)
    (hsim : ∀ x y : V p T,
      B (bc p T (A g₀) (bc p T φ x)) (bc p T φ y) = (ℓ : ℚ_[p]) * B x y) :
    (A g₀).baseChange ℚ_[p] *
        ((b.repr (φ.baseChange ℚ_[p] (b 0)) 0 * b.repr (φ.baseChange ℚ_[p] (b 1)) 1
            - b.repr (φ.baseChange ℚ_[p] (b 1)) 0 * b.repr (φ.baseChange ℚ_[p] (b 0)) 1 : R p T A) :
          Module.End ℚ_[p] (V p T))
      = (ℓ : Module.End ℚ_[p] (V p T)) := by
  have hDr : ((⟨bc p T (A g₀), bc_mem_R A g₀⟩ : R p T A) : Module.End ℚ_[p] (V p T))
      = (A g₀).baseChange ℚ_[p] := rfl
  rw [← hDr]
  exact coe_mul_detF A B b (bc p T φ) (fun r => commute_bc A φ hφ r.2) halt hnd hbal
    ⟨bc p T (A g₀), bc_mem_R A g₀⟩ ℓ hsim

end WeilDetPkg

namespace WeilDetJH

open _root_.ModularCurve hiding baseChangeHom

variable (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ)

omit [Fact p.Prime] in

theorem genOpH_comm (g g' : CohCarrier.Gen M (↑S : Set ℕ)) (P : JH M H) :
    genOpH M H (↑S : Set ℕ) g (genOpH M H (↑S : Set ℕ) g' P)
      = genOpH M H (↑S : Set ℕ) g' (genOpH M H (↑S : Set ℕ) g P) := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI := Fact.mk hℓ
    cases g' with
    | T ℓ' hℓ' hℓ'S hℓ'M =>
      haveI := Fact.mk hℓ'
      exact heckeOperatorHAlong_comm M H ℓ ℓ' P
    | U q hq hqM =>
      haveI := Fact.mk hq
      exact heckeOperatorHAlong_comm M H ℓ q P
    | dia d => exact heckeOperatorHAlong_diamondHBar_comm M H ℓ d P
  | U q hq hqM =>
    haveI := Fact.mk hq
    cases g' with
    | T ℓ' hℓ' hℓ'S hℓ'M =>
      haveI := Fact.mk hℓ'
      exact heckeOperatorHAlong_comm M H q ℓ' P
    | U q' hq' hq'M =>
      haveI := Fact.mk hq'
      exact heckeOperatorHAlong_comm M H q q' P
    | dia d => exact heckeOperatorHAlong_diamondHBar_comm M H q d P
  | dia d =>
    cases g' with
    | T ℓ' hℓ' hℓ'S hℓ'M =>
      haveI := Fact.mk hℓ'
      exact (heckeOperatorHAlong_diamondHBar_comm M H ℓ' d P).symm
    | U q' hq' hq'M =>
      haveI := Fact.mk hq'
      exact (heckeOperatorHAlong_diamondHBar_comm M H q' d P).symm
    | dia d' =>
      show diamondHBar M H d (diamondHBar M H d' P) = diamondHBar M H d' (diamondHBar M H d P)
      rw [← diamondHBar_mul, ← diamondHBar_mul, mul_comm]

theorem tateGenOpH_comm (g g' : CohCarrier.Gen M (↑S : Set ℕ)) (x : TateModule p (JH M H)) :
    tateGenOpH M H (↑S : Set ℕ) p g (tateGenOpH M H (↑S : Set ℕ) p g' x)
      = tateGenOpH M H (↑S : Set ℕ) p g' (tateGenOpH M H (↑S : Set ℕ) p g x) :=
  Subtype.ext (funext fun n => genOpH_comm M H S g g' ((x : ℕ → JH M H) n))

theorem galois_tateGenOpH_comm (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (g : CohCarrier.Gen M (↑S : Set ℕ)) (x : TateModule p (JH M H)) :
    JH.tateGaloisRep M H p σ (tateGenOpH M H (↑S : Set ℕ) p g x)
      = tateGenOpH M H (↑S : Set ℕ) p g (JH.tateGaloisRep M H p σ x) :=
  Subtype.ext (funext fun n => galois_smul_genOpH_comm M H (↑S : Set ℕ) σ g ((x : ℕ → JH M H) n))

end WeilDetJH

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (b : Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : CohCarrier.Gen M (↑S : Set ℕ) =>
          (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g).baseChange ℚ_[p]))
      (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p (CohCarrier.Gen.dia
        (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange ℚ_[p] *
      (↑((b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 0))) 0 *
            (b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 1))) 1 -
          (b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 1))) 0 *
            (b.repr ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] (b 0))) 1) :
        Module.End ℚ_[p] (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)))) =
      (ℓ : Module.End ℚ_[p] (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)))) := by

  have _hS : ℓ ∉ (↑S : Set ℕ) := hℓS

  refine (ModularCurve.exists_diamondFrobeniusSimilitudePairing_rationalTateModule_jH M p H hin).elim
    fun B hB => ?_
  obtain ⟨hT, hD, halt, hnd, hsim⟩ := hB

  have hcommR : IsMulCommutative (WeilDetPkg.R p (TateModule p (ModularCurve.JH M H))
      (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p)) :=
    WeilDetPkg.isMulCommutative_R _ (WeilDetJH.tateGenOpH_comm M p H S)

  have hbal : ∀ (g : CohCarrier.Gen M (↑S : Set ℕ))
      (x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))),
      B (WeilDetPkg.bc p _ (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g) x) y
        = B x (WeilDetPkg.bc p _ (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g) y) := by
    intro g x y
    cases g with
    | T ℓ' hℓ' hℓ'S hℓ'M => exact hT ℓ' hℓ' x y
    | U q hq hqM => exact hT q hq x y
    | dia d => exact hD d x y

  have hφ : ∀ (g : CohCarrier.Gen M (↑S : Set ℕ)) (x : TateModule p (ModularCurve.JH M H)),
      ModularCurve.JH.tateGaloisRep M H p σ (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g x)
        = ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g (ModularCurve.JH.tateGaloisRep M H p σ x) :=
    fun g x => WeilDetJH.galois_tateGenOpH_comm M p H S σ g x

  have hsim' := hsim ℓ hℓ hℓM hℓp A hA σ hσ

  have hmain := @WeilDetPkg.main p _ (TateModule p (ModularCurve.JH M H)) _ _
    (CohCarrier.Gen M (↑S : Set ℕ)) (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p)
    (ModularCurve.JH.tateGaloisRep M H p σ) B b hcommR halt hnd hbal hφ
    (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))) ℓ hsim'
  exact hmain
