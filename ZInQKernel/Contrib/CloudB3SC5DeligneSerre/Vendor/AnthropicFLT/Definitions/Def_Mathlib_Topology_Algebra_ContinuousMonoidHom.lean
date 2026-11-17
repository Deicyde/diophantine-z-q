/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_Mathlib_Topology_Algebra_ContinuousMonoidHom (git blob 7829c8e30b406c8bb1dcbddf8e8d49745ec5c8ea, sha256 bc86db907bb2c55d1708d7f96f3300774b3da7e94e26689d81d3a5b797856cf8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Mathlib_Topology_Algebra_Module_Quotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

section

def ContinuousAddEquiv.toIntContinuousLinearEquiv {M M₂ : Type*} [AddCommGroup M]
    [TopologicalSpace M] [AddCommGroup M₂] [TopologicalSpace M₂] (e : M ≃ₜ+ M₂) :
    M ≃L[ℤ] M₂ where
  __ := e.toIntLinearEquiv
  continuous_toFun := e.continuous
  continuous_invFun := e.continuous_invFun

def ContinuousAddEquiv.quotientPi {ι : Type*} {G : ι → Type*} [(i : ι) → AddCommGroup (G i)]
    [(i : ι) → TopologicalSpace (G i)]
    [(i : ι) → IsTopologicalAddGroup (G i)]
    [Fintype ι] (p : (i : ι) → AddSubgroup (G i)) [DecidableEq ι] :
    ((i : ι) → G i) ⧸ AddSubgroup.pi (_root_.Set.univ) p ≃ₜ+ ((i : ι) → G i ⧸ p i) :=
  (Submodule.quotientPiContinuousLinearEquiv
    (fun (i : ι) => AddSubgroup.toIntSubmodule (p i))).toContinuousAddEquiv

@[to_additive

                                                              ]
def ContinuousMulEquiv.piUnique {ι : Type*} (M : ι → Type*) [(j : ι) → Mul (M j)]
    [(j : ι) → TopologicalSpace (M j)] [Unique ι] :
    ((j : ι) → M j) ≃ₜ* M default where
  __ := MulEquiv.piUnique M
  continuous_toFun := continuous_apply default
  continuous_invFun := by simpa [continuous_pi_iff, Unique.forall_iff] using continuous_id'

@[to_additive piEquivPiSubtypeProd

                                                                  ]
def ContinuousMulEquiv.piEquivPiSubtypeProd {ι : Type*} (p : ι → Prop) (Y : ι → Type*)
    [(i : ι) → TopologicalSpace (Y i)] [(i : ι) → Mul (Y i)] [DecidablePred p] :
    ((i : ι) → Y i) ≃ₜ* ((i : { x : ι // p x }) → Y i) × ((i : { x : ι // ¬p x }) → Y i) :=
  {Homeomorph.piEquivPiSubtypeProd p Y with map_mul' _ _ := rfl}

def ContinuousMulEquiv.units_map {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [Monoid M] [Monoid N] (f : M ≃ₜ* N) : Mˣ ≃ₜ* Nˣ :=
  {
  __ := Units.mapEquiv f
  continuous_toFun := by apply Continuous.units_map _ f.continuous_toFun
  continuous_invFun := by apply Continuous.units_map _ f.continuous_invFun
      }

@[to_additive]
theorem ContinuousMulEquiv.coe_toHomeomorph {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [CommMonoid M] [CommMonoid N]
    (f : M ≃ₜ* N) : f.toHomeomorph = ⇑f := rfl
