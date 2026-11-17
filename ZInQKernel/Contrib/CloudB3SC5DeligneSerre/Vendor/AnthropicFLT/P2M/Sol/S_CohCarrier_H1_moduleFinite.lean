/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CohCarrier_H1_moduleFinite (git blob ed761e2423af328d96f291724f0ce5a441150702, sha256 87896c69a382ea5f3dc1cfb475f40258c3d0fd72dca5af1696a7193f1ba1fd74).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import Mathlib.Algebra.Module.Hom
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Schreier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CohCarrier_H1_moduleFinite.IharaSolFG
end P2MW.S_CohCarrier_H1_moduleFinite.IharaSolFG

namespace P2MW.S_CohCarrier_H1_moduleFinite

set_option autoImplicit false
open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open CohCarrier

namespace IharaSolFG

section CFG

open scoped MatrixGroups

scoped instance SL2Z_fg : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators,
    (Set.finite_singleton _).insert _⟩

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

omit [NeZero M] in

theorem Gamma_le_GammaH : CongruenceSubgroup.Gamma M ≤ GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma_mem] at hA
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr hA.2.2.1
  rw [mem_GammaH_iff]
  refine ⟨h0, ?_⟩
  have hu : gamma0Units M ⟨A, h0⟩ = 1 := Units.ext hA.2.2.2
  rw [hu]
  exact H.one_mem

theorem GammaH_isCongruenceSubgroup : CongruenceSubgroup.IsCongruenceSubgroup (GammaH M H) :=
  ⟨M, NeZero.ne _, Gamma_le_GammaH M H⟩

scoped instance GammaH_finiteIndex : (GammaH M H).FiniteIndex :=
  (GammaH_isCongruenceSubgroup M H).finiteIndex

scoped instance GammaH_fg : Group.FG ↥(GammaH M H) := inferInstance

variable (R : Type*) [CommRing R] (A : Type*) [AddCommGroup A] [Module R A]

def evalAt {Γ : Type*} [Group Γ] (s : Set Γ) : (Additive Γ →+ A) →ₗ[R] (s → A) where
  toFun F x := F (Additive.ofMul (x : Γ))
  map_add' _ _ := funext fun _ => rfl
  map_smul' _ _ := funext fun _ => rfl

theorem evalAt_injective {Γ : Type*} [Group Γ] {s : Set Γ} (hs : Subgroup.closure s = ⊤) :
    Function.Injective (evalAt R A s) := by
  intro F G h
  have key : AddMonoidHom.toMultiplicativeRight F = AddMonoidHom.toMultiplicativeRight G :=
    MonoidHom.eq_of_eqOn_dense hs fun x hx => by
      have hx' : evalAt R A s F ⟨x, hx⟩ = evalAt R A s G ⟨x, hx⟩ := by rw [h]
      exact congrArg Multiplicative.ofAdd hx'
  exact AddMonoidHom.toMultiplicativeRight.injective key

end CFG

end IharaSolFG
open scoped _root_.P2MW.S_CohCarrier_H1_moduleFinite.IharaSolFG

open IharaSolFG in
theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (R : Type*) [CommRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [IsNoetherianRing R] [Module.Finite R A] :
    Module.Finite R (H1 M H A) := by
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG ↥(GammaH M H))
  haveI : Finite s := hfin.to_subtype
  exact Module.Finite.of_injective (evalAt R A s) (evalAt_injective R A hs)

#print axioms solution
