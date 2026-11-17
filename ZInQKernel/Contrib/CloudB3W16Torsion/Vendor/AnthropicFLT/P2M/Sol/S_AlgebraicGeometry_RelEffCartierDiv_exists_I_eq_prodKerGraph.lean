/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
-- Source-local namespace open deferred until its declaration.

namespace AlgebraicGeometry
open _root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph.AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension Scheme Smooth IsSeparated prodKerGraph prodKerGraph_zero prodKerGraph_succ RelEffCartierDiv.empty RelEffCartierDiv.empty_I RelEffCartierDiv.ofPoint RelEffCartierDiv.ofPoint_I RelEffCartierDiv RelEffCartierDiv.exists_I_eq_mul)
namespace RelEffCartierDiv
export _root_.AlgebraicGeometry.RelEffCartierDiv (empty empty_I ofPoint ofPoint_I I exists_I_eq_mul)
namespace SumInduction
open AlgebraicGeometry.RelEffCartierDiv
open AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {T : Scheme.{u}} {g : T ⟶ S}

theorem exists_I_eq_prodKerGraph : ∀ (r : ℕ) (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g),
    ∃ D : RelEffCartierDiv f r g, D.I = prodKerGraph f a ha
  | 0, a, ha => ⟨RelEffCartierDiv.empty f g, by rw [RelEffCartierDiv.empty_I, prodKerGraph_zero]⟩
  | r + 1, a, ha => by
    obtain ⟨E, hE⟩ := exists_I_eq_prodKerGraph r (fun i => a i.succ) (fun i => ha i.succ)
    obtain ⟨F, hF⟩ := RelEffCartierDiv.exists_I_eq_mul E (RelEffCartierDiv.ofPoint f (a 0) (ha 0))
    exact ⟨F, by rw [hF, hE, RelEffCartierDiv.ofPoint_I, prodKerGraph_succ, mul_comm]⟩

end AlgebraicGeometry.RelEffCartierDiv.SumInduction

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    ∃ D : RelEffCartierDiv f r g, D.I = prodKerGraph f a ha :=
  AlgebraicGeometry.RelEffCartierDiv.SumInduction.exists_I_eq_prodKerGraph r a ha
