/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_split
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed.AlgebraicGeometry

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension pointOfClosedPoint LocallyOfFiniteType Spec Scheme LocallyOfFiniteType.jacobsonSpace pointOfClosedPoint_comp IsSeparated RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp prodKerGraph RelEffCartierDiv.exists_split prodKerGraph_comap_mapOnProdOver" namespace SumPtsAux end AlgebraicGeometry.SumPtsAux
open scoped AlgebraicGeometry in
theorem AlgebraicGeometry.SumPtsAux.exists_comp_eq_id_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [Nonempty X] :
    ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ :=
    nonempty_inter_closedPoints (X := X) Set.univ_nonempty isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {k : Type u} [Field k] [IsAlgClosed k] {x : Spec (CommRingCat.of k) ⟶ S}
    {r : ℕ} (D : RelEffCartierDiv f r x) :
    ∃ (a : Fin r → (Spec (CommRingCat.of k) ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = x),
      D.I = prodKerGraph f a ha := by
  obtain ⟨P, gP, p, hp, b, hb, hfin, -, -, hsurj, -, hsplit, -⟩ := D.exists_split
  haveI : Nonempty P := by
    obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary _)
    exact ⟨y⟩
  obtain ⟨u, hu⟩ := AlgebraicGeometry.SumPtsAux.exists_comp_eq_id_of_isAlgClosed p
  have hu' : u ≫ gP = x := by rw [← hp, ← Category.assoc, hu, Category.id_comp]
  have key : D = (D.pullbackAlong p hp).pullbackAlong u hu' := by
    rw [RelEffCartierDiv.pullbackAlong_comp]
    have aux : ∀ (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) (hφ : φ ≫ x = x),
        φ = 𝟙 _ → D.pullbackAlong φ hφ = D := by
      rintro φ hφ rfl
      exact D.pullbackAlong_id
    exact (aux _ _ hu).symm
  refine ⟨fun i => u ≫ b i, fun i => by rw [Category.assoc, hb, hu'], ?_⟩
  calc D.I = ((D.pullbackAlong p hp).pullbackAlong u hu').I := by rw [← key]
    _ = (D.pullbackAlong p hp).I.comap (mapOnProdOver f u hu') := rfl
    _ = (prodKerGraph f b hb).comap (mapOnProdOver f u hu') := by rw [hsplit]
    _ = prodKerGraph f (fun i => u ≫ b i) _ := prodKerGraph_comap_mapOnProdOver b hb u hu'
