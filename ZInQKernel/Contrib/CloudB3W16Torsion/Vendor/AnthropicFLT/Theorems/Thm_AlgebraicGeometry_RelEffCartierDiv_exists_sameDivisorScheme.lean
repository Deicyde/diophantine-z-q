/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_sameDivisorScheme. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_sameDivisorScheme

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding prodKerGraph_comap_mapOnProdOver

theorem AlgebraicGeometry.RelEffCartierDiv.exists_sameDivisorScheme
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f] (r : ℕ) :
    ∃ (R : Scheme.{u}) (s t : R ⟶ fibrePowOver f r)
      (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r),
      IsClosedImmersion (pullback.lift s t hst) ∧
      (IsFinite s ∧ Flat s ∧ LocallyOfFinitePresentation s ∧ Surjective s ∧
        ∀ x, s.finrank x = r.factorial) ∧
      (IsFinite t ∧ Flat t ∧ LocallyOfFinitePresentation t ∧ Surjective t ∧
        ∀ x, t.finrank x = r.factorial) ∧
      ∀ ⦃T' : Scheme.{u}⦄ (u v : T' ⟶ fibrePowOver f r)
        (huv : u ≫ fibrePowOver.toBase f r = v ≫ fibrePowOver.toBase f r),
        (∃ w : T' ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
          SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
            (fun i => v ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv]) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_sameDivisorScheme.solution
