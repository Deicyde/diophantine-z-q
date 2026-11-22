import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Dimension at a closed point (minimal 0A21 proof)

Upstream: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
`Variety/Defs/Dimension/ClosedPoint.lean`, Apache-2.0; see L3/LICENSE.
Prominent change notice, 2026-11-14: the statement is unchanged, but its proof is
replaced by the 00OT minimum-over-maximal-ideals characterization on an affine
chart. At a closed point that minimum has exactly one member. This avoids the
unneeded generic-point 00P1 formula and the regular-ring/maximal-chain tree.
All the scheme, field, finite-type and closed-point hypotheses are retained.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u

#cloudR2Vendor topologicalKrullDimAt_eq_krullDimOfRing_stalk in
/-- At a closed point of a scheme locally of finite type over a field, its local
    topological dimension equals the dimension of its local ring (Stacks 0A21). -/
theorem topologicalKrullDimAt_eq_krullDimOfRing_stalk
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    topologicalKrullDimAt X x = ringKrullDim (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let xV : ↥(V : Set X) := ⟨x, hxV⟩
  let e := hV.isoSpec.hom.homeomorph
  let p : PrimeSpectrum Γ(X, V) := e xV
  have hclosedV : IsClosed ({xV} : Set ↥(V : Set X)) := by
    have hpre : (Subtype.val : ↥(V : Set X) → X) ⁻¹' {x} = {xV} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        exact Subtype.ext hz
      · intro hz
        exact congrArg Subtype.val hz
    exact hpre ▸ hx.preimage continuous_subtype_val
  have hclosedP : IsClosed ({p} : Set (PrimeSpectrum Γ(X, V))) := by
    simpa only [p, Set.image_singleton] using e.isClosedMap _ hclosedV
  haveI hpmax : p.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hclosedP
  let g := (f.appLE ⊤ V (by simp)).hom
  letI : Algebra k Γ(X, V) :=
    (g.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  haveI : Algebra.FiniteType k Γ(X, V) := by
    apply RingHom.FiniteType.comp
      (f.finiteType_appLE (isAffineOpen_top (Spec (.of k))) hV (by simp))
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
  have hloc := StacksPort.PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height
    k p
  have hmin : (⨅ m ∈ {m : Ideal Γ(X, V) | m.IsMaximal ∧ p.asIdeal ≤ m},
      (m.height : WithBot ℕ∞)) = (p.asIdeal.height : WithBot ℕ∞) := by
    refine le_antisymm (iInf₂_le p.asIdeal ⟨hpmax, le_rfl⟩) ?_
    refine le_iInf fun m => le_iInf fun hm => ?_
    have heq : p.asIdeal = m := hpmax.eq_of_le hm.1.ne_top hm.2
    rw [heq]
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxV).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal := by
    change IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf xV).asIdeal
    exact hV.isLocalization_stalk xV
  calc
    topologicalKrullDimAt X x = topologicalKrullDimAt V xV :=
      V.isOpen.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq xV
    _ = topologicalKrullDimAt (PrimeSpectrum Γ(X, V)) p :=
      topologicalKrullDimAt_eq_of_homeomorph e xV
    _ = StacksPort.TopologicalSpace.localKrullDim (PrimeSpectrum Γ(X, V)) p :=
      StacksPort.TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim _ _
    _ = (p.asIdeal.height : WithBot ℕ∞) := hloc.2.trans hmin
    _ = ringKrullDim (X.presheaf.stalk x) :=
      (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)).symm

end AlgebraicGeometry
end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
