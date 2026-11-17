/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_of_isStandardSmooth
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry IsLocalRing

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  classical
  obtain ⟨U, hU, V, hV, hxV, hle, hstd⟩ :=
    Smooth.exists_isStandardSmooth (f := f) x
  have hfxU : f.base x ∈ U := hle hxV
  obtain rfl : U = ⊤ := top_le_iff.mp fun y _ => by
    rw [Subsingleton.elim y (f.base x)]; exact hfxU
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let ψ : k →+* Γ(X, V) := (f.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmooth :=
    RingHom.isStandardSmooth_respectsIso.2 _ e hstd
  letI : Algebra k Γ(X, V) := ψ.toAlgebra
  haveI : Algebra.IsStandardSmooth k Γ(X, V) :=
    (RingHom.isStandardSmooth_algebraMap).mp hψ
  haveI hreg : IsRegularLocalRing (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) :=
    isRegularLocalRing_localization_atPrime_of_isStandardSmooth k Γ(X, V)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxV).hom.toAlgebra
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv
