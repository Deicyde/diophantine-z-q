import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated localization slice of the Stacks differential base-change port

Upstream: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/RingTheory/Kaehler/BaseChange.lean, Apache-2.0; see L3/LICENSE.
Prominent change notice, 2026-11-14: retain only the two unchanged localization
statements and their original proofs. The unrelated formally-smooth tower
splitting and source metadata are omitted, so no Jacobi-Zariski import is needed.
All actual new declarations are isolated beneath the owned StacksPort namespace;
ordinary export aliases restore upstream notation without root declarations.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

#cloudR2Vendor omega_localization_base in
/-- Localization of the base ring does not change differentials of an algebra
whose scalar map already factors through that localization. -/
theorem omega_localization_base
    (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
    (S : Submonoid A) (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra Aₛ B] [IsScalarTower A Aₛ B] :
    Function.Bijective (KaehlerDifferential.map A Aₛ B B) := by
  refine ⟨?_, KaehlerDifferential.map_surjective A Aₛ B⟩
  have : Algebra.FormallyUnramified A Aₛ :=
    Algebra.FormallyUnramified.of_isLocalization (M := S) (Rₘ := Aₛ)
  have : Subsingleton (Ω[Aₛ⁄A]) := (Algebra.formallyUnramified_iff A Aₛ).mp this
  have : Subsingleton (TensorProduct Aₛ B (Ω[Aₛ⁄A])) := by infer_instance
  have hexact := KaehlerDifferential.exact_mapBaseChange_map A Aₛ B
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, hy⟩ := (hexact x).mp hx
  rw [← hy, Subsingleton.elim y 0, map_zero]

#cloudR2Vendor omega_localization_total in
/-- Differentials localize when the total algebra is localized. -/
theorem omega_localization_total
    (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
    (S : Submonoid B) (Bₛ : Type*) [CommRing Bₛ] [Algebra B Bₛ] [IsLocalization S Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ] :
    IsLocalizedModule S (KaehlerDifferential.map A A B Bₛ) :=
  KaehlerDifferential.isLocalizedModule_map A B Bₛ S

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
