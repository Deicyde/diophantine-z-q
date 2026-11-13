/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Norm), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Norm`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Norm
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.AuxiliaryIdeles
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.AuxiliaryPlaces
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Surjective
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Kummer.LocalDegree
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Tower
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Kummer.Unramified
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Units

public section
noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension
variable {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E]

/-- **The auxiliary Kummer idele classes are norms from an intermediate Kummer field.**
Let `M = K(U_S^{1/p})`, where `S` contains the places above the prime `p`, and let `L/K` be an
intermediate field of `M/K`. There is a finite set `T`, disjoint from `S`, such that
`p ^ #T = [M : L]`, the `S`-units surject onto the local unit `p`-th power classes at `T`, and
the image in `C_K` of the auxiliary Kummer subgroup `E_{S,T}` is contained in
`N_{L/K}(C_L)`. -/
theorem exists_auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap
    {p : ℕ} (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hroots : ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      ∃ x : E, x ^ p = algebraMap K E (a : K))
    (L : IntermediateField K
      (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))) [NumberField L] :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      ∃ hST : Disjoint (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _),
        p ^ T.card = Module.finrank L
            (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) ∧
          Function.Surjective
            (Set.unitLocalPowerClassMap (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) hST p) ∧
          auxiliaryKummerIdeleClassSubgroup (K := K) S T p ≤
            (GlobalNumberFields.ideleClassNormMap K L :
              IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  let M := kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hζK : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p :=
    hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  let _ : HasEnoughRootsOfUnity K p := .of_card_le hζK.card_rootsOfUnity.ge
  let _ : (powMonoidHom p : Kˣ →* Kˣ).range.IsFiniteRelIndex
      ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
    ⟨by rw [relIndex_range_powMonoidHom_sUnits_numberField]; exact pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨T, hST, hcard, hsurj, hsplit⟩ :=
    exists_auxiliaryPlaces_unitLocalPowerClassMap_surjective hp S hpS hζ hroots L
  have hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S := fun _ hv ↦
    TauCeti.NumberField.ramifiedSupport_kummerField_sUnits_subset S hpS
      (NumberField.ramifiedSupport_mono K (L := L) (M := M) hv)
  have hMexp : Monoid.exponent (M ≃ₐ[K] M) ∣ p := exponent_algEquiv_kummerField_dvd
  exact ⟨T, hST, hcard, hsurj,
    auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap_of_ramifiedSupport K L
      ((MonoidHom.exponent_dvd (AlgEquiv.restrictNormalHom_surjective M)).trans hMexp) S T
      (fun v hv _ ↦ hsplit v hv) hram⟩

end TauCeti.ClassFieldTheory

end
end
