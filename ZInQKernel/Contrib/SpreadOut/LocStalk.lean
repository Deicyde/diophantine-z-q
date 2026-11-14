import Mathlib
import ZInQKernel.Contrib.SpreadOut.SmoothLocus

/-!
# Spreading out, VI: smoothness at points of a localization base change

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task spread-out, 2026-11-13).

Mathlib only.  Proves the glue `SmoothAtLocalizationBaseChange` of `SmoothLocus.lean`: if `S` is a
localization of `R`, `f : X → Spec R`, and `X ×_R S → Spec S` has a formally smooth stalk map at
`y`, then `f` has a formally smooth stalk map at the image of `y`.
* `formallySmooth_stalkMap_spec_iff`: for `Spec A → Spec R`, formal smoothness of the stalk map
  at `p` is `Algebra.IsSmoothAt R p` (from Mathlib's `Scheme.arrowStalkMapSpecIso`);
* `isSmoothAt_of_tensor`: for `T = A ⊗_R S`, `Tₚ` is a localization of `A` at `p ∩ A`, and `S` is
  formally étale over `R`, so `IsSmoothAt S p` gives `IsSmoothAt R (p ∩ A)`;
* `smoothAtLocalizationBaseChange`: reduce to an affine open `Spec A ⊆ X` via open immersions
  (`Scheme.Hom.preimage_smoothLocus_eq`) and `pullbackSpecIso`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace ZInQ.Contrib.SpreadOut

/-- For `Spec A → Spec R`, formal smoothness of the stalk map at `p` is `IsSmoothAt R p`. -/
theorem formallySmooth_stalkMap_spec_iff {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (p : PrimeSpectrum A) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R A))).stalkMap p).hom.FormallySmooth ↔
      Algebra.IsSmoothAt R p.asIdeal := by
  let q := p.asIdeal
  let p' := q.comap (algebraMap R A)
  haveI : q.LiesOver p' := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p' q
  trans Algebra.FormallySmooth (Localization.AtPrime p') (Localization.AtPrime q)
  · rw [← RingHom.formallySmooth_algebraMap]
    exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R A)) p)
  · exact Algebra.FormallySmooth.iff_restrictScalars.symm

/-- For `T = A ⊗_R S` with `S` a localization of `R`: smoothness of `T` over `S` at `P` gives
smoothness of `A` over `R` at `P ∩ A`. -/
theorem isSmoothAt_of_tensor {R A S : Type} [CommRing R] [CommRing A] [CommRing S] [Algebra R A]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (P : Ideal (A ⊗[R] S)) [P.IsPrime]
    (h : letI : Algebra S (A ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
      Algebra.IsSmoothAt S P) :
    Algebra.IsSmoothAt R (P.comap (algebraMap A (A ⊗[R] S))) := by
  letI : Algebra S (A ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.FormallySmooth R S := Algebra.FormallySmooth.of_isLocalization M
  haveI : Algebra.FormallySmooth S (Localization.AtPrime P) := h
  haveI : Algebra.FormallySmooth R (Localization.AtPrime P) :=
    Algebra.FormallySmooth.comp R S (Localization.AtPrime P)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A M) (A ⊗[R] S) :=
    IsLocalization.tensor S M
  haveI : IsLocalization.AtPrime (Localization.AtPrime P) (P.comap (algebraMap A (A ⊗[R] S))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid A M) (Localization.AtPrime P) P
  let e : Localization.AtPrime (P.comap (algebraMap A (A ⊗[R] S))) ≃ₐ[A]
      Localization.AtPrime P :=
    IsLocalization.algEquiv (P.comap (algebraMap A (A ⊗[R] S))).primeCompl _ _
  exact Algebra.FormallySmooth.of_equiv (e.symm.restrictScalars R)

end ZInQ.Contrib.SpreadOut
