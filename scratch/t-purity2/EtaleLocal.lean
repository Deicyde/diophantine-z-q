import Mathlib

/-!
# Local flatness + unramified ⇒ étale at a prime

Mathlib v4.35 has `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat` only under *global* flatness of
`S` over `R`.  Here: `R → S` of finite presentation, `q` over `p`, `S_q` flat over `R_p`, and
`R → S` unramified at `q`  ⇒  `R → S` étale at `q`.  The proof follows Mathlib's
`Algebra.IsSmoothAt.of_formallySmooth_fiber` (RingTheory/Smooth/Fiber.lean), with the global
flatness replaced by local flatness and the fibre hypothesis derived from unramifiedness.
-/

open IsLocalRing TensorProduct

namespace TPurity2

local notation "𝓀[" R "]" => ResidueField R

theorem isEtaleAt_of_isUnramifiedAt_of_flat_local {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
    (hflat : letI := Localization.AtPrime.algebraOfLiesOver p q;
      Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)) :
    Algebra.IsEtaleAt R q := by
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom
      (M := Algebra.algebraMapSubmonoid S p.primeCompl)
        (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
        by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : Algebra.FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have : Module.Flat Rp Sq := hflat
  have hU : Algebra.FormallyUnramified R Sq := ‹_›
  have : Algebra.FormallyUnramified Rp Sq := .of_restrictScalars R Rp Sq
  have : IsLocalHom (algebraMap Rp Sq) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  have : Algebra.EssFiniteType R Sq := .comp R S Sq
  have : Algebra.EssFiniteType Rp Sq := .of_comp R Rp Sq
  have : Algebra.FormallyEtale 𝓀[Rp] (𝓀[Rp] ⊗[Rp] Sq) :=
    .of_formallyUnramified_of_field _ _
  have : Algebra.FormallySmooth Rp Sq :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := Rp) (S := Sq) (P := Sp)
      (Algebra.algebraMapSubmonoid _ q.primeCompl)
  have : Algebra.FormallySmooth R Sq := .comp R Rp Sq
  exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hU, ‹_›⟩

end TPurity2

#print axioms TPurity2.isEtaleAt_of_isUnramifiedAt_of_flat_local
