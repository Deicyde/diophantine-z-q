import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.DescendedFamily
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves2
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Two descent leaves, proved from Mathlib

* `properLocalOnBase : ProperLocalOnBase`: properness descends along
  surjective, flat, quasi-compact morphisms.
* `descentClosedImmersion : DescentClosedImmersion`: being a closed immersion
  descends along surjective, flat morphisms locally of finite presentation.

Ingredients from Mathlib:
* fpqc descent of `UniversallyClosed`, `LocallyOfFiniteType` and of
  isomorphisms;
* fpqc descent implies fppf descent for properties local at the target;
* descent passes to diagonals;
* `(isomorphisms C).diagonal = monomorphisms C`, and monomorphisms are
  local at the target;
* a closed immersion is the same as a proper monomorphism.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace Y3Buzzard

/-- Surjective, flat, quasi-compact morphisms (fpqc covers). -/
abbrev fpqcCov : MorphismProperty Scheme.{0} :=
  @Surjective ⊓ @Flat ⊓ @QuasiCompact

/-- Surjective, flat morphisms locally of finite presentation (fppf covers). -/
abbrev fppfCov : MorphismProperty Scheme.{0} :=
  @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation

namespace FromMathlib

/-- fpqc covers are stable under base change. -/
theorem fpqc_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange fpqcCov :=
  { of_isPullback h hq :=
      ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h hq.1.1,
        MorphismProperty.of_isPullback (P := @Flat) h hq.1.2⟩,
        MorphismProperty.of_isPullback (P := @QuasiCompact) h hq.2⟩ }

/-- fppf covers are stable under base change. -/
theorem fppf_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange fppfCov :=
  { of_isPullback h hq :=
      ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h hq.1.1,
        MorphismProperty.of_isPullback (P := @Flat) h hq.1.2⟩,
        MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h hq.2⟩ }

/-- Separatedness unfolded: the diagonal is a closed immersion. -/
theorem isSeparated_iff_diag {X Y : Scheme.{0}} (f : X ⟶ Y) :
    IsSeparated f ↔ IsClosedImmersion (pullback.diagonal f) := by
  first
  | (rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
     exact MorphismProperty.diagonal_iff)
  | exact ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- A universally closed diagonal is a closed immersion: the diagonal is an
immersion (hence locally of finite type) and a split monomorphism (hence
separated), so it is proper, and a proper monomorphism is a closed immersion. -/
theorem closedImmersion_diagonal_of_uc {X Y : Scheme.{0}} (f : X ⟶ Y)
    (h : UniversallyClosed (pullback.diagonal f)) :
    IsClosedImmersion (pullback.diagonal f) := by
  haveI hmono : Mono (pullback.diagonal f) := by
    first
    | infer_instance
    | exact IsSplitMono.mono _
  haveI himm : IsImmersion (pullback.diagonal f) := by
    first
    | infer_instance
    | exact IsImmersion.instDiagonalScheme f
  have hsep : IsSeparated (pullback.diagonal f) :=
    IsSeparated.isSeparated_of_mono (pullback.diagonal f)
  have hlft : LocallyOfFiniteType (pullback.diagonal f) := by
    first
    | infer_instance
    | exact IsImmersion.instLocallyOfFiniteType (pullback.diagonal f)
  have hprop : IsProper (pullback.diagonal f) :=
    (isProper_iff (pullback.diagonal f)).mpr ⟨hsep, h, hlft⟩
  exact (IsClosedImmersion.iff_isProper_and_mono (pullback.diagonal f)).mpr ⟨hprop, hmono⟩

/-- A morphism whose diagonal is universally closed is separated. -/
theorem isSeparated_of_diagonal_uc {X Y : Scheme.{0}} (f : X ⟶ Y)
    (h : UniversallyClosed (pullback.diagonal f)) : IsSeparated f :=
  (isSeparated_iff_diag f).mpr (closedImmersion_diagonal_of_uc f h)

/-- Properness descends along any class `Q` of covers, stable under base change,
along which `UniversallyClosed` and `LocallyOfFiniteType` descend. In the square
`IsPullback fst snd f q`, the cover is `q`, the known morphism is `snd`, and the
conclusion is about `f`. -/
theorem isProper_descends (Q : MorphismProperty Scheme.{0})
    [Q.IsStableUnderBaseChange]
    [MorphismProperty.DescendsAlong @UniversallyClosed Q]
    [MorphismProperty.DescendsAlong @LocallyOfFiniteType Q]
    {W B X Y : Scheme.{0}} {fst : W ⟶ B} {snd : W ⟶ X} {f : B ⟶ Y} {q : X ⟶ Y}
    (h : IsPullback fst snd f q) (hq : Q q) (hsnd : IsProper snd) : IsProper f := by
  obtain ⟨hsep, huc, hlft⟩ := (isProper_iff snd).mp hsnd
  have hucf : UniversallyClosed f :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) (Q := Q)
      h.flip hq huc
  have hlftf : LocallyOfFiniteType f :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) (Q := Q)
      h.flip hq hlft
  -- The diagonal of `snd` is a closed immersion, hence proper, hence universally closed.
  have hdci : IsClosedImmersion (pullback.diagonal snd) := (isSeparated_iff_diag snd).mp hsep
  have hduc : UniversallyClosed (pullback.diagonal snd) :=
    ((isProper_iff (pullback.diagonal snd)).mp
      ((IsClosedImmersion.iff_isProper_and_mono (pullback.diagonal snd)).mp hdci).1).2.1
  -- Universal closedness of the diagonal descends along `Q`.
  haveI hri : MorphismProperty.RespectsIso @UniversallyClosed := by
    first
      | exact inferInstance
      | exact AlgebraicGeometry.universallyClosed_respectsIso
  haveI hdesc : MorphismProperty.DescendsAlong
      (MorphismProperty.diagonal @UniversallyClosed) Q := by
    first
    | infer_instance
    | exact MorphismProperty.instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange
        @UniversallyClosed Q
  have hdf : MorphismProperty.diagonal @UniversallyClosed f :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.diagonal @UniversallyClosed) (Q := Q)
      h.flip hq (MorphismProperty.diagonal_iff.mpr hduc)
  have hsepf : IsSeparated f :=
    isSeparated_of_diagonal_uc f (MorphismProperty.diagonal_iff.mp hdf)
  exact (isProper_iff f).mpr ⟨hsepf, hucf, hlftf⟩

/-- Monomorphisms descend along fpqc covers, via the diagonal of isomorphisms. -/
theorem monomorphisms_descendsAlong_fpqc :
    (MorphismProperty.monomorphisms Scheme.{0}).DescendsAlong fpqcCov := by
  haveI hst : MorphismProperty.IsStableUnderBaseChange fpqcCov :=
    fpqc_isStableUnderBaseChange
  haveI hiso : (MorphismProperty.isomorphisms Scheme.{0}).DescendsAlong fpqcCov :=
    descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact
  haveI hd : (MorphismProperty.isomorphisms Scheme.{0}).diagonal.DescendsAlong fpqcCov := by
    first
    | infer_instance
    | exact MorphismProperty.instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange
        (MorphismProperty.isomorphisms Scheme.{0}) fpqcCov
  first
  | (rw [← MorphismProperty.diagonal_isomorphisms]
     exact hd)
  | exact MorphismProperty.diagonal_isomorphisms ▸ hd
  | exact ⟨fun h hf hfst =>
      (MorphismProperty.monomorphisms.iff _).mpr
        ((pullback.isIso_diagonal_iff _).mp
          ((MorphismProperty.isomorphisms.iff _).mp
            (MorphismProperty.diagonal_iff.mp
              (MorphismProperty.of_isPullback_of_descendsAlong
                (P := (MorphismProperty.isomorphisms Scheme.{0}).diagonal) (Q := fpqcCov)
                h hf
                (MorphismProperty.diagonal_iff.mpr
                  ((MorphismProperty.isomorphisms.iff _).mpr
                    ((pullback.isIso_diagonal_iff _).mpr
                      ((MorphismProperty.monomorphisms.iff _).mp hfst))))))))⟩

/-- Monomorphisms descend along fppf covers. In the square
`IsPullback fst snd g q`, the cover is `g`, the known morphism is `fst`, and
the conclusion is about `q`. -/
theorem mono_of_descends_fppf {W X Y' Y : Scheme.{0}}
    {fst : W ⟶ Y'} {snd : W ⟶ X} {g : Y' ⟶ Y} {q : X ⟶ Y}
    (h : IsPullback fst snd g q) (hg : fppfCov g) (hfst : Mono fst) : Mono q := by
  haveI hmfpqc : (MorphismProperty.monomorphisms Scheme.{0}).DescendsAlong fpqcCov :=
    monomorphisms_descendsAlong_fpqc
  haveI hloc : IsZariskiLocalAtTarget (MorphismProperty.monomorphisms Scheme.{0}) := by
    first
    | infer_instance
    | exact instIsZariskiLocalAtTargetMonomorphismsScheme
  haveI hmfppf : (MorphismProperty.monomorphisms Scheme.{0}).DescendsAlong fppfCov := by
    first
    | infer_instance
    | exact instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
        (MorphismProperty.monomorphisms Scheme.{0})
  have h1 : MorphismProperty.monomorphisms Scheme.{0} q :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.monomorphisms Scheme.{0}) (Q := fppfCov)
      h hg ((MorphismProperty.monomorphisms.iff fst).mpr hfst)
  exact (MorphismProperty.monomorphisms.iff q).mp h1

end FromMathlib

/-- Properness is fpqc local on the base. -/
theorem properLocalOnBase : ProperLocalOnBase := by
  intro W B X Y fst snd f q h hflat hsurj hqc hsnd
  haveI hst : MorphismProperty.IsStableUnderBaseChange fpqcCov :=
    FromMathlib.fpqc_isStableUnderBaseChange
  haveI huc : MorphismProperty.DescendsAlong @UniversallyClosed fpqcCov :=
    descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
  haveI hlft : MorphismProperty.DescendsAlong @LocallyOfFiniteType fpqcCov := by
    first
    | infer_instance
    | exact instDescendsAlongSchemeLocallyOfFiniteTypeMinMorphismPropertySurjectiveFlatQuasiCompact
  exact FromMathlib.isProper_descends fpqcCov h ⟨⟨hsurj, hflat⟩, hqc⟩ hsnd

/-- Being a closed immersion descends along fppf covers. -/
theorem descentClosedImmersion : DescentClosedImmersion := by
  intro X Y Y' q g hflat hsurj hlfp hci
  haveI hst : MorphismProperty.IsStableUnderBaseChange fppfCov :=
    FromMathlib.fppf_isStableUnderBaseChange
  haveI hlocUC : IsZariskiLocalAtTarget @UniversallyClosed := by
    first
    | infer_instance
    | exact universallyClosed_isZariskiLocalAtTarget
  haveI hlocLFT : IsZariskiLocalAtTarget @LocallyOfFiniteType := by
    first
    | infer_instance
    | exact HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFiniteType
  haveI hucQC : MorphismProperty.DescendsAlong @UniversallyClosed fpqcCov :=
    descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
  haveI hlftQC : MorphismProperty.DescendsAlong @LocallyOfFiniteType fpqcCov := by
    first
    | infer_instance
    | exact instDescendsAlongSchemeLocallyOfFiniteTypeMinMorphismPropertySurjectiveFlatQuasiCompact
  haveI hucPP : MorphismProperty.DescendsAlong @UniversallyClosed fppfCov := by
    first
    | infer_instance
    | exact instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
        @UniversallyClosed
  haveI hlftPP : MorphismProperty.DescendsAlong @LocallyOfFiniteType fppfCov := by
    first
    | infer_instance
    | exact instDescendsAlongSchemeMinMorphismPropertySurjectiveFlatLocallyOfFinitePresentationOfQuasiCompactOfIsZariskiLocalAtTarget
        @LocallyOfFiniteType
  have hg : fppfCov g := ⟨⟨hsurj, hflat⟩, hlfp⟩
  obtain ⟨hprop, hmono⟩ := (IsClosedImmersion.iff_isProper_and_mono (pullback.snd q g)).mp hci
  have hpq : IsProper q :=
    FromMathlib.isProper_descends fppfCov (IsPullback.of_hasPullback q g) hg hprop
  have hmq : Mono q :=
    FromMathlib.mono_of_descends_fppf (IsPullback.of_hasPullback q g).flip hg hmono
  exact (IsClosedImmersion.iff_isProper_and_mono q).mpr ⟨hpq, hmq⟩

end Y3Buzzard

end
