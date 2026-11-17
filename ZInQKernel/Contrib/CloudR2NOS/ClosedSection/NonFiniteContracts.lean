/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 Step-2 producer item for C3: (B2.a) `NonFiniteContractsSubvariety` (C3
`Step2B2/Plan.lean` 09cbbfbe, statement used verbatim through the import), PROVED natively from
Mathlib. SOURCE ONLY, UNCOMPILED. Native HELD. Universe u, default options.

Route (Stacks 02OG-style, all Mathlib):
1. `φ` is proper (`fX` proper, `fP` separated). Not finite ⇒ not locally quasi-finite
   (`IsFinite.of_isProper_of_locallyQuasiFinite`, `quasiFiniteLocus_eq_top_iff`); the closed
   complement of the quasi-finite locus has a closed point `x₀` (`IsClosed.exists_closed_singleton`).
2. `y₀ = φ x₀` is closed (proper ⇒ closed map), so `Spec κ(y₀) → P` is a closed immersion
   (`isClosed_singleton_iff_isClosedImmersion`); and `Spec κ(y₀) → Spec K` is an ISOMORPHISM: the
   composite `K → κ(y₀) → κ(x₀)` is Mathlib's `residueFieldIsoBase` (K algebraically closed,
   `x₀` closed in a finite-type `K`-scheme), and `κ(y₀) → κ(x₀)` is an injective field map.
3. In the Noetherian fibre `X_{y₀}`, the point over `x₀` is not open
   (`quasiFiniteAt_iff_isOpen_singleton_asFiber`), so it lies in an irreducible closed `Z` with a
   second point (pure topology, `exists_irreducible_closed_of_not_isOpen_singleton`).
4. `C` := the reduced induced subscheme on `Z` (`vanishingIdeal`), integral
   (`isIntegral_subscheme_vanishingIdeal`: radical ideals on the affine cover + irreducible support).
   `i = C ↪ X_{y₀} ↪ X` is a closed immersion; `i ≫ φ` factors through `Spec κ(y₀) ≅ Spec K` by the
   fibre square, giving the `K`-point `p`; `C` irreducible with two points cannot be finite (finite
   ⇒ discrete) over `K`.
Truth: TRUE (C3 sketch; this is the proof).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.Plan
import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.NonFiniteContracts

/-- In a Noetherian space, a point whose singleton is not open lies in an irreducible closed set
containing a second point. -/
theorem exists_irreducible_closed_of_not_isOpen_singleton {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] (t : T) (ht : ¬ IsOpen ({t} : Set T)) :
    ∃ Z : Set T, IsClosed Z ∧ IsIrreducible Z ∧ t ∈ Z ∧ ∃ z ∈ Z, z ≠ t := by
  classical
  by_contra hcon
  push_neg at hcon
  apply ht
  let W : Set T := ⋃₀ {Z ∈ irreducibleComponents T | t ∉ Z}
  have hW : IsClosed W :=
    ((NoetherianSpace.finite_irreducibleComponents (α := T)).subset fun Z hZ => hZ.1).isClosed_sUnion
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  have heq : ({t} : Set T) = Wᶜ := by
    ext x
    constructor
    · rintro rfl ⟨Z, ⟨_, htZ⟩, hxZ⟩
      exact htZ hxZ
    · intro hx
      obtain ⟨Z, hZ, hxZ⟩ : ∃ Z ∈ irreducibleComponents T, x ∈ Z := by
        have hxU : x ∈ ⋃₀ irreducibleComponents T := by
          rw [sUnion_irreducibleComponents]
          trivial
        exact hxU
      by_cases htZ : t ∈ Z
      · exact hcon Z (isClosed_of_mem_irreducibleComponents Z hZ) hZ.1 htZ x hxZ
      · exact (hx ⟨Z, ⟨hZ, htZ⟩, hxZ⟩).elim
  rw [heq]
  exact hW.isOpen_compl

/-- The reduced induced subscheme on an irreducible closed set is integral. -/
theorem isIntegral_subscheme_vanishingIdeal {T : Scheme.{u}} (Z : TopologicalSpace.Closeds T)
    (hZ : IsIrreducible (Z : Set T)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Subtype.irreducibleSpace (by rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact hZ)
  haveI : ∀ U, IsReduced
      ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) := by
    intro U
    have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).IsRadical := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      show (PrimeSpectrum.vanishingIdeal _).radical ≤ _
      refine le_of_eq ?_
      rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
        PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.vanishingIdeal_closure]
    haveI : _root_.IsReduced (Γ(T, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).1 hrad
    exact inferInstanceAs (IsReduced (Spec (CommRingCat.of
      (Γ(T, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U))))
  haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    IsReduced.of_openCover (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- **(B2.a) proved.** -/
theorem nonFiniteContractsSubvariety :
    ZInQ.Contrib.CloudR2NOS.Step2B2.NonFiniteContractsSubvariety.{u} := by
  intro K _ _ X P fX fP _ _ φ hφ hnf
  -- (1) `φ` is proper; a closed point where it is not quasi-finite
  haveI : IsProper (φ ≫ fP) := by rw [hφ]; infer_instance
  haveI : IsProper φ := IsProper.of_comp (f := φ) (g := fP)
  have hnq : ∃ x : X, x ∉ (φ.quasiFiniteLocus : Set X) := by
    by_contra h
    push_neg at h
    apply hnf
    haveI : LocallyQuasiFinite φ := φ.quasiFiniteLocus_eq_top_iff.1 (eq_top_iff.2 fun x _ => h x)
    exact IsFinite.of_isProper_of_locallyQuasiFinite φ
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fX
  obtain ⟨x₀, hx₀Q, hx₀⟩ :=
    (φ.quasiFiniteLocus.isOpen.isClosed_compl).exists_closed_singleton hnq
  have hnqa : ¬ φ.QuasiFiniteAt x₀ := fun h => hx₀Q (Scheme.Hom.mem_quasiFiniteLocus.2 h)
  -- (2) the image point is closed, with residue field `K`
  have hy₀ : IsClosed ({φ.base x₀} : Set P) := by
    have h := φ.isClosedMap _ hx₀
    rwa [Set.image_singleton] at h
  haveI : IsClosedImmersion (P.fromSpecResidueField (φ.base x₀)) :=
    (isClosed_singleton_iff_isClosedImmersion).1 hy₀
  obtain ⟨e, he⟩ : ∃ e : X.residueField x₀ ≅ CommRingCat.of K,
      X.fromSpecResidueField x₀ ≫ fX = Spec.map e.inv :=
    ⟨residueFieldIsoBase fX x₀ hx₀, (SpecMap_residueFieldIsoBase_inv fX x₀ hx₀).symm⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : CommRingCat.of K ⟶ P.residueField (φ.base x₀),
      Spec.map ψ = P.fromSpecResidueField (φ.base x₀) ≫ fP :=
    ⟨_, Spec.map_preimage _⟩
  have hcomp : ψ ≫ φ.residueFieldMap x₀ = e.inv := by
    apply Spec.map_inj.1
    rw [Spec.map_comp, hψ, ← Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc, hφ, he]
  have hr_inj : Function.Injective (φ.residueFieldMap x₀) := (φ.residueFieldMap x₀).hom.injective
  have hψ_bij : Function.Bijective ψ := by
    refine ⟨ψ.hom.injective, fun a => ⟨e.hom (φ.residueFieldMap x₀ a), hr_inj ?_⟩⟩
    have h := congrArg (fun f => f (e.hom (φ.residueFieldMap x₀ a))) hcomp
    simp only [CommRingCat.comp_apply, Iso.hom_inv_id_apply] at h
    exact h
  haveI : IsIso ψ := (ConcreteCategory.isIso_iff_bijective ψ).2 hψ_bij
  haveI : IsIso (P.fromSpecResidueField (φ.base x₀) ≫ fP) := by
    rw [← hψ]
    infer_instance
  -- (3) the fibre is Noetherian and the point over `x₀` is not isolated in it
  haveI : IsLocallyNoetherian (φ.fiber (φ.base x₀)) :=
    inferInstanceAs (IsLocallyNoetherian (pullback φ (P.fromSpecResidueField (φ.base x₀))))
  haveI : CompactSpace (φ.fiber (φ.base x₀)) :=
    inferInstanceAs (CompactSpace (pullback φ (P.fromSpecResidueField (φ.base x₀))))
  haveI : IsNoetherian (φ.fiber (φ.base x₀)) :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have hnotopen : ¬ IsOpen ({φ.asFiber x₀} : Set (φ.fiber (φ.base x₀))) := fun h =>
    hnqa (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.2 h)
  obtain ⟨Z, hZc, hZi, htZ, z, hzZ, hzt⟩ :=
    exists_irreducible_closed_of_not_isOpen_singleton (φ.asFiber x₀) hnotopen
  -- (4) the integral subscheme `C` on `Z`
  let Zc : TopologicalSpace.Closeds (φ.fiber (φ.base x₀)) := ⟨Z, hZc⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Zc
  haveI hCint : IsIntegral I.subscheme := isIntegral_subscheme_vanishingIdeal Zc hZi
  haveI : IsClosedImmersion (φ.fiberι (φ.base x₀)) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst φ (P.fromSpecResidueField (φ.base x₀))))
  let i : I.subscheme ⟶ X := I.subschemeι ≫ φ.fiberι (φ.base x₀)
  haveI : IsClosedImmersion i := inferInstance
  have hsq : φ.fiberι (φ.base x₀) ≫ φ =
      φ.fiberToSpecResidueField (φ.base x₀) ≫ P.fromSpecResidueField (φ.base x₀) :=
    pullback.condition
  refine ⟨I.subscheme, i, inferInstance, hCint,
    inv (P.fromSpecResidueField (φ.base x₀) ≫ fP) ≫ P.fromSpecResidueField (φ.base x₀), ?_, ?_⟩
  · -- the contraction to the `K`-point
    simp only [i, Category.assoc]
    rw [← hφ]
    simp only [Category.assoc]
    rw [hsq, reassoc_of% hsq, ← Category.assoc (P.fromSpecResidueField (φ.base x₀)) fP,
      IsIso.hom_inv_id_assoc]
  · -- `C` is irreducible with two points, hence not finite (finite ⇒ discrete) over `K`
    intro hfin
    haveI : IsFinite (i ≫ fX) := hfin
    haveI : LocallyQuasiFinite (i ≫ fX) := inferInstance
    obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
    have hdisc := (i ≫ fX).isDiscrete_preimage_singleton pt
    have huniv : ((i ≫ fX) ⁻¹' {pt} : Set I.subscheme) = Set.univ :=
      Set.eq_univ_of_forall fun c => show (i ≫ fX).base c = pt from Subsingleton.elim _ _
    rw [huniv, isDiscrete_univ_iff] at hdisc
    haveI := hdisc
    have hsupp : ((I.support : Set (φ.fiber (φ.base x₀)))) = Z :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal Zc
    obtain ⟨a, ha⟩ : φ.asFiber x₀ ∈ Set.range I.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hsupp]
      exact htZ
    obtain ⟨b, hb⟩ : z ∈ Set.range I.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hsupp]
      exact hzZ
    have hab : a ≠ b := fun h =>
      hzt (hb.symm.trans ((congrArg (fun c => I.subschemeι.base c) h).symm.trans ha))
    obtain ⟨w, -, hwa, hwb⟩ := (IrreducibleSpace.isIrreducible_univ I.subscheme).2 {a} {b}
      (isOpen_discrete _) (isOpen_discrete _) ⟨a, trivial, rfl⟩ ⟨b, trivial, rfl⟩
    exact hab (hwa.symm.trans hwb)

end ZInQ.Contrib.CloudR2NOS.ClosedSection.NonFiniteContracts
