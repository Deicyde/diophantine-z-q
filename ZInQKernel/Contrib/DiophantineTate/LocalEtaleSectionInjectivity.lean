import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Uniqueness of étale sections over a local ring

Reduction along the actual residue quotient is injective on sections of an
étale scheme over `Spec R`. The open diagonal equalizer contains the closed
point of the local spectrum, hence covers the whole spectrum.

This proves uniqueness of existing sections, not existence or torsion lifting.
No Henselian, DVR, Noetherian, domain, properness, separatedness or nilpotence
hypothesis is added. AI-assisted proof development, using public Mathlib APIs.
-/

open CategoryTheory AlgebraicGeometry CommRingCat
open CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace AxiomBridge.LocalEtaleSectionInjectivity

private theorem spec_open_eq_top_of_closedPoint_mem
    (R : Type) [CommRing R] [IsLocalRing R]
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : IsLocalRing.closedPoint R ∈ U) : U = ⊤ := by
  change (U : TopologicalSpace.Opens (PrimeSpectrum R)) = ⊤
  exact (IsLocalRing.closedPoint_mem_iff U).mp hU

private theorem residueSpec_closedPoint
    (R : Type) [CommRing R] [IsLocalRing R] :
    (Spec.map
      (CommRingCat.ofHom
        (algebraMap R (IsLocalRing.ResidueField R))))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
        IsLocalRing.closedPoint R := by
  letI : IsLocalHom
      (algebraMap R (IsLocalRing.ResidueField R)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    infer_instance
  exact AlgebraicGeometry.Spec_closedPoint
    (f := CommRingCat.ofHom
      (algebraMap R (IsLocalRing.ResidueField R)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The diagonal equalizer of two sections covers the entire local base. -/
private theorem sections_hom_ext
    (R : Type) [CommRing R] [IsLocalRing R]
    {T : Scheme.{0}} (p : T ⟶ Spec (CommRingCat.of R)) [Etale p]
    (a b : Spec (CommRingCat.of R) ⟶ T)
    (ha : a ≫ p = 𝟙 _) (hb : b ≫ p = 𝟙 _)
    (hr :
      Spec.map
          (CommRingCat.ofHom
            (algebraMap R (IsLocalRing.ResidueField R))) ≫ a =
        Spec.map
          (CommRingCat.ofHom
            (algebraMap R (IsLocalRing.ResidueField R))) ≫ b) :
    a = b := by
  have hEt : Etale p := inferInstance
  haveI : FormallyUnramified p :=
    (Etale.iff_flat_and_formallyUnramified.mp hEt).2.1
  haveI : LocallyOfFinitePresentation p :=
    (Etale.iff_flat_and_formallyUnramified.mp hEt).2.2
  haveI : LocallyOfFiniteType p := inferInstance

  let K : Scheme.{0} := Spec (CommRingCat.of (IsLocalRing.ResidueField R))
  let r : K ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap R (IsLocalRing.ResidueField R)))
  let k : K := IsLocalRing.closedPoint (IsLocalRing.ResidueField R)

  let v : Spec (CommRingCat.of R) ⟶ pullback p p :=
    pullback.lift a b (ha.trans hb.symm)
  let d : T ⟶ pullback p p := pullback.diagonal p
  haveI : IsOpenImmersion d := by
    change IsOpenImmersion (pullback.diagonal p)
    exact FormallyUnramified.isOpenImmersion_diagonal p

  let E : Scheme.{0} := pullback d v
  let e : E ⟶ Spec (CommRingCat.of R) := pullback.snd d v
  haveI : IsOpenImmersion e := by
    change IsOpenImmersion (pullback.snd d v)
    infer_instance

  have key : (r ≫ a) ≫ d = r ≫ v := by
    apply pullback.hom_ext
    · simp only [d, v, Category.assoc, pullback.diagonal_fst,
        pullback.lift_fst, Category.comp_id]
    · simpa only [d, v, r, Category.assoc, pullback.diagonal_snd,
        pullback.lift_snd, Category.comp_id] using hr

  let z : K ⟶ E := pullback.lift (r ≫ a) r key
  have hze : z ≫ e = r := by
    simpa only [z, e] using
      (pullback.lift_snd (f := d) (g := v) (r ≫ a) r key)

  have hEa : pullback.fst d v = e ≫ a := by
    have H := congrArg
      (fun q : E ⟶ pullback p p => q ≫ pullback.fst p p)
      (pullback.condition (f := d) (g := v))
    simpa only [d, v, e, Category.assoc, pullback.diagonal_fst,
      pullback.lift_fst, Category.comp_id] using H

  have hEb : pullback.fst d v = e ≫ b := by
    have H := congrArg
      (fun q : E ⟶ pullback p p => q ≫ pullback.snd p p)
      (pullback.condition (f := d) (g := v))
    simpa only [d, v, e, Category.assoc, pullback.diagonal_snd,
      pullback.lift_snd, Category.comp_id] using H

  have hpoint : e (z k) = IsLocalRing.closedPoint R := by
    calc
      e (z k) = r k := by
        simpa only [Scheme.Hom.comp_apply] using
          congrArg
            (fun q : K ⟶ Spec (CommRingCat.of R) => q k) hze
      _ = IsLocalRing.closedPoint R := by
        simpa only [r, k] using residueSpec_closedPoint R

  have hk : IsLocalRing.closedPoint R ∈ e.opensRange := by
    apply Scheme.Hom.mem_opensRange.mpr
    exact ⟨z k, hpoint⟩

  have heTop : e.opensRange = ⊤ :=
    spec_open_eq_top_of_closedPoint_mem R e.opensRange hk
  haveI : IsIso e :=
    AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top e heTop
  haveI : Epi e := CategoryTheory.IsIso.epi_of_iso e
  exact (CategoryTheory.cancel_epi (g := a) (h := b) e).mp
    (hEa.symm.trans hEb)

/-- Restriction to the actual residue quotient is injective on étale sections. -/
theorem sections_reduction_injective
    (R : Type) [CommRing R] [IsLocalRing R]
    (T : Over (Spec (CommRingCat.of R))) [Etale T.hom] :
    Function.Injective
      (fun Q : 𝟙_ (Over (Spec (of R))) ⟶ T =>
        toUnit
          (Over.mk
            (Spec.map
              (ofHom
                (algebraMap R (IsLocalRing.ResidueField R))))) ≫ Q) := by
  intro Q₁ Q₂ hQ
  apply Over.OverMorphism.ext
  apply sections_hom_ext R T.hom Q₁.left Q₂.left
  · simpa only [Over.tensorUnit_hom] using (Over.w Q₁)
  · simpa only [Over.tensorUnit_hom] using (Over.w Q₂)
  · have hleft :=
      congrArg
        (fun f :
          Over.mk
              (Spec.map
                (ofHom
                  (algebraMap R (IsLocalRing.ResidueField R)))) ⟶ T =>
          f.left)
        hQ
    simp only [Over.comp_left, Over.toUnit_left] at hleft
    dsimp only [Over.left, Over.hom, Over.mk, CostructuredArrow.mk] at hleft ⊢
    exact hleft

end AxiomBridge.LocalEtaleSectionInjectivity
