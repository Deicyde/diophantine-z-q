/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.Defs
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_generates_annihilator_iff_of_isPullback

/-!
# W13 dictionary D7, step 1: base change of a fake elliptic curve with full level-3 structure

`exists_isPullback`: for every ring map `φ : S →+* S'` and every `u : WithFullLevel Λ 1 3 S`, there
is `u' : WithFullLevel Λ 1 3 S'` with `WithFullLevel.IsPullback φ u u'`. The fake elliptic curve
comes from the FLT source theorem `FakeEllipticCurve.exists_isPullback_levelIff`. The level point
`P'` is the pullback lift of `P`; its torsion is transported along the point equivalence
`exists_equiv_schemeHomOver_of_isPullback`, and `generates`/`annihilator` along
`generates_annihilator_iff_of_isPullback`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D7

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open ZInQ.Contrib.CloudW03NeronSurj.FLT.CerednikDrinfeld.QM
open ZInQ.Contrib.CloudB2Shimura.Dictionary

/-- `nsmulPt` is natural in the test scheme. -/
lemma nsmulPt_comp {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ)
    (x : SchemeHomOver t f) :
    nsmulPt L t' n (schemeHomOverComp ψ hψ x) = schemeHomOverComp ψ hψ (nsmulPt L t n x) := by
  induction n with
  | zero => exact (L.one_natural t t' ψ hψ).symm
  | succ n ih =>
    change L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n x) x)
    rw [ih, L.mul_natural t t' ψ hψ]

/-- **D7.1: base change of objects of the moduli problem.** -/
theorem exists_isPullback {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (u : L3 S) :
    ∃ u' : L3 S', FakeEllipticCurve.WithFullLevel.IsPullback φ u u' := by
  obtain ⟨E', g, hg, hmul, hact, hlev, -⟩ := FakeEllipticCurve.exists_isPullback_levelIff φ u.1
  have hw : (Spec.map (CommRingCat.ofHom φ) ≫ u.2.P.1) ≫ u.1.f =
      𝟙 (Spec (CommRingCat.of S')) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.assoc, u.2.P.2, Category.comp_id, Category.id_comp]
  let P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) E'.f := ⟨hg.lift _ _ hw, hg.lift_snd _ _ _⟩
  have hP' : P'.1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ u.2.P.1 := hg.lift_fst _ _ _
  obtain ⟨σ, hσ, hσ1, -, -, hσn, -⟩ :=
    FakeEllipticCurve.exists_equiv_schemeHomOver_of_isPullback φ u.1 E' g hg hmul hact
      (𝟙 (Spec (CommRingCat.of S')))
  have hψ : Spec.map (CommRingCat.ofHom φ) ≫ 𝟙 (Spec (CommRingCat.of S)) =
      𝟙 (Spec (CommRingCat.of S')) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.comp_id, Category.id_comp]
  have hσP : σ P' = schemeHomOverComp (Spec.map (CommRingCat.ofHom φ)) hψ u.2.P :=
    Subtype.ext ((hσ P').trans hP')
  have htors : nsmulPt E'.L (𝟙 (Spec (CommRingCat.of S'))) 3 P' =
      E'.L.one (𝟙 (Spec (CommRingCat.of S'))) := by
    apply σ.injective
    rw [hσn, hσ1, hσP, nsmulPt_comp, u.2.torsion, u.1.L.one_natural]
  refine ⟨⟨E', { P := P', torsion := htors, generates := ?_, annihilator := ?_ }⟩,
    g, hg, hmul, hact, hlev, hP'⟩
  · intro k _ _ sk
    exact ((FakeEllipticCurve.generates_annihilator_iff_of_isPullback Λ 1 3 S S' φ u.1 u.2.P E' g
      hg hmul hact P' hP' k sk).2 ⟨u.2.generates k (sk.comp φ), u.2.annihilator k (sk.comp φ)⟩).1
  · intro k _ _ sk
    exact ((FakeEllipticCurve.generates_annihilator_iff_of_isPullback Λ 1 3 S S' φ u.1 u.2.P E' g
      hg hmul hact P' hP' k sk).2 ⟨u.2.generates k (sk.comp φ), u.2.annihilator k (sk.comp φ)⟩).2

/-- `BCInput`, proved. -/
theorem bcInput : BCInput := fun _ _ _ _ φ u => exists_isPullback φ u

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D7
