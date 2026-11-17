import ZInQKernel.Contrib.OneProof.MumfordGroupLawRed
import ZInQKernel.Contrib.NeronC.NeronGroup

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.GroupLawNeron

open LeafQM.AV.R1UnivRigid PkgI3

/-- The generic point `Spec K → Spec R` of a domain `R` with fraction field `K`. -/
abbrev genMap (R K : Type) [CommRing R] [Field K] [Algebra R K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- **LEAF `NeronSchemeExtensionDVR`** (Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.4 Thm 3 with §1.2 Def. 1;
numbers UNVERIFIED): an abelian variety `A` over the fraction field `K` of a discrete valuation ring `R` has a
Néron model over `R`. -/
def NeronSchemeExtensionDVR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K]
    [IsFractionRing R K] (A : AbVar K),
    ∃ (N : Over (Spec (CommRingCat.of R))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (ε : (Over.pullback (genMap R K)).obj N ≅ A.X),
      ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
        Function.Surjective fun f : Y ⟶ N => (Over.pullback (genMap R K)).map f ≫ ε.hom

/-- **GLUE `NeronGoodModelIso`.** -/
def NeronGoodModelIso : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F N : Over (Spec (CommRingCat.of R))) (e : Spec (CommRingCat.of R) ⟶ F.left),
    IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 _ →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    Smooth N.hom → IsSeparated N.hom → ∀ ψ : F ⟶ N,
      IsIso ((Over.pullback (genMap R (FractionRing R))).map ψ) → IsIso ψ

/-- The fibre at `s` as an iso of `K`-schemes `s^*F ≅ A`. -/
def fibreIso {S : Scheme.{0}} (F : Over S) {K : Type} [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (A : AbVar K) (g : A.X.left ⟶ F.left) (hpb : IsPullback g A.X.hom F.hom s) :
    (Over.pullback s).obj F ≅ A.X :=
  Over.isoMk hpb.isoPullback.symm (by simp)

@[reassoc]
lemma fibreIso_hom_left_g {S : Scheme.{0}} (F : Over S) {K : Type} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K) (g : A.X.left ⟶ F.left)
    (hpb : IsPullback g A.X.hom F.hom s) :
    (fibreIso F s A g hpb).hom.left ≫ g = pullback.fst F.hom s := by
  simp [fibreIso]

lemma spec_algebraMap_self (K : Type) [Field K] :
    Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := by
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

/-- **`MumfordGroupLawDVR` from Néron models over a DVR and the comparison glue.** -/
theorem mumfordGroupLawDVR_of_neron (hN : NeronSchemeExtensionDVR) (hI : NeronGoodModelIso) :
    ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR := by
  intro R _ _ _ F e hP hS hGC he hfib
  let K := FractionRing R
  let s0 := genMap R K
  obtain ⟨A, g, hpb, hone⟩ := hfib K s0
  obtain ⟨N, hNS, hNsep, hNqc, ε, hext⟩ := hN R K A
  haveI : IsSchemeTheoreticallyDominant s0 :=
    NeronC.isSchemeTheoreticallyDominant_spec_map _ (IsFractionRing.injective R K)
  have hinj : ∀ (Y : Over (Spec (CommRingCat.of R))) [Flat Y.hom],
      Function.Injective fun f : Y ⟶ N => (Over.pullback s0).map f ≫ ε.hom := by
    intro Y _ f f' h
    exact NeronC.pullback_map_injective s0 Y N ((cancel_mono ε.hom).mp h)
  let φ := fibreIso F s0 A g hpb
  haveI : Smooth F.hom := hS
  obtain ⟨ψ, hψ⟩ := hext F φ.hom
  have hψ' : (Over.pullback s0).map ψ = φ.hom ≫ ε.inv := by
    rw [← cancel_mono ε.hom]
    simpa using hψ
  have hiso : IsIso ((Over.pullback s0).map ψ) := by
    rw [hψ']; infer_instance
  haveI hψi : IsIso ψ := hI R F N e hP hS hGC he hfib hNS hNsep ψ hiso
  letI : GrpObj N := NeronC.grpObjOfNeron (Over.pullback s0) (fun Y => Smooth Y.hom)
    (NeronC.smooth_tensorUnit _) (fun X Y hX hY => NeronC.smooth_tensor X Y hX hY) N hNS A.X ε
    (fun Y hY => ⟨@hinj Y inferInstance, @hext Y hY⟩)
  have he' : e ≫ F.hom = (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := he
  let eO : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ F := Over.homMk e he'
  have hη : η[N] = eO ≫ ψ := by
    apply @hinj (𝟙_ _) (by haveI := NeronC.smooth_tensorUnit (Spec (CommRingCat.of R)); infer_instance)
    have h1 : (Over.pullback s0).map η[N] ≫ ε.hom = 1 :=
      NeronC.nPhi_nPsi (Over.pullback s0) (fun Y => Smooth Y.hom) N A.X ε
        (fun Y hY => ⟨@hinj Y inferInstance, @hext Y hY⟩) (NeronC.smooth_tensorUnit _) 1
    simp only
    rw [h1, Functor.map_comp, Category.assoc, hψ', Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Hom.one_def]
    ext1
    rw [Over.comp_left, Over.comp_left, Over.toUnit_left]
    apply hpb.hom_ext
    · rw [Category.assoc, Category.assoc, fibreIso_hom_left_g]
      have h2 : (1 : A.Pt K).left ≫ g = s0 ≫ e := hone
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left] at h2
      simp only [AbVar.ptObj, Over.mk_hom, spec_algebraMap_self] at h2
      have h4 : Over.Hom.left η[A.X] ≫ g = s0 ≫ e := by
        rw [← h2, Category.assoc]; exact (Category.id_comp _).symm
      rw [h4]
      simp only [eO, Over.pullback_map_left, Over.homMk_left, pullback.lift_fst]
      rw [← Category.assoc]
      congr 1
      exact (pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of R)))).hom) (g := s0)).symm
    · simp
  refine ⟨GrpObj.ofIso (asIso ψ).symm, ?_⟩
  change (η[N] ≫ (asIso ψ).symm.hom).left = e
  rw [hη]
  simp [eO]

end ZInQ.Contrib.GroupLawNeron

#print axioms ZInQ.Contrib.GroupLawNeron.mumfordGroupLawDVR_of_neron
