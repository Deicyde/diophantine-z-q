import ZInQKernel.Contrib.OneProof.NeronGoodModelIso
import ZInQKernel.Contrib.OneProof.NeronDVRLocalSH

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace DedekindFree

open ZInQ.Contrib ZInQ.Contrib.GroupLawNeron ZInQ.Contrib.GoodModelIso LeafQM.AV.R1UnivRigid PkgI3

section Local

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- `NeronSchemeExtensionDVR` at one DVR `R`. -/
def NeronExtAt : Prop :=
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (A : AbVar K),
    ∃ (N : Over (Spec (CommRingCat.of R))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (ε : (Over.pullback (genMap R K)).obj N ≅ A.X),
      ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
        Function.Surjective fun f : Y ⟶ N => (Over.pullback (genMap R K)).map f ≫ ε.hom

/-- Over a henselian DVR, from the vendored FLT theorem. -/
theorem neronExtAt_of_henselian [HenselianLocalRing R] : NeronExtAt R := by
  intro K _ _ _ A
  obtain ⟨N, hN, ⟨ε⟩⟩ := NeronFLT.exists_neron_of_henselian R K A
  obtain ⟨hS, hSep, -, hQC, hB⟩ := hN
  refine ⟨N, hS, hSep, hQC, ε, fun Y _ g => ?_⟩
  obtain ⟨f, hf⟩ := (hB Y).2 (g ≫ ε.inv)
  refine ⟨f, ?_⟩
  have hf' : (Over.pullback (genMap R K)).map f = g ≫ ε.inv := hf
  change (Over.pullback (genMap R K)).map f ≫ ε.hom = g
  rw [hf', Category.assoc, Iso.inv_hom_id, Category.comp_id]


/-- `NeronGoodModelIso` at one DVR `R` (body of `ZInQ.Contrib.GroupLawNeron.NeronGoodModelIso` with `R` fixed). -/
def GoodModelIsoAt : Prop :=
  ∀ (F N : Over (Spec (CommRingCat.of R))) (e : Spec (CommRingCat.of R) ⟶ F.left),
    IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 _ →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    Smooth N.hom → IsSeparated N.hom → ∀ ψ : F ⟶ N,
      IsIso ((Over.pullback (genMap R (FractionRing R))).map ψ) → IsIso ψ

/-- `MumfordGroupLawDVR` at one DVR `R`. -/
def MumfordGroupLawAt : Prop :=
  ∀ (F : Over (Spec (CommRingCat.of R))) (e : Spec (CommRingCat.of R) ⟶ F.left),
    IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 _ →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

/-- goodmodel-iso's `neronGoodModelIso_of_dvr`, at one DVR (proof copied, `R` fixed). -/
theorem goodModelIsoAt (hN : NeronExtAt R) : GoodModelIsoAt R := by
  intro F N e hP hS hGC he hfib hNS hNsep ψ hK
  haveI := hP; haveI := hS; haveI := hNS; haveI := hNsep
  let K := FractionRing R
  let s0 := genMap R K
  haveI := genMap_isSchemeTheoreticallyDominant (R := R) K
  obtain ⟨A, g, hpb, hone⟩ := hfib K s0
  obtain ⟨N', hN'S, hN'sep, hN'qc, ε, hext⟩ := hN K A
  haveI := hN'S; haveI := hN'sep; haveI := hN'qc
  have hinj : ∀ (Y : Over (Spec (CommRingCat.of R))) [Flat Y.hom],
      Function.Injective fun f : Y ⟶ N' => (Over.pullback s0).map f ≫ ε.hom := by
    intro Y _ f f' h
    exact NeronC.pullback_map_injective s0 Y N' ((cancel_mono ε.hom).mp h)
  let φ := fibreIso F s0 A g hpb
  letI : GrpObj N' := NeronC.grpObjOfNeron (Over.pullback s0) (fun Y => Smooth Y.hom)
    (NeronC.smooth_tensorUnit _) (fun X Y hX hY => NeronC.smooth_tensor X Y hX hY) N' hN'S A.X ε
    (fun Y hY => ⟨@hinj Y inferInstance, @hext Y hY⟩)
  haveI : IsIso ((Over.pullback s0).map ψ) := hK
  obtain ⟨χ, hχ⟩ := hext N (inv ((Over.pullback s0).map ψ) ≫ φ.hom)
  have hχ' : (Over.pullback s0).map χ ≫ ε.hom = inv ((Over.pullback s0).map ψ) ≫ φ.hom := hχ
  let ψ' := ψ ≫ χ
  have hψ' : (Over.pullback s0).map ψ' = φ.hom ≫ ε.inv := by
    rw [← cancel_mono ε.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp,
      Category.assoc, hχ', IsIso.hom_inv_id_assoc]
  have hiso : IsIso ((Over.pullback s0).map ψ') := by rw [hψ']; infer_instance
  have he' : e ≫ F.hom = (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := he
  let eO : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ F := Over.homMk e he'
  have hη : η[N'] = eO ≫ ψ' := by
    apply @hinj (𝟙_ _) (by haveI := NeronC.smooth_tensorUnit (Spec (CommRingCat.of R)); infer_instance)
    have h1 : (Over.pullback s0).map η[N'] ≫ ε.hom = 1 :=
      NeronC.nPhi_nPsi (Over.pullback s0) (fun Y => Smooth Y.hom) N' A.X ε
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
      simp only [PkgI3.AbVar.ptObj, Over.mk_hom, spec_algebraMap_self] at h2
      have h4 : Over.Hom.left η[A.X] ≫ g = s0 ≫ e := by
        rw [← h2, Category.assoc]; exact (Category.id_comp _).symm
      rw [h4]
      simp only [eO, Over.pullback_map_left, Over.homMk_left, pullback.lift_fst]
      rw [← Category.assoc]
      congr 1
      exact (pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of R)))).hom) (g := s0)).symm
    · simp
  have hηl : e ≫ ψ'.left = η[N'].left := by rw [hη]; rfl
  haveI : IsIso ψ' := isIso_of_grp F N' e he hfib ψ' hηl hiso
  let r := χ ≫ inv ψ'
  have h1 : ψ ≫ r = 𝟙 F := by
    simp only [r, ← Category.assoc]; exact IsIso.hom_inv_id ψ'
  have h2 : r ≫ ψ = 𝟙 N := by
    apply NeronC.pullback_map_injective s0 N N
    have h3 : (Over.pullback s0).map ψ ≫ (Over.pullback s0).map r = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, h1, CategoryTheory.Functor.map_id]
    have h4 : (Over.pullback s0).map r = inv ((Over.pullback s0).map ψ) := IsIso.eq_inv_of_hom_inv_id h3
    show (Over.pullback s0).map (r ≫ ψ) = (Over.pullback s0).map (𝟙 N)
    rw [CategoryTheory.Functor.map_comp, h4, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact ⟨⟨r, h1, h2⟩⟩

/-- group-law-dvr's `mumfordGroupLawDVR_of_neron`, at one DVR (proof copied, `R` fixed). -/
theorem mumfordGroupLawAt_of (hN : NeronExtAt R) (hI : GoodModelIsoAt R) : MumfordGroupLawAt R := by
  intro F e hP hS hGC he hfib
  let K := FractionRing R
  let s0 := genMap R K
  obtain ⟨A, g, hpb, hone⟩ := hfib K s0
  obtain ⟨N, hNS, hNsep, hNqc, ε, hext⟩ := hN K A
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
  haveI hψi : IsIso ψ := hI F N e hP hS hGC he hfib hNS hNsep ψ hiso
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

/-- **GIT Thm 6.14 over a henselian DVR** (no leaf: the vendored FLT Néron models). -/
theorem mumfordGroupLawAt_of_henselian [HenselianLocalRing R] : MumfordGroupLawAt R :=
  mumfordGroupLawAt_of R (neronExtAt_of_henselian R) (goodModelIsoAt R (neronExtAt_of_henselian R))

end Local

end DedekindFree
