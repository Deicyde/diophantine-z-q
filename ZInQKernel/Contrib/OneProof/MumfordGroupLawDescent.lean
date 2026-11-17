import ZInQKernel.Contrib.OneProof.NeronGoodModelIso
import ZInQKernel.Contrib.OneProof.NeronDVRLocalSH

/-! # dedekind-free: GIT Thm 6.14 over every DVR (`MumfordGroupLawDVR`) without a Néron leaf

Task dedekind-free (2026-11-16/17); report docs/research/dedekind-free.md. The chain reads the research leaf
`neronSchemeExtensionDedekind` (BLR 1.4 Thm 3 over an affine Dedekind scheme) twice: for *GIT* Thm 6.14 over a DVR
(`GoodModelIso.mumfordGroupLawDVR_of_dedekind`) and for the textbook field `neronSchemeExtensionExists` (the case
`D = 𝓞_L`). This file removes the first reader:

* `mumfordGroupLawDVR_proof : ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR`, with no Néron leaf. Over the strict
  henselization `O₁` of `R` (gt-shpair's `wE w`, a henselian DVR) the vendored FLT development gives Néron models
  (`NeronFLT.exists_neron_of_henselian`), and goodmodel-iso's argument, run at the single ring `O₁`, gives the group
  law on `F ×_R O₁`. The multiplication, inverse and unit descend along the faithfully flat `R → O₁` (Mathlib:
  flat surjective quasi-compact morphisms are effective epimorphisms, Stacks 023Q): the descent condition holds
  because at points over the generic point both pull-backs are computed by the group law of the generic fibre `A`
  over `K` (rigidity), and the `K`-fibre of the (flat) kernel pair is schematically dense in it. The group axioms
  hold because base change along `R → O₁` is injective on morphisms (`GrpObj.ofRepresentableBy`).
* `neronDVRLocal_of_dedekind`: neron-ext's local leaf `NeronExt.NeronDVRLocal` (BLR 1.4 Thm 3 over the DVRs
  `(𝓞_L)_v`) follows from `NeronSchemeExtensionDedekind`, so it is never stronger; and
  `neronSchemeExtensionExists_of_dvrLocal` gives the textbook field from it (neron-ext, with EGA IV 8.10.5 (xii)
  proved by ega-limit).

So the field `neronSchemeExtensionDedekind` can be narrowed to `neronDVRLocal` (count-neutral). It cannot be removed:
its other readers, the height rows through T41 (`H5Neron.NeronModelExists`), need Néron models over `Spec 𝓞_L`
itself, whose local pieces need effective descent from `(𝓞_L)_v^h` (BLR §6), see the report.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.GroupLawDescent

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



section Descent

variable {S S' : Scheme.{0}} (p : S' ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]


/-- Base change along a faithfully flat quasi-compact `p` is injective on morphisms. -/
theorem map_injective (X Y : Over S) :
    Function.Injective (fun f : X ⟶ Y => (Over.pullback p).map f) := by
  intro f g h
  simp only at h
  have e1 : ((Over.pullback p).map f).left ≫ pullback.fst Y.hom p = pullback.fst X.hom p ≫ f.left := by simp
  have e2 : ((Over.pullback p).map g).left ≫ pullback.fst Y.hom p = pullback.fst X.hom p ≫ g.left := by simp
  ext1
  rw [← cancel_epi (pullback.fst X.hom p), ← e1, ← e2, h]

/-- **Descent of morphisms along a faithfully flat quasi-compact `p`** (Stacks 023Q, Mathlib's `EffectiveEpi`). -/
theorem descend (X Y : Over S) (b : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (hb : ∀ (W : Scheme.{0}) (a₁ a₂ : W ⟶ ((Over.pullback p).obj X).left),
      a₁ ≫ pullback.fst X.hom p = a₂ ≫ pullback.fst X.hom p →
        a₁ ≫ b.left ≫ pullback.fst Y.hom p = a₂ ≫ b.left ≫ pullback.fst Y.hom p) :
    ∃ f : X ⟶ Y, (Over.pullback p).map f = b := by
  let fl : X.left ⟶ Y.left :=
    EffectiveEpi.desc (pullback.fst X.hom p) (b.left ≫ pullback.fst Y.hom p) (fun a₁ a₂ h => hb _ a₁ a₂ h)
  have hfl : pullback.fst X.hom p ≫ fl = b.left ≫ pullback.fst Y.hom p := EffectiveEpi.fac _ _ _
  have hw : fl ≫ Y.hom = X.hom := by
    have := Over.w b
    simp only [Over.pullback_obj_hom] at this
    rw [← cancel_epi (pullback.fst X.hom p), reassoc_of% hfl, pullback.condition,
      ← Category.assoc, this, pullback.condition]
  refine ⟨Over.homMk fl hw, ?_⟩
  ext1
  apply pullback.hom_ext
  · simp [hfl]
  · have := Over.w b
    simp only [Over.pullback_obj_hom] at this
    simp [this]

end Descent


section GrpDescent

open Functor.OplaxMonoidal

variable {S S' : Scheme.{0}} (p : S' ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]
  (F : Over S) [GrpObj ((Over.pullback p).obj F)]
  (μd : F ⊗ F ⟶ F) (hμ : (Over.pullback p).map μd = δ (Over.pullback p) F F ≫ μ[(Over.pullback p).obj F])
  (ιd : F ⟶ F) (hι : (Over.pullback p).map ιd = ι[(Over.pullback p).obj F])
  (ηd : 𝟙_ (Over S) ⟶ F) (hη : (Over.pullback p).map ηd = Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj F])

include hμ in
theorem map_mul' {T : Over S} (f g : T ⟶ F) :
    (Over.pullback p).map (lift f g ≫ μd) = (Over.pullback p).map f * (Over.pullback p).map g := by
  rw [Functor.map_comp, hμ, Hom.mul_def, lift_δ_assoc]

include hη in
theorem map_one' {T : Over S} :
    (Over.pullback p).map (toUnit T ≫ ηd) = 1 := by
  rw [Functor.map_comp, hη, Hom.one_def, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

include hι in
theorem map_inv' {T : Over S} (f : T ⟶ F) :
    (Over.pullback p).map (f ≫ ιd) = ((Over.pullback p).map f)⁻¹ := by
  rw [Functor.map_comp, hι, Hom.inv_def]

set_option warn.classDefReducibility false in
/-- The group structure on `T ⟶ F` transported along the injective `(Over.pullback p).map`. -/
def homGroup (T : Over S) : Group (T ⟶ F) :=
  letI : Mul (T ⟶ F) := ⟨fun f g => lift f g ≫ μd⟩
  letI : One (T ⟶ F) := ⟨toUnit T ≫ ηd⟩
  letI : Inv (T ⟶ F) := ⟨fun f => f ≫ ιd⟩
  have hm : ∀ f g : T ⟶ F, (Over.pullback p).map (f * g) = (Over.pullback p).map f * (Over.pullback p).map g :=
    fun f g => map_mul' p F μd hμ f g
  have h1 : (Over.pullback p).map (1 : T ⟶ F) = 1 := map_one' p F ηd hη
  have hi : ∀ f : T ⟶ F, (Over.pullback p).map f⁻¹ = ((Over.pullback p).map f)⁻¹ :=
    fun f => map_inv' p F ιd hι f
  Group.ofLeftAxioms
    (fun a b c => map_injective p T F (by simp only [hm, _root_.mul_assoc]))
    (fun a => map_injective p T F (by simp only [hm, h1, _root_.one_mul]))
    (fun a => map_injective p T F (by simp only [hm, hi, h1, _root_.inv_mul_cancel]))

/-- The presheaf of groups `T ↦ (T ⟶ F)`. -/
def homFunctor : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := @GrpCat.of (T.unop ⟶ F) (homGroup p F μd hμ ιd hι ηd hη T.unop)
  map {T T'} φ := by
    letI := homGroup p F μd hμ ιd hι ηd hη T.unop
    letI := homGroup p F μd hμ ιd hι ηd hη T'.unop
    exact GrpCat.ofHom
      { toFun := fun f => φ.unop ≫ f
        map_one' := by
          change φ.unop ≫ (toUnit _ ≫ ηd) = toUnit _ ≫ ηd
          rw [← Category.assoc, toUnit_unique (φ.unop ≫ toUnit _) (toUnit _)]
        map_mul' := fun f g => by
          change φ.unop ≫ (lift f g ≫ μd) = lift (φ.unop ≫ f) (φ.unop ≫ g) ≫ μd
          rw [← Category.assoc, comp_lift] }
  map_id T := GrpCat.ext fun f => Category.id_comp f
  map_comp φ ψ := GrpCat.ext fun f =>
    show (ψ.unop ≫ φ.unop) ≫ f = ψ.unop ≫ (φ.unop ≫ f) from Category.assoc _ _ _

/-- **The descended group law.** -/
@[instance_reducible]
def grpObjOfDescent : GrpObj F :=
  GrpObj.ofRepresentableBy F (homFunctor p F μd hμ ιd hι ηd hη)
    { homEquiv := Equiv.refl _
      homEquiv_comp := fun f g => by rfl }

theorem grpObjOfDescent_one :
    (grpObjOfDescent p F μd hμ ιd hι ηd hη).one = ηd := by
  change toUnit _ ≫ ηd = ηd
  rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

end GrpDescent




/-- `Spec E → Spec K` for a field extension. -/
abbrev κm (K E : Type) [Field K] [Field E] [Algebra K E] :
    Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K E))

lemma one_left_eq {K : Type} [Field K] (A : AbVar K) : (1 : A.Pt K).left = η[A.X].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  simp [AbVar.ptObj]

/-- The group law of `A_E` (Mathlib's `Functor.grpObjObj`; a local instance of this file). -/
@[instance_reducible]
def grpObj_pullback {K E : Type} [Field K] [Field E] [Algebra K E] (A : AbVar K) :
    GrpObj ((Over.pullback (κm K E)).obj A.X) := Functor.grpObjObj

attribute [local instance] grpObj_pullback

/-- `A_E`, as `PkgI3.AbVar.baseChange` but reducible. -/
abbrev AE {K : Type} [Field K] (A : AbVar K) (E : Type) [Field E] [Algebra K E] : AbVar E where
  X := (Over.pullback (κm K E)).obj A.X
  grp := grpObj_pullback A
  proper := by dsimp; infer_instance
  smooth := by dsimp; infer_instance
  geomInt := by dsimp; infer_instance

lemma baseChange_eta_left_fst {K E : Type} [Field K] [Field E] [Algebra K E] (A : AbVar K) :
    η[(AE A E).X].left ≫ pullback.fst A.X.hom (κm K E) = κm K E ≫ η[A.X].left := by
  change (Functor.LaxMonoidal.ε (Over.pullback (κm K E)) ≫ (Over.pullback (κm K E)).map η[A.X]).left ≫ _ = _
  have hs : inv (pullback.snd (𝟙 _) (κm K E)) ≫ pullback.fst (𝟙 _) (κm K E) = κm K E := by
    rw [IsIso.inv_comp_eq, ← pullback.condition, Category.comp_id]
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst,
    Over.ε_pullback_left]
  rw [← Category.assoc]
  erw [hs]

lemma one_left_hom {E : Type} [Field E] (B : AbVar E) : (1 : B.Pt E).left ≫ B.X.hom = 𝟙 _ := by
  rw [Over.w (1 : B.Pt E)]
  exact ZInQ.Contrib.GroupLawNeron.spec_algebraMap_self E

lemma eta_left_g {K : Type} [Field K] {S : Scheme.{0}} {F : Over S} {e : S ⟶ F.left}
    {ηS : Spec (CommRingCat.of K) ⟶ S} {A : AbVar K} {g : A.X.left ⟶ F.left}
    (hA : IsAbVarFibre F e ηS A g) : η[A.X].left ≫ g = ηS ≫ e := by
  have h2 := hA.2
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left] at h2
  simp only [AbVar.ptObj, Over.mk_hom, ZInQ.Contrib.GroupLawNeron.spec_algebraMap_self] at h2
  rw [← h2, Category.assoc]; exact (Category.id_comp _).symm

lemma baseChange_one_left_fst {K E : Type} [Field K] [Field E] [Algebra K E] (A : AbVar K) :
    (1 : (AE A E).Pt E).left ≫ pullback.fst A.X.hom (κm K E) = κm K E ≫ η[A.X].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left, Category.assoc, baseChange_eta_left_fst]
  simp only [AbVar.ptObj, Over.mk_hom, ZInQ.Contrib.GroupLawNeron.spec_algebraMap_self]
  exact Category.id_comp _


open scoped CategoryTheory.Obj in
/-- **Inverse on a fibre** (rigidity, as `R1UnivRigid.isGrpFibre_of_rigidity`): the identification of an abelian
variety with a fibre of a proper smooth group object commutes with the inverses. -/
theorem inv_fibre {S : Scheme.{0}} (F : Over S) [GrpObj F] [IsProper F.hom]
    [Smooth F.hom] {K : Type} [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K)
    (g : A.X.left ⟶ F.left) (h : IsAbVarFibre F η[F].left s A g) : ι[A.X].left ≫ g = g ≫ ι[F].left := by
  obtain ⟨hpb, h1⟩ := h
  let Fs : Over (Spec (CommRingCat.of K)) := (Over.pullback s).obj F
  have : IsProper Fs.hom := by dsimp [Fs]; infer_instance
  have : Smooth Fs.hom := by dsimp [Fs]; infer_instance
  let eA : A.X ≅ Fs := Over.isoMk hpb.isoPullback (by simp [Fs])
  have : GeometricallyIntegral Fs.hom := by
    have e : eA.inv.left ≫ A.X.hom = Fs.hom := Over.w eA.inv
    have : MorphismProperty.RespectsIso (C := Scheme) @GeometricallyIntegral := by
      rw [GeometricallyIntegral.eq_geometrically]; infer_instance
    rw [← e]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral eA.inv.left
      A.X.hom).2 inferInstance
  let AF : AbVar K := ⟨Fs⟩
  have hg : eA.hom.left ≫ pullback.fst F.hom s = g := hpb.isoPullback_hom_fst
  have h1' : η[A.X].left ≫ g = s ≫ η[F].left := by
    rw [← h1]
    change _ = ((toUnit (AbVar.ptObj (K := K) K)) ≫ η[A.X]).left ≫ g
    rw [Over.comp_left, Over.toUnit_left]
    simp [AbVar.ptObj, Algebra.algebraMap_self]
  have hη : η[A.X] ≫ eA.hom = η[AF.X] := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [Over.comp_left, Category.assoc, hg, h1']
      change s ≫ η[F].left = (Functor.LaxMonoidal.ε (Over.pullback s) ≫
        (Over.pullback s).map η[F]).left ≫ pullback.fst F.hom s
      have hs : inv (pullback.snd (𝟙 S) s) ≫ pullback.fst (𝟙 S) s = s := by
        rw [IsIso.inv_comp_eq, ← pullback.condition, Category.comp_id]
      simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst,
        Over.ε_pullback_left]
      rw [← Category.assoc]
      erw [hs]
    · exact (Over.w (η[A.X] ≫ eA.hom)).trans (Over.w η[AF.X]).symm
  have hmon : IsMonHom eA.hom := G0FibreSimple.rigidityHom K A AF eA.hom hη
  have hi : ι[A.X] ≫ eA.hom = eA.hom ≫ ι[AF.X] := by
    have := GrpObj.inv_comp (𝟙 A.X) eA.hom
    rw [Hom.inv_def, Hom.inv_def, Category.id_comp, Category.id_comp] at this
    exact this
  rw [← hg, ← Category.assoc, ← Over.comp_left, hi]
  change (eA.hom ≫ (Over.pullback s).map ι[F]).left ≫ pullback.fst F.hom s = _
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]

section Fibre

variable {S S' : Scheme.{0}} (p : S' ⟶ S) (F : Over S) (e : S ⟶ F.left) (he : e ≫ F.hom = 𝟙 S)
  {K E : Type} [Field K] [Field E] [Algebra K E]
  (ηS : Spec (CommRingCat.of K) ⟶ S) (η₁ : Spec (CommRingCat.of E) ⟶ S')
  (hsq : η₁ ≫ p = κm K E ≫ ηS)
  (A : AbVar K) (g : A.X.left ⟶ F.left) (hA : IsAbVarFibre F e ηS A g)

/-- The base-changed section `e₁ = (p ≫ e, id)`. -/
def e₁ : S' ⟶ ((Over.pullback p).obj F).left :=
  pullback.lift (p ≫ e) (𝟙 S') (by rw [Category.assoc, he]; simp)

include hA hsq in
/-- The fibre map of `F₁ = F ×_S S'` at `η₁`, from that of `F` at `ηS`. -/
def g₁ : pullback A.X.hom (κm K E) ⟶ ((Over.pullback p).obj F).left :=
  pullback.lift (pullback.fst A.X.hom (κm K E) ≫ g) (pullback.snd A.X.hom (κm K E) ≫ η₁) (by
    rw [Category.assoc, hA.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hsq])

lemma g₁_fst : g₁ p F e ηS η₁ hsq A g hA ≫ pullback.fst F.hom p = pullback.fst A.X.hom (κm K E) ≫ g :=
  pullback.lift_fst _ _ _

lemma g₁_snd : g₁ p F e ηS η₁ hsq A g hA ≫ pullback.snd F.hom p = pullback.snd A.X.hom (κm K E) ≫ η₁ :=
  pullback.lift_snd _ _ _

theorem isAbVarFibre₁ :
    IsAbVarFibre ((Over.pullback p).obj F) (e₁ p F e he) η₁ (AE A E) (g₁ p F e ηS η₁ hsq A g hA) := by
  constructor
  · have hcomp : IsPullback (pullback.fst A.X.hom (κm K E) ≫ g) (pullback.snd A.X.hom (κm K E)) F.hom
        (κm K E ≫ ηS) := (IsPullback.of_hasPullback A.X.hom (κm K E)).paste_horiz hA.1
    refine IsPullback.of_right (h₁₂ := pullback.fst F.hom p) (h₂₂ := p) ?_ (g₁_snd ..)
      (IsPullback.of_hasPullback F.hom p)
    rw [g₁_fst, hsq]
    exact hcomp
  · have key : ∀ x : Spec (CommRingCat.of E) ⟶ pullback A.X.hom (κm K E),
        x ≫ pullback.fst A.X.hom (κm K E) = κm K E ≫ η[A.X].left →
        x ≫ pullback.snd A.X.hom (κm K E) = 𝟙 _ → x ≫ g₁ p F e ηS η₁ hsq A g hA = η₁ ≫ e₁ p F e he := by
      intro x h1 h2
      apply pullback.hom_ext
      · rw [Category.assoc, g₁_fst, ← Category.assoc, h1, Category.assoc, eta_left_g hA]
        simp only [e₁, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, ← Category.assoc, hsq]
      · rw [Category.assoc, g₁_snd, ← Category.assoc, h2, Category.id_comp]
        simp [e₁]
    exact key _ (baseChange_one_left_fst A) (one_left_hom (AE A E))

end Fibre

lemma AE_inv_left_fst {K E : Type} [Field K] [Field E] [Algebra K E] (A : AbVar K) :
    ι[(AE A E).X].left ≫ pullback.fst A.X.hom (κm K E) = pullback.fst A.X.hom (κm K E) ≫ ι[A.X].left := by
  change ((Over.pullback (κm K E)).map ι[A.X]).left ≫ _ = _
  simp

section Generic

variable {S S' : Scheme.{0}} (p : S' ⟶ S) (F : Over S) (e : S ⟶ F.left) (he : e ≫ F.hom = 𝟙 S)
  {K E : Type} [Field K] [Field E] [Algebra K E]
  (ηS : Spec (CommRingCat.of K) ⟶ S) (η₁ : Spec (CommRingCat.of E) ⟶ S')
  (hsq : η₁ ≫ p = κm K E ≫ ηS)
  (A : AbVar K) (g : A.X.left ⟶ F.left) (hA : IsAbVarFibre F e ηS A g)
  [IsProper F.hom] [Smooth F.hom] [GrpObj ((Over.pullback p).obj F)]
  (hη₁ : η[(Over.pullback p).obj F].left = e₁ p F e he)

include hη₁ hsq hA in
/-- **The inverse of `F₁` at a point over the generic point `η₁`** is computed by the inverse of `A` over `K`. -/
theorem gen_inv {T : Scheme.{0}} (a : T ⟶ ((Over.pullback p).obj F).left) (τ : T ⟶ Spec (CommRingCat.of E))
    (ha : a ≫ ((Over.pullback p).obj F).hom = τ ≫ η₁) :
    ∃ w : T ⟶ A.X.left, w ≫ g = a ≫ pullback.fst F.hom p ∧ w ≫ A.X.hom = τ ≫ κm K E ∧
      a ≫ ι[(Over.pullback p).obj F].left ≫ pullback.fst F.hom p = w ≫ ι[A.X].left ≫ g := by
  have hF := isAbVarFibre₁ p F e he ηS η₁ hsq A g hA
  rw [← hη₁] at hF
  have : IsProper ((Over.pullback p).obj F).hom := by dsimp; infer_instance
  have : Smooth ((Over.pullback p).obj F).hom := by dsimp; infer_instance
  have hinv := inv_fibre _ η₁ (AE A E) _ hF
  have hpbE := hF.1
  obtain ⟨v, hv1, hv2⟩ : ∃ v : T ⟶ pullback A.X.hom (κm K E),
      v ≫ g₁ p F e ηS η₁ hsq A g hA = a ∧ v ≫ pullback.snd A.X.hom (κm K E) = τ :=
    ⟨hpbE.lift a τ ha, hpbE.lift_fst _ _ _, hpbE.lift_snd _ _ _⟩
  refine ⟨v ≫ pullback.fst A.X.hom (κm K E), ?_, ?_, ?_⟩
  · rw [Category.assoc, ← g₁_fst p F e ηS η₁ hsq A g hA, ← Category.assoc, hv1]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hv2]
  · rw [← hv1, Category.assoc]
    erw [← reassoc_of% hinv]
    rw [g₁_fst, ← Category.assoc (ι[(AE A E).X].left), AE_inv_left_fst]
    simp only [Category.assoc]

include hη₁ hsq hA in
/-- **The multiplication of `F₁` at a pair of points over the generic point `η₁`** is computed by the
multiplication of `A` over `K`. -/
theorem gen_mul {T : Scheme.{0}} (a : T ⟶ ((Over.pullback p).obj (F ⊗ F)).left)
    (τ : T ⟶ Spec (CommRingCat.of E)) (ha : a ≫ ((Over.pullback p).obj (F ⊗ F)).hom = τ ≫ η₁) :
    ∃ w : T ⟶ (A.X ⊗ A.X).left,
      w ≫ (fst A.X A.X).left ≫ g = a ≫ pullback.fst (F ⊗ F).hom p ≫ (fst F F).left ∧
      w ≫ (snd A.X A.X).left ≫ g = a ≫ pullback.fst (F ⊗ F).hom p ≫ (snd F F).left ∧
      w ≫ (A.X ⊗ A.X).hom = τ ≫ κm K E ∧
      a ≫ (Functor.OplaxMonoidal.δ (Over.pullback p) F F ≫ μ[(Over.pullback p).obj F]).left ≫
        pullback.fst F.hom p = w ≫ μ[A.X].left ≫ g := by
  have hF := isAbVarFibre₁ p F e he ηS η₁ hsq A g hA
  rw [← hη₁] at hF
  have : IsProper ((Over.pullback p).obj F).hom := by dsimp; infer_instance
  have : Smooth ((Over.pullback p).obj F).hom := by dsimp; infer_instance
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := isGrpFibre_of_rigidity _ η₁ (AE A E) _ hF
  have hpbE := hF.1
  let P := Over.pullback p
  set u1 := a ≫ (P.map (fst F F)).left with hu1
  set u2 := a ≫ (P.map (snd F F)).left with hu2
  have hu1' : u1 ≫ (P.obj F).hom = τ ≫ η₁ := by
    rw [hu1, Category.assoc, Over.w (P.map (fst F F)), ha]
  have hu2' : u2 ≫ (P.obj F).hom = τ ≫ η₁ := by
    rw [hu2, Category.assoc, Over.w (P.map (snd F F)), ha]
  obtain ⟨v1, hv11, hv12⟩ : ∃ v : T ⟶ pullback A.X.hom (κm K E),
      v ≫ g₁ p F e ηS η₁ hsq A g hA = u1 ∧ v ≫ pullback.snd A.X.hom (κm K E) = τ :=
    ⟨hpbE.lift u1 τ hu1', hpbE.lift_fst _ _ _, hpbE.lift_snd _ _ _⟩
  obtain ⟨v2, hv21, hv22⟩ : ∃ v : T ⟶ pullback A.X.hom (κm K E),
      v ≫ g₁ p F e ηS η₁ hsq A g hA = u2 ∧ v ≫ pullback.snd A.X.hom (κm K E) = τ :=
    ⟨hpbE.lift u2 τ hu2', hpbE.lift_fst _ _ _, hpbE.lift_snd _ _ _⟩
  let v : T ⟶ ((AE A E).X ⊗ (AE A E).X).left :=
    pullback.lift (f := (AE A E).X.hom) (g := (AE A E).X.hom) v1 v2 (by
      change v1 ≫ pullback.snd A.X.hom (κm K E) = v2 ≫ pullback.snd A.X.hom (κm K E)
      rw [hv12, hv22])
  have hvf : v ≫ (fst (AE A E).X (AE A E).X).left = v1 := pullback.lift_fst _ _ _
  have hvs : v ≫ (snd (AE A E).X (AE A E).X).left = v2 := pullback.lift_snd _ _ _
  have key : v ≫ φ = a ≫ (Functor.OplaxMonoidal.δ P F F).left := by
    apply pullback.hom_ext
    · change v ≫ φ ≫ (fst (P.obj F) (P.obj F)).left = a ≫ (Functor.OplaxMonoidal.δ P F F).left ≫
        (fst (P.obj F) (P.obj F)).left
      rw [hφ1, ← Category.assoc, hvf, hv11, ← Over.comp_left, Functor.OplaxMonoidal.δ_fst]
    · change v ≫ φ ≫ (snd (P.obj F) (P.obj F)).left = a ≫ (Functor.OplaxMonoidal.δ P F F).left ≫
        (snd (P.obj F) (P.obj F)).left
      rw [hφ2, ← Category.assoc, hvs, hv21, ← Over.comp_left, Functor.OplaxMonoidal.δ_snd]
  let μκ := Functor.LaxMonoidal.μ (Over.pullback (κm K E)) A.X A.X
  refine ⟨v ≫ μκ.left ≫ pullback.fst (A.X ⊗ A.X).hom (κm K E), ?_, ?_, ?_, ?_⟩
  · change (v ≫ μκ.left ≫ pullback.fst (A.X ⊗ A.X).hom (κm K E)) ≫ pullback.fst A.X.hom A.X.hom ≫ g = _
    simp only [Category.assoc]
    rw [reassoc_of% (Over.μ_pullback_left_fst_fst (f := κm K E) A.X A.X)]
    change v ≫ (fst (AE A E).X (AE A E).X).left ≫ pullback.fst A.X.hom (κm K E) ≫ g = _
    rw [reassoc_of% hvf, ← g₁_fst p F e ηS η₁ hsq A g hA, reassoc_of% hv11, hu1, Category.assoc]
    simp only [P, Over.pullback_map_left, pullback.lift_fst]
  · change (v ≫ μκ.left ≫ pullback.fst (A.X ⊗ A.X).hom (κm K E)) ≫ pullback.snd A.X.hom A.X.hom ≫ g = _
    simp only [Category.assoc]
    rw [reassoc_of% (Over.μ_pullback_left_fst_snd (f := κm K E) A.X A.X)]
    change v ≫ (snd (AE A E).X (AE A E).X).left ≫ pullback.fst A.X.hom (κm K E) ≫ g = _
    rw [reassoc_of% hvs, ← g₁_fst p F e ηS η₁ hsq A g hA, reassoc_of% hv21, hu2, Category.assoc]
    simp only [P, Over.pullback_map_left, pullback.lift_fst]
  · simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% (Over.μ_pullback_left_snd (f := κm K E) A.X A.X)]
    change v ≫ (snd (AE A E).X (AE A E).X).left ≫ pullback.snd A.X.hom (κm K E) ≫ κm K E = _
    rw [reassoc_of% hvs, reassoc_of% hv22]
  · rw [Over.comp_left, Category.assoc, ← reassoc_of% key, ← reassoc_of% hφ3]
    erw [g₁_fst]
    change v ≫ (μκ ≫ (Over.pullback (κm K E)).map μ[A.X]).left ≫ pullback.fst A.X.hom (κm K E) ≫ g = _
    simp

end Generic


section Cocycle

variable {S S' : Scheme.{0}} (p : S' ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]
  {K E : Type} [Field K] [Field E] [Algebra K E]
  (ηS : Spec (CommRingCat.of K) ⟶ S) [IsSchemeTheoreticallyDominant ηS] [QuasiCompact ηS]
  (η₁ : Spec (CommRingCat.of E) ⟶ S') (hsq : IsPullback η₁ (κm K E) p ηS)

include hsq in
/-- **The cocycle condition from the generic fibre.** A morphism `b : X' → F'` of base changes descends along
`p` if its values at points over the generic point `η₁` of `S'` depend only on their images in `X` and in
`Spec K`: the generic fibre over `S` of the kernel pair is schematically dense (the kernel pair is flat over
`S`), and `F` is separated. -/
theorem cocycle_of_generic (X F : Over S) [Flat X.hom] [IsSeparated F.hom]
    (b : (Over.pullback p).obj X ⟶ (Over.pullback p).obj F)
    (hgen : ∀ (T : Scheme.{0}) (a a' : T ⟶ ((Over.pullback p).obj X).left) (τ τ' : T ⟶ Spec (CommRingCat.of E)),
      a ≫ ((Over.pullback p).obj X).hom = τ ≫ η₁ → a' ≫ ((Over.pullback p).obj X).hom = τ' ≫ η₁ →
      a ≫ pullback.fst X.hom p = a' ≫ pullback.fst X.hom p → τ ≫ κm K E = τ' ≫ κm K E →
      a ≫ b.left ≫ pullback.fst F.hom p = a' ≫ b.left ≫ pullback.fst F.hom p) :
    ∀ (W : Scheme.{0}) (a₁ a₂ : W ⟶ ((Over.pullback p).obj X).left),
      a₁ ≫ pullback.fst X.hom p = a₂ ≫ pullback.fst X.hom p →
        a₁ ≫ b.left ≫ pullback.fst F.hom p = a₂ ≫ b.left ≫ pullback.fst F.hom p := by
  intro W a₁ a₂ h
  let πX := pullback.fst X.hom p
  let pr1 := pullback.fst πX πX
  let pr2 := pullback.snd πX πX
  suffices H : pr1 ≫ b.left ≫ pullback.fst F.hom p = pr2 ≫ b.left ≫ pullback.fst F.hom p by
    have := congrArg (pullback.lift a₁ a₂ h ≫ ·) H
    simp only [pr1, pr2] at this
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hc : ∀ (Z : Scheme.{0}) (q : Z ⟶ ((Over.pullback p).obj X).left),
      q ≫ b.left ≫ pullback.fst F.hom p ≫ F.hom = q ≫ πX ≫ X.hom := by
    intro Z q
    have hb := Over.w b
    simp only [Over.pullback_obj_hom] at hb
    rw [pullback.condition, reassoc_of% hb, ← pullback.condition]
  let D := pullback (pr1 ≫ πX ≫ X.hom) ηS
  let j : D ⟶ _ := pullback.fst (pr1 ≫ πX ≫ X.hom) ηS
  let σ : D ⟶ _ := pullback.snd (pr1 ≫ πX ≫ X.hom) ηS
  have hjσ : j ≫ pr1 ≫ πX ≫ X.hom = σ ≫ ηS := pullback.condition
  have hpr : pr1 ≫ πX = pr2 ≫ πX := pullback.condition
  refine NeronC.ext_of_isSchemeTheoreticallyDominant_of_isSeparated F.hom ?_ j ?_
  · simp only [Category.assoc]
    rw [hc, hc, reassoc_of% hpr]
  · have ht : ∀ q : D ⟶ ((Over.pullback p).obj X).left, q ≫ πX = j ≫ pr1 ≫ πX →
        (q ≫ ((Over.pullback p).obj X).hom) ≫ p = σ ≫ ηS := by
      intro q hq
      simp only [Over.pullback_obj_hom, Category.assoc]
      rw [← pullback.condition, ← Category.assoc, hq, Category.assoc, Category.assoc, hjσ]
    have h1 := ht (j ≫ pr1) (by simp only [Category.assoc])
    have h2 := ht (j ≫ pr2) (by rw [Category.assoc, hpr])
    have := hgen D (j ≫ pr1) (j ≫ pr2) (hsq.lift _ σ h1) (hsq.lift _ σ h2)
      (by rw [hsq.lift_fst, Category.assoc]) (by rw [hsq.lift_fst, Category.assoc])
      (by rw [Category.assoc, Category.assoc]; exact congrArg (j ≫ ·) hpr) (by rw [hsq.lift_snd, hsq.lift_snd])
    simpa only [Category.assoc] using this

end Cocycle

section FibreBC

/-- Fibres of `F ×_S S'` at field points `s` of `S'`: those of `F` at `s ≫ p`. -/
theorem isAbVarFibre_bc {S S' : Scheme.{0}} (p : S' ⟶ S) (F : Over S) (e : S ⟶ F.left)
    (he : e ≫ F.hom = 𝟙 S) {K' : Type} [Field K'] (s : Spec (CommRingCat.of K') ⟶ S') (A : AbVar K')
    (g : A.X.left ⟶ F.left) (hA : IsAbVarFibre F e (s ≫ p) A g) :
    IsAbVarFibre ((Over.pullback p).obj F) (e₁ p F e he) s A
      (pullback.lift g (A.X.hom ≫ s) (by rw [hA.1.w, Category.assoc])) := by
  constructor
  · refine IsPullback.of_right (h₁₂ := pullback.fst F.hom p) (h₂₂ := p) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback F.hom p)
    rw [pullback.lift_fst]
    exact hA.1
  · have key : ∀ x : Spec (CommRingCat.of K') ⟶ A.X.left, x ≫ g = (s ≫ p) ≫ e → x ≫ A.X.hom = 𝟙 _ →
        x ≫ pullback.lift g (A.X.hom ≫ s) (by rw [hA.1.w, Category.assoc]) = s ≫ e₁ p F e he := by
      intro x h1 h2
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, e₁]
        rw [h1, Category.assoc]
      · simp only [Category.assoc, pullback.lift_snd, e₁, Category.comp_id]
        rw [← Category.assoc, h2, Category.id_comp]
    exact key _ hA.2 (one_left_hom A)

end FibreBC

section Main

/-- **GIT Thm 6.14 over a DVR descends along a faithfully flat cover by a DVR** whose generic fibre is a field:
`R → O₁` with `Spec O₁ → Spec R` flat and surjective, and `Spec E = Spec O₁ ×_{Spec R} Spec K`. -/
theorem mumfordGroupLawAt_of_cover (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {O₁ : Type} [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] (φ : R →+* O₁)
    [Flat (Spec.map (CommRingCat.ofHom φ))] [Surjective (Spec.map (CommRingCat.ofHom φ))]
    (E : Type) [Field E] [Algebra (FractionRing R) E] (ι₁ : O₁ →+* E)
    (hsq : IsPullback (Spec.map (CommRingCat.ofHom ι₁)) (κm (FractionRing R) E)
      (Spec.map (CommRingCat.ofHom φ)) (genMap R (FractionRing R)))
    (hM : MumfordGroupLawAt O₁) : MumfordGroupLawAt R := by
  intro F e hP hS hGC he hfib
  haveI := hP; haveI := hS
  let K := FractionRing R
  let ηS := genMap R K
  let p := Spec.map (CommRingCat.ofHom φ)
  let η₁ := Spec.map (CommRingCat.ofHom ι₁)
  haveI : IsSchemeTheoreticallyDominant ηS := genMap_isSchemeTheoreticallyDominant (R := R) K
  obtain ⟨A, g, hA⟩ := hfib K ηS
  let P := Over.pullback p
  let F₁ := P.obj F
  have hP₁ : IsProper F₁.hom := by dsimp [F₁, P]; infer_instance
  have hS₁ : Smooth F₁.hom := by dsimp [F₁, P]; infer_instance
  have hGC₁ : GeometricallyConnected F₁.hom := by dsimp [F₁, P]; infer_instance
  have he₁ : e₁ p F e he ≫ F₁.hom = 𝟙 _ := pullback.lift_snd _ _ _
  have hfib₁ : ∀ (K' : Type) [Field K'] (s : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of O₁)),
      ∃ (A' : AbVar K') (g' : A'.X.left ⟶ F₁.left), IsAbVarFibre F₁ (e₁ p F e he) s A' g' := by
    intro K' _ s
    obtain ⟨A', g', h'⟩ := hfib K' (s ≫ p)
    exact ⟨A', _, isAbVarFibre_bc p F e he s A' g' h'⟩
  obtain ⟨G₁, hη₁⟩ := hM F₁ (e₁ p F e he) hP₁ hS₁ hGC₁ he₁ hfib₁
  letI := G₁
  haveI : Flat (F ⊗ F).hom := by
    change Flat (pullback.fst F.hom F.hom ≫ F.hom); infer_instance
  -- the multiplication
  obtain ⟨μd, hμd⟩ := descend p (F ⊗ F) F (Functor.OplaxMonoidal.δ P F F ≫ μ[F₁])
    (cocycle_of_generic p ηS η₁ hsq (F ⊗ F) F _ (fun T a a' τ τ' ha ha' h1 h2 => by
      obtain ⟨w, hw1, hw2, hw3, hw4⟩ := gen_mul p F e he ηS η₁ hsq.w A g hA hη₁ a τ ha
      obtain ⟨w', hw1', hw2', hw3', hw4'⟩ := gen_mul p F e he ηS η₁ hsq.w A g hA hη₁ a' τ' ha'
      have hww : w = w' := by
        refine pullback.hom_ext (f := A.X.hom) (g := A.X.hom) ?_ ?_
        · apply hA.1.hom_ext
          · change w ≫ (fst A.X A.X).left ≫ g = w' ≫ (fst A.X A.X).left ≫ g
            rw [hw1, hw1', reassoc_of% h1]
          · change w ≫ (fst A.X A.X).left ≫ A.X.hom = w' ≫ (fst A.X A.X).left ≫ A.X.hom
            rw [Over.w (fst A.X A.X), hw3, hw3', h2]
        · apply hA.1.hom_ext
          · change w ≫ (snd A.X A.X).left ≫ g = w' ≫ (snd A.X A.X).left ≫ g
            rw [hw2, hw2', reassoc_of% h1]
          · change w ≫ (snd A.X A.X).left ≫ A.X.hom = w' ≫ (snd A.X A.X).left ≫ A.X.hom
            rw [Over.w (snd A.X A.X), hw3, hw3', h2]
      rw [hw4, hw4', hww]))
  -- the inverse
  obtain ⟨ιd, hιd⟩ := descend p F F ι[F₁]
    (cocycle_of_generic p ηS η₁ hsq F F _ (fun T a a' τ τ' ha ha' h1 h2 => by
      obtain ⟨w, hw1, hw2, hw3⟩ := gen_inv p F e he ηS η₁ hsq.w A g hA hη₁ a τ ha
      obtain ⟨w', hw1', hw2', hw3'⟩ := gen_inv p F e he ηS η₁ hsq.w A g hA hη₁ a' τ' ha'
      have hww : w = w' := hA.1.hom_ext (by rw [hw1, hw1', h1]) (by rw [hw2, hw2', h2])
      rw [hw3, hw3', hww]))
  -- the unit
  have he' : e ≫ F.hom = (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := he
  let ηd : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ F := Over.homMk e he'
  have hηd : P.map ηd = Functor.OplaxMonoidal.η P ≫ η[F₁] := by
    ext1
    apply pullback.hom_ext
    · simp only [P, ηd, Over.pullback_map_left, Over.homMk_left, pullback.lift_fst, Over.comp_left,
        Over.η_pullback_left, Category.assoc, hη₁, e₁]
      rw [← Category.assoc, ← pullback.condition]
      simp
    · have h1 := Over.w (P.map ηd)
      have h2 := Over.w (Functor.OplaxMonoidal.η P ≫ η[F₁])
      simp only [P, F₁, Over.pullback_obj_hom] at h1 h2 ⊢
      rw [h1, h2]
  refine ⟨grpObjOfDescent p F μd hμd ιd hιd ηd hηd, ?_⟩
  rw [grpObjOfDescent_one]
  rfl

end Main

section Ring

open ReductSplit ReductGlue

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **GIT Thm 6.14 over every DVR, with no Néron leaf.** Descend from the strict henselization (a henselian DVR,
where the vendored FLT development gives Néron models and goodmodel-iso's argument gives the group law). -/
theorem mumfordGroupLawAt_all : MumfordGroupLawAt R := by
  let K := FractionRing R
  let O := (ValuationRing.valuation R K).valuationSubring
  haveI := NeronFLT.isDVR_valSub R K
  obtain ⟨w, hw⟩ := GapSHPair.exists_comap_eq (Ω := AlgebraicClosure K) O
  have hS := GapSHPair.isSHSep_inertia w hw
  let E := GapSHPair.inertiaField (K := K) w
  let O₁ := GapSHPair.wE (K := K) w
  haveI : IsDiscreteValuationRing O₁ := hS.1.1
  haveI : HenselianLocalRing O₁ := hS.1.2.1
  have hO : O₁.comap (algebraMap K E) = O := GapSHPair.hE_eq w hw
  let φ : R →+* O₁ := (comapHom hO).comp (NeronFLT.valSubHom R K)
  have hφinj : Function.Injective φ := by
    intro a b h
    have h1 := congrArg (fun x : O₁ => (x : E)) h
    change algebraMap K E (algebraMap R K a) = algebraMap K E (algebraMap R K b) at h1
    exact IsFractionRing.injective R K ((algebraMap K E).injective h1)
  -- faithful flatness
  letI : Algebra R O₁ := φ.toAlgebra
  haveI : Module.Flat R O₁ := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    rw [eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hax⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    change φ a * x = 0 at hax
    rcases mul_eq_zero.1 hax with h | h
    · exact absurd (hφinj (h.trans (map_zero φ).symm)) ha0
    · exact h
  haveI : IsLocalHom (algebraMap R O₁) := by
    haveI : IsLocalHom (comapHom hO) := comapHom_isLocalHom hO
    haveI : IsLocalHom (NeronFLT.valSubHom R K) :=
      (inferInstance : IsLocalHom (NeronFLT.valSubEquiv R K : R →+* O))
    exact (inferInstance : IsLocalHom ((comapHom hO).comp (NeronFLT.valSubHom R K)))
  haveI : Module.FaithfullyFlat R O₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hff := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom φ)).2 (by
    change RingHom.FaithfullyFlat (algebraMap R O₁)
    exact (RingHom.faithfullyFlat_algebraMap_iff).2 inferInstance)
  haveI : Flat (Spec.map (CommRingCat.ofHom φ)) := hff.1
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) := hff.2
  -- the generic fibre
  have hι : Function.Injective (algebraMap O₁ E) := Subtype.val_injective
  haveI : IsLocalization ((nonZeroDivisors R).map φ) E := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, m, hm, rfl⟩
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have : φ m = 0 := hι (h0.trans (map_zero _).symm)
      exact nonZeroDivisors.ne_zero hm (hφinj (this.trans (map_zero φ).symm))
    · intro z
      rcases O₁.mem_or_inv_mem z with hz | hz
      · exact ⟨(⟨z, hz⟩, 1), by simp; rfl⟩
      · by_cases hz0 : z = 0
        · exact ⟨(0, 1), by simp [hz0]⟩
        let b : O₁ := ⟨z⁻¹, hz⟩
        have hb0 : b ≠ 0 := fun h => hz0 (inv_eq_zero.1 (congrArg Subtype.val h))
        obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
        obtain ⟨n, u, hu⟩ := GapSHPair.assoc_pow w hw ϖ hϖ hb0
        let r : R := (NeronFLT.valSubEquiv R K).symm ϖ
        have hr : φ r = comapHom hO ϖ := by
          change comapHom hO (NeronFLT.valSubEquiv R K ((NeronFLT.valSubEquiv R K).symm ϖ)) = _
          rw [RingEquiv.apply_symm_apply]
        have hr0 : r ^ n ∈ nonZeroDivisors R := by
          refine mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ fun h => hϖ.ne_zero ?_)
          rw [show ϖ = NeronFLT.valSubEquiv R K r from (RingEquiv.apply_symm_apply _ _).symm, h, map_zero]
        refine ⟨(↑u⁻¹, ⟨φ (r ^ n), Submonoid.mem_map_of_mem _ hr0⟩), ?_⟩
        change z * algebraMap O₁ E (φ (r ^ n)) = algebraMap O₁ E ↑u⁻¹
        have hb : φ (r ^ n) = b * ↑u⁻¹ := by
          rw [map_pow, hr, ← hu, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
        rw [hb, map_mul, ← _root_.mul_assoc]
        change z * z⁻¹ * _ = _
        rw [mul_inv_cancel₀ hz0, _root_.one_mul]
    · intro x y h
      exact ⟨1, by rw [hι h]⟩
  have hpush := CommRingCat.isPushout_of_isLocalization φ (algebraMap K E)
    (by ext a; rfl) (nonZeroDivisors R) (Rₘ := K) (Sₘ := E)
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  exact mumfordGroupLawAt_of_cover R φ E (algebraMap O₁ E) hsq (mumfordGroupLawAt_of_henselian O₁)

end Ring

/-- **`MumfordGroupLawDVR` (GIT Thm 6.14 over a DVR) proved, with no Néron leaf.** -/
theorem mumfordGroupLawDVR_proof : ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR :=
  fun R _ _ _ => mumfordGroupLawAt_all R

section Textbook

/-- **neron-ext's local leaf is a case of the Dedekind leaf** (`D = (𝓞_L)_v`, a DVR): the narrowing of the field is a
weakening. -/
theorem neronDVRLocal_of_dedekind (h : ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind) :
    NeronExt.NeronDVRLocal := by
  intro K _ A L _ _ _ v _ Rv _ _ _ _ _
  have hv0 : v ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (NumberField.RingOfIntegers.not_isField L)
  haveI : IsDomain Rv :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := v.primeCompl) _
      (Ideal.primeCompl_le_nonZeroDivisors v)
  haveI : IsDiscreteValuationRing Rv :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (NumberField.RingOfIntegers L) hv0 Rv
  haveI : IsFractionRing Rv L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.primeCompl Rv L
  obtain ⟨N, hS, hSep, hQC, ε, hext⟩ := h Rv L (A.baseChange L)
  haveI := hS; haveI := hSep
  haveI : IsSchemeTheoreticallyDominant (genMap Rv L) :=
    genMap_isSchemeTheoreticallyDominant (R := Rv) L
  refine ⟨N, ⟨hS, hSep, inferInstance, hQC, fun Y _ => ⟨fun f f' hf =>
    NeronC.pullback_map_injective (genMap Rv L) Y N hf, fun g => ?_⟩⟩, ⟨ε⟩⟩
  obtain ⟨f, hf⟩ := hext Y (g ≫ ε.hom)
  exact ⟨f, (cancel_mono ε.hom).mp hf⟩

/-- **The textbook field `neronSchemeExtensionExists` from the local leaf** (neron-ext's `extension_of_dvrLocal`,
with EGA IV 8.10.5 (xii) proved by ega-limit). -/
theorem neronSchemeExtensionExists_of_dvrLocal (h : NeronExt.NeronDVRLocal) :
    ZInQ.Contrib.NeronC.NeronSchemeExtensionExists :=
  NeronExt.extension_of_dvrLocal ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof h

end Textbook

end ZInQ.Contrib.GroupLawDescent

