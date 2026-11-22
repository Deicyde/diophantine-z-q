import ZInQKernel.Contrib.OneProof.BLRLocalizes
import ZInQKernel.Contrib.OneProof.NeronExtGlue

/-! # neron-ext: the Néron property near a set of maximal ideals (from GapBLR's `local_pt`) -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open NumberField

namespace NeronExt

open GapBLR

section Local

variable {R : Type} (K : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem locUnit (𝔭 : Ideal R) [𝔭.IsPrime] (t : 𝔭.primeCompl) : IsUnit (algebraMap R K t) :=
  isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2
    (fun h => t.2 (h ▸ 𝔭.zero_mem)))

/-- The algebra `R_𝔭 → K` (the one of `GapBLR.local_pt`). -/
noncomputable def locAlg (𝔭 : Ideal R) [𝔭.IsPrime] : Algebra (Localization.AtPrime 𝔭) K :=
  (IsLocalization.lift (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) (locUnit K 𝔭)).toAlgebra

theorem locAlg_tower (𝔭 : Ideal R) [𝔭.IsPrime] :
    letI := locAlg K 𝔭
    IsScalarTower R (Localization.AtPrime 𝔭) K :=
  letI := locAlg K 𝔭
  IsScalarTower.of_algebraMap_eq (fun z => (IsLocalization.lift_eq (locUnit K 𝔭) z).symm)

/-- `X ⊗_R R_𝔭` is a Néron model over `R_𝔭` (with the algebra `locAlg`). -/
def LocNeron (𝔭 : Ideal R) [𝔭.IsPrime] (X : Over (Spec (CommRingCat.of R))) : Prop :=
  letI := locAlg K 𝔭
  CToPrinted.IsNeronModelOver (Localization.AtPrime 𝔭) K
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime 𝔭))))).obj X)

variable {K}

theorem local_ptT {X : Over (Spec (CommRingCat.of R))} [Smooth X.hom] (T : Set (Ideal R))
    (hloc : ∀ (𝔭 : Ideal R) [𝔭.IsMaximal], 𝔭 ∈ T → LocNeron K 𝔭 X)
    {Y : Scheme.{0}} (y : Y ⟶ Spec (CommRingCat.of R)) [Smooth y]
    (a : pullback y (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ X.left)
    (ha : a ≫ X.hom = pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))) (x : Y)
    (hT : ∃ 𝔭 : Ideal R, 𝔭.IsMaximal ∧ 𝔭 ∈ T ∧ (y.base x).asIdeal ≤ 𝔭) :
    ∃ U : Y.Opens, x ∈ U ∧ ∃ g : U.toScheme ⟶ X.left, g ≫ X.hom = U.ι ≫ y ∧
      pullback.fst (U.ι ≫ y) (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ g =
        pullback.lift (pullback.fst _ _ ≫ U.ι) (pullback.snd _ _)
          (by rw [Category.assoc]; exact pullback.condition) ≫ a := by
  let ιK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  -- an affine open around `x`
  obtain ⟨_, ⟨V0, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : Y.Opens := V0
  haveI : IsAffine V := hV
  let v := V.ι ≫ y
  -- a maximal ideal over the image of `x`
  let q : PrimeSpectrum R := y.base x
  obtain ⟨𝔭, h𝔭, hT𝔭, hq𝔭⟩ := hT
  haveI := h𝔭
  let R𝔭 := Localization.AtPrime 𝔭
  have hunit : ∀ t : 𝔭.primeCompl, IsUnit (algebraMap R K t) := fun t =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2
      (fun h => t.2 (h ▸ 𝔭.zero_mem)))
  letI : Algebra R𝔭 K := locAlg K 𝔭
  haveI : IsScalarTower R R𝔭 K := locAlg_tower K 𝔭
  let jR := Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))
  let kK := Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))
  have hk : kK ≫ jR = ιK := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hN := hloc 𝔭 hT𝔭
  -- the extension over `V ⊗_R R_𝔭`
  let Y' : Over (Spec (CommRingCat.of R𝔭)) := Over.mk (pullback.fst jR v)
  haveI : Smooth Y'.hom := show Smooth (pullback.fst jR v) from inferInstance
  have eqb : (pullback.fst (pullback.fst jR v) kK ≫ pullback.snd jR v ≫ V.ι) ≫ y =
      pullback.snd (pullback.fst jR v) kK ≫ ιK := by
    show pullback.fst (pullback.fst jR v) kK ≫ pullback.snd jR v ≫ v = _
    rw [← pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hk]
  let ε : pullback (pullback.fst jR v) kK ⟶ pullback y ιK :=
    pullback.lift (pullback.fst _ _ ≫ pullback.snd jR v ≫ V.ι) (pullback.snd _ _) eqb
  have hb : (ε ≫ a) ≫ X.hom = pullback.snd (pullback.fst jR v) kK ≫ ιK := by
    rw [Category.assoc, ha, ← Category.assoc, pullback.lift_snd]
  obtain ⟨f𝔭, hf1, hf2⟩ := neron_ext_loc R𝔭 hN Y' (pullback.fst _ _) (pullback.snd _ _)
    (IsPullback.of_hasPullback _ _) (ε ≫ a) hb
  have hf1' : f𝔭 ≫ X.hom = pullback.fst jR v ≫ jR := hf1
  have hf2' : pullback.fst (pullback.fst jR v) kK ≫ f𝔭 = ε ≫ a := hf2
  -- spread `f𝔭` to some `R[1/s] ×_R V`
  haveI hA : ∀ (i : (GapBLR.Idx 𝔭)ᵒᵖ), IsAffine ((bcDiag 𝔭 v).obj i) := fun i => by
    haveI : IsAffine ((specDiag 𝔭).obj i) := show IsAffine (Spec _) from inferInstance
    exact show IsAffine (pullback (ej i) v) from inferInstance
  haveI : ∀ {i j : (GapBLR.Idx 𝔭)ᵒᵖ} (f : i ⟶ j), IsAffineHom ((bcDiag 𝔭 v).map f) := fun f => inferInstance
  haveI : ∀ i : (GapBLR.Idx 𝔭)ᵒᵖ, CompactSpace ((bcDiag 𝔭 v).obj i) := fun i => inferInstance
  haveI : ∀ i : (GapBLR.Idx 𝔭)ᵒᵖ, QuasiSeparatedSpace ((bcDiag 𝔭 v).obj i) := fun i => inferInstance
  have ha' : (bcCone 𝔭 R𝔭 v).π ≫ bcT 𝔭 v = (Functor.const _).map (f𝔭 ≫ X.hom) := by
    ext i
    show bcπ 𝔭 R𝔭 v i ≫ pullback.snd (ej i) v ≫ v = f𝔭 ≫ X.hom
    exact (pullback.lift_snd_assoc _ _ _ _).trans (pullback.condition.symm.trans hf1'.symm)
  obtain ⟨s, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (bcDiag 𝔭 v) (bcT 𝔭 v) X.hom (bcCone 𝔭 R𝔭 v) (bcConeIsLimit 𝔭 R𝔭 v) f𝔭 ha'
  let g' : pullback (ej s) v ⟶ X.left := g
  have hg2' : g' ≫ X.hom = pullback.snd (ej s) v ≫ v := hg2
  have hg1' : bcπ 𝔭 R𝔭 v s ≫ g' = f𝔭 := hg1
  -- the open `U = V ∩ y⁻¹ D(s)` around `x`
  let U : Y.Opens := V ⊓ y ⁻¹ᵁ (ej s).opensRange
  have hxU : x ∈ U := by
    refine ⟨hxV, ?_⟩
    have hrange := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of R) s.unop.s
    have hmem : y.base x ∈ PrimeSpectrum.basicOpen (R := R) s.unop.s :=
      (PrimeSpectrum.mem_basicOpen _ _).2 (fun h => s.unop.hs (hq𝔭 h))
    exact (congrArg (y.base x ∈ ·) hrange).mpr hmem
  have hle : U ≤ V := inf_le_left
  have hr : Set.range (U.ι ≫ y).base ⊆ Set.range (ej s).base := by
    rintro _ ⟨z, rfl⟩
    exact z.2.2
  let n : U.toScheme ⟶ pullback (ej s) v :=
    pullback.lift (IsOpenImmersion.lift (ej s) (U.ι ≫ y) hr) (Y.homOfLE hle)
      (by rw [IsOpenImmersion.lift_fac]; show _ = Y.homOfLE hle ≫ V.ι ≫ y
          rw [← Category.assoc, Scheme.homOfLE_ι])
  refine ⟨U, hxU, n ≫ g', ?_, ?_⟩
  · rw [Category.assoc, hg2']
    show n ≫ pullback.snd (ej s) v ≫ V.ι ≫ y = U.ι ≫ y
    rw [← Category.assoc, pullback.lift_snd, ← Category.assoc, Scheme.homOfLE_ι]
  · let F := pullback.fst (U.ι ≫ y) ιK
    let G := pullback.snd (U.ι ≫ y) ιK
    have hFG : F ≫ U.ι ≫ y = G ≫ ιK := pullback.condition
    let ρ : pullback (U.ι ≫ y) ιK ⟶ pullback jR v :=
      pullback.lift (G ≫ kK) (F ≫ Y.homOfLE hle) (by
        show (G ≫ kK) ≫ jR = (F ≫ Y.homOfLE hle) ≫ V.ι ≫ y
        rw [Category.assoc, hk, Category.assoc, ← Category.assoc (Y.homOfLE hle), Scheme.homOfLE_ι, hFG])
    have l0 : bcπ 𝔭 R𝔭 v s ≫ pullback.fst (ej s) v ≫ ej s = pullback.fst jR v ≫ jR :=
      (pullback.lift_fst_assoc _ _ _ _).trans ((Category.assoc _ _ _).trans
        (congrArg (pullback.fst jR v ≫ ·) (toP_ej R𝔭 s)))
    have l3 : bcπ 𝔭 R𝔭 v s ≫ pullback.snd (ej s) v = pullback.snd jR v := pullback.lift_snd _ _ _
    have l1 : ρ ≫ bcπ 𝔭 R𝔭 v s ≫ pullback.fst (ej s) v ≫ ej s = G ≫ ιK := by
      rw [l0, pullback.lift_fst_assoc, Category.assoc, hk]
    have l2 : F ≫ n ≫ pullback.fst (ej s) v ≫ ej s = G ≫ ιK := by
      rw [pullback.lift_fst_assoc, IsOpenImmersion.lift_fac, hFG]
    have c1 : ρ ≫ bcπ 𝔭 R𝔭 v s = F ≫ n := by
      apply pullback.hom_ext
      · rw [← cancel_mono (ej s)]
        simp only [Category.assoc]
        rw [l1, l2]
      · simp only [Category.assoc]
        rw [l3, pullback.lift_snd, pullback.lift_snd]
    let ρ' : pullback (U.ι ≫ y) ιK ⟶ pullback (pullback.fst jR v) kK :=
      pullback.lift ρ G (pullback.lift_fst _ _ _)
    have c2 : ρ' ≫ ε = pullback.lift (F ≫ U.ι) G (by rw [Category.assoc]; exact hFG) := by
      apply pullback.hom_ext
      · simp only [ε, ρ', ρ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
        rw [Scheme.homOfLE_ι]
      · simp only [ε, ρ', Category.assoc, pullback.lift_snd]
    have hρ : ρ = ρ' ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have key : F ≫ n ≫ g' = pullback.lift (F ≫ U.ι) G (by rw [Category.assoc]; exact hFG) ≫ a := by
      rw [← Category.assoc, ← c1, Category.assoc, hg1', hρ, Category.assoc, hf2', ← Category.assoc, c2]
    exact key

theorem ext_of_localT {X : Over (Spec (CommRingCat.of R))} [Smooth X.hom] [IsSeparated X.hom]
    [QuasiCompact X.hom] (T : Set (Ideal R))
    (hloc : ∀ (𝔭 : Ideal R) [𝔭.IsMaximal], 𝔭 ∈ T → LocNeron K 𝔭 X)
    (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom]
    (hY : ∀ x : Y.left, ∃ 𝔭 : Ideal R, 𝔭.IsMaximal ∧ 𝔭 ∈ T ∧ (Y.hom.base x).asIdeal ≤ 𝔭) :
    Function.Surjective fun f : Y ⟶ X =>
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f := by
  let ιK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  intro h
  have hw : h.left ≫ pullback.snd X.hom ιK = pullback.snd Y.hom ιK := Over.w h
  let a := h.left ≫ pullback.fst X.hom ιK
  have ha : a ≫ X.hom = pullback.snd Y.hom ιK ≫ ιK := by
    simp only [a, Category.assoc]
    rw [pullback.condition, ← Category.assoc, hw]
  choose U hxU g hg1 hg2 using fun x => local_ptT T hloc Y.hom a ha x (hY x)
  let 𝒰 : Y.left.OpenCover := {
    I₀ := Y.left, X i := (U i), f i := (U i).ι,
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ⟨x, by simpa using hxU x⟩, inferInstance⟩ }
  obtain ⟨f, hf1, hf2⟩ := glue_cover R (IsFractionRing.injective R K) X (𝟙 _) Y.hom a 𝒰 g
    (fun i => by rw [Category.comp_id]; exact hg1 i) hg2
  rw [Category.comp_id] at hf1
  refine ⟨Over.homMk f hf1, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, Over.homMk_left, pullback.lift_fst]
    exact hf2
  · simp only [Over.pullback_map_left, Over.homMk_left, pullback.lift_snd]
    exact hw.symm


end Local

section OnU

variable {L : Type} [Field L] [NumberField L]

/-- The maximal ideals of `𝓞_L` at the points of `U`. -/
def maxIn (U : (S L).Opens) : Set (Ideal (𝓞 L)) := {𝔭 | ∃ x : S L, x ∈ U ∧ x.asIdeal = 𝔭}

/-- **The Néron property over `U` is local** (BLR 1.2/4 over the open `U`, from GapBLR's `local_pt`). -/
noncomputable def neronOn_of_local (B : Over (Spec (CommRingCat.of L))) (U : (S L).Opens)
    (X : Over (S L)) [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom] (hX : Supp L U X)
    (e : (gf L).obj X ≅ B)
    (hloc : ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], 𝔭 ∈ maxIn U → LocNeron L 𝔭 X)
    (hT : ∀ x : S L, x ∈ U → ∃ 𝔭 : Ideal (𝓞 L), 𝔭.IsMaximal ∧ 𝔭 ∈ maxIn U ∧ x.asIdeal ≤ 𝔭) :
    NeronOn L B U where
  X := X
  supp := hX
  smooth := inferInstance
  sep := inferInstance
  qc := inferInstance
  e := e
  ext := fun Y _ hY φ => by
    obtain ⟨f, hf⟩ := ext_of_localT (K := L) (maxIn U) hloc Y
      (fun y => hT _ (mem_of_supp L hY y)) (φ ≫ e.inv)
    refine ⟨f, ?_⟩
    have hf' : (gf L).map f = φ ≫ e.inv := hf
    show (gf L).map f ≫ e.hom = φ
    rw [hf', Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In `Spec 𝓞_L`, every point of an open containing a maximal ideal `v` lies under a maximal ideal of
the open. -/
theorem hT_of_mem {U : (S L).Opens} (v : S L) (hv : v.asIdeal.IsMaximal) (hvU : v ∈ U) :
    ∀ x : S L, x ∈ U → ∃ 𝔭 : Ideal (𝓞 L), 𝔭.IsMaximal ∧ 𝔭 ∈ maxIn U ∧ x.asIdeal ≤ 𝔭 := by
  intro x hx
  by_cases h0 : x.asIdeal = ⊥
  · exact ⟨v.asIdeal, hv, ⟨v, hvU, rfl⟩, h0 ▸ bot_le⟩
  · exact ⟨x.asIdeal, Ideal.IsPrime.isMaximal x.isPrime h0, ⟨x, hx, rfl⟩, le_rfl⟩

theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  refine le_antisymm ?_ Ideal.le_jacobson
  by_cases h0 : P = ⊥
  · subst h0
    intro n hn
    rw [Ideal.mem_bot]
    by_contra hne
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp2).irreducible
    have hmem : n ∈ Ideal.span {(p : ℤ)} := (Ideal.mem_sInf.mp hn) ⟨bot_le, hmax⟩
    rw [Ideal.mem_span_singleton] at hmem
    have h2 : p ∣ n.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hmem
      simpa using this
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) h2
    omega
  · haveI := hP.isMaximal h0
    exact Ideal.jacobson_eq_self_of_isMaximal.le

/-- Every point of an open of `Spec 𝓞_L` lies under a maximal ideal of the open (`𝓞_L` is Jacobson). -/
theorem exists_maximal_mem {U : (S L).Opens} (x : S L) (hx : x ∈ U) :
    ∃ 𝔭 : Ideal (𝓞 L), 𝔭.IsMaximal ∧ 𝔭 ∈ maxIn U ∧ x.asIdeal ≤ 𝔭 := by
  by_cases h0 : x.asIdeal = ⊥
  · obtain ⟨_, ⟨g, rfl⟩, hxg, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
    have hg0 : g ≠ 0 := by
      intro h
      apply (PrimeSpectrum.mem_basicOpen _ _).1 hxg
      rw [h]; exact zero_mem _
    haveI : IsJacobsonRing ℤ := isJacobsonRing_int
    haveI : IsJacobsonRing (𝓞 L) := isJacobsonRing_of_isIntegral (R := ℤ)
    have hjac : (⊥ : Ideal (𝓞 L)).jacobson = ⊥ :=
      IsJacobsonRing.out' (⊥ : Ideal (𝓞 L)) (Ideal.isPrime_bot.isRadical)
    have : g ∉ (⊥ : Ideal (𝓞 L)).jacobson := by rw [hjac]; simpa using hg0
    rw [Ideal.jacobson, Ideal.mem_sInf] at this
    push Not at this
    obtain ⟨w, ⟨-, hw⟩, hgw⟩ := this
    refine ⟨w, hw, ⟨⟨w, hw.isPrime⟩, hsub ((PrimeSpectrum.mem_basicOpen _ _).2 hgw), rfl⟩, ?_⟩
    rw [h0]; exact bot_le
  · exact ⟨x.asIdeal, Ideal.IsPrime.isMaximal x.isPrime h0, ⟨x, hx, rfl⟩, le_rfl⟩

/-- **The Néron property over an open `U ⊆ Spec 𝓞_L` is local at the maximal ideals of `U`.** -/
noncomputable def neronOn_of_local' (B : Over (Spec (CommRingCat.of L))) (U : (S L).Opens)
    (X : Over (S L)) [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom] (hX : Supp L U X)
    (e : (gf L).obj X ≅ B)
    (hloc : ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], 𝔭 ∈ maxIn U → LocNeron L 𝔭 X) : NeronOn L B U :=
  neronOn_of_local B U X hX e hloc (fun x hx => exists_maximal_mem x hx)

end OnU

end NeronExt
