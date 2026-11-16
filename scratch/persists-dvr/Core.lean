import ZInQKernel.Contrib.OneProof.NeronDVR
import ZInQKernel.Contrib.OneProof.SGA7PersistsNF

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

set_option linter.style.haveILetI false

namespace GapPersists

open ZInQ.HeightSplit

/-! ### §1 Residue extensions of a finite extension are algebraic -/

theorem isAlgebraic_resMap {K K' : Type} [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    {O : ValuationSubring K} {O' : ValuationSubring K'} (hO : O'.comap (algebraMap K K') = O) :
    letI := (ReductGlue.resMap hO).toAlgebra
    Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') := by
  letI := (ReductGlue.resMap hO).toAlgebra
  constructor
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) (x : K')
  obtain ⟨i, hi, hmax⟩ := p.support.exists_max_image (fun j => O.valuation (p.coeff j))
    (Polynomial.support_nonempty.mpr hp0)
  set c := p.coeff i with hcdef
  have hc : c ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hvc : O.valuation c ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact hc
  have hmem : ∀ j, c⁻¹ * p.coeff j ∈ O := by
    intro j
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hj : j ∈ p.support
    · have := hmax j hj
      rw [inv_mul_le_iff₀ (zero_lt_iff.mpr hvc), mul_one]
      exact this
    · rw [Polynomial.notMem_support_iff.mp hj, map_zero, mul_zero]
      exact zero_le
  let b : ℕ → O := fun j => ⟨c⁻¹ * p.coeff j, hmem j⟩
  let n := p.natDegree
  let q : Polynomial (IsLocalRing.ResidueField O) :=
    ∑ j ∈ Finset.range (n + 1), Polynomial.monomial j (IsLocalRing.residue O (b j))
  have hin : i ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp i hi))
  have hbi : b i = 1 := Subtype.ext (inv_mul_cancel₀ hc)
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : q.coeff i = 1 := by
      simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_ite_eq' (Finset.range (n + 1)) i, if_pos hin, hbi, map_one]
    rw [h, Polynomial.coeff_zero] at h1
    exact zero_ne_one h1
  refine ⟨q, hq0, ?_⟩
  have hsum : (∑ j ∈ Finset.range (n + 1), ReductSplit.comapHom hO (b j) * x ^ j) = 0 := by
    apply Subtype.ext
    have h2 : ((∑ j ∈ Finset.range (n + 1), ReductSplit.comapHom hO (b j) * x ^ j : O') : K') =
        algebraMap K K' c⁻¹ * Polynomial.aeval (x : K') p := by
      rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      show algebraMap K K' (c⁻¹ * p.coeff j) * (x : K') ^ j = _
      rw [map_mul, Algebra.smul_def, mul_assoc, map_inv₀]
    rw [h2, hpx, mul_zero]
    rfl
  simp only [q, map_sum, Polynomial.aeval_monomial]
  have h3 : ∀ j, algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')
      (IsLocalRing.residue O (b j)) * (IsLocalRing.residue O' x) ^ j =
      IsLocalRing.residue O' (ReductSplit.comapHom hO (b j) * x ^ j) := by
    intro j
    rw [RingHom.algebraMap_toAlgebra, ReductGlue.resMap_residue, map_mul, map_pow]
  simp_rw [h3]
  rw [← map_sum, hsum, map_zero]

/-! ### §2 Monoid homomorphisms through a mono -/

theorem isMonHom_of_comp_mono {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C}
    [MonObj X] [MonObj Y] [MonObj Z] (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] [IsMonHom g]
    (hfg : IsMonHom (f ≫ g)) : IsMonHom f := by
  constructor
  · apply (cancel_mono g).1
    rw [Category.assoc, IsMonHom.one_hom (f ≫ g), IsMonHom.one_hom g]
  · apply (cancel_mono g).1
    rw [Category.assoc, IsMonHom.mul_hom (f ≫ g), Category.assoc, IsMonHom.mul_hom g, ← Category.assoc,
      tensorHom_comp_tensorHom]

/-! ### §3 The transfer lemma -/

open MonObj in
/-- If `V` is an open subgroup scheme of `G` with image `G⁰` and also an open subgroup scheme of `H`, then a
semi-abelian identity component of a fibre `G_k` gives one of `H_k`. -/
theorem hasSemiAbelian_transfer {S : Scheme.{0}} {k : Type} [Field k] (p : Spec (CommRingCat.of k) ⟶ S)
    (G H V : Over S) [GrpObj G] [GrpObj H] [GrpObj V] (a : V ⟶ G) (b : V ⟶ H)
    (ha : IsOpenImmersion a.left) (ham : IsMonHom a) (hra : Set.range a.left = CToPrinted.idCompSet G)
    (hb : IsOpenImmersion b.left) (hbm : IsMonHom b)
    (h : letI : GrpObj ((Over.pullback p).obj G) := Functor.grpObjObj
      HasSemiAbelianIdentityComponent ((Over.pullback p).obj G)) :
    letI : GrpObj ((Over.pullback p).obj H) := Functor.grpObjObj
    HasSemiAbelianIdentityComponent ((Over.pullback p).obj H) := by
  letI : GrpObj ((Over.pullback p).obj G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback p).obj H) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback p).obj V) := Functor.grpObjObj
  obtain ⟨U, hU, inc, hoi, hmh, hcon, rest⟩ := h
  haveI : IsOpenImmersion a.left := ha
  haveI : IsOpenImmersion b.left := hb
  haveI hak : IsOpenImmersion ((Over.pullback p).map a).left :=
    ZInQ.H5Glue.isOpenImmersion_pullback_map p a
  haveI hbk : IsOpenImmersion ((Over.pullback p).map b).left :=
    ZInQ.H5Glue.isOpenImmersion_pullback_map p b
  have hamap : ((Over.pullback p).map a).left =
      pullback.map V.hom p G.hom p a.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  have hrange : Set.range ((Over.pullback p).map a).left =
      pullback.fst G.hom p ⁻¹' CToPrinted.idCompSet G := by
    rw [hamap, Scheme.Pullback.range_map, hra]
    have hid : Set.range ((𝟙 (Spec (CommRingCat.of k)) : Spec (CommRingCat.of k) ⟶ _) :
        Spec (CommRingCat.of k) → Spec (CommRingCat.of k)) = Set.univ :=
      Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
    rw [hid, Set.preimage_univ, Set.inter_univ]
  -- the base point of `Spec k`
  let t₀ : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
  have hpt : ∀ t : Spec (CommRingCat.of k), t = t₀ := fun t =>
    Subsingleton.elim (α := PrimeSpectrum k) t t₀
  let s := p t₀
  let F := inc.left ≫ pullback.fst G.hom p
  have hFs : ∀ u, G.hom (F u) = s := by
    intro u
    rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc,
      Scheme.Hom.comp_apply]
    exact congrArg p (hpt _)
  have hTc : _root_.IsPreconnected (Set.range F) := isPreconnected_range F.continuous
  have hTe : (η[G] : 𝟙_ (Over S) ⟶ G).left s ∈ Set.range F := by
    refine ⟨(η[U] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U).left t₀, ?_⟩
    have h1 : (η[U] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U).left ≫ inc.left =
        (η[(Over.pullback p).obj G] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ _).left := by
      rw [← Over.comp_left, IsMonHom.one_hom inc]
    have h2 := CToPrinted.unit_bc_fst p G
    show (η[U].left ≫ inc.left ≫ pullback.fst G.hom p) t₀ = _
    rw [← Category.assoc, h1, h2]
    rfl
  have hTsub : Set.range F ⊆ G.hom ⁻¹' {s} := by
    rintro _ ⟨u, rfl⟩
    exact hFs u
  have hTcc := hTc.subset_connectedComponentIn hTe hTsub
  have hsub : Set.range inc.left ⊆ Set.range ((Over.pullback p).map a).left := by
    rw [hrange]
    rintro _ ⟨u, rfl⟩
    show (inc.left ≫ pullback.fst G.hom p) u ∈ CToPrinted.idCompSet G
    show F u ∈ connectedComponentIn (G.hom.base ⁻¹' {G.hom.base (F u)})
      ((η[G] : 𝟙_ (Over S) ⟶ G).left.base (G.hom.base (F u)))
    have h4 : G.hom.base (F u) = s := hFs u
    rw [h4]
    exact hTcc ⟨u, rfl⟩
  let ℓ : U ⟶ (Over.pullback p).obj V :=
    Over.homMk (IsOpenImmersion.lift ((Over.pullback p).map a).left inc.left hsub) (by
      rw [← Over.w ((Over.pullback p).map a), ← Category.assoc, IsOpenImmersion.lift_fac, Over.w inc])
  have hℓ : ℓ ≫ (Over.pullback p).map a = inc := by
    ext1
    exact IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion inc.left := hoi
  haveI : IsOpenImmersion (ℓ.left ≫ ((Over.pullback p).map a).left) := by
    rw [← Over.comp_left, hℓ]; exact hoi
  haveI : IsOpenImmersion ℓ.left := IsOpenImmersion.of_comp ℓ.left ((Over.pullback p).map a).left
  haveI : Mono ((Over.pullback p).map a) := Over.mono_of_mono_left _
  haveI : IsMonHom ((Over.pullback p).map a) := inferInstance
  haveI : IsMonHom ((Over.pullback p).map b) := inferInstance
  have hℓm : IsMonHom ℓ := isMonHom_of_comp_mono ℓ ((Over.pullback p).map a) (by rw [hℓ]; exact hmh)
  refine ⟨U, hU, ℓ ≫ (Over.pullback p).map b, ?_, ?_, hcon, rest⟩
  · show IsOpenImmersion (ℓ.left ≫ ((Over.pullback p).map b).left)
    infer_instance
  · exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ hℓm inferInstance

/-! ### §4 The main theorem -/

open ReductSplit ReductGlue CToPrinted in
/-- **SGA 7 IX 3.3, first assertion (`ReductSplit.SemistablePersistsDVR`), from the second assertion.** -/
theorem semistablePersistsDVR_of_printed (h3 : CToPrinted.SGA3_VIB_3_10) (h7 : CToPrinted.SGA7_IX_3_3)
    (hG : AVGlue.GeomConnOfRationalPoint) : ReductSplit.SemistablePersistsDVR := by
  intro K _ O _ K' _ _ _ O' _ hO A hA 𝒩' h𝒩'
  obtain ⟨𝒩, h𝒩, hs⟩ := hA
  have hsN : (bcDVR hO 𝒩).IsSemistable := (isSemistable_bcDVR_iff hO (isAlgebraic_resMap hO) 𝒩).mp hs
  -- the identity component `W ⊆ 𝒩`
  have gc := idCompSubgroup_of h3 hG
  let W : 𝒩.G.left.Opens := ⟨idCompSet 𝒩.G, h3 _ 𝒩.G⟩
  have hW : OpenSub.IsSubgroupOpen 𝒩.G W :=
    { one := fun s => idCompSet_one 𝒩.G s
      mul := (gc _ 𝒩.G).1
      inv := (gc _ 𝒩.G).2 }
  letI : GrpObj (OpenSub.G0 W) := OpenSub.grpG0 hW
  have hmon : IsMonHom (OpenSub.incl W) := OpenSub.isMonHom_incl hW
  have hoi : IsOpenImmersion (OpenSub.incl W).left := show IsOpenImmersion W.ι from inferInstance
  have hri : Set.range (OpenSub.incl W).left = idCompSet 𝒩.G := Scheme.Opens.range_ι W
  obtain ⟨j, hj, hjm⟩ := identityComponentBaseChangeDVRRange_of h3 h7 hG K O K' O' hO A ⟨𝒩, h𝒩, hs⟩
    𝒩 h𝒩 𝒩' h𝒩' (OpenSub.G0 W) (OpenSub.incl W) hoi hmon hri
  -- its base change `W ×_O O' → 𝒩 ×_O O'`, with image `(𝒩 ×_O O')⁰`
  let g := Spec.map (CommRingCat.ofHom (comapHom hO))
  letI : GrpObj ((Over.pullback g).obj (OpenSub.G0 W)) := Functor.grpObjObj
  letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
  let k := (Over.pullback g).map (OpenSub.incl W)
  haveI : IsOpenImmersion (OpenSub.incl W).left := hoi
  have hk : IsOpenImmersion k.left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ _
  have hkm : IsMonHom k := inferInstance
  have hkmap : k.left = pullback.map (OpenSub.G0 W).hom g 𝒩.G.hom g (OpenSub.incl W).left (𝟙 _) (𝟙 _)
      (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [k, Over.pullback_map_left]
  have hrk : Set.range k.left = idCompSet (bcO hO 𝒩.G) := by
    rw [hkmap, Scheme.Pullback.range_map]
    have hid : Set.range ((𝟙 (Spec (CommRingCat.of O')) : Spec (CommRingCat.of O') ⟶ _) :
        Spec (CommRingCat.of O') → Spec (CommRingCat.of O')) = Set.univ :=
      Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
    rw [hid, Set.preimage_univ, Set.inter_univ, hri]
    exact idCompBaseChangeDVR_of h3 hG K O K' O' hO 𝒩.G
  exact hasSemiAbelian_transfer (Spec.map (CommRingCat.ofHom (algebraMap O' (ResBarO O'))))
    (bcO hO 𝒩.G) 𝒩'.G ((Over.pullback g).obj (OpenSub.G0 W)) k j hk hkm hrk hj hjm hsN

/-- **The field `semistablePersistsSHcp` (`ReductB.SemistablePersistsSHcp`) discharged**: it is a specialization
of `SemistablePersistsDVR` (the proof of `ReductB.cp_of_general`, second half). -/
theorem semistablePersistsSHcp_of_printed (h3 : CToPrinted.SGA3_VIB_3_10) (h7 : CToPrinted.SGA7_IX_3_3)
    (hG : AVGlue.GeomConnOfRationalPoint) : ReductB.SemistablePersistsSHcp :=
  fun K _ _ O _ _ _ K' _ _ _ O' _ hO A hA => semistablePersistsDVR_of_printed h3 h7 hG K O K' O' hO A hA

/-- The field from the bundle fields as they stand at the base (`OpenResearchLeaves21` holds `sga7_IX_3_3_SH` and
`neronBaseChangeStrictHenselization`, from which `SGA7PersistsNF.sga7_IX_3_3_of_SH` gives `SGA7_IX_3_3`). -/
theorem semistablePersistsSHcp_of_SH (h3 : CToPrinted.SGA3_VIB_3_10) (h7 : SGA7PersistsNF.SGA7_IX_3_3_SH)
    (hN : GapSHPair.NeronBaseChangeStrictHenselization) (hG : AVGlue.GeomConnOfRationalPoint) :
    ReductB.SemistablePersistsSHcp :=
  semistablePersistsSHcp_of_printed h3 (SGA7PersistsNF.sga7_IX_3_3_of_SH h7 hN h3 hG) hG

/-! ### §5 The consumer, for the fold -/

open ReductSplit in
/-- **SS1 and SS3 without `semistablePersistsSHcp`**: `GapNeron.ss1_ss3_of_cpNF` (NeronDVR) with
`persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)` replaced by
`persistsNF_of_general (semistablePersistsDVR_of_printed h3 h7 hG)`. -/
theorem ss1_ss3_of_printedNF (h3 : CToPrinted.SGA3_VIB_3_10) (h7 : CToPrinted.SGA7_IX_3_3)
    (hG : AVGlue.GeomConnOfRationalPoint) (h36 : SemistableReductionDVR)
    (hN : GapNeron.NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal) (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ⟨GapNeron.semistableReductionThm_final_nfNF (ReductB.reductionNF_of_general h36)
      (ReductB.persistsNF_of_general (semistablePersistsDVR_of_printed h3 h7 hG)) hN hLG hAA,
    GapNeron.semistablePersists_final_nfNF
      (ReductB.persistsNF_of_general (semistablePersistsDVR_of_printed h3 h7 hG)) hN hLG⟩

end GapPersists

#print axioms GapPersists.semistablePersistsDVR_of_printed
#print axioms GapPersists.ss1_ss3_of_printedNF
#print axioms GapPersists.semistablePersistsSHcp_of_SH
