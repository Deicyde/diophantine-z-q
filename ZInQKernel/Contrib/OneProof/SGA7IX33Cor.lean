import ZInQKernel.Contrib.OneProof.SGA3NbhdDVR

/-!
# sga33-steps: the field `sga7_IX_3_3_SHpre` from SGA 7 IX Cor. 3.3 as printed

The research field `sga7_IX_3_3_SHpre` (`DictModels.SGA7Pre.SGA7_IX_3_3_SHpre`, defined in
`ZInQKernel/Contrib/OneProof/SGA7IX33SHPre.lean`) differs from the print (SGA 7 I, Exp. IX, Cor. 3.3) in three ways,
and this file proves each step in Lean:

1. **Base.** The print needs only a dominant morphism `S' → S` of regular one-dimensional schemes; the field asks
   for strictly henselian traits with `K'/K` finite. The new leaf `SGA7_IX_Cor3_3` is stated over any extension of
   discrete valuation rings `O ⊆ O'` (`O' ∩ K = O`, which makes `Spec O' → Spec O` dominant), with no henselian and
   no finiteness condition; `cor33SH_of_cor33` specializes it (`SGA7_IX_Cor3_3_SH`).
2. **Dictionary.** The print's `N⁰` is the open subgroup scheme of `N` whose fibres are the identity components
   (`idCompSet`, open over a DVR by `SGA3Nbhd.isOpen_idCompSet_groupModelO`); "the canonical map induces an
   isomorphism `N⁰ ×_S S' ≅ N'⁰`" is stated literally as an isomorphism of schemes `e : U ≅ W` over `N'`, with
   `U = N⁰ ×_S S'` (the preimage of `N⁰` in `N ×_S S'`) and `W = N'⁰`; `openImm_range_iff_iso` converts it to the
   field's "open immersion with image `N'⁰`". The print's hypothesis "semistable reduction" is a property of the
   Néron model `N` (`𝒩.IsSemistable`); the field's `HasSemistableReduction A O` (some Néron model is semistable)
   gives it for every Néron model by uniqueness of Néron models (`ReductGlue.semistableNeronModels_of_has`, from
   `ReductGlue.neronO_unique`).
3. **Comparison map.** The print has the canonical morphism `u : N ×_S S' → N'` (the unique extension of the
   identification of generic fibres, `ReductGlue.bcDVR`); the field has any homomorphism `c` whose generic fibre is
   an isomorphism. By the Néron mapping property of `N'`, `c = u ≫ α` for an automorphism `α` of `N'`
   (`exists_aut_factor`), which fixes the unit section and hence preserves `N'⁰` (`image_idCompSet_subset`).

Main results:
* `SGA33Steps.SGA7_IX_Cor3_3 : Prop` — the new LEAF (printed form);
* `SGA33Steps.shpre_of_cor33 : SGA7_IX_Cor3_3 → DictModels.SGA7Pre.SGA7_IX_3_3_SHpre` — the field, exactly, with
  no other hypothesis;
* `SGA33Steps.shpre_of_cor33SH : SGA7_IX_Cor3_3_SH → DictModels.SGA7Pre.SGA7_IX_3_3_SHpre` — the same from the
  specialization to the field's base (strictly henselian traits, `K'/K` finite), should a reading restrict the base.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology
open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted ReductSplit ReductGlue

namespace SGA33Steps

/-! ## The printed leaf and its specialization -/

/-- **LEAF `SGA7_IX_Cor3_3`** (Grothendieck, *Modèles de Néron et monodromie*, SGA 7 I, Exp. IX, LNM 288 (1972),
Cor. 3.3, p. 348; semistable reduction is Déf. 3.4, p. 349; locator from the 11-16 reading recorded in the
sga33-steps task brief, not re-read here, no network). *Printed* (as read): `S` regular of dimension one, `S' → S`
dominant with `S'` regular of dimension one, `A_K` an abelian variety with semistable reduction, `N`, `N'` the Néron
models of `A_K` over `S` and of `A_{K'}` over `S'`; then the canonical morphism `N ×_S S' → N'` induces an
isomorphism `N⁰ ×_S S' ≅ N'⁰`.

*Lean form* (a specialization): `S = Spec O`, `S' = Spec O'` for discrete valuation rings `O ⊆ K`, `O' ⊆ K'` with
`O' ∩ K = O` (`K'/K` any field extension); `𝒩`, `𝒩'` any Néron models (unique up to unique isomorphism,
`ReductGlue.neronO_unique`), `𝒩` with semistable special fibre (`GroupModelO.IsSemistable`: the identity component
of the geometric special fibre is an extension of an abelian variety by a torus); `u` the canonical morphism, i.e.
the morphism whose generic fibre is the identification `(N ×_O O')_{K'} = (N_K)_{K'} ≅ A_{K'} ≅ N'_{K'}`
(`ReductGlue.bcDVR`; it exists and is unique by the Néron mapping property of `𝒩'`); `U = N⁰ ×_O O'`, the preimage
of `N⁰ = idCompSet 𝒩.G` under the projection `N ×_O O' → N`; `W = N'⁰ = idCompSet 𝒩'.G`. Conclusion: an
isomorphism `e : U ≅ W` with `e ≫ (W ⊆ N') = (U ⊆ N ×_O O') ≫ u`. -/
def SGA7_IX_Cor3_3 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] (O' : ValuationSubring K') [IsDiscreteValuationRing O']
    (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → 𝒩.IsSemistable →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    ∀ u : bcO hO 𝒩.G ⟶ 𝒩'.G,
      (Over.pullback (jO O')).map u ≫ 𝒩'.gen.hom = (ReductGlue.bcDVR hO 𝒩).gen.hom →
    ∀ U : (bcO hO 𝒩.G).left.Opens,
      (U : Set (bcO hO 𝒩.G).left) =
        pullback.fst 𝒩.G.hom (Spec.map (CommRingCat.ofHom (comapHom hO))) ⁻¹' idCompSet 𝒩.G →
    ∀ W : 𝒩'.G.left.Opens, (W : Set 𝒩'.G.left) = idCompSet 𝒩'.G →
      ∃ e : (U : Scheme) ≅ (W : Scheme), e.hom ≫ W.ι = U.ι ≫ u.left

/-- **GLUE (step 1, specialization) `SGA7_IX_Cor3_3_SH`**: `SGA7_IX_Cor3_3` over the field's base (strictly henselian
traits, `K'/K` finite). Proved from the leaf (`cor33SH_of_cor33`); stated separately so that the field can be
rerouted to it should a reading restrict the base of Cor. 3.3. -/
def SGA7_IX_Cor3_3_SH : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], IsStrictlyHenselianDVR O' →
    ∀ (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel → 𝒩.IsSemistable →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    ∀ u : bcO hO 𝒩.G ⟶ 𝒩'.G,
      (Over.pullback (jO O')).map u ≫ 𝒩'.gen.hom = (ReductGlue.bcDVR hO 𝒩).gen.hom →
    ∀ U : (bcO hO 𝒩.G).left.Opens,
      (U : Set (bcO hO 𝒩.G).left) =
        pullback.fst 𝒩.G.hom (Spec.map (CommRingCat.ofHom (comapHom hO))) ⁻¹' idCompSet 𝒩.G →
    ∀ W : 𝒩'.G.left.Opens, (W : Set 𝒩'.G.left) = idCompSet 𝒩'.G →
      ∃ e : (U : Scheme) ≅ (W : Scheme), e.hom ≫ W.ι = U.ι ≫ u.left

/-- **Step 1**: the specialization of the base. -/
theorem cor33SH_of_cor33 (h : SGA7_IX_Cor3_3) : SGA7_IX_Cor3_3_SH := by
  intro K _ O _ _ K' _ _ _ O' _ _ hO A 𝒩 h𝒩 hs 𝒩' h𝒩' u hu U hU W hW
  exact h K O K' O' hO A 𝒩 h𝒩 hs 𝒩' h𝒩' u hu U hU W hW

/-! ## Step 2: the dictionary -/

/-- "Open immersion with image `V`" is "isomorphism onto the open subscheme `V`". -/
theorem openImm_range_iff_iso {X Y : Scheme.{0}} (f : X ⟶ Y) (V : Y.Opens) :
    (IsOpenImmersion f ∧ Set.range f = (V : Set Y)) ↔ ∃ e : X ≅ (V : Scheme), e.hom ≫ V.ι = f := by
  constructor
  · rintro ⟨hf, hr⟩
    refine ⟨IsOpenImmersion.isoOfRangeEq f V.ι (hr.trans (Scheme.Opens.range_ι V).symm), ?_⟩
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  · rintro ⟨e, rfl⟩
    refine ⟨inferInstance, ?_⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rw [show Set.range e.hom = Set.univ from Set.range_eq_univ.mpr e.hom.surjective, Set.image_univ,
      Scheme.Opens.range_ι]

/-! ## Step 3: an arbitrary comparison map is the canonical one followed by an automorphism -/

section Image

variable {S : Scheme.{0}}

/-- A morphism of group schemes over `S` that preserves the unit section maps `G⁰` into `H⁰`. -/
theorem image_idCompSet_subset (G H : Over S) [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (hf : η[G] ≫ f = η[H]) : f.left '' idCompSet G ⊆ idCompSet H := by
  rintro _ ⟨x, hx, rfl⟩
  let eG := (η[G] : 𝟙_ (Over S) ⟶ G).left
  let eH := (η[H] : 𝟙_ (Over S) ⟶ H).left
  have hfw : ∀ y, H.hom (f.left y) = G.hom y := by
    intro y
    rw [← Scheme.Hom.comp_apply, Over.w]
  have hfe : ∀ s, f.left (eG s) = eH s := by
    intro s
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hf]
  let C := connectedComponentIn (G.hom ⁻¹' {G.hom x}) (eG (G.hom x))
  have hC : _root_.IsPreconnected (f.left '' C) :=
    isPreconnected_connectedComponentIn.image _ f.left.continuous.continuousOn
  have hsub : f.left '' C ⊆ H.hom ⁻¹' {G.hom x} := by
    rintro _ ⟨y, hy, rfl⟩
    show H.hom (f.left y) = G.hom x
    rw [hfw]
    exact connectedComponentIn_subset (G.hom ⁻¹' {G.hom x}) _ hy
  have heG : G.hom (eG (G.hom x)) = G.hom x := by
    rw [← Scheme.Hom.comp_apply, Over.w]
    rfl
  have hes : eH (G.hom x) ∈ f.left '' C :=
    ⟨eG (G.hom x), mem_connectedComponentIn (show _ ∈ G.hom ⁻¹' {G.hom x} from heG), hfe _⟩
  have := hC.subset_connectedComponentIn hes hsub ⟨x, hx, rfl⟩
  show f.left x ∈ connectedComponentIn (H.hom ⁻¹' {H.hom (f.left x)}) (eH (H.hom (f.left x)))
  rw [hfw]
  exact this

/-- An isomorphism of group schemes over `S` preserving the unit section maps `G⁰` onto `H⁰`. -/
theorem image_idCompSet_eq (G H : Over S) [GrpObj G] [GrpObj H] (f : G ≅ H)
    (hf : η[G] ≫ f.hom = η[H]) : f.hom.left '' idCompSet G = idCompSet H := by
  have hf' : η[H] ≫ f.inv = η[G] := by rw [← hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine (image_idCompSet_subset G H f.hom hf).antisymm ?_
  intro y hy
  refine ⟨f.inv.left y, image_idCompSet_subset H G f.inv hf' ⟨y, hy, rfl⟩, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.inv_hom_id]
  rfl

end Image

section Factor

variable {K : Type} [Field K] {O : ValuationSubring K} {B : PkgI3.AbVar K}

/-- **Step 3, the factorization**: for a Néron model `𝒩'` and morphisms `u, c : Y → 𝒩'` from a smooth `Y` whose
generic fibres are isomorphisms, `c = u ≫ α` for an automorphism `α` of `𝒩'`. -/
theorem exists_aut_factor (𝒩' : GroupModelO B O) (h𝒩' : 𝒩'.IsNeronModel)
    (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom] (u c : Y ⟶ 𝒩'.G)
    (hu : IsIso ((Over.pullback (jO O)).map u)) (hc : IsIso ((Over.pullback (jO O)).map c)) :
    ∃ α : 𝒩'.G ≅ 𝒩'.G, c = u ≫ α.hom := by
  let F := Over.pullback (jO O)
  let e' := 𝒩'.gen.hom
  obtain ⟨α, hα⟩ := (h𝒩' 𝒩'.G).2 (inv (F.map u) ≫ F.map c ≫ e')
  obtain ⟨β, hβ⟩ := (h𝒩' 𝒩'.G).2 (inv (F.map c) ≫ F.map u ≫ e')
  simp only at hα hβ
  have hα' : F.map α = inv (F.map u) ≫ F.map c :=
    (cancel_mono e').1 (by rw [hα, Category.assoc])
  have hβ' : F.map β = inv (F.map c) ≫ F.map u :=
    (cancel_mono e').1 (by rw [hβ, Category.assoc])
  have e1 : α ≫ β = 𝟙 _ := (h𝒩' 𝒩'.G).1 (by
    simp only
    rw [Functor.map_comp, hα', hβ', CategoryTheory.Functor.map_id]
    simp)
  have e2 : β ≫ α = 𝟙 _ := (h𝒩' 𝒩'.G).1 (by
    simp only
    rw [Functor.map_comp, hα', hβ', CategoryTheory.Functor.map_id]
    simp)
  refine ⟨⟨α, β, e1, e2⟩, ?_⟩
  show c = u ≫ α
  apply (h𝒩' Y).1
  simp only
  rw [Functor.map_comp, Category.assoc, hα]
  exact (IsIso.hom_inv_id_assoc (F.map u) _).symm

end Factor

/-! ## The field -/

/-- **The field `sga7_IX_3_3_SHpre`, exactly**, from the specialization `SGA7_IX_Cor3_3_SH` (steps 2 and 3). -/
theorem shpre_of_cor33SH (h : SGA7_IX_Cor3_3_SH) : DictModels.SGA7Pre.SGA7_IX_3_3_SHpre := by
  intro K _ O _ hS K' _ _ _ O' _ hS' hO A hA 𝒩 h𝒩 𝒩' h𝒩' c hc hci U hU
  -- step 2: semistability of the given Néron model, by uniqueness of Néron models
  have hs : 𝒩.IsSemistable := ReductGlue.semistableNeronModels_of_has hA 𝒩 h𝒩
  -- the canonical morphism `u`
  let N := ReductGlue.bcDVR hO 𝒩
  letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of O')))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (N.G ⊗ N.G).hom := ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  obtain ⟨u, hu⟩ := (h𝒩' N.G).2 N.gen.hom
  simp only at hu
  have hum : IsMonHom u :=
    ReductGlue.isMonHom_of_ext (Over.pullback (jO O')) N.gen.hom 𝒩'.gen.hom N.gen_hom 𝒩'.gen_hom
      (h𝒩' _).1 (h𝒩' _).1 u hu
  have huiso : IsIso ((Over.pullback (jO O')).map u) := by
    have : IsIso ((Over.pullback (jO O')).map u ≫ 𝒩'.gen.hom) := by
      rw [hu]; exact Iso.isIso_hom N.gen
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom 𝒩'.gen) this
  -- step 2: `N'⁰` as an open subscheme, and the printed isomorphism
  let W : 𝒩'.G.left.Opens := ⟨idCompSet 𝒩'.G, SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩'⟩
  obtain ⟨ho, hr⟩ := (openImm_range_iff_iso (U.ι ≫ u.left) W).2
    (h K O hS K' O' hS' hO A 𝒩 h𝒩 hs 𝒩' h𝒩' u hu U hU W rfl)
  -- step 3: `c = u ≫ α`, `α` an automorphism fixing the unit section
  haveI : Smooth (bcO hO 𝒩.G).hom := N.smooth
  obtain ⟨α, hα⟩ := exists_aut_factor 𝒩' h𝒩' (bcO hO 𝒩.G) u c huiso hci
  have hαe : η[𝒩'.G] ≫ α.hom = η[𝒩'.G] := by
    have h1 : η[bcO hO 𝒩.G] ≫ u = η[𝒩'.G] := hum.one_hom
    have h2 : η[bcO hO 𝒩.G] ≫ c = η[𝒩'.G] := hc.one_hom
    calc η[𝒩'.G] ≫ α.hom = (η[bcO hO 𝒩.G] ≫ u) ≫ α.hom := by rw [h1]
      _ = η[bcO hO 𝒩.G] ≫ c := by rw [hα]; exact Category.assoc _ _ _
      _ = η[𝒩'.G] := h2
  have hcl : U.ι ≫ c.left = (U.ι ≫ u.left) ≫ α.hom.left := by
    rw [hα]; exact (Category.assoc _ _ _).symm
  haveI : IsIso α.hom.left := Functor.map_isIso (Over.forget _) α.hom
  haveI := ho
  refine ⟨by rw [hcl]; infer_instance, ?_⟩
  rw [hcl, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [hr]
  exact image_idCompSet_eq 𝒩'.G 𝒩'.G α hαe

/-- **The field `sga7_IX_3_3_SHpre`, exactly**, from the printed leaf `SGA7_IX_Cor3_3` (steps 1, 2, 3). -/
theorem shpre_of_cor33 (h : SGA7_IX_Cor3_3) : DictModels.SGA7Pre.SGA7_IX_3_3_SHpre :=
  shpre_of_cor33SH (cor33SH_of_cor33 h)

end SGA33Steps

end
