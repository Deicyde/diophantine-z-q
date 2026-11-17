import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron
import ZInQKernel.Contrib.FrobChain.Rigidity
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing

/-!
# goodmodel-iso: the comparison glue `NeronGoodModelIso` from BLR 1.4 Thm 3 over a DVR

Task goodmodel-iso (2026-11-16); report docs/research/goodmodel-iso.md. group-law-dvr reduced *GIT* Thm 6.14 over a
DVR to the Néron existence leaf and one glue Prop, `ZInQ.Contrib.GroupLawNeron.NeronGoodModelIso`
(`MumfordGroupLawNeron.lean`). This file proves that glue from the DVR case of the leaf, with no purity theorem:

* `neronGoodModelIso_of_dvr : NeronSchemeExtensionDVR → NeronGoodModelIso` (and `_of_dedekind`);
* `mumfordGroupLawDVR_of_dedekind : NeronSchemeExtensionDedekind → MumfordGroupLawDVR`.

Proof. Group case (`isIso_of_grp`: `N` smooth, separated, quasi-compact, with a group law whose identity is
`e ≫ ψ`):
1. (`exists_inverse_open`) the inverse of `ψ_K` extends to an open `V ⊆ N` containing the generic fibre and
   meeting every component of the special fibre (the vendored FLT lemma
   `NeronModelInfra.exists_opens_extension_of_isProper_of_smooth`, target `F` proper); on `V` and on `ψ⁻¹ V` it
   inverts `ψ` (density of the generic fibre in a flat scheme).
2. (`fibre_injective`) `ψ` is injective on the special fibre: its base change `ψ_k : A → N_k` is a homomorphism
   by rigidity (`MulRigidity.isMonHom_of_geometricallyIntegral`), and if `ψ_k x = ψ_k y` for field-valued points,
   translating by a point `w` with `xw, yw` in the (dense open) locus where `ψ` is invertible gives `xw = yw`.
3. (`isIso_of_injective`) for `z ∈ N` the fibre `ψ⁻¹ z` lies in an affine open `Y`; an affine `U' ∋ z` has
   `ψ⁻¹ U' ⊆ Y`, and `v|_{U' ∩ V}` extends to `U' → Y` by Hartogs (vendored
   `existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk`; stalks of a scheme smooth over a DVR are normal
   domains, points of dimension ≤ 1 lie in `V`). So `ψ` is an isomorphism over each `U'`.
General `N`: compose `ψ` with the extension `χ : N → N'` into the Néron model `N'` (which carries the Néron group
law); `ψ ≫ χ` is an isomorphism by the group case, so `ψ` has a left inverse, a right inverse by density.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.GoodModelIso

open ZInQ.Contrib.GroupLawNeron

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The generic point map never hits the closed point. -/
lemma genMap_ne_closedPoint (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (t : Spec (CommRingCat.of K)) : (genMap R K).base t ≠ IsLocalRing.closedPoint R := by
  intro h
  have h1 : ((genMap R K).base t).asIdeal = Ideal.comap (algebraMap R K) t.asIdeal := rfl
  have h2 : t.asIdeal = ⊥ := by
    have := t.isPrime
    exact Ideal.eq_bot_of_prime t.asIdeal
  rw [h, h2, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)] at h1
  exact IsDiscreteValuationRing.not_a_field R h1

theorem genMap_isSchemeTheoreticallyDominant (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsSchemeTheoreticallyDominant (genMap R K) :=
  NeronC.isSchemeTheoreticallyDominant_spec_map _ (IsFractionRing.injective R K)

/-- **Density of the generic fibre.** Two morphisms from a flat `R`-scheme to a separated one that agree over
`Spec R` and on an open containing every point of the generic fibre are equal. -/
lemma ext_of_generic_open {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p]
    (s : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated s] {f g : X ⟶ Y} (hfs : f ≫ s = g ≫ s)
    (O : X.Opens) (hO : ∀ x, p.base x ≠ IsLocalRing.closedPoint R → x ∈ O)
    (hfg : O.ι ≫ f = O.ι ≫ g) : f = g := by
  haveI := genMap_isSchemeTheoreticallyDominant (R := R) (FractionRing R)
  let j := pullback.fst p (genMap R (FractionRing R))
  have hr : Set.range j.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hO
    have : (j ≫ p).base z = (pullback.snd p (genMap R (FractionRing R)) ≫ genMap R (FractionRing R)).base z := by
      rw [pullback.condition]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
    rw [this]
    exact genMap_ne_closedPoint _ _
  have hj : j = IsOpenImmersion.lift O.ι j hr ≫ O.ι := (IsOpenImmersion.lift_fac _ _ _).symm
  refine NeronC.ext_of_isSchemeTheoreticallyDominant_of_isSeparated s hfs j ?_
  rw [hj, Category.assoc, Category.assoc, hfg]

open ZInQ.Contrib.CloudW03NeronSurj.FLT in
/-- **Step A–B.** The inverse of `ψ_K` extends to an open `V ⊆ N` containing the generic fibre and meeting every
irreducible component of the special fibre (FLT's extension into a proper target), and on `V` and `ψ⁻¹ V` it is
an inverse of `ψ` (density of the generic fibre). -/
lemma exists_inverse_open (F N : Over (Spec (CommRingCat.of R))) [IsProper F.hom] [Smooth F.hom]
    [Smooth N.hom] [IsSeparated N.hom] [QuasiCompact N.hom] (ψ : F ⟶ N)
    (hK : IsIso ((Over.pullback (genMap R (FractionRing R))).map ψ)) :
    ∃ (V : N.left.Opens) (v : (V : Scheme) ⟶ F.left), v ≫ F.hom = V.ι ≫ N.hom ∧
      (∀ x : N.left, N.hom.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      (∀ Z ∈ irreducibleComponents {x : N.left // N.hom.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V) ∧
      v ≫ ψ.left = V.ι ∧ (ψ.left ∣_ V) ≫ v = (ψ.left ⁻¹ᵁ V).ι := by
  let K := FractionRing R
  let s0 := genMap R K
  haveI := genMap_isSchemeTheoreticallyDominant (R := R) K
  let ψK := ((Over.pullback s0).map ψ).left
  haveI : IsIso ψK := by
    have : IsIso ((Over.pullback s0).map ψ) := hK
    exact (Over.forget _).map_isIso ((Over.pullback s0).map ψ)
  have hψK1 : ψK ≫ pullback.fst N.hom s0 = pullback.fst F.hom s0 ≫ ψ.left := by
    simp [ψK]
  have hψK2 : ψK ≫ pullback.snd N.hom s0 = pullback.snd F.hom s0 := by
    simp [ψK]
  let iψ : ((Over.pullback s0).obj N).left ⟶ ((Over.pullback s0).obj F).left := inv ψK
  have hiψ : iψ ≫ pullback.snd F.hom s0 = pullback.snd N.hom s0 := by
    simp only [iψ]; rw [IsIso.inv_comp_eq]; exact hψK2.symm
  let uK : NeronModelInfra.SchemeHomOver (pullback.snd N.hom (NeronModelInfra.specGenericFibreInclusion R K))
      (pullback.snd F.hom (NeronModelInfra.specGenericFibreInclusion R K)) :=
    ⟨iψ, hiψ⟩
  obtain ⟨V, v, hVη, hVs, hvK⟩ :=
    NeronModelInfra.exists_opens_extension_of_isProper_of_smooth R K F.hom N.hom uK
  have hv := v.2
  -- the generic fibre of `v`
  have hvK' : pullback.fst (V.ι ≫ N.hom) s0 ≫ v.1 =
      pullback.map (V.ι ≫ N.hom) s0 N.hom s0 V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ inv ψK ≫ pullback.fst F.hom s0 := by
    have := NeronModelInfra.genericFibreRestrict_coe_comp_fst (R := R) (K := K) F.hom (V.ι ≫ N.hom) v
    refine this.symm.trans ?_
    rw [hvK, Category.assoc]
    rfl
  have hB1 : v.1 ≫ ψ.left = V.ι := by
    refine NeronC.ext_of_isSchemeTheoreticallyDominant_of_isSeparated N.hom ?_
      (pullback.fst (V.ι ≫ N.hom) s0) ?_
    · rw [Category.assoc, Over.w ψ, hv]
    · rw [← Category.assoc, hvK', Category.assoc, Category.assoc, ← hψK1, IsIso.inv_hom_id_assoc]
      simp
  refine ⟨V, v.1, hv, hVη, hVs, hB1, ?_⟩
  let P0 := ψ.left ⁻¹ᵁ V
  refine NeronC.ext_of_isSchemeTheoreticallyDominant_of_isSeparated F.hom ?_
    (pullback.fst (P0.ι ≫ F.hom) s0) ?_
  · rw [Category.assoc, hv, ← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w ψ]
  · let m := pullback.map (P0.ι ≫ F.hom) s0 (V.ι ≫ N.hom) s0 (ψ.left ∣_ V) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w ψ])
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    let pP := pullback.map (P0.ι ≫ F.hom) s0 F.hom s0 P0.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    have h1 : pullback.fst (P0.ι ≫ F.hom) s0 ≫ (ψ.left ∣_ V) = m ≫ pullback.fst (V.ι ≫ N.hom) s0 := by
      simp [m]
    have h2 : m ≫ pullback.map (V.ι ≫ N.hom) s0 N.hom s0 V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) = pP ≫ ψK := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hψK1]
        simp [m, pP, morphismRestrict_ι]
        rfl
      · rw [Category.assoc, Category.assoc, hψK2]
        simp [m, pP]
    rw [← Category.assoc, h1, Category.assoc, hvK', ← Category.assoc m, h2, Category.assoc,
      IsIso.hom_inv_id_assoc]
    simp [pP]
    rfl

/-- On `ψ⁻¹ V` a morphism into `F` is determined by its composite with `ψ` (from `(ψ ∣_ V) ≫ v = ι`). -/
lemma eq_of_comp_eq {F N : Over (Spec (CommRingCat.of R))} (ψ : F ⟶ N) (V : N.left.Opens)
    (v : (V : Scheme) ⟶ F.left) (hB2 : (ψ.left ∣_ V) ≫ v = (ψ.left ⁻¹ᵁ V).ι) {S : Scheme.{0}}
    (a b : S ⟶ F.left) (ha : ∀ x, ψ.left.base (a.base x) ∈ V) (hb : ∀ x, ψ.left.base (b.base x) ∈ V)
    (hab : a ≫ ψ.left = b ≫ ψ.left) : a = b := by
  let P0 := ψ.left ⁻¹ᵁ V
  have hra : Set.range a.base ⊆ Set.range P0.ι.base := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact ha x
  have hrb : Set.range b.base ⊆ Set.range P0.ι.base := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact hb x
  let la := IsOpenImmersion.lift P0.ι a hra
  let lb := IsOpenImmersion.lift P0.ι b hrb
  have hla : la ≫ P0.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hlb : lb ≫ P0.ι = b := IsOpenImmersion.lift_fac _ _ _
  have h : la ≫ (ψ.left ∣_ V) = lb ≫ (ψ.left ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      ← Category.assoc]
    change (la ≫ P0.ι) ≫ ψ.left = (lb ≫ P0.ι) ≫ ψ.left
    rw [hla, hlb, hab]
  rw [← hla, ← hlb, ← hB2, ← Category.assoc, ← Category.assoc, h]

open ZInQ.Contrib.CloudW03NeronSurj.FLT in
/-- **Steps D–G.** If moreover `ψ` is injective on points, it is an isomorphism (Hartogs extension of `v` into
an affine neighbourhood of each fibre). -/
lemma isIso_of_injective (F N : Over (Spec (CommRingCat.of R))) [IsProper F.hom] [Smooth F.hom]
    [Smooth N.hom] [IsSeparated N.hom] (ψ : F ⟶ N) (V : N.left.Opens) (v : (V : Scheme) ⟶ F.left)
    (hv : v ≫ F.hom = V.ι ≫ N.hom)
    (hVη : ∀ x : N.left, N.hom.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : N.left // N.hom.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (hB1 : v ≫ ψ.left = V.ι) (hB2 : (ψ.left ∣_ V) ≫ v = (ψ.left ⁻¹ᵁ V).ι)
    (hinj : Function.Injective ψ.left.base) : IsIso ψ := by
  have hψN : ψ.left ≫ N.hom = F.hom := Over.w ψ
  haveI : IsProper ψ.left := by
    haveI : IsProper (ψ.left ≫ N.hom) := by rw [hψN]; infer_instance
    exact IsProper.of_comp ψ.left N.hom
  haveI : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have hB1pt : ∀ r, ψ.left.base (v.base r) = V.ι.base r := fun r => by
    rw [← Scheme.Hom.comp_apply, hB1]
  suffices h : IsIso ψ.left by
    haveI : IsIso ((Over.forget _).map ψ) := h
    exact isIso_of_reflects_iso ψ (Over.forget _)
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := MorphismProperty.isomorphisms Scheme)
    (f := ψ.left) (fun z => ?_)
  -- D: an affine open `Y` containing the fibre over `z`, and an affine `U' ∋ z` with `ψ⁻¹ U' ⊆ Y`
  obtain ⟨Y, hY, hYz⟩ : ∃ Y : F.left.Opens, IsAffineOpen Y ∧ ∀ x, ψ.left.base x = z → x ∈ Y := by
    by_cases h : ∃ x, ψ.left.base x = z
    · obtain ⟨x, hx⟩ := h
      obtain ⟨Y, hY, hxY, -⟩ : ∃ Y : F.left.Opens, IsAffineOpen Y ∧ x ∈ Y ∧ Y ≤ ⊤ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp F.left.isBasis_affineOpens)
        (Set.mem_univ x : x ∈ (⊤ : F.left.Opens))
      exact ⟨Y, hY, fun x' hx' => by rw [hinj (hx'.trans hx.symm)]; exact hxY⟩
    · exact ⟨⊥, isAffineOpen_bot _, fun x hx => (h ⟨x, hx⟩).elim⟩
  let U : N.left.Opens := ⟨(ψ.left.base '' (Y : Set F.left)ᶜ)ᶜ,
    isOpen_compl_iff.mpr (ψ.left.isClosedMap _ Y.isOpen.isClosed_compl)⟩
  have hzU : z ∈ U := by
    rintro ⟨x, hx, rfl⟩; exact hx (hYz x rfl)
  have hUY : ∀ x, ψ.left.base x ∈ U → x ∈ Y := by
    intro x hx; by_contra h; exact hx ⟨x, h, rfl⟩
  obtain ⟨U', hU', hzU', hU'U⟩ : ∃ U' : N.left.Opens, IsAffineOpen U' ∧ z ∈ U' ∧ U' ≤ U :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp N.left.isBasis_affineOpens) hzU
  refine ⟨U', hzU', ?_⟩
  haveI : IsAffine (Y : Scheme) := hY
  haveI : IsAffine (U' : Scheme) := hU'
  -- E: Hartogs
  have hT : ∀ x : (U' : Scheme), IsDomain ((U' : Scheme).presheaf.stalk x) ∧
      IsIntegrallyClosed ((U' : Scheme).presheaf.stalk x) := fun x =>
    AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R (U'.ι ≫ N.hom) x
  have hVU : ∀ x : (U' : Scheme), ringKrullDim ((U' : Scheme).presheaf.stalk x) ≤ 1 → x ∈ U'.ι ⁻¹ᵁ V := by
    intro x hx
    show U'.ι.base x ∈ V
    refine AlgebraicGeometry.mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing R N.hom V hVη hVs _ ?_
    rwa [ringKrullDim_eq_of_ringEquiv (asIso (U'.ι.stalkMap x)).commRingCatIsoToRingEquiv]
  let O := U'.ι ⁻¹ᵁ V
  have hr : Set.range ((U'.ι ∣_ V) ≫ v).base ⊆ Set.range Y.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hUY
    rw [Scheme.Hom.comp_apply, hB1pt, ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    have hm : U'.ι.base (O.ι.base p) ∈ Set.range U'.ι.base := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at hm
    exact hU'U hm
  let v' : (O : Scheme) ⟶ (Y : Scheme) := IsOpenImmersion.lift Y.ι ((U'.ι ∣_ V) ≫ v) hr
  have hv' : v' ≫ Y.ι = (U'.ι ∣_ V) ≫ v := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ, -⟩ := AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk hT O hVU v'
  -- `φ` lies over `Spec R` (uniqueness of extensions into the affine `Spec R`)
  have hφR : φ ≫ Y.ι ≫ F.hom = U'.ι ≫ N.hom := by
    obtain ⟨_, -, huniq⟩ := AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk hT O hVU
      (O.ι ≫ U'.ι ≫ N.hom)
    have e1 := huniq (φ ≫ Y.ι ≫ F.hom) (by
      beta_reduce
      rw [← Category.assoc, hφ, ← Category.assoc, hv', Category.assoc, hv, ← Category.assoc,
        morphismRestrict_ι, Category.assoc])
    have e2 := huniq (U'.ι ≫ N.hom) rfl
    rw [e1, e2]
  have hOgen : ∀ x : (U' : Scheme), (U'.ι ≫ N.hom).base x ≠ IsLocalRing.closedPoint R → x ∈ O :=
    fun x hx => hVη _ hx
  -- F: `φ` is a section of `ψ` over `U'`
  have h1 : φ ≫ Y.ι ≫ ψ.left = U'.ι := by
    refine ext_of_generic_open (U'.ι ≫ N.hom) N.hom ?_ O hOgen ?_
    · rw [Category.assoc, Category.assoc, hψN, hφR]
    · rw [← Category.assoc, hφ, ← Category.assoc, hv', Category.assoc, hB1, morphismRestrict_ι]
  let P := ψ.left ⁻¹ᵁ U'
  have hrP : Set.range (φ ≫ Y.ι).base ⊆ Set.range P.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    show ψ.left.base ((φ ≫ Y.ι).base p) ∈ U'
    rw [← Scheme.Hom.comp_apply, Category.assoc, h1]
    have hm : U'.ι.base p ∈ Set.range U'.ι.base := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at hm
  let φ' : (U' : Scheme) ⟶ (P : Scheme) := IsOpenImmersion.lift P.ι (φ ≫ Y.ι) hrP
  have hφ' : φ' ≫ P.ι = φ ≫ Y.ι := IsOpenImmersion.lift_fac _ _ _
  have hb : φ' ≫ (ψ.left ∣_ U') = 𝟙 _ := by
    rw [← cancel_mono U'.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hφ', Category.assoc, h1,
      Category.id_comp]
  have ha : (ψ.left ∣_ U') ≫ φ' = 𝟙 _ := by
    rw [← cancel_mono P.ι, Category.assoc, hφ', Category.id_comp]
    let O2 := P.ι ⁻¹ᵁ (ψ.left ⁻¹ᵁ V)
    refine ext_of_generic_open (P.ι ≫ F.hom) F.hom ?_ O2 ?_ ?_
    · rw [Category.assoc, Category.assoc, hφR, ← Category.assoc, morphismRestrict_ι, Category.assoc, hψN]
    · intro x hx
      show ψ.left.base (P.ι.base x) ∈ V
      apply hVη
      rw [← Scheme.Hom.comp_apply, hψN]
      exact hx
    · refine eq_of_comp_eq ψ V v hB2 _ _ ?_ ?_ ?_
      · intro x
        rw [← Scheme.Hom.comp_apply]
        have : ((O2.ι ≫ (ψ.left ∣_ U') ≫ φ ≫ Y.ι) ≫ ψ.left) = O2.ι ≫ P.ι ≫ ψ.left := by
          rw [Category.assoc, Category.assoc, Category.assoc, h1, morphismRestrict_ι]
        rw [this, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact x.2
      · intro x; rw [Scheme.Hom.comp_apply]; exact x.2
      · rw [Category.assoc, Category.assoc, Category.assoc, h1, morphismRestrict_ι, Category.assoc]
  exact (MorphismProperty.isomorphisms.iff _).mpr ⟨⟨φ', ha, hb⟩⟩

/-- The closed point of `Spec R` through the residue field. -/
abbrev resMap (R : Type) [CommRing R] [IsLocalRing R] :
    Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))

lemma resMap_apply (t : Spec (CommRingCat.of (IsLocalRing.ResidueField R))) :
    (resMap R).base t = IsLocalRing.closedPoint R := by
  apply PrimeSpectrum.ext
  show Ideal.comap _ t.asIdeal = IsLocalRing.maximalIdeal R
  have : t.asIdeal = ⊥ := by
    have := t.isPrime
    exact Ideal.eq_bot_of_prime t.asIdeal
  rw [this, ← RingHom.ker_eq_comap_bot]
  exact IsLocalRing.ker_residue

/-- The base change of `ψ` to a field fibre, as a morphism out of the abelian variety `A`. -/
def fibreMap {F N : Over (Spec (CommRingCat.of R))} (ψ : F ⟶ N) {k : Type} [Field k]
    {s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)} (A : PkgI3.AbVar k) (g : A.X.left ⟶ F.left)
    (hw : g ≫ F.hom = A.X.hom ≫ s) : A.X ⟶ (Over.pullback s).obj N :=
  Over.homMk (pullback.lift (g ≫ ψ.left) A.X.hom (by rw [Category.assoc, Over.w ψ, hw]))
    (pullback.lift_snd _ _ _)

@[reassoc]
lemma fibreMap_fst {F N : Over (Spec (CommRingCat.of R))} (ψ : F ⟶ N) {k : Type} [Field k]
    {s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)} (A : PkgI3.AbVar k) (g : A.X.left ⟶ F.left)
    (hw : g ≫ F.hom = A.X.hom ≫ s) :
    (fibreMap ψ A g hw).left ≫ pullback.fst N.hom s = g ≫ ψ.left :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma fibreMap_hom {F N : Over (Spec (CommRingCat.of R))} (ψ : F ⟶ N) {k : Type} [Field k]
    {s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)} (A : PkgI3.AbVar k) (g : A.X.left ⟶ F.left)
    (hw : g ≫ F.hom = A.X.hom ≫ s) :
    (fibreMap ψ A g hw).left ≫ ((Over.pullback s).obj N).hom = A.X.hom :=
  Over.w (fibreMap ψ A g hw)

/-- **Rigidity on a field fibre.** The base change of `ψ` is a homomorphism. -/
lemma fibreMap_isMonHom {F N : Over (Spec (CommRingCat.of R))} [IsSeparated N.hom] [LocallyOfFiniteType N.hom]
    [GrpObj N] (ψ : F ⟶ N) (e : Spec (CommRingCat.of R) ⟶ F.left) (hη : e ≫ ψ.left = η[N].left)
    {k : Type} [Field k] {s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)} (A : PkgI3.AbVar k)
    (g : A.X.left ⟶ F.left) (hw : g ≫ F.hom = A.X.hom ≫ s) (hone : (1 : A.Pt k).left ≫ g = s ≫ e) :
    letI : GrpObj ((Over.pullback s).obj N) := Functor.grpObjObj
    IsMonHom (fibreMap ψ A g hw) := by
  letI : GrpObj ((Over.pullback s).obj N) := Functor.grpObjObj
  haveI : IsSeparated ((Over.pullback s).obj N).hom := by
    change IsSeparated (pullback.snd N.hom s); infer_instance
  haveI : LocallyOfFiniteType ((Over.pullback s).obj N).hom := by
    change LocallyOfFiniteType (pullback.snd N.hom s); infer_instance
  refine MulRigidity.isMonHom_of_geometricallyIntegral A.X _ _ ?_
  have h2 := hone
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left] at h2
  simp only [PkgI3.AbVar.ptObj, Over.mk_hom, spec_algebraMap_self] at h2
  have h4 : Over.Hom.left η[A.X] ≫ g = s ≫ e := by
    rw [← h2, Category.assoc]; exact (Category.id_comp _).symm
  rw [Functor.obj.η_def]
  ext1
  apply pullback.hom_ext
  · have e1 : ((Over.pullback s).map η[N]).left ≫ pullback.fst N.hom s =
        pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom s ≫ η[N].left := by simp
    have e2 : (Functor.LaxMonoidal.ε (Over.pullback s)).left ≫
        pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom s = s := by
      have hw := Over.w (Functor.LaxMonoidal.ε (Over.pullback s))
      have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of R)))).hom) (g := s)
      have h1 : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom s =
          pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom s ≫ (𝟙_ (Over (Spec (CommRingCat.of R)))).hom :=
        (Category.comp_id _).symm
      rw [h1, hc, ← Category.assoc]
      erw [hw]
      exact Category.id_comp _
    rw [Over.comp_left, Category.assoc, fibreMap_fst, ← Category.assoc, h4, Category.assoc, hη,
      Over.comp_left, Category.assoc, e1, ← Category.assoc, e2]
  · rw [Over.comp_left, Category.assoc]
    erw [fibreMap_hom]
    rw [Over.comp_left, Category.assoc]
    erw [Over.w ((Over.pullback s).map η[N])]
    erw [Over.w (Functor.LaxMonoidal.ε (Over.pullback s))]
    exact Over.w η[A.X]

/-- **Step C (special fibre).** On a field fibre that is an abelian variety, `ψ` is injective on points, given one
point of the fibre mapping into `V` (translation by field-valued points and rigidity). -/
lemma fibre_injective {F N : Over (Spec (CommRingCat.of R))} [IsSeparated N.hom] [LocallyOfFiniteType N.hom]
    [GrpObj N] (ψ : F ⟶ N) (e : Spec (CommRingCat.of R) ⟶ F.left) (hη : e ≫ ψ.left = η[N].left)
    {k : Type} [Field k] {s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)} (A : PkgI3.AbVar k)
    (g : A.X.left ⟶ F.left) (hpb : IsPullback g A.X.hom F.hom s) (hone : (1 : A.Pt k).left ≫ g = s ≫ e)
    (hs : Function.Injective (pullback.fst N.hom s).base)
    (V : N.left.Opens) (v : (V : Scheme) ⟶ F.left) (hB2 : (ψ.left ∣_ V) ≫ v = (ψ.left ⁻¹ᵁ V).ι)
    (hW : ∃ a0 : A.X.left, ψ.left.base (g.base a0) ∈ V) (a1 a2 : A.X.left)
    (h12 : ψ.left.base (g.base a1) = ψ.left.base (g.base a2)) : a1 = a2 := by
  letI : GrpObj ((Over.pullback s).obj N) := Functor.grpObjObj
  let ψk := fibreMap ψ A g hpb.w
  haveI : IsMonHom ψk := fibreMap_isMonHom ψ e hη A g hpb.w hone
  have hk : ψk.left.base a1 = ψk.left.base a2 := by
    apply hs
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, fibreMap_fst, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, h12]
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback a1 a2 hk
  let q0 := (pullback ψk.left ψk.left).fromSpecResidueField z
  let xb := q0 ≫ pullback.fst ψk.left ψk.left
  let yb := q0 ≫ pullback.snd ψk.left ψk.left
  have hxy : xb ≫ ψk.left = yb ≫ ψk.left := by
    simp only [xb, yb, Category.assoc, pullback.condition]
  have hyx : yb ≫ A.X.hom = xb ≫ A.X.hom := by
    rw [← fibreMap_hom ψ A g hpb.w, ← Category.assoc, ← hxy, Category.assoc, fibreMap_hom]
  let T : Over (Spec (CommRingCat.of k)) := Over.mk (xb ≫ A.X.hom)
  let x' : T ⟶ A.X := Over.homMk xb rfl
  let y' : T ⟶ A.X := Over.homMk yb hyx
  have hxy' : x' ≫ ψk = y' ≫ ψk := by ext1; exact hxy
  let c : T ⟶ A.X := y' * x'⁻¹
  have hc : c ≫ ψk = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, ← hxy', mul_inv_cancel]
  let σ : T ⊗ A.X ⟶ A.X := (fst T A.X ≫ c) * snd T A.X
  have hσψ : σ ≫ ψk = snd T A.X ≫ ψk := by
    rw [MonObj.mul_comp, Category.assoc, hc, MonObj.comp_one, _root_.one_mul]
  let j : T ⊗ A.X ⟶ T ⊗ A.X := lift (fst T A.X) ((fst T A.X ≫ c⁻¹) * snd T A.X)
  have hjσ : j ≫ σ = snd T A.X := by
    simp only [σ, j, MonObj.comp_mul, lift_fst_assoc, lift_snd, GrpObj.comp_inv]
    exact mul_inv_cancel_left _ _
  -- surjectivity of the translations
  haveI : Subsingleton (Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : Surjective T.hom := ⟨fun y => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have hsnd : Function.Surjective (snd T A.X).left.base := by
    rw [Over.snd_left]; exact (pullback.snd T.hom A.X.hom).surjective
  have hσs : Function.Surjective σ.left.base := by
    have : (j ≫ σ).left.base = σ.left.base ∘ j.left.base := by
      rw [Over.comp_left, Scheme.Hom.comp_base]; rfl
    refine Function.Surjective.of_comp (g := j.left.base) ?_
    rw [← this, hjσ]; exact hsnd
  obtain ⟨a0, ha0⟩ := hW
  obtain ⟨y1, hy1⟩ := hσs a0
  obtain ⟨y2, hy2⟩ := hsnd a0
  let W : A.X.left.Opens := g ⁻¹ᵁ (ψ.left ⁻¹ᵁ V)
  haveI : GeometricallyIrreducible A.X.hom := inferInstance
  haveI : UniversallyOpen A.X.hom := inferInstance
  haveI : IrreducibleSpace T.left := by
    change IrreducibleSpace (PrimeSpectrum ((pullback ψk.left ψk.left).residueField z)); infer_instance
  haveI : IrreducibleSpace (T ⊗ A.X).left := by
    change IrreducibleSpace ((pullback T.hom A.X.hom : Scheme) : Type); infer_instance
  obtain ⟨q, hq1, hq2⟩ := nonempty_preirreducible_inter (σ.left ⁻¹ᵁ W).isOpen ((snd T A.X).left ⁻¹ᵁ W).isOpen
    ⟨y1, by show ψ.left.base (g.base (σ.left.base y1)) ∈ V; rw [hy1]; exact ha0⟩
    ⟨y2, by show ψ.left.base (g.base ((snd T A.X).left.base y2)) ∈ V; rw [hy2]; exact ha0⟩
  have hq1' : ψ.left.base (g.base (σ.left.base q)) ∈ V := hq1
  have hq2' : ψ.left.base (g.base ((snd T A.X).left.base q)) ∈ V := hq2
  let qb := (T ⊗ A.X).left.fromSpecResidueField q
  let a := qb ≫ σ.left
  let b := qb ≫ (snd T A.X).left
  have hab : a ≫ g = b ≫ g := by
    refine eq_of_comp_eq ψ V v hB2 _ _ ?_ ?_ ?_
    · intro x; simp only [a, qb, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hq1'
    · intro x; simp only [b, qb, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hq2'
    · have h3 : σ.left ≫ ψk.left = (snd T A.X).left ≫ ψk.left := by
        rw [← Over.comp_left, hσψ, Over.comp_left]
      simp only [a, b, Category.assoc]
      rw [← fibreMap_fst ψ A g hpb.w, reassoc_of% h3]
  have hab' : a = b := by
    refine hpb.hom_ext hab ?_
    simp only [a, b, Category.assoc, Over.w]
  let Q : Over (Spec (CommRingCat.of k)) := Over.mk (qb ≫ (T ⊗ A.X).hom)
  let q' : Q ⟶ T ⊗ A.X := Over.homMk qb rfl
  have hq' : q' ≫ σ = q' ≫ snd T A.X := by ext1; exact hab'
  have hc1 : (q' ≫ fst T A.X) ≫ c = 1 := by
    have := hq'
    rw [MonObj.comp_mul, ← Category.assoc] at this
    exact mul_eq_right.mp this
  have hc2 : (q' ≫ fst T A.X) ≫ y' = (q' ≫ fst T A.X) ≫ x' := by
    rw [MonObj.comp_mul, GrpObj.comp_inv] at hc1
    exact mul_inv_eq_one.mp hc1
  have := congrArg (fun f => f.base (IsLocalRing.closedPoint _)) (congrArg Over.Hom.left hc2)
  simp only [Over.comp_left, x', y', Over.homMk_left, xb, yb, q0, Scheme.Hom.comp_base, TopCat.coe_comp] at this
  dsimp only [Function.comp] at this
  rw [Scheme.fromSpecResidueField_apply, hz1, hz2] at this
  exact this.symm

/-- **The group case.** `F` as in `NeronGoodModelIso`, `N` smooth, separated, quasi-compact with a group law
whose identity is `e ≫ ψ`; if `ψ` is an isomorphism on generic fibres, it is an isomorphism. -/
theorem isIso_of_grp (F N : Over (Spec (CommRingCat.of R))) (e : Spec (CommRingCat.of R) ⟶ F.left)
    [IsProper F.hom] [Smooth F.hom] (he : e ≫ F.hom = 𝟙 _)
    (hfib : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      ∃ (A : PkgI3.AbVar K) (g : A.X.left ⟶ F.left), LeafQM.AV.R1UnivRigid.IsAbVarFibre F e s A g)
    [Smooth N.hom] [IsSeparated N.hom] [QuasiCompact N.hom] [GrpObj N] (ψ : F ⟶ N)
    (hη : e ≫ ψ.left = η[N].left)
    (hK : IsIso ((Over.pullback (genMap R (FractionRing R))).map ψ)) : IsIso ψ := by
  obtain ⟨V, v, hv, hVη, hVs, hB1, hB2⟩ := exists_inverse_open F N ψ hK
  have hψN : ψ.left ≫ N.hom = F.hom := Over.w ψ
  have hB1pt : ∀ r, ψ.left.base (v.base r) = V.ι.base r := fun r => by
    rw [← Scheme.Hom.comp_apply, hB1]
  have hψpt : ∀ x, N.hom.base (ψ.left.base x) = F.hom.base x := fun x => by
    rw [← Scheme.Hom.comp_apply, hψN]
  haveI : IsProper ψ.left := by
    haveI : IsProper (ψ.left ≫ N.hom) := by rw [hψN]; infer_instance
    exact IsProper.of_comp ψ.left N.hom
  refine isIso_of_injective F N ψ V v hv hVη hVs hB1 hB2 ?_
  -- the special fibre
  let k := IsLocalRing.ResidueField R
  obtain ⟨A, g, hpb, hone⟩ := hfib k (resMap R)
  have hs : Function.Injective (pullback.fst N.hom (resMap R)).base := by
    haveI : IsClosedImmersion (resMap R) :=
      IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective)
    exact (pullback.fst N.hom (resMap R)).isEmbedding.injective
  have hlift : ∀ x : F.left, F.hom.base x = IsLocalRing.closedPoint R → ∃ a, g.base a = x := by
    intro x hx
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := F.hom) (g := resMap R) x
      (IsLocalRing.closedPoint _) (by rw [hx]; exact (resMap_apply _).symm)
    exact ⟨hpb.isoPullback.inv.base z, by rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz1]⟩
  -- a point of the special fibre mapping into `V`
  have hW : ∃ a0 : A.X.left, ψ.left.base (g.base a0) ∈ V := by
    let n0 : {x : N.left // N.hom.base x = IsLocalRing.closedPoint R} :=
      ⟨η[N].left.base (IsLocalRing.closedPoint R), by
        have := congrArg (fun f => f.base (IsLocalRing.closedPoint R)) (Over.w η[N])
        exact this.trans rfl⟩
    obtain ⟨Z, hZ, hnZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {n0}
      isIrreducible_singleton
    obtain ⟨n, -, hnV⟩ := hVs Z hZ
    -- `n` is in the closure of the generic fibre, hence in the closed image of `ψ`
    have hcl : n.1 ∈ closure (Set.range ψ.left.base) := by
      rw [mem_closure_iff]
      intro o ho hno
      have hopen : IsOpen (N.hom.base '' o) := N.hom.isOpenMap _ ho
      let t0 : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint _
      have hgen : (genMap R (FractionRing R)).base t0 ∈ N.hom.base '' o :=
        (IsLocalRing.specializes_closedPoint _).mem_open hopen ⟨n.1, hno, n.2⟩
      obtain ⟨n', hn'o, hn'⟩ := hgen
      have hn'V : n' ∈ V := hVη n' (by rw [hn']; exact genMap_ne_closedPoint _ _)
      exact ⟨n', hn'o, ⟨v.base ⟨n', hn'V⟩, (hB1pt ⟨n', hn'V⟩).trans rfl⟩⟩
    rw [ψ.left.isClosedMap.isClosed_range.closure_eq] at hcl
    obtain ⟨x, hx⟩ := hcl
    obtain ⟨a0, ha0⟩ := hlift x (by rw [← hψpt, hx]; exact n.2)
    exact ⟨a0, by rw [ha0, hx]; exact hnV⟩
  intro x1 x2 h12
  by_cases hc : F.hom.base x1 = IsLocalRing.closedPoint R
  · have hc2 : F.hom.base x2 = IsLocalRing.closedPoint R := by rw [← hψpt, ← h12, hψpt, hc]
    obtain ⟨a1, rfl⟩ := hlift x1 hc
    obtain ⟨a2, rfl⟩ := hlift x2 hc2
    rw [fibre_injective ψ e hη A g hpb hone hs V v hB2 hW a1 a2 h12]
  · -- the generic fibre: `v` inverts `ψ`
    have hc2 : F.hom.base x2 ≠ IsLocalRing.closedPoint R := by rwa [← hψpt, ← h12, hψpt]
    have m1 : x1 ∈ ψ.left ⁻¹ᵁ V := hVη _ (by rwa [hψpt])
    have m2 : x2 ∈ ψ.left ⁻¹ᵁ V := hVη _ (by rwa [hψpt])
    obtain ⟨y1, hy1⟩ : x1 ∈ Set.range (ψ.left ⁻¹ᵁ V).ι.base := by rw [Scheme.Opens.range_ι]; exact m1
    obtain ⟨y2, hy2⟩ : x2 ∈ Set.range (ψ.left ⁻¹ᵁ V).ι.base := by rw [Scheme.Opens.range_ι]; exact m2
    have key : ∀ y, v.base ((ψ.left ∣_ V).base y) = (ψ.left ⁻¹ᵁ V).ι.base y :=
      fun y => by rw [← Scheme.Hom.comp_apply, hB2]
    have hpt : ∀ y, V.ι.base ((ψ.left ∣_ V).base y) = ψ.left.base ((ψ.left ⁻¹ᵁ V).ι.base y) := fun y => by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    have hr : (ψ.left ∣_ V).base y1 = (ψ.left ∣_ V).base y2 :=
      V.ι.injective (by rw [hpt, hpt, hy1, hy2, h12])
    rw [← hy1, ← hy2, ← key, ← key, hr]

/-- **`NeronGoodModelIso` from BLR 1.4 Thm 3 over a DVR.** Compose `ψ` with the extension `χ : N → N'` of the
generic identification into the Néron model `N'` of the generic fibre; `ψ ≫ χ` is an isomorphism by the group case
(`isIso_of_grp`), so `ψ` has a left inverse, which is also a right inverse by density of the generic fibre. -/
theorem neronGoodModelIso_of_dvr (hN : NeronSchemeExtensionDVR) : NeronGoodModelIso := by
  intro R _ _ _ F N e hP hS hGC he hfib hNS hNsep ψ hK
  haveI := hP; haveI := hS; haveI := hNS; haveI := hNsep
  let K := FractionRing R
  let s0 := genMap R K
  haveI := genMap_isSchemeTheoreticallyDominant (R := R) K
  obtain ⟨A, g, hpb, hone⟩ := hfib K s0
  obtain ⟨N', hN'S, hN'sep, hN'qc, ε, hext⟩ := hN R K A
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

/-- **`NeronGoodModelIso` from the Dedekind form of BLR 1.4 Thm 3.** -/
theorem neronGoodModelIso_of_dedekind (hN : NeronSchemeExtensionDedekind) : NeronGoodModelIso :=
  neronGoodModelIso_of_dvr (dvr_of_dedekind hN)

/-- **GIT Thm 6.14 over a DVR from BLR 1.4 Thm 3 alone.** -/
theorem mumfordGroupLawDVR_of_dedekind (hN : NeronSchemeExtensionDedekind) :
    ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR :=
  mumfordGroupLawDVR_of_neron (dvr_of_dedekind hN) (neronGoodModelIso_of_dedekind hN)

end ZInQ.Contrib.GoodModelIso

#print axioms ZInQ.Contrib.GoodModelIso.neronGoodModelIso_of_dvr
#print axioms ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind
