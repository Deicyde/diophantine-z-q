import ZInQKernel.Contrib.OneProof.JavanpeykarFix.Basic

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace JavanpeykarFix

open CategoryTheory AlgebraicGeometry Limits

attribute [local instance] MvPolynomial.gradedAlgebra

section Chart

variable (k : Type) [Field k]

/-- The coordinate ring `k[s]` of the chart `D₊(X₁) ⊆ ℙ¹` (`s = X₀/X₁`). -/
abbrev Rk : Type := MvPolynomial {i : Fin 2 // i ≠ 1} k

/-- The index of `s = X₀/X₁`. -/
def i0 : {i : Fin 2 // i ≠ 1} := ⟨0, by decide⟩

instance : Unique {i : Fin 2 // i ≠ 1} where
  default := i0
  uniq := fun ⟨i, hi⟩ => by
    apply Subtype.ext
    show i = 0
    fin_cases i
    · rfl
    · exact absurd rfl hi

/-- The chart `Spec k[s] ≅ D₊(X₁) ⊆ ℙ¹` (vendored `Proj.standardOpenIso`). -/
def chart : Spec (CommRingCat.of (Rk k)) ⟶ P1 k :=
  (Proj.standardOpenIso (Fin 2) k 1).inv ≫
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 1)).ι

instance : IsOpenImmersion (chart k) := by unfold chart; infer_instance

theorem chart_toSpec : chart k ≫ P1.toSpec k =
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* Rk k)) :=
  Proj.standardOpenIso_inv_over (Fin 2) k 1

end Chart

section Construction

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]

/-- `Spec k(C) → C → Spec k` is `Spec` of the structure map `k → k(C)`. -/
theorem fromSpecFunctionField_hom :
    C.left.fromSpecFunctionField ≫ C.hom =
      Spec.map (CommRingCat.ofHom (ZInQ.LeafPush2.ffStructMap C)) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, ← cancel_epi (Scheme.ΓSpecIso _).inv]
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecFunctionField,
    Scheme.fromSpecStalk_appTop, ZInQ.LeafPush2.ffStructMap, Scheme.germToFunctionField,
    Category.assoc, Iso.inv_hom_id_assoc]
  ext c
  simp

end Construction


section Points

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]

/-- **On a smooth proper integral curve every point other than the generic point is closed.**
(A non-closed `x ≠ η` specializes to a closed `z ≠ x`, giving `z < x < η` and `dim 𝒪_z ≥ 2`; but
`dim 𝒪_z = 1`, vendored `ringKrullDim_stalk_eq_one_of_isClosed`.) -/
theorem isClosed_of_ne_genericPoint (x : C.left) (hx : x ≠ genericPoint C.left) :
    IsClosed ({x} : Set C.left) := by
  have : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  obtain ⟨z, hzS, hz⟩ := (isClosed_closure : IsClosed (closure ({x} : Set C.left))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  by_cases hzx : z = x
  · subst hzx; exact hz
  exfalso
  have hxz : x ⤳ z := specializes_iff_mem_closure.mpr hzS
  have h1 : z < x := ⟨hxz, fun h => hzx (h.antisymm hxz).eq⟩
  have hηx : genericPoint C.left ⤳ x := (genericPoint_spec C.left).specializes (Set.mem_univ x)
  have h2 : x < genericPoint C.left := ⟨hηx, fun h => hx (h.antisymm hηx).eq⟩
  have c1 := Order.coheight_add_one_le h1
  have c2 := Order.coheight_add_one_le h2
  have hz1 := Scheme.ringKrullDim_stalk_eq_one_of_isClosed C.hom hz
  rw [ringKrullDim_stalk_eq_coheight] at hz1
  have hz1' : Order.coheight z = 1 := by exact_mod_cast hz1
  have : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (genericPoint C.left) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight x + 1 := by gcongr
      _ ≤ Order.coheight z := c1
      _ = 1 := hz1'
  exact absurd this (by decide)

/-- **A closed subset of the curve not containing the generic point is finite.** -/
theorem finite_of_isClosed_of_genericPoint_notMem (Z : Set C.left) (hZ : IsClosed Z)
    (hη : genericPoint C.left ∉ Z) : Z.Finite := by
  have : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  have : IsLocallyNoetherian C.left := LocallyOfFiniteType.isLocallyNoetherian C.hom
  have : IsNoetherian C.left := {}
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSf.sUnion fun T hT => ?_
  have hgen := (hSi T hT).isGenericPoint_genericPoint_closure
  rw [(hSc T hT).closure_eq] at hgen
  have hmem : (hSi T hT).genericPoint ∈ T := hgen.mem
  have hne : (hSi T hT).genericPoint ≠ genericPoint C.left := fun h =>
    hη ⟨T, hT, h ▸ hmem⟩
  have hcl := isClosed_of_ne_genericPoint C _ hne
  rw [← hgen.def, hcl.closure_eq]
  exact Set.finite_singleton _

end Points


section Extension

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
  (t : C.left.functionField)

/-- `ψ_t : k[s] → k(C)`, `s ↦ t`. -/
def psi : CommRingCat.of (Rk k) ⟶ C.left.functionField :=
  letI := ZInQ.LeafPush2.ffAlgebra C
  CommRingCat.ofHom (MvPolynomial.aeval (fun _ => t)).toRingHom

theorem psi_C (c : k) : psi C t (MvPolynomial.C c) = ZInQ.LeafPush2.ffStructMap C c := by
  letI := ZInQ.LeafPush2.ffAlgebra C
  show MvPolynomial.aeval (fun _ => t) (MvPolynomial.C c) = _
  rw [MvPolynomial.aeval_C]; rfl

theorem psi_X : psi C t (MvPolynomial.X i0) = t := by
  letI := ZInQ.LeafPush2.ffAlgebra C
  show MvPolynomial.aeval (fun _ => t) (MvPolynomial.X i0) = _
  rw [MvPolynomial.aeval_X]

theorem psi_injective (ht : letI := ZInQ.LeafPush2.ffAlgebra C; Transcendental k t) :
    Function.Injective (psi C t) := by
  letI := ZInQ.LeafPush2.ffAlgebra C
  have : AlgebraicIndependent k (fun _ : {i : Fin 2 // i ≠ 1} => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  exact this

/-- The point `[t : 1] : Spec k(C) → ℙ¹_k`. -/
def ptT : Spec C.left.functionField ⟶ P1 k :=
  Spec.map (psi C t) ≫ chart k

theorem ptT_toSpec : ptT C t ≫ P1.toSpec k = C.left.fromSpecFunctionField ≫ C.hom := by
  rw [fromSpecFunctionField_hom, ptT, Category.assoc, chart_toSpec, ← Spec.map_comp]
  congr 1
  ext c
  exact psi_C C t c

instance P1.over : (P1 k).Over (Spec (CommRingCat.of k)) := ⟨P1.toSpec k⟩

instance : IsProper (P1 k ↘ Spec (CommRingCat.of k)) :=
  inferInstanceAs (IsProper (Proj.projectiveSpaceOverAffineToSpec (Fin 2) k))

instance : (P1 k).IsSeparated := by
  constructor
  rw [show terminal.from (P1 k) = P1.toSpec k ≫ terminal.from _ from terminal.hom_ext _ _]
  have : IsSeparated (P1.toSpec k) := inferInstanceAs (IsSeparated (P1 k ↘ Spec (CommRingCat.of k)))
  infer_instance

/-- **The morphism `β : C → ℙ¹` defined by `t`** (vendored valuative extension of rational maps,
Hartshorne I.6.8). -/
theorem exists_extension [SmoothOfRelativeDimension 1 C.hom] :
    ∃ β : C.left ⟶ P1 k, β ≫ P1.toSpec k = C.hom ∧ C.left.fromSpecFunctionField ≫ β = ptT C t := by
  letI : C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩
  have hval : ∀ x : C.left, ValuationRing (C.left.presheaf.stalk x) := fun x =>
    Scheme.valuationRing_stalk C.hom x
  obtain ⟨β, hβo, hβ⟩ := Scheme.exists_hom_of_valuationRing_stalk
    (base := Spec (CommRingCat.of k)) hval (ptT C t) (ptT_toSpec C t)
  exact ⟨β, hβo.comp_over, hβ⟩

end Extension


section Finite

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] (t : C.left.functionField)

theorem beta_genericPoint {β : C.left ⟶ P1 k} (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t) :
    β (genericPoint C.left) = chart k (Spec.map (psi C t)
      (IsLocalRing.closedPoint (C.left.presheaf.stalk (genericPoint C.left)))) := by
  have h := congrArg (fun f : Spec C.left.functionField ⟶ P1 k =>
    f (IsLocalRing.closedPoint (C.left.presheaf.stalk (genericPoint C.left)))) hβ
  simp only [ptT, Scheme.fromSpecFunctionField] at h
  exact (congrArg β (Scheme.fromSpecStalk_closedPoint (x := genericPoint C.left))).symm.trans h

theorem not_isUnit_X : ¬ IsUnit (MvPolynomial.X i0 : Rk k) := by
  intro h
  have := h.map (MvPolynomial.eval (fun _ => (0 : k)))
  simp at this

theorem not_isClosed_beta_genericPoint (ht : letI := ZInQ.LeafPush2.ffAlgebra C; Transcendental k t)
    {β : C.left ⟶ P1 k} (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t) :
    ¬ IsClosed ({β (genericPoint C.left)} : Set (P1 k)) := by
  rw [beta_genericPoint C t hβ]
  intro hcl
  set z₀ := Spec.map (psi C t)
    (IsLocalRing.closedPoint (C.left.presheaf.stalk (genericPoint C.left)))
  have h1 : IsClosed ({z₀} : Set (Spec (CommRingCat.of (Rk k)))) := by
    have := hcl.preimage (chart k).continuous
    have he : (chart k) ⁻¹' {chart k z₀} = {z₀} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact (chart k).isOpenEmbedding.injective.eq_iff
    rwa [he] at this
  have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z₀).mp h1
  have hbot : z₀.asIdeal = ⊥ := by
    show Ideal.comap (psi C t).hom (IsLocalRing.maximalIdeal _) = ⊥
    ext a
    simp only [Ideal.mem_comap, Ideal.mem_bot, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro h
      by_contra ha
      apply h
      have : (psi C t) a ≠ 0 := fun h0 => ha (psi_injective C t ht (h0.trans (map_zero _).symm))
      exact (show IsUnit ((psi C t) a : C.left.functionField) from isUnit_iff_ne_zero.mpr this)
    · rintro rfl
      rw [map_zero]
      exact not_isUnit_zero
  rw [hbot] at hmax
  have hfield : IsField (Rk k) := Ring.isField_iff_maximal_bot.mpr hmax
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel (MvPolynomial.X_ne_zero i0)
  exact not_isUnit_X (IsUnit.of_mul_eq_one b hb)

theorem finite_fibre (ht : letI := ZInQ.LeafPush2.ffAlgebra C; Transcendental k t)
    {β : C.left ⟶ P1 k} (hβo : β ≫ P1.toSpec k = C.hom)
    (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t) (y : P1 k) : (β ⁻¹' {y}).Finite := by
  have : IsProper (β ≫ P1.toSpec k) := hβo ▸ inferInstance
  have : IsSeparated (P1.toSpec k) :=
    inferInstanceAs (IsSeparated (P1 k ↘ Spec (CommRingCat.of k)))
  have : IsProper β := IsProper.of_comp β (P1.toSpec k)
  have hcm : IsClosedMap β := β.isClosedMap
  by_cases hη : β (genericPoint C.left) = y
  · apply (Set.finite_singleton (genericPoint C.left)).subset
    intro x hx
    by_contra hne
    have h2 := hcm _ (isClosed_of_ne_genericPoint C x hne)
    rw [Set.image_singleton, show β x = y from hx, ← hη] at h2
    exact not_isClosed_beta_genericPoint C t ht hβ h2
  · by_cases hne : (β ⁻¹' {y}).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxη : x ≠ genericPoint C.left := fun h => hη (h ▸ hx)
      have hycl : IsClosed ({y} : Set (P1 k)) := by
        have := hcm _ (isClosed_of_ne_genericPoint C x hxη)
        rwa [Set.image_singleton, show β x = y from hx] at this
      exact finite_of_isClosed_of_genericPoint_notMem C _ (hycl.preimage β.continuous) hη
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty

/-- **`β` is finite** (proper with finite fibres, Mathlib `IsFinite.of_isProper_of_locallyQuasiFinite`). -/
theorem isFinite_beta (ht : letI := ZInQ.LeafPush2.ffAlgebra C; Transcendental k t)
    {β : C.left ⟶ P1 k} (hβo : β ≫ P1.toSpec k = C.hom)
    (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t) : IsFinite β := by
  have : IsProper (β ≫ P1.toSpec k) := hβo ▸ inferInstance
  have : IsSeparated (P1.toSpec k) :=
    inferInstanceAs (IsSeparated (P1 k ↘ Spec (CommRingCat.of k)))
  have : IsProper β := IsProper.of_comp β (P1.toSpec k)
  have : LocallyOfFiniteType (β ≫ P1.toSpec k) := hβo ▸ inferInstance
  have : LocallyOfFiniteType β := locallyOfFiniteType_of_comp β (P1.toSpec k)
  have : LocallyQuasiFinite β :=
    LocallyQuasiFinite.of_finite_preimage_singleton β (finite_fibre C t ht hβo hβ)
  exact IsFinite.of_isProper_of_locallyQuasiFinite β

end Finite


section ChartOpens

variable (k : Type) [Field k]

theorem opensRange_chart : (chart k).opensRange =
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 1) := by
  unfold chart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

theorem chart_mem_basicOpen_X0 (z : Spec (CommRingCat.of (Rk k))) :
    chart k z ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 0) ↔
      (MvPolynomial.X i0 : Rk k) ∉ z.asIdeal := by
  rw [show chart k = _ from Proj.standardOpenIso_inv_ι (Fin 2) k 1, Scheme.Hom.comp_apply]
  have key := Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.X_mem_homogeneousSubmodule_one k 1) Nat.one_pos
    (MvPolynomial.X_mem_homogeneousSubmodule_one k 0) Nat.one_pos
  rw [← SetLike.mem_coe, ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe, key]
  erw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, Spec.map_apply, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]
  erw [MvPolynomial.homogeneousLocalizationAwayXEquiv_awayMk]
  simp only [pow_one, MvPolynomial.dehomogenizeX, MvPolynomial.aeval_X]
  simp [i0]

theorem chart_mem_basicOpen_X0_sub_X1 (z : Spec (CommRingCat.of (Rk k))) :
    chart k z ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.X 0 - MvPolynomial.X 1) ↔ (MvPolynomial.X i0 - 1 : Rk k) ∉ z.asIdeal := by
  rw [show chart k = _ from Proj.standardOpenIso_inv_ι (Fin 2) k 1, Scheme.Hom.comp_apply]
  have key := Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.X_mem_homogeneousSubmodule_one k 1) Nat.one_pos
    (Submodule.sub_mem _
      (MvPolynomial.X_mem_homogeneousSubmodule_one k 0) (MvPolynomial.X_mem_homogeneousSubmodule_one k 1)) Nat.one_pos
  rw [← SetLike.mem_coe, ← Set.mem_preimage, ← TopologicalSpace.Opens.map_coe, key]
  erw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, Spec.map_apply, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]
  erw [MvPolynomial.homogeneousLocalizationAwayXEquiv_awayMk]
  simp only [pow_one, MvPolynomial.dehomogenizeX, MvPolynomial.aeval_X, map_sub]
  simp [i0]

end ChartOpens


section MainIdentity

variable {k : Type} [Field k]

/-- The section of `ℙ¹` over the chart `D₊(X₁)` given by `r ∈ k[s]`. -/
def secR : CommRingCat.of (Rk k) ⟶ Γ(P1 k, (chart k) ''ᵁ ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ ((chart k).appIso ⊤).inv

variable (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left] (t : C.left.functionField)

theorem fromSpecStalk_appLE_top (X : Scheme) (x : X) (V : X.Opens) (hV : x ∈ V)
    (e : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ V) (τ : Γ(X, V)) :
    (X.fromSpecStalk x).appLE V ⊤ e τ = (Scheme.ΓSpecIso _).inv (X.presheaf.germ V x hV τ) := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hV]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  have : (homOfLE (le_top : X.fromSpecStalk x ⁻¹ᵁ V ≤ ⊤)).op ≫ (homOfLE e).op = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

/-- Germs at the generic point through `Spec k(C) → C`. -/
theorem germ_app_eq {Y : Scheme} (f : C.left ⟶ Y) (U : Y.Opens) (h : f (genericPoint C.left) ∈ U)
    (σ : Γ(Y, U)) (e : ⊤ ≤ (C.left.fromSpecFunctionField ≫ f) ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso _).inv (C.left.presheaf.germ (f ⁻¹ᵁ U) (genericPoint C.left) h (f.app U σ)) =
      (C.left.fromSpecFunctionField ≫ f).appLE U ⊤ e σ := by
  rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  exact (fromSpecStalk_appLE_top C.left _ _ h _ _).symm

theorem appLE_top_top {R S : CommRingCat} (φ : R ⟶ S) (e : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤) (a : Γ(Spec R, ⊤)) :
    (Spec.map φ).appLE ⊤ ⊤ e a = (Spec.map φ).appTop a := by
  rw [Scheme.Hom.appLE]
  have : (homOfLE e).op = (𝟙 (Opposite.op (⊤ : (Spec S).Opens)) : _) := Subsingleton.elim _ _
  rw [this]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The chart side: `(Spec φ ≫ chart)^*` of the section `r` is `φ(r)`. -/
theorem specMap_chart_appLE_secR {S : CommRingCat} (φ : CommRingCat.of (Rk k) ⟶ S) (r : Rk k)
    (e : ⊤ ≤ (Spec.map φ ≫ chart k) ⁻¹ᵁ ((chart k) ''ᵁ ⊤)) :
    (Spec.map φ ≫ chart k).appLE ((chart k) ''ᵁ ⊤) ⊤ e (secR r) = (Scheme.ΓSpecIso _).inv (φ r) := by
  rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, secR, CommRingCat.comp_apply,
    Scheme.Hom.appIso_inv_app_apply, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.map_appLE]
  rw [appLE_top_top, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]

/-- **Main identity.** For `x ∈ C` with `β(x)` in the chart, the germ at `β(x)` of the section `r`,
pulled back by `β` and specialized to the generic point, is `ψ_t(r)`. -/
theorem stalkMap_secR {β : C.left ⟶ P1 k} (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t)
    (x : C.left) (hx : β x ∈ (chart k) ''ᵁ ⊤) (r : Rk k) :
    C.left.presheaf.stalkSpecializes ((genericPoint_spec C.left).specializes (Set.mem_univ x))
      (β.stalkMap x ((P1 k).presheaf.germ _ (β x) hx (secR r))) = psi C t r := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hη : β (genericPoint C.left) ∈ (chart k) ''ᵁ ⊤ :=
    ((genericPoint_spec C.left).specializes (Set.mem_univ x)).map β.continuous |>.mem_open
      ((chart k) ''ᵁ ⊤).isOpen hx
  have e : ⊤ ≤ (C.left.fromSpecFunctionField ≫ β) ⁻¹ᵁ ((chart k) ''ᵁ ⊤) := by
    intro p _
    have hp : C.left.fromSpecFunctionField p ⤳ genericPoint C.left := by
      have : C.left.fromSpecFunctionField p ∈ Set.range C.left.fromSpecFunctionField := ⟨p, rfl⟩
      rw [Scheme.fromSpecFunctionField, Scheme.range_fromSpecStalk] at this
      exact this
    have heq : C.left.fromSpecFunctionField p = genericPoint C.left :=
      (hp.antisymm ((genericPoint_spec C.left).specializes (Set.mem_univ _))).eq
    show β (C.left.fromSpecFunctionField p) ∈ ((chart k) ''ᵁ ⊤ : (P1 k).Opens)
    rw [heq]
    exact hη
  have key := germ_app_eq C β _ hη (secR r) e
  have h2 : ∀ (g : Spec C.left.functionField ⟶ P1 k) (hg : g = ptT C t)
      (e' : ⊤ ≤ g ⁻¹ᵁ ((chart k) ''ᵁ ⊤)),
      g.appLE ((chart k) ''ᵁ ⊤) ⊤ e' (secR r) = (Scheme.ΓSpecIso _).inv (psi C t r) := by
    rintro g rfl e'
    exact specMap_chart_appLE_secR (psi C t) r e'
  rw [h2 _ hβ e] at key
  have := congrArg (Scheme.ΓSpecIso C.left.functionField).hom key
  simpa using this

end MainIdentity


section Unramified

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]

/-- The structure map `k → 𝒪_{C,x}`. -/
def iotaX (x : C.left) : CommRingCat.of k ⟶ C.left.presheaf.stalk x :=
  (Scheme.ΓSpecIso _).inv ≫ C.hom.appTop ≫ C.left.presheaf.germ ⊤ x trivial

theorem fromSpecStalk_hom (x : C.left) :
    C.left.fromSpecStalk x ≫ C.hom = Spec.map (iotaX C x) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality,
    ← cancel_epi (Scheme.ΓSpecIso _).inv]
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, iotaX, Category.assoc,
    Iso.inv_hom_id_assoc]
  ext c
  simp

theorem algebraMap_iotaX (x : C.left) (c : k) :
    algebraMap (C.left.presheaf.stalk x) C.left.functionField (iotaX C x c) =
      ZInQ.LeafPush2.ffStructMap C c := by
  simp only [iotaX, ZInQ.LeafPush2.ffStructMap, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [Scheme.algebraMap_germ_eq_germToFunctionField]

/-- **The residue field of a closed point is `k`** (Mathlib `residueFieldIsoBase`, `k` algebraically
closed): every `b ∈ 𝒪_{C,x}` is congruent to a constant mod `𝔪_x`. -/
theorem exists_sub_const_mem [IsAlgClosed k] [LocallyOfFiniteType C.hom] (x : C.left)
    (hx : IsClosed ({x} : Set C.left)) (b : C.left.presheaf.stalk x) :
    ∃ c : k, b - iotaX C x c ∈ IsLocalRing.maximalIdeal (C.left.presheaf.stalk x) := by
  set e := residueFieldIsoBase C.hom x hx
  have hφ : e.inv = iotaX C x ≫ C.left.residue x := by
    apply Spec.map_injective
    rw [SpecMap_residueFieldIsoBase_inv, Spec.map_comp, Scheme.fromSpecResidueField,
      Category.assoc, fromSpecStalk_hom]
  refine ⟨e.hom (C.left.residue x b), ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  have : C.left.residue x (iotaX C x (e.hom (C.left.residue x b))) = C.left.residue x b := by
    rw [← CommRingCat.comp_apply, ← hφ, ← CommRingCat.comp_apply, e.hom_inv_id]
    rfl
  rw [map_sub]; exact sub_eq_zero.mpr this.symm


/-- The valuation subring `𝒪_{C,x} ⊆ k(C)`. -/
def wOf [SmoothOfRelativeDimension 1 C.hom] (x : C.left) : ValuationSubring C.left.functionField where
  toSubring := (algebraMap (C.left.presheaf.stalk x) C.left.functionField).range
  mem_or_inv_mem' a := by
    have : ValuationRing (C.left.presheaf.stalk x) := Scheme.valuationRing_stalk C.hom x
    rcases ValuationRing.isInteger_or_isInteger (C.left.presheaf.stalk x) a with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨b, hb⟩
    · exact Or.inr ⟨b, hb⟩

theorem mem_wOf [SmoothOfRelativeDimension 1 C.hom] (x : C.left) (u : C.left.presheaf.stalk x) :
    algebraMap _ C.left.functionField u ∈ wOf C x := ⟨u, rfl⟩

theorem algebraMap_mem_nonunits_iff [SmoothOfRelativeDimension 1 C.hom] (x : C.left)
    (u : C.left.presheaf.stalk x) :
    algebraMap _ C.left.functionField u ∈ (wOf C x).nonunits ↔
      u ∈ IsLocalRing.maximalIdeal (C.left.presheaf.stalk x) := by
  set γ := algebraMap (C.left.presheaf.stalk x) C.left.functionField
  have hinj : Function.Injective γ := IsFractionRing.injective _ _
  let e : C.left.presheaf.stalk x ≃+* wOf C x :=
    RingEquiv.ofBijective (γ.codRestrict (wOf C x).toSubring (fun u => mem_wOf C x u))
      ⟨fun a b h => hinj (congrArg Subtype.val h), fun ⟨a, ⟨b, hb⟩⟩ => ⟨b, Subtype.ext hb⟩⟩
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨_, h⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
    intro hu
    exact h (hu.map e)
  · intro h
    refine ⟨mem_wOf C x u, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
    intro hu
    apply h
    have : e u = ⟨γ u, mem_wOf C x u⟩ := rfl
    rw [← this] at hu
    simpa using hu.map e.symm

end Unramified

section SecR

variable {k : Type} [Field k]

theorem basicOpen_secR (r : Rk k) :
    (P1 k).basicOpen (secR r) =
      (chart k) ''ᵁ (Spec (CommRingCat.of (Rk k))).basicOpen ((Scheme.ΓSpecIso _).inv r) :=
  (Scheme.image_basicOpen (chart k) _).symm

theorem chart_mem_basicOpen_secR (r : Rk k) (z : Spec (CommRingCat.of (Rk k))) :
    chart k z ∈ (P1 k).basicOpen (secR r) ↔ r ∉ z.asIdeal := by
  rw [basicOpen_secR]
  have hb : z ∈ (Spec (CommRingCat.of (Rk k))).basicOpen ((Scheme.ΓSpecIso _).inv r) ↔
      r ∉ z.asIdeal := by
    rw [basicOpen_eq_of_affine]; rfl
  rw [← hb]
  constructor
  · rintro ⟨z', hz', h⟩
    rw [(chart k).isOpenEmbedding.injective h] at hz'
    exact hz'
  · intro h
    exact ⟨z, h, rfl⟩

end SecR


section Assembly

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] (t : C.left.functionField)

/-- **`β` is unramified at every closed point over `ℙ¹ ∖ {0, 1, ∞}`** (from the Belyi property of `t`
at the valuation ring `𝒪_{C,x}`). -/
theorem unramified [IsAlgClosed k]
    (hB : letI := ZInQ.LeafPush2.ffAlgebra C; LeafModCurves.IsBelyiFunction k C.left.functionField t)
    {β : C.left ⟶ P1 k} (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t)
    (x : C.left) (hx : IsClosed ({x} : Set C.left)) (hy : β x ∈ P1.threePointsCompl k) :
    Ideal.map (β.stalkMap x).hom (IsLocalRing.maximalIdeal ((P1 k).presheaf.stalk (β x))) =
      IsLocalRing.maximalIdeal (C.left.presheaf.stalk x) := by
  letI := ZInQ.LeafPush2.ffAlgebra C
  have hy' : β x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 0) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X 1) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X 0 - MvPolynomial.X 1) := by
    simpa only [P1.threePointsCompl, Proj.basicOpen_mul] using hy
  obtain ⟨⟨hy0, hy1⟩, hy01⟩ := hy'
  have hU : β x ∈ (chart k) ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, opensRange_chart]; exact hy1
  obtain ⟨z, -, hz0⟩ := id hU
  have hz : chart k z = β x := hz0
  let G : CommRingCat.of (Rk k) ⟶ (P1 k).presheaf.stalk (β x) :=
    secR ≫ (P1 k).presheaf.germ _ (β x) hU
  set ρ := (β.stalkMap x).hom
  set γ := algebraMap (C.left.presheaf.stalk x) C.left.functionField
  have hγinj : Function.Injective γ := IsFractionRing.injective _ _
  have hMI : ∀ r, γ (ρ (G r)) = psi C t r := fun r => stalkMap_secR C t hβ x hU r
  set b := ρ (G (MvPolynomial.X i0))
  have hb : γ b = t := (hMI _).trans (psi_X C t)
  obtain ⟨c, hc⟩ := exists_sub_const_mem C x hx b
  have hρC : ∀ c' : k, ρ (G (MvPolynomial.C c')) = iotaX C x c' := fun c' =>
    hγinj ((hMI _).trans ((psi_C C t c').trans (algebraMap_iotaX C x c').symm))
  -- local-hom facts
  have hloc : ∀ a, ρ a ∈ IsLocalRing.maximalIdeal (C.left.presheaf.stalk x) →
      a ∈ IsLocalRing.maximalIdeal ((P1 k).presheaf.stalk (β x)) := by
    intro a ha
    by_contra hna
    have hu : IsUnit a := by
      by_contra h'; exact hna ((IsLocalRing.mem_maximalIdeal _).mpr h')
    exact ((IsLocalRing.mem_maximalIdeal _).mp ha) (hu.map ρ)
  have hunit : ∀ r : Rk k, r ∉ z.asIdeal →
      ρ (G r) ∉ IsLocalRing.maximalIdeal (C.left.presheaf.stalk x) := by
    intro r hr hmem
    have h1 : chart k z ∈ (P1 k).basicOpen (secR r) := (chart_mem_basicOpen_secR r z).mpr hr
    rw [hz] at h1
    rw [Scheme.mem_basicOpen _ _ _ hU] at h1
    exact (IsLocalRing.mem_maximalIdeal _).mp (hloc _ hmem) h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hunit (MvPolynomial.X i0) ((chart_mem_basicOpen_X0 k z).mp (hz ▸ hy0))
    have h0 : iotaX C x 0 = 0 := map_zero _
    rw [h0, sub_zero] at hc
    exact hc
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hunit (MvPolynomial.X i0 - 1) ((chart_mem_basicOpen_X0_sub_X1 k z).mp (hz ▸ hy01))
    have : ρ (G (MvPolynomial.X i0 - 1)) = b - iotaX C x 1 := by
      rw [map_sub, map_sub, map_one, map_one, map_one]
    rw [this]; exact hc
  set e := G (MvPolynomial.X i0 - MvPolynomial.C c)
  have hρe : ρ e = b - iotaX C x c := by
    simp only [e, map_sub]; rw [hρC]
  have he : e ∈ IsLocalRing.maximalIdeal _ := hloc e (hρe ▸ hc)
  have hB2 := hB.2 (wOf C x) (fun c' => ⟨iotaX C x c', algebraMap_iotaX C x c'⟩) ⟨b, hb⟩
    (Polynomial.X - Polynomial.C c) (Polynomial.monic_X_sub_C c) (Polynomial.irreducible_X_sub_C c)
    (fun h => hc0 (by simpa using h))
    (fun h => hc1 (by
      have : Polynomial.C c = 1 := sub_right_injective h
      exact Polynomial.C_injective (this.trans Polynomial.C_1.symm)))
    (by
      have : Polynomial.aeval t (Polynomial.X - Polynomial.C c) = γ (b - iotaX C x c) := by
        rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_sub, hb, algebraMap_iotaX]; rfl
      rw [this, algebraMap_mem_nonunits_iff]; exact hc)
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact map_nonunit ρ a ha
  · intro u hu
    obtain ⟨y', hy'w, hy'⟩ := hB2 (γ u) ((algebraMap_mem_nonunits_iff C x u).mpr hu)
    obtain ⟨v, rfl⟩ := hy'w
    have : u = ρ e * v := by
      apply hγinj
      rw [map_mul, hρe, hy']
      congr 1
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_sub, hb, algebraMap_iotaX]; rfl
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ he)

end Assembly


section Degree

variable {k : Type} [Field k] (C : Over (Spec (CommRingCat.of k))) [IsIntegral C.left]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] (t : C.left.functionField)

theorem secR_surjective : Function.Surjective (secR (k := k)) := fun a =>
  ⟨(Scheme.ΓSpecIso _).hom (((chart k).appIso ⊤).hom a), by
    rw [secR, CommRingCat.comp_apply, Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]⟩

theorem psi_mem_adjoin (r : Rk k) :
    letI := ZInQ.LeafPush2.ffAlgebra C
    psi C t r ∈ IntermediateField.adjoin k {t} := by
  letI := ZInQ.LeafPush2.ffAlgebra C
  induction r using MvPolynomial.induction_on with
  | C c => rw [psi_C]; exact IntermediateField.algebraMap_mem _ c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, Subsingleton.elim i i0, psi_X]
    exact mul_mem hp (IntermediateField.mem_adjoin_simple_self k t)

theorem degree_rep (ht : letI := ZInQ.LeafPush2.ffAlgebra C; Transcendental k t)
    {β : C.left ⟶ P1 k} (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t)
    (o : (P1 k).presheaf.stalk (β (genericPoint C.left))) :
    ∃ r₁ r₂ : Rk k, (β.stalkMap (genericPoint C.left)).hom o * psi C t r₂ = psi C t r₁ ∧
      psi C t r₂ ≠ 0 ∧ (r₁ = 0 → o = 0) := by
  have hyU : β (genericPoint C.left) ∈ (chart k) ''ᵁ ⊤ := by
    rw [beta_genericPoint C t hβ]; exact ⟨_, trivial, rfl⟩
  have hUaff : IsAffineOpen ((chart k) ''ᵁ ⊤) := by
    rw [Scheme.Hom.image_top_eq_opensRange]; exact isAffineOpen_opensRange _
  letI := TopCat.Presheaf.algebra_section_stalk (P1 k).presheaf (⟨β (genericPoint C.left), hyU⟩ : ((chart k) ''ᵁ ⊤ : (P1 k).Opens))
  have hloc := hUaff.isLocalization_stalk ⟨β (genericPoint C.left), hyU⟩
  set ρ := (β.stalkMap (genericPoint C.left)).hom
  have hMI : ∀ r, ρ ((P1 k).presheaf.germ _ (β (genericPoint C.left)) hyU (secR r)) = psi C t r := by
    intro r
    have := stalkMap_secR C t hβ (genericPoint C.left) hyU r
    rwa [TopCat.Presheaf.stalkSpecializes_refl] at this
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (hUaff.primeIdealOf ⟨β (genericPoint C.left), hyU⟩).asIdeal.primeCompl o
  subst hab
  obtain ⟨r₁, rfl⟩ := secR_surjective a
  obtain ⟨r₂, hr₂⟩ := secR_surjective b.1
  have hspec := IsLocalization.mk'_spec ((P1 k).presheaf.stalk (β (genericPoint C.left))) (secR r₁) b
  have hb : IsUnit (algebraMap _ ((P1 k).presheaf.stalk (β (genericPoint C.left))) (b : Γ(P1 k, (chart k) ''ᵁ ⊤))) :=
    IsLocalization.map_units _ b
  refine ⟨r₁, r₂, ?_, ?_, ?_⟩
  · have := congrArg ρ hspec
    rw [map_mul] at this
    rw [← hMI, ← hMI, hr₂]
    exact this
  · rw [← hMI, hr₂]
    exact (hb.map ρ).ne_zero
  · rintro rfl
    show IsLocalization.mk' _ (secR 0) b = 0
    rw [map_zero, IsLocalization.mk'_zero]

theorem rhoEta_secR {β : C.left ⟶ P1 k} (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t)
    (r : Rk k) : ∃ o, (β.stalkMap (genericPoint C.left)).hom o = psi C t r := by
  have hyU : β (genericPoint C.left) ∈ (chart k) ''ᵁ ⊤ := by
    rw [beta_genericPoint C t hβ]; exact ⟨_, trivial, rfl⟩
  refine ⟨(P1 k).presheaf.germ _ _ hyU (secR r), ?_⟩
  have := stalkMap_secR C t hβ (genericPoint C.left) hyU r
  rwa [TopCat.Presheaf.stalkSpecializes_refl] at this

/-- **The degree of `β` is `[k(C) : k(t)]`**: the stalk map at the generic point identifies the
function field of `ℙ¹` with `k(t) ⊆ k(C)`. -/
theorem degree_eq (ht : letI := ZInQ.LeafPush2.ffAlgebra C; Transcendental k t)
    {β : C.left ⟶ P1 k} (hβ : C.left.fromSpecFunctionField ≫ β = ptT C t) (d : ℕ)
    (hd : letI := ZInQ.LeafPush2.ffAlgebra C
      Module.finrank (IntermediateField.adjoin k {t}) C.left.functionField = d) :
    @Module.finrank ((P1 k).presheaf.stalk (β (genericPoint C.left))) C.left.functionField _ _
      (β.stalkMap (genericPoint C.left)).hom.toModule = d := by
  letI := ZInQ.LeafPush2.ffAlgebra C
  set ρ := (β.stalkMap (genericPoint C.left)).hom
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro o ho
    obtain ⟨r₁, r₂, h1, -, h3⟩ := degree_rep C t ht hβ o
    apply h3
    apply psi_injective C t ht
    rw [map_zero, ← h1]
    rw [show ρ o = 0 from ho, zero_mul]
  have hmem : ∀ o, ρ o ∈ IntermediateField.adjoin k {t} := by
    intro o
    obtain ⟨r₁, r₂, h1, h2, -⟩ := degree_rep C t ht hβ o
    have : ρ o = psi C t r₁ * (psi C t r₂)⁻¹ := by
      rw [← h1, mul_assoc, mul_inv_cancel₀ h2, mul_one]
    rw [this]
    exact mul_mem (psi_mem_adjoin C t r₁) (inv_mem (psi_mem_adjoin C t r₂))
  have hunit : ∀ o : (P1 k).presheaf.stalk (β (genericPoint C.left)), o ≠ 0 → IsUnit o := by
    intro o ho
    by_contra hnu
    have hm : o ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h1 := map_nonunit ρ o hm
    have h0 : ρ o = 0 := by
      by_contra hne
      exact ((IsLocalRing.mem_maximalIdeal _).mp h1)
        (show IsUnit (ρ o : C.left.functionField) from isUnit_iff_ne_zero.mpr hne)
    exact ho (hinj (h0.trans (map_zero ρ).symm))
  let S : IntermediateField k C.left.functionField :=
    { carrier := Set.range ρ
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul ρ a b⟩
      one_mem' := ⟨1, map_one ρ⟩
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add ρ a b⟩
      zero_mem' := ⟨0, map_zero ρ⟩
      algebraMap_mem' := fun c => by
        obtain ⟨o, ho⟩ := rhoEta_secR C t hβ (MvPolynomial.C c)
        exact ⟨o, ho.trans (psi_C C t c)⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        by_cases ha : a = 0
        · exact ⟨0, by rw [ha, map_zero, inv_zero]⟩
        · refine ⟨((hunit a ha).unit⁻¹ : (Units _)), ?_⟩
          apply eq_inv_of_mul_eq_one_left
          rw [← map_mul]
          have : (((hunit a ha).unit⁻¹ : Units _) : (P1 k).presheaf.stalk (β (genericPoint C.left))) * a = 1 :=
            (hunit a ha).val_inv_mul
          rw [this, map_one] }
  have hle : IntermediateField.adjoin k {t} ≤ S := by
    rw [IntermediateField.adjoin_simple_le_iff]
    obtain ⟨o, ho⟩ := rhoEta_secR C t hβ (MvPolynomial.X i0)
    exact ⟨o, ho.trans (psi_X C t)⟩
  let i := RingEquiv.ofBijective (ρ.codRestrict (IntermediateField.adjoin k {t}) hmem)
    ⟨fun a b h => hinj (congrArg Subtype.val h), fun ⟨f, hf⟩ => by
      obtain ⟨o, ho⟩ := hle hf
      exact ⟨o, Subtype.ext ho⟩⟩
  letI := ρ.toAlgebra
  rw [← hd]
  exact Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) (RingHom.ext fun o => rfl)

end Degree


/-- **`BelyiMapOfFunction` (step (b), glue, proved).** -/
theorem belyiMapOfFunction_proof : BelyiMapOfFunction := by
  intro k _ _ _ C _ _ _ t hB d hd hd0
  letI := ZInQ.LeafPush2.ffAlgebra C
  obtain ⟨β, hβo, hβ⟩ := exists_extension C t
  exact ⟨β, hβo, isFinite_beta C t hB.1 hβo hβ, fun x hx hy => unramified C t hB hβ x hx hy,
    degree_eq C t hB.1 hβ d hd⟩

end JavanpeykarFix

#print axioms JavanpeykarFix.belyiMapOfFunction_proof
