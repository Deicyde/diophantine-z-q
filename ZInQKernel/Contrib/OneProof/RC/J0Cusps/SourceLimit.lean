import ZInQKernel.Contrib.OneProof.RC.J0Cusps.AffineLimit
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.BranchExpansion
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.FormalBranches
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.LaurentLimit

/-! Specialization of the complex chart to an actual point of the
normalization, on the spot (c) for tex 1785–1787 and 2937–2939. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve ShimuraPointDict PkgI3
open scoped Topology

namespace ZInQ.Manuscript.RC.J0Cusps

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

/-- The existing interior chart, as a field-valued point over the rationals. -/
def interior (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    AbVar.ptObj (K := ℚ) ℂ ⟶ Over.mk (X0Model.overQ N) :=
  Over.homMk (X0Model.complexPoint N τ) (X0Model.complexPoint_overQ N τ)

/-- The complex point of a cusp branch with algebraic coefficients. -/
def branchComplex (N : ℕ) [NeZero N] {K : Type} [Field K] [Algebra ℚ K]
    (ι : K →+* ℂ) (e : modularFunctionField N →+* LaurentSeries K) :
    AbVar.ptObj (K := ℚ) ℂ ⟶ Over.mk (X0Model.overQ N) :=
  Over.homMk (Spec.map (CommRingCat.ofHom ι) ≫ branchPoint N e) (maps_to_rat_unique _ _)

private theorem preimage_top_comp {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B]
    (u : Spec (.of A) ⟶ X) (f : Spec (.of B) ⟶ Spec (.of A)) (U : X.Opens)
    (h : ⊤ ≤ u ⁻¹ᵁ U) : ⊤ ≤ (f ≫ u) ⁻¹ᵁ U :=
  fun x _ => by rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply]; exact h trivial

private def sectionField (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens) [Nonempty U] :
    Γ(X0Model.curve N, U) →+* modularFunctionField N :=
  (X0Model.functionField N).toRingHom.comp ((X0Model.curve N).germToFunctionField U).hom

private def interiorSection (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens) [Nonempty U]
    (τ : UpperHalfPlane) : Γ(X0Model.curve N, U) →+* X0Model.MeromorphicGerm (τ : ℂ) :=
  (X0Model.fieldGerm N τ).comp (sectionField N U)

private theorem regular_interiorSection (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens)
    [Nonempty U] (r : Γ(X0Model.curve N, U)) (τ : UpperHalfPlane) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f (τ : ℂ))
    (he : (f : PuncturedGerm (τ : ℂ)) =
      X0Model.meromorphicIncl (τ : ℂ) (interiorSection N U τ r)) :
    interiorSection N U τ r ∈ X0Model.meromorphicValuation (τ : ℂ) :=
  ⟨f τ, he ▸ hasValue_coe.mpr (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)⟩

private theorem chart_mem_of_regular (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens)
    [Nonempty U] (hU : IsAffineOpen U) (τ : UpperHalfPlane)
    (h : ∀ r, interiorSection N U τ r ∈ X0Model.meromorphicValuation (τ : ℂ))
    (hg : ⊤ ≤ (X0Model.genericMap N (X0Model.fieldGerm N τ)) ⁻¹ᵁ U) :
    ⊤ ≤ (X0Model.complexPoint N τ) ⁻¹ᵁ U := by
  let R := X0Model.meromorphicValuation (τ : ℂ)
  let F := X0Model.MeromorphicGerm (τ : ℂ)
  let g := (interiorSection N U τ).codRestrict R.toSubring h
  let u := Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec
  have hu : ⊤ ≤ u ⁻¹ᵁ U := by
    intro z _
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply]
    change _ ∈ (U : Set (X0Model.curve N))
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self _
  have he : Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ u =
      X0Model.genericMap N (X0Model.fieldGerm N τ) := by
    calc
      _ = Spec.map (X0Model.sectionMap (X0Model.genericMap N (X0Model.fieldGerm N τ)) U hg) ≫
            hU.fromSpec := by
        change Spec.map _ ≫ Spec.map (CommRingCat.ofHom g) ≫ _ = _
        rw [← Category.assoc, ← Spec.map_comp, X0Model.sectionMap_generic]
        rfl
      _ = _ := sectionMap_factor _ hU hg
  let ι : ℚ →+* R :=
    ((X0Model.constantGerm (τ : ℂ)).comp (Rat.castHom ℂ)).codRestrict R.toSubring
      fun c => ⟨(c : ℂ), hasValue_coe.mpr tendsto_const_nhds⟩
  let : Algebra ℚ R := ι.toAlgebra
  obtain ⟨v, _, huniq⟩ :=
    X0Model.existsUnique_specialization (R := R) N (X0Model.fieldGerm N τ)
  have hu' : u = X0Model.analyticArc N τ :=
    (huniq u ⟨he, maps_to_rat_unique _ _⟩).trans
      (huniq _ ⟨X0Model.analyticArc_generic N τ, maps_to_rat_unique _ _⟩).symm
  rw [X0Model.complexPoint, ← hu']
  exact preimage_top_comp u _ U hu

private theorem eventually_chart_mem (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens)
    [Nonempty U] (hU : IsAffineOpen U) {I : Type} {F : Filter I}
    (x : I → UpperHalfPlane)
    (h : ∀ r, ∀ᶠ i in F,
      interiorSection N U (x i) r ∈ X0Model.meromorphicValuation (x i : ℂ))
    (hg : ∀ i, ⊤ ≤ (X0Model.genericMap N (X0Model.fieldGerm N (x i))) ⁻¹ᵁ U) :
    ∀ᶠ i in F, ⊤ ≤ (X0Model.complexPoint N (x i)) ⁻¹ᵁ U := by
  classical
  let A := Γ(X0Model.curve N, U)
  let hf : LocallyOfFiniteType (X0Model.overQ N) := (X0Model.proper N).toLocallyOfFiniteType
  let α : ℚ →+* A :=
    ((Scheme.ΓSpecIso (.of ℚ)).inv ≫ (X0Model.overQ N).appLE ⊤ U (by simp)).hom
  let := α.toAlgebra
  have hα : α.FiniteType :=
    ((X0Model.overQ N).finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (RingHom.FiniteType.of_surjective _ ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of ℚ)).inv).2))
  have hfin : Algebra.FiniteType ℚ A := hα
  obtain ⟨S, hS⟩ := hfin.out
  filter_upwards [(eventually_all_finset S).2 fun r _ => h r] with i hi
  apply chart_mem_of_regular N U hU (x i) _ (hg i)
  let B : Subalgebra ℚ A :=
    { toSubsemiring := ((X0Model.meromorphicValuation (x i : ℂ)).toSubring.comap
        (interiorSection N U (x i))).toSubsemiring
      algebraMap_mem' := fun q => by
        change interiorSection N U (x i) (α q) ∈ X0Model.meromorphicValuation (x i : ℂ)
        have e : (interiorSection N U (x i)).comp α =
            (X0Model.constantGerm (x i : ℂ)).comp (Rat.castHom ℂ) := Subsingleton.elim _ _
        change ((interiorSection N U (x i)).comp α) q ∈ _
        rw [e]
        exact ⟨(q : ℂ), hasValue_coe.mpr tendsto_const_nhds⟩ }
  have hle : Algebra.adjoin ℚ (S : Set A) ≤ B := Algebra.adjoin_le fun r hr => hi r hr
  rw [hS] at hle
  exact fun r => hle (show r ∈ (⊤ : Subalgebra ℚ A) from trivial)

private theorem generic_hits_open (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens)
    [Nonempty U] {K : Type} [Field K] (e : modularFunctionField N →+* K) :
    ⊤ ≤ (X0Model.genericMap N e) ⁻¹ᵁ U := by
  intro z _
  have hz : X0Model.genericMap N e z = genericPoint (X0Model.curve N) := by
    rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
    dsimp only [X0Model.genericMap]
    erw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  change X0Model.genericMap N e z ∈ U
  rw [hz]
  exact ((genericPoint_spec (X0Model.curve N)).mem_open_set_iff U.isOpen).mpr
    (by rw [Set.univ_inter]; exact Set.nonempty_coe_sort.mp ‹Nonempty U›)

private theorem chart_section_value (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens)
    [Nonempty U] (r : Γ(X0Model.curve N, U)) (τ : UpperHalfPlane)
    (h : ⊤ ≤ (X0Model.complexPoint N τ) ⁻¹ᵁ U) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f (τ : ℂ))
    (he : (f : PuncturedGerm (τ : ℂ)) =
      X0Model.meromorphicIncl (τ : ℂ) (interiorSection N U τ r)) :
    X0Model.sectionMap (X0Model.complexPoint N τ) U h r = f τ := by
  obtain ⟨s, hs, hv⟩ := X0Model.sectionGerm N τ U r (h trivial)
  rw [← hv]
  have h' : (f : PuncturedGerm (τ : ℂ)) = X0Model.meromorphicIncl (τ : ℂ) s.val :=
    he.trans (congrArg (X0Model.meromorphicIncl (τ : ℂ)) hs.symm)
  exact hasValue_unique (finiteValue_spec _ s) (h' ▸ hasValue_coe.mpr
    (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))

private theorem sectionValue_comp {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B]
    (u : Spec (.of A) ⟶ X) (e : A →+* B) (U : X.Opens) (hu : ⊤ ≤ u ⁻¹ᵁ U)
    (he : ⊤ ≤ (Spec.map (CommRingCat.ofHom e) ≫ u) ⁻¹ᵁ U) (r : Γ(X, U)) :
    sectionEval (Spec.map (CommRingCat.ofHom e) ≫ u) U he r = e (sectionEval u U hu r) :=
  congrArg (fun v : Γ(X, U) ⟶ CommRingCat.of B => v r) (X0Model.sectionMap_comp u e U hu he)

set_option maxHeartbeats 1000000 in
/-- Two convergent generator expansions identify the source limit with the
closed end of the specified formal branch. This does not use a map to an
elliptic curve or any period or group data. -/
theorem sourceLimit_of_generator_expansions (N : ℕ) [NeZero N] {K : Type} [Field K] [Algebra ℚ K]
    (ι : K →+* ℂ) (e : modularFunctionField N →+* LaurentSeries K)
    {I : Type} {F : Filter I} [F.NeBot] (q : I → ℂ) (x : I → UpperHalfPlane)
    (hq : Tendsto q F (𝓝[≠] 0)) (hqn : ∀ i, q i ≠ 0)
    (hJ : ∀ᶠ i in F, HasSum (fun n : ℤ => ι ((e ⟨jq, jq_mem N⟩).coeff n) * q i ^ n)
      (X0Model.analyticJ (x i)))
    (hJN : ∀ᶠ i in F, HasSum (fun n : ℤ => ι ((e ⟨jqN N, jqN_mem N⟩).coeff n) * q i ^ n)
      (X0Model.analyticJN N (x i))) :
    Tendsto (fun i => complexLift (interior N (x i))) F (𝓝 (complexLift (branchComplex N ι e))) := by
  let b := formalBranch N e
  let c := branchComplex N ι e
  let p := fun i => interior N (x i)
  obtain ⟨U, hU, hb, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := b (IsLocalRing.closedPoint (PowerSeries K))) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨_, hb⟩⟩
  have hb' : ⊤ ≤ b ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem b hb).ge
  have hc₁ : ⊤ ≤ (branchPoint N e) ⁻¹ᵁ U := preimage_top_comp b _ U hb'
  have hc : ⊤ ≤ c.left ⁻¹ᵁ U := preimage_top_comp (branchPoint N e) _ U hc₁
  have hscope : ∀ r : Γ(X0Model.curve N, U), ∃ f : ℂ → ℂ,
      (∀ w : UpperHalfPlane, (f : PuncturedGerm (w : ℂ)) =
        X0Model.meromorphicIncl (w : ℂ) (interiorSection N U w r)) ∧
      ∀ᶠ i in F, AnalyticAt ℂ f (x i : ℂ) ∧
        HasSum (fun n : ℤ => ι ((e (sectionField N U r)).coeff n) * q i ^ n) (f (x i)) :=
    fun r => branch_expansion N ι e q x hq hqn hJ hJN (sectionField N U r)
  have hmem : ∀ᶠ i in F, ⊤ ≤ (p i).left ⁻¹ᵁ U := by
    apply eventually_chart_mem N U hU x _ (fun i => generic_hits_open N U _)
    intro r
    obtain ⟨f, hf, he⟩ := hscope r
    exact he.mono fun i hi => regular_interiorSection N U r (x i) hi.1 (hf (x i))
  apply tendsto_complexLift_of_sections U hU p c hmem hc
  intro r
  let P := X0Model.sectionMap b U hb' r
  have hg : ⊤ ≤ (X0Model.genericMap N e) ⁻¹ᵁ U := generic_hits_open N U e
  let i := algebraMap (PowerSeries K) (LaurentSeries K)
  have hform := X0Model.sectionMap_comp b i U hb' (preimage_top_comp b _ U hb')
  have hgen (v : Spec (.of (LaurentSeries K)) ⟶ X0Model.curve N) (hv : ⊤ ≤ v ⁻¹ᵁ U)
      (he : v = X0Model.genericMap N e) :
      X0Model.sectionMap v U hv = CommRingCat.ofHom (e.comp (sectionField N U)) := by
    subst v
    rw [X0Model.sectionMap_generic]
    rfl
  have hform' := (hgen _ _ (formalBranch_generic N e)).symm.trans hform
  have hP : e (sectionField N U r) = (P : LaurentSeries K) :=
    congrArg (fun v : Γ(X0Model.curve N, U) ⟶ CommRingCat.of (LaurentSeries K) => v r) hform'
  have hval : sectionEval c.left U hc r = ι (PowerSeries.constantCoeff P) :=
    (sectionValue_comp (branchPoint N e) ι U hc₁ hc r).trans
      (congrArg (fun z : K => ι z) (sectionValue_comp b PowerSeries.constantCoeff U hb' hc₁ r))
  obtain ⟨f, hf, hs⟩ := hscope r
  have hs' := tendsto_powerSeries_eval ι P q (fun i => f (x i))
    (hq.mono_right nhdsWithin_le_nhds) (Eventually.of_forall hqn) (hs.mono fun i hi => hP ▸ hi.2)
  rw [← hval] at hs'
  apply hs'.congr'
  filter_upwards [hmem, hs] with i hi hsi
  rw [dite_eq_left hi]
  exact (chart_section_value N U r (x i) hi hsi.1 (hf (x i))).symm


end ZInQ.Manuscript.RC.J0Cusps
