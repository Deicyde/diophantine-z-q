import ZInQKernel.Contrib.OneProof.FaltingsRestateDVR
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.SmoothSourceDescent

/-! The fibre conditions in Faltings' definition (Invent. Math. 73 (1983), p. 350)
for the DVR models of `FaltingsLemma1DVR`. -/

noncomputable section

namespace ZInQ.FaltingsRestate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit DictModels.RaynaudOr ZInQ.HeightSplit

set_option linter.style.haveILetI false

/-- A faithfully flat group quotient of the entire group by a torus, written using
the kernel's affine functor of points over an algebraic closure. The torus need
not split over the residue field itself. -/
def HasTorusExtension {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] :
    Prop :=
  ∃ (B : PkgI3.AbVar k) (π : G ⟶ B.X), IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
    ∃ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
        letI := algK (φbar k) R
        (Fin r → Rˣ) →* (algPt k R ⟶ G)),
      (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R)) ∧
      (∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
        letI := algK (φbar k) R
        ∀ u : algPt k R ⟶ G, u ≫ π = 1 ↔ u ∈ (e R).range) ∧
      (∀ (R S : Type) [CommRing R] [CommRing S] [Algebra (AlgebraicClosure k) R]
        [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
        letI := algK (φbar k) R
        letI := algK (φbar k) S
        e S (fun i => Units.map (f : R →* S) (t i)) =
          algPtMap (k := k) ({ (f : R →+* S) with commutes' := fun a => f.commutes (φbar k a) } :
            R →ₐ[k] S) ≫ e R t)

private theorem isIso_openSubgroup_of_connected {k : Type} [Field k]
    {U G : Over (Spec (CommRingCat.of k))} [GrpObj U] [GrpObj G] [ConnectedSpace U.left]
    [ConnectedSpace G.left] [LocallyOfFiniteType G.hom]
    (i : U ⟶ G) [IsOpenImmersion i.left] [IsMonHom i] : IsIso i := by
  have hr := ZInQ.SemistabAssembly.range_eq_connectedComponent i
  rw [PreconnectedSpace.connectedComponent_eq_univ] at hr
  haveI : IsIso i.left := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    exact ⟨inferInstance, ⟨Set.range_eq_univ.mp hr⟩⟩
  haveI : IsIso ((Over.forget _).map i) := ‹IsIso i.left›
  exact isIso_of_reflects_iso i (Over.forget _)

/-- In a connected group scheme the open connected subgroup in the
identity-component condition is the whole group, so the quotient is defined on `G`. -/
theorem hasTorusExtension_of_connected {k : Type} [Field k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom]
    [ConnectedSpace G.left] (h : HasSemiAbelianIdCompTorus G) : HasTorusExtension G := by
  obtain ⟨U, _, i, hi, him, hc, B, π, hπ, hf, hs, r, e, he, hk, hn⟩ := h
  haveI : IsIso i := isIso_openSubgroup_of_connected i
  let j := (asIso i).inv
  haveI : IsMonHom j := inferInstanceAs (IsMonHom (asIso i).inv)
  haveI : IsIso j.left := (Over.forget _).map_isIso j
  have hji : j ≫ i = 𝟙 G := (asIso i).inv_hom_id
  have hij : i ≫ j = 𝟙 U := (asIso i).hom_inv_id
  let E (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] :
      letI := algK (φbar k) R
      (Fin r → Rˣ) →* (algPt k R ⟶ G) :=
    letI := algK (φbar k) R
    { toFun := fun t => e R t ≫ i
      map_one' := by rw [map_one, MonObj.one_comp]
      map_mul' := by intro a b; rw [map_mul, MonObj.mul_comp] }
  refine ⟨B, j ≫ π, inferInstance, ?_, ?_, r, E, ?_, ?_, ?_⟩
  · change Flat (j.left ≫ π.left)
    infer_instance
  · change Surjective (j.left ≫ π.left)
    infer_instance
  · intro R _ _ a b hab
    exact he R ((cancel_mono i).mp hab)
  · intro R _ _ u
    letI := algK (φbar k) R
    change (u ≫ j ≫ π = 1) ↔ ∃ t, e R t ≫ i = u
    rw [← Category.assoc, hk R]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [ht, Category.assoc, hji, Category.comp_id]⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [← ht, Category.assoc, hij, Category.comp_id]⟩
  · intro R S _ _ _ _ f t
    dsimp only [E, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [hn, Category.assoc]

variable {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}

/-- The fraction field of a DVR is the localization at any uniformizer. -/
theorem isLocalizationAway_uniformizer [IsDiscreteValuationRing O] {π : O}
    (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := K)
    (nonZeroDivisors O) ?_ ?_).mpr inferInstance
  · rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hπ.ne_zero)
  · intro x hx
    obtain ⟨n, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (mem_nonZeroDivisors_iff_ne_zero.mp hx) hπ
    refine ⟨π ^ n, ⟨n, rfl⟩, ?_⟩
    have hu : (↑u : O) ∣ (1 : O) := isUnit_iff_dvd_one.mp u.isUnit
    exact (mul_dvd_mul_right hu (π ^ n)).trans (by rw [_root_.one_mul])

/-- The image of the generic inclusion is the principal open of a uniformizer. -/
theorem jO_range_eq_basicOpen [IsDiscreteValuationRing O] {π : O}
    (hπ : Irreducible π) :
    Set.range (jO O) = (PrimeSpectrum.basicOpen π).1 := by
  letI := isLocalizationAway_uniformizer hπ
  exact PrimeSpectrum.localization_away_comap_range K π

/-- `jO` identifies `Spec K` with the dense open consisting of the generic
point of `Spec O`. -/
theorem jO_genericOpen (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    IsOpenImmersion (jO O) ∧ DenseRange (jO O) ∧
      Set.range (jO O) = {genericPoint (Spec (CommRingCat.of O))} := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  letI := isLocalizationAway_uniformizer hπ
  haveI : IsOpenImmersion (jO O) := IsOpenImmersion.of_isLocalization π
  have hr : Set.range (jO O) = {genericPoint (Spec (CommRingCat.of O))} :=
    Set.range_eq_singleton (fun x => by
      rw [Subsingleton.elim x (genericPoint (Spec (CommRingCat.of K)))]
      exact genericPoint_eq_of_isOpenImmersion (jO O))
  refine ⟨inferInstance, ?_, hr⟩
  rw [DenseRange, dense_iff_closure_eq, hr]
  exact isGenericPoint_def.mp (genericPoint_spec (Spec (CommRingCat.of O)))

/-- The two residue-field maps used in the definition account for every
point of the DVR base. -/
theorem specDVR_points (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (x : Spec (CommRingCat.of O)) :
    x ∈ Set.range (jO O) ∨ x ∈ Set.range (closedFibreMap O) := by
  let z : Spec (CommRingCat.of O) := IsLocalRing.closedPoint O
  have hs : Set.range (closedFibreMap O) = {z} :=
    Set.range_eq_singleton (fun y => IsLocalRing.PrimeSpectrum.comap_residue O y)
  rw [(jO_genericOpen O).2.2, hs, Set.mem_singleton_iff, Set.mem_singleton_iff]
  by_cases h : x.asIdeal = ⊥
  · left
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext h
  · right
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ring.DimensionLEOne.maximalOfPrime h x.isPrime))

/-- The group scheme over the actual residue field of the DVR. -/
abbrev closedFibre (G : GroupModelO A O) := (Over.pullback (closedFibreMap O)).obj G.G

/-- The whole closed fibre has a torus kernel over its residue field. -/
theorem closedFibre_hasTorusExtension (G : GroupModelO A O) (h : IsSemiabelianModelO G) :
    letI : GrpObj (closedFibre G) := Functor.grpObjObj
    HasTorusExtension (closedFibre G) := by
  letI : GrpObj (closedFibre G) := Functor.grpObjObj
  obtain ⟨hc, ht⟩ := h
  haveI : LocallyOfFiniteType (closedFibre G).hom := by
    change LocallyOfFiniteType (pullback.snd G.G.hom (closedFibreMap O))
    infer_instance
  exact hasTorusExtension_of_connected _ ht

private theorem smoothRank_chart {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (n : ℕ), x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, V, -, -, hx, hle, n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
  refine ⟨V, n, hx, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f hle]
  exact smoothOfRelativeDimension_comp (n := n) (m := 0) _ _

private theorem smoothRank_mono {X S : Scheme.{0}} {f : X ⟶ S}
    {U V : X.Opens} (e : U ≤ V) {n : ℕ} (hn : SmoothOfRelativeDimension n (V.ι ≫ f)) :
    SmoothOfRelativeDimension n (U.ι ≫ f) := by
  rw [← X.homOfLE_ι e, Category.assoc]
  have : SmoothOfRelativeDimension (0 + n) (X.homOfLE e ≫ V.ι ≫ f) := inferInstance
  simpa only [zero_add] using this

/-- On a connected smooth scheme over a field the relative dimension on any
nonempty chart is the relative dimension everywhere. -/
private theorem smoothRank_of_connected {k : Type} [Field k] {X : Scheme.{0}}
    [ConnectedSpace X] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (V : X.Opens) (hV : Nonempty V) {n : ℕ} (hn : SmoothOfRelativeDimension n (V.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  let P (d : ℕ) : Set X :=
    {x | ∃ U : X.Opens, x ∈ U ∧ SmoothOfRelativeDimension d (U.ι ≫ f)}
  have hsubset (d : ℕ) (U : X.Opens) (hU : SmoothOfRelativeDimension d (U.ι ≫ f)) :
      (U : Set X) ⊆ P d := fun _ hx => ⟨U, hx, hU⟩
  have hopen (d : ℕ) : IsOpen (P d) := isOpen_iff_mem_nhds.mpr fun x ⟨U, hx, hU⟩ =>
    Filter.mem_of_superset (U.2.mem_nhds hx) (hsubset d U hU)
  have huniq (x : X) (m d : ℕ) (hm : x ∈ P m) (hd : x ∈ P d) : m = d := by
    obtain ⟨U, hxU, hU⟩ := hm
    obtain ⟨W, hxW, hW⟩ := hd
    haveI : Nonempty (U ⊓ W : X.Opens) := ⟨⟨x, ⟨hxU, hxW⟩⟩⟩
    exact SmoothOfRelativeDimension.eq_of_field ((U ⊓ W).ι ≫ f)
      (smoothRank_mono inf_le_left hU) (smoothRank_mono inf_le_right hW)
  have hc : IsClosed (P n) := by
    rw [← isOpen_compl_iff]
    refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    obtain ⟨U, m, hxU, hU⟩ := smoothRank_chart f x
    have hmn : m ≠ n := fun e => hx (e ▸ hsubset m U hU hxU)
    exact Filter.mem_of_superset ((hopen m).mem_nhds (hsubset m U hU hxU))
      (fun y hy hyn => hmn (huniq y m n hy hyn))
  obtain ⟨x⟩ := hV
  have hne : (P n).Nonempty := ⟨x.1, hsubset n V hn x.2⟩
  exact smoothOfRelativeDimension_of_forall_exists_mem f n fun x => by
    change x ∈ P n
    rw [IsClopen.eq_univ ⟨hc, hopen n⟩ hne]
    trivial

private theorem dim_baseChange_eq_chart {k : Type} [Field k] {X S : Scheme.{0}} (f : X ⟶ S)
    [Smooth f] (t : Spec (CommRingCat.of k) ⟶ S)
    [ConnectedSpace (pullback f t : Scheme)] (V : X.Opens)
    (hV : Nonempty (pullback.fst f t ⁻¹ᵁ V : (pullback f t).Opens))
    {n : ℕ} (hn : SmoothOfRelativeDimension n (V.ι ≫ f)) :
    topologicalKrullDim (pullback f t : Scheme) = n := by
  let W := pullback.fst f t ⁻¹ᵁ V
  haveI : SmoothOfRelativeDimension n (W.ι ≫ pullback.snd f t) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
    exact MorphismProperty.of_isPullback
      ((isPullback_morphismRestrict (pullback.fst f t) V).paste_vert
        (IsPullback.of_hasPullback f t)) hn
  haveI : SmoothOfRelativeDimension n (pullback.snd f t) :=
    smoothRank_of_connected (pullback.snd f t) W hV inferInstance
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension (pullback.snd f t) n

private theorem genericFibre_connected (G : GroupModelO A O) :
    ConnectedSpace ((Over.pullback (jO O)).obj G.G).left := by
  haveI : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.X.hom
  exact (Scheme.homeoOfIso ((Over.forget _).mapIso G.gen)).connectedSpace_iff.mpr
    (inferInstance : ConnectedSpace A.X.left)

/-- The Krull dimension of the generic fibre is that of the abelian variety. -/
theorem genericFibre_dim_eq (G : GroupModelO A O) :
    topologicalKrullDim ((Over.pullback (jO O)).obj G.G).left = A.dim :=
  IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso ((Over.forget _).mapIso G.gen)).isHomeomorph

/-- The two fibres have a common finite Krull dimension: a smooth chart
at the closed identity meets both fibres along the identity section. -/
theorem fibre_dims (G : GroupModelO A O) (h : IsSemiabelianModelO G) :
    ∃ n : ℕ, topologicalKrullDim ((Over.pullback (jO O)).obj G.G).left = n ∧
      topologicalKrullDim (closedFibre G).left = n := by
  haveI : ConnectedSpace (pullback G.G.hom (closedFibreMap O) : Scheme) := h.1
  haveI : ConnectedSpace (pullback G.G.hom (jO O) : Scheme) := genericFibre_connected G
  let s : Spec (CommRingCat.of O) ⟶ G.G.left :=
    (η[G.G] : 𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ G.G).left
  have hs : s ≫ G.G.hom = 𝟙 _ := Over.w (η[G.G])
  obtain ⟨V, n, hv, hn⟩ := smoothRank_chart G.G.hom (s (IsLocalRing.closedPoint O))
  have hAll (x : Spec (CommRingCat.of O)) : s x ∈ V :=
    ((IsLocalRing.specializes_closedPoint x).map s.continuous).mem_open V.2 hv
  have hmeets {k : Type} [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of O)) :
      Nonempty (pullback.fst G.G.hom t ⁻¹ᵁ V : (pullback G.G.hom t).Opens) := by
    let u : Spec (CommRingCat.of k) ⟶ pullback G.G.hom t :=
      pullback.lift (t ≫ s) (𝟙 _) (by simp [Category.assoc, hs])
    let x : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
    refine ⟨⟨u x, ?_⟩⟩
    change pullback.fst G.G.hom t (u x) ∈ V
    have hu : u ≫ pullback.fst G.G.hom t = t ≫ s := pullback.lift_fst ..
    simpa only [← Scheme.Hom.comp_apply, hu] using hAll (t x)
  exact ⟨n, dim_baseChange_eq_chart G.G.hom (jO O) V (hmeets _) hn,
    dim_baseChange_eq_chart G.G.hom (closedFibreMap O) V (hmeets _) hn⟩

/-- The dimension of the whole closed fibre equals the dimension of `A`. -/
theorem closedFibre_dim_eq (G : GroupModelO A O) (h : IsSemiabelianModelO G) :
    topologicalKrullDim (closedFibre G).left = A.dim := by
  obtain ⟨n, hη, hs⟩ := fibre_dims G h
  exact hs.trans (hη.symm.trans (genericFibre_dim_eq G))

/-- A smooth separated model of an abelian variety is commutative. Restriction
to the schematically dense generic fibre is injective on maps from the square
of the model, since the square is flat and the target is separated. -/
theorem isCommMonObj_groupModelO (G : GroupModelO A O) : IsCommMonObj G.G := by
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj G.G) := Functor.grpObjObj
  haveI : IsMonHom G.gen.hom := G.gen_hom
  haveI : IsSchemeTheoreticallyDominant (jO O) :=
    ZInQ.Contrib.NeronC.isSchemeTheoreticallyDominant_spec_map _
      (FaithfulSMul.algebraMap_injective O K)
  haveI : Smooth (G.G ⊗ G.G).hom :=
    ZInQ.Contrib.NeronC.smooth_tensor G.G G.G inferInstance inferInstance
  refine ⟨?_⟩
  rw [MonObj.mul_eq_mul G.G, MonObj.comp_mul]
  simp only [braiding_hom_fst, braiding_hom_snd]
  apply ZInQ.Contrib.NeronC.pullback_map_injective (jO O) (G.G ⊗ G.G) G.G
  apply (cancel_mono G.gen.hom).mp
  change F.map (snd _ _ * fst _ _) ≫ G.gen.hom = F.map (fst _ _ * snd _ _) ≫ G.gen.hom
  rw [F.map_mul, F.map_mul, MonObj.mul_comp, MonObj.mul_comp, mul_comm]

/-- The abelian generic fibre is an extension with torus of rank zero. -/
theorem genericFibre_hasTorusExtension (G : GroupModelO A O) :
    letI : GrpObj ((Over.pullback (jO O)).obj G.G) := Functor.grpObjObj
    HasTorusExtension ((Over.pullback (jO O)).obj G.G) := by
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj G.G) := Functor.grpObjObj
  haveI : IsIso G.gen.hom.left := (Over.forget _).map_isIso G.gen.hom
  refine ⟨A, G.gen.hom, G.gen_hom, inferInstance, inferInstance, 0,
    fun R _ _ => letI := algK (φbar K) R; 1, ?_, ?_, ?_⟩
  · intro R _ _
    exact fun _ _ _ => Subsingleton.elim _ _
  · intro R _ _ u
    letI := algK (φbar K) R
    change u ≫ G.gen.hom = 1 ↔ ∃ _ : Fin 0 → Rˣ, (1 : algPt K R ⟶ F.obj G.G) = u
    haveI : IsMonHom G.gen.hom := G.gen_hom
    constructor
    · intro hu
      exact ⟨1, (cancel_mono G.gen.hom).mp (by simpa only [MonObj.one_comp] using hu.symm)⟩
    · rintro ⟨_, rfl⟩
      exact MonObj.one_comp _
  · intros
    exact (MonObj.comp_one _).symm

/-- Faltings' fibrewise semiabelian condition on a DVR model, with its common
fibre dimension. The model is a smooth separated group scheme of finite type;
both residue-field fibres are connected and are extensions of abelian varieties
by tori. We include commutativity to cover that reading of “algebraic group”. -/
def FaltingsSemiabelianDef [IsDiscreteValuationRing O] (G : GroupModelO A O) : Prop :=
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj G.G) := Functor.grpObjObj
  letI : GrpObj (closedFibre G) := Functor.grpObjObj
  Smooth G.G.hom ∧ IsSeparated G.G.hom ∧ LocallyOfFiniteType G.G.hom ∧
    QuasiCompact G.G.hom ∧ IsCommMonObj G.G ∧
    ConnectedSpace (F.obj G.G).left ∧ HasTorusExtension (F.obj G.G) ∧
    ConnectedSpace (closedFibre G).left ∧ HasTorusExtension (closedFibre G) ∧
    ∃ g : ℕ, A.dim = g ∧ topologicalKrullDim (F.obj G.G).left = g ∧
      topologicalKrullDim (closedFibre G).left = g

/-- Every model in the domain of `FaltingsLemma1DVR` satisfies the fibrewise
definition of a semiabelian scheme on p. 350. -/
theorem isSemiabelianModelO_imp_faltingsDef [IsDiscreteValuationRing O]
    (G : GroupModelO A O) (h : IsSemiabelianModelO G) : FaltingsSemiabelianDef G := by
  obtain ⟨g, hη, hs⟩ := fibre_dims G h
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, isCommMonObj_groupModelO G,
    genericFibre_connected G, genericFibre_hasTorusExtension G, h.1,
    closedFibre_hasTorusExtension G h, g, (genericFibre_dim_eq G).symm.trans hη, hη, hs⟩

/-- The dictionary applies to both the source and the target in the DVR leaf. -/
theorem faltingsLemma1DVR_models [IsDiscreteValuationRing O]
    {B : PkgI3.AbVar K} (G : GroupModelO A O) (H : GroupModelO B O)
    (hG : IsSemiabelianModelO G) (hH : IsSemiabelianModelO H) :
    FaltingsSemiabelianDef G ∧ FaltingsSemiabelianDef H :=
  ⟨isSemiabelianModelO_imp_faltingsDef G hG, isSemiabelianModelO_imp_faltingsDef H hH⟩

/-- A homomorphism extension theorem on the printed fibre conditions supplies
the existing DVR leaf. Here the premises include normality of the affine base
and the dense open immersion, as in the recorded reading of Lemma 1. -/
theorem faltingsLemma1DVR_of_printed
    (extend : ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (A B : PkgI3.AbVar K) (G : GroupModelO A O) (H : GroupModelO B O),
      IsIntegrallyClosed O →
      FaltingsSemiabelianDef G → FaltingsSemiabelianDef H →
      ∀ {U : Scheme.{0}} (j : U ⟶ Spec (CommRingCat.of O)), IsOpenImmersion j → DenseRange j →
      let F := Over.pullback j
      letI : GrpObj (F.obj G.G) := Functor.grpObjObj
      letI : GrpObj (F.obj H.G) := Functor.grpObjObj
      ∀ f : F.obj G.G ⟶ F.obj H.G, IsMonHom f →
        ∃! g : G.G ⟶ H.G, IsMonHom g ∧ F.map g = f) :
    FaltingsLemma1DVR := by
  intro K _ O _ A B G H hG hH
  obtain ⟨hG', hH'⟩ := faltingsLemma1DVR_models G H hG hH
  obtain ⟨hj, hd, _⟩ := jO_genericOpen O
  exact extend K O A B G H inferInstance hG' hH' (jO O) hj hd

end ZInQ.FaltingsRestate
