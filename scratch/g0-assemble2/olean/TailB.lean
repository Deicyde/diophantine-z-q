import TailA

/-! ## g0-assemble2: fs1-descend (scratch/fs1-descend/FiniteDescends.lean lines 2-117, verbatim; its own copy of
`FiniteDescends` is kept in namespace `FS1Descend` and identified with g0-fibresimple's below by `Iff.rfl`) -/

/-!
# fs1-descend: FS1b′ `FiniteDescends` proved

`FiniteDescends` is copied verbatim from `scratch/g0-fibresimple/FibreSimple.lean` (it depends
only on Mathlib). It is proved here from Mathlib v4.35 alone:

* `IsFinite = IsProper ⊓ LocallyQuasiFinite` (Mathlib, Zariski's main theorem file,
  `IsFinite.iff_isProper_and_locallyQuasiFinite`, Stacks 02LS);
* `IsProper = IsSeparated ⊓ UniversallyClosed ⊓ LocallyOfFiniteType`; universal closedness and
  local finite type descend along fpqc morphisms (Mathlib instances), and separatedness descends
  because `IsSeparated = diagonal UniversallyClosed` (proved below: the diagonal is an immersion,
  and an immersion with closed image is a closed immersion) and Mathlib descends diagonals;
* local quasi-finiteness descends along surjections for locally-finite-type targets (proved
  below by the fibre-cardinality criterion `LocallyQuasiFinite.of_finite_preimage_singleton`
  and the points of a fibre product, `Scheme.exists_preimage_of_isPullback`);
* `Spec L → Spec K` is surjective, flat and quasi-compact, and so is its base change
  `Y_L → Y`; the square `X_L → Y_L` over `X → Y` is a pullback (pasting).
-/

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

namespace FS1Descend

universe u

set_option backward.isDefEq.respectTransparency.types false

/-- **Glue piece FS1b′ (finiteness descends along a field extension).** *Why true* (STANDARD):
finiteness is fpqc local on the target (EGA IV₂ 2.7.1, UNVERIFIED number). Mathlib v4.35 has
`RingHom.Finite.codescendsAlong_faithfullyFlat` and `HasAffineProperty.descendsAlong_of_affineAnd`,
but not the descent of `IsAffineHom` that the latter needs. Glue (scheme theory). -/
def FiniteDescends : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (X Y : Over (Spec (CommRingCat.of K)))
    (g : X ⟶ Y),
    IsFinite ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g).left →
      IsFinite g.left

/-- Separated morphisms are those with universally closed diagonal (the diagonal is always an
immersion, and an immersion with closed image is a closed immersion). -/
theorem isSeparated_eq_diagonal_universallyClosed :
    @IsSeparated = MorphismProperty.diagonal @UniversallyClosed := by
  rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
  ext X Y f
  show IsClosedImmersion (pullback.diagonal f) ↔ UniversallyClosed (pullback.diagonal f)
  constructor
  · intro h
    infer_instance
  · intro h
    exact IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range

/-- Separatedness satisfies fpqc descent. -/
instance isSeparated_descendsAlong :
    MorphismProperty.DescendsAlong (@IsSeparated) (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  rw [isSeparated_eq_diagonal_universallyClosed]
  infer_instance

/-- Properness satisfies fpqc descent. -/
instance isProper_descendsAlong :
    MorphismProperty.DescendsAlong (@IsProper) (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  rw [isProper_eq]
  infer_instance

/-- Local quasi-finiteness descends along surjective morphisms, for a locally-finite-type
morphism whose base change is quasi-compact. -/
theorem locallyQuasiFinite_of_isPullback {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [Surjective f] [LocallyOfFiniteType g]
    [LocallyQuasiFinite fst] [QuasiCompact fst] : LocallyQuasiFinite g := by
  refine LocallyQuasiFinite.of_finite_preimage_singleton g fun z => ?_
  obtain ⟨x, hx⟩ := f.surjective z
  refine ((fst.finite_preimage_singleton x).image snd).subset ?_
  intro y hy
  obtain ⟨a, ha1, ha2⟩ := Scheme.exists_preimage_of_isPullback h x y (by rw [hx]; exact hy.symm)
  exact ⟨a, ha1, ha2⟩

/-- Finiteness satisfies fpqc descent. -/
instance isFinite_descendsAlong :
    MorphismProperty.DescendsAlong (@IsFinite) (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have : IsFinite fst := hfst
    have : Surjective f := hf.1.1
    have : IsProper g :=
      of_isPullback_of_descendsAlong (P := @IsProper) h hf (inferInstanceAs (IsProper fst))
    have : LocallyQuasiFinite g := locallyQuasiFinite_of_isPullback h
    exact IsFinite.of_isProper_of_locallyQuasiFinite g

/-- `Spec L → Spec K` is flat and surjective (`L/K` is faithfully flat). -/
theorem specMap_flat_surjective (K L : Type) [Field K] [Field L] [Algebra K L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  apply (flat_and_surjective_SpecMap_iff _).mpr
  rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
  infer_instance

/-- **FS1b′ is proved.** -/
theorem finiteDescends : FiniteDescends := by
  intro K L _ _ _ X Y g hfin
  set φ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  obtain ⟨h1, h2⟩ := specMap_flat_surjective K L
  have hY : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (pullback.fst Y.hom φ) :=
    ⟨⟨MorphismProperty.pullback_fst (P := @Surjective) _ _ h2,
      MorphismProperty.pullback_fst (P := @Flat) _ _ h1⟩,
      MorphismProperty.pullback_fst (P := @QuasiCompact) _ _ (inferInstanceAs (QuasiCompact φ))⟩
  have hsq : IsPullback ((Over.pullback φ).map g).left (pullback.fst X.hom φ)
      (pullback.fst Y.hom φ) g.left := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback Y.hom φ).flip
    · have e1 : ((Over.pullback φ).map g).left ≫ pullback.snd Y.hom φ = pullback.snd X.hom φ := by
        simp
      have e2 : g.left ≫ Y.hom = X.hom := Over.w g
      rw [e1, e2]
      exact (IsPullback.of_hasPullback X.hom φ).flip
    · simp
  exact of_isPullback_of_descendsAlong (P := @IsFinite) hsq hY hfin

end FS1Descend

namespace G0FibreSimple
/-- (g0-assemble2) the two verbatim copies of FS1b′ agree. -/
theorem finiteDescends_copy : FS1Descend.FiniteDescends ↔ FiniteDescends := Iff.rfl
/-- FS1b′ is proved (fs1-descend). -/
theorem finiteDescends_proof : FiniteDescends := FS1Descend.finiteDescends
end G0FibreSimple

/-! ## g0-assemble2: mul-rigidity (scratch/mul-rigidity/MulRigidity.lean lines 3-604 verbatim, minus its verbatim
copies of `G0FibreSimple.RigidityHom` (L190-195) and `G0FibreSimple.MulIsogeny` (L316-323), which part 40 defines) -/


/-!
# mul-rigidity: the textbook leaf `RigidityHom` proved from Mathlib

`RigidityHom` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4‴). The proof
follows Mathlib's proof that proper geometrically integral group schemes are commutative
(`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`, Stacks 0BFD),
with the commutator replaced by an arbitrary `c : G ⊗ G ⟶ Z` that is constant on `{e} × G` and on
`G × {e}` (the rigidity lemma, Mumford §4).
-/

noncomputable section

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {K : Type u} [Field K]

theorem isClosedImmersion_point (G : Over (Spec (.of K))) (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    IsClosedImmersion x.left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom x.left (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Rigidity lemma (two-sided form), over an algebraically closed field.** Let `G` be proper
over `K` with `G ×_K G` integral, `Z` separated of finite type, and `c : G × G → Z` with
`c(e, y) = z` and `c(x, e) = z` (as morphisms, for all `T`-points). Then `c` is constant. -/
theorem rigidity_algClosed [IsAlgClosed K]
    (G Z : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ G) (z : 𝟙_ (Over (Spec (.of K))) ⟶ Z) (c : G ⊗ G ⟶ Z)
    (h1 : ∀ (T : Over (Spec (.of K))) (y : T ⟶ G), lift (toUnit T ≫ e) y ≫ c = toUnit T ≫ z)
    (h2 : ∀ (T : Over (Spec (.of K))) (x : T ⟶ G), lift x (toUnit T ≫ e) ≫ c = toUnit T ≫ z) :
    c = toUnit _ ≫ z := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : IsClosedImmersion e.left := isClosedImmersion_point G e
  have : Nonempty G.left := ⟨e.left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsSeparated (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (c.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : IsClosedImmersion ((lift e z).left ≫ (fst G Z).left) := by
    simpa using inferInstanceAs (IsClosedImmersion e.left)
  have : IsClosedImmersion (lift e z).left := .of_comp _ (g := (fst G Z).left)
  let gm : G ⊗ G ⟶ G ⊗ Z := lift (fst _ _) c
  have : IsProper (gm.left ≫ (fst G Z).left) := by simpa [gm]
  have : IsProper gm.left := .of_comp _ (fst G Z).left
  ext1
  have H : gm.left '' ((fst G G).left ⁻¹' {e.left point}) ⊆ {(lift e z).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift e z).left.isClosedMap _ hpoint).preimage gm.left.continuous).isOpen_compl
      · exact (e.left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨p, hp⟩, hpe⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : p point = c₀ := congr(($hpe).1)
    let pt : 𝟙_ (Over S) ⟶ G ⊗ G := Over.homMk p hp
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (pt ≫ snd G G)
    have : p ≫ pullback.fst G.hom G.hom = e.left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : p = fc.left ≫ (e ▷ G).left := by dsimp; ext <;> simp [fc, pt, S, this]
    have H₂ : fc ≫ e ▷ G ≫ gm = lift e z := by
      have h1' := h1 _ (pt ≫ snd G G)
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at h1'
      ext1
      · simp [fc, gm, S]
      · simpa [fc, gm, S] using h1'
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    gm.left (fst G Z).left (e.left point) (by
      dsimp [-Scheme.Hom.comp_base, gm]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset H)
  have H (x : U) : ((pullback.fst G.hom Z.hom) ⁻¹' {x.1} ∩ Set.range ⇑gm.left).Finite := by
    refine ((((gm.left.imageι ≫ (fst G Z).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ gm.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G Z).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact gm.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq Z.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xe : (G ⊗ Z).left := (lift (fst G G) (toUnit _ ≫ z)).left y
    have hgm : lift (fst G G) (toUnit _ ≫ e) ≫ gm = lift (fst G G) (toUnit _ ≫ z) := by
      ext1
      · simp [gm]
      · simpa [gm] using h2 _ (fst G G)
    have : gm.left y = xe := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ gm.left.continuous
        gm.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, gm])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨(lift (fst G G) (toUnit _ ≫ e)).left y, subset_closure ?_, ?_⟩
        · rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, ← Over.comp_left,
            lift_fst]
        · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hgm]
    convert congr((snd G Z).left $this) using 1
    · simp [gm, ← Scheme.Hom.comp_apply]
    · simp only [xe]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
  · simp

/-- **A pointed morphism of proper group schemes is a homomorphism, over an algebraically closed
field** (rigidity, Mumford §4 Cor. 1). Apply `rigidity_algClosed` to
`c = (μ ≫ h) * ((h ⊗ h) ≫ μ)⁻¹`. -/
theorem isMonHom_of_algClosed [IsAlgClosed K]
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  have hone : ∀ (T : Over (Spec (.of K))), (1 : T ⟶ G) ≫ h = 1 := fun T => by
    rw [Hom.one_def, Hom.one_def, Category.assoc, h0]
  have key := rigidity_algClosed G B η[G] η[B] ((μ ≫ h) * ((h ⊗ₘ h) ≫ μ)⁻¹)
    (fun T y => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.one_mul, hone, _root_.one_mul, mul_inv_cancel,
        Hom.one_def])
    (fun T x => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.mul_one, hone, _root_.mul_one, mul_inv_cancel,
        Hom.one_def])
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact ⟨h0, key⟩

/-- **Rigidity over any field** (Mumford §4 Cor. 1 / Milne Cor. 2.2): base change to `K̄` and
`isMonHom_of_algClosed`; `Over.pullback` along `Spec K̄ → Spec K` is faithful and monoidal. -/
theorem isMonHom_of_geometricallyIntegral
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom]
    [GeometricallyIntegral G.hom] [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback f
  let G' := F.obj G
  let B' := F.obj B
  have : IsProper G'.hom := by dsimp [G', F]; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G', F]; infer_instance
  have : IsSeparated B'.hom := by dsimp [B', F]; infer_instance
  have : LocallyOfFiniteType B'.hom := by dsimp [B', F]; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  let : GrpObj B' := Functor.grpObjObj
  have h0' : η[G'] ≫ F.map h = η[B'] := by
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, ← F.map_comp, h0]
  have := isMonHom_of_algClosed G' B' (F.map h) h0'
  refine ⟨h0, F.map_injective ?_⟩
  have hm := IsMonHom.mul_hom (F.map h)
  rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc]
    at hm
  simp only [← F.map_comp] at hm
  exact (cancel_epi _).mp hm

end MulRigidity

/-! ## The leaf, copied verbatim, and its proof -/

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj


/-- **`RigidityHom` holds** (proved from Mathlib; no new hypotheses). -/
theorem rigidityHom : RigidityHom := fun _ _ A B h h0 =>
  MulRigidity.isMonHom_of_geometricallyIntegral A.X B.X h h0

end G0FibreSimple



/-!
# mul-rigidity: the textbook leaf `MulIsogeny` reduced to smaller named Props

`MulIsogeny` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4″). Mathlib
proves "finite and surjective" from local properties of `[n]`:
* proper (`A` proper) and locally quasi-finite give finite (Zariski's main theorem, Mathlib
  `IsFinite.of_isProper_of_locallyQuasiFinite`, Stacks 02LS);
* a locally quasi-finite closed self-map of an irreducible Noetherian scheme is surjective
  (`surjective_of_lqf_self`, generic-point orbit), so `QuasiFiniteEndSurjective` is proved;
* formally unramified + locally of finite type gives locally quasi-finite;
* `[n]` is formally unramified once the unit section of `A[n]` is an open immersion
  (`diagonal_isPullback`: `Δ_f` is a base change of that section).
Chain: `KerUnitOpenOfCotangentSurj` + `CotangentMulN` (glue, unproved) ⇒ `KerUnitOpen` (leaf,
implied by the published `MulEtale`) ⇒ `MulUnramified` ⇒ `MulIsogeny`.
-/

noncomputable section

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- Formally unramified and locally of finite type implies locally quasi-finite (Mathlib's algebra
instance `Algebra.QuasiFinite` from `EssFiniteType` and `FormallyUnramified`, made affine-local). -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h1 : (f.appLE U V e).hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified f inferInstance U V e
  have h2 : (f.appLE U V e).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

variable {K : Type} [Field K]

/-- A `K`-morphism between abelian varieties is proper (source proper, target separated). -/
theorem isProper_left (A B : PkgI3.AbVar K) (f : A.X ⟶ B.X) : IsProper f.left := by
  have : IsProper (f.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp f.left B.X.hom

/-- **Glue.** A locally quasi-finite open `K`-endomorphism of an abelian variety is finite and
surjective. -/
theorem isIsogenyMor_of_lqf_of_isOpenMap (A : PkgI3.AbVar K) (f : A.X ⟶ A.X)
    [LocallyQuasiFinite f.left] (ho : IsOpenMap f.left.base) : PkgI3.AbVar.IsIsogenyMor f := by
  have := isProper_left A A f
  refine ⟨IsFinite.of_isProper_of_locallyQuasiFinite f.left, ⟨?_⟩⟩
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have hcl : IsClopen (Set.range f.left.base) :=
    ⟨f.left.isClosedMap.isClosed_range, ho.isOpen_range⟩
  have hne : (Set.range f.left.base).Nonempty :=
    ⟨_, ⟨η[A.X].left (IsLocalRing.closedPoint K), rfl⟩⟩
  exact Set.range_eq_univ.mp (hcl.eq_univ hne)

/-- Under a locally quasi-finite morphism, a strict specialization maps to two distinct points
(the fibres are discrete, Mathlib `Scheme.Hom.isDiscrete_preimage_singleton`). -/
theorem ne_of_specializes_of_lqf {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x y : X} (hxy : x ⤳ y) (hne : x ≠ y) : f x ≠ f y := by
  intro heq
  have hd := (f.isDiscrete_preimage_singleton (f y)).to_subtype
  let x' : (f.base ⁻¹' {f y} : Set X) := ⟨x, heq⟩
  let y' : (f.base ⁻¹' {f y} : Set X) := ⟨y, rfl⟩
  have h' : x' ⤳ y' := (subtype_specializes_iff x' y').mpr hxy
  exact hne (congrArg Subtype.val h'.eq)

/-- **A locally quasi-finite closed self-map of an irreducible Noetherian scheme is
surjective.** If `f ξ ≠ ξ` for the generic point `ξ`, then `ξ ⤳ f ξ ⤳ f² ξ ⤳ ⋯` are strict
specializations (continuity, and `ne_of_specializes_of_lqf`), so the closures `cl{fᵐ ξ}` form a
strictly decreasing chain of closed sets, contradicting Noetherianity. So `ξ ∈ range f`, which is
closed, hence everything. -/
theorem surjective_of_lqf_self {X : Scheme} [IrreducibleSpace X] [TopologicalSpace.NoetherianSpace X]
    (f : X ⟶ X) [LocallyQuasiFinite f] (hc : IsClosedMap f.base) :
    Function.Surjective f.base := by
  set ξ := genericPoint X
  have hξ : ∀ x : X, ξ ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hfix : f ξ = ξ := by
    by_contra hne
    let s : ℕ → X := fun m => (f.base)^[m] ξ
    have hs : ∀ m, s m ⤳ s (m + 1) ∧ s m ≠ s (m + 1) := by
      intro m
      induction m with
      | zero => exact ⟨hξ _, fun h => hne h.symm⟩
      | succ m ih =>
        have e1 : s (m + 1) = f (s m) := Function.iterate_succ_apply' _ _ _
        have e2 : s (m + 1 + 1) = f (s (m + 1)) := Function.iterate_succ_apply' _ _ _
        rw [e1, e2]
        exact ⟨ih.1.map f.base.hom.continuous, ne_of_specializes_of_lqf f ih.1 ih.2⟩
    let c : ℕ → TopologicalSpace.Closeds X := fun m => ⟨closure {s m}, isClosed_closure⟩
    have hc' : StrictAnti c := by
      refine strictAnti_nat_of_succ_lt fun m => ?_
      refine lt_of_le_of_ne ?_ ?_
      · change closure {s (m + 1)} ⊆ closure {s m}
        exact specializes_iff_closure_subset.mp (hs m).1
      · intro h
        have h2 : closure {s (m + 1)} = closure {s m} := congrArg SetLike.coe h
        exact (hs m).2 (inseparable_iff_closure_eq.mpr h2.symm).eq
    exact not_strictAnti_of_wellFoundedLT c hc'
  intro y
  have hy : y ∈ closure {ξ} := specializes_iff_mem_closure.mp (hξ y)
  exact (hc.isClosed_range.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr ⟨ξ, hfix⟩)) hy

end MulRigidity

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj


end G0FibreSimple

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Leaf (Mumford, *Abelian varieties*, §4 Application 2 and §6: `n_X` is separable when
`char k ∤ n`; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2: `n_A` is étale iff
`char k ∤ n`; locators UNVERIFIED).** In characteristic `0`, `[n]` is étale for `n ≠ 0`. A
consequence of the published statement (only characteristic `0`). -/
def MulEtale : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    Etale ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (the infinitesimal half of `MulEtale`; Mumford §4: `d(n_X) = n` on the tangent space
at `0`, so `n_X^* ω = n ω` for invariant differentials; locator UNVERIFIED).** In characteristic
`0`, `[n]` is formally unramified (`Ω_{[n]} = 0`) for `n ≠ 0`. Implied by `MulEtale`
(`mulUnramified_of_mulEtale`). -/
def MulUnramified : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    FormallyUnramified ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (dimension theory; Mumford §4 / Milne, *Abelian varieties*, Prop. 8.1: a homomorphism
of abelian varieties of the same dimension with finite kernel is surjective, an isogeny; locators
UNVERIFIED).** A locally quasi-finite endomorphism of an abelian variety is surjective
(any characteristic). -/
def QuasiFiniteEndSurjective : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (f : PkgI3.AbVar.End A),
    LocallyQuasiFinite f.hom.left → Surjective f.hom.left

theorem mulUnramified_of_mulEtale (h : MulEtale) : MulUnramified := by
  intro k _ _ A n hn
  have := h k A n hn
  infer_instance

/-- **`MulIsogeny` from `MulEtale`** (glue proved here). -/
theorem mulIsogeny_of_mulEtale (h : MulEtale) : G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact isIsogenyMor_of_lqf_of_isOpenMap A _ (Scheme.Hom.isOpenMap _)

/-- **`MulIsogeny` from `MulUnramified` and `QuasiFiniteEndSurjective`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified (h1 : MulUnramified) (h2 : QuasiFiniteEndSurjective) :
    G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h1 k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, h2 k A _ inferInstance⟩

/-- **`QuasiFiniteEndSurjective` holds** (proved from Mathlib; it is not a leaf). -/
theorem quasiFiniteEndSurjective : QuasiFiniteEndSurjective := by
  intro k _ A f hf
  have := isProper_left A A f.hom
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : IsNoetherian A.X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian A.X.hom }
  exact ⟨surjective_of_lqf_self f.hom.left f.hom.left.isClosedMap⟩

/-- **`MulIsogeny` from the single leaf `MulUnramified`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified' (h : MulUnramified) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified h quasiFiniteEndSurjective

end MulRigidity


/-! ## `MulUnramified` reduced to a statement at the origin of the kernel `A[n]` -/

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K]

/-- The unit section `Spec K → ker f = A ×_{f, A, e} Spec K` of the kernel of a homomorphism. -/
def kerUnit (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    𝟙_ (Over (Spec (.of K))) ⟶ pullback f η[A.X] :=
  pullback.lift η[A.X] (𝟙 _) (by rw [IsMonHom.one_hom, Category.id_comp])

/-- `(x, y) ↦ x⁻¹ y : A ×_{f, A, f} A → ker f`. -/
def diffKer (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    pullback f f ⟶ pullback f η[A.X] :=
  pullback.lift ((pullback.fst f f)⁻¹ * pullback.snd f f) (toUnit _) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, pullback.condition, inv_mul_cancel, Hom.one_def])

/-- **The diagonal of a homomorphism `f` is the base change of the unit section of `ker f`**
along `(x, y) ↦ x⁻¹ y` (the square is cartesian: `x⁻¹ y = e ⇔ x = y`). -/
theorem diagonal_isPullback (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    IsPullback (toUnit A.X) (pullback.diagonal f) (kerUnit A f) (diffKer A f) := by
  have key : ∀ {T : Over (Spec (.of K))} (a : T ⟶ pullback f f),
      a ≫ diffKer A f ≫ pullback.fst f η[A.X] = (a ≫ pullback.fst f f)⁻¹ * (a ≫ pullback.snd f f) := by
    intro T a
    simp only [diffKer, pullback.lift_fst, MonObj.comp_mul, GrpObj.comp_inv]
  refine IsPullback.flip ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ pullback.fst f f)
    ?_ ?_ ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, key, pullback.diagonal_fst, pullback.diagonal_snd, inv_mul_cancel,
        Category.assoc]
      simp only [kerUnit, pullback.lift_fst, Hom.one_def]
    · exact toUnit_unique _ _
  · intro c
    have hc := congrArg (· ≫ pullback.fst f η[A.X]) c.condition
    simp only [Category.assoc] at hc
    simp only [kerUnit, pullback.lift_fst] at hc
    rw [key, toUnit_unique c.snd (toUnit _), ← Hom.one_def, inv_mul_eq_one] at hc
    apply pullback.hom_ext
    · simp
    · simp [hc]
  · intro c
    exact toUnit_unique _ _
  · intro c m hm _
    rw [← hm, Category.assoc, pullback.diagonal_fst, Category.comp_id]

/-- **Glue.** If the unit section of `ker f` is an open immersion, the homomorphism `f` is formally
unramified (its diagonal is an open immersion, as a base change of the unit section). -/
theorem formallyUnramified_of_kerUnit (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f]
    (h : IsOpenImmersion (kerUnit A f).left) : FormallyUnramified f.left := by
  have hP := (Over.forget _).map_isPullback (diagonal_isPullback A f)
  have h1 : IsOpenImmersion (pullback.diagonal f).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hP h
  let e := PreservesPullback.iso (Over.forget (Spec (.of K))) f f
  have he : pullback.diagonal f.left = (pullback.diagonal f).left ≫ e.hom := by
    apply pullback.hom_ext
    · rw [pullback.diagonal_fst, Category.assoc]
      erw [PreservesPullback.iso_hom_fst]
      show 𝟙 _ = (pullback.diagonal f).left ≫ (pullback.fst f f).left
      rw [← Over.comp_left, pullback.diagonal_fst]
      rfl
    · rw [pullback.diagonal_snd, Category.assoc]
      erw [PreservesPullback.iso_hom_snd]
      show 𝟙 _ = (pullback.diagonal f).left ≫ (pullback.snd f f).left
      rw [← Over.comp_left, pullback.diagonal_snd]
      rfl
  have : IsOpenImmersion (pullback.diagonal f.left) := by rw [he]; infer_instance
  infer_instance

/-- **Leaf (Mumford, *Abelian varieties*, §4, Application 2 and §6: `A[n]` is étale, of order
`n^{2g}`, when `char k ∤ n`; equivalently `d[n] = n` on the tangent space at `0`; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Thm 8.2; locators UNVERIFIED).** In characteristic `0`, for
`n ≠ 0`, the unit section of the kernel `A[n] = A ×_{[n], A, e} Spec k` is an open immersion
(`A[n]` is unramified over `k` at the origin: its tangent space there, `ker(n · : Lie A → Lie A)`,
vanishes). A consequence of "`A[n]` is étale over `k`" (a section of an étale separated morphism
is an open immersion; `kerUnitOpen_of_mulEtale`). -/
def KerUnitOpen : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    IsOpenImmersion (kerUnit A ((n : PkgI3.AbVar.End A).hom)).left

/-- A section of a formally unramified morphism locally of finite type is an open immersion
(Stacks 024T; from Mathlib's `isOpenImmersion_diagonal` and
`MorphismProperty.hasOfPostcompProperty_iff_le_diagonal`). -/
theorem isOpenImmersion_of_section {X Y : Scheme} (s : Y ⟶ X) (q : X ⟶ Y)
    [FormallyUnramified q] [LocallyOfFiniteType q] (h : s ≫ q = 𝟙 _) : IsOpenImmersion s := by
  set gr : Y ⟶ pullback (s ≫ q) q := pullback.lift (𝟙 Y) s (by simp)
  have e : s = gr ≫ pullback.snd _ _ := by simp [gr]
  rw [e]
  have h1 : IsOpenImmersion gr :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pullback_lift_diagonal_isPullback s q)
      (FormallyUnramified.isOpenImmersion_diagonal q)
  have h2 : IsOpenImmersion (pullback.snd (s ≫ q) q) :=
    MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ _
      (by rw [h]; exact (inferInstance : IsOpenImmersion (𝟙 Y)))
  infer_instance

/-- **`KerUnitOpen` is a consequence of `MulEtale`** (so it is implied by the published
statement): the kernel is a base change of `[n]`, hence étale over `k`, and its unit section is a
section of an étale morphism. -/
theorem kerUnitOpen_of_mulEtale (h : MulEtale) : KerUnitOpen := by
  intro k _ _ A n hn
  have hE : Etale ((n : PkgI3.AbVar.End A).hom).left := h k A n hn
  have hP := (Over.forget _).map_isPullback
    (IsPullback.of_hasPullback ((n : PkgI3.AbVar.End A).hom) η[A.X])
  have : Etale (pullback.snd ((n : PkgI3.AbVar.End A).hom) η[A.X]).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hP hE
  refine isOpenImmersion_of_section _ (pullback.snd ((n : PkgI3.AbVar.End A).hom) η[A.X]).left ?_
  rw [← Over.comp_left]
  simp [kerUnit]

/-- `MulUnramified` from `KerUnitOpen` (glue proved here). -/
theorem mulUnramified_of_kerUnitOpen (h : KerUnitOpen) : MulUnramified := by
  intro k _ _ A n hn
  exact formallyUnramified_of_kerUnit A _ (h k A n hn)

/-- **`MulIsogeny` from the single leaf `KerUnitOpen`.** -/
theorem mulIsogeny_of_kerUnitOpen (h : KerUnitOpen) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified' (mulUnramified_of_kerUnitOpen h)

end MulRigidity


/-! ## `KerUnitOpen` reduced to two glue statements on the cotangent space at the origin -/

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K]

/-- The origin of `A`, as a point of the underlying space. -/
def origin (A : PkgI3.AbVar K) : A.X.left := η[A.X].left (IsLocalRing.closedPoint K)

theorem map_origin (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    f.left (origin A) = origin A := by
  have h := congrArg (fun g : 𝟙_ (Over (Spec (.of K))) ⟶ A.X => g.left) (IsMonHom.one_hom f)
  simp only [Over.comp_left] at h
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun g : (𝟙_ (Over (Spec (.of K)))).left ⟶ A.X.left => g (IsLocalRing.closedPoint K)) h)

/-- The local ring `𝒪_{A,0}` at the origin. -/
abbrev O0 (A : PkgI3.AbVar K) : CommRingCat := A.X.left.presheaf.stalk (origin A)

/-- The local endomorphism `f^♯ : 𝒪_{A,0} → 𝒪_{A,0}` of a homomorphism `f` (which fixes `0`). -/
def stalkEndo (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] : O0 A ⟶ O0 A :=
  (A.X.left.presheaf.stalkCongr (Inseparable.of_eq (map_origin A f).symm)).hom ≫
    f.left.stalkMap (origin A)

instance (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] : IsLocalHom (stalkEndo A f).hom := by
  unfold stalkEndo
  rw [CommRingCat.hom_comp]
  infer_instance

/-- The cotangent map `m₀/m₀² → m₀/m₀²` of a homomorphism `f` at the origin. -/
def cotangentMap (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    IsLocalRing.CotangentSpace (O0 A) →ₗ[ℤ] IsLocalRing.CotangentSpace (O0 A) :=
  Ideal.mapCotangent _ _ (stalkEndo A f).hom.toIntAlgHom (fun x hx => by
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (isUnit_of_map_unit (stalkEndo A f).hom x hu))

/-- **Glue (commutative algebra of the fibre `ker f`; Nakayama).** For a homomorphism `f : A → A`
over `k` whose cotangent map at the origin is surjective, the unit section of `ker f` is an open
immersion. *Why true* (STANDARD): `𝒪_{ker f, 0} = 𝒪_{A,0} / f^♯(m₀)𝒪_{A,0}` (the fibre of `f`
over the rational point `0`), so surjectivity gives `m₀ = f^♯(m₀)𝒪 + m₀²`, hence
`m₀ = f^♯(m₀)𝒪` by Nakayama, so `𝒪_{ker f, 0} = k`; a rational point of a Noetherian scheme with
local ring a field is isolated, and the open point is `Spec k`. Glue, unproved. -/
def KerUnitOpenOfCotangentSurj : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (f : A.X ⟶ A.X) [IsMonHom f],
    Function.Surjective (cotangentMap A f) → IsOpenImmersion (kerUnit A f).left

/-- **Glue (the group law to first order; Mumford §4, `d(n_X) = n`, UNVERIFIED locator).** The
cotangent map of `[n]` at the origin is multiplication by `n`, for every `n ∈ ℤ` and in every
characteristic. *Why true* (STANDARD): the unit axioms give `μ^♯(φ) ≡ φ ⊗ 1 + 1 ⊗ φ` modulo
`m ⊗ m` on cotangent spaces, so the cotangent map of `f * g = μ ∘ (f, g)` is the sum of those of
`f` and `g`; induct on `n`. Glue, unproved. -/
def CotangentMulN : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (n : ℤ),
    cotangentMap A ((n : PkgI3.AbVar.End A).hom) = n • LinearMap.id

/-- The residue field at the origin has characteristic `0` when `k` does. -/
theorem charZero_residueField [CharZero K] (A : PkgI3.AbVar K) :
    CharZero (IsLocalRing.ResidueField (O0 A)) := by
  let φ : K →+* IsLocalRing.ResidueField (O0 A) :=
    (IsLocalRing.residue (O0 A)).comp ((A.X.left.presheaf.Γgerm (origin A)).hom.comp
      ((A.X.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))
  exact (RingHom.charZero_iff φ.injective).mp inferInstance

/-- **`KerUnitOpen` from the two glue statements** (proved here: in characteristic `0`,
multiplication by `n ≠ 0` is bijective on the cotangent space, a vector space over the residue
field). -/
theorem kerUnitOpen_of_cotangent (h1 : KerUnitOpenOfCotangentSurj) (h2 : CotangentMulN) :
    KerUnitOpen := by
  intro k _ _ A n hn
  apply h1
  rw [h2]
  have := charZero_residueField A
  have hn' : (n : IsLocalRing.ResidueField (O0 A)) ≠ 0 := Int.cast_ne_zero.mpr hn
  intro v
  refine ⟨((n : IsLocalRing.ResidueField (O0 A))⁻¹) • v, ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply,
    ← Int.cast_smul_eq_zsmul (IsLocalRing.ResidueField (O0 A)), smul_smul, mul_inv_cancel₀ hn',
    one_smul]

/-- **`MulIsogeny` from glue alone**: the two cotangent-space glue statements imply it, with no
literature leaf. -/
theorem mulIsogeny_of_cotangent (h1 : KerUnitOpenOfCotangentSurj) (h2 : CotangentMulN) :
    G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_kerUnitOpen (kerUnitOpen_of_cotangent h1 h2)

end MulRigidity

end
end

/-! ## g0-assemble2: height-bc (scratch/height-bc/Final.lean lines 2-end, verbatim except that the line
`open PkgI3 (AbVar)` is deleted (as for part 61)) -/

/-! # height-bc: glue H4a (`ModelHeightBaseChange`) and `HodgeLineBaseChange`

Self-contained (Mathlib + project only; no `sorry`, no `axiom`).
* Verbatim copies: `IsBaseChangeOf`, `ModelHeightBaseChange` (from `scratch/h5-glue/H5Final.lean`,
  over the kernel's objects); `ModelHeightBaseChangeLE`, the Arakelov half of H4a,
  `MetrizationBaseChange`, `HodgeLineBaseChange` and `metrizationBaseChange_of_hodgeLine` (from
  `scratch/g0-stablebc/Main.part`, there over a verbatim copy of the same objects).
* Part A (new): the descent half `ModelHeightBaseChangeGE` and the reduction of H4a (`=`) to one
  geometric statement `HodgeLineBaseChangeDescent` (`modelHeightBaseChange_of_descent`).
* Part B (new): the natural map of a base change `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`: `bcProj` (π), `bcMap`
  (stalk map at the origin), `bcCot`, `bcExt`, `bcHodge` (ψ = L' ⊗ ⋀^g π^*), `bcPts` (β on complex
  points); compatibility of germs and Jacobians (`jacDet_bcPts`); half of the lattice clause
  (`span_bcHodge_le`).
* Part C (new): glue statements over the natural map. Proved here: `ptsBaseChangeMul`,
  `ptsBaseChangeBij`, `detLatticeBC_of_omega`, `hodgeSpanBC_of`, `jacobianPullbackSpan_of`,
  `uniformizationLift_of`, `jacobianSemilinear_of`, and the glue statement `GermDerivation`
  itself (`germDerivation`, from the section `GermDer`: germs along `Φ` form a ring
  homomorphism near `0`, germs in `𝔪_ξ` vanish at the unit point, structure sections take the
  value `τ(r)`).
  **Main results** (final form): `modelHeightBaseChange_of_glue4` and
  `hodgeLineBaseChange_of_glue4` (H4a and `HodgeLineBaseChange`, verbatim, from the four glue
  statements `HodgeBCInjective`, `CotangentSpanBC`, `OmegaBaseChange`,
  `UniformizationLiftAnalytic`), and `modelHeightBaseChangeGE_of_main` (the descent half from
  `HodgeBCInjective` and `OmegaBaseChange`). Coarser forms: `_of_final`, `_of_glue5`,
  `_of_five`, `_of_main`, `_of_four`, `_of_glue`. -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-! ## Verbatim copies -/

/-- (copied from h5-neron) -/
def IsBaseChangeOf {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L]
    [Algebra K L] [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) : Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

-- copied verbatim from scratch/h5-glue/H5Final.lean

/-- **Glue H4a.** The height of a fixed smooth model is invariant under base change:
`ω_{𝒢_{L'}} = ω_𝒢 ⊗ 𝓞_{L'}` (flat base change of the conormal sheaf), the Arakelov degree is
multiplied by `[L':L]`, and each `τ' : L' → ℂ` restricts to `τ = τ'|_L` with the same
uniformization. -/
def ModelHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height = 𝒢.height

-- copied verbatim from scratch/g0-stablebc/Main.part

/-- **Glue H4a, the inequality half (used here).** `h(𝒢_{L'}) ≤ h(𝒢)` for a group model `𝒢` and
a base change `𝒢'` of it. Implied by `ModelHeightBaseChange` (`modelHeightBaseChangeLE`
below). Same justification (h5-neron §2): `ω` of a smooth model commutes with base change, the
Arakelov degree is multiplied by `[L':L]`, and `𝒢'(ℂ)_{τ'} = 𝒢(ℂ)_{τ'|_L}`. -/
def ModelHeightBaseChangeLE : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height ≤ 𝒢.height


-- copied verbatim from scratch/g0-stablebc/Main.part (lines 240-500)
/-! ### The Arakelov half of H4a (proved) and the geometric half (glue, stated)

`modelHeight_eq_of_isHodgeBaseChange`: if `D'` over `L'` is obtained from `D` over `L` by base
change (a semilinear injection `ψ` on the Hodge lines, with `⋀^g ω' = 𝓞_{L'} · ψ(⋀^g ω)`,
restricted period lattices and compatible coefficient maps), the model heights agree. The finite
part reduces to fractional ideals (`N(𝔞𝓞_{L'}) = N(𝔞)^{[L':L]}`, def-faltings'
`absNorm_extendedHom`) and the archimedean part to `sum_embeddings_comp`. -/

section ArakelovBC

open scoped nonZeroDivisors

/-- `secIndex` is invariant under an injective linear map. -/
theorem secIndex_map {K : Type*} [Field K] [NumberField K] {V W : Type*} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (f : V →ₗ[𝓞 K] W) (hf : Function.Injective f)
    (Λ : Submodule (𝓞 K) V) (w : V) : secIndex (Λ.map f) (f w) = secIndex Λ w := by
  unfold secIndex
  rw [← Set.image_singleton, ← Submodule.map_span, Submodule.map_toAddSubgroup,
    Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hf

/-- A finite index kills the quotient: `#(Λ/𝓞η) • x ∈ 𝓞η` for `x ∈ Λ`. -/
theorem secIndex_nsmul_mem {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V) (w : V)
    {x : V} (hx : x ∈ Λ) : secIndex Λ w • x ∈ Submodule.span (𝓞 K) {w} :=
  AddSubgroup.nsmul_relIndex_mem (Submodule.span (𝓞 K) {w}).toAddSubgroup hx

variable {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']

/-- **The finite part of base change**: `#(Λ'/𝓞_{L'}ιη) = #(Λ/𝓞_Lη)^{[L':L]}` for
`Λ' = 𝓞_{L'} · ψ(Λ)`. -/
theorem secIndex_baseChange {V V' : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
    [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V'] [Module (𝓞 L') V']
    [IsScalarTower (𝓞 L') L' V'] (hV : Module.finrank L V = 1) (ψ : V →+ V')
    (hsmul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) (Λ : Submodule (𝓞 L) V)
    {w : V} (hηΛ : w ∈ Λ) (hη : w ≠ 0) (hη' : ψ w ≠ 0) (hi : secIndex Λ w ≠ 0) :
    secIndex (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w) = secIndex Λ w ^ Module.finrank L L' := by
  -- coordinates `c ↦ c • w` and `c ↦ c • ιη`
  let φ : L →ₗ[𝓞 L] V := (LinearMap.toSpanSingleton L V w).restrictScalars (𝓞 L)
  let φ' : L' →ₗ[𝓞 L'] V' := (LinearMap.toSpanSingleton L' V' (ψ w)).restrictScalars (𝓞 L')
  have hφ : ∀ c, φ c = c • w := fun c => rfl
  have hφ' : ∀ c, φ' c = c • ψ w := fun c => rfl
  have hφinj : Function.Injective φ := fun a b h => by
    rw [hφ, hφ] at h
    exact smul_left_injective L hη h
  have hφ'inj : Function.Injective φ' := fun a b h => by
    rw [hφ', hφ'] at h
    exact smul_left_injective L' hη' h
  have hφsurj : Function.Surjective φ := fun v => by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hη).mp hV v
    exact ⟨c, hc⟩
  set I : Submodule (𝓞 L) L := Λ.comap φ with hI
  have hΛ : Λ = I.map φ := (Submodule.map_comap_eq_of_surjective hφsurj Λ).symm
  have h1I : (1 : L) ∈ I := by simpa [hI, hφ] using hηΛ
  have hidx : secIndex I 1 = secIndex Λ w := by
    conv_rhs => rw [hΛ, show w = φ 1 by simp [hφ]]
    exact (secIndex_map φ hφinj I 1).symm
  -- `ψ(Λ) = φ'(L'-image of I)`
  have himg : ψ '' (Λ : Set V) = φ' '' (algebraMap L L' '' (I : Set L)) := by
    rw [hΛ, Submodule.map_coe, Set.image_image, Set.image_image]
    refine Set.image_congr fun c _ => ?_
    rw [hφ, hφ', hsmul]
  have hspan : Submodule.span (𝓞 L') (ψ '' (Λ : Set V)) =
      (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))).map φ' := by
    rw [himg, Submodule.map_span]
  have hidx' : secIndex (Submodule.span (𝓞 L') (ψ '' (Λ : Set V))) (ψ w) =
      secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 := by
    rw [hspan, show ψ w = φ' 1 by simp [hφ']]
    exact secIndex_map φ' hφ'inj _ 1
  -- `I` is a fractional ideal
  set N := secIndex I 1 with hN
  have hN0 : N ≠ 0 := hidx ▸ hi
  have hfrac : IsFractional (𝓞 L)⁰ I := by
    refine ⟨(N : 𝓞 L), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0), fun b hb => ?_⟩
    have hm := secIndex_nsmul_mem I 1 hb
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← ha, Algebra.smul_def, _root_.mul_one]
  let I₀ : FractionalIdeal (𝓞 L)⁰ L := ⟨I, hfrac⟩
  have hI₀ : (I₀ : Submodule (𝓞 L) L) = I := rfl
  have e1 := secIndex_mul_absNorm I₀ (x := 1) h1I one_ne_zero
  have e2 := secIndex_mul_absNorm (FractionalIdeal.extendedHom L' (𝓞 L') I₀) (x := 1)
    (by
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_extendedHom_eq_span]
      exact Submodule.subset_span ⟨1, h1I, map_one _⟩) one_ne_zero
  rw [FractionalIdeal.coe_extendedHom_eq_span, absNorm_extendedHom, map_one, abs_one] at e2
  rw [map_one, abs_one] at e1
  have e1' : (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I₀ = 1 := e1
  have e2' : (secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 : ℚ) *
      FractionalIdeal.absNorm I₀ ^ Module.finrank L L' = 1 := e2
  rw [← hidx, hidx']
  have key : (secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 : ℚ) =
      (secIndex I 1 : ℚ) ^ Module.finrank L L' := by
    rw [eq_inv_of_mul_eq_one_left e1', eq_inv_of_mul_eq_one_left e2', inv_pow]
  exact_mod_cast key

/-- **Base change data for Hodge data** `D/L ↦ D'/L'` along a semilinear injection `ψ`. -/
structure IsHodgeBaseChange {g : ℕ} {V V' : Type*} [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [AddCommGroup V'] [Module L' V'] [Module (𝓞 L') V']
    (D : HodgeData L g V) (D' : HodgeData L' g V') (ψ : V →+ V') : Prop where
  smul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v
  ne_zero : ∀ v, v ≠ 0 → ψ v ≠ 0
  lattice : D'.lattice = Submodule.span (𝓞 L') (ψ '' D.lattice)
  periods : ∀ τ' : L' →+* ℂ, D'.periods τ' = D.periods (τ'.comp (algebraMap L L'))
  coeff : ∀ (τ' : L' →+* ℂ) v, D'.coeff τ' (ψ v) = D.coeff (τ'.comp (algebraMap L L')) v

/-- **The model height is invariant under base change of Hodge data.** Proved. -/
theorem modelHeight_eq_of_isHodgeBaseChange {g : ℕ} {V V' : Type*} [AddCommGroup V]
    [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V']
    [Module (𝓞 L') V'] [IsScalarTower (𝓞 L') L' V'] (D : HodgeData L g V) (D' : HodgeData L' g V')
    (ψ : V →+ V') (h : IsHodgeBaseChange D D' ψ) : D'.modelHeight = D.modelHeight := by
  obtain ⟨w, hηM, hη, hi⟩ := D.isLattice
  have hη' : ψ w ≠ 0 := h.ne_zero w hη
  have hηM' : ψ w ∈ D'.lattice := by
    rw [h.lattice]; exact Submodule.subset_span ⟨w, hηM, rfl⟩
  rw [D.modelHeight_eq hηM hη, D'.modelHeight_eq hηM' hη']
  have hsec : secIndex D'.lattice (ψ w) = secIndex D.lattice w ^ Module.finrank L L' := by
    rw [h.lattice]
    exact secIndex_baseChange D.finrank_eq_one ψ h.smul D.lattice hηM hη hη' hi
  have hsum : ∑ τ' : L' →+* ℂ, Real.log (torusMetricSq (D'.periods τ') (D'.coeff τ' (ψ w))) =
      Module.finrank L L' *
        ∑ σ : L →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)) := by
    simp only [h.periods, h.coeff]
    exact sum_embeddings_comp (fun σ => Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)))
  rw [hsec, hsum, ← Module.finrank_mul_finrank ℚ L L']
  have hK : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < Module.finrank L L' := by exact_mod_cast Module.finrank_pos
  push_cast
  rw [Real.log_pow]
  field_simp

end ArakelovBC

/-- **Glue H4a, geometric half (stated).** A metrization of a group model `𝒢/𝓞_L` induces one of
its base change `𝒢'/𝓞_{L'}`, by base change of the Hodge data: `ψ` is the natural map
`⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (from `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`), `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)`
(formation of `e*Ω¹` of a smooth group scheme commutes with base change; EGA IV 17.2.3,
UNVERIFIED locator), and at `τ' : L' → ℂ` the uniformization of `𝒢(ℂ)_{τ'|_L}` composed with the
bijection `𝒢(ℂ)_{τ'|_L} ≅ 𝒢'(ℂ)_{τ'}` (universal property of the pullback). Glue (a property of
def-faltings' definitions), STANDARD; not a literature leaf. -/
def MetrizationBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 →
    ∀ (g : ℕ) (Mm : MetrizedModel A L g), Mm.model = 𝒢 →
    ∃ (Mm' : MetrizedModel A L' g) (ψ : Mm.model.hodgeSpace g →+ Mm'.model.hodgeSpace g),
      Mm'.model = 𝒢' ∧ IsHodgeBaseChange Mm.hodge Mm'.hodge ψ

/-- **`ModelHeightBaseChangeLE` from the geometric half.** Proved. -/
theorem modelHeightBaseChangeLE_of_metrization (h : MetrizationBaseChange) :
    ModelHeightBaseChangeLE := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun Mm => le_iInf fun hM => ?_
  obtain ⟨Mm', ψ, hM', hι⟩ := h K A L L' 𝒢 𝒢' h𝒢 g Mm hM
  refine iInf_le_of_le g (iInf_le_of_le Mm' (iInf_le_of_le hM' ?_))
  rw [modelHeight_eq_of_isHodgeBaseChange Mm.hodge Mm'.hodge ψ hι]

/-- **Glue H4a, geometric content, stated without metrized models.** For a base change `𝒢'` of
`𝒢` and each `g`, the natural map `ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (induced by
`𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`):
* is `L`-semilinear over `L → L'` and injective on nonzero vectors, and the Hodge space of `𝒢'` is
  an `L'`-line when that of `𝒢` is an `L`-line (it is `L' ⊗_L` of it);
* carries the lattice: `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)` (formation of `e*Ω¹` of a smooth group
  scheme commutes with base change; EGA IV 17.2.3, UNVERIFIED locator);
* is compatible with uniformizations: an analytic uniformization `Φ` of `𝒢(ℂ)_{τ'|_L}` gives one
  `Φ'` of `𝒢'(ℂ)_{τ'}` with the same kernel (compose with the bijection
  `𝒢(ℂ)_{τ'|_L} ≅ 𝒢'(ℂ)_{τ'}` of the pullback), and if a coefficient map `c` is computed by `Φ` on
  wedges of germs, its `τ'`-semilinear extension `c'` (`c' ∘ ψ = c`) is computed by `Φ'` on wedges
  of germs of `𝒢'` (both sides are `τ'`-semilinear alternating functions of the differentials
  `df'_i`, and they agree on pulled-back germs, which span).
Glue (a property of def-faltings' definitions), STANDARD; not a literature leaf. -/
def HodgeLineBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → ∀ g : ℕ,
    ∃ ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g,
      (∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) ∧
      (∀ v, v ≠ 0 → ψ v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 → Module.finrank L' (𝒢'.hodgeSpace g) = 1) ∧
      𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) ∧
      ∀ (τ' : L' →+* ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
        (Φ : (Fin g → ℂ) → 𝒢.Pts (τ'.comp (algebraMap L L'))),
        𝒢.IsAnalyticUniformization _ Λ Φ →
        ∃ Φ' : (Fin g → ℂ) → 𝒢'.Pts τ', 𝒢'.IsAnalyticUniformization τ' Λ Φ' ∧
          ∀ (c : 𝒢.hodgeSpace g →ₛₗ[τ'.comp (algebraMap L L')] ℂ)
            (c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ),
            (∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f) → (∀ v, c' (ψ v) = c v) →
            ∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f'

/-- **`MetrizationBaseChange` from `HodgeLineBaseChange`.** The Hodge data of `𝒢'`: lattice
`⋀^g ω_{𝒢'}`, restricted period lattices, and the `τ'`-semilinear extension of the coefficient
maps along `ψ` (through the coordinate `c ↦ c · ψ(w)` on the `L'`-line). Proved. -/
theorem metrizationBaseChange_of_hodgeLine (h : HodgeLineBaseChange) :
    MetrizationBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g Mm hM
  subst hM
  obtain ⟨ψ, hsmul, hne, hfin, hlat, harch⟩ := h K A L L' Mm.model 𝒢' h𝒢 g
  obtain ⟨w, hwM, hw, hi⟩ := Mm.hodge.isLattice
  have hw' : ψ w ≠ 0 := hne w hw
  have hfin' : Module.finrank L' (𝒢'.hodgeSpace g) = 1 := hfin Mm.hodge.finrank_eq_one
  -- the coordinate `c ↦ c • ψ w` on the `L'`-line
  have hinj : Function.Injective (LinearMap.toSpanSingleton L' (𝒢'.hodgeSpace g) (ψ w)) :=
    fun a b hab => smul_left_injective L' hw' hab
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton L' (𝒢'.hodgeSpace g) (ψ w)) :=
    fun v => (finrank_eq_one_iff_of_nonzero' (ψ w) hw').mp hfin' v
  let e : L' ≃ₗ[L'] 𝒢'.hodgeSpace g := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have he : ∀ c, e c = c • ψ w := fun c => rfl
  -- the extended coefficient maps
  let lin : ∀ τ' : L' →+* ℂ, L' →ₛₗ[τ'] ℂ := fun τ' =>
    { toFun := fun c => τ' c * Mm.hodge.coeff (τ'.comp (algebraMap L L')) w
      map_add' := fun a b => by rw [map_add, add_mul]
      map_smul' := fun a b => by rw [smul_eq_mul, map_mul, smul_eq_mul, _root_.mul_assoc] }
  let coeff' : ∀ τ' : L' →+* ℂ, 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ := fun τ' =>
    (lin τ').comp e.symm.toLinearMap
  have hcoeff' : ∀ (τ' : L' →+* ℂ) v,
      coeff' τ' (ψ v) = Mm.hodge.coeff (τ'.comp (algebraMap L L')) v := by
    intro τ' v
    obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_nonzero' w hw).mp Mm.hodge.finrank_eq_one v
    have h1 : e.symm (ψ (a • w)) = algebraMap L L' a := by
      rw [LinearEquiv.symm_apply_eq, he, hsmul]
    show lin τ' (e.symm (ψ (a • w))) = _
    rw [h1]
    show τ' (algebraMap L L' a) * _ = _
    rw [map_smulₛₗ, smul_eq_mul]
    rfl
  have hlat' : 𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' Mm.hodge.lattice) := by
    rw [hlat, Mm.lattice_eq]
  let D' : HodgeData L' g (𝒢'.hodgeSpace g) :=
    { lattice := 𝒢'.detLattice g
      finrank_eq_one := hfin'
      isLattice := by
        refine ⟨ψ w, ?_, hw', ?_⟩
        · rw [hlat']; exact Submodule.subset_span ⟨w, hwM, rfl⟩
        · rw [hlat', secIndex_baseChange Mm.hodge.finrank_eq_one ψ hsmul _ hwM hw hw' hi]
          exact pow_ne_zero _ hi
      periods := fun τ' => Mm.hodge.periods (τ'.comp (algebraMap L L'))
      periods_discrete := fun τ' => Mm.hodge.periods_discrete _
      periods_isZLattice := fun τ' => Mm.hodge.periods_isZLattice _
      coeff := coeff'
      coeff_ne_zero := fun τ' h0 => by
        have h2 := hcoeff' τ' w
        rw [h0, LinearMap.zero_apply] at h2
        exact Mm.hodge.coeff_apply_ne_zero _ hw h2.symm }
  let Mm' : MetrizedModel A L' g :=
    { model := 𝒢'
      hodge := D'
      lattice_eq := rfl
      arch := fun τ' => by
        obtain ⟨Φ, hΦ, hc⟩ := Mm.arch (τ'.comp (algebraMap L L'))
        obtain ⟨Φ', hΦ', hc'⟩ := harch τ' _ Φ hΦ
        exact ⟨Φ', hΦ', hc' _ (coeff' τ') hc (hcoeff' τ')⟩ }
  exact ⟨Mm', ψ, rfl,
    { smul := hsmul
      ne_zero := hne
      lattice := hlat'
      periods := fun _ => rfl
      coeff := hcoeff' }⟩


/-! ## Part A (new): the descent half of H4a -/

section DescentArakelov

open scoped nonZeroDivisors

variable {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']

/-- Every complex embedding of `L` extends to `L'`. -/
theorem exists_comp_eq (σ : L →+* ℂ) : ∃ τ' : L' →+* ℂ, τ'.comp (algebraMap L L') = σ := by
  let _ : Algebra L ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic L L' := Algebra.IsAlgebraic.of_finite L L'
  refine ⟨(IsAlgClosed.lift (R := L) (S := L') (M := ℂ)).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift (R := L) (S := L') (M := ℂ)).commutes x

/-- An element of `L` whose image in `L'` is an algebraic integer is an algebraic integer. -/
theorem exists_ringOfIntegers_of_algebraMap {c : L} {a : 𝓞 L'}
    (h : algebraMap (𝓞 L') L' a = algebraMap L L' c) : ∃ y : 𝓞 L, algebraMap (𝓞 L) L y = c := by
  have h1 : IsIntegral ℤ (algebraMap L L' c) :=
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 L')).mpr ⟨a, h⟩
  have h2 : IsIntegral ℤ c :=
    (isIntegral_algHom_iff (algebraMap L L').toIntAlgHom (algebraMap L L').injective).mp h1
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 L)).mp h2

/-- **Descent of finite index**: if `Λ' = 𝓞_{L'} · ψ(Λ)` has finite index over `𝓞_{L'} ψ(w)`,
then `Λ` has finite index over `𝓞_L w` (`Λ` is then a fractional ideal in coordinates). -/
theorem secIndex_ne_zero_of_baseChange {V V' : Type*} [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V']
    [Module (𝓞 L') V'] [IsScalarTower (𝓞 L') L' V'] (hV : Module.finrank L V = 1)
    (ψ : V →+ V') (hsmul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v)
    (Λ : Submodule (𝓞 L) V) {w : V} (hηΛ : w ∈ Λ) (hη : w ≠ 0) (hη' : ψ w ≠ 0)
    (hi' : secIndex (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w) ≠ 0) : secIndex Λ w ≠ 0 := by
  let φ : L →ₗ[𝓞 L] V := (LinearMap.toSpanSingleton L V w).restrictScalars (𝓞 L)
  have hφ : ∀ c, φ c = c • w := fun c => rfl
  have hφinj : Function.Injective φ := fun a b h => by
    rw [hφ, hφ] at h
    exact smul_left_injective L hη h
  have hφsurj : Function.Surjective φ := fun v => by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hη).mp hV v
    exact ⟨c, hc⟩
  set I : Submodule (𝓞 L) L := Λ.comap φ with hI
  have hΛ : Λ = I.map φ := (Submodule.map_comap_eq_of_surjective hφsurj Λ).symm
  have h1I : (1 : L) ∈ I := by simpa [hI, hφ] using hηΛ
  have hidx : secIndex I 1 = secIndex Λ w := by
    conv_rhs => rw [hΛ, show w = φ 1 by simp [hφ]]
    exact (secIndex_map φ hφinj I 1).symm
  set N := secIndex (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w) with hN
  have hfrac : IsFractional (𝓞 L)⁰ I := by
    refine ⟨(N : 𝓞 L), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hi'), fun b hb => ?_⟩
    have hbΛ : b • w ∈ Λ := hb
    have hm := secIndex_nsmul_mem (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w)
      (Submodule.subset_span ⟨_, hbΛ, rfl⟩)
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨a, ha⟩ := hm
    rw [hsmul] at ha
    have h2 : (algebraMap (𝓞 L') L' a) • ψ w = algebraMap L L' ((N : L) * b) • ψ w := by
      rw [algebraMap_smul, ha, map_mul, mul_smul, map_natCast, Nat.cast_smul_eq_nsmul]
    obtain ⟨y, hy⟩ := exists_ringOfIntegers_of_algebraMap (smul_left_injective L' hη' h2)
    refine ⟨y, ?_⟩
    rw [hy, Algebra.smul_def, map_natCast]
  let I₀ : FractionalIdeal (𝓞 L)⁰ L := ⟨I, hfrac⟩
  have e1 := secIndex_mul_absNorm I₀ (x := 1) h1I one_ne_zero
  rw [map_one, abs_one] at e1
  have e1' : (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I₀ = 1 := e1
  rw [← hidx]
  intro h0
  rw [h0] at e1'
  simp at e1'

end DescentArakelov

/-- **Glue H4a, the descent half.** `h(𝒢) ≤ h(𝒢_{L'})` for a base change `𝒢'` of `𝒢`. Together
with `ModelHeightBaseChangeLE` it is `ModelHeightBaseChange`. -/
def ModelHeightBaseChangeGE : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢.height ≤ 𝒢'.height

/-- **Glue H4a, geometric content in both directions** (a property of def-faltings' definitions;
STANDARD, not a literature leaf). For a base change `𝒢'` of `𝒢` and each `g`, there is a map
`ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (the Prop asserts `∃ ψ`; the witness used in Part C is the
natural map `bcHodge`, induced by `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`) satisfying the clauses of
`HodgeLineBaseChange`, with the line clause as an equivalence (`hodgeSpace' = L' ⊗_L hodgeSpace`),
and in addition the *descent* clause: an analytic uniformization `Φ'` of `𝒢'(ℂ)_{τ'}` gives one
`Φ` of `𝒢(ℂ)_σ`, `σ = τ'|_L`, with the same kernel (compose with the bijection
`β : 𝒢'(ℂ)_{τ'} ≅ 𝒢(ℂ)_σ` of the pullback), and a coefficient map `c'` computed by `Φ'` on wedges of
germs of `𝒢'` computes `jacDet Φ` on wedges of germs of `𝒢` through `ψ`
(`ψ(wedge f) = wedge' (f pulled back)`, and the Jacobians agree along the bijection). -/
def HodgeLineBaseChangeDescent : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → ∀ g : ℕ,
    ∃ ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g,
      (∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) ∧
      (∀ v, v ≠ 0 → ψ v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 ↔ Module.finrank L' (𝒢'.hodgeSpace g) = 1) ∧
      𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) ∧
      (∀ (τ' : L' →+* ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
        (Φ : (Fin g → ℂ) → 𝒢.Pts (τ'.comp (algebraMap L L'))),
        𝒢.IsAnalyticUniformization _ Λ Φ →
        ∃ Φ' : (Fin g → ℂ) → 𝒢'.Pts τ', 𝒢'.IsAnalyticUniformization τ' Λ Φ' ∧
          ∀ (c : 𝒢.hodgeSpace g →ₛₗ[τ'.comp (algebraMap L L')] ℂ)
            (c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ),
            (∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f) → (∀ v, c' (ψ v) = c v) →
            ∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f') ∧
      (∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ), τ'.comp (algebraMap L L') = σ →
        ∀ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
        𝒢'.IsAnalyticUniformization τ' Λ Φ' →
        ∃ Φ : (Fin g → ℂ) → 𝒢.Pts σ, 𝒢.IsAnalyticUniformization σ Λ Φ ∧
          ∀ c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ, (∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f') →
            ∀ f, c' (ψ (𝒢.wedge f)) = 𝒢.jacDet Φ f)

/-- **The descent half of `HodgeLineBaseChangeDescent`** (all clauses except the forward
uniformization clause); it is what `ModelHeightBaseChangeGE` uses. -/
def HodgeLineDescentHalf : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → ∀ g : ℕ,
    ∃ ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g,
      (∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) ∧
      (∀ v, v ≠ 0 → ψ v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 ↔ Module.finrank L' (𝒢'.hodgeSpace g) = 1) ∧
      𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) ∧
      (∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ), τ'.comp (algebraMap L L') = σ →
        ∀ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
        𝒢'.IsAnalyticUniformization τ' Λ Φ' →
        ∃ Φ : (Fin g → ℂ) → 𝒢.Pts σ, 𝒢.IsAnalyticUniformization σ Λ Φ ∧
          ∀ c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ, (∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f') →
            ∀ f, c' (ψ (𝒢.wedge f)) = 𝒢.jacDet Φ f)

theorem descentHalf_of_descent (h : HodgeLineBaseChangeDescent) : HodgeLineDescentHalf := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨ψ, h1, h2, h3, h4, -, h6⟩ := h K A L L' 𝒢 𝒢' h𝒢 g
  exact ⟨ψ, h1, h2, h3, h4, h6⟩

/-- `HodgeLineBaseChangeDescent` implies `HodgeLineBaseChange`. Proved. -/
theorem hodgeLineBaseChange_of_descent (h : HodgeLineBaseChangeDescent) : HodgeLineBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨ψ, h1, h2, h3, h4, h5, -⟩ := h K A L L' 𝒢 𝒢' h𝒢 g
  exact ⟨ψ, h1, h2, h3.mp, h4, h5⟩

/-- **`ModelHeightBaseChangeGE` from the geometric statement.** A metrization of `𝒢'` gives one
of `𝒢`: lattice `⋀^g ω_𝒢`, and at each `σ : L → ℂ` the data of `𝒢'` at a place `τ'` above `σ`
that maximizes `log ‖ψ w‖²_{τ'}` (the maximum over the fibre is at least the average). Proved. -/
theorem modelHeightBaseChangeGE_of_descentHalf (h : HodgeLineDescentHalf) :
    ModelHeightBaseChangeGE := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun Mm' => le_iInf fun hM' => ?_
  subst hM'
  obtain ⟨ψ, hsmul, hne, hfin, hlat, hdesc⟩ := h K A L L' 𝒢 Mm'.model h𝒢 g
  have hfinL : Module.finrank L (𝒢.hodgeSpace g) = 1 := hfin.mpr Mm'.hodge.finrank_eq_one
  have hlat' : Mm'.hodge.lattice = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) := by
    rw [Mm'.lattice_eq, hlat]
  obtain ⟨s', hs'M, hs', -⟩ := Mm'.hodge.isLattice
  have hex : ∃ w ∈ 𝒢.detLattice g, ψ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hs'
    rw [hlat'] at hs'M
    have hsub : ψ '' (𝒢.detLattice g : Set (𝒢.hodgeSpace g)) ⊆ {0} := by
      rintro _ ⟨x, hx, rfl⟩
      exact hcon x hx
    have h0 := Submodule.span_mono (R := 𝓞 L') hsub hs'M
    simpa using h0
  obtain ⟨w, hwM, hw'⟩ := hex
  have hw : w ≠ 0 := by
    rintro rfl
    exact hw' (map_zero ψ)
  have hψwM : ψ w ∈ Mm'.hodge.lattice := by
    rw [hlat']
    exact Submodule.subset_span ⟨w, hwM, rfl⟩
  have hi' : secIndex Mm'.hodge.lattice (ψ w) ≠ 0 :=
    Mm'.hodge.hodgeBundle.secIndex_ne_zero hψwM hw'
  have hi : secIndex (𝒢.detLattice g) w ≠ 0 :=
    secIndex_ne_zero_of_baseChange hfinL ψ hsmul _ hwM hw hw' (hlat' ▸ hi')
  -- the place above `σ` maximizing the archimedean term
  let F : (L' →+* ℂ) → ℝ := fun τ' =>
    Real.log (torusMetricSq (Mm'.hodge.periods τ') (Mm'.hodge.coeff τ' (ψ w)))
  have hext : ∀ σ : L →+* ℂ, ∃ τ' : L' →+* ℂ, τ'.comp (algebraMap L L') = σ ∧
      ∀ τ'' : L' →+* ℂ, τ''.comp (algebraMap L L') = σ → F τ'' ≤ F τ' := by
    intro σ
    classical
    obtain ⟨τ₀, hτ₀⟩ := exists_comp_eq (L' := L') σ
    have hne' : (Finset.univ.filter
        fun τ' : L' →+* ℂ => τ'.comp (algebraMap L L') = σ).Nonempty :=
      ⟨τ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ₀⟩⟩
    obtain ⟨τ', hτ'm, hmax⟩ := Finset.exists_max_image _ F hne'
    exact ⟨τ', (Finset.mem_filter.mp hτ'm).2,
      fun τ'' h'' => hmax τ'' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h''⟩)⟩
  choose ch hch hmax using hext
  let coeff : ∀ σ : L →+* ℂ, 𝒢.hodgeSpace g →ₛₗ[σ] ℂ := fun σ =>
    { toFun := fun v => Mm'.hodge.coeff (ch σ) (ψ v)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun a v => by
        rw [hsmul, map_smulₛₗ, smul_eq_mul, smul_eq_mul]
        have hσa : (ch σ) (algebraMap L L' a) = σ a := by
          have := congrArg (fun f : L →+* ℂ => f a) (hch σ)
          simpa using this
        rw [hσa] }
  let D : HodgeData L g (𝒢.hodgeSpace g) :=
    { lattice := 𝒢.detLattice g
      finrank_eq_one := hfinL
      isLattice := ⟨w, hwM, hw, hi⟩
      periods := fun σ => Mm'.hodge.periods (ch σ)
      periods_discrete := fun σ => Mm'.hodge.periods_discrete _
      periods_isZLattice := fun σ => Mm'.hodge.periods_isZLattice _
      coeff := coeff
      coeff_ne_zero := fun σ h0 => by
        have h2 : coeff σ w = 0 := by rw [h0]; rfl
        exact Mm'.hodge.coeff_apply_ne_zero (ch σ) hw' h2 }
  let Mm : MetrizedModel A L g :=
    { model := 𝒢
      hodge := D
      lattice_eq := rfl
      arch := fun σ => by
        obtain ⟨Φ', hΦ', hc'⟩ := Mm'.arch (ch σ)
        obtain ⟨Φ, hΦ, hc⟩ := hdesc σ (ch σ) (hch σ) _ Φ' hΦ'
        exact ⟨Φ, hΦ, fun f => hc _ hc' f⟩ }
  refine iInf_le_of_le g (iInf_le_of_le Mm (iInf_le_of_le rfl ?_))
  refine EReal.coe_le_coe_iff.mpr ?_
  show D.modelHeight ≤ Mm'.hodge.modelHeight
  rw [D.modelHeight_eq hwM hw, Mm'.hodge.modelHeight_eq hψwM hw']
  have hsec : secIndex Mm'.hodge.lattice (ψ w) =
      secIndex (𝒢.detLattice g) w ^ Module.finrank L L' := by
    rw [hlat']
    exact secIndex_baseChange hfinL ψ hsmul _ hwM hw hw' hi
  have hsum : ∑ τ' : L' →+* ℂ, F τ' ≤ Module.finrank L L' * ∑ σ : L →+* ℂ, F (ch σ) := by
    rw [← sum_embeddings_comp (fun σ => F (ch σ))]
    exact Finset.sum_le_sum fun τ' _ => hmax _ τ' rfl
  have hD : ∑ σ : L →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)) =
      ∑ σ : L →+* ℂ, F (ch σ) := rfl
  have hD' : ∑ τ' : L' →+* ℂ,
      Real.log (torusMetricSq (Mm'.hodge.periods τ') (Mm'.hodge.coeff τ' (ψ w))) =
      ∑ τ' : L' →+* ℂ, F τ' := rfl
  rw [hD, hD', hsec, ← Module.finrank_mul_finrank ℚ L L']
  have hK : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < Module.finrank L L' := by exact_mod_cast Module.finrank_pos
  push_cast
  rw [Real.log_pow, div_le_div_iff₀ hK (mul_pos hK hL)]
  have := mul_le_mul_of_nonneg_left hsum hK.le
  nlinarith

theorem modelHeightBaseChangeGE_of_descent (h : HodgeLineBaseChangeDescent) :
    ModelHeightBaseChangeGE :=
  modelHeightBaseChangeGE_of_descentHalf (descentHalf_of_descent h)

/-- **Glue H4a (`ModelHeightBaseChange`, verbatim statement) from `HodgeLineBaseChangeDescent`.**
Proved. -/
theorem modelHeightBaseChange_of_descent (h : HodgeLineBaseChangeDescent) :
    ModelHeightBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢
  exact le_antisymm
    (modelHeightBaseChangeLE_of_metrization
      (metrizationBaseChange_of_hodgeLine (hodgeLineBaseChange_of_descent h)) K A L L' 𝒢 𝒢' h𝒢)
    (modelHeightBaseChangeGE_of_descent h K A L L' 𝒢 𝒢' h𝒢)


/-! # Part B: the natural map of a base change (from `Natural.lean`) -/

/-- `Spec 𝓞_{L'} → Spec 𝓞_L`. -/
noncomputable abbrev bO (L L' : Type) [Field L] [Field L'] [Algebra L L'] :
    Spec (CommRingCat.of (𝓞 L')) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))

section Construction

variable {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']

theorem bO_genericPt : bO L L' (genericPt L') = genericPt L := by
  change PrimeSpectrum.comap (algebraMap (𝓞 L) (𝓞 L')) (genericPt L') = _
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (algebraMap (𝓞 L) (𝓞 L')) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 L'))

theorem bO_appTop (r : 𝓞 L) :
    (bO L L').appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv (algebraMap (𝓞 L) (𝓞 L') r) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).hom
      ((bO L L').appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) =
        algebraMap (𝓞 L) (𝓞 L') r := by
    rw [← CommRingCat.comp_apply, h, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  rw [← h3, Iso.hom_inv_id_apply]

variable (𝒢 : GroupModel A L) (𝒢' : GroupModel A L')
  (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)

/-- `e` is an isomorphism of group schemes (the content of `IsBaseChangeOf`). -/
def IsMonBC : Prop :=
  letI : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  IsMonHom e.hom

/-- The projection `π : 𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'} → 𝒢`. -/
noncomputable def bcProj : 𝒢'.G.left ⟶ 𝒢.G.left := e.hom.left ≫ pullback.fst _ _

theorem bcProj_w : bcProj 𝒢 𝒢' e ≫ 𝒢.G.hom = 𝒢'.G.hom ≫ bO L L' := by
  unfold bcProj
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact Over.w e.hom

variable {𝒢 𝒢' e} in
theorem bcProj_unit (he : IsMonBC 𝒢 𝒢' e) :
    𝒢'.unitSection ≫ bcProj 𝒢 𝒢' e = bO L L' ≫ 𝒢.unitSection := by
  let _ : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  have : IsMonHom e.hom := he
  have h1 : (η[𝒢'.G] ≫ e.hom).left = (η[(Over.pullback (bO L L')).obj 𝒢.G]).left :=
    congrArg Over.Hom.left (IsMonHom.one_hom (f := e.hom))
  have hε : (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫ pullback.fst _ _ =
      bO L L' := by
    have hw := Over.w (Functor.LaxMonoidal.ε (Over.pullback (bO L L')))
    have hc := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom)
      (g := bO L L')
    calc _ = (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫
          (pullback.fst _ _ ≫ (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom) := by
            exact congrArg (fun k => _ ≫ k) (Category.comp_id _).symm
      _ = (Functor.LaxMonoidal.ε (Over.pullback (bO L L'))).left ≫ pullback.snd _ _ ≫ bO L L' := by
            rw [hc]
      _ = bO L L' := by
            rw [← Category.assoc]
            erw [hw]
            exact Category.id_comp _
  unfold GroupModel.unitSection bcProj
  rw [← Category.assoc, ← Over.comp_left]
  erw [h1]
  show (Functor.LaxMonoidal.ε _ ≫ (Over.pullback (bO L L')).map η[𝒢.G]).left ≫ pullback.fst _ _ = _
  have hmap : ((Over.pullback (bO L L')).map η[𝒢.G]).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ η[𝒢.G].left := pullback.lift_fst _ _ _
  rw [Over.comp_left, Category.assoc]
  erw [hmap]
  rw [← Category.assoc]
  erw [hε]

variable {𝒢 𝒢' e} in
theorem bcProj_genericUnit (he : IsMonBC 𝒢 𝒢' e) :
    bcProj 𝒢 𝒢' e 𝒢'.genericUnit = 𝒢.genericUnit := by
  have h2 := congrArg (fun φ => φ (genericPt L')) (bcProj_unit he)
  unfold GroupModel.genericUnit
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  simp only
  rw [bO_genericPt]

variable {𝒢 𝒢' e}

/-- The comparison `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}` along `π` (`π(ξ') = ξ`). -/
noncomputable def bcMap (he : IsMonBC 𝒢 𝒢' e) : 𝒢.genStalk ⟶ 𝒢'.genStalk :=
  𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq (bcProj_genericUnit he)).specializes ≫
    (bcProj 𝒢 𝒢' e).stalkMap 𝒢'.genericUnit

/-- `bcMap` is `π^*` on germs. -/
theorem bcMap_germ (he : IsMonBC 𝒢 𝒢' e) (U : 𝒢.G.left.Opens) (hx : 𝒢.genericUnit ∈ U)
    (hx' : 𝒢'.genericUnit ∈ (bcProj 𝒢 𝒢' e) ⁻¹ᵁ U) (s : Γ(𝒢.G.left, U)) :
    (bcMap he) (𝒢.G.left.presheaf.germ U 𝒢.genericUnit hx s) =
      𝒢'.G.left.presheaf.germ ((bcProj 𝒢 𝒢' e) ⁻¹ᵁ U) 𝒢'.genericUnit hx'
        ((bcProj 𝒢 𝒢' e).app U s) := by
  unfold bcMap
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

theorem isIso_stalkSpecializes_bcMap (he : IsMonBC 𝒢 𝒢' e) :
    IsIso (𝒢.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (bcProj_genericUnit he)).specializes) :=
  Iso.isIso_hom (𝒢.G.left.presheaf.stalkCongr (Inseparable.of_eq (bcProj_genericUnit he)).symm)

theorem bcMap_mem_maximalIdeal (he : IsMonBC 𝒢 𝒢' e) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcMap he t ∈ IsLocalRing.maximalIdeal 𝒢'.genStalk := by
  haveI := isIso_stalkSpecializes_bcMap he
  set e' := 𝒢.G.left.presheaf.stalkSpecializes
    (Inseparable.of_eq (bcProj_genericUnit he)).specializes
  have h1 : e' t ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
    intro hu
    apply ht
    have := hu.map (inv e').hom
    rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
  exact map_nonunit ((bcProj 𝒢 𝒢' e).stalkMap 𝒢'.genericUnit).hom _ h1

/-- `bcMap` is compatible with the structure maps `𝓞_L → 𝓞_{L'}`. -/
theorem bcMap_structMap (he : IsMonBC 𝒢 𝒢' e) (r : 𝓞 L) :
    bcMap he (𝒢.structMap r) = 𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) := by
  have e1 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  have e2 : 𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) =
      𝒢'.G.left.presheaf.germ ⊤ 𝒢'.genericUnit trivial
      (𝒢'.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L'))).inv
        (algebraMap (𝓞 L) (𝓞 L') r))) := rfl
  rw [e1, e2, bcMap_germ he ⊤ (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
    (show 𝒢'.genericUnit ∈ (bcProj 𝒢 𝒢' e) ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) from trivial)]
  have hw := bcProj_w 𝒢 𝒢' e
  have : 𝒢.G.hom.appTop ≫ (bcProj 𝒢 𝒢' e).appTop = (bO L L').appTop ≫ 𝒢'.G.hom.appTop := by
    rw [← Scheme.Hom.comp_appTop, hw, Scheme.Hom.comp_appTop]
  rw [← bO_appTop, ← CommRingCat.comp_apply (bO L L').appTop, ← this, CommRingCat.comp_apply]
  rfl

/-- The `𝓞_L`-module structure on `ω_{A_{L'}}` by restriction along `𝓞_L → 𝓞_{L'}`. -/
noncomputable abbrev cotRes (𝒢' : GroupModel A L') : Module (𝓞 L) 𝒢'.cotangent :=
  Module.compHom _ (algebraMap (𝓞 L) (𝓞 L'))

/-- **The induced map `ω_{A_L} → ω_{A_{L'}}` on cotangent spaces at the origin** (`π^*`),
semilinear over `𝓞_L → 𝓞_{L'}`. -/
noncomputable def bcCot (he : IsMonBC 𝒢 𝒢' e) :
    𝒢.cotangent →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] 𝒢'.cotangent where
  toFun x := Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk)
    (IsLocalRing.maximalIdeal 𝒢'.genStalk) (bcMap he).hom.toIntAlgHom
    (fun t ht => bcMap_mem_maximalIdeal he t ht) x
  map_add' x y := map_add _ x y
  map_smul' r x := by
    obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ x
    let ψ := (bcMap he).hom.toIntAlgHom
    have h : IsLocalRing.maximalIdeal 𝒢.genStalk ≤
        (IsLocalRing.maximalIdeal 𝒢'.genStalk).comap ψ :=
      fun t ht => bcMap_mem_maximalIdeal he t ht
    change Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk)
        (IsLocalRing.maximalIdeal 𝒢'.genStalk) ψ h (𝒢.structMap r • Ideal.toCotangent _ m) =
      𝒢'.structMap (algebraMap (𝓞 L) (𝓞 L') r) • Ideal.mapCotangent
        (IsLocalRing.maximalIdeal 𝒢.genStalk) (IsLocalRing.maximalIdeal 𝒢'.genStalk) ψ h
        (Ideal.toCotangent _ m)
    rw [← (Ideal.toCotangent _).map_smul, Ideal.mapCotangent_toCotangent,
      Ideal.mapCotangent_toCotangent, ← (Ideal.toCotangent _).map_smul]
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, ψ, RingHom.toIntAlgHom_apply]
    rw [bcMap_structMap]

theorem bcCot_dCls (he : IsMonBC 𝒢 𝒢' e) (t : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcCot he (𝒢.dCls t) = 𝒢'.dCls ⟨bcMap he t, bcMap_mem_maximalIdeal he t t.2⟩ := rfl

/-! ### The map of Hodge lines `ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` -/

open scoped TensorProduct
open ExteriorAlgebra

/-- The `𝓞_L`-module structure on `⋀^g_{𝓞_{L'}} ω_{A_{L'}}` by restriction of scalars. -/
noncomputable abbrev extRes (𝒢' : GroupModel A L') (g : ℕ) :
    Module (𝓞 L) (exteriorPower (𝓞 L') g 𝒢'.cotangent) :=
  Module.compHom _ (algebraMap (𝓞 L) (𝓞 L'))

theorem bcCot_update (he : IsMonBC 𝒢 𝒢' e) {g : ℕ} [DecidableEq (Fin g)]
    (m : Fin g → 𝒢.cotangent) (i : Fin g) (z : 𝒢.cotangent) :
    (fun j => bcCot he (Function.update m i z j)) =
      Function.update (fun j => bcCot he (m j)) i (bcCot he z) := by
  funext j
  exact Function.apply_update (fun _ => bcCot he) m i z j

/-- `v ↦ π^*v₁ ∧ ⋯ ∧ π^*v_g`, alternating over `𝓞_L`. -/
noncomputable def bcAlt (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    letI := extRes (L := L) 𝒢' g
    𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] exteriorPower (𝓞 L') g 𝒢'.cotangent :=
  letI := extRes (L := L) 𝒢' g
  { toFun := fun v => exteriorPower.ιMulti (𝓞 L') g (fun i => bcCot he (v i))
    map_update_add' := by
      intro _ m i x y
      simp only [bcCot_update he, map_add]
      exact (exteriorPower.ιMulti (𝓞 L') g).map_update_add _ i _ _
    map_update_smul' := by
      intro _ m i r x
      simp only [bcCot_update he, map_smulₛₗ]
      exact (exteriorPower.ιMulti (𝓞 L') g).map_update_smul _ i _ _
    map_eq_zero_of_eq' := by
      intro v i j hv hij
      exact (exteriorPower.ιMulti (𝓞 L') g).map_eq_zero_of_eq _ (by simp only [hv]) hij }

/-- `⋀^g π^* : ⋀^g_{𝓞_L} ω_{A_L} → ⋀^g_{𝓞_{L'}} ω_{A_{L'}}`, additive and semilinear. -/
noncomputable def bcExt (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    exteriorPower (𝓞 L) g 𝒢.cotangent →+ exteriorPower (𝓞 L') g 𝒢'.cotangent :=
  letI := extRes (L := L) 𝒢' g
  (exteriorPower.alternatingMapLinearEquiv (bcAlt he g)).toAddMonoidHom

theorem bcExt_ιMulti (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (v : Fin g → 𝒢.cotangent) :
    bcExt he g (exteriorPower.ιMulti (𝓞 L) g v) =
      exteriorPower.ιMulti (𝓞 L') g (fun i => bcCot he (v i)) := by
  letI := extRes (L := L) 𝒢' g
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (bcAlt he g) v

theorem bcExt_smul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (r : 𝓞 L)
    (x : exteriorPower (𝓞 L) g 𝒢.cotangent) :
    bcExt he g (r • x) = algebraMap (𝓞 L) (𝓞 L') r • bcExt he g x := by
  letI := extRes (L := L) 𝒢' g
  exact (exteriorPower.alternatingMapLinearEquiv (bcAlt he g)).map_smul r x

/-- **The natural map of Hodge spaces** `ψ = L' ⊗ ⋀^g π^* : hodgeSpace g → hodgeSpace' g`. -/
noncomputable def bcHodge (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun a : L => AddMonoidHom.mk'
      (fun x => algebraMap L L' a ⊗ₜ[𝓞 L'] bcExt he g x)
      (fun x y => by rw [map_add, TensorProduct.tmul_add]))
      (fun a b => by
        ext x
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add,
          TensorProduct.add_tmul]))
    (fun r a x => by
      simp only [AddMonoidHom.mk'_apply]
      rw [bcExt_smul, ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, map_mul]
      rfl)

theorem bcHodge_tmul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (a : L)
    (x : exteriorPower (𝓞 L) g 𝒢.cotangent) :
    bcHodge he g (a ⊗ₜ[𝓞 L] x) = algebraMap L L' a ⊗ₜ[𝓞 L'] bcExt he g x := rfl

theorem bcHodge_smul (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (c : L) (v : 𝒢.hodgeSpace g) :
    bcHodge he g (c • v) = algebraMap L L' c • bcHodge he g v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [TensorProduct.smul_tmul', bcHodge_tmul, bcHodge_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `ψ(1 ⊗ df₁ ∧ ⋯ ∧ df_g) = 1 ⊗ d(π^*f₁) ∧ ⋯ ∧ d(π^*f_g)`. -/
theorem bcHodge_wedge (he : IsMonBC 𝒢 𝒢' e) {g : ℕ}
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    bcHodge he g (𝒢.wedge f) =
      𝒢'.wedge (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩) := by
  unfold GroupModel.wedge
  rw [bcHodge_tmul, map_one, bcExt_ιMulti]
  rfl

/-! ### Complex points and Jacobians along `π` -/

omit [NumberField L] [NumberField L'] in
/-- (copied from `scratch/h5-glue/BaseChangePts.lean`, proved there) -/
theorem ptC_hom_comp_bO (τ' : L' →+* ℂ) :
    (GroupModel.ptC (L := L') τ').hom ≫ bO L L' =
      (GroupModel.ptC (L := L) (τ'.comp (algebraMap L L'))).hom := by
  simp only [GroupModel.ptC, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) Restriction does not change values
at points that land in the smaller open. -/
theorem evalAt_res {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens}
    (i : W ⟶ U) (hp : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U s = 𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) := by
  unfold GroupModel.evalAt
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hp.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  rw [dif_pos hU, dif_pos hp]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem ptC_hom_apply {L : Type} [Field L] [NumberField L] (τ : L →+* ℂ) (x : PrimeSpectrum ℂ) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  change PrimeSpectrum.comap (τ.comp (algebraMap (𝓞 L) L)) x = _
  haveI := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  show τ (algebraMap (𝓞 L) L a) ∈ x.asIdeal ↔ a ∈ (⊥ : Ideal (𝓞 L))
  rw [hx, Ideal.mem_bot, Ideal.mem_bot, map_eq_zero_iff _ τ.injective]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem one_mem_dom {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (τ : L →+* ℂ) {W : 𝒢.G.left.Opens}
    (hW : 𝒢.genericUnit ∈ W) : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x ∈ W
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  show (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left ((GroupModel.ptC τ).hom x) ∈ W
  have hx : (GroupModel.ptC (L := L) τ).hom x = genericPt L := ptC_hom_apply τ x
  rw [hx]
  exact hW

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem map_zero_of_hom {G : Type*} [Group G] {g : ℕ} (Φ : (Fin g → ℂ) → G)
    (h : ∀ z w, Φ (z + w) = Φ z * Φ w) : Φ 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact (mul_eq_left.mp this.symm)

variable (e) in
/-- **Complex points along the base change**: `β : 𝒢'(ℂ)_{τ'} → 𝒢(ℂ)_σ`, `p' ↦ π ∘ p'`, for
`σ = τ'|_L`. -/
noncomputable def bcPts (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    (p : 𝒢'.Pts τ') : 𝒢.Pts σ :=
  Over.homMk (p.left ≫ bcProj 𝒢 𝒢' e) (by
    subst hστ
    refine (Category.assoc _ _ _).trans ?_
    rw [bcProj_w]
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ bO L L') (Over.w p)).trans (ptC_hom_comp_bO τ'))

theorem evalAt_bcPts (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    (p : 𝒢'.Pts τ') (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt (bcPts e σ τ' hστ p) U s =
      𝒢'.evalAt p (bcProj 𝒢 𝒢' e ⁻¹ᵁ U) ((bcProj 𝒢 𝒢' e).app U s) := by
  unfold GroupModel.evalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (bcProj 𝒢 𝒢' e ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (bcPts e σ τ' hστ p).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (bcPts e σ τ' hστ p).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem dom_bcPts (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ) {g : ℕ}
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ') (U : 𝒢.G.left.Opens) :
    𝒢.dom (fun z => bcPts e σ τ' hστ (Φ' z)) U = 𝒢'.dom Φ' (bcProj 𝒢 𝒢' e ⁻¹ᵁ U) := rfl

/-- **The germ along `β ∘ Φ'` of `t` agrees near `0` with the germ along `Φ'` of `π^* t`.** -/
theorem germAlong_bcPts_eventuallyEq (he : IsMonBC 𝒢 𝒢' e) (σ : L →+* ℂ) (τ' : L' →+* ℂ)
    (hστ : τ'.comp (algebraMap L L') = σ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ') (hΦ : 𝒢'.IsAnalyticUniformization τ' Λ Φ')
    (t : 𝒢.genStalk) :
    𝒢.germAlong (fun z => bcPts e σ τ' hστ (Φ' z)) t =ᶠ[nhds 0] 𝒢'.germAlong Φ' (bcMap he t) := by
  obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
  set U := (𝒢.exists_rep t).choose
  set m := (𝒢.exists_rep t).choose_spec.choose
  set s := (𝒢.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  have hx' : 𝒢'.genericUnit ∈ bcProj 𝒢 𝒢' e ⁻¹ᵁ U := by
    show bcProj 𝒢 𝒢' e 𝒢'.genericUnit ∈ U
    rw [bcProj_genericUnit he]; exact m
  set U' := (𝒢'.exists_rep (bcMap he t)).choose
  set m' := (𝒢'.exists_rep (bcMap he t)).choose_spec.choose
  set s' := (𝒢'.exists_rep (bcMap he t)).choose_spec.choose_spec.choose
  have hs' : 𝒢'.G.left.presheaf.germ U' 𝒢'.genericUnit m' s' = bcMap he t :=
    (𝒢'.exists_rep (bcMap he t)).choose_spec.choose_spec.choose_spec
  have heq : 𝒢'.G.left.presheaf.germ (bcProj 𝒢 𝒢' e ⁻¹ᵁ U) 𝒢'.genericUnit hx'
      ((bcProj 𝒢 𝒢' e).app U s) = 𝒢'.G.left.presheaf.germ U' 𝒢'.genericUnit m' s' := by
    rw [hs', ← hs, bcMap_germ he U m hx' s]
  obtain ⟨W, mW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ hx' m' _ _ heq
  have hnhds : 𝒢'.dom Φ' W ∈ nhds (0 : Fin g → ℂ) := by
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ' 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ' hmul]
    exact one_mem_dom 𝒢' τ' mW
  filter_upwards [hnhds] with z hz
  show 𝒢.evalAt (bcPts e σ τ' hστ (Φ' z)) U s = 𝒢'.evalAt (Φ' z) U' s'
  rw [evalAt_bcPts, evalAt_res 𝒢' (Φ' z) iU hz, hW, ← evalAt_res 𝒢' (Φ' z) iV hz]

/-- **Jacobian determinants along the base change**:
`jacDet (β ∘ Φ') f = jacDet' Φ' (π^* f)`. -/
theorem jacDet_bcPts (he : IsMonBC 𝒢 𝒢' e) (σ : L →+* ℂ) (τ' : L' →+* ℂ)
    (hστ : τ'.comp (algebraMap L L') = σ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ') (hΦ : 𝒢'.IsAnalyticUniformization τ' Λ Φ')
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet (fun z => bcPts e σ τ' hστ (Φ' z)) f =
      𝒢'.jacDet Φ' (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩) := by
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [(germAlong_bcPts_eventuallyEq he σ τ' hστ Λ Φ' hΦ (f i)).fderiv_eq]

end Construction

/-! ### Half of BC-lat: `ψ(⋀^g ω_𝒢) ⊆ ⋀^g ω_{𝒢'}` (proved) -/

section LatticeHalf

variable {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'} {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G}

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem stalkSpecializes_stalkSpecializes_apply' {X : Scheme.{0}} {x y z : X} (h : x ⤳ y)
    (h' : y ⤳ z) (t : X.presheaf.stalk z) :
    X.presheaf.stalkSpecializes h (X.presheaf.stalkSpecializes h' t) =
      X.presheaf.stalkSpecializes (h.trans h') t := by
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem stalkSpecializes_self_apply' {X : Scheme.{0}} {x : X} (h : x ⤳ x)
    (t : X.presheaf.stalk x) : X.presheaf.stalkSpecializes h t = t := by
  rw [show h = specializes_refl x from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- At each point `s'` of `Spec 𝓞_{L'}`, `π^*` maps `(ω_𝒢)_{s}` (`s` the image of `s'`) into
`(ω_{𝒢'})_{s'}`. -/
theorem bcCot_omegaAt (he : IsMonBC 𝒢 𝒢' e) (s' : Spec (CommRingCat.of (𝓞 L')))
    (m : 𝒢.cotangent) (hm : m ∈ 𝒢.omegaAt (bO L L' s')) : bcCot he m ∈ 𝒢'.omegaAt s' := by
  have hE := bcProj_unit he
  have hp : bcProj 𝒢 𝒢' e (𝒢'.unitSection s') = 𝒢.unitSection (bO L L' s') :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun φ => φ s') hE).trans (Scheme.Hom.comp_apply _ _ _))
  let T := 𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, hmem, rfl⟩ := hx
    set g' := (bcProj 𝒢 𝒢' e).stalkMap (𝒢'.unitSection s') (T g)
    have hspec : 𝒢'.G.left.presheaf.stalkSpecializes (𝒢'.specializes_genericUnit s') g' =
        bcMap he (𝒢.G.left.presheaf.stalkSpecializes
          (𝒢.specializes_genericUnit (bO L L' s')) g) := by
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
      unfold bcMap
      rw [CommRingCat.comp_apply]
      congr 1
      rw [stalkSpecializes_stalkSpecializes_apply', stalkSpecializes_stalkSpecializes_apply']
    have hker : g' ∈ RingHom.ker (𝒢'.unitSection.stalkMap s').hom := by
      rw [RingHom.mem_ker]
      have h1 := Scheme.Hom.stalkMap_comp 𝒢'.unitSection (bcProj 𝒢 𝒢' e) s'
      have h2 := Scheme.Hom.stalkMap_congr_hom _ _ hE s'
      have h1' : (𝒢'.unitSection.stalkMap s') g' =
          ((𝒢'.unitSection ≫ bcProj 𝒢 𝒢' e).stalkMap s') (T g) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h1
        exact this.symm
      have h2' : ((𝒢'.unitSection ≫ bcProj 𝒢 𝒢' e).stalkMap s') (T g) =
          ((bO L L' ≫ 𝒢.unitSection).stalkMap s') ((𝒢.G.left.presheaf.stalkCongr
            (Inseparable.of_eq (hE ▸ rfl))).hom (T g)) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h2
        exact this
      rw [h1', h2']
      have h3 := Scheme.Hom.stalkMap_comp (bO L L') 𝒢.unitSection s'
      have h3' := congrArg (fun φ => (ConcreteCategory.hom φ) ((𝒢.G.left.presheaf.stalkCongr
            (Inseparable.of_eq (hE ▸ rfl))).hom (T g))) h3
      simp only at h3'
      rw [h3']
      have h4 : ∀ y : 𝒢.G.left.presheaf.stalk (𝒢.unitSection (bO L L' s')), y = g →
          (𝒢.unitSection.stalkMap (bO L L' s')) y = 0 := by
        rintro y rfl; exact hg
      have h5 : (𝒢.unitSection.stalkMap (bO L L' s')) ((𝒢.G.left.presheaf.stalkCongr
          (Inseparable.of_eq hp)).hom (T g)) = 0 := by
        apply h4
        show 𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).symm.specializes
          (T g) = g
        exact (stalkSpecializes_stalkSpecializes_apply' _ _ g).trans
          (stalkSpecializes_self_apply' _ g)
      exact (congrArg (fun y => ((bO L L').stalkMap s') y) h5).trans (map_zero _)
    have hmem' : 𝒢'.G.left.presheaf.stalkSpecializes (𝒢'.specializes_genericUnit s') g' ∈
        IsLocalRing.maximalIdeal 𝒢'.genStalk := by
      rw [hspec]; exact bcMap_mem_maximalIdeal he _ hmem
    apply Submodule.subset_span
    refine ⟨g', hker, hmem', ?_⟩
    rw [bcCot_dCls]
    congr 1
    exact Subtype.ext hspec.symm
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/-- `π^*(ω_𝒢) ⊆ ω_{𝒢'}`. -/
theorem bcCot_omega (he : IsMonBC 𝒢 𝒢' e) (m : 𝒢.cotangent) (hm : m ∈ 𝒢.omega) :
    bcCot he m ∈ 𝒢'.omega := by
  rw [GroupModel.omega, Submodule.mem_iInf] at hm ⊢
  exact fun s' => bcCot_omegaAt he s' m (hm _)

/-- `ψ(⋀^g ω_𝒢) ⊆ ⋀^g ω_{𝒢'}`. -/
theorem bcHodge_detLattice (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) (x : 𝒢.hodgeSpace g)
    (hx : x ∈ 𝒢.detLattice g) : bcHodge he g x ∈ 𝒢'.detLattice g := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [bcHodge_tmul, map_one, bcExt_ιMulti]
    apply Submodule.subset_span
    exact ⟨fun i => ⟨bcCot he (v i), bcCot_omega he _ (v i).2⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul L r y, bcHodge_smul]
    have : algebraMap L L' (algebraMap (𝓞 L) L r) • bcHodge he g y =
        (algebraMap (𝓞 L) (𝓞 L') r) • bcHodge he g y := by
      rw [← algebraMap_smul L' (algebraMap (𝓞 L) (𝓞 L') r)]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ hy

/-- **Half of BC-lat (proved)**: `𝓞_{L'} · ψ(⋀^g ω_𝒢) ⊆ ⋀^g ω_{𝒢'}`. -/
theorem span_bcHodge_le (he : IsMonBC 𝒢 𝒢' e) (g : ℕ) :
    Submodule.span (𝓞 L') (bcHodge he g '' 𝒢.detLattice g) ≤ 𝒢'.detLattice g :=
  Submodule.span_le.mpr (by
    rintro _ ⟨x, hx, rfl⟩
    exact bcHodge_detLattice he g x hx)

/-- A multilinear map sends a tuple of vectors of `span S` into the span of its values on tuples
of vectors of `S` (induction on the number of coordinates not yet in `S`). -/
theorem multilinear_mem_span {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M) N)
    (S : Set M) : ∀ (k : ℕ) (v : Fin n → M), (∀ i : Fin n, (i : ℕ) < k → v i ∈ Submodule.span R S) →
      (∀ i : Fin n, k ≤ (i : ℕ) → v i ∈ S) →
      f v ∈ Submodule.span R (f '' {w | ∀ i, w i ∈ S}) := by
  classical
  intro k
  induction k with
  | zero =>
    intro v _ hS
    exact Submodule.subset_span ⟨v, fun i => hS i (Nat.zero_le _), rfl⟩
  | succ k ih =>
    intro v hspan hS
    by_cases hk : k < n
    · set i0 : Fin n := ⟨k, hk⟩
      have hmot : ∀ x ∈ Submodule.span R S,
          f (Function.update v i0 x) ∈ Submodule.span R (f '' {w | ∀ i, w i ∈ S}) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          apply ih
          · intro i hi
            rw [Function.update_of_ne (fun h => by rw [h] at hi; exact lt_irrefl _ hi)]
            exact hspan i (Nat.lt_succ_of_lt hi)
          · intro i hi
            by_cases hii : i = i0
            · rw [hii, Function.update_self]; exact hy
            · rw [Function.update_of_ne hii]
              apply hS i
              have : (i : ℕ) ≠ k := fun h => hii (Fin.ext h)
              omega
        | zero => rw [f.map_update_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [f.map_update_add]; exact add_mem hx hy
        | smul r x _ hx => rw [f.map_update_smul]; exact Submodule.smul_mem _ r hx
      have := hmot (v i0) (hspan i0 (Nat.lt_succ_self k))
      rwa [Function.update_eq_self] at this
    · apply ih v
      · intro i hi; exact hspan i (Nat.lt_succ_of_lt hi)
      · intro i hi
        apply hS i
        have := i.2
        omega

end LatticeHalf

/-- **Glue BC-omega (flat base change of `e*Ω¹`, the hard inclusion).** Every element of
`ω_{𝒢'} = Γ(Spec 𝓞_{L'}, e'*Ω¹_{𝒢'/𝓞_{L'}})` is an `𝓞_{L'}`-combination of pull-backs
`π^*η`, `η ∈ ω_𝒢`. True: `e*Ω¹_{𝒢/𝓞_L}` is locally free (`𝒢` smooth), its formation commutes with
base change (EGA IV 16.4.5 / 17.2.5, UNVERIFIED locators), and for the projective `𝓞_L`-module
`ω_𝒢`, `Γ(Spec 𝓞_{L'}, f^*ω̃) = 𝓞_{L'} ⊗ ω_𝒢`. The other inclusion is proved (`bcCot_omega`).
A model review notes that this inclusion needs less: `e` is a closed immersion (`𝒢` separated),
`omegaAt s` is the image of the stalk of the quasi-coherent conormal `e^*(I/I²)`, and
`I'_{e'(s')} = I_{e(s)} · 𝒪_{𝒢',e'(s')}` for the base-changed section, so
`d(a · π^*f) = e'^#(a) · π^*(df)`; smoothness is not used. STANDARD. -/
def OmegaBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e), 𝒢'.omega ≤ Submodule.span (𝓞 L') (bcCot he '' 𝒢.omega)


/-! ### The differential at the origin along `Φ` (proves `GermDerivation`) -/

section GermDer

variable {K : Type} [Field K] {A : AbVar K}

variable {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)

/-- Values at a point of `V(ℂ)` are additive in the section. -/
theorem evalAt_add {τ : L →+* ℂ} (p : 𝒢.Pts τ) (V : 𝒢.G.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ V)
    (r₁ r₂ : Γ(𝒢.G.left, V)) : 𝒢.evalAt p V (r₁ + r₂) = 𝒢.evalAt p V r₁ + 𝒢.evalAt p V r₂ := by
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp, dif_pos hp, map_add]
  exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _

/-- Values at a point of `V(ℂ)` are multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (V : 𝒢.G.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ V)
    (r₁ r₂ : Γ(𝒢.G.left, V)) : 𝒢.evalAt p V (r₁ * r₂) = 𝒢.evalAt p V r₁ * 𝒢.evalAt p V r₂ := by
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp, dif_pos hp, map_mul]
  exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _

variable {𝒢}

/-- **Any representative computes the germ along `Φ` near `0`.** -/
theorem germAlong_eventuallyEq_rep {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (V : 𝒢.G.left.Opens) (mV : 𝒢.genericUnit ∈ V) (r : Γ(𝒢.G.left, V))
    (ht : 𝒢.G.left.presheaf.germ V 𝒢.genericUnit mV r = t) :
    𝒢.germAlong Φ t =ᶠ[nhds 0] fun z => 𝒢.evalAt (Φ z) V r := by
  obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
  set U := (𝒢.exists_rep t).choose
  set m := (𝒢.exists_rep t).choose_spec.choose
  set s := (𝒢.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  have heq : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s =
      𝒢.G.left.presheaf.germ V 𝒢.genericUnit mV r := by rw [hs, ht]
  obtain ⟨W, mW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ m mV _ _ heq
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  filter_upwards [hnhds] with z hz
  show 𝒢.evalAt (Φ z) U s = 𝒢.evalAt (Φ z) V r
  rw [evalAt_res 𝒢 (Φ z) iU hz, hW, ← evalAt_res 𝒢 (Φ z) iV hz]

/-- The germ along `Φ` is differentiable at `0`. -/
theorem germAlong_differentiableAt {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk) :
    DifferentiableAt ℂ (𝒢.germAlong Φ t) 0 := by
  obtain ⟨V, mV, r, hr⟩ := 𝒢.exists_rep t
  have hev := germAlong_eventuallyEq_rep hΦ t V mV r hr
  obtain ⟨hmul, -, -, hopen, hdiff⟩ := hΦ
  have h0 : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ V := by
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ V
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mV
  have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) V r) 0 :=
    (hdiff V r).differentiableAt ((hopen V).mem_nhds h0)
  exact hev.differentiableAt_iff.mpr hd

/-- **Eventual additivity and multiplicativity of germs along `Φ`.** -/
theorem germAlong_add_mul {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    (𝒢.germAlong Φ (t₁ + t₂) =ᶠ[nhds 0] fun z => 𝒢.germAlong Φ t₁ z + 𝒢.germAlong Φ t₂ z) ∧
      (𝒢.germAlong Φ (t₁ * t₂) =ᶠ[nhds 0] fun z => 𝒢.germAlong Φ t₁ z * 𝒢.germAlong Φ t₂ z) := by
  obtain ⟨V₁, m₁, r₁, h₁⟩ := 𝒢.exists_rep t₁
  obtain ⟨V₂, m₂, r₂, h₂⟩ := 𝒢.exists_rep t₂
  have e₁ := germAlong_eventuallyEq_rep hΦ t₁ V₁ m₁ r₁ h₁
  have e₂ := germAlong_eventuallyEq_rep hΦ t₂ V₂ m₂ r₂ h₂
  set W := V₁ ⊓ V₂
  have mW : 𝒢.genericUnit ∈ W := ⟨m₁, m₂⟩
  let i₁ : W ⟶ V₁ := homOfLE inf_le_left
  let i₂ : W ⟶ V₂ := homOfLE inf_le_right
  let ρ₁ := 𝒢.G.left.presheaf.map i₁.op r₁
  let ρ₂ := 𝒢.G.left.presheaf.map i₂.op r₂
  have g₁ : 𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW ρ₁ = t₁ := by
    rw [TopCat.Presheaf.germ_res_apply]; exact h₁
  have g₂ : 𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW ρ₂ = t₂ := by
    rw [TopCat.Presheaf.germ_res_apply]; exact h₂
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  constructor
  · have eS := germAlong_eventuallyEq_rep hΦ (t₁ + t₂) W mW (ρ₁ + ρ₂)
      (by rw [map_add, g₁, g₂])
    filter_upwards [eS, e₁, e₂, hnhds] with z hS hz₁ hz₂ hz
    rw [hS, hz₁, hz₂, evalAt_add 𝒢 (Φ z) W hz, evalAt_res 𝒢 (Φ z) i₁ hz r₁,
      evalAt_res 𝒢 (Φ z) i₂ hz r₂]
  · have eP := germAlong_eventuallyEq_rep hΦ (t₁ * t₂) W mW (ρ₁ * ρ₂)
      (by rw [map_mul, g₁, g₂])
    filter_upwards [eP, e₁, e₂, hnhds] with z hP hz₁ hz₂ hz
    rw [hP, hz₁, hz₂, evalAt_mul 𝒢 (Φ z) W hz, evalAt_res 𝒢 (Φ z) i₁ hz r₁,
      evalAt_res 𝒢 (Φ z) i₂ hz r₂]

/-- `appLE ⊤ ⊤` is `appTop`. -/
theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app (U := ⊤) f

/-- **Structure sections take the value `τ(r)` at every complex point.** -/
theorem evalAt_structSection {τ : L →+* ℂ} (p : 𝒢.Pts τ) (r : 𝓞 L) :
    𝒢.evalAt p ⊤ (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) =
      τ (algebraMap (𝓞 L) L r) := by
  unfold GroupModel.evalAt
  have h : ⊤ ≤ p.left ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) := fun x _ => trivial
  rw [dif_pos h, appLE_top_top, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have hw : p.left ≫ 𝒢.G.hom = Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))) :=
    Over.w p
  rw [hw]
  have hN := congrArg (fun φ => (ConcreteCategory.hom φ)
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))
  refine hN.trans ?_
  erw [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- **Germs in `𝔪_ξ` vanish at the unit complex point.** -/
theorem evalAt_one_eq_zero (τ : L →+* ℂ) (U : 𝒢.G.left.Opens) (hU : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U))
    (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit hU s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.evalAt (1 : 𝒢.Pts τ) U s = 0 := by
  unfold GroupModel.evalAt
  have h : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U := one_mem_dom 𝒢 τ hU
  rw [dif_pos h]
  have h1 : (1 : 𝒢.Pts τ).left = (GroupModel.ptC τ).hom ≫ 𝒢.unitSection := rfl
  have hgen : genericPt L ∈ 𝒢.unitSection ⁻¹ᵁ U := hU
  have hz : 𝒢.unitSection.app U s = 0 := by
    apply germ_injective_of_isIntegral _ (genericPt L) hgen
    rw [map_zero]
    refine (Scheme.Hom.germ_stalkMap_apply 𝒢.unitSection U (genericPt L) hgen s).symm.trans ?_
    have hfield : IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) := by
      have : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
        (genericPoint_eq_bot_of_affine (CommRingCat.of (𝓞 L))).symm
      rw [this]
      exact Field.toIsField _
    have hloc := map_nonunit (𝒢.unitSection.stalkMap (genericPt L)).hom _
      ((IsLocalRing.mem_maximalIdeal _).mp hs)
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at hloc
    exact hloc
  have h2 : (1 : 𝒢.Pts τ).left.appLE U ⊤ h s =
      ((GroupModel.ptC τ).hom.appLE (𝒢.unitSection ⁻¹ᵁ U) ⊤ h) (𝒢.unitSection.app U s) := by
    have := Scheme.Hom.comp_appLE (GroupModel.ptC τ).hom 𝒢.unitSection U ⊤ h
    exact congrArg (fun φ => (ConcreteCategory.hom φ) s) this
  rw [h2, hz, map_zero]
  exact map_zero _

section Derivation

variable {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}

/-- Germs in `𝔪_ξ` vanish at `0` along `Φ`. -/
theorem germAlong_zero_of_mem (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.germAlong Φ t 0 = 0 := by
  have hs : 𝒢.G.left.presheaf.germ (𝒢.exists_rep t).choose 𝒢.genericUnit
      (𝒢.exists_rep t).choose_spec.choose (𝒢.exists_rep t).choose_spec.choose_spec.choose = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  show 𝒢.evalAt (Φ 0) _ _ = 0
  rw [map_zero_of_hom Φ hΦ.1]
  exact evalAt_one_eq_zero τ _ _ _ (hs ▸ ht)

/-- Structure sections are constant `τ(r)` along `Φ` near `0`. -/
theorem germAlong_structMap (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (r : 𝓞 L) :
    𝒢.germAlong Φ (𝒢.structMap r) =ᶠ[nhds 0] fun _ => τ (algebraMap (𝓞 L) L r) := by
  have e1 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  filter_upwards [germAlong_eventuallyEq_rep hΦ _ ⊤ trivial _ e1.symm] with z hz
  rw [hz, evalAt_structSection]

/-- The derivative at `0` of the germ along `Φ`. -/
noncomputable def D0 (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (t : 𝒢.genStalk) : (Fin g → ℂ) →L[ℂ] ℂ :=
  fderiv ℂ (𝒢.germAlong Φ t) 0

theorem D0_add (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    D0 Φ (t₁ + t₂) = D0 Φ t₁ + D0 Φ t₂ := by
  unfold D0
  rw [(germAlong_add_mul hΦ t₁ t₂).1.fderiv_eq]
  exact fderiv_add (germAlong_differentiableAt hΦ t₁) (germAlong_differentiableAt hΦ t₂)

theorem D0_mul (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    D0 Φ (t₁ * t₂) = 𝒢.germAlong Φ t₁ 0 • D0 Φ t₂ + 𝒢.germAlong Φ t₂ 0 • D0 Φ t₁ := by
  unfold D0
  rw [(germAlong_add_mul hΦ t₁ t₂).2.fderiv_eq]
  exact fderiv_mul (germAlong_differentiableAt hΦ t₁) (germAlong_differentiableAt hΦ t₂)

theorem D0_mul_apply (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (t₁ * t₂) v =
      𝒢.germAlong Φ t₁ 0 * D0 Φ t₂ v + 𝒢.germAlong Φ t₂ 0 * D0 Φ t₁ v := by
  rw [D0_mul hΦ]
  rfl

theorem D0_add_apply (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (t₁ + t₂) v = D0 Φ t₁ v + D0 Φ t₂ v := by
  rw [D0_add hΦ]
  rfl

theorem D0_structMap_mul (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (r : 𝓞 L) (t : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (𝒢.structMap r * t) v = τ (algebraMap (𝓞 L) L r) * D0 Φ t v := by
  rw [D0_mul_apply hΦ]
  have h0 : D0 Φ (𝒢.structMap r) = 0 := by
    unfold D0
    rw [(germAlong_structMap hΦ r).fderiv_eq, fderiv_const_apply]
  rw [h0, (germAlong_structMap hΦ r).eq_of_nhds]
  simp

theorem D0_sq (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x : 𝒢.genStalk)
    (hx : x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2) (v : Fin g → ℂ) : D0 Φ x v = 0 := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on (C := fun x => D0 Φ x v = 0) hx ?_ ?_
  · intro a ha b hb
    rw [D0_mul_apply hΦ, germAlong_zero_of_mem hΦ a ha, germAlong_zero_of_mem hΦ b hb]
    ring
  · intro x y hx hy
    rw [D0_add_apply hΦ, hx, hy, add_zero]

/-- **`GermDerivation` holds for every analytic uniformization** (proved). -/
theorem germDerivation_at (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) :
    ∃ D : 𝒢.cotangent →+ (Fin g → ℂ),
      (∀ (r : 𝓞 L) x, D (r • x) = τ (algebraMap (𝓞 L) L r) • D x) ∧
      ∀ (t : IsLocalRing.maximalIdeal 𝒢.genStalk) (j : Fin g),
        D (𝒢.dCls t) j = fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1) := by
  let 𝔪 := IsLocalRing.maximalIdeal 𝒢.genStalk
  let D1 : 𝔪 → (Fin g → ℂ) := fun t j => D0 Φ (t : 𝒢.genStalk) (Pi.single j 1)
  have hD1add : ∀ a b : 𝔪, D1 (a + b) = D1 a + D1 b := by
    intro a b
    funext j
    simp only [D1, Submodule.coe_add, D0_add_apply hΦ, Pi.add_apply]
  have hD1wd : ∀ a b : 𝔪, 𝔪.toCotangent a = 𝔪.toCotangent b → D1 a = D1 b := by
    intro a b hab
    rw [Ideal.toCotangent_eq] at hab
    have this : D0 Φ (a : 𝒢.genStalk) = D0 Φ ((a : 𝒢.genStalk) - b) + D0 Φ (b : 𝒢.genStalk) := by
      rw [← D0_add hΦ, sub_add_cancel]
    funext j
    simp only [D1]
    rw [this, ContinuousLinearMap.add_apply, D0_sq hΦ _ hab, zero_add]
  let sec : 𝒢.cotangent → 𝔪 := Function.surjInv (𝔪.toCotangent_surjective)
  have hsec : ∀ x : 𝒢.cotangent, 𝔪.toCotangent (sec x) = x :=
    Function.surjInv_eq _
  let D : 𝒢.cotangent →+ (Fin g → ℂ) :=
    { toFun := fun x => D1 (sec x)
      map_zero' := by
        have : D1 (sec 0) = D1 0 := hD1wd _ _ (by rw [hsec, map_zero]; rfl)
        rw [this]
        have h00 : D0 Φ (0 : 𝒢.genStalk) = 0 := by
          have := D0_add hΦ (0 : 𝒢.genStalk) 0
          rw [add_zero] at this
          exact add_eq_left.mp this.symm
        funext j
        simp [D1, h00]
      map_add' := fun x y => by
        show D1 (sec (x + y)) = D1 (sec x) + D1 (sec y)
        rw [← hD1add]
        exact hD1wd _ _ (by rw [hsec, map_add, hsec, hsec]; rfl) }
  have hD : ∀ t : 𝔪, D (𝔪.toCotangent t) = D1 t := fun t => hD1wd _ _ (hsec _)
  refine ⟨D, fun r x => ?_, fun t j => ?_⟩
  · obtain ⟨t, rfl⟩ := 𝔪.toCotangent_surjective x
    have hrx : r • 𝒢.dCls t = 𝔪.toCotangent (𝒢.structMap r • t) := by
      show 𝒢.structMap r • 𝔪.toCotangent t = _
      rw [LinearMap.map_smul]
    show D (r • 𝒢.dCls t) = _ • D (𝒢.dCls t)
    rw [hrx]
    show D (𝔪.toCotangent _) = _ • D (𝔪.toCotangent t)
    rw [hD, hD]
    funext j
    simp only [D1, SetLike.val_smul, smul_eq_mul, Pi.smul_apply]
    rw [D0_structMap_mul hΦ]
  · show D (𝔪.toCotangent t) j = _
    rw [hD]
    rfl

end Derivation

end GermDer

/-! # Part C: `HodgeLineBaseChangeDescent` from glue statements over the natural map

All six are about the honest natural map: `π = e.hom.left ≫ pullback.fst : 𝒢' → 𝒢`, its stalk map
`bcMap : 𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`, `ψ = bcHodge = L' ⊗ ⋀^g π^*` and `β = bcPts : 𝒢'(ℂ)_{τ'} → 𝒢(ℂ)_σ`,
`p' ↦ π ∘ p'`. None is a literature leaf; each is glue (a property of def-faltings' definitions).
Six statements are stated; `PtsBaseChangeMul` and `PtsBaseChangeBij` are then proved, and
`DetLatticeBC` is reduced to `OmegaBaseChange` (`detLatticeBC_of_omega`). -/

/-- **Glue BC-alg (cotangent base change).** `ψ` is injective on nonzero vectors and the Hodge space
of `𝒢'` is an `L'`-line iff that of `𝒢` is an `L`-line. True because `ω_{A_{L'}} = L' ⊗_L ω_{A_L}`
(the cotangent space at a rational point commutes with field extension: `𝒪_{𝒢',ξ'}` is a
localization of `𝒪_{𝒢,ξ} ⊗_L L'` with maximal ideal generated by that of `𝒪_{𝒢,ξ}`), and `⋀^g`
commutes with base change; with `L ⊗_{𝓞_L} ⋀^g_{𝓞_L} V ≅ ⋀^g_L V` (exterior powers commute with
localization) this gives `L' ⊗_L hodgeSpace ≅ hodgeSpace'` through `ψ`. STANDARD. -/
def HodgeBCInjective : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (g : ℕ),
    (∀ v, v ≠ 0 → bcHodge he g v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 ↔ Module.finrank L' (𝒢'.hodgeSpace g) = 1)

/-- **Glue BC-lat (flat base change of `e*Ω¹`).** `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)`. True because
formation of `e*Ω¹_{𝒢/𝓞_L}` (locally free, `𝒢` smooth) commutes with base change
(EGA IV 16.4.5 for `Ω¹`, IV 17.2.5 for conormal `≅ e*Ω¹`; UNVERIFIED locators), so
`ω_{𝒢'} = 𝓞_{L'} · π^*(ω_𝒢)` inside `ω_{A_{L'}}`. It relies on `omegaAt s` being the conormal stalk
and on `omega` being the intersection of the stalks, as every statement about `ω` does.
Reduced to `OmegaBaseChange` below (`detLatticeBC_of_omega`). STANDARD. -/
def DetLatticeBC : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (g : ℕ),
    𝒢'.detLattice g = Submodule.span (𝓞 L') (bcHodge he g '' 𝒢.detLattice g)

open ExteriorAlgebra in
/-- **BC-lat from BC-omega** (proved; the inclusion `⊇` is `span_bcHodge_le`). -/
theorem detLatticeBC_of_omega (h : OmegaBaseChange) : DetLatticeBC := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he g
  refine le_antisymm ?_ (span_bcHodge_le he g)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v', rfl⟩
  let F : MultilinearMap (𝓞 L') (fun _ : Fin g => 𝒢'.cotangent) (𝒢'.hodgeSpace g) :=
    (TensorProduct.mk (𝓞 L') L' (exteriorPower (𝓞 L') g 𝒢'.cotangent) 1).compMultilinearMap
      (exteriorPower.ιMulti (𝓞 L') g).toMultilinearMap
  have key := multilinear_mem_span F (bcCot he '' 𝒢.omega) g (fun i => (v' i : 𝒢'.cotangent))
    (fun i _ => h K A L L' 𝒢 𝒢' e he (v' i).2) (fun i hi => absurd i.2 (not_lt.mpr hi))
  show F (fun i => (v' i : 𝒢'.cotangent)) ∈ _
  refine Submodule.span_mono ?_ key
  rintro _ ⟨w, hw, rfl⟩
  choose u hu hwu using hw
  refine ⟨(1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => u i),
    Submodule.subset_span ⟨fun i => ⟨u i, hu i⟩, rfl⟩, ?_⟩
  rw [bcHodge_tmul, map_one, bcExt_ιMulti]
  have hw' : (fun i => bcCot he (u i)) = w := funext hwu
  rw [hw']
  rfl

/-- **Glue BC-pts-mul.** `β : 𝒢'(ℂ)_{τ'} → 𝒢(ℂ)_σ` is multiplicative (it is induced by the
pullback, a monoidal functor, and `e` is a homomorphism). Category theory; STANDARD. -/
def PtsBaseChangeMul : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    (p q : 𝒢'.Pts τ'), bcPts e σ τ' hστ (p * q) = bcPts e σ τ' hστ p * bcPts e σ τ' hστ q

/-- **Glue BC-pts-bij.** `β` is bijective (universal property of the pullback; h5-glue's
`ptsBaseChangeEquiv` is a bijection with the same underlying map). STANDARD. -/
def PtsBaseChangeBij : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ),
    Function.Bijective (bcPts e σ τ' hστ)

/-- **Glue BC-lift (local structure of the base change).** A map `Φ' : ℂ^g → 𝒢'(ℂ)_{τ'}` whose
composite with `β` is an analytic uniformization of `𝒢(ℂ)_σ` is an analytic uniformization of
`𝒢'(ℂ)_{τ'}`: `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}` is covered by affine opens `Spec(R ⊗_{𝓞_L} 𝓞_{L'})`, whose
regular functions are, locally, quotients of sums `∑ fᵢ ⊗ aᵢ`, so their values along `Φ'` are
holomorphic where those of the `fᵢ` along `β ∘ Φ'` are (`evalAt_bcPts`). Openness of
`Φ'⁻¹(U'(ℂ))` for opens `U'` defined over `L'` (not pulled back from `𝒢`): `U'` is a union of
basic opens `D(h') ⊂ π⁻¹V`, and `{z ∈ dom (β ∘ Φ') V : h'(Φ' z) ≠ 0}` is open by continuity.
Neither `Λ` nor the group clauses are used for these two clauses. STANDARD. -/
def UniformizationLift : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
    𝒢.IsAnalyticUniformization σ Λ (fun z => bcPts e σ τ' hστ (Φ' z)) →
      𝒢'.IsAnalyticUniformization τ' Λ Φ'

/-- **Glue BC-span (Jacobians are determined by pulled-back germs).** For an analytic
uniformization `Φ'` of `𝒢'(ℂ)_{τ'}` and a `τ'`-semilinear `c'` on the Hodge space of `𝒢'`: if `c'`
computes `jacDet Φ'` on wedges of germs pulled back from `𝒢`, it does so on all wedges. True: the
derivative at `0` of `t ↦ germAlong Φ' t` kills `𝔪'²` and is `τ'`-semilinear, so `jacDet Φ'` is a
`τ'`-semilinear alternating function of `(df'_i)`, as is `c' ∘ wedge`; the classes `d(π^*f)`
span `ω_{A_{L'}}` over `𝓞_{L'}` (cotangent base change `V' = L' · bcCot(V)`, clearing
denominators; this spanning fact is part of this statement, not of `HodgeBCInjective`).
STANDARD. -/
def JacobianPullbackSpan : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (τ' : L' →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'), 𝒢'.IsAnalyticUniformization τ' Λ Φ' →
    ∀ c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ,
      (∀ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
        c' (𝒢'.wedge (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩)) =
          𝒢'.jacDet Φ' (fun i => ⟨bcMap he (f i), bcMap_mem_maximalIdeal he _ (f i).2⟩)) →
      ∀ f' : Fin g → IsLocalRing.maximalIdeal 𝒢'.genStalk, c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f'

/-- **BC-pts-bij is a theorem** (universal property of the pullback). -/
theorem ptsBaseChangeBij : PtsBaseChangeBij := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ
  subst hστ
  have hhominv : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, e.hom_inv_id]; rfl
  have hinvhom : e.inv.left ≫ e.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, e.inv_hom_id]; rfl
  have hw : e.hom.left ≫ pullback.snd _ _ = 𝒢'.G.hom := Over.w e.hom
  constructor
  · intro p q hpq
    have h1 : p.left ≫ bcProj 𝒢 𝒢' e = q.left ≫ bcProj 𝒢 𝒢' e := congrArg Over.Hom.left hpq
    have h2 : p.left ≫ e.hom.left = q.left ≫ e.hom.left := by
      apply pullback.hom_ext
      · simpa only [bcProj, Category.assoc] using h1
      · rw [Category.assoc, Category.assoc, hw]
        exact (Over.w p).trans (Over.w q).symm
    have h3 := congrArg (· ≫ e.inv.left) h2
    simp only [Category.assoc, hhominv, Category.comp_id] at h3
    exact Over.OverMorphism.ext h3
  · intro q
    have w : q.left ≫ 𝒢.G.hom = (GroupModel.ptC (L := L') τ').hom ≫ bO L L' :=
      (Over.w q).trans (ptC_hom_comp_bO (L := L) τ').symm
    let pl : (GroupModel.ptC (L := L') τ').left ⟶ 𝒢'.G.left :=
      pullback.lift q.left (GroupModel.ptC (L := L') τ').hom w ≫ e.inv.left
    have hpl : pl ≫ 𝒢'.G.hom = (GroupModel.ptC (L := L') τ').hom := by
      have hw' : e.inv.left ≫ 𝒢'.G.hom = pullback.snd _ _ := Over.w e.inv
      simp only [pl, Category.assoc, hw']
      exact pullback.lift_snd _ _ _
    refine ⟨Over.homMk pl hpl, ?_⟩
    apply Over.OverMorphism.ext
    show pl ≫ bcProj 𝒢 𝒢' e = q.left
    simp only [pl, bcProj, Category.assoc]
    rw [reassoc_of% hinvhom]
    exact pullback.lift_fst _ _ _

/-- **BC-pts-mul is a theorem** (`e` is a homomorphism; components of `μ` of `Over.pullback`). -/
theorem ptsBaseChangeMul : PtsBaseChangeMul := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ p q
  subst hστ
  let _ : GrpObj ((Over.pullback (bO L L')).obj 𝒢.G) := Functor.grpObjObj
  have : IsMonHom e.hom := he
  apply Over.OverMorphism.ext
  show (p * q).left ≫ bcProj 𝒢 𝒢' e =
    (bcPts e _ τ' rfl p * bcPts e _ τ' rfl q).left
  have h1 : (p * q) ≫ e.hom = (p ≫ e.hom) * (q ≫ e.hom) := MonObj.mul_comp p q e.hom
  have h2 : (p * q).left ≫ bcProj 𝒢 𝒢' e =
      ((p ≫ e.hom) * (q ≫ e.hom)).left ≫ pullback.fst _ _ := by
    rw [← h1, Over.comp_left, Category.assoc]
    rfl
  rw [h2]
  show (lift (p ≫ e.hom) (q ≫ e.hom) ≫ (Functor.LaxMonoidal.μ (Over.pullback (bO L L')) 𝒢.G 𝒢.G ≫
      (Over.pullback (bO L L')).map μ[𝒢.G])).left ≫ pullback.fst _ _ =
    (lift (bcPts e _ τ' rfl p) (bcPts e _ τ' rfl q) ≫ μ[𝒢.G]).left
  have hmap : ((Over.pullback (bO L L')).map μ[𝒢.G]).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ μ[𝒢.G].left := pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hmap,
    ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst, Over.lift_left,
      Over.lift_left, pullback.lift_fst_assoc]
    rw [Over.comp_left, Category.assoc]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd, Over.lift_left,
      Over.lift_left, pullback.lift_snd_assoc]
    rw [Over.comp_left, Category.assoc]
    exact (pullback.lift_snd _ _ _).symm

/-- **Glue AN-jac (the Jacobian is a semilinear function of the wedge).** For an analytic
uniformization `Φ` of `𝒢(ℂ)_τ` (any group model, any `g`), `f ↦ jacDet Φ f` factors through
`wedge` by a `τ`-semilinear map on the Hodge space. True: near `0`, `t ↦ germAlong Φ t` is a ring
homomorphism into germs of holomorphic functions (`Φ(0) = 1` lies over `ξ`, the sets `dom Φ U`
are open), so `D(t) = d(germAlong Φ t)(0)` is a derivation at evaluation at `0`: it kills `𝔪_ξ²`
and is `τ`-semilinear on `𝔪_ξ/𝔪_ξ²` (structure sections are constant `τ(r)` along `Φ`), and
`det(D(fᵢ)(e_j))` is alternating in the `dfᵢ`; it extends to `L ⊗ ⋀^g` by `a ⊗ x ↦ τ(a) J(x)`.
A statement about one group model; analytic glue. STANDARD. -/
def JacobianSemilinear : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ J : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ, ∀ f, 𝒢.jacDet Φ f = J (𝒢.wedge f)

/-- **Glue AN-der (the differential at the origin along `Φ`).** For an analytic uniformization
`Φ` of `𝒢(ℂ)_τ`, `t ↦ d(germAlong Φ t)(0)` on `𝔪_ξ` descends to an additive map
`D : 𝔪_ξ/𝔪_ξ² → ℂ^g` (the `j`-th coordinate is the derivative in the direction `e_j`) which is
`τ`-semilinear over `𝓞_L`. True: near `0`, `t ↦ germAlong Φ t` is a ring homomorphism into germs
of holomorphic functions (`Φ(0) = 1` lies over `ξ`, the sets `dom Φ U` are open, representatives
agree near `0`), germs in `𝔪_ξ` vanish at `0`, so the product rule kills `𝔪_ξ²`; structure
sections are the constants `τ(r)` along `Φ`. A statement about one group model; analytic glue.
STANDARD. -/
def GermDerivation : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ D : 𝒢.cotangent →+ (Fin g → ℂ),
      (∀ (r : 𝓞 L) x, D (r • x) = τ (algebraMap (𝓞 L) L r) • D x) ∧
      ∀ (t : IsLocalRing.maximalIdeal 𝒢.genStalk) (j : Fin g),
        D (𝒢.dCls t) j = fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1)

open ExteriorAlgebra in
/-- **AN-jac from AN-der** (determinants and the universal property of `⋀^g`; proved). -/
theorem jacobianSemilinear_of (h : GermDerivation) : JacobianSemilinear := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨D, hDs, hDf⟩ := h K A L 𝒢 τ Λ Φ hΦ
  let σ0 : 𝓞 L →+* ℂ := τ.comp (algebraMap (𝓞 L) L)
  let _ : Module (𝓞 L) ℂ := Module.compHom ℂ σ0
  have e : ∀ [DecidableEq (Fin g)] (m : Fin g → 𝒢.cotangent) (i : Fin g) (z : 𝒢.cotangent),
      (Matrix.of fun i' j => D (Function.update m i z i') j) =
        (Matrix.of fun i' j => D (m i') j).updateRow i (D z) := by
    intro _ m i z
    ext i' j
    by_cases hi : i' = i
    · subst hi
      simp [Matrix.updateRow_self]
    · simp [Matrix.updateRow_ne hi, Function.update_of_ne hi]
  let alt : 𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] ℂ :=
    { toFun := fun v => (Matrix.of fun i j => D (v i) j).det
      map_update_add' := by
        intro inst m i x y
        obtain rfl : inst = instDecidableEqFin g := Subsingleton.elim _ _
        rw [e, e, e, map_add]
        exact Matrix.det_updateRow_add _ _ _ _
      map_update_smul' := by
        intro inst m i r x
        obtain rfl : inst = instDecidableEqFin g := Subsingleton.elim _ _
        rw [e, e, hDs, Matrix.det_updateRow_smul]
        rfl
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        exact Matrix.det_zero_of_row_eq hij (by funext k; simp [hv]) }
  let J0 : exteriorPower (𝓞 L) g 𝒢.cotangent →ₗ[𝓞 L] ℂ :=
    exteriorPower.alternatingMapLinearEquiv alt
  have hJ0 : ∀ (r : 𝓞 L) x, J0 (r • x) = σ0 r * J0 x := fun r x => J0.map_smul r x
  let Jadd : 𝒢.hodgeSpace g →+ ℂ :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun a : L => AddMonoidHom.mk' (fun x => τ a * J0 x)
        (fun x y => by rw [map_add, mul_add]))
        (fun a b => by
          ext x
          simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_mul]))
      (fun r a x => by
        simp only [AddMonoidHom.mk'_apply]
        rw [hJ0, Algebra.smul_def, map_mul]
        show τ (algebraMap (𝓞 L) L r) * τ a * J0 x = τ a * (σ0 r * J0 x)
        simp only [σ0, RingHom.comp_apply]
        ring)
  have hJt : ∀ (a : L) x, Jadd (a ⊗ₜ[𝓞 L] x) = τ a * J0 x := fun a x => rfl
  let J : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ :=
    { toFun := Jadd
      map_add' := map_add Jadd
      map_smul' := fun c v => by
        induction v using TensorProduct.induction_on with
        | zero => simp
        | tmul a x =>
          rw [TensorProduct.smul_tmul', hJt, hJt, smul_eq_mul, map_mul, smul_eq_mul, _root_.mul_assoc]
        | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }
  refine ⟨J, fun f => ?_⟩
  show 𝒢.jacDet Φ f = Jadd ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i)))
  rw [hJt, map_one, _root_.one_mul]
  show _ = exteriorPower.alternatingMapLinearEquiv alt
    (exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i)))
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  show _ = (Matrix.of fun i j => D (𝒢.dCls (f i)) j).det
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [hDf]

/-- **AN-der is a theorem** (`germDerivation_at`). -/
theorem germDerivation : GermDerivation :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hΦ => germDerivation_at hΦ

/-- **AN-jac is a theorem.** -/
theorem jacobianSemilinear : JacobianSemilinear := jacobianSemilinear_of germDerivation

/-- **Glue BC-hspan (the image of `ψ` spans).** `L' · ψ(hodgeSpace g) = hodgeSpace' g`. True by
cotangent base change `ω_{A_{L'}} = L' · π^*(ω_{A_L})` and multilinearity; proved from
`CotangentSpanBC` below (`hodgeSpanBC_of`). (The `L'`-linear extension `L' ⊗_L hodgeSpace →
hodgeSpace'` is in fact an isomorphism, but that does not follow from this statement and
`HodgeBCInjective` alone unless `hodgeSpace` is a line.) STANDARD. -/
def HodgeSpanBC : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e) (g : ℕ),
    Submodule.span L' (Set.range (bcHodge he g)) = ⊤

/-- **Glue BC-cot (cotangent base change, spanning half).** The classes `π^*v`, `v ∈ ω_{A_L}`,
span `ω_{A_{L'}}` over `𝓞_{L'}`. True: `𝒪_{𝒢',ξ'}` is a localization of `𝒪_{𝒢,ξ} ⊗_L L'` whose
maximal ideal is generated by `𝔪_ξ`, so `ω_{A_{L'}} = L' ⊗_L ω_{A_L}`; denominators in `L'` are
cleared because `ω_{A_L}` is a `ℚ`-vector space. A statement about the local rings at the origin
only (no Hodge data). STANDARD. -/
def CotangentSpanBC : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G)
    (he : IsMonBC 𝒢 𝒢' e), Submodule.span (𝓞 L') (Set.range (bcCot he)) = ⊤

open ExteriorAlgebra in
/-- **BC-hspan from BC-cot** (multilinearity; proved). -/
theorem hodgeSpanBC_of (h : CotangentSpanBC) : HodgeSpanBC := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he g
  rw [eq_top_iff]
  rintro w -
  induction w using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a x =>
    rw [show a ⊗ₜ[𝓞 L'] x = a • ((1 : L') ⊗ₜ[𝓞 L'] x) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]]
    refine Submodule.smul_mem _ a ?_
    have hx : x ∈ Submodule.span (𝓞 L') (Set.range (exteriorPower.ιMulti (𝓞 L') g)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v', rfl⟩ := hy
      let F : MultilinearMap (𝓞 L') (fun _ : Fin g => 𝒢'.cotangent) (𝒢'.hodgeSpace g) :=
        (TensorProduct.mk (𝓞 L') L' (exteriorPower (𝓞 L') g 𝒢'.cotangent) 1).compMultilinearMap
          (exteriorPower.ιMulti (𝓞 L') g).toMultilinearMap
      have key := multilinear_mem_span F (Set.range (bcCot he)) g v'
        (fun i _ => by rw [h K A L L' 𝒢 𝒢' e he]; trivial)
        (fun i hi => absurd i.2 (not_lt.mpr hi))
      have hsub : Submodule.span (𝓞 L') (F '' {w | ∀ i, w i ∈ Set.range (bcCot he)}) ≤
          (Submodule.span L' (Set.range (bcHodge he g))).restrictScalars (𝓞 L') := by
        rw [Submodule.span_le]
        rintro _ ⟨w, hw, rfl⟩
        choose u hu using hw
        apply Submodule.subset_span
        refine ⟨(1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g u, ?_⟩
        rw [bcHodge_tmul, map_one, bcExt_ιMulti]
        have hw' : (fun i => bcCot he (u i)) = w := funext hu
        rw [hw']
        rfl
      exact hsub key
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_of_tower_mem _ r hy
  | add x y hx hy => exact add_mem hx hy

open ExteriorAlgebra in
/-- **BC-span from AN-jac and BC-hspan** (proved). -/
theorem jacobianPullbackSpan_of (hJ : JacobianSemilinear) (hS : HodgeSpanBC) :
    JacobianPullbackSpan := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he τ' g Λ Φ' hΦ' c' hc f'
  obtain ⟨J, hJf⟩ := hJ K A L' 𝒢' τ' Λ Φ' hΦ'
  suffices hcJ : c' = J by rw [hcJ, hJf]
  have hwedge : ∀ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      c' (bcHodge he g (𝒢.wedge f)) = J (bcHodge he g (𝒢.wedge f)) := by
    intro f
    rw [bcHodge_wedge, hc f, hJf]
  have hagree : ∀ v, c' (bcHodge he g v) = J (bcHodge he g v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have hx : x ∈ Submodule.span (𝓞 L) (Set.range (exteriorPower.ιMulti (𝓞 L) g)) := by
        rw [exteriorPower.ιMulti_span]; trivial
      induction hx using Submodule.span_induction generalizing a with
      | mem y hy =>
        obtain ⟨v, rfl⟩ := hy
        choose f hf using fun i => (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective (v i)
        have h1 : a ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v = a • 𝒢.wedge f := by
          unfold GroupModel.wedge GroupModel.dCls
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
          congr 2
          funext i
          exact (hf i).symm
        rw [h1, bcHodge_smul, map_smulₛₗ, map_smulₛₗ, hwedge f]
      | zero => simp
      | add y z _ _ hy hz =>
        rw [TensorProduct.tmul_add, map_add, map_add, map_add, hy, hz]
      | smul r y _ hy =>
        rw [← TensorProduct.smul_tmul]
        exact hy _
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  apply LinearMap.ext
  intro w
  have hw : w ∈ Submodule.span L' (Set.range (bcHodge he g)) := by
    rw [hS K A L L' 𝒢 𝒢' e he g]; trivial
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    exact hagree v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul a y _ hy => rw [map_smulₛₗ, map_smulₛₗ, hy]

/-- **Glue BC-lift-an (the analytic core of BC-lift).** If `β ∘ Φ'` is an analytic
uniformization of `𝒢(ℂ)_σ`, then the sets `Φ'⁻¹(U'(ℂ))` are open and the regular functions of
`𝒢'` are holomorphic along `Φ'`, for every open `U'` of `𝒢'` (including opens defined over `L'`
and not pulled back from `𝒢`). Same justification as `UniformizationLift` (affine opens
`Spec(R ⊗_{𝓞_L} 𝓞_{L'})` and basic opens `D(h')`). STANDARD. -/
def UniformizationLiftAnalytic : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L') (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G),
    IsMonBC 𝒢 𝒢' e → ∀ (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ'),
    𝒢.IsAnalyticUniformization σ Λ (fun z => bcPts e σ τ' hστ (Φ' z)) →
      (∀ U, IsOpen (𝒢'.dom Φ' U)) ∧
        ∀ U (s : Γ(𝒢'.G.left, U)),
          DifferentiableOn ℂ (fun z => 𝒢'.evalAt (Φ' z) U s) (𝒢'.dom Φ' U)

/-- **BC-lift from its analytic core** (the group clauses come from `β` being a bijective
homomorphism: `ptsBaseChangeMul`, `ptsBaseChangeBij`). Proved. -/
theorem uniformizationLift_of (h : UniformizationLiftAnalytic) : UniformizationLift := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' e he σ τ' hστ g Λ Φ' hU
  obtain ⟨hopen, hdiff⟩ := h K A L L' 𝒢 𝒢' e he σ τ' hστ Λ Φ' hU
  obtain ⟨hmul, hker, hsurj, -, -⟩ := hU
  have hbij := ptsBaseChangeBij K A L L' 𝒢 𝒢' e he σ τ' hστ
  have hm := ptsBaseChangeMul K A L L' 𝒢 𝒢' e he σ τ' hστ
  have h1 : bcPts e σ τ' hστ (1 : 𝒢'.Pts τ') = 1 := by
    have := hm 1 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.mp this.symm
  refine ⟨?_, ?_, ?_, hopen, hdiff⟩
  · intro z w
    apply hbij.1
    rw [hm]
    exact hmul z w
  · intro z
    rw [← hker z]
    constructor
    · intro hz
      show bcPts e σ τ' hστ (Φ' z) = 1
      rw [hz, h1]
    · intro hz
      apply hbij.1
      rw [h1]
      exact hz
  · intro p
    obtain ⟨z, hz⟩ := hsurj (bcPts e σ τ' hστ p)
    exact ⟨z, hbij.1 hz⟩

/-- **Descent of analytic uniformizations along `β`** (proved, from BC-pts-mul and BC-pts-bij). -/
theorem isAnalyticUniformization_bcPts (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij)
    {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'} {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G}
    (he : IsMonBC 𝒢 𝒢' e) (σ : L →+* ℂ) (τ' : L' →+* ℂ) (hστ : τ'.comp (algebraMap L L') = σ)
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ' : (Fin g → ℂ) → 𝒢'.Pts τ')
    (h : 𝒢'.IsAnalyticUniformization τ' Λ Φ') :
    𝒢.IsAnalyticUniformization σ Λ (fun z => bcPts e σ τ' hστ (Φ' z)) := by
  obtain ⟨hmul, hker, hsurj, hopen, hdiff⟩ := h
  have hbij := hb K A L L' 𝒢 𝒢' e he σ τ' hστ
  have hmul' := hm K A L L' 𝒢 𝒢' e he σ τ' hστ
  have h1 : bcPts e σ τ' hστ (1 : 𝒢'.Pts τ') = 1 := by
    have := hmul' 1 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.mp this.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z w
    simp only
    rw [hmul, hmul']
  · intro z
    rw [← hker z]
    constructor
    · intro hz
      apply hbij.1
      have hz' : bcPts e σ τ' hστ (Φ' z) = 1 := hz
      rw [hz', h1]
    · intro hz
      simp only
      rw [hz, h1]
  · intro q
    obtain ⟨p, rfl⟩ := hbij.2 q
    obtain ⟨z, rfl⟩ := hsurj p
    exact ⟨z, rfl⟩
  · intro U
    rw [dom_bcPts]
    exact hopen _
  · intro U s
    rw [dom_bcPts]
    simp only [evalAt_bcPts]
    exact hdiff _ _

/-- **`HodgeLineBaseChangeDescent` from the six glue statements over the natural map** (two of
them, `PtsBaseChangeMul` and `PtsBaseChangeBij`, are proved above). Proved. -/
theorem hodgeLineBaseChangeDescent_of_glue (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij) (hl : UniformizationLift)
    (hj : JacobianPullbackSpan) : HodgeLineBaseChangeDescent := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨e, he⟩ := h𝒢
  obtain ⟨hinj, hfin⟩ := h1 K A L L' 𝒢 𝒢' e he g
  refine ⟨bcHodge he g, bcHodge_smul he g, hinj, hfin, h2 K A L L' 𝒢 𝒢' e he g, ?_, ?_⟩
  · intro τ' Λ Φ hΦ
    have hbij := hb K A L L' 𝒢 𝒢' e he _ τ' rfl
    choose Φ' hΦ' using fun z => hbij.2 (Φ z)
    have hΦeq : (fun z => bcPts e _ τ' rfl (Φ' z)) = Φ := funext hΦ'
    have hU' : 𝒢'.IsAnalyticUniformization τ' Λ Φ' := by
      refine hl K A L L' 𝒢 𝒢' e he _ τ' rfl Λ Φ' ?_
      rw [hΦeq]
      exact hΦ
    refine ⟨Φ', hU', fun c c' hc hcc' => hj K A L L' 𝒢 𝒢' e he τ' Λ Φ' hU' c' (fun f => ?_)⟩
    rw [← bcHodge_wedge he f, hcc', hc, ← jacDet_bcPts he _ τ' rfl Λ Φ' hU' f, hΦeq]
  · intro σ τ' hστ Λ Φ' hΦ'
    refine ⟨fun z => bcPts e σ τ' hστ (Φ' z),
      isAnalyticUniformization_bcPts hm hb he σ τ' hστ Λ Φ' hΦ', fun c' hc' f => ?_⟩
    rw [bcHodge_wedge he f, hc', jacDet_bcPts he σ τ' hστ Λ Φ' hΦ' f]

/-- **Glue H4a (`ModelHeightBaseChange`, verbatim) from the six glue statements.** Proved. -/
theorem modelHeightBaseChange_of_glue (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij) (hl : UniformizationLift)
    (hj : JacobianPullbackSpan) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_descent (hodgeLineBaseChangeDescent_of_glue h1 h2 hm hb hl hj)

/-- **`HodgeLineBaseChange` (verbatim) from the six glue statements.** Proved. -/
theorem hodgeLineBaseChange_of_glue (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hm : PtsBaseChangeMul) (hb : PtsBaseChangeBij) (hl : UniformizationLift)
    (hj : JacobianPullbackSpan) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_descent (hodgeLineBaseChangeDescent_of_glue h1 h2 hm hb hl hj)

/-- **Main result: glue H4a (`ModelHeightBaseChange`, verbatim) from four glue statements**
(BC-alg, BC-lat, BC-lift, BC-span; BC-pts-mul and BC-pts-bij are now theorems). Proved. -/
theorem modelHeightBaseChange_of_four (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_glue h1 h2 ptsBaseChangeMul ptsBaseChangeBij hl hj

/-- **Main result: `HodgeLineBaseChange` (verbatim) from the same four glue statements.** -/
theorem hodgeLineBaseChange_of_four (h1 : HodgeBCInjective) (h2 : DetLatticeBC)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_glue h1 h2 ptsBaseChangeMul ptsBaseChangeBij hl hj

/-- **`ModelHeightBaseChangeGE` (descent half of H4a) needs only BC-alg and BC-lat** (the
uniformization descent is proved). -/
theorem modelHeightBaseChangeGE_of_two (h1 : HodgeBCInjective) (h2 : DetLatticeBC) :
    ModelHeightBaseChangeGE := by
  refine modelHeightBaseChangeGE_of_descentHalf ?_
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g
  obtain ⟨e, he⟩ := h𝒢
  obtain ⟨hinj, hfin⟩ := h1 K A L L' 𝒢 𝒢' e he g
  refine ⟨bcHodge he g, bcHodge_smul he g, hinj, hfin, h2 K A L L' 𝒢 𝒢' e he g, ?_⟩
  intro σ τ' hστ Λ Φ' hΦ'
  refine ⟨fun z => bcPts e σ τ' hστ (Φ' z), isAnalyticUniformization_bcPts ptsBaseChangeMul
    ptsBaseChangeBij he σ τ' hστ Λ Φ' hΦ', fun c' hc' f => ?_⟩
  rw [bcHodge_wedge he f, hc', jacDet_bcPts he σ τ' hστ Λ Φ' hΦ' f]

/-- **Main result: glue H4a (`ModelHeightBaseChange`, verbatim) from four glue statements over
the natural map**: BC-alg (`HodgeBCInjective`), BC-omega (`OmegaBaseChange`), BC-lift
(`UniformizationLift`), BC-span (`JacobianPullbackSpan`). Proved. -/
theorem modelHeightBaseChange_of_main (h1 : HodgeBCInjective) (hω : OmegaBaseChange)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_four h1 (detLatticeBC_of_omega hω) hl hj

/-- **Main result: `HodgeLineBaseChange` (verbatim) from the same four glue statements.** -/
theorem hodgeLineBaseChange_of_main (h1 : HodgeBCInjective) (hω : OmegaBaseChange)
    (hl : UniformizationLift) (hj : JacobianPullbackSpan) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_four h1 (detLatticeBC_of_omega hω) hl hj

/-- **The descent half of H4a from BC-alg and BC-omega only.** -/
theorem modelHeightBaseChangeGE_of_main (h1 : HodgeBCInjective) (hω : OmegaBaseChange) :
    ModelHeightBaseChangeGE :=
  modelHeightBaseChangeGE_of_two h1 (detLatticeBC_of_omega hω)

/-- **Main result (finest form): glue H4a (`ModelHeightBaseChange`, verbatim) from five glue
statements**: BC-alg (`HodgeBCInjective`), BC-hspan (`HodgeSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`), AN-jac (`JacobianSemilinear`).
Proved. -/
theorem modelHeightBaseChange_of_five (h1 : HodgeBCInjective) (hS : HodgeSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_main h1 hω (uniformizationLift_of hl) (jacobianPullbackSpan_of hJ hS)

/-- **`HodgeLineBaseChange` (verbatim) from the same five glue statements.** -/
theorem hodgeLineBaseChange_of_five (h1 : HodgeBCInjective) (hS : HodgeSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_main h1 hω (uniformizationLift_of hl) (jacobianPullbackSpan_of hJ hS)

/-- **Main result (finest form, with BC-cot): glue H4a (`ModelHeightBaseChange`, verbatim) from
five glue statements**: BC-alg (`HodgeBCInjective`), BC-cot (`CotangentSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`), AN-jac (`JacobianSemilinear`).
Proved. -/
theorem modelHeightBaseChange_of_glue5 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_five h1 (hodgeSpanBC_of hc) hω hl hJ

/-- **`HodgeLineBaseChange` (verbatim) from the same five glue statements.** -/
theorem hodgeLineBaseChange_of_glue5 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hJ : JacobianSemilinear) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_five h1 (hodgeSpanBC_of hc) hω hl hJ

/-- **Main result (final form): glue H4a (`ModelHeightBaseChange`, verbatim) from five glue
statements**: BC-alg (`HodgeBCInjective`), BC-cot (`CotangentSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`), AN-der (`GermDerivation`). Proved. -/
theorem modelHeightBaseChange_of_final (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hD : GermDerivation) :
    ModelHeightBaseChange :=
  modelHeightBaseChange_of_glue5 h1 hc hω hl (jacobianSemilinear_of hD)

/-- **`HodgeLineBaseChange` (verbatim) from the same five glue statements** (final form). -/
theorem hodgeLineBaseChange_of_final (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) (hD : GermDerivation) :
    HodgeLineBaseChange :=
  hodgeLineBaseChange_of_glue5 h1 hc hω hl (jacobianSemilinear_of hD)

/-- **Main result (final form): glue H4a (`ModelHeightBaseChange`, verbatim) from four glue
statements**: BC-alg (`HodgeBCInjective`), BC-cot (`CotangentSpanBC`), BC-omega
(`OmegaBaseChange`), BC-lift-an (`UniformizationLiftAnalytic`). `GermDerivation` is proved.
Proved. -/
theorem modelHeightBaseChange_of_glue4 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) : ModelHeightBaseChange :=
  modelHeightBaseChange_of_final h1 hc hω hl germDerivation

/-- **`HodgeLineBaseChange` (verbatim) from the same four glue statements** (final form). -/
theorem hodgeLineBaseChange_of_glue4 (h1 : HodgeBCInjective) (hc : CotangentSpanBC)
    (hω : OmegaBaseChange) (hl : UniformizationLiftAnalytic) : HodgeLineBaseChange :=
  hodgeLineBaseChange_of_final h1 hc hω hl germDerivation


end ZInQ.HeightBC

namespace ZInQ.HeightBC
/-- (height-bc Part E) g0-stablebc's `HodgeLineBaseChange` is height-bc's (verbatim copies). -/
theorem g0_hodgeLine_iff : G0StableBC.HodgeLineBaseChange ↔ HodgeLineBaseChange := Iff.rfl
end ZInQ.HeightBC

/-! ## g0-assemble2: product-height (scratch/product-height/ProductHeight.lean lines 2-969, verbatim except that
the line `open PkgI3 (AbVar)` is replaced by a comment: `AbVar` is def-faltings' copy through
`open DefFaltings`, as in leaf-adopt3's hodge-lattice fold in Leaves.lean) -/

/-! # product-height: the glue Prop `ProductModelHeight` (P2)

Task product-height. Imports only the kernel module `ZInQKernel.HDecomp.Faltings.H5Neron`
(no scratch import). No `sorry`, no `axiom`. See `docs/research/product-height.md`.

Contents.
* §0 A verbatim copy of `ProductModelHeight` (from `scratch/h5-neron/H5Neron.lean`, identical to
  `scratch/h5-glue/H5Final.lean` and to the kernel's `ZInQ.H5Neron.ProductModelHeight`) with the
  definitions it uses, and `copy_iff : Copy.ProductModelHeight ↔ H5Neron.ProductModelHeight`
  (`Iff.rfl`), so that everything below is about the same Prop.
* §1 Route S (new, no `AnalyticUniformizationUnique`): `ProductModelHeight` from one glue Prop
  `ProductMetrizationSplit` (every metrization of a product model splits into metrizations of the
  factors whose heights add up to at most its height).
* §2 Route U (g0-heightadd's reduction, ported to the kernel's types): `ProductModelHeight` from
  `AnalyticUniformizationUnique`, `MetrizationDimUnique`, `MetrizationExists`,
  `ProductMetrizationGeo`; and the sharper form with the single Prop `MetrizationHeightUnique`
  in place of the first two.
* §3 Route U implies route S (`productMetrizationSplit_of`): the two routes are consistent, and S
  is no stronger than the inputs of U.
* §4 What `ProductModelHeight` forces: `metrizable_left/right_of_productModelHeight`,
  `analyticUnif_left_of_productModelHeight` (a metrization of the product forces metrizations,
  hence uniformizations, of the factors) and `le_of_productModelHeight`.
* §5 Complex points of a product model (`ptsEquiv`) and the product uniformization (`prodUnif`,
  algebraic clauses proved; analytic clauses = glue `ProductUnifAnalytic`).
* §6 **Main result.** `productModelHeight_of_splits : ProductUnifSplits →
  ProductMetrizationOfProductUnif → ProductModelHeight`. Neither glue Prop involves AN3: the first
  splits the product's *own* uniformization by elementary analysis, the second is Hodge theory
  with the uniformizations given. The change of coordinates (`recoordM`) is proved.

Correction (run 1). An earlier version of this header and of §4 claimed that P2 needs analytic
input of AN3 type. An independent model review refuted this (log). The splitting is elementary
(§6), and the §4 lemmas show only that P2 forces descent of uniformizations to the factors, which
§6's `ProductUnifSplits` provides without AN3. -/

namespace ZInQ.ProductHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings
-- (g0-assemble2) `open PkgI3 (AbVar)` deleted: `AbVar` is def-faltings' copy through `open DefFaltings`, as in leaf-adopt3's hodge-lattice fold

/-! ## §0. Verbatim copy (from `scratch/h5-neron/H5Neron.lean`) -/

namespace Copy

section General

variable {S S' : Scheme.{0}} (j : S' ⟶ S) (P : Over S → Prop)

variable {j P}

/-- The identification of the generic fibre of `N₁ ⊗ N₂` with `A₁ ⊗ A₂`. -/
noncomputable def tensorGen {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (Over.pullback j).obj (N₁ ⊗ N₂) ≅ A₁ ⊗ A₂ :=
  prodComparisonIso (Over.pullback j) N₁ N₂ ≪≫ tensorIso e₁ e₂

end General

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

variable {K : Type} [Field K]

/-- `C_L ≅ A_L ⊗ B_L`. -/
noncomputable def bcProd {A B C : AbVar K} (L : Type) [Field L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) : (C.baseChange L).X ≅ (A.baseChange L).X ⊗ (B.baseChange L).X :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso eC ≪≫
    prodComparisonIso (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))) A.X B.X

/-- `𝒢P ≅ 𝒢₁ × 𝒢₂` as group models of `C_L ≅ A_L × B_L`. -/
def IsProductModel {A B C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) :
    Prop :=
  ∃ e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G, IsMonHom (e.hom ≫ fst _ _) ∧ IsMonHom (e.hom ≫ snd _ _) ∧
    (Over.pullback (jL L)).map e.hom ≫ (tensorGen 𝒢₁.gen 𝒢₂.gen).hom =
      𝒢P.gen.hom ≫ (bcProd L eC).hom

/-- **Glue P2** (the direction used). The height of a product model is at least the sum of the
heights: `ω_{𝒢₁×𝒢₂} = ω_{𝒢₁} ⊕ ω_{𝒢₂}`, `det(ω₁ ⊕ ω₂) = det ω₁ ⊗ det ω₂`, the Arakelov degree is
additive, and a product of uniformizations is a uniformization of the product (equality holds). -/
def ProductModelHeight : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ → 𝒢₁.height + 𝒢₂.height ≤ 𝒢P.height

end Copy

/-- The copy is the kernel's Prop (definitional equality). -/
theorem copy_iff : Copy.ProductModelHeight ↔ H5Neron.ProductModelHeight := Iff.rfl

open H5Neron

/-! ## Basic facts about `GroupModel.height` -/

section Basic

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A metrization bounds the height of its model from above. -/
theorem height_le_of_model {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L}
    (h : M.model = 𝒢) : 𝒢.height ≤ (M.hodge.modelHeight : EReal) :=
  iInf_le_of_le g (iInf_le_of_le M (iInf_le_of_le h le_rfl))

/-- A group model without metrization has height `⊤`. -/
theorem height_eq_top_of_not_metrizable {𝒢 : GroupModel A L}
    (h : ¬ ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒢) : 𝒢.height = ⊤ := by
  refine eq_top_iff.mpr (le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_)
  exact absurd ⟨g, M, hM⟩ h

/-- A metrizable group model has height `< ⊤`. -/
theorem height_ne_top_of_model {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L}
    (h : M.model = 𝒢) : 𝒢.height ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (height_le_of_model M h)

end Basic

/-! ## §1. Route S: `ProductModelHeight` from the splitting of metrizations (no AN3) -/

/-- **Glue S (splitting of a metrization of a product model).** If `𝒢P ≅ 𝒢₁ × 𝒢₂`
(`IsProductModel`), then every metrization `MP` of `𝒢P` (of any dimension `g`) yields metrizations
`M₁` of `𝒢₁` and `M₂` of `𝒢₂` with `h(M₁) + h(M₂) ≤ h(MP)`.

Why true (STANDARD; elementary analysis, no AN3; reduced in §6 to `ProductUnifSplits` and
`ProductMetrizationOfProductUnif`): a holomorphic surjective homomorphism
`Φ : ℂ^g → 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` with lattice kernel splits, after a `ℂ`-linear change of
coordinates `T`, as `Φ₁ × Φ₂` (restrict `Φ` to the identity components of `ker(p₂ ∘ Φ)` and
`ker(p₁ ∘ Φ)`, which are complementary complex subspaces). Then `g = g₁ + g₂`,
`⋀^{g}ω_{𝒢P} = ⋀^{g₁}ω_{𝒢₁} ⊗ ⋀^{g₂}ω_{𝒢₂}`, the Jacobian is block diagonal and
`covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`, so equality holds (`modelHeight_add_of`). The
algebraic half is the same as in `ProductMetrizationGeo`. Unproved. -/
def ProductMetrizationSplit : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g : ℕ) (MP : MetrizedModel C L g), MP.model = 𝒢P →
      ∃ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
        M₁.model = 𝒢₁ ∧ M₂.model = 𝒢₂ ∧
        M₁.hodge.modelHeight + M₂.hodge.modelHeight ≤ MP.hodge.modelHeight

/-- **`ProductModelHeight` from `ProductMetrizationSplit` alone (proved).** No uniqueness of
uniformizations, no existence of metrizations and no dimension statement is used. -/
theorem productModelHeight_of_split (h : ProductMetrizationSplit) : ProductModelHeight := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hPM
  refine le_iInf fun g => le_iInf fun MP => le_iInf fun hMP => ?_
  obtain ⟨g₁, g₂, M₁, M₂, h₁, h₂, hle⟩ := h K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM g MP hMP
  calc 𝒢₁.height + 𝒢₂.height
      ≤ (M₁.hodge.modelHeight : EReal) + (M₂.hodge.modelHeight : EReal) :=
        add_le_add (height_le_of_model M₁ h₁) (height_le_of_model M₂ h₂)
    _ = ((M₁.hodge.modelHeight + M₂.hodge.modelHeight : ℝ) : EReal) := (EReal.coe_add _ _).symm
    _ ≤ (MP.hodge.modelHeight : EReal) := EReal.coe_le_coe_iff.mpr hle

/-! ## §2. Route U (g0-heightadd's reduction, on the kernel's types)

The four Props `ProductMetrization`, `MetrizationExists`, `MetrizationDimUnique`,
`ProductMetrizationGeo` and the lemmas `modelHeight_add_of`, `productModelHeight_of`,
`productMetrization_of_geo` are copied from `scratch/g0-heightadd/part_heightadd.lean` and
`part_prod.lean` (there over the def-faltings copy `Prefix.lean`); here they are over the kernel's
`PkgI3.AbVar`, `DefFaltings.GroupModel` and `H5Neron.IsProductModel`. Statements unchanged. -/

/-- **Glue P2a (product of metrized models).** If `𝒢P ≅ 𝒢₁ × 𝒢₂` (`IsProductModel`) and `M₁`, `M₂`
are metrizations of `𝒢₁`, `𝒢₂` of dimensions `g₁`, `g₂`, then `𝒢P` has a metrization of
dimension `g₁ + g₂` whose model height is the sum. (Copied from g0-heightadd; STANDARD, unproved:
`ω_{𝒢P} = ω₁ ⊕ ω₂`, `Φ₁ × Φ₂` is a uniformization with lattice `Λ₁ × Λ₂`.) -/
def ProductMetrization : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ → M₂.model = 𝒢₂ →
      ∃ MP : MetrizedModel C L (g₁ + g₂), MP.model = 𝒢P ∧
        MP.hodge.modelHeight = M₁.hodge.modelHeight + M₂.hodge.modelHeight

/-- **Glue (existence of metrizations; correctness of def-faltings' definition).** Every smooth
group model `𝒢` of `A_L` carries a metrization (copied from g0-heightadd; from
`HodgeLatticeTheorem` and `AnalyticUniformizationExists`, AN3-existence; unproved). -/
def MetrizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒢

/-- **Glue (the dimension of a metrization).** Two metrizations of the same group model have
the same dimension (copied from g0-heightadd; both equal `dim A`; unproved). -/
def MetrizationDimUnique : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (g g' : ℕ) (M : MetrizedModel A L g) (M' : MetrizedModel A L g'), M.model = M'.model → g = g'

/-- **Glue H (new; what U and `MetrizationDimUnique` are used for).** Two metrizations of the
same group model (of any dimensions) have the same model height: the height of a group model
does not depend on the choice of analytic uniformization. Follows from
`AnalyticUniformizationUnique` and `MetrizationDimUnique` (`metrizationHeightUnique_of`). -/
def MetrizationHeightUnique : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (g g' : ℕ) (M : MetrizedModel A L g) (M' : MetrizedModel A L g'), M.model = M'.model →
      M.hodge.modelHeight = M'.hodge.modelHeight

/-- `MetrizationHeightUnique` from U and `MetrizationDimUnique` (proved). -/
theorem metrizationHeightUnique_of (hU : AnalyticUniformizationUnique)
    (hD : MetrizationDimUnique) : MetrizationHeightUnique := by
  intro K _ A L _ _ _ g g' M M' h
  obtain rfl := hD K A L g g' M M' h
  exact MetrizedModel.modelHeight_eq_of_model_eq hU M M' h

section HeightOf

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Under `MetrizationHeightUnique`, a metrization computes the height of its model. -/
theorem height_eq_of_model (hH : MetrizationHeightUnique) {g : ℕ} (M : MetrizedModel A L g)
    {𝒢 : GroupModel A L} (h : M.model = 𝒢) : 𝒢.height = (M.hodge.modelHeight : EReal) := by
  refine le_antisymm (height_le_of_model M h) ?_
  refine le_iInf fun g' => le_iInf fun M' => le_iInf fun hM' => ?_
  rw [hH K A L g g' M M' (h.trans hM'.symm)]

/-- Given AN3-uniqueness and `MetrizationDimUnique`, a metrization computes the height of its
model from below (g0-heightadd's lemma). -/
theorem le_height_of_model (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L} (h : M.model = 𝒢) :
    (M.hodge.modelHeight : EReal) ≤ 𝒢.height :=
  (height_eq_of_model (metrizationHeightUnique_of hU hD) M h).ge

end HeightOf

/-- **`ProductModelHeight` from `MetrizationHeightUnique`, `MetrizationExists` and
`ProductMetrization` (proved).** -/
theorem productModelHeight_of_unique (hH : MetrizationHeightUnique) (hE : MetrizationExists)
    (hP : ProductMetrization) : ProductModelHeight := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hPM
  obtain ⟨g₁, M₁, h₁⟩ := hE K A L 𝒢₁
  obtain ⟨g₂, M₂, h₂⟩ := hE K B L 𝒢₂
  obtain ⟨MP, hMP, hh⟩ := hP K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM g₁ g₂ M₁ M₂ h₁ h₂
  rw [height_eq_of_model hH M₁ h₁, height_eq_of_model hH M₂ h₂, height_eq_of_model hH MP hMP,
    hh, EReal.coe_add]

/-- **g0-heightadd's `productModelHeight_of`, on the kernel's types (proved).** -/
theorem productModelHeight_of (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    (hE : MetrizationExists) (hP : ProductMetrization) : ProductModelHeight :=
  productModelHeight_of_unique (metrizationHeightUnique_of hU hD) hE hP

section HodgeAdd

variable {K : Type*} [Field K] [NumberField K]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V₁] [Module K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁]
  [AddCommGroup V₂] [Module K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂]

/-- **Additivity of the model height (copied from g0-heightadd, proved).** If the Hodge data `D`
(dimension `g₁ + g₂`) has a nonzero section `s` whose lattice index, coefficients and period
covolumes are the products of those of nonzero sections `s₁`, `s₂` of `D₁`, `D₂`, then
`h(D) = h(D₁) + h(D₂)`. -/
theorem modelHeight_add_of {g₁ g₂ : ℕ} (D : HodgeData K (g₁ + g₂) V) (D₁ : HodgeData K g₁ V₁)
    (D₂ : HodgeData K g₂ V₂) {s : V} {s₁ : V₁} {s₂ : V₂} (hs : s ∈ D.lattice) (hs0 : s ≠ 0)
    (hs₁ : s₁ ∈ D₁.lattice) (hs₁0 : s₁ ≠ 0) (hs₂ : s₂ ∈ D₂.lattice) (hs₂0 : s₂ ≠ 0)
    (hidx : secIndex D.lattice s = secIndex D₁.lattice s₁ * secIndex D₂.lattice s₂)
    (hcoeff : ∀ σ, D.coeff σ s = D₁.coeff σ s₁ * D₂.coeff σ s₂)
    (hcov : ∀ σ, ZLattice.covolume (D.periods σ) =
      ZLattice.covolume (D₁.periods σ) * ZLattice.covolume (D₂.periods σ)) :
    D.modelHeight = D₁.modelHeight + D₂.modelHeight := by
  rw [D.modelHeight_eq hs hs0, D₁.modelHeight_eq hs₁ hs₁0, D₂.modelHeight_eq hs₂ hs₂0]
  have ht : ∀ σ : K →+* ℂ, torusMetricSq (D.periods σ) (D.coeff σ s) =
      torusMetricSq (D₁.periods σ) (D₁.coeff σ s₁) *
        torusMetricSq (D₂.periods σ) (D₂.coeff σ s₂) := by
    intro σ
    simp only [torusMetricSq, hcoeff σ, hcov σ, norm_mul]
    ring
  have hlog : ∀ σ : K →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ s)) =
      Real.log (torusMetricSq (D₁.periods σ) (D₁.coeff σ s₁)) +
        Real.log (torusMetricSq (D₂.periods σ) (D₂.coeff σ s₂)) := by
    intro σ
    rw [ht σ]
    have := D₁.periods_discrete σ
    have := D₁.periods_isZLattice σ
    have := D₂.periods_discrete σ
    have := D₂.periods_isZLattice σ
    exact Real.log_mul (torusMetricSq_pos _ (D₁.coeff_apply_ne_zero σ hs₁0)).ne'
      (torusMetricSq_pos _ (D₂.coeff_apply_ne_zero σ hs₂0)).ne'
  have hi₁ : (secIndex D₁.lattice s₁ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D₁.hodgeBundle.secIndex_ne_zero hs₁ hs₁0)
  have hi₂ : (secIndex D₂.lattice s₂ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D₂.hodgeBundle.secIndex_ne_zero hs₂ hs₂0)
  rw [hidx, Nat.cast_mul, Real.log_mul hi₁ hi₂, Finset.sum_congr rfl (fun σ _ => hlog σ),
    Finset.sum_add_distrib]
  ring

end HodgeAdd

/-- **Glue P2a-geo (copied from g0-heightadd).** For `𝒢P ≅ 𝒢₁ × 𝒢₂` and metrizations `M₁`, `M₂`,
there is a metrization `MP` of `𝒢P` of dimension `g₁ + g₂` and nonzero sections
`s ∈ ⋀^{g₁+g₂}ω_{𝒢P}`, `sᵢ ∈ ⋀^{gᵢ}ω_{𝒢ᵢ}` whose lattice index, coefficients and period
covolumes multiply (`s = p₁*s₁ ∧ p₂*s₂`, `Φ₁ × Φ₂` with lattice `Λ₁ × Λ₂`; STANDARD, unproved). -/
def ProductMetrizationGeo : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ → M₂.model = 𝒢₂ →
      ∃ (MP : MetrizedModel C L (g₁ + g₂)) (s : MP.model.hodgeSpace (g₁ + g₂))
        (s₁ : M₁.model.hodgeSpace g₁) (s₂ : M₂.model.hodgeSpace g₂),
        MP.model = 𝒢P ∧ s ∈ MP.hodge.lattice ∧ s ≠ 0 ∧ s₁ ∈ M₁.hodge.lattice ∧ s₁ ≠ 0 ∧
        s₂ ∈ M₂.hodge.lattice ∧ s₂ ≠ 0 ∧
        secIndex MP.hodge.lattice s = secIndex M₁.hodge.lattice s₁ * secIndex M₂.hodge.lattice s₂ ∧
        (∀ σ, MP.hodge.coeff σ s = M₁.hodge.coeff σ s₁ * M₂.hodge.coeff σ s₂) ∧
        (∀ σ, ZLattice.covolume (MP.hodge.periods σ) =
          ZLattice.covolume (M₁.hodge.periods σ) * ZLattice.covolume (M₂.hodge.periods σ))

/-- **P2a from P2a-geo (copied from g0-heightadd, proved).** -/
theorem productMetrization_of_geo (h : ProductMetrizationGeo) : ProductMetrization := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  obtain ⟨MP, s, s₁, s₂, hMP, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hc, hcov⟩ :=
    h K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  exact ⟨MP, hMP,
    modelHeight_add_of MP.hodge M₁.hodge M₂.hodge hs hs0 hs₁ hs₁0 hs₂ hs₂0 hidx hc hcov⟩

/-- **`ProductModelHeight` from U, `MetrizationDimUnique`, `MetrizationExists` and
`ProductMetrizationGeo` (proved).** -/
theorem productModelHeight_of_geo (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    (hE : MetrizationExists) (hG : ProductMetrizationGeo) : ProductModelHeight :=
  productModelHeight_of hU hD hE (productMetrization_of_geo hG)

/-! ## §3. Route U implies route S -/

/-- **`ProductMetrizationSplit` from `MetrizationHeightUnique`, `MetrizationExists` and
`ProductMetrization` (proved).** So S is implied by the inputs of route U. -/
theorem productMetrizationSplit_of (hH : MetrizationHeightUnique) (hE : MetrizationExists)
    (hP : ProductMetrization) : ProductMetrizationSplit := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hPM g MP hMP
  obtain ⟨g₁, M₁, h₁⟩ := hE K A L 𝒢₁
  obtain ⟨g₂, M₂, h₂⟩ := hE K B L 𝒢₂
  obtain ⟨MP', hMP', hh⟩ := hP K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM g₁ g₂ M₁ M₂ h₁ h₂
  refine ⟨g₁, g₂, M₁, M₂, h₁, h₂, ?_⟩
  rw [← hh, hH K C L _ g MP' MP (hMP'.trans hMP.symm)]

/-! ## §4. What `ProductModelHeight` forces

`ProductModelHeight` forces, from a single metrization of the product (an analytic
uniformization `Φ` of `(𝒢₁ × 𝒢₂)(ℂ)_τ` at every `τ`, with its Hodge data), the existence of
metrizations of each factor, i.e. of analytic uniformizations of `𝒢₁(ℂ)_τ` with a *discrete*
kernel. The composite `p₁ ∘ Φ` is onto but has a non-discrete kernel. A discrete one is obtained
by restricting `Φ` to the identity component of `ker(p₂ ∘ Φ)`, an elementary step (§6,
`ProductUnifSplits`); this is *not* AN3. (An earlier version of this text called it AN3-type; that
was wrong.) P2 also bounds every single metrization of the product from below. -/

section Forces

variable {K : Type} [Field K] {A B C : AbVar K} {eC : C.X ≅ A.X ⊗ B.X} {L : Type} [Field L]
  [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}

/-- `ProductModelHeight` bounds every single metrization of the product from below. -/
theorem le_of_productModelHeight (h : ProductModelHeight) (hPM : IsProductModel eC 𝒢P 𝒢₁ 𝒢₂)
    {g : ℕ} (MP : MetrizedModel C L g) (hMP : MP.model = 𝒢P) :
    𝒢₁.height + 𝒢₂.height ≤ (MP.hodge.modelHeight : EReal) :=
  (h K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM).trans (height_le_of_model MP hMP)

/-- **`ProductModelHeight` forces metrizations of the left factor** (proved): if the product
model has a metrization and `h(𝒢₂) ≠ ⊥`, then `𝒢₁` has a metrization. -/
theorem metrizable_left_of_productModelHeight (h : ProductModelHeight)
    (hPM : IsProductModel eC 𝒢P 𝒢₁ 𝒢₂) {g : ℕ} (MP : MetrizedModel C L g) (hMP : MP.model = 𝒢P)
    (h₂ : 𝒢₂.height ≠ ⊥) : ∃ (g₁ : ℕ) (M₁ : MetrizedModel A L g₁), M₁.model = 𝒢₁ := by
  by_contra hn
  have h1 := height_eq_top_of_not_metrizable hn
  have key := le_of_productModelHeight h hPM MP hMP
  rw [h1, EReal.top_add_of_ne_bot h₂, top_le_iff] at key
  exact EReal.coe_ne_top _ key

/-- **`ProductModelHeight` forces metrizations of the right factor** (proved). -/
theorem metrizable_right_of_productModelHeight (h : ProductModelHeight)
    (hPM : IsProductModel eC 𝒢P 𝒢₁ 𝒢₂) {g : ℕ} (MP : MetrizedModel C L g) (hMP : MP.model = 𝒢P)
    (h₁ : 𝒢₁.height ≠ ⊥) : ∃ (g₂ : ℕ) (M₂ : MetrizedModel B L g₂), M₂.model = 𝒢₂ := by
  by_contra hn
  have h2 := height_eq_top_of_not_metrizable hn
  have key := le_of_productModelHeight h hPM MP hMP
  rw [h2, EReal.add_top_of_ne_bot h₁, top_le_iff] at key
  exact EReal.coe_ne_top _ key

end Forces

/-- **`ProductModelHeight` forces uniformizations of the left factor** (proved): if the product
model has a metrization and `h(𝒢₂) ≠ ⊥`, then at every `τ` the complex points `𝒢₁(ℂ)_τ` have an
analytic uniformization with a full discrete lattice as kernel (the conclusion of
`AnalyticUniformizationExists` for `𝒢₁`, obtained from the product's; elementary, see §6). -/
theorem analyticUnif_left_of_productModelHeight (h : ProductModelHeight)
    {K : Type} [Field K] {A B C : AbVar K} {eC : C.X ≅ A.X ⊗ B.X} {L : Type} [Field L]
    [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (hPM : IsProductModel eC 𝒢P 𝒢₁ 𝒢₂) {g : ℕ}
    (MP : MetrizedModel C L g) (hMP : MP.model = 𝒢P) (h₂ : 𝒢₂.height ≠ ⊥) (τ : L →+* ℂ) :
    ∃ (g₁ : ℕ) (Λ : Submodule ℤ (Fin g₁ → ℂ)) (Φ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢₁.IsAnalyticUniformization τ Λ Φ := by
  obtain ⟨g₁, M₁, rfl⟩ := metrizable_left_of_productModelHeight h hPM MP hMP h₂
  obtain ⟨Φ, hΦ, -⟩ := M₁.arch τ
  exact ⟨g₁, _, Φ, M₁.hodge.periods_discrete τ, M₁.hodge.periods_isZLattice τ, hΦ⟩

/-! ## §5. Complex points of a product model, and the product uniformization (algebraic half)

For `e : 𝒢P ≅ 𝒢₁ ⊗ 𝒢₂` with homomorphic components, `𝒢P(ℂ)_τ ≅ 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` as groups
(`ptsEquiv`, proved). For uniformizations `Φ₁`, `Φ₂` of the factors, the product
`Φ(z) = (Φ₁(z₁), Φ₂(z₂))` (`z = Fin.append z₁ z₂`) satisfies the three algebraic clauses of
`IsAnalyticUniformization` with kernel `Λ₁ × Λ₂` (`prodUnif_clauses`, proved); the two analytic
clauses (openness of `Φ⁻¹(U(ℂ))`, holomorphy of regular functions along `Φ`) are the glue Prop
`ProductUnifAnalytic`. This is the "easy" direction (products of uniformizations), used by
`ProductMetrizationGeo`; it is not the splitting of §1. -/

section Points

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
  {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}

/-- The two projections on complex points, as one homomorphism. -/
noncomputable def ptsProj (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] (τ : L →+* ℂ) : 𝒢P.Pts τ →* 𝒢₁.Pts τ × 𝒢₂.Pts τ :=
  (IsMonHom.monoidHom (e.hom ≫ fst _ _) (GroupModel.ptC τ)).prod
    (IsMonHom.monoidHom (e.hom ≫ snd _ _) (GroupModel.ptC τ))

theorem ptsProj_bijective (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] (τ : L →+* ℂ) : Function.Bijective (ptsProj e τ) := by
  constructor
  · intro p q hpq
    simp only [ptsProj, MonoidHom.prod_apply, IsMonHom.monoidHom_apply, Prod.mk.injEq] at hpq
    rw [← cancel_mono e.hom]
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc] using hpq.1
    · simpa only [Category.assoc] using hpq.2
  · rintro ⟨a, b⟩
    refine ⟨lift a b ≫ e.inv, ?_⟩
    simp only [ptsProj, MonoidHom.prod_apply, IsMonHom.monoidHom_apply, Category.assoc,
      Iso.inv_hom_id_assoc, lift_fst, lift_snd]

/-- **`𝒢P(ℂ)_τ ≅ 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` as groups (proved).** -/
noncomputable def ptsEquiv (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] (τ : L →+* ℂ) : 𝒢P.Pts τ ≃* 𝒢₁.Pts τ × 𝒢₂.Pts τ :=
  MulEquiv.ofBijective (ptsProj e τ) (ptsProj_bijective e τ)

/-- The lattice `Λ₁ × Λ₂ ⊂ ℂ^{g₁+g₂}` (coordinates `Fin.append`). -/
def prodLattice {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) :
    Submodule ℤ (Fin (g₁ + g₂) → ℂ) :=
  Λ₁.comap (LinearMap.funLeft ℤ ℂ (Fin.castAdd g₂)) ⊓
    Λ₂.comap (LinearMap.funLeft ℤ ℂ (Fin.natAdd g₁))

/-- The product uniformization `z ↦ (Φ₁(z₁), Φ₂(z₂))`. -/
noncomputable def prodUnif (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) : (Fin (g₁ + g₂) → ℂ) → 𝒢P.Pts τ := fun z =>
  (ptsEquiv e τ).symm (Φ₁ fun i => z (Fin.castAdd g₂ i), Φ₂ fun i => z (Fin.natAdd g₁ i))

/-- **The algebraic clauses of `IsAnalyticUniformization` for the product (proved).** -/
theorem prodUnif_clauses (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)}
    {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ}
    {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ} (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    (∀ z w, prodUnif e Φ₁ Φ₂ (z + w) = prodUnif e Φ₁ Φ₂ z * prodUnif e Φ₁ Φ₂ w) ∧
    (∀ z, prodUnif e Φ₁ Φ₂ z = 1 ↔ z ∈ prodLattice Λ₁ Λ₂) ∧
    Function.Surjective (prodUnif e Φ₁ Φ₂) := by
  obtain ⟨m₁, k₁, s₁, -, -⟩ := h₁
  obtain ⟨m₂, k₂, s₂, -, -⟩ := h₂
  refine ⟨fun z w => ?_, fun z => ?_, fun p => ?_⟩
  · simp only [prodUnif, ← map_mul, Prod.mk_mul_mk]
    congr 2
    · exact m₁ _ _
    · exact m₂ _ _
  · simp only [prodUnif, MulEquiv.map_eq_one_iff, Prod.mk_eq_one, k₁, k₂, prodLattice,
      Submodule.mem_inf, Submodule.mem_comap]
    rfl
  · obtain ⟨z₁, hz₁⟩ := s₁ (ptsEquiv e τ p).1
    obtain ⟨z₂, hz₂⟩ := s₂ (ptsEquiv e τ p).2
    refine ⟨Fin.append z₁ z₂, ?_⟩
    simp only [prodUnif, Fin.append_left, Fin.append_right, hz₁, hz₂, Prod.mk.eta,
      MulEquiv.symm_apply_apply]

/-- **Glue (analytic half of the product uniformization).** For analytic uniformizations `Φ₁`,
`Φ₂` of the factors, the product uniformization satisfies the two analytic clauses of
`IsAnalyticUniformization`: each `Φ⁻¹(U(ℂ))` is open and each regular function on an open of
`𝒢P` is holomorphic along `Φ` there. Why true (STANDARD): the affine products
`U₁ ×_{𝓞_L} U₂ = Spec(R₁ ⊗ R₂)` cover `𝒢₁ ×_{𝓞_L} 𝒢₂`, and their basic opens `D(f)`,
`f = Σ aᵢ ⊗ bᵢ`, form a basis (products of opens alone do not: the Zariski topology of a product
is finer than the product topology). On `U₁ × U₂` the preimage under `Φ` is
`Φ₁⁻¹(U₁) × Φ₂⁻¹(U₂)` (open), the value of `a ⊗ b` at `Φ z` is `a(Φ₁ z₁) b(Φ₂ z₂)` (holomorphic),
so `Φ⁻¹(D(f))` is open and the sections `h / fⁿ` of `D(f)` are holomorphic along `Φ`; both
properties are local (EGA I 3.2.2 / Stacks 01JR for the affine product, UNVERIFIED). Needs
Mathlib's affine fibre products (`pullbackSpecIso`) and the comparison of evaluations; unproved.
No AN3 input. -/
def ProductUnifAnalytic : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
      (∀ U, IsOpen (𝒢P.dom (prodUnif e Φ₁ Φ₂) U)) ∧
      (∀ U (s : Γ(𝒢P.G.left, U)),
        DifferentiableOn ℂ (fun z => 𝒢P.evalAt (prodUnif e Φ₁ Φ₂ z) U s)
          (𝒢P.dom (prodUnif e Φ₁ Φ₂) U))

/-- **The product of analytic uniformizations is an analytic uniformization of the product
model, with lattice `Λ₁ × Λ₂`** (proved from `ProductUnifAnalytic`). -/
theorem prodUnif_isAnalyticUniformization (hA : ProductUnifAnalytic)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)}
    {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ}
    {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ} (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodUnif e Φ₁ Φ₂) := by
  obtain ⟨hm, hk, hs⟩ := prodUnif_clauses e h₁ h₂
  obtain ⟨ho, hd⟩ := hA K A B C L 𝒢P 𝒢₁ 𝒢₂ e τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  exact ⟨hm, hk, hs, ho, hd⟩

/-- The splitting direction, formal part: for any uniformization `Φ` of the product, `p₁ ∘ Φ`
is a surjective homomorphism `ℂ^g → 𝒢₁(ℂ)_τ` (proved). Its kernel `Φ⁻¹(1 × 𝒢₂(ℂ)_τ)` is not
discrete when `𝒢₂(ℂ)_τ` is infinite; a uniformization of `𝒢₁` is extracted by restricting `Φ`
to the identity component of `ker(p₂ ∘ Φ)` (§6, `ProductUnifSplits`; elementary). -/
theorem proj_comp_unif (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢P.Pts τ} (hΦ : 𝒢P.IsAnalyticUniformization τ Λ Φ) :
    (∀ z w, (ptsEquiv e τ (Φ (z + w))).1 = (ptsEquiv e τ (Φ z)).1 * (ptsEquiv e τ (Φ w)).1) ∧
    Function.Surjective fun z => (ptsEquiv e τ (Φ z)).1 := by
  obtain ⟨m, -, s, -, -⟩ := hΦ
  refine ⟨fun z w => by rw [m, map_mul, Prod.fst_mul], fun a => ?_⟩
  obtain ⟨z, hz⟩ := s ((ptsEquiv e τ).symm (a, 1))
  exact ⟨z, by simp only [hz, MulEquiv.apply_symm_apply]⟩

end Points


/-! ## §5b. The product lattice (copied from `Lattice.lean`, which compiles standalone)

`Λ₁ × Λ₂` is a full discrete lattice with `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`
(`prodLattice_facts`, proved): the covolume clause of `ProductMetrizationGeo` and of S-alg for
the product lattice. -/

section LatticeProd

open Module ZSpan

section LatticeGeneral

variable {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] [MeasurableSpace E₁]
  [BorelSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] [MeasurableSpace E₂]
  [BorelSpace E₂]
  (Λ₁ : Submodule ℤ E₁) (Λ₂ : Submodule ℤ E₂)

omit [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] [MeasurableSpace E₂] [BorelSpace E₂] in
theorem discreteTopology_prod [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] :
    DiscreteTopology (Λ₁.prod Λ₂) := by
  let f : Λ₁.prod Λ₂ → Λ₁ × Λ₂ := fun x =>
    (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
  have hf : Continuous f := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  have : ({x} : Set (Λ₁.prod Λ₂)) = f ⁻¹' {f x} := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]
  rw [this]
  exact (isOpen_discrete _).preimage hf

instance instDiscreteTopologyProd [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] :
    DiscreteTopology (Λ₁.prod Λ₂) :=
  discreteTopology_prod Λ₁ Λ₂

instance instIsZLatticeProd [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₁]
    [IsZLattice ℝ Λ₂] : IsZLattice ℝ (Λ₁.prod Λ₂) := by
  refine ⟨?_⟩
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have hx : x ∈ Submodule.span ℝ (Λ₁ : Set E₁) := by rw [IsZLattice.span_top]; trivial
  have hy : y ∈ Submodule.span ℝ (Λ₂ : Set E₂) := by rw [IsZLattice.span_top]; trivial
  have h1 : Submodule.map (LinearMap.inl ℝ E₁ E₂) (Submodule.span ℝ (Λ₁ : Set E₁)) ≤
      Submodule.span ℝ ((Λ₁.prod Λ₂ : Submodule ℤ (E₁ × E₂)) : Set (E₁ × E₂)) := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.mem_prod.mpr ⟨ha, Λ₂.zero_mem⟩
  have h2 : Submodule.map (LinearMap.inr ℝ E₁ E₂) (Submodule.span ℝ (Λ₂ : Set E₂)) ≤
      Submodule.span ℝ ((Λ₁.prod Λ₂ : Submodule ℤ (E₁ × E₂)) : Set (E₁ × E₂)) := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.mem_prod.mpr ⟨Λ₁.zero_mem, ha⟩
  have : ((x, y) : E₁ × E₂) = LinearMap.inl ℝ E₁ E₂ x + LinearMap.inr ℝ E₁ E₂ y := by simp
  rw [this]
  exact Submodule.add_mem _ (h1 ⟨x, hx, rfl⟩) (h2 ⟨y, hy, rfl⟩)

/-- Unique translates into the fundamental domain of a basis, for the lattice itself. -/
theorem exists_unique_add_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {κ : Type*} [Fintype κ] (b : Basis κ ℤ L) (x : E) :
    ∃! l : L, (l : E) + x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ) := by
  have hs := b.ofZLatticeBasis_span ℝ
  obtain ⟨v, hv, hu⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) x
  refine ⟨⟨v, hs.le v.2⟩, hv, fun l hl => ?_⟩
  have := hu ⟨l, hs.ge l.2⟩ hl
  have h : ((⟨(l : E), hs.ge l.2⟩ : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ))) : E) =
      (v : E) := congrArg Subtype.val this
  exact Subtype.ext h

theorem isAddFundamentalDomain_prod [DiscreteTopology Λ₁] [DiscreteTopology Λ₂]
    [IsZLattice ℝ Λ₁] [IsZLattice ℝ Λ₂] {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (b₁ : Basis κ₁ ℤ Λ₁) (b₂ : Basis κ₂ ℤ Λ₂) (μ₁ : Measure E₁) (μ₂ : Measure E₂) :
    IsAddFundamentalDomain (Λ₁.prod Λ₂)
      (fundamentalDomain (b₁.ofZLatticeBasis ℝ) ×ˢ fundamentalDomain (b₂.ofZLatticeBasis ℝ))
      (μ₁.prod μ₂) := by
  refine IsAddFundamentalDomain.mk' (((fundamentalDomain_measurableSet _).prod
    (fundamentalDomain_measurableSet _)).nullMeasurableSet) fun x => ?_
  obtain ⟨l₁, h₁, u₁⟩ := exists_unique_add_mem Λ₁ b₁ x.1
  obtain ⟨l₂, h₂, u₂⟩ := exists_unique_add_mem Λ₂ b₂ x.2
  refine ⟨⟨((l₁ : E₁), (l₂ : E₂)), Submodule.mem_prod.mpr ⟨l₁.2, l₂.2⟩⟩, ⟨h₁, h₂⟩, ?_⟩
  rintro ⟨⟨y₁, y₂⟩, hy⟩ hm
  obtain ⟨hm₁, hm₂⟩ := hm
  have e1 := u₁ ⟨y₁, (Submodule.mem_prod.mp hy).1⟩ hm₁
  have e2 := u₂ ⟨y₂, (Submodule.mem_prod.mp hy).2⟩ hm₂
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)

/-- **`covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`** (proved). -/
theorem covolume_prod [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₁]
    [IsZLattice ℝ Λ₂] (μ₁ : Measure E₁) (μ₂ : Measure E₂) [μ₁.IsAddHaarMeasure]
    [μ₂.IsAddHaarMeasure] :
    ZLattice.covolume (Λ₁.prod Λ₂) (μ₁.prod μ₂) =
      ZLattice.covolume Λ₁ μ₁ * ZLattice.covolume Λ₂ μ₂ := by
  let b₁ := Free.chooseBasis ℤ Λ₁
  let b₂ := Free.chooseBasis ℤ Λ₂
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (Λ₁.prod Λ₂) (μ₁.prod μ₂)
      (isAddFundamentalDomain_prod Λ₁ Λ₂ b₁ b₂ μ₁ μ₂),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ₁ μ₁ (ZLattice.isAddFundamentalDomain b₁ μ₁),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ₂ μ₂ (ZLattice.isAddFundamentalDomain b₂ μ₂),
    measureReal_def, measureReal_def, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]

end LatticeGeneral

section LatticeSplit

/-- `ℂ^{g₁+g₂} ≅ ℂ^{g₁} × ℂ^{g₂}`, `z ↦ (z ∘ castAdd, z ∘ natAdd)`. -/
def splitLE (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) ≃ₗ[ℝ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) where
  toFun z := (fun i => z (Fin.castAdd g₂ i), fun i => z (Fin.natAdd g₁ i))
  invFun p := Fin.append p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv p := by ext i <;> simp

/-- The continuous version. -/
noncomputable def splitCL (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) ≃L[ℝ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) :=
  (splitLE g₁ g₂).toContinuousLinearEquiv

theorem splitCL_apply (g₁ g₂ : ℕ) (z : Fin (g₁ + g₂) → ℂ) :
    splitCL g₁ g₂ z = (fun i => z (Fin.castAdd g₂ i), fun i => z (Fin.natAdd g₁ i)) := rfl

theorem splitCL_measurePreserving (g₁ g₂ : ℕ) :
    MeasurePreserving (splitCL g₁ g₂) volume volume := by
  have h1 := MeasurePreserving.symm _
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (g₁ + g₂) => ℂ) finSumFinEquiv)
  have h2 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)
  have h := h2.comp h1
  convert h using 1
  funext z
  rw [splitCL_apply]
  ext i
  · simp only [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi,
      Equiv.sumPiEquivProdPi_apply]
    show z _ = (Equiv.piCongrLeft (fun _ => ℂ) finSumFinEquiv).symm z (Sum.inl i)
    rw [Equiv.piCongrLeft_symm_apply, finSumFinEquiv_apply_left]
  · simp only [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi,
      Equiv.sumPiEquivProdPi_apply]
    show z _ = (Equiv.piCongrLeft (fun _ => ℂ) finSumFinEquiv).symm z (Sum.inr i)
    rw [Equiv.piCongrLeft_symm_apply, finSumFinEquiv_apply_right]

theorem prodLattice_eq_comap {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) :
    prodLattice Λ₁ Λ₂ = ZLattice.comap ℝ (Λ₁.prod Λ₂) (splitCL g₁ g₂).toLinearMap := by
  ext z
  simp only [prodLattice, Submodule.mem_inf, Submodule.mem_comap]
  rfl

/-- **The product lattice is a full discrete lattice with `covol = covol Λ₁ · covol Λ₂`**
(proved). -/
theorem prodLattice_facts {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) [DiscreteTopology Λ₁] [IsZLattice ℝ Λ₁]
    [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₂] :
    ∃ _ : DiscreteTopology (prodLattice Λ₁ Λ₂), IsZLattice ℝ (prodLattice Λ₁ Λ₂) ∧
      ZLattice.covolume (prodLattice Λ₁ Λ₂) = ZLattice.covolume Λ₁ * ZLattice.covolume Λ₂ := by
  have h01 : (volume : Measure (Fin g₁ → ℂ)).IsAddHaarMeasure := inferInstance
  have h02 : (volume : Measure (Fin g₂ → ℂ)).IsAddHaarMeasure := inferInstance
  have : (volume : Measure ((Fin g₁ → ℂ) × (Fin g₂ → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin g₁ → ℂ))
      (volume : Measure (Fin g₂ → ℂ))
  rw [prodLattice_eq_comap]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [ZLattice.covolume_comap (Λ₁.prod Λ₂) volume volume (splitCL_measurePreserving g₁ g₂)]
  exact covolume_prod Λ₁ Λ₂ volume volume

end LatticeSplit

/-- **A product of full-lattice uniformizations is a full-lattice uniformization of the product**
(proved from `ProductUnifAnalytic`): the conclusion of `AnalyticUniformizationExists` for the
product model, from the factors'. -/
theorem prodUnif_fullLattice (hA : ProductUnifAnalytic) {K : Type} [Field K] {A B C : AbVar K}
    {L : Type} [Field L] [NumberField L] [Algebra K L] {𝒢P : GroupModel C L}
    {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G)
    [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ}
    {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} [DiscreteTopology Λ₁]
    [DiscreteTopology Λ₂] (hl₁ : IsZLattice ℝ Λ₁) (hl₂ : IsZLattice ℝ Λ₂)
    {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}
    (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁) (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    ∃ _ : DiscreteTopology (prodLattice Λ₁ Λ₂), IsZLattice ℝ (prodLattice Λ₁ Λ₂) ∧
      ZLattice.covolume (prodLattice Λ₁ Λ₂) = ZLattice.covolume Λ₁ * ZLattice.covolume Λ₂ ∧
      𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodUnif e Φ₁ Φ₂) := by
  obtain ⟨hd, hz, hc⟩ := prodLattice_facts Λ₁ Λ₂
  exact ⟨hd, hz, hc, prodUnif_isAnalyticUniformization hA e h₁ h₂⟩

end LatticeProd

/-! ## §6. Route S refined: the splitting is elementary (no AN3)

An independent model review (log) pointed out that the splitting needed by route S uses only the
product's own uniformization, so neither half of AN3 is needed (the author re-checked each
step). Let `Φ` uniformize
`𝒢P(ℂ)_τ = 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` with full discrete kernel `Λ`, and let `Kᵢ = ker(pᵢ ∘ Φ)`.
- `K₁` is closed: the complement `U` of the closure of `p₁⁻¹(unit section)` is Zariski open, and
  among the `τ`-points only those with `p₁ x = 1` meet that closure (the unit section of the
  separated `𝒢₁` is a closed immersion, and `Spec ℂ → Spec 𝓞_L` over `τ` is unique); so
  `{z | p₁Φ(z) ≠ 1} = dom Φ U` is open (clause 4).
- The identity component `W₂` of `K₁` is a real subspace (closed subgroups of `ℝ^{2g}`), and it
  is complex: `t ↦ f(p₁ Φ(t w))` is holomorphic (clause 5) and constant on `ℝ`, hence constant
  near `0`; a `τ`-point of an affine open is determined by its function values, so `t w ∈ K₁`
  for small complex `t`, and `ℂ w ⊆ W₂`.
- `K₁ + K₂ = ℂ^g` (surjectivity), so `W₁ + W₂ = ℂ^g` (Baire). `W₁ ∩ W₂ ⊆ Λ` is discrete, hence
  `0`.
- So `Φ` restricted to `Wᵢ` gives uniformizations `Φᵢ` of the factors, and `Φ ∘ T = Φ₁ × Φ₂` for
  a linear `T`.

This analytic step is the glue Prop `ProductUnifSplits`. The rest is the Hodge-theoretic glue
`ProductMetrizationOfProductUnif`, mirror image of `ProductMetrizationGeo`. The change of
coordinates is proved here (`recoordM`, from def-faltings' `HodgeData.recoord`,
`GroupModel.jacDet_comp` and `HodgeData.modelHeight_recoord`). -/

section Recoord

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **Precomposing an analytic uniformization with a `ℂ`-linear automorphism `T`** gives an
analytic uniformization with lattice `T⁻¹ Λ` (proved). -/
theorem isAnalyticUniformization_comp {𝒢 : GroupModel A L} {τ : L →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (h : 𝒢.IsAnalyticUniformization τ Λ Φ) (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) :
    𝒢.IsAnalyticUniformization τ (ZLattice.comap ℝ Λ (realify T).toLinearMap)
      (fun z => Φ (T z)) := by
  obtain ⟨hm, hk, hs, ho, hd⟩ := h
  have hTc : Continuous (T : (Fin g → ℂ) → (Fin g → ℂ)) := (realify T).continuous
  refine ⟨fun z w => by simp only [map_add, hm], fun z => ?_, fun p => ?_, fun U => ?_,
    fun U s => ?_⟩
  · rw [hk]; rfl
  · obtain ⟨w, rfl⟩ := hs p
    exact ⟨T.symm w, by simp⟩
  · exact (ho U).preimage hTc
  · let T' : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
      LinearMap.toContinuousLinearMap (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    exact (hd U s).comp T'.differentiableOn (fun z hz => hz)

/-- **Change of linear coordinates of a metrized model** (proved): same group model, Hodge data
`hodge.recoord T`, uniformizations `Φ ∘ T_τ`. -/
noncomputable def recoordM {g : ℕ} (M : MetrizedModel A L g)
    (T : (L →+* ℂ) → ((Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))) : MetrizedModel A L g where
  model := M.model
  hodge := M.hodge.recoord T
  lattice_eq := M.lattice_eq
  arch τ := by
    obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
    refine ⟨fun z => Φ (T τ z), isAnalyticUniformization_comp hΦ (T τ), fun f => ?_⟩
    show (LinearMap.det (T τ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) • M.hodge.coeff τ)
      (M.model.wedge f) = _
    rw [GroupModel.jacDet_comp, LinearMap.smul_apply, hc, smul_eq_mul, mul_comm]

theorem recoordM_model {g : ℕ} (M : MetrizedModel A L g)
    (T : (L →+* ℂ) → ((Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))) : (recoordM M T).model = M.model := rfl

theorem recoordM_modelHeight {g : ℕ} (M : MetrizedModel A L g)
    (T : (L →+* ℂ) → ((Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))) :
    (recoordM M T).hodge.modelHeight = M.hodge.modelHeight :=
  HodgeData.modelHeight_recoord _ _

end Recoord

/-! ## §6b. Clauses 4 and 5 transport along morphisms and linear maps (pieces of S-an)

In S-an the factor uniformizations are `Φᵢ = pᵢ ∘ Φ ∘ ℓᵢ` for linear embeddings `ℓᵢ`. Their
analytic clauses (openness of `dom`, holomorphy of regular functions) follow formally from those
of `Φ`: `analyticClauses_comp` (along any morphism of `𝓞_L`-schemes, via `evalAt_comp`) and
`analyticClauses_precomp` (along any `ℂ`-linear map). Proved. -/

section MorphComp

variable {K : Type} [Field K] {A B : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

theorem dom_comp (𝒢 : GroupModel A L) (𝒢' : GroupModel B L) (f : 𝒢.G ⟶ 𝒢'.G) {τ : L →+* ℂ}
    {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (U : 𝒢'.G.left.Opens) :
    𝒢'.dom (fun z => Φ z ≫ f) U = 𝒢.dom Φ (f.left ⁻¹ᵁ U) := rfl

/-- **Values of regular functions along a morphism** (proved):
`s(f ∘ p) = (f* s)(p)`. -/
theorem evalAt_comp (𝒢 : GroupModel A L) (𝒢' : GroupModel B L) (f : 𝒢.G ⟶ 𝒢'.G)
    {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢'.G.left.Opens) (s : Γ(𝒢'.G.left, U)) :
    𝒢'.evalAt (p ≫ f) U s = 𝒢.evalAt p (f.left ⁻¹ᵁ U) (f.left.app U s) := by
  unfold GroupModel.evalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (f.left ⁻¹ᵁ U)
  · rw [dif_pos (show ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U from h), dif_pos h]
    congr 1
  · rw [dif_neg (show ¬ ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U from h), dif_neg h]

/-- **Clauses 4 and 5 transport along a morphism of `𝓞_L`-schemes** (proved). -/
theorem analyticClauses_comp (𝒢 : GroupModel A L) (𝒢' : GroupModel B L) (f : 𝒢.G ⟶ 𝒢'.G)
    {τ : L →+* ℂ} {g : ℕ} {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (ho : ∀ U, IsOpen (𝒢.dom Φ U))
    (hd : ∀ U (s : Γ(𝒢.G.left, U)),
      DifferentiableOn ℂ (fun z => 𝒢.evalAt (Φ z) U s) (𝒢.dom Φ U)) :
    (∀ U, IsOpen (𝒢'.dom (fun z => Φ z ≫ f) U)) ∧
    (∀ U (s : Γ(𝒢'.G.left, U)), DifferentiableOn ℂ (fun z => 𝒢'.evalAt (Φ z ≫ f) U s)
      (𝒢'.dom (fun z => Φ z ≫ f) U)) := by
  refine ⟨fun U => ?_, fun U s => ?_⟩
  · rw [dom_comp]; exact ho _
  · rw [dom_comp]
    simp only [evalAt_comp]
    exact hd _ _

/-- **Clauses 4 and 5 transport along a `ℂ`-linear map** `ℓ : ℂ^{g'} → ℂ^g` (proved). -/
theorem analyticClauses_precomp (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g g' : ℕ}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (ℓ : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (ho : ∀ U, IsOpen (𝒢.dom Φ U))
    (hd : ∀ U (s : Γ(𝒢.G.left, U)),
      DifferentiableOn ℂ (fun z => 𝒢.evalAt (Φ z) U s) (𝒢.dom Φ U)) :
    (∀ U, IsOpen (𝒢.dom (fun z => Φ (ℓ z)) U)) ∧
    (∀ U (s : Γ(𝒢.G.left, U)), DifferentiableOn ℂ (fun z => 𝒢.evalAt (Φ (ℓ z)) U s)
      (𝒢.dom (fun z => Φ (ℓ z)) U)) := by
  let ℓ' : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap ℓ
  refine ⟨fun U => (ho U).preimage ℓ'.continuous, fun U s => ?_⟩
  exact (hd U s).comp ℓ'.differentiableOn (fun z hz => hz)

/-- **The analytic clauses of the factor uniformizations in S-an** (proved): for `e : 𝒢P ≅ 𝒢₁ ⊗ 𝒢₂`,
an analytic uniformization `Φ` of the product and any `ℂ`-linear `ℓ : ℂ^{g₁} → ℂ^g`, the map
`z ↦ p₁(Φ(ℓ z))` satisfies clauses 4 and 5 for `𝒢₁`. -/
theorem proj_analyticClauses {C : AbVar K} {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g g₁ : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢P.Pts τ} (hΦ : 𝒢P.IsAnalyticUniformization τ Λ Φ)
    (ℓ : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    (∀ U, IsOpen (𝒢₁.dom (fun z => (ptsEquiv e τ (Φ (ℓ z))).1) U)) ∧
    (∀ U (s : Γ(𝒢₁.G.left, U)),
      DifferentiableOn ℂ (fun z => 𝒢₁.evalAt (ptsEquiv e τ (Φ (ℓ z))).1 U s)
        (𝒢₁.dom (fun z => (ptsEquiv e τ (Φ (ℓ z))).1) U)) := by
  obtain ⟨-, -, -, ho, hd⟩ := hΦ
  obtain ⟨ho', hd'⟩ := analyticClauses_precomp 𝒢P ℓ ho hd
  exact analyticClauses_comp 𝒢P 𝒢₁ (e.hom ≫ fst _ _) ho' hd'

end MorphComp

/-- **Glue S-an (splitting of a uniformization of a product; elementary analysis, no AN3).**
Let `e : 𝒢P ≅ 𝒢₁ ⊗ 𝒢₂` have homomorphic components. Every analytic uniformization `Φ` of
`𝒢P(ℂ)_τ` with a full discrete lattice `Λ ⊂ ℂ^g` as kernel splits: for some `g₁ + g₂ = g`, full
discrete lattices `Λᵢ ⊂ ℂ^{gᵢ}`, analytic uniformizations `Φᵢ` of `𝒢ᵢ(ℂ)_τ` with kernels `Λᵢ` and a
`ℂ`-linear automorphism `T`, we have `Φ ∘ T = Φ₁ × Φ₂` (`prodUnif`, coordinates `Fin.append`).

Why true (STANDARD, argued in the section header; no uniformization theorem is used). The
ingredients are the structure of closed subgroups of `ℝⁿ` (Bourbaki, *Topologie générale* VII §1,
UNVERIFIED; small elements of a closed subgroup lie in its identity component), the identity
theorem in one complex variable, Baire's theorem, the fact that a `τ`-point of an affine open is
determined by its function values, and the compatibility of `evalAt` with the projections.
Then `Φᵢ = pᵢ ∘ Φ|_{Wᵢ}` with
`Wᵢ = ker(p_{3-i} ∘ Φ)⁰`, `Λᵢ = Λ ∩ Wᵢ`. Unproved. -/
def ProductUnifSplits : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (Φ : (Fin g → ℂ) → 𝒢P.Pts τ), IsZLattice ℝ Λ → 𝒢P.IsAnalyticUniformization τ Λ Φ →
    ∃ (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
      (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
      (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) ∧ (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) ∧
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ ∧ 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ ∧
      ∀ z, Φ (T z) = prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))

/-- **Glue S-alg (metrizations of the factors from a product-form metrization; Hodge theory, no
AN3).** Let `e : MP.model ≅ 𝒢₁ ⊗ 𝒢₂` have homomorphic components. Suppose that at every `τ` the
metrization `MP` of the product model is in product form: its period lattice is `Λ₁ × Λ₂` and its
coefficient map is computed by `Φ₁ × Φ₂`, for full discrete lattices `Λᵢ ⊂ ℂ^{gᵢ(τ)}` and analytic
uniformizations `Φᵢ` of the factors. Then the factors have metrizations `M₁`, `M₂` with
`h(M₁) + h(M₂) ≤ h(MP)`.

Why true (STANDARD; mirror image of `ProductMetrizationGeo`).
- `gᵢ(τ) = dim 𝒢ᵢ`: `MP.hodge.finrank_eq_one` gives `g ∈ {0, d₁ + d₂}` (if `g = 0`, the factors'
  complex points are trivial and `dᵢ = 0`); otherwise, with the algebraic splitting
  `cotangent_P = cotangent₁ ⊕ cotangent₂`, the wedge of `p₁*f, p₂*h` (bases) is nonzero, so
  `coeff ≠ 0` makes the block-shaped Jacobian of `Φ₁ × Φ₂` at `0` nonsingular.
- `ω_{MP} = ω₁ ⊕ ω₂` and `⋀^{top}ω_{MP} = ⋀ω₁ ⊗ ⋀ω₂`.
- `jacDet Φᵢ` descends to a semilinear map on `⋀^{gᵢ}`.
- Indices, coefficients and covolumes multiply (`modelHeight_add_of`); equality holds.

Unproved. -/
def ProductMetrizationOfProductUnif : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)],
    (∀ τ : L →+* ℂ, ∃ (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
        (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
        (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
        (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) ∧
        (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) ∧
        𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ ∧ 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ ∧
        (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) ∧
        ∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
          MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    ∃ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ ∧ M₂.model = 𝒢₂ ∧
      M₁.hodge.modelHeight + M₂.hodge.modelHeight ≤ MP.hodge.modelHeight

/-- **`ProductMetrizationSplit` from S-an and S-alg (proved).** The change of coordinates
`Φ ↦ Φ ∘ T_τ` is done by `recoordM`, which does not change the height. -/
theorem productMetrizationSplit_of_splits (hS : ProductUnifSplits)
    (hA : ProductMetrizationOfProductUnif) : ProductMetrizationSplit := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hPM g MP hMP
  obtain ⟨e, he₁, he₂, -⟩ := hPM
  subst hMP
  have key : ∀ τ : L →+* ℂ, ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      ∃ (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
        (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
        (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
        (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) ∧
        (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) ∧
        𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ ∧ 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ ∧
        (∀ z, T z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) ∧
        ∀ f, LinearMap.det (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) *
            MP.hodge.coeff τ (MP.model.wedge f) =
          MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f := by
    intro τ
    obtain ⟨Φ, hΦ, hc⟩ := MP.arch τ
    have := MP.hodge.periods_discrete τ
    obtain ⟨g₁, g₂, hg, Λ₁, Λ₂, Φ₁, Φ₂, T, hl₁, hl₂, hu₁, hu₂, hT⟩ :=
      hS K A B C L MP.model 𝒢₁ 𝒢₂ e τ g (MP.hodge.periods τ) Φ
        (MP.hodge.periods_isZLattice τ) hΦ
    refine ⟨T, g₁, g₂, hg, Λ₁, Λ₂, Φ₁, Φ₂, hl₁, hl₂, hu₁, hu₂, fun z => ?_, fun f => ?_⟩
    · rw [← hΦ.2.1, hT, (prodUnif_clauses e hu₁ hu₂).2.1]
    · have hfun : (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) =
          fun z => Φ (T z) := funext fun z => (hT z).symm
      rw [hfun, GroupModel.jacDet_comp, hc, mul_comm]
  choose T g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco using key
  obtain ⟨h₁, h₂, M₁, M₂, hM₁, hM₂, hle⟩ := @hA K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g (recoordM MP T) e he₁ he₂
    (fun τ => ⟨g₁ τ, g₂ τ, hg τ, Λ₁ τ, Λ₂ τ, Φ₁ τ, Φ₂ τ, hl₁ τ, hl₂ τ, hu₁ τ, hu₂ τ,
      fun z => hper τ z, fun f => by
        show (LinearMap.det (T τ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) • MP.hodge.coeff τ)
          (MP.model.wedge f) = _
        rw [LinearMap.smul_apply, smul_eq_mul]
        exact hco τ f⟩)
  exact ⟨h₁, h₂, M₁, M₂, hM₁, hM₂, hle.trans_eq (recoordM_modelHeight MP T)⟩

/-- **`ProductModelHeight` from S-an and S-alg (proved).** Neither half of AN3 is used: no
`AnalyticUniformizationExists`, no `AnalyticUniformizationUnique`, no `MetrizationExists`. -/
theorem productModelHeight_of_splits (hS : ProductUnifSplits)
    (hA : ProductMetrizationOfProductUnif) : ProductModelHeight :=
  productModelHeight_of_split (productMetrizationSplit_of_splits hS hA)

end ZInQ.ProductHeight

/-! ## g0-assemble2: g10-odd and conj-twist (G10Glue)

* scratch/g10-odd/G10Odd.lean §2-§3 (lines 99-246, verbatim): `ConjTwistNontrivial` and
  `g10Glue_of_conjTwist`. Its proof `intro _ _ hF …` applies unchanged to g0-assemble's corrected
  `G10Glue` (hypotheses `T11a → T11b → FaltingsTate`, same binder count as the opaque version).
* scratch/conj-twist/ConjTwist.lean lines 84-192 and 206-1612 (verbatim; its §1 copies of `resQ`,
  `isComplexConj_mul_self`, `one_tmul_injective`, `baseChange_injective'`, `ConjTwistNontrivial`
  (= g10-odd's above), `qEmbRing` and `resQ_spec` (= part 70's, same text) are not repeated).
-/
section G10OddSec
namespace G0Galois
open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-! ## §2. The algebraic part (proved) -/

open scoped TensorProduct

/-- A `2 × 2` involution over a field that is not `±1` has determinant `−1` (trace `0`). -/
theorem det_eq_neg_one_of_sq_eq_one {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (h2 : M * M = 1) (h1 : M ≠ 1) (hm1 : M ≠ -1) : M.det = -1 := by
  have e00 := congrFun (congrFun h2 0) 0
  have e01 := congrFun (congrFun h2 0) 1
  have e10 := congrFun (congrFun h2 1) 0
  have e11 := congrFun (congrFun h2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two]
  by_cases ht : M 0 0 + M 1 1 = 0
  · have : M 1 1 = -M 0 0 := by linear_combination ht
    rw [this]; linear_combination -e00
  · have hb : M 0 1 = 0 := by
      have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right ht
    have hc : M 1 0 = 0 := by
      have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right ht
    rw [hb, hc] at e00 e11
    have ha : M 0 0 = 1 ∨ M 0 0 = -1 := by
      have : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination e00
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    have hd : M 1 1 = 1 ∨ M 1 1 = -1 := by
      have : (M 1 1 - 1) * (M 1 1 + 1) = 0 := by linear_combination e11
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    exfalso
    rcases ha with ha | ha <;> rcases hd with hd | hd
    · exact h1 (by ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd])
    · exact ht (by rw [ha, hd]; ring)
    · exact ht (by rw [ha, hd]; ring)
    · exact hm1 (by ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd])

/-- A complex conjugation is an involution. -/
theorem isComplexConj_mul_self {c : PkgI4.GQ} (hc : PkgI4.IsComplexConj c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  apply AlgEquiv.ext; intro x
  apply j.toRingHom.injective
  change j (c (c x)) = j x
  rw [hj, hj, Complex.conj_conj]

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem GaloisRep.mat_mul (r : GaloisRep ℓ 2) (g h : PkgI4.GQ) :
    r.mat (g * h) = r.mat g * r.mat h := by
  simp [PkgI4.GaloisRep.mat, map_mul, Units.val_mul]

theorem GaloisRep.mat_one (r : GaloisRep ℓ 2) : r.mat 1 = 1 := by
  simp [PkgI4.GaloisRep.mat]

/-- **Oddness from non-scalarity (proved).** If no complex conjugation acts by `±1`, then `r` is
odd. -/
theorem isOdd_of_not_pm_one (r : GaloisRep ℓ 2)
    (h : ∀ c, PkgI4.IsComplexConj c → r.mat c ≠ 1 ∧ r.mat c ≠ -1) : r.IsOdd := by
  intro c hc
  have h2 : r.mat c * r.mat c = 1 := by
    rw [← GaloisRep.mat_mul, isComplexConj_mul_self hc, GaloisRep.mat_one]
  exact det_eq_neg_one_of_sq_eq_one _ h2 (h c hc).1 (h c hc).2

/-- `v ↦ 1 ⊗ v` is injective for a field extension (flatness of vector spaces). -/
theorem one_tmul_injective (k E V : Type*) [Field k] [Field E] [Algebra k E] [AddCommGroup V]
    [Module k V] : Function.Injective (fun v : V => (1 : E) ⊗ₜ[k] v) := by
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := V)
    (Algebra.linearMap k E) (algebraMap k E).injective
  intro x y hxy
  apply (TensorProduct.lid k V).symm.injective
  apply hinj
  simpa using hxy

/-- Base change along a field extension is injective on linear maps. -/
theorem baseChange_injective' (k E V : Type*) [Field k] [Field E] [Algebra k E] [AddCommGroup V]
    [Module k V] {f g : V →ₗ[k] V} (h : f.baseChange E = g.baseChange E) : f = g := by
  ext v
  apply one_tmul_injective k E V
  have := LinearMap.congr_fun h ((1 : E) ⊗ₜ[k] v)
  simpa using this

/-! ## §3. The remaining glue, and `G10Glue` from it -/

/-- **G10 core: complex conjugation twists the Tate representation of `G_K` nontrivially (GLUE,
unproved; STANDARD).** For a number field `K` Galois over `ℚ`, an abelian surface `A/K`, a prime
`ℓ` and a complex conjugation `c ∈ G_ℚ`, it is not the case that `ρ_ℓ(τ) = ρ_ℓ(σ)` on `V_ℓ(A)`
whenever `τ, σ ∈ G_K` satisfy `τ = c σ c⁻¹` in `G_ℚ` (`resQ`).

Proof (STANDARD; N5 L742-751, h-trust C5): suppose it is. Let `ι : ℚ̄ → ℂ` realize `c`, `c̄ = c|_K`
(`K` normal), `A^c = A ⊗_{K,c̄} K`. The `c`-semilinear bijection `A(K̄) → A^c(K̄)` gives
`c_* : V_ℓ(A) → V_ℓ(A^c)` with `c_* ρ_A(σ) = ρ_{A^c}(cσc⁻¹) c_*`; by the assumption `c_*` is
`G_K`-equivariant, so by Faltings (`PkgI3.FaltingsTate`, R9b) `c_* ∈ Hom(A, A^c) ⊗ ℚ_ℓ`. By the
Artin comparison at `ι` (T12, through the uniformization T35 and T5), `c_* = F_* ⊗ 1` for the
antiholomorphic `F : A(ℂ) → A^c(ℂ)`, `F_* : H₁(A(ℂ),ℚ) → H₁(A^c(ℂ),ℚ)` `ℚ`-rational; since
`(W ⊗ ℚ_ℓ) ∩ Hom_ℚ(H, H') = W` for the `ℚ`-subspace `W = Hom(A, A^c) ⊗ ℚ`, `F_* ∈ W`, so `F_*` is
`ℂ`-linear by T11 (`F_* J = J' F_*`) and `ℂ`-antilinear (`F_* J = −J' F_*`), hence `F_* = 0`,
contradicting `F_*` bijective and `H ≠ 0` (`dim A = 2`). The case `c ∈ G_K` (`c̄ = id`,
`A^c = A`) is the same with `c_* = ρ_A(c)`. -/
def ConjTwistNontrivial : Prop :=
  PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime], A.dim = 2 → ∀ c : PkgI4.GQ, PkgI4.IsComplexConj c →
    ¬ ∀ σ τ : Field.absoluteGaloisGroup K, resQ K τ = c * resQ K σ * c⁻¹ →
      A.galRep ℓ τ = A.galRep ℓ σ

/-- If `r(c)` is central (here `±1`), the Tate action is unchanged by the `c`-twist. -/
theorem galRep_eq_of_central {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hI : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) (c : PkgI4.GQ)
    (hcen : ∀ X, r.mat c * X = X * r.mat c) (σ τ : Field.absoluteGaloisGroup K)
    (hτ : resQ K τ = c * resQ K σ * c⁻¹) : A.galRep ℓ τ = A.galRep ℓ σ := by
  have hm : r.mat (resQ K τ) = r.mat (resQ K σ) := by
    rw [hτ, GaloisRep.mat_mul, GaloisRep.mat_mul, hcen, _root_.mul_assoc, ← GaloisRep.mat_mul,
      _root_.mul_inv_cancel, GaloisRep.mat_one, _root_.mul_one]
  have ht : tate A ℓ τ = tate A ℓ σ := by
    apply LinearMap.ext; intro v
    apply e.injective
    rw [hI τ v, hI σ v]
    simp only [hm]
  exact baseChange_injective' ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) ht

/-- **The conclusion of `G10Glue` from `ConjTwistNontrivial` (proved),** without the opaque
hypotheses and without the rank, division and noncommutativity hypotheses. -/
theorem g10Out_of_conjTwist (h : ConjTwistNontrivial) (hF : PkgI3.FaltingsTate) (K : Type)
    [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hdim : A.dim = 2) (hI : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) :
    G10Out r := by
  apply isOdd_of_not_pm_one
  intro c hc
  have key := h hF K A ℓ hdim c hc
  constructor
  · intro h1
    exact key (galRep_eq_of_central A r e hI c (fun X => by rw [h1, _root_.one_mul, _root_.mul_one]))
  · intro h1
    exact key (galRep_eq_of_central A r e hI c (fun X => by rw [h1]; simp))

/-- **`G10Glue` from `ConjTwistNontrivial` (proved).** The opaque hypotheses `T11_RiemannGAGA`,
`T12_ArtinComparison` and the rank, division and noncommutativity hypotheses are not used. -/
theorem g10Glue_of_conjTwist (h : ConjTwistNontrivial) : G10Glue := by
  intro _ _ hF K _ _ _ A ℓ _ r e hdim _ _ _ hI
  exact g10Out_of_conjTwist h hF K A ℓ r e hdim hI

end G0Galois
end G10OddSec

section ConjTwistSec
namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj

open ZInQ.LeafPush2 in
/-- **G10 core from the leaves (GLUE, unproved; STANDARD).** `ConjTwistNontrivial` with T11(a),
T11(b), T35, T5 and T26 available: the leaves its proof (docstring of `ConjTwistNontrivial`, §6)
uses besides Faltings. The remaining work is glue: the conjugate variety `A^c`, the Artin
comparison `T_ℓ(A) ≅ Λ ⊗ ℤ_ℓ` at `ι` (from T35 and T5, as for `T12_ComplexConjEigen`) compatible
with `c_*` and `F_*`, and the instantiation of `betti_skeleton`. -/
def ConjTwistFromLeaves : Prop :=
  T11a_RiemannEnd → T11b_Rigidity → UniformizationExists → PkgI2.TorsionStructure.{0} →
  PkgI3.TateModuleFree → ConjTwistNontrivial

/-- Base change along a field extension is injective on linear maps `V → V'`. -/
theorem baseChange_injective₂ (k E V V' : Type*) [Field k] [Field E] [Algebra k E]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V'] {f g : V →ₗ[k] V'}
    (h : f.baseChange E = g.baseChange E) : f = g := by
  ext v
  apply one_tmul_injective k E V'
  have := LinearMap.congr_fun h ((1 : E) ⊗ₜ[k] v)
  simpa using this

/-- A map that is both linear and antilinear for complex structures (`J'` injective) is `0`. -/
theorem eq_zero_of_holo_of_antiholo {R M N : Type*} [Field R] [CharZero R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (J : M →ₗ[R] M) (J' : N →ₗ[R] N)
    (hJ' : Function.Injective J') (F : M →ₗ[R] N) (h1 : F ∘ₗ J = J' ∘ₗ F)
    (h2 : F ∘ₗ J = -(J' ∘ₗ F)) : F = 0 := by
  ext m
  have a := LinearMap.congr_fun h1 m
  have b := LinearMap.congr_fun h2 m
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.neg_apply] at a b
  have h3 : (2 : R) • J' (F m) = 0 := by
    rw [two_smul]
    have : J' (F m) = -J' (F m) := a.symm.trans b
    nth_rewrite 1 [this]; exact neg_add_cancel _
  have h4 : J' (F m) = J' 0 := by
    rw [map_zero]; exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  simpa using hJ' h4

/-- **Rationality for matrices (proved).** If `X.map (algebraMap k E)` lies in the `E`-span of
`W.map`, then `X ∈ W`. -/
theorem matrix_mem_of_map_mem_span {k E m n : Type*} [Field k] [Field E] [Algebra k E]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (W : Submodule k (Matrix m n k))
    (X : Matrix m n k)
    (h : X.map (algebraMap k E) ∈
      Submodule.span E ((fun Y : Matrix m n k => Y.map (algebraMap k E)) '' (W : Set _))) :
    X ∈ W := by
  by_contra hX
  obtain ⟨mu, hmuX, hmuW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hX inferInstance
  have hmuW' : ∀ Y ∈ W, mu Y = 0 := fun Y hY => by
    have : mu Y ∈ W.map mu := ⟨Y, hY, rfl⟩
    rwa [hmuW, Submodule.mem_bot] at this
  let muE : Matrix m n E →ₗ[E] E := ∑ i, ∑ j,
    algebraMap k E (mu (Matrix.single i j 1)) • Matrix.entryLinearMap E E i j
  have key : ∀ Y : Matrix m n k, muE (Y.map (algebraMap k E)) = algebraMap k E (mu Y) := by
    intro Y
    conv_rhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [muE, LinearMap.sum_apply, LinearMap.smul_apply,
      Matrix.entryLinearMap_apply, Matrix.map_apply, map_sum, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hs : Matrix.single i j (Y i j) = Y i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, _root_.mul_one]
    rw [hs, map_smul, smul_eq_mul, map_mul, mul_comm]
  have hle : Submodule.span E ((fun Y : Matrix m n k => Y.map (algebraMap k E)) '' (W : Set _)) ≤
      LinearMap.ker muE := by
    rw [Submodule.span_le]
    rintro _ ⟨Y, hY, rfl⟩
    simp [key, hmuW' Y hY]
  have h0 : muE (X.map (algebraMap k E)) = 0 := hle h
  rw [key] at h0
  exact hmuX ((algebraMap k E).injective (by rw [h0, map_zero]))

/-- **Rationality for linear maps (proved).** For finite-dimensional `H, H'`, if `F ⊗ 1` lies in
the `E`-span of `{φ ⊗ 1 : φ ∈ W}` inside `Hom_E(E ⊗ H, E ⊗ H')`, then `F ∈ W`. -/
theorem mem_of_baseChange_mem_span (k E : Type*) [Field k] [Field E] [Algebra k E]
    {H H' : Type*} [AddCommGroup H] [Module k H] [FiniteDimensional k H] [AddCommGroup H']
    [Module k H'] [FiniteDimensional k H'] (W : Submodule k (H →ₗ[k] H')) (F : H →ₗ[k] H')
    (hFal : F.baseChange E ∈
      Submodule.span E ((fun φ : H →ₗ[k] H' => φ.baseChange E) '' (W : Set (H →ₗ[k] H')))) :
    F ∈ W := by
  let b := Module.finBasis k H
  let b' := Module.finBasis k H'
  let T := LinearMap.toMatrix b b'
  let TE := LinearMap.toMatrix (Algebra.TensorProduct.basis E b) (Algebra.TensorProduct.basis E b')
  have hT : T F ∈ W.map T.toLinearMap := by
    apply matrix_mem_of_map_mem_span (E := E)
    have h1 := Submodule.mem_map_of_mem (f := TE.toLinearMap) hFal
    rw [Submodule.map_span, Set.image_image] at h1
    simp only [LinearEquiv.coe_coe, TE, LinearMap.toMatrix_baseChange] at h1
    rw [Submodule.map_coe, Set.image_image]
    exact h1
  obtain ⟨G, hG, hTG⟩ := hT
  rwa [T.injective hTG] at hG

/-- **The Betti skeleton, finite-dimensional form (proved).** As `betti_skeleton`, without the
canonical map: `H, H'` finite-dimensional, `F ⊗ 1` in the `E`-span of `{φ ⊗ 1 : φ ∈ W}`. -/
theorem betti_skeleton_fd (E : Type*) [Field E] [Algebra ℚ E] {H H' : Type*} [AddCommGroup H]
    [Module ℚ H] [FiniteDimensional ℚ H] [AddCommGroup H'] [Module ℚ H'] [FiniteDimensional ℚ H']
    (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H')
    (hJ' : Function.Injective J') (W : Submodule ℚ (H →ₗ[ℚ] H'))
    (hW : ∀ φ ∈ W, φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ)
    (F : H →ₗ[ℚ] H') (hF : F.baseChange ℝ ∘ₗ J = -(J' ∘ₗ F.baseChange ℝ))
    (hFal : F.baseChange E ∈
      Submodule.span E ((fun φ : H →ₗ[ℚ] H' => φ.baseChange E) '' (W : Set (H →ₗ[ℚ] H')))) :
    F = 0 := by
  have hFW : F ∈ W := mem_of_baseChange_mem_span ℚ E W F hFal
  have h0 : F.baseChange ℝ = 0 :=
    eq_zero_of_holo_of_antiholo J J' hJ' (F.baseChange ℝ) (hW F hFW) hF
  apply baseChange_injective₂ ℚ ℝ H H'
  rw [h0, LinearMap.baseChange_zero]

/-- The embedding `ℚ̄ → K̄` that `Field.absoluteGaloisGroup.map` chooses (`IsAlgClosed.lift`). -/
/-- `qEmbRing K : ℚ̄ → K̄` is bijective (`K̄` is algebraic over `ℚ`). -/
theorem qEmbRing_bijective (K : Type) [Field K] [NumberField K] :
    Function.Bijective (qEmbRing K) := by
  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)
  let g : AlgebraicClosure K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let h : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ := (g.toRingHom.comp (qEmbRing K)).toRatAlgHom
  have hb : Function.Bijective h := Algebra.IsAlgebraic.algHom_bijective h
  refine ⟨(qEmbRing K).injective, fun z => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (g z)
  exact ⟨x, g.toRingHom.injective hx⟩

/-- Elements of `ℚ̄` landing in `K` are fixed by `resQ K σ`. -/
theorem resQ_fix (K : Type) [Field K] [NumberField K] (σ : Field.absoluteGaloisGroup K)
    (u : AlgebraicClosure ℚ)
    (hu : qEmbRing K u ∈ (algebraMap K (AlgebraicClosure K)).range) : resQ K σ u = u := by
  obtain ⟨k, hk⟩ := hu
  apply (qEmbRing K).injective
  refine (resQ_spec K σ u).trans ?_
  rw [← hk]
  exact AlgEquiv.commutes (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) k

/-- For `K/ℚ` Galois, the elements of `ℚ̄` landing in `K` form a `G_ℚ`-stable set. -/
theorem range_stable (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (g : PkgI4.GQ)
    (u : AlgebraicClosure ℚ)
    (hu : qEmbRing K u ∈ (algebraMap K (AlgebraicClosure K)).range) :
    qEmbRing K (g u) ∈ (algebraMap K (AlgebraicClosure K)).range := by
  obtain ⟨k, hk⟩ := hu
  have hsplit : ((minpoly ℚ k).map (algebraMap ℚ K)).Splits :=
    Normal.splits (IsGalois.to_normal) k
  have hp0 : (minpoly ℚ k).map (algebraMap ℚ K) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral k))
  apply hsplit.mem_range_of_isRoot hp0
  rw [Polynomial.map_map, Polynomial.IsRoot, Polynomial.eval_map]
  have e1 : (algebraMap K (AlgebraicClosure K)).comp (algebraMap ℚ K) =
      (qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have e2 : (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
      (algebraMap ℚ (AlgebraicClosure ℚ)) = algebraMap ℚ (AlgebraicClosure ℚ) :=
    Subsingleton.elim _ _
  have hu0 : Polynomial.eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) u (minpoly ℚ k) = 0 := by
    apply (qEmbRing K).injective
    rw [Polynomial.hom_eval₂, ← e1, ← hk, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
      minpoly.aeval, map_zero, map_zero]
  rw [e1, ← Polynomial.hom_eval₂]
  have : Polynomial.eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) (g u) (minpoly ℚ k) = 0 := by
    have := Polynomial.hom_eval₂ (minpoly ℚ k) (algebraMap ℚ (AlgebraicClosure ℚ))
      (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) u
    rw [e2, hu0, map_zero] at this
    exact this.symm
  rw [this, map_zero]
/-! ## §2. Faltings in `ℚ_ℓ`-form (proved from `FaltingsTate` and `TateModuleFree`) -/

/-- The `ℚ_ℓ`-span of `{V_ℓ(f) : f ∈ Hom_K(A, B)}` inside `Hom_{ℚ_ℓ}(V_ℓ A, V_ℓ B)`. -/
def homSpanV {K : Type} [Field K] (A B : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Submodule ℚ_[ℓ] (A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ) :=
  Submodule.span ℚ_[ℓ] (Set.range fun f : PkgI3.AbVar.Hom A B =>
    (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ])

open PkgI3 PkgI3.AbVar in
/-- **Faltings, `ℚ_ℓ`-form (proved).** For abelian varieties `A, B` over a number field, every
`G_K`-equivariant `ℚ_ℓ`-linear map `V_ℓ(A) → V_ℓ(B)` lies in the `ℚ_ℓ`-span of
`{V_ℓ(f) : f ∈ Hom_K(A, B)}`. From `FaltingsTate` (Faltings 1983, Satz 4 / Kor. 1) and
`TateModuleFree` (T26): `T_ℓ A` is finitely presented, so `s • φ` maps `T_ℓ A` into `T_ℓ B` for
some `s ≠ 0`, and the lift is equivariant (the proof of `PkgI3.exists_hom_ne_zero_of_equivariant`). -/
theorem faltingsV (hF : FaltingsTate) (hT : TateModuleFree)
    {K : Type} [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ)
    (heq : ∀ σ, φ ∘ₗ A.galRep ℓ σ = B.galRep ℓ σ ∘ₗ φ) : φ ∈ homSpanV A B ℓ := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfinA, -⟩ := hT K A ℓ hℓK
  obtain ⟨hfreeB, -, -⟩ := hT K B ℓ hℓK
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  let ιA : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  let ιB : B.T ℓ →ₗ[ℤ_[ℓ]] B.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (B.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) ιB := inferInstance
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (nonZeroDivisors ℤ_[ℓ]) ιB ((φ.restrictScalars ℤ_[ℓ]) ∘ₗ ιA)
  have hs0 : (s : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hιB : Function.Injective ιB := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) ιB).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  have hιAσ : ∀ σ x, ιA (A.galT σ x) = A.galRep ℓ σ (ιA x) := fun σ x => by
    simp [ιA, galRep, LinearMap.baseChange_tmul]
  have hιBσ : ∀ σ x, ιB (B.galT σ x) = B.galRep ℓ σ (ιB x) := fun σ x => by
    simp [ιB, galRep, LinearMap.baseChange_tmul]
  have hsφ : ∀ x, ιB (h x) = (s : ℤ_[ℓ]) • φ (ιA x) := fun x => by
    have := congrArg (fun g => g x) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
    exact this
  have hheq : IsGalEquivariant h := by
    intro σ x
    apply hιB
    rw [hsφ, hιAσ, hιBσ, hsφ]
    have := congrArg (fun g => g (ιA x)) (heq σ)
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, LinearMap.map_smul_of_tower]
  obtain ⟨z, hz⟩ : h ∈ Set.range (tateHomZl ℓ A B) := by
    rw [(hF K A B ℓ).2]; exact hheq
  have hmem : ∀ z, (tateHomZl ℓ A B z).baseChange ℚ_[ℓ] ∈ homSpanV A B ℓ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      have e : tateHomZl ℓ A B (a ⊗ₜ f) = a • tateHom ℓ A B f := rfl
      rw [e, LinearMap.baseChange_smul]
      have : (a • (tateHom ℓ A B f).baseChange ℚ_[ℓ]) =
          (algebraMap ℤ_[ℓ] ℚ_[ℓ] a) • (tateHom ℓ A B f).baseChange ℚ_[ℓ] :=
        (algebraMap_smul ℚ_[ℓ] a _).symm
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
    | add y z hy hz =>
      rw [map_add, LinearMap.baseChange_add]; exact Submodule.add_mem _ hy hz
  have hc : algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]) ≠ 0 := by
    simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne hs0
  have hφ : φ = (algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]))⁻¹ • h.baseChange ℚ_[ℓ] := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    apply LinearMap.ext
    intro x
    change φ ((1 : ℚ_[ℓ]) ⊗ₜ x) =
      (algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]))⁻¹ • h.baseChange ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ x)
    rw [LinearMap.baseChange_tmul]
    have h1 : ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] h x : B.V ℓ) = (s : ℤ_[ℓ]) • φ ((1 : ℚ_[ℓ]) ⊗ₜ x) :=
      hsφ x
    rw [h1, ← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]), smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hφ, ← hz]
  exact Submodule.smul_mem _ _ (hmem z)

/-! ## §3. From `c ∈ G_ℚ` to an automorphism of `K̄` (proved) -/

/-- `σ ∈ G_K` as a `K`-automorphism of `K̄` (for application to elements). -/
abbrev gA {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- **Complex conjugation on `K̄` (proved).** For `K/ℚ` Galois and a complex conjugation
`c ∈ G_ℚ`, transport `c` along `qEmbRing K : ℚ̄ ≅ K̄` to `cc : K̄ ≅ K̄`. Then `cc` is complex
conjugation for the embedding `ι = j ∘ qEmbRing⁻¹` (`j` realizing `c`), maps `K` to itself (`K`
normal), is an involution, and `τ ∘ cc = cc ∘ σ` in `Aut(K̄)` implies
`resQ K τ = c · resQ K σ · c⁻¹` in `G_ℚ`. -/
theorem conjData (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (c : PkgI4.GQ)
    (hc : PkgI4.IsComplexConj c) :
    ∃ (cc : AlgebraicClosure K ≃+* AlgebraicClosure K) (emb : AlgebraicClosure K →+* ℂ),
      (∀ x, emb (cc x) = starRingEnd ℂ (emb x)) ∧
      (∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') ∧
      (∀ x, cc (cc x) = x) ∧
      (∀ σ τ : Field.absoluteGaloisGroup K, (∀ x, gA τ (cc x) = cc (gA σ x)) →
        resQ K τ = c * resQ K σ * c⁻¹) := by
  have c2 := isComplexConj_mul_self hc
  obtain ⟨j, hj⟩ := hc
  let Φ : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
    RingEquiv.ofBijective (qEmbRing K) (qEmbRing_bijective K)
  let cc : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    (Φ.symm.trans (c : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)).trans Φ
  have hcc : ∀ u, cc (Φ u) = Φ (c u) := fun u => by
    change Φ (c (Φ.symm (Φ u))) = _
    rw [Φ.symm_apply_apply]
  have hΦ : ∀ u, Φ u = qEmbRing K u := fun _ => rfl
  refine ⟨cc, j.toRingHom.comp Φ.symm.toRingHom, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨u, rfl⟩ := Φ.surjective x
    rw [hcc]
    change j (Φ.symm (Φ (c u))) = starRingEnd ℂ (j (Φ.symm (Φ u)))
    rw [Φ.symm_apply_apply, Φ.symm_apply_apply, hj]
  · intro k
    obtain ⟨u, hu⟩ := Φ.surjective (algebraMap K _ k)
    obtain ⟨k', hk'⟩ := range_stable K c u ⟨k, hu.symm⟩
    exact ⟨k', by rw [← hu, hcc]; exact hk'.symm⟩
  · intro x
    obtain ⟨u, rfl⟩ := Φ.surjective x
    rw [hcc, hcc]
    congr 1
    exact congrArg (fun g : PkgI4.GQ => g u) c2
  · intro σ τ hστ
    apply AlgEquiv.ext; intro u
    apply (qEmbRing K).injective
    have e1 : (c * resQ K σ * c⁻¹) u = c (resQ K σ (c⁻¹ u)) := rfl
    have a1 : qEmbRing K (resQ K τ u) = gA τ (Φ u) := resQ_spec K τ u
    have a2 : Φ (resQ K σ (c⁻¹ u)) = gA σ (Φ (c⁻¹ u)) := resQ_spec K σ _
    have a3 : Φ u = cc (Φ (c⁻¹ u)) := by
      rw [hcc]; congr 1; exact (AlgEquiv.apply_symm_apply c u).symm
    rw [a1, e1]
    change gA τ (Φ u) = Φ (c (resQ K σ (c⁻¹ u)))
    rw [← hcc, a2, ← hστ, ← a3]

/-- **Every `τ ∈ G_K` is a `cc`-twist (proved):** `σ = cc τ cc` fixes `K`. -/
theorem exists_twist (K : Type) [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k')
    (h2 : ∀ x, cc (cc x) = x) (τ : Field.absoluteGaloisGroup K) :
    ∃ σ : Field.absoluteGaloisGroup K, ∀ x, gA τ (cc x) = cc (gA σ x) := by
  let σr : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    (cc.trans ((gA τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : AlgebraicClosure K ≃+* AlgebraicClosure K)).trans cc
  have hfix : ∀ k : K, σr (algebraMap K _ k) = algebraMap K _ k := by
    intro k
    obtain ⟨k', hk'⟩ := hK k
    change cc (gA τ (cc (algebraMap K _ k))) = _
    rw [hk', AlgEquiv.commutes, ← hk', h2]
  refine ⟨AlgEquiv.ofRingEquiv (f := σr) hfix, fun x => ?_⟩
  change gA τ (cc x) = cc (cc (gA τ (cc x)))
  rw [h2]

/-! ## §4. The remaining glue and the reduction -/

/-- The `ℚ`-subspace of `Hom_ℚ(H, H')` of maps that are holomorphic for complex structures `J, J'`
on `H ⊗ ℝ`, `H' ⊗ ℝ`. -/
def holoSub {H H' : Type} [AddCommGroup H] [Module ℚ H] [AddCommGroup H'] [Module ℚ H']
    (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H') :
    Submodule ℚ (H →ₗ[ℚ] H') where
  carrier := {φ | φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ}
  add_mem' := by
    intro φ ψ hφ hψ
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.baseChange_add, LinearMap.add_comp, LinearMap.comp_add, hφ, hψ]
  zero_mem' := by simp
  smul_mem' := by
    intro q φ hφ
    simp only [Set.mem_setOf_eq] at *
    apply LinearMap.ext; intro x
    have := LinearMap.congr_fun hφ x
    simp only [LinearMap.coe_comp, Function.comp_apply] at this ⊢
    rw [LinearMap.baseChange_smul, LinearMap.smul_apply, LinearMap.smul_apply, this,
      LinearMap.map_smul_of_tower]

/-- **G10 core, geometric input (GLUE, unproved; STANDARD).** Conjugate variety plus Artin
comparison at a complex place, with holomorphy of homomorphisms. For a number field `K`, an
abelian surface `A/K`, a prime `ℓ`, a ring automorphism `cc` of `K̄` mapping `K` to itself and an
embedding `ι : K̄ → ℂ` with `ι ∘ cc = conj ∘ ι`, there are
* an abelian variety `B/K` and a `ℚ_ℓ`-linear `C : V_ℓ(A) → V_ℓ(B)` with the twisted equivariance
  `C ρ_A(σ) = ρ_B(τ) C` whenever `τ ∘ cc = cc ∘ σ`. Witness: `B = A^s = A ×_{K,s} K`, `s = cc|_K`,
  and `C = c_*`, the transport of `K̄`-points `P ↦ P ∘ Spec(cc)` (`A^s(K̄) = A(K̄ via s)`);
* finite-dimensional `ℚ`-spaces `H, H'` with `ℚ_ℓ ⊗ H ≅ V_ℓ(A)` (`α`), `ℚ_ℓ ⊗ H' ≅ V_ℓ(B)` (`β`),
  ℝ-linear `J, J'` on `ℝ ⊗ H, ℝ ⊗ H'` (`J'` injective) and a nonzero `ℚ`-linear `F : H → H'`.
  Witness: `H = H₁(A(ℂ)_ι, ℚ)`, `H' = H₁(B(ℂ)_ι, ℚ) = H₁(A(ℂ)_{conj ∘ ι}, ℚ)` (the lattices of
  the uniformizations T35, `ℝ ⊗ H = ℂ^g`), `J, J'` multiplication by `i`, `α, β` the Artin
  comparison through `ι` (`A(K̄)[ℓⁿ] ≅ A(ℂ)[ℓⁿ] = ℓ⁻ⁿΛ/Λ`, bijective by T5), `F = F_*` the map
  of complex conjugation `A(ℂ)_ι → A(ℂ)_{conj ∘ ι}` on `H₁` (bijective, `H ≠ 0` as `dim A = 2`);
such that `F` is antiholomorphic (`F J = −J' F`), `C` corresponds to `F ⊗ 1` (`ι ∘ cc = conj ∘ ι`),
and each `f ∈ Hom_K(A, B)` corresponds to `φ ⊗ 1` for a holomorphic `φ : H → H'` (`φ = H₁(f)`,
holomorphic as `f` is a morphism of varieties: T11(a) in Hom form, Mumford §1, Birkenhake–Lange
1.2.1; UNVERIFIED numbers). Sources: SGA 4 XI 4.4 (Artin comparison), Mumford §1, §4 (T35, T5);
N5 L742-751, h-trust C5. -/
def ConjBettiData : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (cc : AlgebraicClosure K ≃+* AlgebraicClosure K) (emb : AlgebraicClosure K →+* ℂ),
    A.dim = 2 → (∀ x, emb (cc x) = starRingEnd ℂ (emb x)) →
    (∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') →
    ∃ (B : PkgI3.AbVar K) (C : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ),
      (∀ σ τ : Field.absoluteGaloisGroup K, (∀ x, gA τ (cc x) = cc (gA σ x)) →
          C ∘ₗ A.galRep ℓ σ = B.galRep ℓ τ ∘ₗ C) ∧
      ∃ (H H' : Type) (_ : AddCommGroup H) (_ : Module ℚ H) (_ : FiniteDimensional ℚ H)
        (_ : AddCommGroup H') (_ : Module ℚ H') (_ : FiniteDimensional ℚ H')
        (α : ℚ_[ℓ] ⊗[ℚ] H ≃ₗ[ℚ_[ℓ]] A.V ℓ) (β : ℚ_[ℓ] ⊗[ℚ] H' ≃ₗ[ℚ_[ℓ]] B.V ℓ)
        (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H') (F : H →ₗ[ℚ] H'),
        Function.Injective J' ∧ F ≠ 0 ∧
        F.baseChange ℝ ∘ₗ J = -(J' ∘ₗ F.baseChange ℝ) ∧
        β.symm.toLinearMap ∘ₗ C ∘ₗ α.toLinearMap = F.baseChange ℚ_[ℓ] ∧
        ∀ f : PkgI3.AbVar.Hom A B, ∃ φ : H →ₗ[ℚ] H',
          φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ ∧
          β.symm.toLinearMap ∘ₗ (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] ∘ₗ
            α.toLinearMap = φ.baseChange ℚ_[ℓ]

/-- **`ConjTwistNontrivial` from T26 and `ConjBettiData` (proved).** If `ρ_A(τ) = ρ_A(σ)` whenever
`resQ τ = c resQ σ c⁻¹`, the twisted-equivariant `C` is `G_K`-equivariant, so lies in the span of
`Hom(A, B)` (`faltingsV`); on the Betti side `F ⊗ 1` lies in the span of holomorphic `φ ⊗ 1`, so
`F = 0` (`betti_skeleton_fd`), a contradiction. -/
theorem conjTwistNontrivial_of_conjBettiData (hT : PkgI3.TateModuleFree)
    (hB : ConjBettiData) : ConjTwistNontrivial := by
  intro hF K _ _ _ A ℓ _ hdim c hc hall
  obtain ⟨cc, emb, hι, hK, h2, hres⟩ := conjData K c hc
  obtain ⟨B, C, htw, H, H', _, _, _, _, _, _, α, β, J, J', F, hJ', hF0, hanti, hCF, hhol⟩ :=
    hB K A ℓ cc emb hdim hι hK
  have heq : ∀ τ, C ∘ₗ A.galRep ℓ τ = B.galRep ℓ τ ∘ₗ C := by
    intro τ
    obtain ⟨σ, hσ⟩ := exists_twist K cc hK h2 τ
    rw [hall σ τ (hres σ τ hσ), htw σ τ hσ]
  have hCmem := faltingsV hF hT A B ℓ C heq
  let Tr : (A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ) ≃ₗ[ℚ_[ℓ]] (ℚ_[ℓ] ⊗[ℚ] H →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] H') :=
    LinearEquiv.arrowCongr α.symm β.symm
  have hTr : ∀ M, Tr M = β.symm.toLinearMap ∘ₗ M ∘ₗ α.toLinearMap := fun M => by
    apply LinearMap.ext; intro x
    simp [Tr, LinearEquiv.arrowCongr_apply]
  have hle : homSpanV A B ℓ ≤ (Submodule.span ℚ_[ℓ]
      ((fun φ : H →ₗ[ℚ] H' => φ.baseChange ℚ_[ℓ]) ''
        (holoSub J J' : Set (H →ₗ[ℚ] H')))).comap Tr.toLinearMap := by
    rw [homSpanV, Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    obtain ⟨φ, hφJ, hφ⟩ := hhol f
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, hTr]
    rw [hφ]
    exact Submodule.subset_span ⟨φ, hφJ, rfl⟩
  have hFmem := hle hCmem
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, hTr, hCF] at hFmem
  exact hF0 (betti_skeleton_fd ℚ_[ℓ] J J' hJ' (holoSub J J') (fun φ hφ => hφ) F hanti hFmem)

/-- **`ConjTwistFromLeaves` from `ConjBettiData` (proved).** T26 is among its hypotheses. -/
theorem conjTwistFromLeaves_of_conjBettiData (hB : ConjBettiData) : ConjTwistFromLeaves :=
  fun _ _ _ _ hT => conjTwistNontrivial_of_conjBettiData hT hB

/-! ## §5. The conjugate variety and the transport `c_*` (proved), and the Betti glue

`conjVar A s = A ×_{Spec K, Spec s} Spec K` for a ring endomorphism `s` of `K` (Mathlib's
`Over.pullback`, as `PkgI3.AbVar.baseChange`), and for an automorphism `cc` of `K̄` extending `s`,
the transport of points `A(K̄) → A^s(K̄)`, `P ↦ P ∘ Spec(cc)` read through the adjunction
`Over.map ⊣ Over.pullback` (the recipe of scratch/unram-tate/BCPoints.lean). It carries the
action of `σ` to that of `τ` whenever `τ ∘ cc = cc ∘ σ`. -/

open PkgI3 in
/-- `Spec(s) : Spec K → Spec K`. -/
abbrev specS {K : Type} [Field K] (s : K →+* K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom s)

/-- **The conjugate abelian variety** `A^s = A ×_{Spec K, Spec s} Spec K` (pullback along
`Spec(s)`; group structure transported by the monoidal functor `Over.pullback`). -/
def conjVar {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K) : PkgI3.AbVar K :=
  let f := specS s
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

section Transport

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K)
  (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
  (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k))

/-- The adjunction bijection for `Over.map (Spec s) ⊣ Over.pullback (Spec s)` is
multiplicative. -/
theorem homEquiv_mul_conj (X : Over (Spec (CommRingCat.of K)))
    (p q : (Over.map (specS s)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (specS s)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (specS s)).homEquiv X A.X p *
        (Over.mapPullbackAdj (specS s)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- `Spec(cc)`, as a morphism over `K` from `Spec K̄` (structure map `Spec(s) ∘ Spec(alg)`) to
`Spec K̄`. -/
def ccHom : (Over.map (specS s)).obj (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)) ⟶
    PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K))) (by
    simp only [Over.map_obj_hom, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact hs x)

/-- **The transport `c_*` on `K̄`-points (proved):** `A(K̄) → A^s(K̄)`, a group homomorphism. -/
def conjPt : A.Pt (AlgebraicClosure K) →* (conjVar A s).Pt (AlgebraicClosure K) :=
  MonoidHom.mk' (fun P => (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ P))
    (fun P Q => by
      change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ (P * Q)) = _
      rw [MonObj.comp_mul, homEquiv_mul_conj]
      rfl)

/-- **Twisted equivariance of `c_*` on points (proved):** if `τ ∘ cc = cc ∘ σ` then
`c_*(σ P) = τ c_*(P)`. -/
theorem conjPt_galAct (σ τ : Field.absoluteGaloisGroup K)
    (h : ∀ x, gA τ (cc x) = cc (gA σ x)) (P : A.Pt (AlgebraicClosure K)) :
    conjPt A s cc hs (A.galAct (gA σ) P) = (conjVar A s).galAct (gA τ) (conjPt A s cc hs P) := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ PkgI3.AbVar.galHom (gA σ) ≫ P) =
    PkgI3.AbVar.galHom (gA τ) ≫ (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ P)
  have hsq : ccHom s cc hs ≫ PkgI3.AbVar.galHom (gA σ) =
      (Over.map (specS s)).map (PkgI3.AbVar.galHom (gA τ)) ≫ ccHom s cc hs := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
        Spec.map (CommRingCat.ofHom ((gA σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →+* AlgebraicClosure K)) =
      Spec.map (CommRingCat.ofHom ((gA τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →+* AlgebraicClosure K)) ≫
        Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, hsq, Category.assoc, Adjunction.homEquiv_naturality_left]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`c_*` on Tate modules (proved):** `T_ℓ(A) → T_ℓ(A^s)`. -/
def conjT : A.T ℓ →ₗ[ℤ_[ℓ]] (conjVar A s).T ℓ :=
  PkgI3.Tate.map (MonoidHom.toAdditive (conjPt A s cc hs))

/-- **`c_*` on `V_ℓ` (proved):** `V_ℓ(A) → V_ℓ(A^s)`. -/
def conjV : A.V ℓ →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ :=
  (conjT A s cc hs ℓ).baseChange ℚ_[ℓ]

theorem conjT_galT (σ τ : Field.absoluteGaloisGroup K) (h : ∀ x, gA τ (cc x) = cc (gA σ x)) :
    conjT A s cc hs ℓ ∘ₗ A.galT σ = (conjVar A s).galT τ ∘ₗ conjT A s cc hs ℓ := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  exact congrArg Additive.ofMul (conjPt_galAct A s cc hs σ τ h (Additive.toMul (x.1 n)))

/-- **Twisted equivariance of `c_*` on `V_ℓ` (proved):** `c_* ρ_A(σ) = ρ_{A^s}(τ) c_*` whenever
`τ ∘ cc = cc ∘ σ`. -/
theorem conjV_galRep (σ τ : Field.absoluteGaloisGroup K)
    (h : ∀ x, gA τ (cc x) = cc (gA σ x)) :
    conjV A s cc hs ℓ ∘ₗ A.galRep ℓ σ = (conjVar A s).galRep ℓ τ ∘ₗ conjV A s cc hs ℓ := by
  change (conjT A s cc hs ℓ).baseChange ℚ_[ℓ] ∘ₗ (A.galT σ).baseChange ℚ_[ℓ] =
    ((conjVar A s).galT τ).baseChange ℚ_[ℓ] ∘ₗ (conjT A s cc hs ℓ).baseChange ℚ_[ℓ]
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, conjT_galT A s cc hs ℓ σ τ h]

end Transport

/-- The function `cc|_K : K → K` for an automorphism `cc` of `K̄` mapping `K` into itself. -/
def sFun {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') (k : K) : K :=
  Classical.choose (hK k)

theorem sFun_spec {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') (k : K) :
    algebraMap K (AlgebraicClosure K) (sFun cc hK k) = cc (algebraMap K _ k) :=
  (Classical.choose_spec (hK k)).symm

/-- The ring endomorphism `s = cc|_K` of `K`. -/
def restrictK {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') : K →+* K where
  toFun := sFun cc hK
  map_one' := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [sFun_spec]; simp)
  map_mul' a b := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [map_mul, sFun_spec, sFun_spec, sFun_spec, map_mul, map_mul])
  map_zero' := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [sFun_spec]; simp)
  map_add' a b := (algebraMap K (AlgebraicClosure K)).injective (by
    rw [map_add, sFun_spec, sFun_spec, sFun_spec, map_add, map_add])

theorem restrictK_spec {K : Type} [Field K] (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hK : ∀ k : K, ∃ k' : K, cc (algebraMap K _ k) = algebraMap K _ k') (k : K) :
    cc (algebraMap K _ k) = algebraMap K _ (restrictK cc hK k) :=
  (sFun_spec cc hK k).symm

/-- **G10 core, Betti input for the concrete `c_*` (GLUE, unproved; STANDARD).** For a number
field `K`, an abelian surface `A/K`, a prime `ℓ`, a ring endomorphism `s` of `K`, an automorphism
`cc` of `K̄` extending `s` and an embedding `ι : K̄ → ℂ` with `ι ∘ cc = conj ∘ ι`: there are
finite-dimensional `ℚ`-spaces `H, H'`, `ℚ_ℓ`-isomorphisms `α : ℚ_ℓ ⊗ H ≅ V_ℓ(A)`,
`β : ℚ_ℓ ⊗ H' ≅ V_ℓ(A^s)`, ℝ-linear `J, J'` on `ℝ ⊗ H, ℝ ⊗ H'` (`J'` injective) and a nonzero
`F : H → H'`, such that `F J = −J' F`, `β⁻¹ c_* α = F ⊗ 1` for the transport
`c_* = conjV A s cc hs ℓ` (§5), and every `f ∈ Hom_K(A, A^s)` acts as `φ ⊗ 1` with `φ J = J' φ`.
Witness (STANDARD): `H = H₁(A(ℂ)_ι, ℚ)`, `H' = H₁(A^s(ℂ)_ι, ℚ) = H₁(A(ℂ)_{conj∘ι}, ℚ)` (lattices
of the uniformizations T35, `ℝ ⊗ H = ℂ^g`), `J, J'` multiplication by `i`, `α, β` Artin's
comparison through `ι` (`A(K̄)[ℓⁿ] → A(ℂ)[ℓⁿ] = ℓ⁻ⁿΛ/Λ` bijective, by T5 over `K̄` and over `ℂ`;
SGA 4 XI 4.4), `F = F_*` for complex conjugation `A(ℂ)_ι → A(ℂ)_{conj∘ι}`, `P ↦ P ∘ Spec(conj)`,
antiholomorphic and bijective, `H ≠ 0` as `dim A = 2`; `β⁻¹ c_* α = F ⊗ 1` because
`P ∘ Spec(cc) ∘ Spec(ι) = P ∘ Spec(ι) ∘ Spec(conj)`; `φ = H₁(f)`, holomorphic because `f` is a
morphism of varieties (T11(a) in Hom form: Mumford §1, Birkenhake–Lange 1.2.1, UNVERIFIED
numbers). N5 L742-751, h-trust C5. -/
def ConjBettiComparison : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (s : K →+* K) (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k)) (emb : AlgebraicClosure K →+* ℂ),
    A.dim = 2 → (∀ x, emb (cc x) = starRingEnd ℂ (emb x)) →
      ∃ (H H' : Type) (_ : AddCommGroup H) (_ : Module ℚ H) (_ : FiniteDimensional ℚ H)
        (_ : AddCommGroup H') (_ : Module ℚ H') (_ : FiniteDimensional ℚ H')
        (α : ℚ_[ℓ] ⊗[ℚ] H ≃ₗ[ℚ_[ℓ]] A.V ℓ) (β : ℚ_[ℓ] ⊗[ℚ] H' ≃ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ)
        (J : ℝ ⊗[ℚ] H →ₗ[ℝ] ℝ ⊗[ℚ] H) (J' : ℝ ⊗[ℚ] H' →ₗ[ℝ] ℝ ⊗[ℚ] H') (F : H →ₗ[ℚ] H'),
        Function.Injective J' ∧ F ≠ 0 ∧
        F.baseChange ℝ ∘ₗ J = -(J' ∘ₗ F.baseChange ℝ) ∧
        β.symm.toLinearMap ∘ₗ conjV A s cc hs ℓ ∘ₗ α.toLinearMap = F.baseChange ℚ_[ℓ] ∧
        ∀ f : PkgI3.AbVar.Hom A (conjVar A s), ∃ φ : H →ₗ[ℚ] H',
          φ.baseChange ℝ ∘ₗ J = J' ∘ₗ φ.baseChange ℝ ∧
          β.symm.toLinearMap ∘ₗ (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] ∘ₗ
            α.toLinearMap = φ.baseChange ℚ_[ℓ]

/-- **`ConjBettiData` from `ConjBettiComparison` (proved):** `B = conjVar A s` with
`s = cc|_K`, `C = conjV`, twisted equivariance by `conjV_galRep`. -/
theorem conjBettiData_of_comparison (h : ConjBettiComparison) : ConjBettiData := by
  intro K _ _ A ℓ _ cc emb hdim hι hK
  obtain ⟨H, H', i1, i2, i3, i4, i5, i6, α, β, J, J', F, hrest⟩ :=
    h K A ℓ (restrictK cc hK) cc (restrictK_spec cc hK) emb hdim hι
  exact ⟨conjVar A (restrictK cc hK), conjV A (restrictK cc hK) cc (restrictK_spec cc hK) ℓ,
    fun σ τ hστ => conjV_galRep A _ cc _ ℓ σ τ hστ,
    H, H', i1, i2, i3, i4, i5, i6, α, β, J, J', F, hrest⟩

/-- **`ConjTwistNontrivial` from T26 and `ConjBettiComparison` (proved).** -/
theorem conjTwistNontrivial_of_comparison (hT : PkgI3.TateModuleFree)
    (h : ConjBettiComparison) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_conjBettiData hT (conjBettiData_of_comparison h)

/-- **`ConjTwistFromLeaves` from `ConjBettiComparison` (proved).** -/
theorem conjTwistFromLeaves_of_comparison (h : ConjBettiComparison) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_conjBettiData (conjBettiData_of_comparison h)

/-! ## §6. The next split of `ConjBettiComparison` (statements compile; the assembly is not
formalized)

`ConjBettiComparison` follows (STANDARD argument, docs/research/conj-twist.md §3) from T35
(`UniformizationExists`, applied to `A` and `A^s` at `σ = ι ∘ alg`) and the five Props below.
`toC` is the comparison of `K̄`-points with complex points through `ι : K̄ → ℂ`. -/

open ZInQ.LeafPush2 (CPts cptObj IsUniformization)

/-- `Spec(ι) : Spec ℂ → Spec K̄` over `K`. -/
def embHom {K : Type} [Field K] (emb : AlgebraicClosure K →+* ℂ) :
    cptObj (emb.comp (algebraMap K (AlgebraicClosure K))) ⟶
      PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom emb)) (by
    simp only [cptObj, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- **Comparison of points through `ι` (proved to be a homomorphism):** `A(K̄) → A(ℂ)_{ι∘alg}`,
`P ↦ P ∘ Spec(ι)`. -/
def toC {K : Type} [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) :
    A.Pt (AlgebraicClosure K) →* CPts A (emb.comp (algebraMap K (AlgebraicClosure K))) where
  toFun P := embHom emb ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- **`toC` is injective (proved).** -/
theorem toC_injective {K : Type} [Field K] (A : PkgI3.AbVar K)
    (emb : AlgebraicClosure K →+* ℂ) : Function.Injective (toC A emb) := by
  intro P P' h
  apply Over.OverMorphism.ext
  have hU : Spec.map (CommRingCat.ofHom emb) ≫ P.left =
      Spec.map (CommRingCat.ofHom emb) ≫ P'.left := by
    have := congrArg CommaMorphism.left h
    exact this
  haveI : IsReduced (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).left := by
    change IsReduced (Spec (CommRingCat.of (AlgebraicClosure K))); infer_instance
  have h0 : Surjective (Spec.map (CommRingCat.ofHom emb)) :=
    ⟨fun y => ⟨IsLocalRing.closedPoint ℂ, Subsingleton.elim _ _⟩⟩
  let ι' : Spec (CommRingCat.of ℂ) ⟶ (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).left :=
    Spec.map (CommRingCat.ofHom emb)
  haveI : Surjective ι' := h0
  exact ext_of_isDominant_of_isSeparated A.X.hom (by rw [Over.w P, Over.w P']) ι' hU

/-- **N1. Torsion comparison (GLUE, unproved; STANDARD).** `toC` is injective (`Spec ℂ → Spec K̄`
is faithfully flat, hence an epimorphism of schemes) and every `n`-torsion complex point
(`n ≥ 1`) comes from `A(K̄)`: `A(K̄)[n]` and `A(ℂ)[n]` both have `n^{2g}` elements (T5 over `K̄`
and over `ℂ`) and `toC` is injective. Equivalently, `A[n]` is finite étale in characteristic `0`
(Mumford §4, §6; UNVERIFIED numbers). -/
def ArtinTorsion : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (n : ℕ), 0 < n →
    Function.Injective (toC A emb) ∧
      ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))), Q ^ n = 1 →
        ∃ P, toC A emb P = Q

/-- **N4. Tate module of a uniformized abelian variety (GLUE, unproved; STANDARD).** For a
uniformization `Φ : ℂ^g → A(ℂ)_{ι∘alg}` with lattice `Λ` (T35), there is a `ℤ_ℓ`-isomorphism
`α : ℤ_ℓ ⊗ Λ ≅ T_ℓ(A)` with `toC (α(1 ⊗ λ))ₙ = Φ(ℓ⁻ⁿ λ)` for `λ ∈ Λ`. (The sequence
`Φ(ℓ⁻ⁿλ)` is compatible and `Φ(λ) = 1`; it comes from `A(K̄)` by N1; bijectivity is
`T_ℓ = lim Λ/ℓⁿΛ = Λ ⊗ ℤ_ℓ`, `Λ ≅ ℤ^{2g}`. Mumford §1, §4; this is Artin's comparison for
abelian varieties, SGA 4 XI 4.4; UNVERIFIED numbers.) The formula pins `α` and makes it natural
for homomorphisms and for `c_*` (by injectivity of `toC`). -/
def TateLattice : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))),
    A.dim = (g : WithBot ℕ∞) → ∀ [DiscreteTopology Λ], IsZLattice ℝ Λ →
    IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ α : TensorProduct ℤ ℤ_[ℓ] Λ ≃ₗ[ℤ_[ℓ]] A.T ℓ,
      ∀ (lam : Λ) (n : ℕ), toC A emb (Additive.toMul ((α (1 ⊗ₜ lam)).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ))

/-- **N2. T11(a) in Hom form (textbook LEAF; Birkenhake–Lange, *Complex abelian varieties*,
Prop. 1.2.1, with holomorphy of algebraic morphisms; Mumford §1; UNVERIFIED numbers).** For
abelian varieties `A, B` over `K`, `σ : K → ℂ` and uniformizations `Φ_A, Φ_B` of `A(ℂ)_σ`,
`B(ℂ)_σ`, every homomorphism `f : A → B` lifts to a `ℂ`-linear map `M` with
`Φ_B(Mz) = f(Φ_A(z))`. (`T11a_RiemannEnd`'s second half is the case `A = B` over `ℂ`.) -/
def HomLinearLift : Prop :=
  ∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom

/-- `Spec(conj) : Spec ℂ → Spec ℂ`, over `K` from `σ ∘ s` to `σ`, when `σ ∘ s = conj ∘ σ`. -/
def conjHom {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : cptObj (σ.comp s) ⟶ cptObj σ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) (by
    simp only [cptObj, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

/-- Complex conjugation `A(ℂ)_σ → A(ℂ)_{σ∘s}` when `σ ∘ s = conj ∘ σ`: `Q ↦ Q ∘ Spec(conj)`. -/
def conjCs {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) : CPts A (σ.comp s) :=
  conjHom σ s h ≫ Q

/-- `(Over.map Spec(s)).obj (Spec ℂ via σ) ⟶ Spec ℂ via σ ∘ s` (the identity of `Spec ℂ`). -/
def mapPtIso {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K) :
    (Over.map (specS s)).obj (cptObj σ) ⟶ cptObj (σ.comp s) :=
  Over.homMk (𝟙 _) (by
    simp only [Over.map_obj_hom, cptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- The map `A(ℂ)_σ → A^s(ℂ)_σ`, `Q ↦ Q ∘ Spec(conj)` read through `A^s(ℂ)_σ = A(ℂ)_{σ∘s}`
(adjunction `Over.map ⊣ Over.pullback`). -/
def twistC {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (Q : CPts A σ) : CPts (conjVar A s) σ :=
  (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjCs A σ s h Q)

/-- **N3. Complex conjugation is antiholomorphic (GLUE, unproved; STANDARD).** If
`σ ∘ s = conj ∘ σ`, then for uniformizations `Φ` of `A(ℂ)_σ` and `Φ'` of `A^s(ℂ)_σ` the map
`twistC` lifts to an injective `ℝ`-linear, `ℂ`-antilinear `N` (`N(iz) = −iN(z)`) with
`Φ'(Nz) = twistC(Φ z)`. (`z ↦ twistC(Φ(z̄))` is a holomorphic uniformization of
`A^s(ℂ)_σ = A(ℂ)_{conj∘σ}`; two uniformizations differ by a `ℂ`-linear isomorphism, BL 1.2.1.) -/
def ConjAntiLift : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) (Φ' : (Fin g → ℂ) → CPts (conjVar A s) σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ → IsUniformization σ Λ' Φ' →
    ∃ N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ z, N (Complex.I • z) = -(Complex.I • N z)) ∧
      Function.Injective N ∧ ∀ z, Φ' (N z) = twistC A σ s h (Φ z)

/-- **N5. Dimension of the conjugate (GLUE, unproved; STANDARD).** For a number field `K`, every
ring endomorphism `s` is an automorphism, so `Spec(s)` is an isomorphism and so is
`A^s → A`; Krull dimension is preserved. -/
def ConjVarDim : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (s : K →+* K),
    (conjVar A s).dim = A.dim

/-- **`toC` intertwines `c_*` with `twistC` (proved):** `toC (c_* P) = twistC (toC P)` for
`σ = ι ∘ alg`, `ι ∘ cc = conj ∘ ι`. This is the identity `Spec(ι) ≫ Spec(cc) = Spec(conj) ≫ Spec(ι)`
read through the adjunction; it is the "`β⁻¹ c_* α = F ⊗ 1`" part of `ConjBettiComparison` at
the level of points. -/
theorem toC_conjPt {K : Type} [Field K] (A : PkgI3.AbVar K) (s : K →+* K)
    (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k)) (emb : AlgebraicClosure K →+* ℂ)
    (hι : ∀ x, emb (cc x) = starRingEnd ℂ (emb x))
    (h : (emb.comp (algebraMap K _)).comp s = (starRingEnd ℂ).comp (emb.comp (algebraMap K _)))
    (P : A.Pt (AlgebraicClosure K)) :
    toC (conjVar A s) emb (conjPt A s cc hs P) =
      twistC A (emb.comp (algebraMap K _)) s h (toC A emb P) := by
  change embHom emb ≫ (Over.mapPullbackAdj (specS s)).homEquiv _ _ (ccHom s cc hs ≫ P) =
    (Over.mapPullbackAdj (specS s)).homEquiv _ _
      (mapPtIso _ s ≫ conjCs A _ s h (embHom emb ≫ P))
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  simp only [conjCs, ← Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom emb) ≫
      Spec.map (CommRingCat.ofHom (cc : AlgebraicClosure K →+* AlgebraicClosure K)) =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom emb)
  rw [Category.id_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact hι x

/-! ## §7. Naturality of the comparison of N4 (proved; uses `toC_injective`)

With N1, the formula of N4 pins `α`, and `α` is natural: for a homomorphism `f` with linear lift
`M` (N2), `T_ℓ(f) ∘ α_A = α_B ∘ (M ⊗ 1)` on `1 ⊗ Λ_A`; for `c_*` with antilinear lift `N` (N3),
`c_* ∘ α_A = α_{A^s} ∘ (N ⊗ 1)` on `1 ⊗ Λ_A`. These are the two compatibilities
`β⁻¹ V(f) α = φ ⊗ 1` and `β⁻¹ c_* α = F ⊗ 1` of `ConjBettiComparison`, before tensoring with `ℚ`
and `ℚ_ℓ`. -/

/-- The lattice point `λ` lies in the kernel of `Φ`, and a linear lift maps lattices to lattices:
`Φ_B(Mλ) = f(Φ_A(λ)) = f(1) = 1`. -/
theorem lift_mem_lattice {K : Type} [Field K] {A B : PkgI3.AbVar K} {σ : K →+* ℂ} {g h : ℕ}
    {ΛA : Submodule ℤ (Fin g → ℂ)} {ΛB : Submodule ℤ (Fin h → ℂ)}
    {ΦA : (Fin g → ℂ) → CPts A σ} {ΦB : (Fin h → ℂ) → CPts B σ}
    (hA : IsUniformization σ ΛA ΦA) (hB : IsUniformization σ ΛB ΦB) (f : PkgI3.AbVar.Hom A B)
    (M : (Fin g → ℂ) → (Fin h → ℂ)) (hM : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (lam : ΛA) :
    M lam ∈ ΛB := by
  rw [← hB.2.1, hM, (hA.2.1 _).mpr lam.2]
  exact MonObj.one_comp f.hom

/-- **Naturality for homomorphisms (proved).** -/
theorem homT_tateLattice {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (emb : AlgebraicClosure K →+* ℂ) {g h : ℕ} {ΛA : Submodule ℤ (Fin g → ℂ)}
    {ΛB : Submodule ℤ (Fin h → ℂ)}
    {ΦA : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))}
    {ΦB : (Fin h → ℂ) → CPts B (emb.comp (algebraMap K (AlgebraicClosure K)))}
    (ℓ : ℕ) [Fact ℓ.Prime]
    (αA : TensorProduct ℤ ℤ_[ℓ] ΛA →ₗ[ℤ_[ℓ]] A.T ℓ)
    (hαA : ∀ (lam : ΛA) (n : ℕ), toC A emb (Additive.toMul ((αA (1 ⊗ₜ lam)).1 n)) =
        ΦA (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)))
    (αB : TensorProduct ℤ ℤ_[ℓ] ΛB →ₗ[ℤ_[ℓ]] B.T ℓ)
    (hαB : ∀ (lam : ΛB) (n : ℕ), toC B emb (Additive.toMul ((αB (1 ⊗ₜ lam)).1 n)) =
        ΦB (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin h → ℂ)))
    (f : PkgI3.AbVar.Hom A B) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))
    (hM : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (lam : ΛA) (hlam : M lam ∈ ΛB) :
    PkgI3.AbVar.homT f (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ ⟨M lam, hlam⟩) := by
  apply Subtype.ext; funext n
  apply Additive.toMul.injective
  apply toC_injective B emb
  change toC B emb (Additive.toMul ((αA (1 ⊗ₜ lam)).1 n) ≫ f.hom) = _
  rw [hαB]
  change embHom emb ≫ Additive.toMul ((αA (1 ⊗ₜ lam)).1 n) ≫ f.hom = _
  rw [← Category.assoc]
  change toC A emb (Additive.toMul ((αA (1 ⊗ₜ lam)).1 n)) ≫ f.hom = _
  rw [hαA, ← hM, map_smul]

/-- **Naturality for `c_*` (proved, from `toC_conjPt`).** -/
theorem conjT_tateLattice {K : Type} [Field K] (A : PkgI3.AbVar K)
    (s : K →+* K) (cc : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k)) (emb : AlgebraicClosure K →+* ℂ)
    (hι : ∀ x, emb (cc x) = starRingEnd ℂ (emb x))
    (h : (emb.comp (algebraMap K _)).comp s = (starRingEnd ℂ).comp (emb.comp (algebraMap K _)))
    {g : ℕ} {Λ Λ' : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))}
    {Φ' : (Fin g → ℂ) → CPts (conjVar A s) (emb.comp (algebraMap K (AlgebraicClosure K)))}
    (ℓ : ℕ) [Fact ℓ.Prime]
    (α : TensorProduct ℤ ℤ_[ℓ] Λ →ₗ[ℤ_[ℓ]] A.T ℓ)
    (hα : ∀ (lam : Λ) (n : ℕ), toC A emb (Additive.toMul ((α (1 ⊗ₜ lam)).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)))
    (α' : TensorProduct ℤ ℤ_[ℓ] Λ' →ₗ[ℤ_[ℓ]] (conjVar A s).T ℓ)
    (hα' : ∀ (lam : Λ') (n : ℕ),
        toC (conjVar A s) emb (Additive.toMul ((α' (1 ⊗ₜ lam)).1 n)) =
        Φ' (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)))
    (N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (hN : ∀ z, Φ' (N z) = twistC A (emb.comp (algebraMap K _)) s h (Φ z))
    (lam : Λ) (hlam : N lam ∈ Λ') :
    conjT A s cc hs ℓ (α (1 ⊗ₜ lam)) = α' (1 ⊗ₜ ⟨N lam, hlam⟩) := by
  apply Subtype.ext; funext n
  apply Additive.toMul.injective
  apply toC_injective (conjVar A s) emb
  change toC (conjVar A s) emb (conjPt A s cc hs (Additive.toMul ((α (1 ⊗ₜ lam)).1 n))) = _
  rw [hα', toC_conjPt A s cc hs emb hι h, hα, ← hN]
  congr 1
  have e : ∀ v : Fin g → ℂ, ((ℓ : ℂ) ^ n)⁻¹ • v = (((ℓ : ℝ) ^ n)⁻¹ : ℝ) • v := fun v => by
    ext i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast; rfl
  rw [e, e, map_smul]

/-! ## §8. The linear algebra of the lattice argument (proved)

The lattices replace the abstract `H` of `ConjBettiComparison`: with `ℤ`-bases of `Λ_A`, `Λ_B`,
the matrices of `c_*` and of `V_ℓ(f)` on `ℚ_ℓ ⊗ (ℤ_ℓ ⊗ Λ)` (through `ℚ_ℓ ⊗ α`, §10) are the
integer matrices of the lifts `N` and `M_f` on the lattices (§7). Faltings puts the first in the `ℚ_ℓ`-span of the others,
rationality (`matrix_mem_of_map_mem_span`) in their `ℚ`-span, so `N` is a `ℚ`-combination of
`ℂ`-linear maps on a basis of `ℂ^g` over `ℝ`, hence `ℂ`-linear; it is antilinear and nonzero. -/

section LatticeAlgebra

open Module

/-- **A lattice map determines the real-linear map (proved).** -/
theorem toLin_of_lattice {g : ℕ} {ΛA ΛB : Submodule ℤ (Fin g → ℂ)} {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
    (bA : Basis ιA ℤ ΛA) (bB : Basis ιB ℤ ΛB) (bAℝ : Basis ιA ℝ (Fin g → ℂ))
    (bBℝ : Basis ιB ℝ (Fin g → ℂ)) (hbA : ∀ i, bAℝ i = bA i) (hbB : ∀ i, bBℝ i = bB i)
    (u : ΛA →ₗ[ℤ] ΛB) (Y : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (hu : ∀ lam, (u lam : Fin g → ℂ) = Y lam) :
    Matrix.toLin bAℝ bBℝ ((LinearMap.toMatrix bA bB u).map (Int.castRingHom ℝ)) = Y := by
  apply bAℝ.ext; intro j
  rw [Matrix.toLin_self, hbA j, ← hu]
  conv_rhs => rw [← bB.sum_repr (u (bA j))]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, hbB i, Submodule.coe_smul, eq_intCast,
    Int.cast_smul_eq_zsmul]

/-- **The lattice contradiction (proved).** If the integer matrix of an antilinear nonzero `N`
lies in the `E`-span (`E ⊇ ℚ`) of the integer matrices of `ℂ`-linear maps `M_f`, then `False`. -/
theorem lattice_contradiction {g : ℕ} {ΛA ΛB : Submodule ℤ (Fin g → ℂ)} {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
    (bA : Basis ιA ℤ ΛA) (bB : Basis ιB ℤ ΛB) (bAℝ : Basis ιA ℝ (Fin g → ℂ))
    (bBℝ : Basis ιB ℝ (Fin g → ℂ)) (hbA : ∀ i, bAℝ i = bA i) (hbB : ∀ i, bBℝ i = bB i)
    (E : Type*) [Field E] [CharZero E] {S : Type*} (uM : S → (ΛA →ₗ[ℤ] ΛB))
    (M : S → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) (hM : ∀ f lam, (uM f lam : Fin g → ℂ) = M f lam)
    (uN : ΛA →ₗ[ℤ] ΛB) (N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (hN : ∀ lam, (uN lam : Fin g → ℂ) = N lam)
    (hanti : ∀ z, N (Complex.I • z) = -(Complex.I • N z)) (hN0 : N ≠ 0)
    (hspan : (LinearMap.toMatrix bA bB uN).map (Int.castRingHom E) ∈ Submodule.span E
      (Set.range fun f => (LinearMap.toMatrix bA bB (uM f)).map (Int.castRingHom E))) :
    False := by
  let W : Submodule ℚ (Matrix ιB ιA ℚ) := Submodule.span ℚ
    (Set.range fun f => (LinearMap.toMatrix bA bB (uM f)).map (Int.castRingHom ℚ))
  have hmapE : ∀ X : Matrix ιB ιA ℤ,
      (X.map (Int.castRingHom ℚ)).map (algebraMap ℚ E) = X.map (Int.castRingHom E) := by
    intro X; rw [Matrix.map_map]; congr 1; ext x; simp
  have hmapR : ∀ X : Matrix ιB ιA ℤ,
      (X.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) = X.map (Int.castRingHom ℝ) := by
    intro X; rw [Matrix.map_map]; congr 1
  have hXN : (LinearMap.toMatrix bA bB uN).map (Int.castRingHom ℚ) ∈ W := by
    apply matrix_mem_of_map_mem_span (E := E)
    rw [hmapE]
    refine Submodule.span_mono ?_ hspan
    rintro _ ⟨f, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨f, rfl⟩, hmapE _⟩
  have hP : ∀ X ∈ W, ∀ z, Matrix.toLin bAℝ bBℝ (X.map (algebraMap ℚ ℝ)) (Complex.I • z) =
      Complex.I • Matrix.toLin bAℝ bBℝ (X.map (algebraMap ℚ ℝ)) z := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      intro z
      rw [hmapR, toLin_of_lattice bA bB bAℝ bBℝ hbA hbB (uM f) ((M f).restrictScalars ℝ)
        (hM f)]
      exact (M f).map_smul Complex.I z
    | zero => intro z; simp
    | add x y _ _ hx hy =>
      intro z
      have e : (x + y).map (algebraMap ℚ ℝ) = x.map (algebraMap ℚ ℝ) + y.map (algebraMap ℚ ℝ) :=
        Matrix.map_add _ (map_add _) x y
      rw [e, map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy, smul_add]
    | smul q x _ hx =>
      intro z
      have e : (q • x).map (algebraMap ℚ ℝ) = (q : ℝ) • x.map (algebraMap ℚ ℝ) := by
        ext i j; simp [Matrix.map_apply, Algebra.smul_def]
      rw [e, LinearEquiv.map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hx, smul_comm]
  have hNlin := hP _ hXN
  rw [hmapR, toLin_of_lattice bA bB bAℝ bBℝ hbA hbB uN N hN] at hNlin
  apply hN0
  apply LinearMap.ext; intro z
  have h1 : Complex.I • N z = -(Complex.I • N z) := (hNlin z).symm.trans (hanti z)
  have h2 : Complex.I • N z = 0 := by
    have : (2 : ℂ) • (Complex.I • N z) = 0 := by
      rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel _
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  rw [LinearMap.zero_apply]
  exact (smul_eq_zero.mp h2).resolve_left Complex.I_ne_zero

end LatticeAlgebra

/-- `twistC` maps `1` to `1` (proved). -/
theorem twistC_one {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : twistC A σ s h 1 = 1 := by
  change (Over.mapPullbackAdj (specS s)).homEquiv _ _ (mapPtIso σ s ≫ conjHom σ s h ≫ 1) = 1
  rw [MonObj.comp_one, MonObj.comp_one, Adjunction.homEquiv_unit, Functor.map_one,
    MonObj.comp_one]
  rfl

/-! ## §9. N5 `ConjVarDim` (proved) -/

/-- A ring endomorphism of a number field is bijective. -/
theorem ringHom_bijective_of_numberField (K : Type) [Field K] [NumberField K] (s : K →+* K) :
    Function.Bijective s := by
  have hinj : Function.Injective s := s.injective
  refine ⟨hinj, ?_⟩
  have h := (LinearMap.injective_iff_surjective (f := s.toRatAlgHom.toLinearMap)).mp hinj
  exact h

/-- **N5 (proved).** For a number field, `dim A^s = dim A`: `Spec(s)` is an isomorphism, so the
projection `A^s → A` is an isomorphism of schemes, hence a homeomorphism. -/
theorem conjVarDim : ConjVarDim := by
  intro K _ _ A s
  have hb := ringHom_bijective_of_numberField K s
  let e : K ≃+* K := RingEquiv.ofBijective s hb
  haveI : IsIso (CommRingCat.ofHom s) :=
    ⟨⟨CommRingCat.ofHom (e.symm : K →+* K), by ext x; exact e.symm_apply_apply x,
      by ext x; exact e.apply_symm_apply x⟩⟩
  have : IsIso (specS s) := by unfold specS; infer_instance
  change topologicalKrullDim (conjVar A s).X.left = topologicalKrullDim A.X.left
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.Hom.homeomorph (Limits.pullback.fst A.X.hom (specS s))).isHomeomorph

/-! ## §9b. N3 from N2 and a smaller glue N3a (proved reduction)

`ConjAntiLiftLat` is N3 for number fields and full lattices (all that §10 uses). It follows from
N2 (`HomLinearLift` for the identity of `A^s`) and N3a (`ConjUniformization`): the conjugate
`z ↦ twistC(Φ z̄)` of a uniformization of `A(ℂ)_σ` is a uniformization of `A^s(ℂ)_σ`. -/

/-- Complex conjugation on `ℂ^g`, as an `ℝ`-linear map. -/
def conjL (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun z i := starRingEnd ℂ (z i)
  map_add' z w := by funext i; simp
  map_smul' r z := by funext i; simp

theorem conjL_conjL {g : ℕ} (z : Fin g → ℂ) : conjL g (conjL g z) = z := by
  funext i; simp [conjL]

theorem conjL_I {g : ℕ} (z : Fin g → ℂ) :
    conjL g (Complex.I • z) = -(Complex.I • conjL g z) := by
  funext i; simp [conjL]

/-- **N3a. The conjugate of a uniformization (GLUE, unproved; STANDARD).** If `σ ∘ s = conj ∘ σ`
and `Φ` uniformizes `A(ℂ)_σ` with kernel `Λ`, then `z ↦ twistC(Φ(z̄))` uniformizes `A^s(ℂ)_σ`
with kernel `Λ̄ = {z | z̄ ∈ Λ}`. (`A^s(ℂ)_σ = A(ℂ)_{σ∘s} = A(ℂ)_{conj∘σ}`, and on affine charts
`twistC` conjugates the values of regular functions, so `z ↦ s(twistC(Φ z̄)) = conj(s'(Φ z))`-type
compositions are holomorphic; the group-theoretic clauses follow from `twistC` being a bijective
homomorphism.) -/
def ConjUniformization : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ),
    A.dim = (g : WithBot ℕ∞) → IsUniformization σ Λ Φ →
    IsUniformization σ (Λ.comap ((conjL g).restrictScalars ℤ))
      (fun z => twistC A σ s h (Φ (conjL g z)))

/-- **N3 for number fields and full lattices (GLUE; implied by `ConjAntiLift`).** -/
def ConjAntiLiftLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) (Φ' : (Fin g → ℂ) → CPts (conjVar A s) σ),
    A.dim = (g : WithBot ℕ∞) → ∀ [DiscreteTopology Λ], IsZLattice ℝ Λ →
    IsUniformization σ Λ Φ → IsUniformization σ Λ' Φ' →
    ∃ N : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ z, N (Complex.I • z) = -(Complex.I • N z)) ∧
      Function.Injective N ∧ ∀ z, Φ' (N z) = twistC A σ s h (Φ z)

theorem conjAntiLiftLat_of_conjAntiLift (h : ConjAntiLift) : ConjAntiLiftLat :=
  fun K _ _ A σ s hs g Λ Λ' Φ Φ' hd _ _ hΦ hΦ' => h K A σ s hs g Λ Λ' Φ Φ' hd hΦ hΦ'

/-- `Spec(conj)` back from `σ` to `σ ∘ s`. -/
def conjHomInv {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : cptObj σ ⟶ cptObj (σ.comp s) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (starRingEnd ℂ))) (by
    simp only [cptObj, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    congr 2
    ext x
    simp)

/-- The inverse of `mapPtIso`. -/
def mapPtIsoInv {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K) :
    cptObj (σ.comp s) ⟶ (Over.map (specS s)).obj (cptObj σ) :=
  Over.homMk (𝟙 _) (by
    simp only [Over.map_obj_hom, cptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

theorem twistC_inj_aux {K : Type} [Field K] (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) :
    conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
    Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) = 𝟙 _
  rw [Category.id_comp, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

/-- `twistC` is injective (proved). -/
theorem twistC_injective {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (s : K →+* K)
    (h : σ.comp s = (starRingEnd ℂ).comp σ) : Function.Injective (twistC A σ s h) := by
  intro Q Q' hQ
  have h1 : mapPtIso σ s ≫ conjHom σ s h ≫ Q = mapPtIso σ s ≫ conjHom σ s h ≫ Q' :=
    ((Over.mapPullbackAdj (specS s)).homEquiv _ _).injective hQ
  calc Q = (conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h) ≫ Q := by
        rw [twistC_inj_aux, Category.id_comp]
    _ = conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ (mapPtIso σ s ≫ conjHom σ s h ≫ Q) := by
        simp only [Category.assoc]
    _ = conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ (mapPtIso σ s ≫ conjHom σ s h ≫ Q') := by
        rw [h1]
    _ = (conjHomInv σ s h ≫ mapPtIsoInv σ s ≫ mapPtIso σ s ≫ conjHom σ s h) ≫ Q' := by
        simp only [Category.assoc]
    _ = Q' := by rw [twistC_inj_aux, Category.id_comp]

/-- A vector all of whose real multiples lie in a full lattice is `0` (proved). -/
theorem eq_zero_of_real_smul_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (z : Fin g → ℂ) (hz : ∀ t : ℝ, t • z ∈ Λ) : z = 0 := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  let bℝ := b.ofZLatticeBasis ℝ Λ
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, bℝ.repr z j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (bℝ.repr.injective (Finsupp.ext fun j => by simp [hall j]))
  have hmem := hz (2 * bℝ.repr z j)⁻¹
  have e1 : bℝ.repr ((2 * bℝ.repr z j)⁻¹ • z) j = 1 / 2 := by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    field_simp
  have e2 : bℝ.repr ((2 * bℝ.repr z j)⁻¹ • z) j = (b.repr ⟨_, hmem⟩ j : ℝ) :=
    Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b ⟨_, hmem⟩ j
  rw [e1] at e2
  have : (2 : ℝ) * (b.repr ⟨_, hmem⟩ j : ℝ) = 1 := by rw [← e2]; norm_num
  have h3 : (2 * b.repr ⟨_, hmem⟩ j : ℤ) = 1 := by exact_mod_cast this
  omega

/-- **`ConjAntiLiftLat` from N2 and N3a (proved).** -/
theorem conjAntiLiftLat_of (hN2 : HomLinearLift) (hN3a : ConjUniformization) :
    ConjAntiLiftLat := by
  intro K _ _ A σ s h g Λ Λ' Φ Φ' hd _ hlat hΦ hΦ'
  have hd' : (conjVar A s).dim = (g : WithBot ℕ∞) := by rw [conjVarDim]; exact hd
  have hψ := hN3a K A σ s h g Λ Φ hd hΦ
  obtain ⟨M, hM⟩ := hN2 K (conjVar A s) (conjVar A s) σ g g _ Λ' _ Φ' hd' hd' hψ hΦ' 1
  have hM' : ∀ z, Φ' (M z) = twistC A σ s h (Φ (conjL g z)) := fun z => by
    rw [hM z]; exact Category.comp_id _
  refine ⟨(M.restrictScalars ℝ) ∘ₗ conjL g, fun z => ?_, ?_, fun z => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [conjL_I, map_neg, M.map_smul]
  · intro z w hzw
    have key : ∀ v, M (conjL g v) = 0 → v = 0 := by
      intro v hv
      apply eq_zero_of_real_smul_mem Λ v
      intro t
      rw [← hΦ.2.1]
      apply twistC_injective A σ s h
      rw [twistC_one, ← conjL_conjL (t • v), ← hM', map_smul, ← Complex.coe_smul,
        M.map_smul, hv, smul_zero]
      exact (hΦ'.2.1 0).mpr (Submodule.zero_mem _)
    have : M (conjL g (z - w)) = 0 := by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars] at hzw
      rw [map_sub, map_sub, hzw, sub_self]
    exact sub_eq_zero.mp (key _ this)
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [hM', conjL_conjL]

/-! ## §10. A weaker N4 suffices: an injective comparison (proved reduction)

Only injectivity of `α` is used: `ℚ_ℓ` is flat over `ℤ_ℓ`, so `ι = ℚ_ℓ ⊗ α` is injective, and
postcomposition with `ι_B` is injective on `Hom` spaces. The matrices are then taken on
`ℚ_ℓ ⊗ (ℤ_ℓ ⊗ Λ)`, where `c_*` and `V_ℓ(f)` become the base changes of `N|_Λ` and `M_f|_Λ`. -/

/-- **N4' (GLUE; weaker than `TateLattice`).** As `TateLattice` with `α` only an injective
`ℤ_ℓ`-linear map. -/
def TateLatticeInj : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K)))),
    A.dim = (g : WithBot ℕ∞) → ∀ [DiscreteTopology Λ], IsZLattice ℝ Λ →
    IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ α : TensorProduct ℤ ℤ_[ℓ] Λ →ₗ[ℤ_[ℓ]] A.T ℓ,
      Function.Injective α ∧
      ∀ (lam : Λ) (n : ℕ), toC A emb (Additive.toMul ((α (1 ⊗ₜ lam)).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ))

theorem tateLatticeInj_of_tateLattice (h : TateLattice) : TateLatticeInj := by
  intro K _ A emb g Λ Φ hd _ hlat hΦ ℓ _
  obtain ⟨α, hα⟩ := h K A emb g Λ Φ hd hlat hΦ ℓ
  exact ⟨α.toLinearMap, α.injective, hα⟩

/-- **`ConjTwistNontrivial` from T26, T35, N2, N3 and N4' (proved).** -/
theorem conjTwistNontrivial_of_latticeInj (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLiftLat) (hN4 : TateLatticeInj) : ConjTwistNontrivial := by
  classical
  intro hF K _ _ _ A ℓ _ hdim c hc hall
  obtain ⟨cc, emb, hι, hK, h2, hres⟩ := conjData K c hc
  let s := restrictK cc hK
  have hs : ∀ k, cc (algebraMap K _ k) = algebraMap K _ (s k) := restrictK_spec cc hK
  let σ : K →+* ℂ := emb.comp (algebraMap K (AlgebraicClosure K))
  have hσs : σ.comp s = (starRingEnd ℂ).comp σ := by
    apply RingHom.ext; intro k
    change emb (algebraMap K _ (s k)) = starRingEnd ℂ (emb (algebraMap K _ k))
    rw [← hs, hι]
  have hd2 : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hd2' : (conjVar A s).dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [conjVarDim]; exact hd2
  obtain ⟨ΛA, ΦA, hdA, hlatA, hA⟩ := h35 K A σ 2 hd2
  obtain ⟨ΛB, ΦB, hdB, hlatB, hB⟩ := h35 K (conjVar A s) σ 2 hd2'
  obtain ⟨N, hNanti, hNinj, hN⟩ := hN3 K A σ s hσs 2 ΛA ΛB ΦA ΦB hd2 hlatA hA hB
  obtain ⟨αA, -, hαA⟩ := hN4 K A emb 2 ΛA ΦA hd2 hlatA hA ℓ
  obtain ⟨αB, hαBinj, hαB⟩ := hN4 K (conjVar A s) emb 2 ΛB ΦB hd2' hlatB hB ℓ
  choose M hM using fun f => hN2 K A (conjVar A s) σ 2 2 ΛA ΛB ΦA ΦB hd2 hd2' hA hB f
  have heq : ∀ τ, conjV A s cc hs ℓ ∘ₗ A.galRep ℓ τ =
      (conjVar A s).galRep ℓ τ ∘ₗ conjV A s cc hs ℓ := by
    intro τ
    obtain ⟨σ', hσ'⟩ := exists_twist K cc hK h2 τ
    rw [hall σ' τ (hres σ' τ hσ'), conjV_galRep A s cc hs ℓ σ' τ hσ']
  have hspan := faltingsV hF hT A (conjVar A s) ℓ _ heq
  have hNlat : ∀ lam : ΛA, N lam ∈ ΛB := fun lam => by
    rw [← hB.2.1, hN, (hA.2.1 _).mpr lam.2]
    exact twistC_one A σ s hσs
  have hMlat : ∀ f (lam : ΛA), M f lam ∈ ΛB := fun f lam =>
    lift_mem_lattice hA hB f (M f) (hM f) lam
  let uN : ΛA →ₗ[ℤ] ΛB :=
    { toFun := fun lam => ⟨N lam, hNlat lam⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun n x => Subtype.ext (by
        simp only [RingHom.id_apply, Submodule.coe_smul]; exact map_zsmul N n _) }
  let uM : PkgI3.AbVar.Hom A (conjVar A s) → (ΛA →ₗ[ℤ] ΛB) := fun f =>
    { toFun := fun lam => ⟨M f lam, hMlat f lam⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun n x => Subtype.ext (by
        simp only [RingHom.id_apply, Submodule.coe_smul]; exact map_zsmul (M f) n _) }
  have hCN : ∀ lam, conjT A s cc hs ℓ (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ uN lam) := fun lam =>
    conjT_tateLattice A s cc hs emb hι hσs ℓ αA hαA αB hαB N hN lam (hNlat lam)
  have hMf : ∀ f lam, PkgI3.AbVar.homT f (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ uM f lam) :=
    fun f lam => homT_tateLattice emb ℓ αA hαA αB hαB f (M f) (hM f) lam (hMlat f lam)
  -- `ℚ_ℓ ⊗ α`
  let ιA := αA.baseChange ℚ_[ℓ]
  let ιB := αB.baseChange ℚ_[ℓ]
  have : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  have hιB : Function.Injective ιB := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ_[ℓ]) αB hαBinj
    rwa [← LinearMap.baseChange_eq_lTensor] at this
  let lift : (ΛA →ₗ[ℤ] ΛB) → (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]]
      ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛB)) := fun u => (u.baseChange ℤ_[ℓ]).baseChange ℚ_[ℓ]
  have hcomp : ∀ (Tm : A.T ℓ →ₗ[ℤ_[ℓ]] (conjVar A s).T ℓ) (u : ΛA →ₗ[ℤ] ΛB),
      (∀ lam, Tm (αA (1 ⊗ₜ lam)) = αB (1 ⊗ₜ u lam)) →
      Tm.baseChange ℚ_[ℓ] ∘ₗ ιA = ιB ∘ₗ lift u := by
    intro Tm u h
    simp only [ιA, ιB, lift, ← LinearMap.baseChange_comp]
    congr 1
    apply TensorProduct.AlgebraTensorModule.curry_injective
    apply LinearMap.ext_ring
    apply LinearMap.ext
    intro lam
    change Tm (αA (1 ⊗ₜ lam)) = αB ((u.baseChange ℤ_[ℓ]) (1 ⊗ₜ lam))
    rw [h, LinearMap.baseChange_tmul]
  let Pre : (A.V ℓ →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ) →ₗ[ℚ_[ℓ]]
      (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ) :=
    { toFun := fun X => X ∘ₗ ιA
      map_add' := fun X Y => LinearMap.add_comp _ _ _
      map_smul' := fun a X => LinearMap.smul_comp _ _ _ }
  let Post : (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛB)) →ₗ[ℚ_[ℓ]]
      (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] ΛA) →ₗ[ℚ_[ℓ]] (conjVar A s).V ℓ) :=
    { toFun := fun Y => ιB ∘ₗ Y
      map_add' := fun X Y => LinearMap.comp_add _ _ _
      map_smul' := fun a X => LinearMap.comp_smul _ _ _ }
  have hPost : Function.Injective Post := fun Y Y' h =>
    LinearMap.ext fun x => hιB (LinearMap.congr_fun h x)
  have key : lift uN ∈ Submodule.span ℚ_[ℓ] (Set.range fun f => lift (uM f)) := by
    have h1 := Submodule.mem_map_of_mem (f := Pre) hspan
    rw [homSpanV, Submodule.map_span, ← Set.range_comp] at h1
    have e1 : (⇑Pre ∘ fun f : PkgI3.AbVar.Hom A (conjVar A s) =>
        (PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ]) = ⇑Post ∘ fun f => lift (uM f) := by
      funext f
      exact hcomp _ _ (hMf f)
    have e2 : Pre (conjV A s cc hs ℓ) = Post (lift uN) := hcomp _ _ hCN
    rw [e1, Set.range_comp, ← Submodule.map_span, e2] at h1
    obtain ⟨y, hy, hyN⟩ := h1
    rwa [hPost hyN] at hy
  -- bases and matrices
  haveI := ZLattice.module_finite ℝ ΛA
  haveI := ZLattice.module_free ℝ ΛA
  haveI := ZLattice.module_finite ℝ ΛB
  haveI := ZLattice.module_free ℝ ΛB
  let bA := Module.Free.chooseBasis ℤ ΛA
  let bB := Module.Free.chooseBasis ℤ ΛB
  let bAℝ := bA.ofZLatticeBasis ℝ ΛA
  let bBℝ := bB.ofZLatticeBasis ℝ ΛB
  let TM := LinearMap.toMatrix (Algebra.TensorProduct.basis ℚ_[ℓ]
      (Algebra.TensorProduct.basis ℤ_[ℓ] bA))
    (Algebra.TensorProduct.basis ℚ_[ℓ] (Algebra.TensorProduct.basis ℤ_[ℓ] bB))
  have hTM : ∀ u, TM (lift u) = (LinearMap.toMatrix bA bB u).map (Int.castRingHom ℚ_[ℓ]) := by
    intro u
    simp only [TM, lift, LinearMap.toMatrix_baseChange, Matrix.map_map]
    congr 1
  have hspan' : (LinearMap.toMatrix bA bB uN).map (Int.castRingHom ℚ_[ℓ]) ∈
      Submodule.span ℚ_[ℓ]
        (Set.range fun f => (LinearMap.toMatrix bA bB (uM f)).map (Int.castRingHom ℚ_[ℓ])) := by
    have h1 := Submodule.mem_map_of_mem (f := TM.toLinearMap) key
    rw [Submodule.map_span, ← Set.range_comp] at h1
    rw [← hTM]
    convert h1 using 3
    funext f
    exact (hTM (uM f)).symm
  have hN0 : N ≠ 0 := by
    intro h0
    have : (Pi.single 0 1 : Fin 2 → ℂ) = 0 := hNinj (by rw [h0]; simp)
    have := congrFun this 0
    simp at this
  exact lattice_contradiction bA bB bAℝ bBℝ (fun i => by simp [bAℝ]) (fun i => by simp [bBℝ])
    ℚ_[ℓ] uM M (fun f lam => rfl) uN N (fun lam => rfl) hNanti hN0 hspan'

/-- **`ConjTwistNontrivial` from T26, T35, N2, N3 and N4 (proved; N5 is proved).** -/
theorem conjTwistNontrivial_of_lattice (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) (hN4 : TateLattice) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN2 (conjAntiLiftLat_of_conjAntiLift hN3)
    (tateLatticeInj_of_tateLattice hN4)

/-- **`ConjTwistFromLeaves` from N2, N3, N4' (proved):** T35 and T26 are among its
hypotheses. -/
theorem conjTwistFromLeaves_of_latticeInj (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) (hN4 : TateLatticeInj) : ConjTwistFromLeaves :=
  fun _ _ h35 _ hT => conjTwistNontrivial_of_latticeInj hT h35 hN2
    (conjAntiLiftLat_of_conjAntiLift hN3) hN4

/-- **`ConjTwistFromLeaves` from N2, N3, N4 (proved).** -/
theorem conjTwistFromLeaves_of_lattice (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) (hN4 : TateLattice) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_latticeInj hN2 hN3 (tateLatticeInj_of_tateLattice hN4)

/-! ## §11. N4' from N1 (proved): the injective comparison `ℤ_ℓ ⊗ Λ → T_ℓ(A)`

`x(λ)ₙ` is the unique `K̄`-point with `toC(x(λ)ₙ) = Φ(ℓ⁻ⁿλ)` (N1); `λ ↦ x(λ)` is additive, and its
`ℤ_ℓ`-linear extension is injective: if `Σ aᵢ x(bᵢ) = 0`, then `Φ(ℓ⁻ⁿ Σ (aᵢ mod ℓⁿ) bᵢ) = 1`, so
`Σ (aᵢ mod ℓⁿ) bᵢ ∈ ℓⁿΛ` and `ℓⁿ ∣ (aᵢ mod ℓⁿ)`, for every `n`. -/

section TateLatticeProof

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) {g : ℕ}
  (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))

theorem phi_zero (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) : Φ 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  have := congrArg (fun x => (Φ 0)⁻¹ * x) h
  simp only [inv_mul_cancel, inv_mul_cancel_left] at this
  exact this.symm

theorem phi_nsmul (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (k : ℕ) (z : Fin g → ℂ) :
    Φ (k • z) = Φ z ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero, phi_zero A emb Φ hadd]
  | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem phi_sum (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) {J : Type*} (s : Finset J)
    (f : J → (Fin g → ℂ)) : Φ (∑ i ∈ s, f i) = ∏ i ∈ s, Φ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phi_zero A emb Φ hadd]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem ell_ne_zero : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.out.ne_zero

theorem smul_inv_pow (n : ℕ) (v : Fin g → ℂ) : (ℓ ^ n : ℕ) • (((ℓ : ℂ) ^ n)⁻¹ • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  push_cast
  rw [mul_inv_cancel₀ (pow_ne_zero _ (ell_ne_zero ℓ)), one_smul]

theorem smul_inv_succ (n : ℕ) (v : Fin g → ℂ) :
    ℓ • (((ℓ : ℂ) ^ (n + 1))⁻¹ • v) = ((ℓ : ℂ) ^ n)⁻¹ • v := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have := ell_ne_zero ℓ
  field_simp
  ring

variable {Λ : Submodule ℤ (Fin g → ℂ)}
  (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)

include hadd hker in
theorem phi_tors (lam : Λ) (n : ℕ) : Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)) ^ (ℓ ^ n) = 1 := by
  rw [← phi_nsmul A emb Φ hadd, smul_inv_pow, (hker _).mpr lam.2]

variable (hsurj : ∀ n : ℕ, 0 < n → ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))),
    Q ^ n = 1 → ∃ P, toC A emb P = Q)

/-- `x(λ)ₙ ∈ A(K̄)` with `toC(x(λ)ₙ) = Φ(ℓ⁻ⁿλ)`. -/
def xPt (lam : Λ) (n : ℕ) : A.Pt (AlgebraicClosure K) :=
  Classical.choose (hsurj (ℓ ^ n) (pow_pos hℓ.out.pos n) _
    (phi_tors A emb Φ ℓ hadd hker lam n))

theorem xPt_spec (lam : Λ) (n : ℕ) :
    toC A emb (xPt A emb Φ ℓ hadd hker hsurj lam n) = Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)) :=
  Classical.choose_spec (hsurj (ℓ ^ n) (pow_pos hℓ.out.pos n) _
    (phi_tors A emb Φ ℓ hadd hker lam n))

/-- `x(λ) ∈ T_ℓ(A)`. -/
def xSeq (lam : Λ) : A.T ℓ :=
  ⟨fun n => Additive.ofMul (xPt A emb Φ ℓ hadd hker hsurj lam n), by
    refine ⟨?_, fun n => ?_⟩
    · apply Additive.toMul.injective
      change xPt A emb Φ ℓ hadd hker hsurj lam 0 = 1
      apply toC_injective A emb
      rw [xPt_spec, map_one, pow_zero, inv_one, one_smul]
      exact (hker _).mpr lam.2
    · apply Additive.toMul.injective
      change xPt A emb Φ ℓ hadd hker hsurj lam (n + 1) ^ ℓ = xPt A emb Φ ℓ hadd hker hsurj lam n
      apply toC_injective A emb
      rw [map_pow, xPt_spec, xPt_spec, ← phi_nsmul A emb Φ hadd, smul_inv_succ]⟩

theorem xSeq_apply (lam : Λ) (n : ℕ) :
    toC A emb (Additive.toMul ((xSeq A emb Φ ℓ hadd hker hsurj lam).1 n)) =
      Φ (((ℓ : ℂ) ^ n)⁻¹ • (lam : Fin g → ℂ)) :=
  xPt_spec A emb Φ ℓ hadd hker hsurj lam n

/-- `λ ↦ x(λ)`, additive. -/
def xHom : Λ →+ A.T ℓ :=
  AddMonoidHom.mk' (xSeq A emb Φ ℓ hadd hker hsurj) (fun a b => by
    apply Subtype.ext; funext n
    apply Additive.toMul.injective
    apply toC_injective A emb
    change toC A emb (Additive.toMul ((xSeq A emb Φ ℓ hadd hker hsurj (a + b)).1 n)) =
      toC A emb (Additive.toMul ((xSeq A emb Φ ℓ hadd hker hsurj a).1 n) *
        Additive.toMul ((xSeq A emb Φ ℓ hadd hker hsurj b).1 n))
    rw [map_mul, xSeq_apply, xSeq_apply, xSeq_apply, ← hadd, Submodule.coe_add, smul_add])

/-- `λ ↦ x(λ)`, `ℤ`-linear. -/
def xLin : Λ →ₗ[ℤ] A.T ℓ :=
  { xHom A emb Φ ℓ hadd hker hsurj with
    map_smul' := fun n x => by
      simp only [RingHom.id_apply]
      exact map_zsmul (xHom A emb Φ ℓ hadd hker hsurj) n x }

end TateLatticeProof

section TateLatticeInjProof

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) {g : ℕ}
  (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {Λ : Submodule ℤ (Fin g → ℂ)}
  (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
  (hsurj : ∀ n : ℕ, 0 < n → ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))),
    Q ^ n = 1 → ∃ P, toC A emb P = Q)

/-- **Injectivity of the comparison (proved from N1).** -/
theorem xLin_liftBaseChange_injective [Module.Free ℤ Λ] [Module.Finite ℤ Λ] :
    Function.Injective ((xLin A emb Φ ℓ hadd hker hsurj).liftBaseChange ℤ_[ℓ]) := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let bZ := Algebra.TensorProduct.basis ℤ_[ℓ] b
  set α := (xLin A emb Φ ℓ hadd hker hsurj).liftBaseChange ℤ_[ℓ] with hαdef
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  apply bZ.repr.injective
  refine Finsupp.ext fun j => ?_
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [map_zero]
  set a : Module.Free.ChooseBasisIndex ℤ Λ → ℤ_[ℓ] := fun i => bZ.repr v i with ha
  set k : Module.Free.ChooseBasisIndex ℤ Λ → ℕ := fun i => (PadicInt.toZModPow n (a i)).val
    with hk
  have hαv : α v = ∑ i, a i • xLin A emb Φ ℓ hadd hker hsurj (b i) := by
    conv_lhs => rw [← bZ.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.TensorProduct.basis_apply, hαdef, LinearMap.liftBaseChange_one_tmul]
  have hent : Additive.toMul ((α v).1 n) =
      ∏ i, Additive.toMul ((xLin A emb Φ ℓ hadd hker hsurj (b i)).1 n) ^ k i := by
    rw [hαv, AddSubgroup.val_finset_sum, Finset.sum_apply, toMul_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [PkgI3.Tate.smul_apply, toMul_nsmul]
  have h0 : Additive.toMul ((α v).1 n) = 1 := by rw [hv]; rfl
  let w : Λ := ∑ i, k i • b i
  have hC : Φ (((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ)) = 1 := by
    have e1 : toC A emb (Additive.toMul ((α v).1 n)) =
        Φ (((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ)) := by
      rw [hent, map_prod]
      simp only [map_pow]
      have e2 : ∀ i, toC A emb (Additive.toMul ((xLin A emb Φ ℓ hadd hker hsurj (b i)).1 n)) =
          Φ (((ℓ : ℂ) ^ n)⁻¹ • ((b i : Λ) : Fin g → ℂ)) := fun i =>
        xSeq_apply A emb Φ ℓ hadd hker hsurj (b i) n
      simp only [e2, ← phi_nsmul A emb Φ hadd]
      rw [← phi_sum A emb Φ hadd]
      congr 1
      simp only [w, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm]
    rw [← e1, h0, map_one]
  have hw : ((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ) ∈ Λ := (hker _).mp hC
  let mu : Λ := ⟨((ℓ : ℂ) ^ n)⁻¹ • (w : Fin g → ℂ), hw⟩
  have hwμ : w = (ℓ ^ n : ℕ) • mu := by
    apply Subtype.ext
    rw [Submodule.coe_smul_of_tower]
    exact (smul_inv_pow ℓ n (w : Fin g → ℂ)).symm
  have hrepr := congrArg (fun x => b.repr x j) hwμ
  simp only [w, map_sum, map_nsmul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hrepr
  have hdvd : (ℓ ^ n : ℕ) ∣ k j := by
    have h1 : ((ℓ ^ n : ℕ) : ℤ) ∣ ((k j : ℕ) : ℤ) := by
      refine ⟨b.repr mu j, ?_⟩
      simpa [nsmul_eq_mul] using hrepr
    exact Int.natCast_dvd_natCast.mp h1
  have hlt : k j < ℓ ^ n := ZMod.val_lt _
  exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hdvd hlt)

end TateLatticeInjProof

/-- **N4' from N1 (proved).** -/
theorem tateLatticeInj_of_artinTorsion (hN1 : ArtinTorsion) : TateLatticeInj := by
  intro K _ A emb g Λ Φ _ _ hlat hΦ ℓ _
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  have hsurj := fun n hn => (hN1 K A emb n hn).2
  refine ⟨(xLin A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj).liftBaseChange ℤ_[ℓ],
    xLin_liftBaseChange_injective A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj, fun lam n => ?_⟩
  rw [LinearMap.liftBaseChange_one_tmul]
  exact xSeq_apply A emb Φ ℓ hΦ.1 hΦ.2.1 hsurj lam n

/-- **`ConjTwistNontrivial` from T26, T35, N1, N2, N3 (proved).** -/
theorem conjTwistNontrivial_of_N123 (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hN1 : ArtinTorsion) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN2 (conjAntiLiftLat_of_conjAntiLift hN3)
    (tateLatticeInj_of_artinTorsion hN1)

/-- **`ConjTwistFromLeaves` from N1, N2, N3 (proved).** -/
theorem conjTwistFromLeaves_of_N123 (hN1 : ArtinTorsion) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_latticeInj hN2 hN3 (tateLatticeInj_of_artinTorsion hN1)

/-! ## §12. The injectivity half of N1 (proved)

`Spec ℂ → Spec K̄` is surjective, hence dominant, `Spec K̄` is reduced and `A → Spec K` is
separated (proper), so two `K̄`-points agreeing after `Spec ℂ → Spec K̄` are equal (Mathlib's
`ext_of_isDominant_of_isSeparated`). What remains of N1 is the torsion surjectivity. -/

/-- **N1-surj. Torsion comparison, surjectivity (GLUE, unproved; STANDARD).** Every `n`-torsion
point of `A(ℂ)_{ι∘alg}` (`n ≥ 1`) comes from `A(K̄)`. (`toC` is injective, `toC_injective`; both
`A(K̄)[n]` and `A(ℂ)[n]` have `n^{2g}` elements, by T5 over `K̄` and over `ℂ`; equivalently `A[n]`
is finite étale in characteristic `0`. Mumford §4, §6, UNVERIFIED numbers.) -/
def ArtinTorsionSurj : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (emb : AlgebraicClosure K →+* ℂ) (n : ℕ), 0 < n →
    ∀ Q : CPts A (emb.comp (algebraMap K (AlgebraicClosure K))), Q ^ n = 1 →
      ∃ P, toC A emb P = Q

theorem artinTorsion_of_surj (h : ArtinTorsionSurj) : ArtinTorsion :=
  fun K _ A emb n hn => ⟨toC_injective A emb, h K A emb n hn⟩

/-- **`ConjTwistNontrivial` from T26, T35, N1-surj, N2, N3 (proved).** -/
theorem conjTwistNontrivial_of_surj (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_N123 hT h35 (artinTorsion_of_surj hS) hN2 hN3

/-- **`ConjTwistFromLeaves` from N1-surj, N2, N3 (proved).** -/
theorem conjTwistFromLeaves_of_surj (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3 : ConjAntiLift) : ConjTwistFromLeaves :=
  conjTwistFromLeaves_of_N123 (artinTorsion_of_surj hS) hN2 hN3

/-- **Main result: `ConjTwistNontrivial` from T26, T35, N1-surj, N2 and N3a (proved).** -/
theorem conjTwistNontrivial_main (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3a : ConjUniformization) : ConjTwistNontrivial :=
  conjTwistNontrivial_of_latticeInj hT h35 hN2
    (conjAntiLiftLat_of hN2 hN3a) (tateLatticeInj_of_artinTorsion (artinTorsion_of_surj hS))

/-- **Main result: `ConjTwistFromLeaves` from N1-surj, N2 and N3a (proved).** -/
theorem conjTwistFromLeaves_main (hS : ArtinTorsionSurj) (hN2 : HomLinearLift)
    (hN3a : ConjUniformization) : ConjTwistFromLeaves :=
  fun _ _ h35 _ hT => conjTwistNontrivial_main hT h35 hS hN2 hN3a

end G0Galois

end ConjTwistSec

/-! ## g0-assemble2: g12-det (its new parts, assembled as in scratch/g12-det/build_int.py, minus ResQ and part_integrate) -/
noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace WeilPairing

open PkgI3 PkgI3.AbVar

variable {K : Type} [Field K]

/-! ## §1. Torsion, roots of unity, Galois actions -/

/-- The group `A(K̄)`, written additively. -/
abbrev P (A : AbVar K) : Type := Additive (A.Pt (AlgebraicClosure K))

/-- `A[n] = A(K̄)[n]`, the `n`-torsion of `A(K̄)`. -/
def tors (A : AbVar K) (n : ℕ) : AddSubgroup (P A) where
  carrier := {x | n • x = 0}
  add_mem' {x y} hx hy := by
    change n • x = 0 at hx
    change n • y = 0 at hy
    change n • (x + y) = 0
    rw [smul_add, hx, hy, add_zero]
  zero_mem' := smul_zero n
  neg_mem' {x} hx := by
    change n • x = 0 at hx
    change n • (-x) = 0
    rw [smul_neg, hx, neg_zero]

lemma mem_tors {A : AbVar K} {n : ℕ} {x : P A} : x ∈ tors A n ↔ n • x = 0 := Iff.rfl

lemma nsmul_tors {A : AbVar K} {n : ℕ} (x : tors A n) : n • (x : P A) = 0 := x.2

/-- A group homomorphism `A(K̄) → B(K̄)` restricted to `n`-torsion. -/
def torsHom {A B : AbVar K} (φ : P A →+ P B) (n : ℕ) : tors A n →+ tors B n where
  toFun x := ⟨φ x, by rw [mem_tors, ← map_nsmul, nsmul_tors x, map_zero]⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_add' x y := Subtype.ext (map_add φ _ _)

@[simp] lemma torsHom_coe {A B : AbVar K} (φ : P A →+ P B) (n : ℕ) (x : tors A n) :
    (torsHom φ n x : P B) = φ x := rfl

/-- The inclusion `A[n] ⊆ A[k]` for `n ∣ k`. -/
def torsIncl (A : AbVar K) {n k : ℕ} (h : n ∣ k) : tors A n →+ tors A k where
  toFun x := ⟨x, by
    obtain ⟨c, rfl⟩ := h
    rw [mem_tors, mul_comm, mul_smul, nsmul_tors x, smul_zero]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Multiplication by `m`, `A[m n] → A[n]`. -/
def torsSmul (A : AbVar K) (m n : ℕ) : tors A (m * n) →+ tors A n where
  toFun x := ⟨m • (x : P A), by
    rw [mem_tors, ← mul_smul, mul_comm, nsmul_tors x]⟩
  map_zero' := Subtype.ext (smul_zero m)
  map_add' x y := Subtype.ext (smul_add m (x : P A) y)

/-- `μ_n = μ_n(K̄)`, written additively. -/
abbrev Mu (K : Type) [Field K] (n : ℕ) : Type := Additive (rootsOfUnity n (AlgebraicClosure K))

/-- The underlying unit of `K̄` of an element of `μ_n`. -/
def Mu.val {n : ℕ} (z : Mu K n) : (AlgebraicClosure K)ˣ :=
  ((Additive.toMul z : rootsOfUnity n (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ)

@[simp] lemma Mu.val_add {n : ℕ} (z w : Mu K n) : (z + w).val = z.val * w.val := rfl
@[simp] lemma Mu.val_zero {n : ℕ} : (0 : Mu K n).val = 1 := rfl
@[simp] lemma Mu.val_nsmul {n : ℕ} (m : ℕ) (z : Mu K n) : (m • z).val = z.val ^ m := rfl
@[simp] lemma Mu.val_neg {n : ℕ} (z : Mu K n) : (-z).val = z.val⁻¹ := rfl

lemma Mu.val_injective {n : ℕ} : Function.Injective (Mu.val : Mu K n → _) := by
  intro z w h
  exact Additive.toMul.injective (Subtype.ext h)

lemma Mu.val_pow {n : ℕ} (z : Mu K n) : z.val ^ n = 1 :=
  (mem_rootsOfUnity n _).1 (Additive.toMul z).2

/-- Every element of `μ_n` is killed by `n`. -/
lemma Mu.nsmul_eq_zero {n : ℕ} (z : Mu K n) : n • z = 0 :=
  Mu.val_injective (by rw [Mu.val_nsmul, Mu.val_pow, Mu.val_zero])

/-- The absolute Galois group `G_K = Aut(K̄/K)` (definitionally `Field.absoluteGaloisGroup K`). -/
abbrev Gal (K : Type) [Field K] : Type := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

/-- `G_K` acting on `A(K̄)` (Objects' `galAct`: `σ` applied to coordinates). -/
def galP (A : AbVar K) (σ : Gal K) : P A →+ P A := MonoidHom.toAdditive (A.galAct σ)

/-- `G_K` acting on `A[n]`. -/
def galTors (A : AbVar K) (n : ℕ) (σ : Gal K) : tors A n →+ tors A n := torsHom (galP A σ) n

/-- `G_K` acting on `μ_n`. -/
def galMu (n : ℕ) (σ : Gal K) : Mu K n →+ Mu K n :=
  MonoidHom.toAdditive
    (restrictRootsOfUnity σ n)

@[simp] lemma galMu_val (n : ℕ) (σ : Gal K) (z : Mu K n) :
    ((galMu n σ z).val : AlgebraicClosure K) =
      σ (z.val : AlgebraicClosure K) := rfl

/-- A homomorphism `f : A → B` acting on `K̄`-points. -/
def homP {A B : AbVar K} (f : Hom A B) : P A →+ P B := MonoidHom.toAdditive (ptMap f)

/-- `f` acting on `n`-torsion. -/
def torsMap {A B : AbVar K} (f : Hom A B) (n : ℕ) : tors A n →+ tors B n := torsHom (homP f) n

/-- Homomorphisms of abelian varieties over `K` commute with `G_K` on `K̄`-points. -/
lemma homP_galP {A B : AbVar K} (f : Hom A B) (σ : Gal K) (x : P A) :
    homP f (galP A σ x) = galP B σ (homP f x) := by
  change Additive.ofMul ((galHom _ ≫ Additive.toMul x) ≫ f.hom) =
    Additive.ofMul (galHom _ ≫ (Additive.toMul x ≫ f.hom))
  rw [Category.assoc]

lemma torsMap_galTors {A B : AbVar K} (f : Hom A B) (n : ℕ) (σ : Gal K) (x : tors A n) :
    torsMap f n (galTors A n σ x) = galTors B n σ (torsMap f n x) :=
  Subtype.ext (homP_galP f σ x)

/-! ## §2. Pairings with values in `μ_n` -/

/-- A pairing `A[n] × B[n] → μ_n`. It is bi-additive (bimultiplicative in `μ_n`) and takes values
in `μ_n` by construction. -/
abbrev Pairing (A B : AbVar K) (n : ℕ) : Type := tors A n →+ tors B n →+ Mu K n

variable {A B A' B' : AbVar K} {n : ℕ}

/-- Perfect (both kernels trivial; for finite groups of the same order this is perfectness). -/
def IsPerfect (e : Pairing A B n) : Prop :=
  (∀ x, (∀ y, e x y = 0) → x = 0) ∧ (∀ y, (∀ x, e x y = 0) → y = 0)

/-- Alternating: `e(x, x) = 1` (written additively: `0`). -/
def IsAlternating (e : Pairing A A n) : Prop := ∀ x, e x x = 0

/-- Galois-equivariant: `e(σx, σy) = σ(e(x, y))`. -/
def IsGalEquivariant (e : Pairing A B n) : Prop :=
  ∀ (σ : Gal K) x y, e (galTors A n σ x) (galTors B n σ y) = galMu n σ (e x y)

/-- Pull-back of a pairing on `A'[n] × B'[n]` along `f : A(K̄) → A'(K̄)`, `g : B(K̄) → B'(K̄)`. -/
def pull (e : Pairing A' B' n) (f : P A →+ P A') (g : P B →+ P B') : Pairing A B n where
  toFun x := (e (torsHom f n x)).comp (torsHom g n)
  map_zero' := by ext y; simp
  map_add' x x' := by ext y; simp

@[simp] lemma pull_apply (e : Pairing A' B' n) (f : P A →+ P A') (g : P B →+ P B') (x y) :
    pull e f g x y = e (torsHom f n x) (torsHom g n y) := rfl

/-! ### Basic API -/

lemma add_left (e : Pairing A B n) (x x' y) : e (x + x') y = e x y + e x' y := by
  rw [map_add, AddMonoidHom.add_apply]

lemma add_right (e : Pairing A B n) (x y y') : e x (y + y') = e x y + e x y' := map_add _ _ _

/-- Bimultiplicativity, in `K̄ˣ`. -/
lemma val_mul_left (e : Pairing A B n) (x x' y) :
    (e (x + x') y).val = (e x y).val * (e x' y).val := by rw [add_left, Mu.val_add]

lemma val_mul_right (e : Pairing A B n) (x y y') :
    (e x (y + y')).val = (e x y).val * (e x y').val := by rw [add_right, Mu.val_add]

lemma nsmul_left (e : Pairing A B n) (m : ℕ) (x y) : e (m • x) y = m • e x y := by
  rw [map_nsmul, AddMonoidHom.nsmul_apply]

lemma nsmul_right (e : Pairing A B n) (m : ℕ) (x y) : e x (m • y) = m • e x y := map_nsmul _ _ _

/-- Values in `μ_n`: `e(x, y)ⁿ = 1`. -/
lemma val_pow_eq_one (e : Pairing A B n) (x y) : (e x y).val ^ n = 1 := Mu.val_pow _

/-- An alternating pairing is skew-symmetric: `e(x, y) = e(y, x)⁻¹`. -/
lemma IsAlternating.skew {e : Pairing A A n} (h : IsAlternating e) (x y) : e x y = -e y x := by
  have h1 := h (x + y)
  rw [add_left, add_right, add_right, h x, h y, zero_add, add_zero] at h1
  exact eq_neg_of_add_eq_zero_left h1

lemma IsAlternating.pull {e : Pairing A' A' n} (h : IsAlternating e) (f : P A →+ P A') :
    IsAlternating (pull e f f) := fun _ => h _

/-- Pull-back along `G_K`-equivariant maps preserves Galois equivariance. -/
lemma IsGalEquivariant.pull {e : Pairing A' B' n} (h : IsGalEquivariant e)
    {f : P A →+ P A'} {g : P B →+ P B'}
    (hf : ∀ σ x, f (galP A σ x) = galP A' σ (f x)) (hg : ∀ σ y, g (galP B σ y) = galP B' σ (g y)) :
    IsGalEquivariant (pull e f g) := by
  intro σ x y
  have h1 : torsHom f n (galTors A n σ x) = galTors A' n σ (torsHom f n x) := Subtype.ext (hf σ x)
  have h2 : torsHom g n (galTors B n σ y) = galTors B' n σ (torsHom g n y) := Subtype.ext (hg σ y)
  rw [pull_apply, pull_apply, h1, h2, h σ]

/-- In particular along homomorphisms of abelian varieties over `K` (compatibility with
isogenies). -/
lemma IsGalEquivariant.pull_hom {e : Pairing A' B' n} (h : IsGalEquivariant e)
    (f : Hom A A') (g : Hom B B') : IsGalEquivariant (WeilPairing.pull e (homP f) (homP g)) :=
  h.pull (homP_galP f) (homP_galP g)

/-- Perfectness forces nontrivial torsion on the right: if `e` is perfect and `B[n] = 0` then
`A[n] = 0` (a non-vacuity check on `WeilDual`). -/
lemma IsPerfect.left_trivial {e : Pairing A B n} (h : IsPerfect e)
    (hB : ∀ y : tors B n, y = 0) (x : tors A n) : x = 0 :=
  h.1 x fun y => by rw [hB y, map_zero]

/-- The zero pairing is perfect only when both torsion groups are trivial. -/
lemma isPerfect_zero_iff :
    IsPerfect (0 : Pairing A B n) ↔ (∀ x : tors A n, x = 0) ∧ (∀ y : tors B n, y = 0) :=
  ⟨fun h => ⟨fun x => h.1 x fun _ => rfl, fun y => h.2 y fun _ => rfl⟩,
   fun h => ⟨fun x _ => h.1 x, fun y _ => h.2 y⟩⟩

/-! ## §3. Duals (as seen by their Weil pairings), polarizations, the Weil pairing -/

/-- Composition of homomorphisms, `g ∘ f`. -/
def comp {A B C : AbVar K} (f : Hom A B) (g : Hom B C) : Hom A C := Hom.mk' (f.hom ≫ g.hom)

lemma homP_comp {A B C : AbVar K} (f : Hom A B) (g : Hom B C) (x : P A) :
    homP (comp f g) x = homP g (homP f x) := by
  change Additive.ofMul (Additive.toMul x ≫ (f.hom ≫ g.hom)) =
    Additive.ofMul ((Additive.toMul x ≫ f.hom) ≫ g.hom)
  rw [Category.assoc]

lemma torsMap_comp {A B C : AbVar K} (f : Hom A B) (g : Hom B C) (n : ℕ) (x : tors A n) :
    torsMap (comp f g) n x = torsMap g n (torsMap f n x) := Subtype.ext (homP_comp f g x)

/-- **The dual of `A`, as seen by its Weil pairings.** An abelian variety `Â` over `K` with a
family of pairings `e_n : A[n] × Â[n] → μ_n` which, for every `n ≥ 1` invertible in `K`, is
perfect and `G_K`-equivariant, and compatible: `e_{mn}(x, y) = e_n(m x, y)` for `x ∈ A[mn]`,
`y ∈ Â[n]` (Mumford, *Abelian varieties*, §20, properties of `e_n`; UNVERIFIED numbering).
The genuine dual `Â = Pic⁰_{A/K}` with Mumford's `e_n` is one (STANDARD; Mumford §§8, 13, 20 over
`K̄`, and the pairing is defined over `K`). Mathlib has no Picard scheme (no line bundles on
schemes), so `Pic⁰` cannot be defined here. CAUTION: a `WeilDual` is not unique; over an
algebraically closed `K` any `Â` with compatible isomorphisms `Â[n] ≅ A[n]` (all `n` invertible
in `K`) carries one, even `Â = A`. Hence leaves over
`WeilDual` must be *existential* (`∃ D : WeilDual A, …`, witnessed by `Pic⁰`); a leaf of the form
`∀ D : WeilDual A, …` need not be a consequence of the literature (see the report). -/
structure WeilDual (A : AbVar K) where
  /-- the dual abelian variety -/
  dual : AbVar K
  /-- the Weil pairings `e_n : A[n] × Â[n] → μ_n` -/
  e : ∀ n : ℕ, Pairing A dual n
  perfect : ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)
  galois : ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsGalEquivariant (e n)
  compat : ∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
    ∀ (x : tors A (m * n)) (y : tors dual n),
      (e (m * n) x (torsIncl dual (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val
  /-- every endomorphism has a dual (for `Pic⁰`: `f ↦ f^∨`, Mumford §8, §20 (5); UNVERIFIED);
  added after review so that Rosati conditions are never vacuous for lack of duals -/
  dualEnd : ∀ f : End A, ∃ fv : End dual, ∀ n : ℕ, 0 < n → (n : K) ≠ 0 →
    ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y

/-- `g : B̂ → Â` is dual to `f : A → B`: `e_n(x, g y) = e_n(f x, y)` for all `n` invertible in `K`
(Mumford §20, (5); UNVERIFIED numbering). -/
def IsDualHom {A B : AbVar K} (DA : WeilDual A) (DB : WeilDual B) (f : Hom A B)
    (g : Hom DB.dual DA.dual) : Prop :=
  ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x y, DA.e n x (torsMap g n y) = DB.e n (torsMap f n x) y

/-- Every endomorphism has a dual (field `dualEnd`). -/
lemma WeilDual.exists_dualEnd {A : AbVar K} (D : WeilDual A) (f : End A) :
    ∃ fv : End D.dual, IsDualHom D D f fv :=
  D.dualEnd f

/-- The dual morphism is unique on all torsion of order invertible in `K` (perfectness). -/
lemma IsDualHom.unique {A B : AbVar K} {DA : WeilDual A} {DB : WeilDual B} {f : Hom A B}
    {g g' : Hom DB.dual DA.dual} (hg : IsDualHom DA DB f g) (hg' : IsDualHom DA DB f g')
    {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) (y : tors DB.dual n) :
    torsMap g n y = torsMap g' n y := by
  have h := (DA.perfect n hn hnK).2 (torsMap g n y - torsMap g' n y) fun x => by
    rw [map_sub, hg n hn hnK, hg' n hn hnK, sub_self]
  exact sub_eq_zero.1 h

/-- Duals compose contravariantly: `(g ∘ f)^∨ = f^∨ ∘ g^∨`. -/
lemma IsDualHom.comp {A B C : AbVar K} {DA : WeilDual A} {DB : WeilDual B} {DC : WeilDual C}
    {f : Hom A B} {g : Hom B C} {fv : Hom DB.dual DA.dual} {gv : Hom DC.dual DB.dual}
    (hf : IsDualHom DA DB f fv) (hg : IsDualHom DB DC g gv) :
    IsDualHom DA DC (WeilPairing.comp f g) (WeilPairing.comp gv fv) := by
  intro n hn hnK x y
  rw [torsMap_comp, torsMap_comp, hf n hn hnK, hg n hn hnK]

/-- **The Weil pairing of `λ : A → Â`**: `e^λ_n(x, y) = e_n(x, λ y)` on `A[n]`
(Mumford §20, §23; UNVERIFIED numbering). -/
def weil {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) (n : ℕ) : Pairing A A n :=
  pull (D.e n) (AddMonoidHom.id _) (homP lam)

@[simp] lemma weil_apply {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) (n : ℕ) (x y) :
    weil D lam n x y = D.e n x (torsMap lam n y) := by
  simp only [weil, pull_apply]
  rfl

/-- `e^λ_n` is `G_K`-equivariant (`λ` is defined over `K`). -/
lemma weil_galois {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) {n : ℕ} (hn : 0 < n)
    (hnK : (n : K) ≠ 0) : IsGalEquivariant (weil D lam n) :=
  (D.galois n hn hnK).pull (fun _ _ => rfl) (homP_galP lam)

/-- `λ` is symmetric: every `e^λ_n` (`n` invertible in `K`) is alternating. For `λ = φ_L` this
is Mumford §23 ("`e^L` is skew-symmetric, `e^L(x, x) = 1`"); conversely a homomorphism with
skew-symmetric `e^λ` is symmetric, `λ^∨ = λ` (Mumford §20, §23; UNVERIFIED numbering). -/
def IsSymmetric {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) : Prop :=
  ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsAlternating (weil D lam n)

/-- **A symmetric isogeny** `λ : A → Â` (a polarization without the positivity condition). -/
structure SymmIsogeny (A : AbVar K) where
  /-- the dual -/
  D : WeilDual A
  /-- the isogeny `λ : A → Â` -/
  lam : Hom A D.dual
  isogeny : IsIsogenyMor lam.hom
  symm : IsSymmetric D lam

/-- `ψ : Â → A` is a quasi-inverse of `λ` of exponent `d`: `λ ψ = [d]` on `Â(K̄)` and
`ψ λ = [d]` on `A(K̄)`. -/
def IsQuasiInverse {A B : AbVar K} (f : Hom A B) (g : Hom B A) (d : ℕ) : Prop :=
  (∀ z : P B, homP f (homP g z) = d • z) ∧ ∀ x : P A, homP g (homP f x) = d • x

/-- (With `WeilDual.dualEnd`, every `φ` has some `φv`, so this is not vacuous.)
**Rosati positivity** of `λ`: for every nonzero `φ ∈ End(A)` with dual `φ^∨` and every
quasi-inverse `ψ` of `λ` of exponent `d ≥ 1` (so that `d·φ† = ψ φ^∨ λ`, `φ†` the Rosati
involution), the trace of `φ ∘ (d φ†)` on `T_ℓ A` is a positive integer, for every prime `ℓ`
invertible in `K` (Mumford §21, Thm 1: `Tr(φ φ†) > 0` for `φ ≠ 0`; Tr the trace of the
`2g`-dimensional `ℓ`-adic representation, Mumford §19; UNVERIFIED numbering). -/
def RosatiPositive {A : AbVar K} (S : SymmIsogeny A) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    ∀ (d : ℕ) (ψ : Hom S.D.dual A), 0 < d → IsQuasiInverse S.lam ψ d →
      ∀ (φ : End A) (φv : End S.D.dual), IsDualHom S.D S.D φ φv → φ ≠ 0 →
        ∃ t : ℕ, 0 < t ∧
          LinearMap.trace ℤ_[ℓ] (A.T ℓ)
            (homT (ℓ := ℓ) (WeilPairing.comp (WeilPairing.comp (WeilPairing.comp S.lam φv) ψ) φ))
            = (t : ℤ_[ℓ])

/-- **A polarization (up to sign)**: a symmetric isogeny with Rosati positivity. CAUTION: `-λ` has
the same Rosati involution, so `-φ_L` also qualifies (and on a product, `λ₁ × (-λ₂)`); the
genuine notion (ampleness) is not expressible without line bundles. Safe only in existential
leaves; a leaf `∀ S : Polarization A, …` would be unsafe. -/
structure Polarization (A : AbVar K) extends SymmIsogeny A where
  pos : RosatiPositive toSymmIsogeny

/-- **Principal**: `λ` is an isomorphism. -/
def SymmIsogeny.IsPrincipal {A : AbVar K} (S : SymmIsogeny A) : Prop :=
  ∃ g : Hom S.D.dual A, (WeilPairing.comp S.lam g).hom = 𝟙 _ ∧ (WeilPairing.comp g S.lam).hom = 𝟙 _

/-- **Nondegeneracy of `e^λ` up to `d`** (proved): if `λ ψ = [d]` on `Â(K̄)` and
`e^λ_n(x, y) = 1` for all `y ∈ A[n]`, then `d x = 0`. -/
lemma weil_nondeg {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) {ψ : Hom D.dual A} {d : ℕ}
    (hψ : ∀ z : P D.dual, homP lam (homP ψ z) = d • z) {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0)
    (x : tors A n) (hx : ∀ y, weil D lam n x y = 0) : d • x = 0 := by
  apply (D.perfect n hn hnK).1
  intro z
  have hz : torsMap lam n (torsMap ψ n z) = d • z := Subtype.ext (hψ z)
  rw [nsmul_left, ← nsmul_right, ← hz, ← weil_apply, hx]

/-- With a principal `λ`, `e^λ_n` is perfect. -/
lemma weil_perfect_of_principal {A : AbVar K} (S : SymmIsogeny A) (hS : S.IsPrincipal) {n : ℕ}
    (hn : 0 < n) (hnK : (n : K) ≠ 0) : IsPerfect (weil S.D S.lam n) := by
  obtain ⟨g, h1, h2⟩ := hS
  have hP : ∀ z : P S.D.dual, homP S.lam (homP g z) = (1 : ℕ) • z := fun z => by
    rw [one_smul, ← homP_comp]
    change Additive.ofMul (Additive.toMul z ≫ (WeilPairing.comp g S.lam).hom) = z
    rw [h2, Category.comp_id]; rfl
  refine ⟨fun x hx => by simpa using weil_nondeg S.D S.lam hP hn hnK x hx, fun y hy => ?_⟩
  -- skew-symmetry turns the right kernel into the left kernel
  have hy' : ∀ x, weil S.D S.lam n y x = 0 := fun x => by
    rw [(S.symm n hn hnK).skew, hy x, neg_zero]
  simpa using weil_nondeg S.D S.lam hP hn hnK y hy'

/-- **Pull-back of a symmetric `λ_B` along `f : A → B`** (compatibility with isogenies, proved):
if `f^∨` is dual to `f` then `f^∨ λ_B f : A → Â` is symmetric. -/
lemma isSymmetric_pullback {A B : AbVar K} {DA : WeilDual A} {DB : WeilDual B} {f : Hom A B}
    {fv : Hom DB.dual DA.dual} (hf : IsDualHom DA DB f fv) {lamB : Hom B DB.dual}
    (hB : IsSymmetric DB lamB) :
    IsSymmetric DA (WeilPairing.comp (WeilPairing.comp f lamB) fv) := by
  intro n hn hnK x
  rw [weil_apply, torsMap_comp, hf n hn hnK, torsMap_comp, ← weil_apply]
  exact hB n hn hnK _

/-- The Weil pairing of the pulled-back `λ` is the pull-back of the Weil pairing:
`e^{f^∨ λ f}_n(x, y) = e^λ_n(f x, f y)`. -/
lemma weil_pullback {A B : AbVar K} {DA : WeilDual A} {DB : WeilDual B} {f : Hom A B}
    {fv : Hom DB.dual DA.dual} (hf : IsDualHom DA DB f fv) (lamB : Hom B DB.dual) {n : ℕ}
    (hn : 0 < n) (hnK : (n : K) ≠ 0) (x y : tors A n) :
    weil DA (WeilPairing.comp (WeilPairing.comp f lamB) fv) n x y =
      weil DB lamB n (torsMap f n x) (torsMap f n y) := by
  rw [weil_apply, torsMap_comp, hf n hn hnK, torsMap_comp, ← weil_apply]

/-! ## §4. Leaves (`def … : Prop`) and the restated T9 -/

/-- **T9 (restated over the definitions of §3).** Every abelian variety over a field carries a
symmetric isogeny `λ : A → Â` to its dual, with Galois-equivariant perfect compatible Weil
pairings. Published: Mumford §6 (Application 1: `A` is projective, so an ample `L` exists over
`K`), §8 (`Â`), §13, §20 (the pairing `e_n`: bilinear, perfect, Galois-equivariant,
`e_{mn}(x, y) = e_n(m x, y)`), §23 (`e^L_n(x, x) = 1`, so `λ = φ_L` is symmetric), and `φ_L` is an
isogeny for ample `L` (§6, Application 1); Milne, *Abelian varieties* (Cornell–Silverman 1986)
§§8-13, 16 (UNVERIFIED numbering). Take `D = (Pic⁰, e_n)`, `λ = φ_L`. Existential in `D`, hence a
consequence, never stronger. -/
def T09_SymmIsogenyExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K), Nonempty (SymmIsogeny A)

/-- **T9⁺ (polarization).** Every abelian variety over a field has a polarization in the sense of
§3 (`λ = φ_L`, `L` ample over `K`; Rosati positivity is Mumford §21, Thm 1; UNVERIFIED
numbering). Not needed by G12 (which uses only T9). -/
def T09plus_PolarizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K), Nonempty (Polarization A)

/-- **Quasi-inverse of an isogeny.** For an isogeny `f : A → B` (finite and surjective) there are
`d ≥ 1` and `g : B → A` with `f g = [d]`, `g f = [d]` (take `d = deg f`, which kills `ker f`;
Mumford §7, Remark after Thm 4, and §8 Thm 1 (UNVERIFIED numbering); Milne 1986, Prop. 7.1 /
Rem. 8.4 (UNVERIFIED)). Stated on `K̄`-points, a consequence. -/
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B), IsIsogenyMor f.hom →
    ∃ d : ℕ, 0 < d ∧ ∃ g : Hom B A, IsQuasiInverse f g d

/-! ### Non-vacuity: the definitions are satisfiable (at `A = 0`) -/

lemma pt_zero_subsingleton (x y : (AbVar.zero K).Pt (AlgebraicClosure K)) : x = y :=
  CartesianMonoidalCategory.toUnit_unique x y

lemma tors_zero_eq (n : ℕ) (x : tors (AbVar.zero K) n) : x = 0 :=
  Subtype.ext (Additive.toMul.injective (pt_zero_subsingleton _ _))

/-- The zero abelian variety has a `WeilDual` (itself, zero pairings). -/
def weilDualZero (K : Type) [Field K] : WeilDual (AbVar.zero K) where
  dual := AbVar.zero K
  e _ := 0
  perfect _ _ _ := isPerfect_zero_iff.2 ⟨tors_zero_eq _, tors_zero_eq _⟩
  galois _ _ _ σ x y := by simp
  compat _ _ _ _ _ _ _ := rfl
  dualEnd _ := ⟨0, fun _ _ _ _ _ => rfl⟩

lemma isIsogenyMor_id (X : Over (Spec (CommRingCat.of K))) : IsIsogenyMor (𝟙 X) := by
  unfold IsIsogenyMor
  rw [Over.id_left]
  exact ⟨inferInstance, inferInstance⟩

/-- `T09_SymmIsogenyExists` holds at `A = 0`: the hypotheses are consistent. -/
theorem symmIsogeny_zero (K : Type) [Field K] : Nonempty (SymmIsogeny (AbVar.zero K)) :=
  ⟨{ D := weilDualZero K, lam := (1 : End (AbVar.zero K)), isogeny := isIsogenyMor_id _,
     symm := fun _ _ _ _ => rfl }⟩

/-! ## §5. The old consequence-form T9 (`LeafPush.T09_WeilPairing`), derived -/

namespace OldT9

universe u

open PkgI2

/-- Copied verbatim from `scratch/h-decomposition/Leaves.lean` (`LeafPush.T09_WeilPairing`, from
leaf-push), with `Type u` replaced by `Type` (the build uses universe `0`). -/
def T09_WeilPairing : Prop :=
  ∀ (K : Type) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
    ∃ d : ℕ, 0 < d ∧ ∃ e : ℕ → Pts A (AlgebraicClosure K) → Pts A (AlgebraicClosure K) →
        AlgebraicClosure K,
      ∀ n : ℕ, 0 < n → (n : K) ≠ 0 →
        (∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ y ∈ torsion A (AlgebraicClosure K) n,
          e n x y ^ n = 1) ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ x' ∈ torsion A (AlgebraicClosure K) n,
          ∀ y ∈ torsion A (AlgebraicClosure K) n,
            e n (x * x') y = e n x y * e n x' y ∧ e n y (x * x') = e n y x * e n y x') ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n, e n x x = 1) ∧
        (∀ x ∈ torsion A (AlgebraicClosure K) n,
          (∀ y ∈ torsion A (AlgebraicClosure K) n, e n x y = 1) → x ^ d = 1) ∧
        (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) n, ∀ y ∈ torsion A (AlgebraicClosure K) n,
            e n (galAct A σ x) (galAct A σ y) = σ (e n x y)) ∧
        (∀ m : ℕ, 0 < m → (m : K) ≠ 0 →
          ∀ x ∈ torsion A (AlgebraicClosure K) (m * n),
          ∀ y ∈ torsion A (AlgebraicClosure K) (m * n),
            e n (x ^ m) (y ^ m) = e (m * n) x y ^ m)

end OldT9

section Old

variable (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A]

/-- A torsion point of `A` (I2's multiplicative points) as an element of `tors (ofGrp A) n`. -/
def toT {n : ℕ} {x : PkgI2.Pts A (AlgebraicClosure K)} (hx : x ^ n = 1) :
    tors (ObjBridge.ofGrp A) n :=
  ⟨Additive.ofMul x, by rw [mem_tors]; change Additive.ofMul (x ^ n) = 0; rw [hx]; rfl⟩

open Classical in
/-- The old leaf's `e`, read off `e^λ`. -/
def oldE (S : SymmIsogeny (ObjBridge.ofGrp A)) (n : ℕ) (x y : PkgI2.Pts A (AlgebraicClosure K)) :
    AlgebraicClosure K :=
  if h : x ^ n = 1 ∧ y ^ n = 1 then ((weil S.D S.lam n (toT A h.1) (toT A h.2)).val : _) else 1

lemma oldE_eq (S : SymmIsogeny (ObjBridge.ofGrp A)) {n : ℕ} {x y : PkgI2.Pts A (AlgebraicClosure K)}
    (hx : x ^ n = 1) (hy : y ^ n = 1) :
    oldE A S n x y = ((weil S.D S.lam n (toT A hx) (toT A hy)).val : _) := by
  classical
  exact dite_eq_left_of_eq_true (eq_true ⟨hx, hy⟩)

end Old

/-- **The new T9 implies the old one.** `T09_SymmIsogenyExists` (over the definitions of §3)
together with `IsogenyQuasiInverse` implies the consequence-form leaf
`LeafPush.T09_WeilPairing` used by `scratch/h-decomposition/Leaves.lean` (`HSyn` bundle field
`t9`). So the old leaf can be replaced by the two leaves of §4. -/
theorem oldT9_of_symmIsogeny (h9 : T09_SymmIsogenyExists) (hQ : IsogenyQuasiInverse) :
    OldT9.T09_WeilPairing := by
  intro K _ A _
  obtain ⟨S⟩ := h9 K (ObjBridge.ofGrp A)
  obtain ⟨d, hd, ψ, hψ, -⟩ := hQ K _ _ S.lam S.isogeny
  refine ⟨d, hd, oldE A S, fun n hn hnK => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- values in `μ_n`
    intro x hx y hy
    rw [oldE_eq A S hx hy, ← Units.val_pow_eq_pow_val, val_pow_eq_one, Units.val_one]
  · -- bimultiplicative
    intro x hx x' hx' y hy
    have hxx' : (x * x') ^ n = 1 := by
      change x ^ n = 1 at hx
      change x' ^ n = 1 at hx'
      rw [mul_pow, hx, hx', one_mul]
    have e1 : toT A hxx' = toT A hx + toT A hx' := rfl
    refine ⟨?_, ?_⟩
    · rw [oldE_eq A S hxx' hy, oldE_eq A S hx hy, oldE_eq A S hx' hy, e1, val_mul_left,
        Units.val_mul]
    · rw [oldE_eq A S hy hxx', oldE_eq A S hy hx, oldE_eq A S hy hx', e1, val_mul_right,
        Units.val_mul]
  · -- alternating
    intro x hx
    rw [oldE_eq A S hx hx, S.symm n hn hnK, Mu.val_zero, Units.val_one]
  · -- nondegenerate up to `d`
    intro x hx H
    have h0 : ∀ t : tors (ObjBridge.ofGrp A) n, weil S.D S.lam n (toT A hx) t = 0 := by
      intro t
      have ht : (Additive.toMul (t : P (ObjBridge.ofGrp A))) ^ n = 1 :=
        Additive.ofMul.injective (nsmul_tors t)
      have h1 := H _ ht
      rw [oldE_eq A S hx ht] at h1
      have h2 : toT A ht = t := rfl
      rw [h2] at h1
      exact Mu.val_injective (Units.val_eq_one.1 h1)
    have h3 := weil_nondeg S.D S.lam hψ hn hnK (toT A hx) h0
    exact Additive.ofMul.injective (congrArg Subtype.val h3)
  · -- Galois-equivariant
    intro σ x hx y hy
    have hσx : (PkgI2.galAct A σ x) ^ n = 1 := by
      change x ^ n = 1 at hx
      rw [← PkgI2.galAct_pow, hx]
      exact MonObj.comp_one _
    have hσy : (PkgI2.galAct A σ y) ^ n = 1 := by
      change y ^ n = 1 at hy
      rw [← PkgI2.galAct_pow, hy]
      exact MonObj.comp_one _
    have ex : toT A hσx = galTors _ n σ (toT A hx) := rfl
    have ey : toT A hσy = galTors _ n σ (toT A hy) := rfl
    rw [oldE_eq A S hσx hσy, oldE_eq A S hx hy, ex, ey, weil_galois S.D S.lam hn hnK, galMu_val]
  · -- compatibility
    intro m hm hmK x hx y hy
    have hmn : 0 < m * n := Nat.mul_pos hm hn
    have hmnK : ((m * n : ℕ) : K) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hmK hnK
    change x ^ (m * n) = 1 at hx
    change y ^ (m * n) = 1 at hy
    have hxm : (x ^ m) ^ n = 1 := by rw [← pow_mul, hx]
    have hym : (y ^ m) ^ n = 1 := by rw [← pow_mul, hy]
    have ex : toT A hxm = torsSmul _ m n (toT A hx) := rfl
    have ey : torsIncl _ (dvd_mul_left n m) (torsMap S.lam n (toT A hym)) =
        m • torsMap S.lam (m * n) (toT A hy) := by
      apply Subtype.ext
      change homP S.lam (Additive.ofMul (y ^ m)) = m • homP S.lam (Additive.ofMul y)
      rw [← map_nsmul]
      rfl
    rw [oldE_eq A S hxm hym, oldE_eq A S hx hy, weil_apply, ex,
      ← S.D.compat m n hm hn hmnK, ey, nsmul_right, Mu.val_nsmul, ← weil_apply,
      Units.val_pow_eq_pow_val]

/-! ## §6. The G12 input: the multiplier is cyclotomic; `det² = χ^{rank}` -/

/-- `G_K` acts on `μ_n` through the mod-`n` cyclotomic character (Mathlib's
`modularCyclotomicCharacter'`). -/
lemma galMu_eq_nsmul (n : ℕ) [NeZero n] (σ : Gal K) (z : Mu K n) :
    galMu n σ z =
      (Units.val (modularCyclotomicCharacter' (AlgebraicClosure K) n σ.toRingEquiv)).val • z := by
  apply Mu.val_injective
  apply Units.ext
  rw [galMu_val, Mu.val_nsmul, Units.val_pow_eq_pow_val]
  have := modularCyclotomicCharacter'.spec' (AlgebraicClosure K) n σ.toRingEquiv
    (Additive.toMul z).2
  exact this

/-- **Finite-level G12 input (proved).** For `n` invertible in `K`, `e^λ_n` has cyclotomic
multiplier: `e^λ_n(σx, σy) = χ_n(σ) · e^λ_n(x, y)` (additively), `χ_n` the mod-`n` cyclotomic
character. Hence `G_K` acts on `A[n]` through `GSp(e^λ_n)` with multiplier `χ_n`. -/
theorem weil_cyclotomic {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual) {n : ℕ} [NeZero n]
    (hnK : (n : K) ≠ 0) (σ : Gal K) (x y : tors A n) :
    weil D lam n (galTors A n σ x) (galTors A n σ y) =
      (Units.val (modularCyclotomicCharacter' (AlgebraicClosure K) n σ.toRingEquiv)).val •
        weil D lam n x y := by
  rw [weil_galois D lam (Nat.pos_of_ne_zero (NeZero.ne n)) hnK, galMu_eq_nsmul]

/-- **The determinant identity (proved, linear algebra).** Let `B` be a bilinear form on a free
module with basis `b` over a commutative ring, with Gram determinant a unit (a perfect
pairing), and `f` a similitude with multiplier `c`: `B(f x, f y) = c B(x, y)`. Then
`det(f)² = c^{rank}`. For `M = V_ℓ(A)`, `B` the `ℓ`-adic Weil pairing of `λ` (perfect on
`V_ℓ`) and `f = ρ_ℓ(σ)`, `c = χ_ℓ(σ)`: `det ρ_ℓ(σ)² = χ_ℓ(σ)^{2g}`, the input
`(det r₅)⁴ = χ⁴` on `G_F` (for `g = 2`) of C8's determinant argument. -/
theorem det_sq_of_similitude {R M idx : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype idx] [DecidableEq idx] (b : Module.Basis idx R M) (B : LinearMap.BilinForm R M)
    (hB : IsUnit (LinearMap.BilinForm.toMatrix b B).det) (f : M →ₗ[R] M) (c : R)
    (hf : ∀ x y, B (f x) (f y) = c * B x y) :
    LinearMap.det f ^ 2 = c ^ Fintype.card idx := by
  have hc : B.comp f f = c • B := by
    ext x y
    simp [hf]
  have h1 := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hc, map_smul] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix] at h2
  exact hB.mul_left_cancel (by linear_combination -h2)

/-- Over a field: a nondegenerate `B` with multiplier `c` for `f` gives `det(f)² = c^{dim}`. -/
theorem det_sq_of_similitude_field {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] (B : LinearMap.BilinForm F M) (hB : B.Nondegenerate)
    (f : M →ₗ[F] M) (c : F) (hf : ∀ x y, B (f x) (f y) = c * B x y) :
    LinearMap.det f ^ 2 = c ^ Module.finrank F M := by
  classical
  let b := Module.finBasis F M
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hB
  rw [det_sq_of_similitude b B (Ne.isUnit hdet) f c hf, Fintype.card_fin]

-- (twist_finite_four, WeilPairing.lean L644-675, omitted: it uses GlueAssembly)


/-! ## §7. The `ℓ`-adic Weil pairing on `T_ℓ A`, with cyclotomic multiplier -/

section Adic

variable {A : AbVar K} (D : WeilDual A) (lam : Hom A D.dual)

open Classical in
/-- `e^λ_n` on all of `A(K̄)`, as a unit of `K̄` (junk value `1` off `A[n]`); a non-dependent
form used to pass to the limit. -/
def wv (n : ℕ) (x y : P A) : (AlgebraicClosure K)ˣ :=
  if h : n • x = 0 ∧ n • y = 0 then (weil D lam n ⟨x, h.1⟩ ⟨y, h.2⟩).val else 1

variable {D lam}

lemma wv_eq {n : ℕ} {x y : P A} (hx : n • x = 0) (hy : n • y = 0) :
    wv D lam n x y = (weil D lam n ⟨x, hx⟩ ⟨y, hy⟩).val := by
  classical
  exact dite_eq_left_of_eq_true (eq_true ⟨hx, hy⟩)

lemma wv_pow (n : ℕ) (x y : P A) : wv D lam n x y ^ n = 1 := by
  classical
  unfold wv
  split_ifs
  · exact val_pow_eq_one _ _ _
  · exact one_pow n

lemma wv_one (x y : P A) : wv D lam 1 x y = 1 := by
  simpa using wv_pow (D := D) (lam := lam) 1 x y

lemma wv_add_left {n : ℕ} {x x' y : P A} (hx : n • x = 0) (hx' : n • x' = 0) (hy : n • y = 0) :
    wv D lam n (x + x') y = wv D lam n x y * wv D lam n x' y := by
  have hxx' : n • (x + x') = 0 := by rw [smul_add, hx, hx', add_zero]
  rw [wv_eq hxx' hy, wv_eq hx hy, wv_eq hx' hy]
  exact val_mul_left _ ⟨x, hx⟩ ⟨x', hx'⟩ _

lemma wv_add_right {n : ℕ} {x y y' : P A} (hx : n • x = 0) (hy : n • y = 0) (hy' : n • y' = 0) :
    wv D lam n x (y + y') = wv D lam n x y * wv D lam n x y' := by
  have hyy' : n • (y + y') = 0 := by rw [smul_add, hy, hy', add_zero]
  rw [wv_eq hx hyy', wv_eq hx hy, wv_eq hx hy']
  exact val_mul_right _ _ ⟨y, hy⟩ ⟨y', hy'⟩

lemma wv_nsmul_left {n : ℕ} (c : ℕ) {x y : P A} (hx : n • x = 0) (hy : n • y = 0) :
    wv D lam n (c • x) y = wv D lam n x y ^ c := by
  have hcx : n • (c • x) = 0 := by rw [smul_comm, hx, smul_zero]
  rw [wv_eq hcx hy, wv_eq hx hy, ← Mu.val_nsmul, ← nsmul_left]
  rfl

lemma wv_nsmul_right {n : ℕ} (c : ℕ) {x y : P A} (hx : n • x = 0) (hy : n • y = 0) :
    wv D lam n x (c • y) = wv D lam n x y ^ c := by
  have hcy : n • (c • y) = 0 := by rw [smul_comm, hy, smul_zero]
  rw [wv_eq hx hcy, wv_eq hx hy, ← Mu.val_nsmul, ← nsmul_right]
  rfl

/-- Compatibility: `e^λ_n(m x, m y) = e^λ_{mn}(x, y)^m`. -/
lemma wv_compat {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hK : ((m * n : ℕ) : K) ≠ 0) {x y : P A}
    (hx : (m * n) • x = 0) (hy : (m * n) • y = 0) :
    wv D lam n (m • x) (m • y) = wv D lam (m * n) x y ^ m := by
  have hmx : n • (m • x) = 0 := by rw [← mul_smul, mul_comm, hx]
  have hmy : n • (m • y) = 0 := by rw [← mul_smul, mul_comm, hy]
  have ex : (⟨m • x, hmx⟩ : tors A n) = torsSmul A m n ⟨x, hx⟩ := rfl
  have ey : torsIncl _ (dvd_mul_left n m) (torsMap lam n ⟨m • y, hmy⟩) =
      m • torsMap lam (m * n) ⟨y, hy⟩ := by
    apply Subtype.ext
    change homP lam (m • y) = m • homP lam y
    rw [map_nsmul]
  rw [wv_eq hmx hmy, wv_eq hx hy, weil_apply, ex, ← D.compat m n hm hn hK, ey, nsmul_right,
    Mu.val_nsmul, ← weil_apply]

/-- `G_K`-equivariance: `e^λ_n(σx, σy) = σ(e^λ_n(x, y))`. -/
lemma wv_galois {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) (σ : Gal K) {x y : P A}
    (hx : n • x = 0) (hy : n • y = 0) :
    wv D lam n (galP A σ x) (galP A σ y) =
      Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K) (wv D lam n x y) := by
  have hσx : n • galP A σ x = 0 := by rw [← map_nsmul, hx, map_zero]
  have hσy : n • galP A σ y = 0 := by rw [← map_nsmul, hy, map_zero]
  have ex : (⟨galP A σ x, hσx⟩ : tors A n) = galTors A n σ ⟨x, hx⟩ := rfl
  have ey : (⟨galP A σ y, hσy⟩ : tors A n) = galTors A n σ ⟨y, hy⟩ := rfl
  rw [wv_eq hσx hσy, wv_eq hx hy, ex, ey, weil_galois D lam hn hnK]
  rfl

variable (D lam)
variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(μ) = lim μ_{ℓᵏ}(K̄)`, as Objects' `Tate.T` of `K̄ˣ`. -/
abbrev TMu (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  Tate.T ℓ (Additive (AlgebraicClosure K)ˣ)

/-- `G_K` acting on `T_ℓ(μ)`. -/
def galTMu (σ : Gal K) : TMu K ℓ →ₗ[ℤ_[ℓ]] TMu K ℓ :=
  Tate.map (MonoidHom.toAdditive (Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K)))

omit [Fact ℓ.Prime] in
lemma tors_pow {x : A.T ℓ} (k : ℕ) : (ℓ ^ k) • x.1 k = 0 := Tate.pow_smul_eq_zero x.2 k

/-- The components `e^λ_{ℓᵏ}(x_k, y_k)`. -/
def tateSeq (x y : A.T ℓ) : ℕ → Additive (AlgebraicClosure K)ˣ :=
  fun k => Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k))

variable {ℓ}

lemma tateSeq_mem (hℓ : (ℓ : K) ≠ 0) (x y : A.T ℓ) : tateSeq D lam ℓ x y ∈ Tate.T ℓ _ := by
  refine ⟨?_, fun k => ?_⟩
  · change Additive.ofMul (wv D lam (ℓ ^ 0) _ _) = 0
    rw [pow_zero, wv_one]
    rfl
  · change Additive.ofMul (wv D lam (ℓ ^ (k + 1)) (x.1 (k + 1)) (y.1 (k + 1)) ^ ℓ) =
      Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k))
    congr 1
    have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
    have hK : ((ℓ * ℓ ^ k : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_mul, Nat.cast_pow]; exact mul_ne_zero hℓ (pow_ne_zero _ hℓ)
    have hx : (ℓ * ℓ ^ k) • x.1 (k + 1) = 0 := by rw [← pow_succ']; exact tors_pow ℓ (k + 1)
    have hy : (ℓ * ℓ ^ k) • y.1 (k + 1) = 0 := by rw [← pow_succ']; exact tors_pow ℓ (k + 1)
    rw [← x.2.2 k, ← y.2.2 k, wv_compat hl (pow_pos hl k) hK hx hy, pow_succ']

/-- **The `ℓ`-adic Weil pairing** `E^λ : T_ℓ A × T_ℓ A → T_ℓ(μ)`, `ℤ_ℓ`-bilinear, with
components `e^λ_{ℓᵏ}(x_k, y_k)`. -/
def tatePairing (hℓ : (ℓ : K) ≠ 0) : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ →ₗ[ℤ_[ℓ]] TMu K ℓ :=
  LinearMap.mk₂ ℤ_[ℓ] (fun x y => ⟨tateSeq D lam ℓ x y, tateSeq_mem D lam hℓ x y⟩)
    (fun x x' y => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k + x'.1 k) (y.1 k)) =
        Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k) * wv D lam (ℓ ^ k) (x'.1 k) (y.1 k))
      rw [wv_add_left (tors_pow ℓ k) (tors_pow ℓ k) (tors_pow ℓ k)])
    (fun a x y => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D lam (ℓ ^ k) ((PadicInt.toZModPow k a).val • x.1 k) (y.1 k)) =
        Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k) ^ (PadicInt.toZModPow k a).val)
      rw [wv_nsmul_left _ (tors_pow ℓ k) (tors_pow ℓ k)])
    (fun x y y' => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k + y'.1 k)) =
        Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k) * wv D lam (ℓ ^ k) (x.1 k) (y'.1 k))
      rw [wv_add_right (tors_pow ℓ k) (tors_pow ℓ k) (tors_pow ℓ k)])
    (fun a x y => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) ((PadicInt.toZModPow k a).val • y.1 k)) =
        Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k) ^ (PadicInt.toZModPow k a).val)
      rw [wv_nsmul_right _ (tors_pow ℓ k) (tors_pow ℓ k)])

lemma tatePairing_apply (hℓ : (ℓ : K) ≠ 0) (x y : A.T ℓ) (k : ℕ) :
    (tatePairing D lam hℓ x y).1 k = Additive.ofMul (wv D lam (ℓ ^ k) (x.1 k) (y.1 k)) := rfl

/-- `E^λ` is alternating when `λ` is symmetric. -/
theorem tatePairing_self (hS : IsSymmetric D lam) (hℓ : (ℓ : K) ≠ 0) (x : A.T ℓ) :
    tatePairing D lam hℓ x x = 0 := by
  have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  apply Subtype.ext; funext k
  rw [tatePairing_apply, wv_eq (tors_pow ℓ k) (tors_pow ℓ k),
    hS (ℓ ^ k) (pow_pos hl k) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ)]
  rfl

/-- `E^λ` is `G_K`-equivariant: `E^λ(σx, σy) = σ E^λ(x, y)`. -/
theorem tatePairing_galois (hℓ : (ℓ : K) ≠ 0) (σ : Gal K) (x y : A.T ℓ) :
    tatePairing D lam hℓ (A.galT σ x) (A.galT σ y) = galTMu ℓ σ (tatePairing D lam hℓ x y) := by
  have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  apply Subtype.ext; funext k
  change Additive.ofMul (wv D lam (ℓ ^ k) (galP A σ (x.1 k)) (galP A σ (y.1 k))) =
    Additive.ofMul (Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K)
      (wv D lam (ℓ ^ k) (x.1 k) (y.1 k)))
  rw [wv_galois (pow_pos hl k) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ) σ (tors_pow ℓ k)
    (tors_pow ℓ k)]

/-- `G_K` acts on `T_ℓ(μ)` through the `ℓ`-adic cyclotomic character (Mathlib's
`cyclotomicCharacter`). -/
theorem galTMu_eq_cyclotomic [NeZero (ℓ : K)] (σ : Gal K) (z : TMu K ℓ) :
    galTMu ℓ σ z = ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • z := by
  apply Subtype.ext; funext k
  have hz : ((Additive.toMul (z.1 k) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) ^ ℓ ^ k = 1 := by
    have h := Tate.pow_smul_eq_zero z.2 k
    have h' : (Additive.toMul (z.1 k)) ^ ℓ ^ k = 1 := Additive.ofMul.injective h
    rw [← Units.val_pow_eq_pow_val, h', Units.val_one]
  have := cyclotomicCharacter.spec ℓ (n := k) σ.toRingEquiv _ hz
  change Additive.ofMul (Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K)
      (Additive.toMul (z.1 k))) = Additive.ofMul ((Additive.toMul (z.1 k)) ^ _)
  congr 1
  apply Units.ext
  rw [Units.coe_map, Units.val_pow_eq_pow_val]
  exact this

/-- **The `ℓ`-adic G12 input (proved):** `E^λ(σx, σy) = χ_ℓ(σ) · E^λ(x, y)`, i.e. `G_K` acts on
`T_ℓ A` through `GSp(E^λ)` with the cyclotomic multiplier (C8 item 1). -/
theorem tatePairing_cyclotomic [NeZero (ℓ : K)] (σ : Gal K) (x y : A.T ℓ) :
    tatePairing D lam (NeZero.ne _) (A.galT σ x) (A.galT σ y) =
      ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) •
        tatePairing D lam (NeZero.ne _) x y := by
  rw [tatePairing_galois, galTMu_eq_cyclotomic]

end Adic


/-! ## §8. Nondegeneracy of `E^λ` and `det ρ_ℓ(σ)² = χ_ℓ(σ)^{2g}` -/

section Det

/-- Iterating `ℓ • u(i+1) = u i`. -/
lemma iterate_smul {M : Type*} [AddCommGroup M] {ℓ : ℕ} {u : ℕ → M}
    (hu : ∀ i, ℓ • u (i + 1) = u i) (k a : ℕ) : ℓ ^ a • u (k + a) = u k := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ, mul_smul, ← Nat.add_assoc, hu, ih]

/-- If `a • x = 0` and `b • x = 0` with `a, b` coprime then `x = 0`. -/
lemma eq_zero_of_coprime {M : Type*} [AddCommGroup M] {x : M} {a b : ℕ} (hab : a.Coprime b)
    (ha : a • x = 0) (hb : b • x = 0) : x = 0 := by
  have h1 := addOrderOf_dvd_of_nsmul_eq_zero ha
  have h2 := addOrderOf_dvd_of_nsmul_eq_zero hb
  have h3 : addOrderOf x ∣ 1 := by
    rw [← hab.gcd_eq_one]; exact Nat.dvd_gcd h1 h2
  exact AddMonoid.addOrderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

/-- **Leaf (divisibility of `A(K̄)`).** For `n ≥ 1`, `[n] : A → A` is an isogeny (of degree
`n^{2g}`), hence surjective, hence surjective on `K̄`-points (Mumford §4, Application 2, and §6;
UNVERIFIED numbering). -/
def DivisiblePoints : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), 0 < n → ∀ z : P A, ∃ w : P A, n • w = z

variable {A : AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]

/-- A sequence of successive `ℓ`-th roots starting at `t`. -/
def rootSeq {M : Type*} [AddCommGroup M] (hdiv : ∀ z : M, ∃ w : M, ℓ • w = z) (t : M) : ℕ → M
  | 0 => t
  | i + 1 => Classical.choose (hdiv (rootSeq hdiv t i))

omit [Fact ℓ.Prime] in
lemma rootSeq_succ {M : Type*} [AddCommGroup M] (hdiv : ∀ z : M, ∃ w : M, ℓ • w = z) (t : M)
    (i : ℕ) : ℓ • rootSeq hdiv t (i + 1) = rootSeq hdiv t i :=
  Classical.choose_spec (hdiv (rootSeq hdiv t i))

omit [Fact ℓ.Prime] in
/-- `T_ℓ M → M[ℓᵏ]` is onto when `M` is `ℓ`-divisible (glue; for `M = A(K̄)` from
`DivisiblePoints`). -/
theorem tate_surj {M : Type*} [AddCommGroup M] (hdiv : ∀ z : M, ∃ w : M, ℓ • w = z) (k : ℕ)
    (t : M) (ht : ℓ ^ k • t = 0) : ∃ y : Tate.T ℓ M, y.1 k = t := by
  refine ⟨⟨fun j => ℓ ^ k • rootSeq hdiv t j, ?_, fun j => ?_⟩, ?_⟩
  · change ℓ ^ k • t = 0; exact ht
  · change ℓ • ℓ ^ k • rootSeq hdiv t (j + 1) = ℓ ^ k • rootSeq hdiv t j
    rw [smul_comm, rootSeq_succ]
  · change ℓ ^ k • rootSeq hdiv t k = t
    have := iterate_smul (rootSeq_succ hdiv t) 0 k
    rwa [Nat.zero_add] at this

variable (D : WeilDual A) (lam : Hom A D.dual)

/-- **`E^λ` has trivial left kernel (proved)**, given a quasi-inverse `ψ` of `λ` (`λψ = [d]`)
and the surjectivity of `T_ℓ A → A[ℓᵏ]`. -/
theorem tatePairing_left_ker {ψ : Hom D.dual A} {d : ℕ} (hd : 0 < d)
    (hψ : ∀ z : P D.dual, homP lam (homP ψ z) = d • z) (hℓ : (ℓ : K) ≠ 0)
    (hsurj : ∀ (k : ℕ) (t : P A), ℓ ^ k • t = 0 → ∃ y : A.T ℓ, y.1 k = t)
    (x : A.T ℓ) (hx : ∀ y, tatePairing D lam hℓ x y = 0) : x = 0 := by
  have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  -- `d • x_k = 0` for every `k`
  have hdk : ∀ k, d • x.1 k = 0 := by
    intro k
    have hkK : ((ℓ ^ k : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ
    have h := weil_nondeg D lam hψ (pow_pos hl k) hkK ⟨x.1 k, tors_pow ℓ k⟩ (fun t => by
      obtain ⟨y, hy⟩ := hsurj k t (nsmul_tors t)
      have h1 := congrArg (fun z : TMu K ℓ => z.1 k) (hx y)
      simp only [tatePairing_apply] at h1
      have h2 : wv D lam (ℓ ^ k) (x.1 k) (y.1 k) = 1 := Additive.ofMul.injective h1
      have h3 : (⟨y.1 k, tors_pow ℓ k⟩ : tors A (ℓ ^ k)) = t := Subtype.ext hy
      rw [wv_eq (tors_pow ℓ k) (tors_pow ℓ k), h3] at h2
      exact Mu.val_injective h2)
    exact congrArg Subtype.val h
  obtain ⟨a, d', hd', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' ℓ
    (Fact.out : ℓ.Prime).one_lt.ne'
  apply Subtype.ext; funext k
  have hcop : d'.Coprime (ℓ ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_comm.1 ((Fact.out : ℓ.Prime).coprime_iff_not_dvd.2 hd')))
  refine eq_zero_of_coprime hcop ?_ (tors_pow ℓ k)
  have h := hdk (k + a)
  rw [mul_comm, mul_smul, iterate_smul x.2.2 k a] at h
  exact h

/-- `det(f)² = c^{rank}` over a domain, for a bilinear form with nonzero Gram determinant. -/
theorem det_sq_of_similitude_domain {R M idx : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [Fintype idx] [DecidableEq idx] (b : Module.Basis idx R M)
    (B : LinearMap.BilinForm R M) (hB : (LinearMap.BilinForm.toMatrix b B).det ≠ 0)
    (f : M →ₗ[R] M) (c : R) (hf : ∀ x y, B (f x) (f y) = c * B x y) :
    LinearMap.det f ^ 2 = c ^ Fintype.card idx := by
  have hc : B.comp f f = c • B := by
    ext x y
    simp [hf]
  have h1 := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hc, map_smul] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix] at h2
  exact mul_left_cancel₀ hB (by linear_combination -h2)

/-- **G12 input on `V_ℓ A` (proved from the hypotheses).** Let `λ : A → Â` be symmetric with a
quasi-inverse (`λψ = [d]`), `ℓ` invertible in `K`, `T_ℓ A` free of finite rank (leaf
`PkgI3.TateModuleFree`), `T_ℓ A → A[ℓᵏ]` onto (from `DivisiblePoints`), and `iota : T_ℓ(μ) → ℤ_ℓ` an
injective `ℤ_ℓ`-linear map (glue target `TateMuEmbeds`). Then for every `σ ∈ G_K`,
`det ρ_ℓ(σ)² = χ_ℓ(σ)^{rank T_ℓ A}` on `V_ℓ A` (`= χ^{4}` for an abelian surface): C8 item 1. -/
theorem det_galRep_sq {ψ : Hom D.dual A} {d : ℕ} (hd : 0 < d)
    (hψ : ∀ z : P D.dual, homP lam (homP ψ z) = d • z) [NeZero (ℓ : K)]
    [Module.Free ℤ_[ℓ] (A.T ℓ)] [Module.Finite ℤ_[ℓ] (A.T ℓ)]
    (hsurj : ∀ (k : ℕ) (t : P A), ℓ ^ k • t = 0 → ∃ y : A.T ℓ, y.1 k = t)
    (iota : TMu K ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) (hiota : Function.Injective iota) (σ : Gal K) :
    LinearMap.det (A.galRep ℓ σ) ^ 2 =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) :
        ℤ_[ℓ]) ^ Module.finrank ℤ_[ℓ] (A.T ℓ) := by
  classical
  set hℓ : (ℓ : K) ≠ 0 := NeZero.ne _
  let B : LinearMap.BilinForm ℤ_[ℓ] (A.T ℓ) := (tatePairing D lam hℓ).compr₂ iota
  have hB : ∀ x y, B (A.galT σ x) (A.galT σ y) =
      ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * B x y := by
    intro x y
    simp only [B, LinearMap.compr₂_apply]
    rw [tatePairing_cyclotomic, map_smul, smul_eq_mul]
  have hsep : B.SeparatingLeft := by
    intro x hx
    exact tatePairing_left_ker D lam hd hψ hℓ hsurj x fun y => hiota (by
      rw [map_zero]; exact hx y)
  have hnd : B.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hnd
  have key := det_sq_of_similitude_domain b B hdet (A.galT σ) _ hB
  rw [← Module.finrank_eq_card_chooseBasisIndex] at key
  change LinearMap.det ((A.galT σ).baseChange ℚ_[ℓ]) ^ 2 = _
  rw [LinearMap.det_baseChange, ← map_pow, key, map_pow]

end Det


/-! ## §9. `T_ℓ(μ) ↪ ℤ_ℓ` (proved), and the G12 determinant input from leaves alone -/

section TMuEmbed

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- `K̄ˣ` is divisible. -/
lemma units_divisible {n : ℕ} (hn : 0 < n) (z : Additive (AlgebraicClosure K)ˣ) :
    ∃ w : Additive (AlgebraicClosure K)ˣ, n • w = z := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul z : (AlgebraicClosure K)ˣ) :
    AlgebraicClosure K) hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hw
    exact (Additive.toMul z).ne_zero hw.symm
  refine ⟨Additive.ofMul (Units.mk0 w hw0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  change ((Units.mk0 w hw0 ^ n : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = _
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, hw]

variable (K ℓ) in
/-- A generator of `T_ℓ(μ)`: a compatible system `(ζ_n)` with `ζ_n` of exact order `ℓⁿ`. -/
lemma exists_tmu_gen [NeZero (ℓ : K)] :
    ∃ g : TMu K ℓ, ∀ n, addOrderOf (g.1 n) = ℓ ^ n := by
  have hl1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure K) ℓ
  let u : (AlgebraicClosure K)ˣ := Units.mk0 ξ (hξ.ne_zero hl.ne')
  have ht : ℓ ^ 1 • Additive.ofMul u = 0 := by
    apply Additive.toMul.injective
    apply Units.ext
    change ((u ^ ℓ ^ 1 : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1
    rw [pow_one, Units.val_pow_eq_pow_val, Units.val_mk0, hξ.pow_eq_one]
  have ht0 : Additive.ofMul u ≠ 0 := by
    intro h
    have h' : (u : AlgebraicClosure K) = 1 := by
      rw [show u = 1 from Additive.ofMul.injective h, Units.val_one]
    exact hξ.ne_one hl1 h'
  obtain ⟨y, hy⟩ := tate_surj (units_divisible hl) 1 _ ht
  refine ⟨y, fun n => ?_⟩
  cases n with
  | zero => rw [y.2.1, addOrderOf_zero, pow_zero]
  | succ m =>
    refine addOrderOf_eq_prime_pow ?_ (Tate.pow_smul_eq_zero y.2 (m + 1))
    intro h
    have h1 := iterate_smul y.2.2 1 m
    rw [Nat.add_comm 1 m, h, hy] at h1
    exact ht0 h1.symm

/-- Discrete logarithms to a base of exact order `ℓⁿ` in `K̄ˣ`. -/
lemma exists_dlog {g w : Additive (AlgebraicClosure K)ˣ} {n : ℕ} (hg : addOrderOf g = ℓ ^ n)
    (hw : ℓ ^ n • w = 0) : ∃ c : ℕ, c • g = w := by
  have hord : orderOf (Additive.toMul g) = ℓ ^ n := (addOrderOf_ofMul_eq_orderOf _).symm.trans hg
  have h : IsPrimitiveRoot (Additive.toMul g) (ℓ ^ n) := IsPrimitiveRoot.iff_orderOf.2 hord
  have hw' : Additive.toMul w ∈ rootsOfUnity (ℓ ^ n) (AlgebraicClosure K) := by
    rw [mem_rootsOfUnity]
    exact Additive.ofMul.injective hw
  obtain ⟨i, -, hi⟩ := h.eq_pow_of_mem_rootsOfUnity hw'
  exact ⟨i, congrArg Additive.ofMul hi⟩

variable {g : TMu K ℓ} (hg : ∀ n, addOrderOf (g.1 n) = ℓ ^ n)

/-- `dlog z n`: the exponent `c` with `z_n = c · ζ_n`. -/
def dlog (z : TMu K ℓ) (n : ℕ) : ℕ :=
  Classical.choose (exists_dlog (hg n) (Tate.pow_smul_eq_zero z.2 n))

lemma dlog_spec (z : TMu K ℓ) (n : ℕ) : dlog hg z n • g.1 n = z.1 n :=
  Classical.choose_spec (exists_dlog (hg n) (Tate.pow_smul_eq_zero z.2 n))

include hg in
lemma modEq_of_smul_eq {n a b : ℕ} (h : a • g.1 n = b • g.1 n) : (a : ZMod (ℓ ^ n)) = b := by
  rw [ZMod.natCast_eq_natCast_iff, ← hg n]
  exact (nsmul_eq_nsmul_iff_modEq).1 h

lemma dlog_compat (z : TMu K ℓ) (n : ℕ) :
    ((ℓ : ℤ) ^ n) ∣ ((dlog hg z (n + 1) : ℕ) : ℤ) - ((dlog hg z n : ℕ) : ℤ) := by
  have h : dlog hg z (n + 1) • g.1 n = dlog hg z n • g.1 n := by
    calc dlog hg z (n + 1) • g.1 n = dlog hg z (n + 1) • (ℓ • g.1 (n + 1)) := by rw [g.2.2 n]
      _ = ℓ • (dlog hg z (n + 1) • g.1 (n + 1)) := smul_comm _ _ _
      _ = ℓ • z.1 (n + 1) := by rw [dlog_spec]
      _ = z.1 n := z.2.2 n
      _ = dlog hg z n • g.1 n := (dlog_spec hg z n).symm
  have h2 := modEq_of_smul_eq hg h
  rw [ZMod.natCast_eq_natCast_iff] at h2
  have h3 := (Nat.modEq_iff_dvd.1 h2.symm)
  simpa using h3

/-- The coordinate `T_ℓ(μ) → ℤ_ℓ`, `z ↦ lim dlog z n`. -/
def tmuCoord (z : TMu K ℓ) : ℤ_[ℓ] :=
  PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
    (fun n => ((dlog hg z n : ℕ) : ℤ)) ℓ (dlog_compat hg z))

lemma toZModPow_tmuCoord (z : TMu K ℓ) (n : ℕ) :
    PadicInt.toZModPow n (tmuCoord hg z) = (dlog hg z n : ZMod (ℓ ^ n)) := by
  unfold tmuCoord
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ _ (dlog_compat hg z)]
  simp

/-- **`T_ℓ(μ) ↪ ℤ_ℓ` (proved):** the coordinate is `ℤ_ℓ`-linear and injective. -/
def tmuCoordLin : TMu K ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ] where
  toFun := tmuCoord hg
  map_add' z z' := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    rw [map_add, toZModPow_tmuCoord, toZModPow_tmuCoord, toZModPow_tmuCoord, ← Nat.cast_add]
    apply modEq_of_smul_eq hg
    rw [add_smul, dlog_spec, dlog_spec, dlog_spec]
    rfl
  map_smul' a z := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    rw [RingHom.id_apply, smul_eq_mul, map_mul, toZModPow_tmuCoord, toZModPow_tmuCoord,
      ← ZMod.natCast_zmod_val (PadicInt.toZModPow n a), ← Nat.cast_mul]
    apply modEq_of_smul_eq hg
    rw [dlog_spec, mul_smul, dlog_spec]
    rfl

lemma tmuCoordLin_injective : Function.Injective (tmuCoordLin hg) := by
  intro z z' h
  apply Subtype.ext; funext n
  have h1 := congrArg (PadicInt.toZModPow n) h
  change PadicInt.toZModPow n (tmuCoord hg z) = PadicInt.toZModPow n (tmuCoord hg z') at h1
  rw [toZModPow_tmuCoord, toZModPow_tmuCoord, ZMod.natCast_eq_natCast_iff, ← hg n] at h1
  rw [← dlog_spec hg z n, ← dlog_spec hg z' n]
  exact (nsmul_eq_nsmul_iff_modEq).2 h1

end TMuEmbed

/-- **G12 determinant input (glue target, stated over Objects' `galRep`).** For an abelian
variety `A/K`, a prime `ℓ` invertible in `K` and `σ ∈ G_K`: `det ρ_ℓ(σ)² = χ_ℓ(σ)^{rank T_ℓ A}`
(`rank = 2g`). C8 item 1 in `det²` form (with `twist_finite_four`). -/
def G12_DetInput : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] (σ : Gal K),
    LinearMap.det (A.galRep ℓ σ) ^ 2 =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv :
        ℤ_[ℓ]ˣ) : ℤ_[ℓ]) ^ Module.finrank ℤ_[ℓ] (A.T ℓ)

/-- **The G12 input from four leaves (proved).** T9 (restated), the isogeny quasi-inverse, the
freeness of `T_ℓ A` (`PkgI3.TateModuleFree`, Objects) and the divisibility of `A(K̄)` imply
`G12_DetInput`. -/
theorem g12_detInput_of_leaves (h9 : T09_SymmIsogenyExists) (hQ : IsogenyQuasiInverse)
    (hT : PkgI3.TateModuleFree) (hD : DivisiblePoints) : G12_DetInput := by
  intro K _ A ℓ _ _ σ
  obtain ⟨S⟩ := h9 K A
  obtain ⟨d, hd, ψ, hψ, -⟩ := hQ K _ _ S.lam S.isogeny
  obtain ⟨hfree, hfin, -⟩ := hT K A ℓ (NeZero.ne _)
  obtain ⟨g, hg⟩ := exists_tmu_gen K ℓ
  exact det_galRep_sq S.D S.lam hd hψ
    (fun k t ht => tate_surj (hD K A ℓ (Fact.out : ℓ.Prime).pos) k t ht)
    (tmuCoordLin hg) (tmuCoordLin_injective hg) σ


end WeilPairing

end


section G12DetDetSec
noncomputable section
namespace G0Galois
open scoped Matrix

/-! ## The named pieces -/

/-- **Symplectic (Darboux) bases (GLUE, pure linear algebra; STANDARD: Bourbaki, Algèbre IX §5
no. 1, Artin, *Geometric algebra*, Thm 3.7; numbering UNVERIFIED).** A nondegenerate alternating
bilinear form on a space of dimension `2n` over a field has a basis, indexed by `Fin n ⊕ Fin n`,
in which its Gram matrix is Mathlib's `Matrix.J`. -/
def Darboux : Prop :=
  ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (n : ℕ), B.Nondegenerate → (∀ x, B x x = 0) →
    Module.finrank F V = 2 * n →
    ∃ b : Module.Basis (Fin n ⊕ Fin n) F V, LinearMap.BilinForm.toMatrix b B = Matrix.J (Fin n) F

/-- **Determinant of a symplectic similitude (GLUE, pure linear algebra; STANDARD: the Pfaffian
identity `Pf(MᵀGM) = det M · Pf G`, Bourbaki, Algèbre IX §5 no. 2; numbering UNVERIFIED).** If `f`
multiplies a nondegenerate alternating form on a `2n`-dimensional space by `c ≠ 0`, then
`det f = cⁿ`. Proved below from `Darboux` (`sympSimDet_of_darboux`). -/
def SympSimDet : Prop :=
  ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (f : V →ₗ[F] V) (c : F) (n : ℕ), B.Nondegenerate →
    (∀ x, B x x = 0) → Module.finrank F V = 2 * n → c ≠ 0 →
    (∀ x y, B (f x) (f y) = c * B x y) → LinearMap.det f = c ^ n

/-- **The `ℓ`-adic Weil pairing on `V_ℓ(A)` (GLUE; from T9 = Mumford §20, §23 and T26 =
Mumford §18-19, as restated in scratch/weil-pairing).** For an abelian variety `A` of dimension
`g` over a number field `K` and a prime `ℓ`: `V_ℓ(A)` has dimension `2g` and carries a
nondegenerate alternating `ℚ_ℓ`-bilinear form `B` with `B(σx, σy) = χ_ℓ(σ) B(x, y)` for
`σ ∈ G_K`, `χ_ℓ` the cyclotomic character of `G_K` on `K̄`. (`B = E^λ` for a polarization `λ`
over `K`, composed with a coordinate `T_ℓ(μ) ≅ ℤ_ℓ`.) scratch/weil-pairing proves, from the leaves
`T09_SymmIsogenyExists`, `IsogenyQuasiInverse`, `TateModuleFree`, `DivisiblePoints`, the
`ℤ_ℓ`-level pairing `tatePairing` on `T_ℓ A` (alternating `tatePairing_self`, multiplier
`tatePairing_cyclotomic`, trivial left kernel `tatePairing_left_ker`) and the coordinate
`tmuCoordLin`; what is left is the extension of scalars to `V_ℓ = ℚ_ℓ ⊗ T_ℓ` (nondegeneracy over
the fraction field from the trivial kernel on a free module of finite rank) and
`dim V_ℓ = rank T_ℓ = 2g` (T26). -/
def TateGSp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ),
    A.dim = g →
    ∃ (_ : FiniteDimensional ℚ_[ℓ] (A.V ℓ)) (B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ)),
      Module.finrank ℚ_[ℓ] (A.V ℓ) = 2 * g ∧ B.Nondegenerate ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Field.absoluteGaloisGroup K) (x y : A.V ℓ),
        B (A.galRep ℓ σ x) (A.galRep ℓ σ y) =
          (((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) :
            ℚ_[ℓ]) * B x y

/-! ## Proofs -/

/-- `Dᵀ J D = c⁻¹ J` for `D = diag(1, c⁻¹)`. -/
lemma J_conj_diag {F : Type*} [Field F] (n : ℕ) (c : F) :
    (Matrix.fromBlocks 1 0 0 (c⁻¹ • 1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
        Matrix.J (Fin n) F * Matrix.fromBlocks 1 0 0 (c⁻¹ • 1) = c⁻¹ • Matrix.J (Fin n) F := by
  simp [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]

/-- **`SympSimDet` from `Darboux`** (and Mathlib's `Matrix.symplecticGroup.det_eq_one`). -/
theorem sympSimDet_of_darboux (hD : Darboux) : SympSimDet := by
  intro F V _ _ _ _ B f c n hB halt hdim hc hf
  classical
  obtain ⟨b, hb⟩ := hD F V B n hB halt hdim
  set M := LinearMap.toMatrix b b f with hM
  have hcomp : B.comp f f = c • B := by
    ext x y
    simp [hf]
  have h1 := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hcomp, map_smul, hb] at h1
  -- `h1 : c • J = Mᵀ * J * M`
  set D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 1 0 0 (c⁻¹ • 1) with hDdef
  have hsymp : M * D ∈ Matrix.symplecticGroup (Fin n) F := by
    rw [SymplecticGroup.mem_iff']
    calc (M * D)ᵀ * Matrix.J (Fin n) F * (M * D)
        = Dᵀ * (Mᵀ * Matrix.J (Fin n) F * M) * D := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = c • (Dᵀ * Matrix.J (Fin n) F * D) := by
          rw [← h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = Matrix.J (Fin n) F := by
          rw [hDdef, J_conj_diag, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hdet1 := SymplecticGroup.det_eq_one hsymp
  have hDdet : D.det = c⁻¹ ^ n := by
    rw [hDdef, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin]
    ring
  rw [Matrix.det_mul, hDdet] at hdet1
  rw [← LinearMap.det_toMatrix b f, ← hM]
  have hcn : c ^ n ≠ 0 := pow_ne_zero n hc
  rw [inv_pow] at hdet1
  exact (mul_inv_eq_one₀ hcn).1 hdet1

/-- The cyclotomic characters of two fields agree on automorphisms intertwined by a ring
homomorphism (both fields containing all `ℓ`-power roots of unity). -/
lemma cyc_eq_of_intertwines {L L' : Type*} [Field L] [Field L'] (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ k, HasEnoughRootsOfUnity L (ℓ ^ k)] [∀ k, HasEnoughRootsOfUnity L' (ℓ ^ k)]
    (i : L →+* L') (g : L ≃+* L) (g' : L' ≃+* L') (h : ∀ x, i (g x) = g' (i x)) :
    cyclotomicCharacter L ℓ g = cyclotomicCharacter L' ℓ g' := by
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : Units.map i.toMonoidHom t ∈ rootsOfUnity (ℓ ^ n) L' := by
    rw [mem_rootsOfUnity] at ht ⊢
    rw [← map_pow, ht, map_one]
  have := modularCyclotomicCharacter.spec L'
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity L' (ℓ ^ n)) g' ht'
  apply i.injective
  rw [h, map_pow]
  simpa using this

/-- `χ_ℓ(resQ σ)` on `ℚ̄` is `χ_ℓ(σ)` on `K̄`. -/
lemma cycQ_resQ (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K) :
    cyclotomicCharacter PkgI4.Qbar ℓ (toRingEquivQ (resQ K σ)) =
      cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv :=
  cyc_eq_of_intertwines ℓ (qEmbRing K) _ _ (fun x => resQ_spec K σ x)

/-- **`DetTate` from `TateGSp` and `SympSimDet`.** -/
theorem detTate_of (hW : TateGSp) (hS : SympSimDet) : DetTate := by
  intro K _ _ A ℓ _ g hdim σ
  obtain ⟨hfd, B, hrank, hB, halt, hmult⟩ := hW K A ℓ g hdim
  set c : ℚ_[ℓ] := (((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) :
    ℤ_[ℓ]) : ℚ_[ℓ]) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, PadicInt.coe_ne_zero]
    exact Units.ne_zero _
  have hdet : LinearMap.det (A.galRep ℓ σ) = c ^ g :=
    hS ℚ_[ℓ] (A.V ℓ) B (A.galRep ℓ σ) c g hB halt hrank hc0 (hmult σ)
  change LinearMap.det ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ)) = _
  rw [LinearMap.det_baseChange, hdet, map_pow]
  congr 1
  simp only [cycQ, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, RingHom.coe_comp]
  rw [cycQ_resQ]
  rfl

/-- **`DetTate` from `TateGSp` and `Darboux`.** -/
theorem detTate_of_darboux (hW : TateGSp) (hD : Darboux) : DetTate :=
  detTate_of hW (sympSimDet_of_darboux hD)


/-! ## `Darboux`, proved (same proof as scratch/g12-det/Darboux.lean) -/

section DarbouxProof

open Module LinearMap LinearMap.BilinForm

variable {F : Type} [Field F]

lemma skew_of_alt {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (x y : V) : B y x = - B x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  linear_combination h

lemma isRefl_of_alt {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) : B.IsRefl := by
  intro x y h
  rw [skew_of_alt B halt x y, h, neg_zero]

/-- A family with Gram matrix `J` is linearly independent. -/
lemma linearIndependent_of_gram {V : Type} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (n : ℕ) (v : Fin n ⊕ Fin n → V)
    (hv : ∀ i j, B (v i) (v j) = Matrix.J (Fin n) F i j) : LinearIndependent F v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : Matrix.vecMul g (Matrix.J (Fin n) F) = 0 := by
    funext j
    have := congrArg (fun x => B x (v j)) hg
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_eq_mul,
      map_zero, LinearMap.zero_apply] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have h2 := congrArg (fun w => Matrix.vecMul w (Matrix.J (Fin n) F)) h1
  simp only [Matrix.vecMul_vecMul, Matrix.J_squared, Matrix.zero_vecMul] at h2
  intro i
  have := congrFun h2 i
  simpa [Matrix.vecMul_neg] using this

/-- The family version of Darboux, by induction. -/
lemma exists_gram_J : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V), B.Nondegenerate → (∀ x, B x x = 0) → finrank F V = 2 * n →
    ∃ v : Fin n ⊕ Fin n → V, ∀ i j, B (v i) (v j) = Matrix.J (Fin n) F i j := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ B _ _ _
    exact ⟨fun i => by rcases i with i | i <;> exact i.elim0, fun i => by
      rcases i with i | i <;> exact i.elim0⟩
  | succ n ih =>
    intro V _ _ _ B hB halt hdim
    have hrefl := isRefl_of_alt B halt
    have hpos : 0 < finrank F V := by rw [hdim]; omega
    haveI : Nontrivial V := Module.finrank_pos_iff.mp hpos
    obtain ⟨e, he⟩ := exists_ne (0 : V)
    have : ∃ y, B e y ≠ 0 := by
      by_contra h
      push Not at h
      exact he (hB.1 e h)
    obtain ⟨y, hy⟩ := this
    set f := (B e y)⁻¹ • y with hfdef
    have hef : B e f = 1 := by
      rw [hfdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
    have hfe : B f e = -1 := by rw [skew_of_alt B halt, hef]
    have hee : B e e = 0 := halt e
    have hff : B f f = 0 := halt f
    set H : Submodule F V := Submodule.span F {e, f} with hH
    set W : Submodule F V := B.orthogonal H with hW
    -- elements of `H`
    have hmemH : ∀ x ∈ H, ∃ a b : F, a • e + b • f = x := fun x hx =>
      Submodule.mem_span_pair.mp hx
    have heH : e ∈ H := Submodule.subset_span (by simp)
    have hfH : f ∈ H := Submodule.subset_span (by simp)
    -- `H ∩ H^⊥ = 0`
    have hdisj : Disjoint H W := by
      rw [Submodule.disjoint_def]
      intro x hx hxW
      obtain ⟨a, b, rfl⟩ := hmemH x hx
      have h1 : B e (a • e + b • f) = 0 := hxW e heH
      have h2 : B f (a • e + b • f) = 0 := hxW f hfH
      simp only [map_add, map_smul, smul_eq_mul, hee, hef, hfe, hff] at h1 h2
      have ha : a = 0 := by linear_combination -h2
      have hb : b = 0 := by linear_combination h1
      simp [ha, hb]
    have hcompl : IsCompl H W :=
      isCompl_orthogonal_of_restrict_nondegenerate hrefl
        (B.nondegenerate_restrict_of_disjoint_orthogonal hrefl hdisj)
    -- `finrank H = 2`
    have hli : LinearIndependent F ![e, f] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (B e) hst
      have h2 := congrArg (B f) hst
      simp only [map_add, map_smul, smul_eq_mul, hee, hef, hfe, hff, map_zero] at h1 h2
      constructor
      · linear_combination -h2
      · linear_combination h1
    have hH2 : finrank F H = 2 := by
      have := finrank_span_eq_card hli
      rw [Matrix.range_cons_cons_empty, Fintype.card_fin] at this
      exact this
    have hW2 : finrank F W = 2 * n := by
      rw [hW, finrank_orthogonal hB, hdim, hH2]; omega
    -- the restriction to `W` is nondegenerate and alternating
    have hBW : (B.restrict W).Nondegenerate := by
      have hsplit : ∀ z : V, ∃ h ∈ H, ∃ w ∈ W, h + w = z := fun z =>
        Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top)
      constructor
      · intro m hm
        apply Subtype.ext
        apply hB.1
        intro z
        obtain ⟨h, hh, w, hw, rfl⟩ := hsplit z
        rw [map_add, hrefl _ _ (m.2 h hh)]
        have := hm ⟨w, hw⟩
        simpa using this
      · intro m hm
        apply Subtype.ext
        apply hB.2
        intro z
        obtain ⟨h, hh, w, hw, rfl⟩ := hsplit z
        rw [LinearMap.map_add₂, m.2 h hh]
        have := hm ⟨w, hw⟩
        simpa using this
    have haltW : ∀ x, B.restrict W x x = 0 := fun x => halt x
    obtain ⟨w, hw⟩ := ih W (B.restrict W) hBW haltW hW2
    have hfw : ∀ x : W, B f x = 0 := fun x => x.2 f hfH
    have hew : ∀ x : W, B e x = 0 := fun x => x.2 e heH
    have hwf : ∀ x : W, B x f = 0 := fun x => hrefl _ _ (hfw x)
    have hwe : ∀ x : W, B x e = 0 := fun x => hrefl _ _ (hew x)
    have hww : ∀ i j, B (w i) (w j) = Matrix.J (Fin n) F i j := hw
    let v : Fin (n + 1) ⊕ Fin (n + 1) → V :=
      Sum.elim (Fin.cons f fun j => (w (Sum.inl j) : V))
        (Fin.cons e fun j => (w (Sum.inr j) : V))
    refine ⟨v, ?_⟩
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [v, Matrix.J, hef, hfe, hee, hff, hfw, hew, hwf, hwe, hww, Matrix.one_apply,
        Fin.succ_ne_zero, Fin.succ_inj]
    all_goals exact (Fin.succ_ne_zero _).symm

/-- **`Darboux`, proved.** -/
theorem darboux : Darboux := by
  intro F V _ _ _ _ B n hB halt hdim
  classical
  obtain ⟨v, hv⟩ := exists_gram_J n V B hB halt hdim
  have hli := linearIndependent_of_gram B n v hv
  have hcard : Fintype.card (Fin n ⊕ Fin n) = finrank F V := by
    rw [Fintype.card_sum, Fintype.card_fin, hdim]; ring
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hli hcard, ?_⟩
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.BilinForm.toMatrix_apply, coe_basisOfLinearIndependentOfCardEqFinrank', hv]

end DarbouxProof

/-- **`DetTate` from `TateGSp` alone** (`Darboux` and `SympSimDet` are proved). -/
theorem detTate_of_tateGSp (hW : TateGSp) : DetTate :=
  detTate_of_darboux hW darboux


/-! ## `TateGSp` from the `ℤ_ℓ`-level Weil pairing (scratch/weil-pairing) and T26 -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **The `ℓ`-adic Weil pairing on `T_ℓ(A)`, `ℤ_ℓ`-valued (GLUE, proved in scratch/weil-pairing
from leaves, up to restatement).** There is an alternating `ℤ_ℓ`-bilinear form on `T_ℓ(A)` with
trivial left kernel and multiplier the cyclotomic character of `G_K` on `K̄`. In
scratch/weil-pairing this is `B = (tatePairing D lam hℓ).compr₂ (tmuCoordLin hg)` for a
polarization `S.lam` (leaf `T09_SymmIsogenyExists`), with `tatePairing_self` (alternating),
`tatePairing_cyclotomic` (multiplier), and `tatePairing_left_ker` + `tmuCoordLin_injective`
(trivial left kernel; leaves `IsogenyQuasiInverse`, `DivisiblePoints`), exactly as in the proof
of `det_galRep_sq` / `g12_detInput_of_leaves` there (VERIFIED by reading WeilPairing.lean
L969-1148). The statement below is not compiled against that file (scratch files cannot import
each other); its `B` is theirs. -/
def TatePairingZl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ B : LinearMap.BilinForm ℤ_[ℓ] (A.T ℓ), B.SeparatingLeft ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Field.absoluteGaloisGroup K) (x y : A.T ℓ),
        B (A.galT σ x) (A.galT σ y) =
          ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * B x y

lemma skew_of_alt' {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (B : LinearMap.BilinForm R V) (halt : ∀ x, B x x = 0) (x y : V) : B y x = - B x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  linear_combination h

/-- **`TateGSp` from `TatePairingZl` and T26 (`PkgI3.TateModuleFree`, leaf I3 of Objects).** The
form on `V_ℓ = ℚ_ℓ ⊗ T_ℓ` is the one with the same Gram matrix in the base-changed basis. -/
theorem tateGSp_of_zl (hZ : TatePairingZl) (hT : PkgI3.TateModuleFree) : TateGSp := by
  intro K _ _ A ℓ _ g hdim
  classical
  obtain ⟨B0, hsep, halt0, hmult⟩ := hZ K A ℓ
  have hℓ : (ℓ : K) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfree, hfin, hrk⟩ := hT K A ℓ hℓ
  have hrank : Module.finrank ℤ_[ℓ] (A.T ℓ) = 2 * g := by
    rw [hdim] at hrk
    have h3 : (((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((2 * g : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [hrk]; push_cast; rfl
    exact_mod_cast WithBot.coe_injective h3
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  let bV : Module.Basis _ ℚ_[ℓ] (A.V ℓ) := Algebra.TensorProduct.basis ℚ_[ℓ] b
  have hnd0 : B0.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  have hdet0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hnd0
  set G := LinearMap.BilinForm.toMatrix b B0 with hG
  let φ := algebraMap ℤ_[ℓ] ℚ_[ℓ]
  have hφ : Function.Injective φ := IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
  set G' := G.map φ with hG'
  let B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) := Matrix.toBilin bV G'
  have hBG : LinearMap.BilinForm.toMatrix bV B = G' := LinearMap.BilinForm.toMatrix_toBilin _ _
  haveI : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := Module.Finite.of_basis bV
  refine ⟨inferInstance, B, ?_, ?_, ?_, ?_⟩
  · rw [Module.finrank_baseChange, hrank]
  · rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bV, hBG, hG', show G.map φ = φ.mapMatrix G from rfl, ← RingHom.map_det]
    exact fun h => hdet0 (hφ (by rw [h, map_zero]))
  · -- alternating: the Gram matrix is alternating, and `2 ≠ 0`
    have hskew : ∀ i j, G' j i = - G' i j := by
      intro i j
      simp only [hG', hG, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply]
      rw [skew_of_alt' B0 halt0, map_neg]
    intro x
    have hsum : B x x = ∑ i, ∑ j, bV.repr x i * G' i j * bV.repr x j := Matrix.toBilin_apply bV G' x x
    have hsum' : B x x = - B x x := by
      conv_rhs => rw [hsum, Finset.sum_comm]
      rw [hsum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hskew j i]
      ring
    have h2 : (2 : ℚ_[ℓ]) * B x x = 0 := by linear_combination hsum'
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  · intro σ
    set c0 := ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ])
    have hc0 : B0.comp (A.galT σ) (A.galT σ) = c0 • B0 := by
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      change B0 (A.galT σ x) (A.galT σ y) = c0 * B0 x y
      rw [hmult σ x y]
    set M := LinearMap.toMatrix b b (A.galT σ) with hM
    have h1 := LinearMap.BilinForm.toMatrix_comp b b B0 (A.galT σ) (A.galT σ)
    rw [hc0, map_smul] at h1
    -- `h1 : c0 • G = Mᵀ * G * M`
    have hfM : LinearMap.toMatrix bV bV (A.galRep ℓ σ) = M.map φ :=
      LinearMap.toMatrix_baseChange ℚ_[ℓ] (A.galT σ) b b
    have hcomp : B.comp (A.galRep ℓ σ) (A.galRep ℓ σ) = (φ c0) • B := by
      apply (LinearMap.BilinForm.toMatrix bV).injective
      rw [LinearMap.BilinForm.toMatrix_comp bV bV, hfM, hBG, map_smul, hBG, hG']
      have h2 := congrArg (fun X => X.map φ) h1
      simp only [Matrix.map_mul, Matrix.transpose_map] at h2
      rw [← hG] at h2
      exact h2.symm
    intro x y
    have := congrArg (fun C : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) => C x y) hcomp
    simpa [φ] using this

/-- **`DetTate` from the `ℤ_ℓ`-level Weil pairing and T26.** -/
theorem detTate_of_zl (hZ : TatePairingZl) (hT : PkgI3.TateModuleFree) : DetTate :=
  detTate_of_tateGSp (tateGSp_of_zl hZ hT)

end G0Galois
end
end G12DetDetSec


/-! ## Part 3: `TatePairingZl` from the leaves of scratch/weil-pairing -/

namespace G0Galois

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **`TatePairingZl` from T9 (restated), the isogeny quasi-inverse and divisibility** (as in
weil-pairing's `det_galRep_sq` / `g12_detInput_of_leaves`). -/
theorem tatePairingZl_of_leaves (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hD : WeilPairing.DivisiblePoints) : TatePairingZl := by
  intro K _ _ A ℓ _
  haveI : NeZero (ℓ : K) := ⟨by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨S⟩ := h9 K A
  obtain ⟨d, hd, ψ, hψ, -⟩ := hQ K _ _ S.lam S.isogeny
  obtain ⟨g, hg⟩ := WeilPairing.exists_tmu_gen K ℓ
  refine ⟨(WeilPairing.tatePairing S.D S.lam (NeZero.ne _)).compr₂ (WeilPairing.tmuCoordLin hg),
    ?_, ?_, ?_⟩
  · intro x hx
    exact WeilPairing.tatePairing_left_ker S.D S.lam hd hψ (NeZero.ne _)
      (fun k t ht => WeilPairing.tate_surj (hD K A ℓ (Fact.out : ℓ.Prime).pos) k t ht) x
      fun y => WeilPairing.tmuCoordLin_injective hg (by rw [map_zero]; exact hx y)
  · intro x
    simp only [LinearMap.compr₂_apply]
    rw [WeilPairing.tatePairing_self S.D S.lam S.symm (NeZero.ne _) x, map_zero]
  · intro σ x y
    simp only [LinearMap.compr₂_apply]
    have h := congrArg (WeilPairing.tmuCoordLin hg)
      (WeilPairing.tatePairing_cyclotomic S.D S.lam σ x y)
    rw [map_smul, smul_eq_mul] at h
    exact h

/-- **`DetTate` from leaves**: T9 restated (`T09_SymmIsogenyExists`), `IsogenyQuasiInverse`,
`DivisiblePoints` (scratch/weil-pairing §4, §8) and T26 (`PkgI3.TateModuleFree`, Objects). -/
theorem detTate_of_leaves (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hD : WeilPairing.DivisiblePoints)
    (hT : PkgI3.TateModuleFree) : DetTate :=
  detTate_of_zl (tatePairingZl_of_leaves h9 hQ hD) hT

end G0Galois



section G12DetWeightSec
namespace G0Galois
open PkgI4 (GaloisRep GaloisChar)

/-! ### Named pieces -/

/-- `ρ'` is the twist `ψ ⊗ ρ`: `ρ'(σ) = ψ(σ) ρ(σ)`. -/
def IsTwist {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ' : GaloisRep ℓ n) (ψ : GaloisChar ℓ)
    (ρ : GaloisRep ℓ n) : Prop :=
  ∀ σ, ρ'.mat σ = (ψ.toHom σ : PadicAlgCl ℓ) • ρ.mat σ

/-- `r` and `ρ'` are conjugate by a fixed matrix: `r(σ) = P ρ'(σ) P⁻¹`. -/
def IsConj {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r ρ' : GaloisRep ℓ n) : Prop :=
  ∃ P : GL (Fin n) (PadicAlgCl ℓ), ∀ σ, r.toHom σ = P * ρ'.toHom σ * P⁻¹

/-- **The twist exists (GLUE, elementary).** `σ ↦ ψ(σ) ρ(σ)` is a continuous representation:
a homomorphism because scalars are central, continuous because `GL_n(ℚ̄_ℓ)` carries the topology
induced from `M_n × M_nᵐᵒᵖ` and `ψ`, `ψ⁻¹`, `ρ`, `ρ⁻¹` are continuous. -/
def TwistExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (ρ : GaloisRep ℓ n) (ψ : GaloisChar ℓ),
    ∃ ρ' : GaloisRep ℓ n, IsTwist ρ' ψ ρ

/-- **`r ≅ ψ ⊗ ρ_g` (GLUE, from T18 Chebotarev and T19 Brauer–Nesbitt).** If `r` is
irreducible, `ρ` semisimple and attached to `g`, `r` attached to `g` up to the twist `ψ` outside
`S`, and `ρ' = ψ ⊗ ρ`, then `r` and `ρ'` are conjugate. Argument (as in `g12Det_of`,
scratch/g0-mod-galois): `tr r = tr ρ'` at arithmetic Frobenius outside `S ∪ {p ∣ 5N}` (`ιC`
injective identifies the two `α`), hence everywhere (`eq_of_eq_on_arithFrob`, T18); `r` is
semisimple (Burnside-irreducible: an invariant subspace is invariant under `M₂(ℚ̄₅)`), `ρ'` is
semisimple (same invariant subspaces as `ρ`); Brauer–Nesbitt (T19, `G = G_ℚ`, `E = ℚ̄₅`). -/
def TwistConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (r ρ ρ' : GaloisRep ℓ 2) (ψ : GaloisChar ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (k : ℤ)
    (g : PkgI4.CF N k) (S : Finset ℕ),
    0 < N → r.IsIrreducible → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    r.AttachedUpToTwist ψ ιC ιL g S → IsTwist ρ' ψ ρ → IsConj r ρ'

/-- **Hodge–Tate weights are invariant under conjugation (GLUE, about the definition
`PkgI4.LocalHasHTWeights`; STANDARD).** Enlarge the finite coefficient field `E` to contain the
entries of `P` and `P⁻¹` and use that `htMult` does not change under a finite extension of `E`
(`(ℂ_p(i) ⊗ V)^G` commutes with `E'/E` base change) nor under an `E'`-linear isomorphism. -/
def HTConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (r ρ' : GaloisRep ℓ n) (S : Multiset ℤ),
    IsConj r ρ' → r.HasHTWeightsAtSelf ℓ S → ρ'.HasHTWeightsAtSelf ℓ S

/-- **Sen weights of a twist (LEAF; Sen, *Continuous cohomology and p-adic Galois
representations*, Invent. Math. 62 (1980), §2 Thm 4 and Cor. (Hodge–Tate iff the Sen operator `Θ`
is semisimple with integer eigenvalues, the Hodge–Tate weights), with
`Θ_{ψ⊗V} = Θ_ψ + Θ_V` (Sen 1980 §2; Fontaine–Ouyang, *Theory of p-adic Galois representations*,
§2.4-2.5); numbering UNVERIFIED).** If `ρ` and `ρ' = ψ ⊗ ρ` (restricted to `G_{ℚ_p}`) are both
Hodge–Tate, with weight multisets `S`, `S'` of full size `n`, then `S' = S + s` for an integer
`s`. Consequence of the published theorems: the Sen operators satisfy `Θ_{ρ'} = Θ_ρ + s_ψ`, both
are semisimple with eigenvalue multisets `S`, `S'`, so `S' = S + s_ψ` in `ℂ_p`, and `s_ψ ∈ ℤ`
when `n ≥ 1` (for `n = 0`, `s = 0`). (Full size is needed: `HasHTWeights S` with `card S < n`
holds for non-Hodge–Tate `ρ`, and then the statement fails.) -/
def SenTwist : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ ρ' : GaloisRep p n) (ψ : GaloisChar p)
    (S S' : Multiset ℤ),
    IsTwist ρ' ψ ρ → Multiset.card S = n → Multiset.card S' = n →
    ρ.HasHTWeightsAtSelf p S → ρ'.HasHTWeightsAtSelf p S' →
    ∃ s : ℤ, S' = S.map (· + s)

/-- **Finite image implies Hodge–Tate of weight 0 (LEAF; Tate, *p-divisible groups* (1967) §3
Thm 2 (`ℂ_p(i)^{G_L} = 0` for `i ≠ 0`) and Ax–Sen–Tate (`ℂ_p^{G_L} = L`), with Hilbert 90 for
the finite extension cut out by the image; Fontaine–Ouyang Prop. 2.15 / Sen 1980 Cor. of Thm 11;
numbering UNVERIFIED).** A representation of `G_ℚ` with finite image is Hodge–Tate at `p` with all
weights `0` (its image lies in `GL_n(E)` for a finite `E/ℚ_p`: finitely many algebraic entries).
-/
def FiniteImageHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GaloisRep p n),
    (Set.range ρ.toHom).Finite → ρ.HasHTWeightsAtSelf p (Multiset.replicate n 0)

/-! ### Proof -/

/-- The conclusion of `G12Weight` is `k = 2` (for `k ≥ 1`). -/
theorem g12Weight_concl_iff (k : ℤ) (hk : 1 ≤ k) :
    (∃ n : ℤ, ({n, n + 1 - k} : Multiset ℤ) = {0, -1}) ↔ k = 2 := by
  constructor
  · rintro ⟨n, hn⟩
    have h0 : (0 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [hn]; simp
    have h1 : (-1 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [hn]; simp
    have hc : ((n + 1 - k : ℤ) ∈ ({0, -1} : Multiset ℤ)) := by rw [← hn]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1 hc
    omega
  · rintro rfl
    exact ⟨0, by norm_num⟩

/-- **`G12Weight` from the named pieces** (and the leaves R14, R13, R15 it takes). -/
theorem g12Weight_of (hTE : TwistExists) (hTC : TwistConj) (hHC : HTConj) (hSen : SenTwist)
    (hFI : FiniteImageHT) : G12Weight := by
  intro hR hHT hDS _hFD _hBN r N k χ g ψ ιC ιL S hN hk hg hirr hw hatt
  obtain ⟨ρH, hss, hρatt⟩ := hR 5 ιC ιL N k χ g hN hk hg
  let ρ : GaloisRep 5 2 := ⟨ρH.toHom, ρH.continuous_toHom⟩
  have hss' : ρ.IsSemisimple := hss
  have hatt' : ρ.AttachedTo ιC ιL g := hρatt
  obtain ⟨ρ', htw⟩ := hTE 5 2 ρ ψ
  have hconj : IsConj r ρ' := hTC 5 r ρ ρ' ψ ιC ιL N k g S hN hirr hss' hatt' hatt htw
  have hw' : ρ'.HasHTWeightsAtSelf 5 {0, -1} := hHC 5 2 r ρ' _ hconj hw
  rcases eq_or_lt_of_le hk with h1 | h2
  · -- weight one: `ρ_g` has finite image, so `ψ ⊗ ρ_g` would have equal weights
    exfalso
    subst h1
    have hfin : (Set.range ρH.toHom).Finite := hDS 5 ιC ιL ρH N χ g hN hg hss hρatt
    have h0 : ρ.HasHTWeightsAtSelf 5 (Multiset.replicate 2 0) := hFI 5 2 ρ hfin
    obtain ⟨s, hs⟩ := hSen 5 2 ρ ρ' ψ _ _ htw (by simp) (by simp) h0 hw'
    have ha : (0 : ℤ) ∈ ({0, -1} : Multiset ℤ) := by simp
    have hb : (-1 : ℤ) ∈ ({0, -1} : Multiset ℤ) := by simp
    rw [hs] at ha hb
    simp only [Multiset.mem_map, Multiset.mem_replicate] at ha hb
    obtain ⟨a, ⟨-, rfl⟩, ha⟩ := ha
    obtain ⟨b, ⟨-, rfl⟩, hb⟩ := hb
    omega
  · -- weight `k ≥ 2`: weights `{0, 1 − k} + s = {0, −1}`
    have h := hHT 5 ιC ιL N k χ g ρ hN (by omega) hg hss' hatt'
    obtain ⟨s, hs⟩ := hSen 5 2 ρ ρ' ψ _ _ htw (by simp) (by simp) h hw'
    refine ⟨s, ?_⟩
    rw [hs]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    congr 1
    · ring
    · congr 1; ring

end G0Galois
end G12DetWeightSec


section G12DetTwistSec
noncomputable section
namespace G0Galois
open PkgI4 (GaloisRep GaloisChar)

/-! ### `TwistExists` -/

/-- Scalar matrices as units. -/
def scalarU {ℓ : ℕ} [Fact ℓ.Prime] (n : ℕ) : (PadicAlgCl ℓ)ˣ →* GL (Fin n) (PadicAlgCl ℓ) :=
  Units.map (Matrix.scalar (Fin n) : PadicAlgCl ℓ →+* Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))

lemma scalarU_commute {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (u : (PadicAlgCl ℓ)ˣ)
    (M : GL (Fin n) (PadicAlgCl ℓ)) : Commute (scalarU n u) M := by
  apply Units.ext
  simp only [Units.val_mul, scalarU, Units.coe_map, MonoidHom.coe_coe]
  exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _

/-- `σ ↦ ψ(σ) ρ(σ)`. -/
def twistHom {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ : GaloisRep ℓ n) (ψ : GaloisChar ℓ) :
    PkgI4.GQ →* GL (Fin n) (PadicAlgCl ℓ) where
  toFun σ := scalarU n (ψ.toHom σ) * ρ.toHom σ
  map_one' := by simp
  map_mul' σ τ := by
    simp only [map_mul, mul_assoc]
    congr 1
    rw [← mul_assoc, (scalarU_commute (ψ.toHom τ) (ρ.toHom σ)).eq, mul_assoc]

lemma twistHom_val {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ : GaloisRep ℓ n) (ψ : GaloisChar ℓ)
    (σ : PkgI4.GQ) :
    ((twistHom ρ ψ σ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) =
      (ψ.toHom σ : PadicAlgCl ℓ) • ρ.mat σ := by
  change ((scalarU n (ψ.toHom σ) * ρ.toHom σ : GL (Fin n) (PadicAlgCl ℓ)) :
    Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) = _
  rw [Units.val_mul]
  simp only [scalarU, Units.coe_map, MonoidHom.coe_coe, Matrix.scalar_apply,
    PkgI4.GaloisRep.mat]
  rw [Matrix.smul_eq_diagonal_mul]

/-- **`TwistExists`, proved.** -/
theorem twistExists : TwistExists := by
  intro ℓ _ n ρ ψ
  have hv : Continuous fun σ =>
      ((twistHom ρ ψ σ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := by
    simp only [twistHom_val]
    exact (Units.continuous_val.comp ψ.continuous_toHom).smul (continuous_mat ρ)
  refine ⟨⟨twistHom ρ ψ, Units.continuous_iff.mpr ⟨hv, ?_⟩⟩, fun σ => twistHom_val ρ ψ σ⟩
  have : (fun σ => (((twistHom ρ ψ σ)⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) :
      Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) =
      (fun σ => ((twistHom ρ ψ σ : GL (Fin n) (PadicAlgCl ℓ)) :
        Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ∘ (fun σ => σ⁻¹) := by
    funext σ; simp [map_inv]
  rw [this]
  exact hv.comp continuous_inv

/-! ### `TwistConj` from T18 and T19 -/

/-- Invariance under all matrices of an algebra generated by the image. -/
lemma invariant_of_irreducible {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r : GaloisRep ℓ n)
    (hirr : r.IsIrreducible) (W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ))
    (hW : ∀ σ, W.map (Matrix.toLin' (r.mat σ)) ≤ W) :
    ∀ M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ), ∀ x ∈ W, M.mulVec x ∈ W := by
  let S : Subalgebra (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) :=
    { carrier := {M | ∀ x ∈ W, M.mulVec x ∈ W}
      mul_mem' := by
        intro a b ha hb x hx
        rw [← Matrix.mulVec_mulVec]
        exact ha _ (hb x hx)
      add_mem' := by
        intro a b ha hb x hx
        rw [Matrix.add_mulVec]
        exact W.add_mem (ha x hx) (hb x hx)
      algebraMap_mem' := by
        intro c x hx
        rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact W.smul_mem c hx }
  have hle : Algebra.adjoin (PadicAlgCl ℓ) (Set.range r.mat) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨σ, rfl⟩ x hx
    exact hW σ ⟨x, hx, rfl⟩
  intro M x hx
  have hM : M ∈ S := hle (hirr ▸ Algebra.mem_top)
  exact hM x hx

/-- An irreducible (Burnside form) representation is semisimple. -/
lemma isSemisimple_of_irreducible {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r : GaloisRep ℓ n)
    (hirr : r.IsIrreducible) : r.IsSemisimple := by
  intro W hW
  have hinv := invariant_of_irreducible r hirr W hW
  by_cases h : W = ⊥
  · subst h
    exact ⟨⊤, isCompl_bot_top, fun σ => le_top⟩
  · have htop : W = ⊤ := by
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hw0 (funext hc)
      rw [eq_top_iff]
      intro v _
      let M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) :=
        Matrix.of fun a b => if b = i then v a / w i else 0
      have hMw : M.mulVec w = v := by
        funext a
        simp [M, Matrix.mulVec, dotProduct, div_mul_cancel₀ _ hi]
      rw [← hMw]
      exact hinv M w hw
    subst htop
    exact ⟨⊥, isCompl_top_bot, fun σ => by simp⟩

/-- A twist of a semisimple representation by a character is semisimple. -/
lemma isSemisimple_twist {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ ρ' : GaloisRep ℓ n) (ψ : GaloisChar ℓ)
    (hss : ρ.IsSemisimple) (htw : IsTwist ρ' ψ ρ) : ρ'.IsSemisimple := by
  have key : ∀ (W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ)) σ,
      W.map (Matrix.toLin' (ρ'.mat σ)) ≤ W ↔ W.map (Matrix.toLin' (ρ.mat σ)) ≤ W := by
    intro W σ
    have hu : (ψ.toHom σ : PadicAlgCl ℓ) ≠ 0 := Units.ne_zero _
    simp only [Submodule.map_le_iff_le_comap, htw σ]
    constructor
    · intro h x hx
      have := W.smul_mem ((ψ.toHom σ : PadicAlgCl ℓ))⁻¹ (h hx)
      simpa [Matrix.toLin'_apply, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hu] using this
    · intro h x hx
      have := W.smul_mem ((ψ.toHom σ : PadicAlgCl ℓ)) (h hx)
      simpa [Matrix.toLin'_apply, Matrix.smul_mulVec] using this
  intro W hW
  obtain ⟨W', hc, hW'⟩ := hss W (fun σ => (key W σ).1 (hW σ))
  exact ⟨W', hc, fun σ => (key W' σ).2 (hW' σ)⟩

/-- **`TwistConj` from T18 (Chebotarev) and T19 (Brauer–Nesbitt), proved.** -/
theorem twistConj_of (hD : HSyn.FrobeniusDense) (hBN : HSyn.BrauerNesbitt) : TwistConj := by
  intro ℓ _ r ρ ρ' ψ ιC ιL N k g S hN hirr hss hρatt hatt htw
  have hNl : N * ℓ ≠ 0 := Nat.mul_ne_zero (by omega) (Fact.out : ℓ.Prime).ne_zero
  have htr : ∀ x, (r.mat x).trace = (ρ'.mat x).trace := by
    have h := eq_of_eq_on_arithFrob (frobeniusDenseQ_of hD) (S ∪ (N * ℓ).primeFactors)
      (fun x => (r.mat x).trace) (fun x => (ρ'.mat x).trace)
      (continuous_mat r).matrix_trace (continuous_mat ρ').matrix_trace
      (by
        intro p hp hpS v τ hv hτ
        have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
        have hpN : ¬ p ∣ N * ℓ := fun h =>
          hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hNl⟩))
        obtain ⟨-, α, hα, hαt⟩ := hatt p hp hpS1
        obtain ⟨-, α', hα', hα't⟩ := hρatt p hp hpN
        have hαα : α = α' := ιC.toRingHom.injective (hα.trans hα'.symm)
        rw [hαt v τ hv hτ, htw τ, Matrix.trace_smul, hα't v τ hv hτ, hαα, smul_eq_mul])
    exact fun x => congrFun h x
  have hss' : ρ'.IsSemisimple := isSemisimple_twist ρ ρ' ψ hss htw
  have hssr : r.IsSemisimple := isSemisimple_of_irreducible r hirr
  obtain ⟨P, hP⟩ := hBN PkgI4.GQ (PadicAlgCl ℓ) 2 ρ'.toHom r.toHom hss' hssr
    (fun σ => (htr σ).symm)
  exact ⟨P, hP⟩

/-- **`G12Weight` from `HTConj`, `SenTwist`, `FiniteImageHT`** (`TwistExists` proved; `TwistConj`
from the T18 and T19 that `G12Weight` itself takes). -/
theorem g12Weight_of_HT (hHC : HTConj) (hSen : SenTwist) (hFI : FiniteImageHT) : G12Weight := by
  intro hR hHT hDS hFD hBN
  exact g12Weight_of twistExists (twistConj_of hFD hBN) hHC hSen hFI hR hHT hDS hFD hBN

end G0Galois
end
end G12DetTwistSec


/-! ## g12-det: `HTConj` reduced to `HTExtend` (independence of the coefficient field) -/

section G12DetHTSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- **Hodge–Tate multiplicities do not depend on the finite coefficient field (GLUE, about the
definition `PkgI4.LocalHasHTWeights`; STANDARD).** If a `ℚ̄_p`-valued `ρ` has a model `ρ_E` over a
finite `E ⊆ ℚ̄_p` with weights `S`, then for every finite `E' ⊇ E` the model over `E'` (the same
matrices) has weights `S`. Argument: `E' ⊗_E E^n ≅ (E^n)^{[E':E]}` as `ℚ_p[G]`-modules (`G` acts
trivially on `E'`), so `dim_{ℚ_p} H_i(ρ_{E'}) = [E':E] dim_{ℚ_p} H_i(ρ_E)` and `htMult`, which divides
by `[E':ℚ_p]`, is unchanged. (The docstring of `LocalHasHTWeights` asserts this, STANDARD.) -/
def HTExtend : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : PkgI4.GQp p →* GL (Fin n) (PadicAlgCl p))
    (S : Multiset ℤ) (E E' : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'], E ≤ E' →
    ∀ ρE : PkgI4.GQp p →* GL (Fin n) E,
      (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) →
      PkgI4.HasHTWeights p ρE S →
      ∃ ρE' : PkgI4.GQp p →* GL (Fin n) E',
        (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E' (PadicAlgCl p)) (ρE' σ) = ρ σ) ∧
        PkgI4.HasHTWeights p ρE' S

/-- Conjugating a model by `P ∈ GL_n(E)` does not change the Hodge–Tate spaces' dimensions. -/
lemma finrank_htSpace_conj {p : ℕ} [Fact p.Prime] {n : ℕ} {E : Type*} [Field E]
    [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (ρ ρ' : PkgI4.GQp p →* GL (Fin n) E) (P : GL (Fin n) E)
    (h : ∀ σ, ρ' σ = P⁻¹ * ρ σ * P) (i : ℤ) :
    Module.finrank ℚ_[p] (PkgI4.htSpace p ρ' i) = Module.finrank ℚ_[p] (PkgI4.htSpace p ρ i) := by
  let A : Matrix (Fin n) (Fin n) E := (P : Matrix (Fin n) (Fin n) E)
  let B : Matrix (Fin n) (Fin n) E := ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
  have hAB : A * B = 1 := by simp [A, B]
  have hBA : B * A = 1 := by simp [A, B]
  have hρ' : ∀ σ, ((ρ' σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      B * (ρ σ : Matrix (Fin n) (Fin n) E) * A := by
    intro σ; rw [h σ]; simp [A, B]
  let LA : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E) := (Matrix.mulVecLin A).restrictScalars ℚ_[p]
  let LB : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E) := (Matrix.mulVecLin B).restrictScalars ℚ_[p]
  let TA := LinearMap.lcomp ℚ_[p] ℂ_[p] LA
  let TB := LinearMap.lcomp ℚ_[p] ℂ_[p] LB
  have hTA : ∀ φ ∈ PkgI4.htSpace p ρ i, TA φ ∈ PkgI4.htSpace p ρ' i := by
    intro φ hφ σ v
    have := hφ σ (A.mulVec v)
    simp only [TA, LA, LinearMap.lcomp_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at this ⊢
    rw [hρ', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
    exact this
  have hTB : ∀ φ ∈ PkgI4.htSpace p ρ' i, TB φ ∈ PkgI4.htSpace p ρ i := by
    intro φ hφ σ v
    have := hφ σ (B.mulVec v)
    simp only [TB, LB, LinearMap.lcomp_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at this ⊢
    rw [hρ', Matrix.mulVec_mulVec, Matrix.mul_assoc _ A B, hAB, Matrix.mul_one] at this
    rw [Matrix.mulVec_mulVec]
    exact this
  let f : PkgI4.htSpace p ρ i →ₗ[ℚ_[p]] PkgI4.htSpace p ρ' i := TA.restrict hTA
  let g : PkgI4.htSpace p ρ' i →ₗ[ℚ_[p]] PkgI4.htSpace p ρ i := TB.restrict hTB
  have e : PkgI4.htSpace p ρ i ≃ₗ[ℚ_[p]] PkgI4.htSpace p ρ' i := LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext; intro φ; apply Subtype.ext; apply LinearMap.ext; intro v
      simp [f, g, TA, TB, LA, LB, Matrix.mulVec_mulVec, hAB, hBA])
    (by
      apply LinearMap.ext; intro φ; apply Subtype.ext; apply LinearMap.ext; intro v
      simp [f, g, TA, TB, LA, LB, Matrix.mulVec_mulVec, hAB, hBA])
  exact e.finrank_eq.symm

/-- **`HTConj` from `HTExtend`.** -/
theorem htConj_of (hX : HTExtend) : HTConj := by
  intro ℓ _ n r ρ' S hconj hr
  obtain ⟨P, hP⟩ := hconj
  obtain ⟨E, hEfd, ρE, hmap, hHT⟩ := hr
  let T : Set (PadicAlgCl ℓ) :=
    Set.range (fun ij : Fin n × Fin n => (P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) ij.1 ij.2) ∪
    Set.range (fun ij : Fin n × Fin n =>
      ((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) ij.1 ij.2)
  have hTfin : Finite T := ((Set.finite_range _).union (Set.finite_range _)).to_subtype
  have hadj : FiniteDimensional ℚ_[ℓ] (IntermediateField.adjoin ℚ_[ℓ] T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E' : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) := E ⊔ IntermediateField.adjoin ℚ_[ℓ] T
  have hE'fd : FiniteDimensional ℚ_[ℓ] E' := IntermediateField.finiteDimensional_sup _ _
  obtain ⟨ρE', hmap', hHT'⟩ := hX ℓ n (r.restrictLocal ℓ) S E E' le_sup_left ρE hmap hHT
  have hmemT : ∀ x ∈ T, x ∈ E' := fun x hx =>
    (le_sup_right : IntermediateField.adjoin ℚ_[ℓ] T ≤ E') (IntermediateField.subset_adjoin _ _ hx)
  let Pm : Matrix (Fin n) (Fin n) E' := Matrix.of fun i j =>
    ⟨(P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j, hmemT _ (Or.inl ⟨(i, j), rfl⟩)⟩
  let Qm : Matrix (Fin n) (Fin n) E' := Matrix.of fun i j =>
    ⟨((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j,
      hmemT _ (Or.inr ⟨(i, j), rfl⟩)⟩
  let φ := algebraMap E' (PadicAlgCl ℓ)
  have hinj : Function.Injective (φ.mapMatrix : Matrix (Fin n) (Fin n) E' → _) := by
    intro M N hMN
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hMN i) j)
  have hPm : φ.mapMatrix Pm = (P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := by
    ext i j; rfl
  have hQm : φ.mapMatrix Qm =
      ((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := by
    ext i j; rfl
  have hPQ : Pm * Qm = 1 := hinj (by rw [map_mul, map_one, hPm, hQm]; simp)
  have hQP : Qm * Pm = 1 := hinj (by rw [map_mul, map_one, hPm, hQm]; simp)
  let P' : GL (Fin n) E' := ⟨Pm, Qm, hPQ, hQP⟩
  have hP' : Matrix.GeneralLinearGroup.map φ P' = P := by
    apply Units.ext
    exact hPm
  let ρ'E : PkgI4.GQp ℓ →* GL (Fin n) E' :=
    { toFun := fun σ => P'⁻¹ * ρE' σ * P'
      map_one' := by simp
      map_mul' := fun σ τ => by simp [mul_assoc] }
  refine ⟨E', hE'fd, ρ'E, ?_, ?_⟩
  · intro σ
    change Matrix.GeneralLinearGroup.map φ (P'⁻¹ * ρE' σ * P') = _
    rw [map_mul, map_mul, map_inv, hP', hmap' σ]
    change P⁻¹ * r.toHom (PkgI4.decomp ℓ σ) * P = ρ'.toHom (PkgI4.decomp ℓ σ)
    rw [hP]
    group
  · intro w
    unfold PkgI4.htMult
    rw [finrank_htSpace_conj ρE' ρ'E P' (fun σ => rfl) (-w)]
    exact hHT' w

end G0Galois

end

end G12DetHTSec



/-! ## g12-det: `HTExtend` proved (Hodge–Tate multiplicities do not depend on the coefficient
field) -/

section G12DetHTExtSec

noncomputable section

namespace G0Galois

section Extend

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {E E' : Type} [Field E] [Field E'] [Algebra ℚ_[p] E]
  [Algebra ℚ_[p] E'] [Algebra E E'] [IsScalarTower ℚ_[p] E E'] [FiniteDimensional ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E'] {m : ℕ} (b : Module.Basis (Fin m) E E')

/-- `v ↦ (v_a • b_k)_a`. -/
def jk (k : Fin m) : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E') :=
  (LinearMap.pi fun a => (LinearMap.toSpanSingleton E E' (b k)).comp (LinearMap.proj a) :
    (Fin n → E) →ₗ[E] (Fin n → E')).restrictScalars ℚ_[p]

/-- `w ↦ (b.coord k (w_a))_a`. -/
def ck (k : Fin m) : (Fin n → E') →ₗ[ℚ_[p]] (Fin n → E) :=
  (LinearMap.pi fun a => (b.coord k).comp (LinearMap.proj a) :
    (Fin n → E') →ₗ[E] (Fin n → E)).restrictScalars ℚ_[p]

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma jk_apply (k : Fin m) (v : Fin n → E) (a : Fin n) : jk (p := p) b k v a = v a • b k := rfl

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_apply (k : Fin m) (w : Fin n → E') (a : Fin n) :
    ck (p := p) b k w a = b.repr (w a) k := rfl

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma jk_mulVec (k : Fin m) (M : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    jk (p := p) b k (M.mulVec v) = (M.map (algebraMap E E')).mulVec (jk (p := p) b k v) := by
  funext a
  simp only [jk_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  ring

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_mulVec (k : Fin m) (M : Matrix (Fin n) (Fin n) E) (w : Fin n → E') :
    ck (p := p) b k ((M.map (algebraMap E E')).mulVec w) = M.mulVec (ck (p := p) b k w) := by
  funext a
  simp only [ck_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_jk (k l : Fin m) (v : Fin n → E) :
    ck (p := p) b l (jk (p := p) b k v) = if k = l then v else 0 := by
  funext a
  rw [ck_apply, jk_apply, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma sum_jk_ck (w : Fin n → E') : ∑ k, jk (p := p) b k (ck (p := p) b k w) = w := by
  funext a
  simp only [Finset.sum_apply, jk_apply, ck_apply]
  exact b.sum_repr (w a)

/-- `htSpace` of the extended model is `htSpace` of the model, `m` times. -/
def htSpaceExtendEquiv (ρE : PkgI4.GQp p →* GL (Fin n) E) (i : ℤ) :
    PkgI4.htSpace p ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) i ≃ₗ[ℚ_[p]]
      (Fin m → PkgI4.htSpace p ρE i) where
  toFun φ k := ⟨φ.1.comp (jk (p := p) b k), by
    intro σ v
    have := φ.2 σ (jk (p := p) b k v)
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [jk_mulVec]
    exact this⟩
  invFun ψ := ⟨∑ k, (ψ k).1.comp (ck (p := p) b k), by
    intro σ w
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
      map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := (ψ k).2 σ (ck (p := p) b k w)
    have hm : ((((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) σ :
        GL (Fin n) E') : Matrix (Fin n) (Fin n) E') =
        ((ρE σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E E') := rfl
    rw [hm, ck_mulVec]
    exact h⟩
  left_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [← map_sum, sum_jk_ck]
  right_inv ψ := by
    funext k
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [Finset.sum_eq_single k]
    · rw [ck_jk, if_pos rfl]
    · intro l _ hl
      rw [ck_jk, if_neg (Ne.symm hl), map_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  map_add' φ ψ := by
    funext k; apply Subtype.ext; rfl
  map_smul' c φ := by
    funext k; apply Subtype.ext; rfl

include b in
lemma htMult_extend (ρE : PkgI4.GQp p →* GL (Fin n) E) (w : ℤ) :
    PkgI4.htMult p ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) w =
      PkgI4.htMult p ρE w := by
  have hm : 0 < m := by
    by_contra h
    have h0 : m = 0 := by omega
    subst h0
    have := b.index_nonempty
    exact (IsEmpty.false this.some)
  unfold PkgI4.htMult
  rw [(htSpaceExtendEquiv b ρE (-w)).finrank_eq,
    ← (Finsupp.linearEquivFunOnFinite ℚ_[p] (PkgI4.htSpace p ρE (-w)) (Fin m)).finrank_eq,
    Module.finrank_finsupp, Fintype.card_fin, ← Module.finrank_mul_finrank ℚ_[p] E E',
    Module.finrank_eq_card_basis b, Fintype.card_fin, mul_comm (Module.finrank ℚ_[p] E) m]
  exact Nat.mul_div_mul_left _ _ hm

end Extend

/-- **`HTExtend`, proved.** -/
theorem htExtend : HTExtend := by
  intro p _ n ρ S E E' _ _ hle ρE hmap hHT
  letI : Algebra E E' := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[p] E E' := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite E E' := Module.Finite.of_restrictScalars_finite ℚ_[p] E E'
  haveI : Module.Free E E' := Module.Free.of_divisionRing E E'
  let b := Module.finBasis E E'
  refine ⟨(Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE, ?_, ?_⟩
  · intro σ
    rw [← hmap σ]
    apply Units.ext
    ext i j
    rfl
  · intro w
    rw [htMult_extend b ρE w]
    exact hHT w

end G0Galois

end

end G12DetHTExtSec



/-! ## g12-det: `G12Weight` from `HTExtend` and the two new leaves -/

namespace G0Galois

/-- **`G12Weight` from `HTExtend` (glue) and the leaves `SenTwist`, `FiniteImageHT`.** -/
theorem g12Weight_of_htExtend (hX : HTExtend) (hSen : SenTwist) (hFI : FiniteImageHT) :
    G12Weight :=
  g12Weight_of_HT (htConj_of hX) hSen hFI

/-- **`G12Weight` from the two new leaves `SenTwist` and `FiniteImageHT`** (with the leaves R13,
R14, R15, T18, T19 that `G12Weight` itself takes as hypotheses); all glue proved. -/
theorem g12Weight_of_senTwist (hSen : SenTwist) (hFI : FiniteImageHT) : G12Weight :=
  g12Weight_of_htExtend htExtend hSen hFI

end G0Galois


/-! ## g0-assemble2: swan (scratch/swan/Swan.lean, Bridge.lean, final_part.lean, assembled as in its build.sh,
minus t-different's Herbrand copy: Leaves.lean already proves `PkgI6.herbrandQuotient`) -/

/-!
# swan: the glue Props `SwanIndependent`, `SwanIntegral`, `AdaptedExists`

Task swan. The three Props are stated in the kernel module
`ZInQKernel/HDecomp/Conductor/LadicCond.lean` (namespace `LadicCond`) and used by
`scratch/g0-mod-newform/` (G15). §0 repeats them verbatim (checked equal by `rfl`).

* §1-§4: **`AdaptedExists` is proved** (`Swan.adaptedExists`), from Mathlib only.
* §5: `SwanIntegral` and `SwanIndependent` are reduced to three smaller named Props.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Swan

open PkgI4 LadicCond

/-! ## §0. The three Props, verbatim from `LadicCond.lean` -/

section Verbatim

variable {p : ℕ} [Fact p.Prime]

/-- Verbatim copy of `LadicCond.SwanIndependent`. -/
def SwanIndependent : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (ρ : GQp p →* GL (Fin n) k) (L L' : Fld p),
    IsAdapted L ρ → IsAdapted L' ρ → swanAt L ρ = swanAt L' ρ

/-- Verbatim copy of `LadicCond.AdaptedExists`. -/
def AdaptedExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)),
    Continuous ρ → ∃ L : Fld p, IsAdapted L ρ

/-- Verbatim copy of `LadicCond.SwanIntegral`. -/
def SwanIntegral : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime], p ≠ ℓ →
    ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)), Continuous ρ →
    ∀ L : Fld p, IsAdapted L ρ →
      (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ)

example : SwanIndependent (p := p) = LadicCond.SwanIndependent (p := p) := rfl
example : AdaptedExists (p := p) = LadicCond.AdaptedExists (p := p) := rfl
example : SwanIntegral = LadicCond.SwanIntegral := rfl

end Verbatim

/-! ## §1. Wild elements act through `p`-power order on a finite Galois level -/

section Wild

variable {p : ℕ} [Fact p.Prime]

/-- Ultrametric: `‖a − b‖ < ‖b‖ ⇒ ‖a‖ = ‖b‖`. -/
theorem norm_eq_of_norm_sub_lt {a b : Kbar p} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have h1 : ‖a‖ ≤ max ‖a - b‖ ‖b‖ := by
    have := IsUltrametricDist.norm_add_le_max (a - b) b
    rwa [sub_add_cancel] at this
  have h2 : ‖b‖ ≤ max ‖b - a‖ ‖a‖ := by
    have := IsUltrametricDist.norm_add_le_max (b - a) a
    rwa [sub_add_cancel] at this
  rw [norm_sub_rev] at h2
  rcases le_total ‖a - b‖ ‖b‖ with h3 | h3
  · rw [max_eq_right h3] at h1
    rcases le_total ‖a - b‖ ‖a‖ with h4 | h4
    · rw [max_eq_right h4] at h2; linarith
    · rw [max_eq_left h4] at h2; linarith
  · linarith

theorem mul_mem_wildSet {σ τ : GQp p} (hσ : σ ∈ wildSet) (hτ : τ ∈ wildSet) :
    σ * τ ∈ wildSet := by
  intro x hx
  have hτx : ‖τ x‖ = ‖x‖ := norm_eq_of_norm_sub_lt (hτ x hx)
  have hτx0 : τ x ≠ 0 := by
    intro h; rw [h, norm_zero] at hτx; exact hx (norm_eq_zero.1 hτx.symm)
  have e : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx))
  rw [← hτx]; exact hσ _ hτx0

theorem pow_mem_wildSet {σ : GQp p} (hσ : σ ∈ wildSet) (m : ℕ) : σ ^ m ∈ wildSet := by
  induction m with
  | zero => rw [pow_zero]; exact one_mem_wildSet
  | succ m ih => rw [pow_succ]; exact mul_mem_wildSet ih hσ

/-- On a finite Galois `L`, every `γ` has finite order: some `γ^m`, `m > 0`, fixes `L`. -/
theorem exists_pow_fix {L : Fld p} (hL : IsFinGal L) (γ : GQp p) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, (γ ^ m) x = x := by
  have hfin := (finite_restr hL (Set.univ : Set (GQp p))).to_subtype
  let f : ℕ → restr L '' (Set.univ : Set (GQp p)) := fun j => ⟨restr L (γ ^ j), γ ^ j, trivial, rfl⟩
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have he' : restr L (γ ^ i) = restr L (γ ^ j) := congrArg Subtype.val he
  -- symmetric: reduce to `i < j`
  have key : ∀ a b : ℕ, a < b → restr L (γ ^ a) = restr L (γ ^ b) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, (γ ^ m) x = x := by
    intro a b hab hrab
    refine ⟨b - a, by omega, fun x hx => ?_⟩
    have h1 : (γ ^ b) x = (γ ^ a) x := (congrFun hrab ⟨x, hx⟩).symm
    have h2 : γ ^ b = γ ^ a * γ ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [h2, AlgEquiv.mul_apply] at h1
    exact (γ ^ a).injective h1
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h he'
  · exact key j i h he'.symm

/-- `‖m‖ = 1` in `ℚ̄_p` for `p ∤ m`. -/
theorem norm_natCast_eq_one {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : Kbar p)‖ = 1 := by
  have e : ((m : ℚ_[p]) : PadicAlgCl p) = (m : Kbar p) := map_natCast (algebraMap ℚ_[p] _) m
  rw [← e, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm

/-- **A wild element of order prime to `p` on `L` is trivial on `L`.** The map
`T x = ∑_{j<m} δ^j x` satisfies `‖T x‖ = ‖x‖` (`T x = m x + ∑ (δ^j x − x)`, `‖m‖ = 1`), so `T` is
an injective, hence surjective, `ℚ_p`-linear endomorphism of `L`; its image is `δ`-fixed. -/
theorem wild_fix_of_coprime {L : Fld p} (hL : IsFinGal L) {δ : GQp p} (hδ : δ ∈ wildSet)
    {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m) (hfix : ∀ x ∈ L, (δ ^ m) x = x) :
    ∀ x ∈ L, δ x = x := by
  have : FiniteDimensional ℚ_[p] L := hL.1
  have hmemj : ∀ (j : ℕ) {x : Kbar p}, x ∈ L → (δ ^ j) x ∈ L := fun j x hx => apply_mem hL _ hx
  let T : L →ₗ[ℚ_[p]] L :=
    { toFun := fun x => ⟨∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p),
        L.sum_mem fun j _ => hmemj j x.2⟩
      map_add' := by
        intro x y; ext
        simp only [IntermediateField.coe_add, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x; ext
        simp only [IntermediateField.coe_smul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def] }
  have hT : ∀ x : L, ((T x : L) : Kbar p) = ∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p) :=
    fun _ => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hx0' : (x : Kbar p) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hsum : ∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p) =
        (m : Kbar p) * x + ∑ j ∈ Finset.range m, ((δ ^ j) (x : Kbar p) - x) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have hlt : ‖∑ j ∈ Finset.range m, ((δ ^ j) (x : Kbar p) - x)‖ < ‖(x : Kbar p)‖ := by
      obtain ⟨j, -, hj⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
        (Finset.nonempty_range_iff.2 hm0.ne') (fun j => (δ ^ j) (x : Kbar p) - x)
      exact lt_of_le_of_lt hj (pow_mem_wildSet hδ j _ hx0')
    have hmx : ‖(m : Kbar p) * x‖ = ‖(x : Kbar p)‖ := by
      rw [norm_mul, norm_natCast_eq_one hpm, one_mul]
    have hTx : ‖((T x : L) : Kbar p)‖ = ‖(x : Kbar p)‖ := by
      rw [hT, hsum, ← hmx]
      apply norm_eq_of_norm_sub_lt
      rw [add_sub_cancel_left, hmx]; exact hlt
    rw [hx, IntermediateField.coe_zero, norm_zero] at hTx
    exact hx0' (norm_eq_zero.1 hTx.symm)
  have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.1 hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  have hy' : y = ∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p) := by
    rw [← hT, hx]
  rw [hy', map_sum]
  have hshift : ∀ j, δ ((δ ^ j) (x : Kbar p)) = (δ ^ (j + 1)) (x : Kbar p) := by
    intro j; rw [pow_succ', AlgEquiv.mul_apply]
  simp_rw [hshift]
  have h1 := Finset.sum_range_succ' (fun j => (δ ^ j) (x : Kbar p)) m
  have h2 := Finset.sum_range_succ (fun j => (δ ^ j) (x : Kbar p)) m
  rw [hfix x x.2, pow_zero, AlgEquiv.one_apply] at *
  rw [h2] at h1
  linear_combination h1.symm

/-- **Wild elements have `p`-power order on every finite Galois level** (the image of `P_p` in
`Gal(L/ℚ_p)` is a `p`-group). -/
theorem wild_pow_fix {L : Fld p} (hL : IsFinGal L) {γ : GQp p} (hγ : γ ∈ wildSet) :
    ∃ k : ℕ, ∀ x ∈ L, (γ ^ (p ^ k)) x = x := by
  obtain ⟨m, hm0, hm⟩ := exists_pow_fix hL γ
  obtain ⟨k, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p
    (Fact.out : p.Prime).one_lt.ne'
  refine ⟨k, wild_fix_of_coprime hL (pow_mem_wildSet hγ _) (Nat.pos_of_ne_zero ?_) hm' ?_⟩
  · rintro rfl; simp at hm0
  · intro x hx; rw [← pow_mul]; exact hm x hx

end Wild

/-! ## §2. Ultrametric matrix estimate -/

section Matrix

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)

/-- All entries of `A` have norm `≤ c`. -/
def Bd (c : ℝ) (A : Mat) : Prop := ∀ i j, ‖A i j‖ ≤ c

theorem Bd.add {c : ℝ} {A B : Mat} (hA : Bd c A) (hB : Bd c B) : Bd c (A + B) := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (hB i j))

theorem Bd.mul {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) {A B : Mat} (hA : Bd c A) (hB : Bd d B) :
    Bd (c * d) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hc

theorem Bd.nsmul {c : ℝ} {A : Mat} (hA : Bd c A) (m : ℕ) : Bd c (m • A) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, norm_mul]
  calc ‖(m : PadicAlgCl ℓ)‖ * ‖A i j‖ ≤ 1 * ‖A i j‖ :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one _ m) (norm_nonneg _)
    _ ≤ c := by rw [one_mul]; exact hA i j

theorem Bd.zero {c : ℝ} (hc : 0 ≤ c) : Bd c (0 : Mat) := fun i j => by simpa using hc

theorem Bd.one_add {A : Mat} (hA : Bd 1 A) : Bd 1 (1 + A) := by
  refine Bd.add (fun i j => ?_) hA
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

/-- `(1 + A)^m − 1 − m A` has entries `≤ a²` when `A` has entries `≤ a ≤ 1`. -/
theorem Bd.pow_sub {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A : Mat} (hA : Bd a A) (m : ℕ) :
    Bd (a ^ 2) ((1 + A) ^ m - 1 - m • A) := by
  induction m with
  | zero => simpa using Bd.zero (sq_nonneg a)
  | succ m ih =>
    have e : (1 + A) ^ (m + 1) - 1 - (m + 1) • A =
        (1 + A) * ((1 + A) ^ m - 1 - m • A) + m • (A * A) := by
      rw [pow_succ', mul_sub, mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, add_mul,
        one_mul, smul_add, add_smul, one_smul]
      abel
    rw [e]
    have hA1 : Bd 1 A := fun i j => (hA i j).trans ha1
    refine Bd.add ?_ ?_
    · simpa using Bd.mul zero_le_one (sq_nonneg a) (Bd.one_add hA1) ih
    · have h := (Bd.mul ha0 ha0 hA hA).nsmul m
      rwa [← sq] at h

end Matrix

/-! ## §3. Continuity gives a finite Galois level -/

section Topo

open scoped Topology

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)

/-- The neighbourhood `{g : ‖g_{ij} − δ_{ij}‖ < r ∀ i j}` of `1` in `GL_n(ℚ̄_ℓ)`. -/
def nbhd (r : ℝ) : Set (GL (Fin n) (PadicAlgCl ℓ)) :=
  {g | ∀ i j, ‖(g : Mat) i j - (1 : Mat) i j‖ < r}

theorem isOpen_nbhd (r : ℝ) : IsOpen (nbhd (ℓ := ℓ) (n := n) r) := by
  have e : nbhd (ℓ := ℓ) (n := n) r =
      ⋂ i, ⋂ j, {g : GL (Fin n) (PadicAlgCl ℓ) | ‖(g : Mat) i j - (1 : Mat) i j‖ < r} := by
    ext g; simp [nbhd]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_lt (((Units.continuous_val.matrix_elem i j).sub continuous_const).norm)
    continuous_const

theorem one_mem_nbhd {r : ℝ} (hr : 0 < r) : (1 : GL (Fin n) (PadicAlgCl ℓ)) ∈ nbhd r := by
  intro i j; simp [hr]

/-- **Continuity gives a level.** For continuous `ρ` and `r > 0` there is a finite Galois
`L/ℚ_p` with `ρ(G_L) ⊆ nbhd r` (Krull topology, `krullTopology_mem_nhds_one_iff_of_normal`). -/
theorem exists_level (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)) (hρ : Continuous ρ) {r : ℝ}
    (hr : 0 < r) : ∃ L : Fld p, IsFinGal L ∧ ∀ σ ∈ fixSet L, ρ σ ∈ nbhd r := by
  have hmem : ρ ⁻¹' nbhd r ∈ 𝓝 (1 : GQp p) := by
    apply hρ.continuousAt.preimage_mem_nhds
    rw [map_one]; exact (isOpen_nbhd r).mem_nhds (one_mem_nbhd hr)
  obtain ⟨E, hEf, hEn, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[p] (PadicAlgCl p) _).1 hmem
  refine ⟨E, ⟨hEf, isGalois_iff.2 ⟨inferInstance, hEn⟩⟩, fun σ hσ => ?_⟩
  exact hE ((IntermediateField.mem_fixingSubgroup_iff E σ).2 hσ)

end Topo

/-! ## §4. `AdaptedExists` -/

section Main

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)

/-- Ultrametric, for `ℚ̄_ℓ`: `‖a − b‖ < ‖b‖ ⇒ ‖a‖ = ‖b‖`. -/
theorem norm_eq_of_norm_sub_lt' {a b : PadicAlgCl ℓ} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ :=
  norm_eq_of_norm_sub_lt (p := ℓ) h

/-- **The key estimate.** If all entries of `A` have norm `≤ a = ‖A_{ij}‖`, `0 < a < 1`, and
`ℓ ∤ m`, then `‖((1 + A)^m − 1)_{ij}‖ = a`. -/
theorem norm_pow_sub_one_entry {A : Mat} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hA : Bd a A)
    {i j : Fin n} (hij : ‖A i j‖ = a) {m : ℕ} (hm : ¬ ℓ ∣ m) :
    ‖((1 + A) ^ m - 1) i j‖ = a := by
  have hB := Bd.pow_sub ha0.le ha1.le hA m i j
  set B := (1 + A) ^ m - 1 - m • A with hBdef
  have e : ((1 + A) ^ m - 1) i j = B i j + (m : PadicAlgCl ℓ) * A i j := by
    have hs : (m • A) i j = (m : PadicAlgCl ℓ) * A i j := by
      rw [Matrix.smul_apply, nsmul_eq_mul]
    simp only [hBdef, Matrix.sub_apply, hs]; ring
  have hmA : ‖(m : PadicAlgCl ℓ) * A i j‖ = a := by
    rw [norm_mul, norm_natCast_eq_one (p := ℓ) hm, one_mul, hij]
  rw [e, ← hmA]
  apply norm_eq_of_norm_sub_lt'
  rw [add_sub_cancel_right, hmA]
  calc ‖B i j‖ ≤ a ^ 2 := hB
    _ < a := by nlinarith

/-- **`AdaptedExists` (proved).** For `ℓ ≠ p` and continuous `ρ : G_{ℚ_p} → GL_n(ℚ̄_ℓ)` there is a
finite Galois `L/ℚ_p` with `ρ` trivial on `P_p ∩ G_L`. Take `L` with `ρ(G_L) ⊆ nbhd 1`. If
`γ ∈ P_p ∩ G_L` had `ρ(γ) = 1 + A ≠ 1`, let `a = max ‖A_{ij}‖ ∈ (0, 1)`, and take `L'` with
`ρ(G_{L'}) ⊆ nbhd a`. Some `γ^{p^k}` fixes `L'` (`wild_pow_fix`), so `‖((1+A)^{p^k} − 1)_{ij}‖ < a`,
against `norm_pow_sub_one_entry` (`ℓ ∤ p^k`). -/
theorem adaptedExists {p : ℕ} [Fact p.Prime] : LadicCond.AdaptedExists (p := p) := by
  intro ℓ _ hℓp n ρ hρ
  obtain ⟨L, hL, hL1⟩ := exists_level ρ hρ one_pos
  refine ⟨L, hL, fun γ hγ => ?_⟩
  obtain ⟨hw, hf⟩ := hγ
  by_contra hne
  set A : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) := (ρ γ : Matrix (Fin n) (Fin n) _) - 1 with hAdef
  have hρA : (ρ γ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) = 1 + A := by
    rw [hAdef]; abel
  obtain ⟨i0, j0, h0⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hne
    apply Units.ext
    rw [Units.val_one, hρA]
    have : A = 0 := Matrix.ext fun i j => by simpa using hc i j
    rw [this, add_zero]
  have : Nonempty (Fin n × Fin n) := ⟨(i0, j0)⟩
  obtain ⟨⟨i1, j1⟩, hmax⟩ := Finite.exists_max (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖)
  set a := ‖A i1 j1‖ with hadef
  have hBd : Bd a A := fun i j => hmax (i, j)
  have ha0 : 0 < a := lt_of_lt_of_le (norm_pos_iff.2 h0) (hmax (i0, j0))
  have ha1 : a < 1 := by
    have := hL1 γ hf i1 j1
    rwa [hadef, hAdef, Matrix.sub_apply]
  obtain ⟨L', hL', hL'a⟩ := exists_level ρ hρ ha0
  obtain ⟨k, hk⟩ := wild_pow_fix hL' hw
  have hlt := hL'a (γ ^ (p ^ k)) hk i1 j1
  rw [map_pow, Units.val_pow_eq_pow_val, hρA, ← Matrix.sub_apply] at hlt
  have hℓ : ¬ ℓ ∣ p ^ k := by
    intro h
    have h1 := (Fact.out : ℓ.Prime).dvd_of_dvd_pow h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 h1)
  rw [norm_pow_sub_one_entry ha0 ha1 hBd rfl hℓ] at hlt
  exact lt_irrefl _ hlt

end Main

/-! ## §5. `SwanIntegral` and `SwanIndependent` from three smaller Props

Both follow from: for `L` adapted to `ρ` and `u > 0`, `V^{G^u} = V^{G^u(L) ∩ P}` (the absolute
upper group acts through its image in `Gal(L/ℚ_p)`), plus the finite-level integral formula. -/

section Reduction

/-- **H1 (GLUE: finite-level change of variables; Serre, *Corps locaux* IV §3 and VI §2,
numbering UNVERIFIED).** At an adapted finite Galois level `L`, the Swan conductor
`∑_{i ≥ 1} (g_i/g_0) codim V^{G_i ∩ P}` equals `∫₀^∞ codim V^{G^u(L) ∩ P} du`: substitute
`u = φ_{L/ℚ_p}(t)`, `dφ = (g_{⌈t⌉}/g_0) dt`, `G^{φ(t)} = G_{⌈t⌉}`. A statement about one finite
extension and real step functions; no theorem of ramification theory beyond the definitions. -/
def SwanAtIntegral : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (n : ℕ) (ρ : GQp p →* GL (Fin n) k) (L : Fld p),
    IsAdapted L ρ →
      (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperSet L u ∩ wildSet) : ℝ)

/-- **H2 (GLUE from the definitions; Serre, *Corps locaux* IV §1-§3).** For `u > 0` the absolute
upper ramification group lies in wild inertia: `G^u ⊆ P_p`. (For `x ≠ 0` take a finite Galois `L ∋ x`;
`ψ_L(u) > 0`, so `σ ∈ G_1(L)`, and `G_1(L)` acts by `σx/x ≡ 1` mod the maximal ideal.) -/
def UpperAbsWild : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (u : ℝ), 0 < u → upperAbs p u ⊆ wildSet

/-- **H3 (GLUE from Herbrand's theorem plus compactness; Serre, *Corps locaux* IV §3, Prop. 14 and
the remark defining `G^v` for infinite Galois extensions, numbering UNVERIFIED).** The projection
`G^u → G^u(L/ℚ_p)` is onto: every `σ` in `G^u(L) ∩ P` (preimage in `G_{ℚ_p}`) agrees on `L` with
an element of the absolute `G^u`. -/
def UpperAbsSurj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Fld p), IsFinGal L → ∀ u : ℝ, 0 < u →
    ∀ σ ∈ upperSet L u ∩ wildSet, ∃ τ ∈ upperAbs p u, ∀ x ∈ L, τ x = σ x

variable {p : ℕ} [Fact p.Prime]

theorem inv_mem_wildSet {σ : GQp p} (hσ : σ ∈ wildSet) : σ⁻¹ ∈ wildSet := by
  intro x hx
  have hy : σ (σ⁻¹ x) = x := σ.apply_symm_apply x
  have hy0 : σ⁻¹ x ≠ 0 := fun h => hx (by rw [← hy, h, map_zero])
  have h1 := hσ _ hy0
  rw [hy] at h1
  have h2 : ‖x‖ = ‖σ⁻¹ x‖ := norm_eq_of_norm_sub_lt h1
  rw [h2, norm_sub_rev]
  exact h1

/-- **The absolute upper group acts through `L`.** For `L` adapted to `ρ` and `u > 0`,
`V^{G^u} = V^{G^u(L) ∩ P}`. -/
theorem invariants_upperAbs (h2 : UpperAbsWild) (h3 : UpperAbsSurj) {k : Type} [Field k] {n : ℕ}
    {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsAdapted L ρ) {u : ℝ} (hu : 0 < u) :
    invariants ρ (upperAbs p u) = invariants ρ (upperSet L u ∩ wildSet) := by
  apply le_antisymm
  · intro v hv σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := h3 p L hL.1 u hu σ hσ
    have hτw : τ ∈ wildSet := h2 p u hu hτ
    have h1 : τ⁻¹ * σ ∈ wildSet ∩ fixSet L := by
      refine ⟨mul_mem_wildSet (inv_mem_wildSet hτw) hσ.2, fun x hx => ?_⟩
      rw [AlgEquiv.mul_apply, ← hτσ x hx]
      exact τ.symm_apply_apply x
    have h2' : ρ σ = ρ τ * ρ (τ⁻¹ * σ) := by rw [← map_mul, mul_inv_cancel_left]
    rw [h2', hL.2 _ h1, mul_one]
    exact hv τ hτ
  · intro v hv σ hσ
    exact hv σ ⟨hσ L hL.1, h2 p u hu hσ⟩

/-- At any adapted level, `Sw_L(ρ) = ∫₀^∞ codim V^{G^u} du` (absolute upper filtration). -/
theorem swanAt_eq_integral_upperAbs (h1 : SwanAtIntegral) (h2 : UpperAbsWild)
    (h3 : UpperAbsSurj) {k : Type} [Field k] {n : ℕ} {ρ : GQp p →* GL (Fin n) k} {L : Fld p}
    (hL : IsAdapted L ρ) :
    (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ) := by
  rw [h1 p k n ρ L hL]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [codimInv, codimInv, invariants_upperAbs h2 h3 hL hu]

/-- **`SwanIntegral` (L8) from H1-H3.** (Continuity and `p ≠ ℓ` are not used.) -/
theorem swanIntegral_of (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (h3 : UpperAbsSurj) :
    LadicCond.SwanIntegral := by
  intro ℓ _ p _ _ n ρ _ L hL
  exact swanAt_eq_integral_upperAbs h1 h2 h3 hL

/-- **`SwanIndependent` from H1-H3**, for every field `k` and every homomorphism `ρ`: both levels
compute the same integral over the absolute upper filtration. -/
theorem swanIndependent_of (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (h3 : UpperAbsSurj) :
    LadicCond.SwanIndependent (p := p) := by
  intro k _ n ρ L L' hL hL'
  have e := (swanAt_eq_integral_upperAbs h1 h2 h3 hL).trans
    (swanAt_eq_integral_upperAbs h1 h2 h3 hL').symm
  exact_mod_cast e

/-- **All three glue Props of G15** from H1-H3 (`AdaptedExists` needs nothing). -/
theorem swan_all (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (h3 : UpperAbsSurj) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  ⟨fun _ _ => swanIndependent_of h1 h2 h3, swanIntegral_of h1 h2 h3, fun _ _ => adaptedExists⟩

end Reduction

/-! ## §6. H3 from Herbrand's theorem and the compactness of `G_{ℚ_p}` -/

section Herbrand

open scoped Topology

/-- **Leaf H3a: Herbrand's theorem** (Serre, *Corps locaux* IV §3, Prop. 14, numbering UNVERIFIED;
the same theorem as pkg-I6's leaf I6.8 `PkgI6.HerbrandQuotient`, here over the finite Galois
subfields of `ℚ̄_p` and the upper numbering `LadicCond.upperSet`). For `L ⊆ M` finite Galois over
`ℚ_p` and every `v`, the image of `G^v(M/ℚ_p)` in `Gal(L/ℚ_p)` is `G^v(L/ℚ_p)`:
`(G/H)^v = G^v H/H`. Preimages in `G_{ℚ_p}` restricted to `L`. Stated only for `v > 0`, the
range the proof uses (Serre's statement covers every `v ≥ −1`). -/
def HerbrandUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L M : Fld p), IsFinGal L → IsFinGal M → L ≤ M → ∀ v : ℝ, 0 < v →
    restr L '' upperSet M v = restr L '' upperSet L v

variable {p : ℕ} [Fact p.Prime]

/-- Membership in `ramSet L i` depends only on the restriction to `L`. -/
theorem mem_ramSet_of_restr {L : Fld p} {σ τ : GQp p} (h : ∀ x ∈ L, τ x = σ x) {i : ℕ}
    (hσ : σ ∈ ramSet L i) : τ ∈ ramSet L i := by
  obtain ⟨ϖ, hϖ, hb⟩ := hσ
  exact ⟨ϖ, hϖ, fun x hx hx1 => by rw [h x hx]; exact hb x hx hx1⟩

/-- Membership in `upperSet L v` depends only on the restriction to `L`. -/
theorem mem_upperSet_of_restr {L : Fld p} {σ τ : GQp p} (h : ∀ x ∈ L, τ x = σ x) {v : ℝ}
    (hσ : σ ∈ upperSet L v) : τ ∈ upperSet L v := by
  unfold upperSet ramSetR at *
  split_ifs at * with h1
  · trivial
  · exact mem_ramSet_of_restr h hσ

theorem restr_eq_iff {L : Fld p} {σ τ : GQp p} : restr L τ = restr L σ ↔ ∀ x ∈ L, τ x = σ x :=
  ⟨fun h x hx => congrFun h ⟨x, hx⟩, fun h => funext fun x => h x x.2⟩

/-- A finite Galois `E` containing `L` and every member of a finite family of finite Galois
fields. -/
theorem exists_finGal_above {L : Fld p} (hL : IsFinGal L)
    (u : Finset {M : Fld p // IsFinGal M}) :
    ∃ E : Fld p, IsFinGal E ∧ L ≤ E ∧ ∀ i ∈ u, i.1 ≤ E := by
  classical
  induction u using Finset.induction_on with
  | empty => exact ⟨L, hL, le_rfl, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert i u _ ih =>
    obtain ⟨E, ⟨hEf, hEg⟩, hLE, hu⟩ := ih
    have : FiniteDimensional ℚ_[p] E := hEf
    have : IsGalois ℚ_[p] E := hEg
    have : FiniteDimensional ℚ_[p] i.1 := i.2.1
    have : IsGalois ℚ_[p] i.1 := i.2.2
    refine ⟨E ⊔ i.1, ⟨IntermediateField.finiteDimensional_sup _ _, inferInstance⟩,
      hLE.trans le_sup_left, fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact le_sup_right
    · exact (hu j hj).trans le_sup_left

/-- A set of `τ` determined by `τ|_E` for a finite `E` is closed. -/
theorem isClosed_of_restr {E : Fld p} (hE : FiniteDimensional ℚ_[p] E) {S : Set (GQp p)}
    (hS : ∀ σ τ, (∀ x ∈ E, τ x = σ x) → σ ∈ S → τ ∈ S) : IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro τ hτ
  have hU : (E.fixingSubgroup : Set (GQp p)) ∈ 𝓝 (1 : GQp p) :=
    (krullTopology_mem_nhds_one_iff ℚ_[p] (PadicAlgCl p) _).2 ⟨E, hE, subset_rfl⟩
  have hf : ContinuousAt (fun g : GQp p => τ⁻¹ * g) τ :=
    (continuous_const.mul continuous_id).continuousAt
  have hmem : (fun g : GQp p => τ⁻¹ * g) ⁻¹' (E.fixingSubgroup : Set (GQp p)) ∈ 𝓝 τ := by
    apply hf.preimage_mem_nhds
    simp only [inv_mul_cancel]; exact hU
  refine Filter.mem_of_superset hmem fun g hg hgS => hτ (hS g τ (fun x hx => ?_) hgS)
  have h1 : (τ⁻¹ * g) x = x := (IntermediateField.mem_fixingSubgroup_iff E _).1 hg x hx
  rw [AlgEquiv.mul_apply] at h1
  calc τ x = τ ((τ⁻¹) (g x)) := by rw [h1]
    _ = g x := τ.apply_symm_apply (g x)

/-- **H3 from Herbrand's theorem (GLUE, proved).** If `σ ∈ G^u(L)` (preimage), then some `τ` in
the absolute `G^u` agrees with `σ` on `L`: the closed sets
`C_M = {τ : τ|_L = σ|_L, τ ∈ G^u(M)}` have the finite intersection property (Herbrand, at a finite
Galois `E` containing `L` and the `M`s), and `G_{ℚ_p}` is compact (Mathlib). -/
theorem upperAbsSurj_of_herbrand (hH : HerbrandUpper) : UpperAbsSurj := by
  intro p _ L hL u hu σ hσ
  let ι := {M : Fld p // IsFinGal M}
  let t : ι → Set (GQp p) := fun M => {τ | (∀ x ∈ L, τ x = σ x) ∧ τ ∈ upperSet M.1 u}
  have htc : ∀ M, IsClosed (t M) := by
    intro M
    have : FiniteDimensional ℚ_[p] L := hL.1
    have : FiniteDimensional ℚ_[p] M.1 := M.2.1
    refine isClosed_of_restr (E := L ⊔ M.1) (IntermediateField.finiteDimensional_sup _ _) ?_
    intro a b hab ⟨ha1, ha2⟩
    refine ⟨fun x hx => (hab x (le_sup_left (a := L) hx)).trans (ha1 x hx), ?_⟩
    exact mem_upperSet_of_restr (fun x hx => hab x (le_sup_right (b := M.1) hx)) ha2
  have hst : ∀ s : Finset ι, ((Set.univ : Set (GQp p)) ∩ ⋂ i ∈ s, t i).Nonempty := by
    intro s
    obtain ⟨E, hE, hLE, hsE⟩ := exists_finGal_above hL s
    have h1 : restr L σ ∈ restr L '' upperSet E u := by
      rw [hH p L E hL hE hLE u hu]; exact ⟨σ, hσ.1, rfl⟩
    obtain ⟨τ, hτE, hτσ⟩ := h1
    refine ⟨τ, trivial, Set.mem_iInter₂.2 fun M hM => ⟨restr_eq_iff.1 hτσ, ?_⟩⟩
    have h2 : restr M.1 τ ∈ restr M.1 '' upperSet M.1 u := by
      rw [← hH p M.1 E M.2 hE (hsE M hM) u hu]; exact ⟨τ, hτE, rfl⟩
    obtain ⟨τ', hτ', he⟩ := h2
    exact mem_upperSet_of_restr (restr_eq_iff.1 he.symm) hτ'
  obtain ⟨τ, -, hτ⟩ := isCompact_univ.inter_iInter_nonempty t htc hst
  rw [Set.mem_iInter] at hτ
  refine ⟨τ, fun M hM => (hτ ⟨M, hM⟩).2, ?_⟩
  obtain ⟨M0, hM0⟩ : ∃ M : ι, True := ⟨⟨L, hL⟩, trivial⟩
  exact (hτ M0).1

/-- **`SwanIntegral` and `SwanIndependent` from H1, H2 and Herbrand's theorem.** -/
theorem swan_all' (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (hH : HerbrandUpper) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  swan_all h1 h2 (upperAbsSurj_of_herbrand hH)

end Herbrand

/-! ## §7. H2 (`UpperAbsWild`) from the definitions -/

section Wild2

variable {p : ℕ} [Fact p.Prime]

/-- `z ≠ 0` and `‖σz − z‖ < ‖z‖`. -/
def WildAt (σ : GQp p) (z : Kbar p) : Prop := z ≠ 0 ∧ ‖σ z - z‖ < ‖z‖

theorem WildAt.norm_eq {σ : GQp p} {z : Kbar p} (h : WildAt σ z) : ‖σ z‖ = ‖z‖ :=
  norm_eq_of_norm_sub_lt h.2

theorem WildAt.mul {σ : GQp p} {a b : Kbar p} (ha : WildAt σ a) (hb : WildAt σ b) :
    WildAt σ (a * b) := by
  refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
  have e : σ (a * b) - a * b = σ a * (σ b - b) + (σ a - a) * b := by rw [map_mul]; ring
  rw [e]
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha.1
  have hb0 : 0 < ‖b‖ := norm_pos_iff.2 hb.1
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_mul, ha.norm_eq]; exact mul_lt_mul_of_pos_left hb.2 ha0
  · rw [norm_mul, norm_mul]; exact mul_lt_mul_of_pos_right ha.2 hb0

theorem WildAt.inv {σ : GQp p} {a : Kbar p} (ha : WildAt σ a) : WildAt σ a⁻¹ := by
  refine ⟨inv_ne_zero ha.1, ?_⟩
  have hσa : σ a ≠ 0 := fun h => ha.1 (by simpa using congrArg σ.symm h)
  have e : σ a⁻¹ - a⁻¹ = (a - σ a) * (σ a)⁻¹ * a⁻¹ := by
    have h1 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.1
    have h2 : σ a * (σ a)⁻¹ = 1 := mul_inv_cancel₀ hσa
    rw [map_inv₀]; linear_combination -(σ a)⁻¹ * h1 + a⁻¹ * h2
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha.1
  rw [e, norm_mul, norm_mul, norm_inv, norm_inv, ha.norm_eq, norm_sub_rev]
  calc ‖σ a - a‖ * ‖a‖⁻¹ * ‖a‖⁻¹ < ‖a‖ * ‖a‖⁻¹ * ‖a‖⁻¹ := by
        have : 0 < ‖a‖⁻¹ := inv_pos.2 ha0
        exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right ha.2 this) this
    _ = ‖a‖⁻¹ := by field_simp

theorem wildAt_one (σ : GQp p) : WildAt σ 1 := ⟨one_ne_zero, by simp⟩

theorem WildAt.zpow {σ : GQp p} {a : Kbar p} (ha : WildAt σ a) (n : ℤ) : WildAt σ (a ^ n) := by
  have hn : ∀ m : ℕ, WildAt σ (a ^ m) := by
    intro m
    induction m with
    | zero => simpa using wildAt_one σ
    | succ m ih => rw [pow_succ]; exact ih.mul ha
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact hn m
  · rw [zpow_neg, zpow_natCast]; exact (hn m).inv

/-- **`G_1(L)` acts wildly on `L`.** If `σ ∈ ramSet L 1` then `‖σx − x‖ < ‖x‖` for every
`x ∈ L`, `x ≠ 0`: write `x = y ϖ^a` with `‖y‖ = 1` (discreteness of `‖L^×‖`, from `IsUnif`); then
`‖σy − y‖ ≤ ‖ϖ‖² < 1` and `‖σϖ − ϖ‖ ≤ ‖ϖ‖² < ‖ϖ‖`, and `WildAt` is multiplicative. -/
theorem wildAt_of_ramSet_one {L : Fld p} {σ : GQp p} (hσ : σ ∈ ramSet L 1) {x : Kbar p}
    (hx : x ∈ L) (hx0 : x ≠ 0) : WildAt σ x := by
  obtain ⟨ϖ, hϖ, hb⟩ := hσ
  set r := ‖ϖ‖ with hrdef
  have hr1 : r < 1 := hϖ.2.1
  have hpL : (p : Kbar p) ∈ L := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hr0 : 0 < r := by
    have h1 := hϖ.2.2 (p : Kbar p) hpL isUnif_bot.2.1
    have h2 : 0 < ‖(p : Kbar p)‖ := by
      rw [norm_p_kbar]; exact inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)
    exact lt_of_lt_of_le h2 h1
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.1 hr0
  have hr2 : r ^ (1 + 1) < r :=
    calc r ^ (1 + 1) = r * r := by ring
      _ < r * 1 := mul_lt_mul_of_pos_left hr1 hr0
      _ = r := mul_one r
  have hwϖ : WildAt σ ϖ := ⟨hϖ0, lt_of_le_of_lt (hb ϖ hϖ.1 hr1.le) hr2⟩
  have hx0' : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hx0' (one_lt_inv₀ hr0 |>.2 hr1)
  set y := x * ϖ ^ (n + 1) with hydef
  have hyL : y ∈ L := L.mul_mem hx (zpow_mem hϖ.1 _)
  have hy : ‖y‖ = ‖x‖ * r ^ (n + 1) := by rw [hydef, norm_mul, norm_zpow]
  have hrn : r ^ (n + 1) = r ^ n * r := by rw [zpow_add_one₀ hr0.ne']
  have hrinv : ∀ m : ℤ, r⁻¹ ^ m * r ^ m = 1 := by
    intro m; rw [← mul_zpow, inv_mul_cancel₀ hr0.ne', one_zpow]
  have hrpos : 0 < r ^ (n + 1) := zpow_pos hr0 _
  have hyle : ‖y‖ ≤ 1 := by
    rw [hy, ← hrinv (n + 1)]
    exact mul_le_mul_of_nonneg_right hn2 hrpos.le
  have hygt : r < ‖y‖ := by
    rw [hy]
    calc r = r⁻¹ ^ n * r ^ (n + 1) := by rw [hrn, ← mul_assoc, hrinv n, one_mul]
      _ < ‖x‖ * r ^ (n + 1) := mul_lt_mul_of_pos_right hn1 hrpos
  have hy1 : ‖y‖ = 1 := by
    rcases hyle.lt_or_eq with h | h
    · exact absurd (hϖ.2.2 y hyL h) (not_le.2 hygt)
    · exact h
  have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; exact zero_ne_one hy1
  have hwy : WildAt σ y := ⟨hy0, by
    rw [hy1]; exact lt_of_le_of_lt (hb y hyL hyle) (hr2.trans hr1)⟩
  have hxe : x = y * ϖ ^ (-(n + 1)) := by
    rw [hydef, mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, mul_one]
  rw [hxe]
  exact hwy.mul (hwϖ.zpow _)

/-! ### `ψ_L(u) > 0` for `u > 0`, so `G^u(L) ⊆ G_1(L)` -/

theorem ramSet_anti {L : Fld p} {i j : ℕ} (h : i ≤ j) : ramSet L j ⊆ ramSet L i := by
  rintro σ ⟨ϖ, hϖ, hb⟩
  exact ⟨ϖ, hϖ, fun x hx h1 => (hb x hx h1).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega))⟩

theorem ramSetR_anti {L : Fld p} {t t' : ℝ} (h : t ≤ t') : ramSetR L t' ⊆ ramSetR L t := by
  unfold ramSetR
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h.trans h1) h2
  · exact Set.subset_univ _
  · exact ramSet_anti (Int.toNat_le_toNat (Int.ceil_mono h))

theorem one_mem_ramSetR {L : Fld p} (hL : IsFinGal L) (t : ℝ) : (1 : GQp p) ∈ ramSetR L t := by
  unfold ramSetR
  split_ifs
  · trivial
  · obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
    exact fixSet_subset_ramSet hϖ _ (fun x _ => rfl)

theorem one_le_ramCardR {L : Fld p} (hL : IsFinGal L) (t : ℝ) : 1 ≤ ramCardR L t := by
  have hfin := (finite_restr hL (ramSetR L t)).to_subtype
  have hne : Nonempty (restr L '' ramSetR L t) := ⟨⟨restr L 1, 1, one_mem_ramSetR hL t, rfl⟩⟩
  exact Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨hne, hfin⟩)

theorem ramCardR_le {L : Fld p} (hL : IsFinGal L) (t : ℝ) :
    ramCardR L t ≤ Nat.card (restr L '' (Set.univ : Set (GQp p))) :=
  Nat.card_mono (finite_restr hL _) (Set.image_mono (Set.subset_univ _))

theorem ramCardR_anti {L : Fld p} (hL : IsFinGal L) :
    Antitone (fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ)) := by
  intro t t' h
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Nat.card_mono (finite_restr hL _) (Set.image_mono (ramSetR_anti h))

theorem phiAt_nonpos {L : Fld p} {t : ℝ} (ht : t ≤ 0) : phiAt L t ≤ 0 := by
  rw [phiAt, intervalIntegral.integral_symm, neg_nonpos]
  exact intervalIntegral.integral_nonneg ht fun x _ => by positivity

theorem phiAt_ge {L : Fld p} (hL : IsFinGal L) {t : ℝ} (ht : 0 ≤ t) :
    t / (ramCard L 0 : ℝ) ≤ phiAt L t := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht
    (f := fun _ => 1 / (ramCard L 0 : ℝ))
    (g := fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ))
    intervalIntegrable_const (ramCardR_anti hL).intervalIntegrable
    (fun x _ => div_le_div_of_nonneg_right (by exact_mod_cast one_le_ramCardR hL x)
      (Nat.cast_nonneg _))
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one_div] at h
  exact h

theorem phiAt_le {L : Fld p} (hL : IsFinGal L) {t : ℝ} (ht : 0 ≤ t) :
    phiAt L t ≤ t * ((Nat.card (restr L '' (Set.univ : Set (GQp p))) : ℝ) / (ramCard L 0 : ℝ)) := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht
    (g := fun _ => (Nat.card (restr L '' (Set.univ : Set (GQp p))) : ℝ) / (ramCard L 0 : ℝ))
    (f := fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ))
    (ramCardR_anti hL).intervalIntegrable intervalIntegrable_const
    (fun x _ => div_le_div_of_nonneg_right (by exact_mod_cast ramCardR_le hL x)
      (Nat.cast_nonneg _))
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  exact h

/-- **`G^u(L) ⊆ G_1(L)` for `u > 0`** (preimages in `G_{ℚ_p}`): `ψ_L(u) > 0`, from
`t/g_0 ≤ φ_L(t) ≤ t·|Gal(L/ℚ_p)|/g_0` for `t ≥ 0` and `φ_L ≤ 0` on `[−1, 0]`. -/
theorem upperSet_subset_ramSet_one {L : Fld p} (hL : IsFinGal L) {u : ℝ} (hu : 0 < u) :
    upperSet L u ⊆ ramSet L 1 := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
  set g0 : ℝ := (ramCard L 0 : ℝ) with hg0
  have hg0pos : 0 < g0 := by
    rw [hg0]; exact_mod_cast Nat.pos_of_ne_zero (ramCard_ne_zero hL hϖ 0)
  set C : ℝ := (Nat.card (restr L '' (Set.univ : Set (GQp p))) : ℝ) with hC
  have hC1 : 1 ≤ C := by
    rw [hC]; exact_mod_cast (one_le_ramCardR hL 0).trans (ramCardR_le hL 0)
  have hCg : 0 < C / g0 := div_pos (by linarith) hg0pos
  set S := {t : ℝ | -1 ≤ t ∧ u ≤ phiAt L t} with hS
  have hne : S.Nonempty := by
    refine ⟨u * g0, by nlinarith, ?_⟩
    have := phiAt_ge hL (t := u * g0) (by positivity)
    rwa [mul_div_assoc, div_self hg0pos.ne', mul_one] at this
  have hlb : ∀ t ∈ S, u / (C / g0) ≤ t := by
    rintro t ⟨-, ht⟩
    by_cases h0 : t ≤ 0
    · exact absurd (ht.trans (phiAt_nonpos h0)) (not_le.2 hu)
    · rw [div_le_iff₀ hCg]
      exact ht.trans (phiAt_le hL (le_of_lt (not_le.1 h0)))
  have hs : 0 < sInf S := lt_of_lt_of_le (div_pos hu hCg) (le_csInf hne hlb)
  intro σ hσ
  unfold upperSet ramSetR at hσ
  rw [← hS] at hσ
  split_ifs at hσ with hle
  · exact absurd hle (by linarith)
  refine ramSet_anti ?_ hσ
  have : 0 < ⌈sInf S⌉ := Int.ceil_pos.2 hs
  omega

/-- Every `x ∈ ℚ̄_p` lies in a finite Galois `L/ℚ_p` (the normal closure of `ℚ_p(x)`). -/
theorem exists_finGal_mem (x : Kbar p) : ∃ L : Fld p, IsFinGal L ∧ x ∈ L := by
  have hint : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  set K : Fld p := IntermediateField.adjoin ℚ_[p] {x} with hK
  have : FiniteDimensional ℚ_[p] K := IntermediateField.adjoin.finiteDimensional hint
  refine ⟨IntermediateField.normalClosure ℚ_[p] K (Kbar p),
    ⟨normalClosure.is_finiteDimensional _ _ _, isGalois_iff.2 ⟨inferInstance, inferInstance⟩⟩, ?_⟩
  exact K.le_normalClosure (IntermediateField.mem_adjoin_simple_self ℚ_[p] x)

/-- **H2 (`UpperAbsWild`) is proved.** -/
theorem upperAbsWild : UpperAbsWild := by
  intro p _ u hu σ hσ x hx0
  obtain ⟨L, hL, hxL⟩ := exists_finGal_mem x
  exact (wildAt_of_ramSet_one (upperSet_subset_ramSet_one hL hu (hσ L hL)) hxL hx0).2

end Wild2

/-! ## §7b. H1 (`SwanAtIntegral`): the finite-level change of variables -/

section ChangeVar

variable {p : ℕ} [Fact p.Prime]

open MeasureTheory

/-- `g_i/g_0`. -/
def wt (L : Fld p) (i : ℕ) : ℝ := (ramCard L i : ℝ) / (ramCard L 0 : ℝ)

/-- `Φ_j = φ_L(j) = ∑_{i=1}^{j} g_i/g_0`. -/
def Phi (L : Fld p) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, wt L (i + 1)

theorem Phi_zero (L : Fld p) : Phi L 0 = 0 := by simp [Phi]

theorem Phi_succ (L : Fld p) (j : ℕ) : Phi L (j + 1) = Phi L j + wt L (j + 1) := by
  simp [Phi, Finset.sum_range_succ]

theorem wt_pos {L : Fld p} (hL : IsFinGal L) (i : ℕ) : 0 < wt L i := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
  unfold wt
  exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero (ramCard_ne_zero hL hϖ i))
    (by exact_mod_cast Nat.pos_of_ne_zero (ramCard_ne_zero hL hϖ 0))

theorem wt_ge {L : Fld p} (hL : IsFinGal L) (i : ℕ) : 1 / (ramCard L 0 : ℝ) ≤ wt L i := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
  unfold wt
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (ramCard_ne_zero hL hϖ i)) (Nat.cast_nonneg _)

theorem Phi_strictMono {L : Fld p} (hL : IsFinGal L) : StrictMono (Phi L) :=
  strictMono_nat_of_lt_succ fun j => by rw [Phi_succ]; linarith [wt_pos hL (j + 1)]

theorem Phi_nonneg {L : Fld p} (hL : IsFinGal L) (j : ℕ) : 0 ≤ Phi L j := by
  rw [← Phi_zero L]; exact (Phi_strictMono hL).monotone (Nat.zero_le j)

theorem Phi_ge {L : Fld p} (hL : IsFinGal L) (j : ℕ) :
    (j : ℝ) * (1 / (ramCard L 0 : ℝ)) ≤ Phi L j := by
  induction j with
  | zero => simp [Phi_zero]
  | succ j ih => rw [Phi_succ]; push_cast; linarith [wt_ge hL (j + 1)]

/-- On `(j, j+1]` the integrand of `φ_L` is `g_{j+1}/g_0`. -/
theorem integrand_eq {L : Fld p} {j : ℕ} {t : ℝ} (h1 : (j : ℝ) < t) (h2 : t ≤ j + 1) :
    (ramCardR L t : ℝ) / (ramCard L 0 : ℝ) = wt L (j + 1) := by
  have hc : ⌈t⌉ = (j : ℤ) + 1 := Int.ceil_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
  have ht : ¬ t ≤ -1 := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  unfold ramCardR ramSetR wt
  rw [if_neg ht, hc]
  rfl

theorem integral_piece {L : Fld p} (j : ℕ) {t : ℝ} (h1 : (j : ℝ) ≤ t) (h2 : t ≤ j + 1) :
    ∫ x in (j : ℝ)..t, (ramCardR L x : ℝ) / (ramCard L 0 : ℝ) = (t - j) * wt L (j + 1) := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => wt L (j + 1)) ?_]
  · rw [intervalIntegral.integral_const, smul_eq_mul]
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le h1] at hx
    exact integrand_eq hx.1 (hx.2.trans h2)

theorem integrable_phi {L : Fld p} (hL : IsFinGal L) (a b : ℝ) :
    IntervalIntegrable (fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ)) volume a b :=
  (ramCardR_anti hL).intervalIntegrable

theorem phiAt_nat {L : Fld p} (hL : IsFinGal L) (j : ℕ) : phiAt L j = Phi L j := by
  induction j with
  | zero => simp [phiAt, Phi_zero]
  | succ j ih =>
    rw [phiAt] at ih ⊢
    rw [← intervalIntegral.integral_add_adjacent_intervals (integrable_phi hL 0 j)
      (integrable_phi hL j (j + 1 : ℕ)), ih, Phi_succ]
    push_cast
    rw [integral_piece j (t := (j : ℝ) + 1) (by linarith) le_rfl (L := L)]
    ring

theorem phiAt_piece {L : Fld p} (hL : IsFinGal L) (j : ℕ) {t : ℝ} (h1 : (j : ℝ) ≤ t)
    (h2 : t ≤ j + 1) : phiAt L t = Phi L j + (t - j) * wt L (j + 1) := by
  rw [← phiAt_nat hL j, phiAt, phiAt, ← intervalIntegral.integral_add_adjacent_intervals
    (integrable_phi hL 0 j) (integrable_phi hL j t), integral_piece j h1 h2]

theorem phiAt_mono {L : Fld p} (hL : IsFinGal L) {t t' : ℝ} (h : t ≤ t') :
    phiAt L t ≤ phiAt L t' := by
  rw [phiAt, phiAt, ← intervalIntegral.integral_add_adjacent_intervals
    (integrable_phi hL 0 t) (integrable_phi hL t t')]
  have : 0 ≤ ∫ x in t..t', (ramCardR L x : ℝ) / (ramCard L 0 : ℝ) :=
    intervalIntegral.integral_nonneg h fun x _ => by positivity
  linarith

/-- **`G^u(L) = G_{j+1}(L)` for `Φ_j < u ≤ Φ_{j+1}`** (i.e. `⌈ψ_L(u)⌉ = j + 1`). -/
theorem upperSet_eq {L : Fld p} (hL : IsFinGal L) {j : ℕ} {u : ℝ} (h1 : Phi L j < u)
    (h2 : u ≤ Phi L (j + 1)) : upperSet L u = ramSet L (j + 1) := by
  set S := {t : ℝ | -1 ≤ t ∧ u ≤ phiAt L t} with hS
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hw := wt_pos hL (j + 1)
  have hmem : ((j : ℝ) + 1) ∈ S := by
    refine ⟨by linarith, ?_⟩
    have := phiAt_nat hL (j + 1)
    push_cast at this
    rw [this]; exact h2
  have hbdd : BddBelow S := ⟨-1, fun t ht => ht.1⟩
  have hle : sInf S ≤ j + 1 := csInf_le hbdd hmem
  set t0 := (j : ℝ) + (u - Phi L j) / wt L (j + 1) with ht0
  have ht0j : (j : ℝ) < t0 := by
    have : 0 < (u - Phi L j) / wt L (j + 1) := div_pos (by linarith) hw
    linarith
  have ht0le : t0 ≤ j + 1 := by
    have : (u - Phi L j) / wt L (j + 1) ≤ 1 := by
      rw [div_le_one hw]; rw [Phi_succ] at h2; linarith
    linarith
  have hlb : ∀ t ∈ S, t0 ≤ t := by
    rintro t ⟨-, ht⟩
    by_contra hlt
    push Not at hlt
    by_cases htj : t ≤ j
    · have := phiAt_mono hL htj
      rw [phiAt_nat hL] at this
      linarith
    · push Not at htj
      rw [phiAt_piece hL j htj.le (by linarith)] at ht
      have : (t - j) * wt L (j + 1) < (t0 - j) * wt L (j + 1) :=
        mul_lt_mul_of_pos_right (by linarith) hw
      have e : (t0 - j) * wt L (j + 1) = u - Phi L j := by
        rw [ht0]; field_simp; ring
      linarith
  have hgt : (j : ℝ) < sInf S := lt_of_lt_of_le ht0j (le_csInf ⟨_, hmem⟩ hlb)
  have hc : ⌈sInf S⌉ = (j : ℤ) + 1 :=
    Int.ceil_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
  show ramSetR L (sInf S) = _
  unfold ramSetR
  rw [if_neg (by linarith), hc]
  rfl

theorem exists_piece {L : Fld p} (hL : IsFinGal L) {u : ℝ} (hu : 0 < u) :
    ∃ j : ℕ, Phi L j < u ∧ u ≤ Phi L (j + 1) := by
  classical
  have hg0 : 0 < (ramCard L 0 : ℝ) := by
    have := wt_pos hL 0
    unfold wt at this
    rcases (div_pos_iff.1 this) with h | h
    · exact h.2
    · exact absurd h.2 (not_lt.2 (Nat.cast_nonneg _))
  have hex : ∃ j : ℕ, u ≤ Phi L (j + 1) := by
    obtain ⟨m, hm⟩ := exists_nat_gt (u * (ramCard L 0 : ℝ))
    refine ⟨m, le_trans ?_ (Phi_ge hL (m + 1))⟩
    rw [mul_one_div, le_div_iff₀ hg0]; push_cast; linarith
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h | h
  · rw [h, Phi_zero]; exact hu
  · have hmin := Nat.find_min hex (show (Nat.find hex).pred < Nat.find hex by omega)
    push Not at hmin
    rw [h]; exact hmin

/-- **H1 (`SwanAtIntegral`) is proved.** -/
theorem swanAtIntegral : SwanAtIntegral := by
  intro p _ k _ n ρ L hL
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1.1
  obtain ⟨N, hN⟩ := eventuallyTrivial hL.1 hϖ
  set c : ℕ → ℕ := fun i => codimInv ρ (ramSet L i ∩ wildSet) with hcdef
  have hc0 : ∀ i, N ≤ i → c i = 0 := fun i hi =>
    codimInv_eq_zero fun σ hσ => hL.2 σ ⟨hσ.2, hN i hi hσ.1⟩
  -- left side: a finite sum
  have hsupp : Function.support (fun i : ℕ => ((ramCard L (i + 1) : ℚ) / ramCard L 0) *
      (codimInv ρ (ramSet L (i + 1) ∩ wildSet) : ℚ)) ⊆ ↑(Finset.range N) := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hi
    have : c (i + 1) = 0 := hc0 (i + 1) (by omega)
    simp only [hcdef] at this
    simp [this]
  have hLHS : (swanAt L ρ : ℝ) = ∑ i ∈ Finset.range N, wt L (i + 1) * (c (i + 1) : ℝ) := by
    rw [swanAt, finsum_eq_sum_of_support_subset _ hsupp]
    push_cast
    rfl
  -- right side: the integrand is a finite sum of indicators
  have hpt : ∀ u ∈ Set.Ioi (0 : ℝ), (codimInv ρ (upperSet L u ∩ wildSet) : ℝ) =
      ∑ j ∈ Finset.range N,
        (Set.Ioc (Phi L j) (Phi L (j + 1))).indicator (fun _ => (c (j + 1) : ℝ)) u := by
    intro u hu
    obtain ⟨j, h1, h2⟩ := exists_piece hL.1 hu
    rw [upperSet_eq hL.1 h1 h2]
    have hmono := (Phi_strictMono hL.1).monotone
    have hterm : ∀ m, (Set.Ioc (Phi L m) (Phi L (m + 1))).indicator
        (fun _ => (c (m + 1) : ℝ)) u = if j = m then (c (m + 1) : ℝ) else 0 := by
      intro m
      by_cases hm : j = m
      · subst hm
        rw [Set.indicator_of_mem (show u ∈ Set.Ioc (Phi L j) (Phi L (j + 1)) from ⟨h1, h2⟩),
          if_pos rfl]
      · rw [Set.indicator_of_notMem, if_neg hm]
        rintro ⟨hm1, hm2⟩
        rcases lt_or_gt_of_ne hm with hlt | hlt
        · have := hmono (show j + 1 ≤ m by omega); linarith
        · have := hmono (show m + 1 ≤ j by omega); linarith
    rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_ite_eq (Finset.range N) j]
    split_ifs with hj
    · rfl
    · have : c (j + 1) = 0 := hc0 (j + 1) (by simp at hj; omega)
      simp only [hcdef] at this
      simp [this]
  have hint : ∀ j ∈ Finset.range N, Integrable
      ((Set.Ioc (Phi L j) (Phi L (j + 1))).indicator (fun _ => (c (j + 1) : ℝ)))
      (volume.restrict (Set.Ioi 0)) := by
    intro j _
    rw [integrable_indicator_iff measurableSet_Ioc]
    refine IntegrableOn.restrict ?_
    exact integrableOn_const (by simp [Real.volume_Ioc])
  rw [hLHS, setIntegral_congr_fun measurableSet_Ioi hpt, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsub : Set.Ioc (Phi L j) (Phi L (j + 1)) ⊆ Set.Ioi 0 :=
    Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (Phi_nonneg hL.1 j))
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsub, setIntegral_const,
    Real.volume_real_Ioc_of_le ((Phi_strictMono hL.1).monotone (Nat.le_succ j)), smul_eq_mul,
    Phi_succ]
  ring

end ChangeVar

/-! ## §8. Final form -/

/-- **Main result.** `AdaptedExists` holds outright; `SwanIndependent` (every `p`) and
`SwanIntegral` (L8) follow from one glue Prop, H1 `SwanAtIntegral` (the finite-level change of
variables), and one leaf, `HerbrandUpper` (Herbrand's theorem). -/
theorem swan_final (h1 : SwanAtIntegral) (hH : HerbrandUpper) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  swan_all h1 upperAbsWild (upperAbsSurj_of_herbrand hH)

/-- **Main result (final form).** `AdaptedExists` holds outright; `SwanIndependent` (every `p`)
and `SwanIntegral` (L8) follow from the single leaf `HerbrandUpper` (Herbrand's theorem). -/
theorem swan_main (hH : HerbrandUpper) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  swan_final swanAtIntegral hH

end Swan

end


/-!
# swan, part 2: transport of Herbrand's theorem from DVRs to the subfields of `ℚ̄_p`

Goal: `HerbrandUpper` (Swan.lean §6) from `PkgI6.HerbrandQuotient` (kernel leaf I6.8, proved by
task t-different over DVRs). For a finite Galois `E/ℚ_p` inside `ℚ̄_p`, `𝓞_E = {x ∈ E : ‖x‖ ≤ 1}`
is the integral closure of `ℤ_p` in `E`; `Gal(𝓞_E/ℤ_p) ≅ Gal(E/ℚ_p)` (Mathlib's `galRestrict`)
carries `PkgI6.lowerRam` to `LadicCond.ramSet`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SwanBridge

open PkgI4 LadicCond Polynomial

variable {p : ℕ} [Fact p.Prime]

/-! ## §1. `𝓞_E` -/

/-- `y ∈ ℚ̄_p` is integral over `ℤ_p` iff `‖y‖ ≤ 1` (the norm of `ℚ̄_p` is the spectral norm). -/
theorem isIntegral_iff_norm_le_one (y : Kbar p) : IsIntegral ℤ_[p] y ↔ ‖y‖ ≤ 1 := by
  have hyQ : IsIntegral ℚ_[p] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

theorem norm_algebraMap_le_one (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (Kbar p) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kbar p), PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

/-- `𝓞_E = {x ∈ E : ‖x‖ ≤ 1}`, as a `ℤ_p`-subalgebra of `ℚ̄_p`. -/
def OE (E : Fld p) : Subalgebra ℤ_[p] (Kbar p) where
  carrier := {x | x ∈ E ∧ ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => ⟨E.mul_mem ha.1 hb.1, by
    rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg b, ha.2, hb.2]⟩
  add_mem' := fun {a b} ha hb => ⟨E.add_mem ha.1 hb.1,
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha.2 hb.2)⟩
  algebraMap_mem' := fun a => ⟨by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kbar p)]
    exact E.algebraMap_mem _, norm_algebraMap_le_one a⟩

theorem mem_OE {E : Fld p} {x : Kbar p} : x ∈ OE E ↔ x ∈ E ∧ ‖x‖ ≤ 1 := Iff.rfl

variable (E : Fld p)

/-- `𝓞_E → E`. -/
def toE : OE E →+* E where
  toFun x := ⟨x, x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

instance algOE : Algebra (OE E) E := (toE E).toAlgebra

theorem algebraMap_OE_coe (x : OE E) : ((algebraMap (OE E) E x : E) : Kbar p) = x := rfl

instance : IsScalarTower ℤ_[p] (OE E) E :=
  IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    rw [algebraMap_OE_coe]
    rfl

instance towerE : IsScalarTower ℤ_[p] E (Kbar p) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] E, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kbar p)]
    rfl

instance isIntegralClosure_OE : IsIntegralClosure (OE E) ℤ_[p] E where
  algebraMap_injective := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  isIntegral_iff := by
    intro x
    have hint : IsIntegral ℤ_[p] x ↔ IsIntegral ℤ_[p] (x : Kbar p) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[p] E (Kbar p))
        (algebraMap E (Kbar p)).injective).symm
    rw [hint, isIntegral_iff_norm_le_one]
    constructor
    · intro h; exact ⟨⟨x, x.2, h⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact y.2.2

/-! ## §2. `𝓞_E` is a DVR, finite over `ℤ_p`; its maximal ideal by norms -/

section DVR

variable [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]

instance isFractionRing_OE : IsFractionRing (OE E) E :=
  IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] E (OE E)

instance finite_OE : Module.Finite ℤ_[p] (OE E) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] E (OE E)

omit [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E] in
theorem algebraMap_Kbar_injective : Function.Injective (algebraMap ℤ_[p] (Kbar p)) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (Kbar p)]
  exact (algebraMap ℚ_[p] _).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

instance faithful_Kbar : FaithfulSMul ℤ_[p] (Kbar p) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 algebraMap_Kbar_injective

instance torsionFree_Kbar : Module.IsTorsionFree ℤ_[p] (Kbar p) :=
  FaithfulSMul.to_isTorsionFree ℤ_[p] (Kbar p)

instance torsionFree_OE : Module.IsTorsionFree ℤ_[p] (OE E) :=
  Subalgebra.instIsTorsionFree (OE E)

variable {E}

theorem norm_pos_of_ne {x : OE E} (hx : x ≠ 0) : 0 < ‖(x : Kbar p)‖ :=
  norm_pos_iff.2 fun h => hx (Subtype.ext h)

/-- Units of `𝓞_E` are the elements of norm `1`. -/
theorem isUnit_iff {x : OE E} : IsUnit x ↔ ‖(x : Kbar p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖((u : OE E) : Kbar p)‖ * ‖(((u⁻¹ : (OE E)ˣ) : OE E) : Kbar p)‖ = 1 := by
      rw [← norm_mul]
      have : ((u : OE E) : Kbar p) * (((u⁻¹ : (OE E)ˣ) : OE E) : Kbar p) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
      rw [this, norm_one]
    have h2 := (u : OE E).2.2
    have h3 := ((u⁻¹ : (OE E)ˣ) : OE E).2.2
    nlinarith [norm_nonneg ((u : OE E) : Kbar p),
      norm_nonneg (((u⁻¹ : (OE E)ˣ) : OE E) : Kbar p)]
  · intro h
    have hx0 : (x : Kbar p) ≠ 0 := by intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : Kbar p)⁻¹, E.inv_mem x.2.1, ?_⟩, ?_⟩
    · rw [norm_inv, h, inv_one]
    · apply Subtype.ext
      change (x : Kbar p) * (x : Kbar p)⁻¹ = 1
      exact mul_inv_cancel₀ hx0

/-- Divisibility in `𝓞_E` by norms. -/
theorem dvd_iff {a x : OE E} (ha : a ≠ 0) : a ∣ x ↔ ‖(x : Kbar p)‖ ≤ ‖(a : Kbar p)‖ := by
  have ha0 : (a : Kbar p) ≠ 0 := fun h => ha (Subtype.ext h)
  constructor
  · rintro ⟨c, rfl⟩
    change ‖(a : Kbar p) * (c : Kbar p)‖ ≤ _
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) c.2.2
  · intro h
    refine ⟨⟨(x : Kbar p) / a, E.div_mem x.2.1 a.2.1, ?_⟩, ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · apply Subtype.ext
      change (x : Kbar p) = (a : Kbar p) * ((x : Kbar p) / a)
      field_simp

variable (E)

/-- A uniformizer of `E` as an element of `𝓞_E`. -/
def unif : OE E :=
  ⟨(exists_isUnif (L := E) inferInstance).choose,
    (exists_isUnif (L := E) inferInstance).choose_spec.1,
    (exists_isUnif (L := E) inferInstance).choose_spec.2.1.le⟩

theorem isUnif_unif : IsUnif E ((unif E : OE E) : Kbar p) :=
  (exists_isUnif (L := E) inferInstance).choose_spec

theorem unif_norm_pos : 0 < ‖((unif E : OE E) : Kbar p)‖ := by
  have hpL : (p : Kbar p) ∈ E := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have h1 := (isUnif_unif E).2.2 (p : Kbar p) hpL isUnif_bot.2.1
  have h2 : 0 < ‖(p : Kbar p)‖ := by
    rw [norm_p_kbar]; exact inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)
  exact lt_of_lt_of_le h2 h1

theorem unif_ne_zero : unif E ≠ 0 := fun h => by
  have := unif_norm_pos E; rw [h] at this; simp at this

theorem irreducible_unif : Irreducible (unif E) := by
  have hr := isUnif_unif E
  have hr0 := unif_norm_pos E
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · rw [isUnit_iff] at hu; linarith [hr.2.1]
  · have hn : ‖((unif E : OE E) : Kbar p)‖ = ‖(a : Kbar p)‖ * ‖(b : Kbar p)‖ := by
      rw [hab, Subalgebra.coe_mul, norm_mul]
    by_contra hcon
    push Not at hcon
    rw [isUnit_iff, isUnit_iff] at hcon
    have ha1 : ‖(a : Kbar p)‖ < 1 := lt_of_le_of_ne a.2.2 hcon.1
    have hb1 : ‖(b : Kbar p)‖ < 1 := lt_of_le_of_ne b.2.2 hcon.2
    have ha := hr.2.2 _ a.2.1 ha1
    have hb := hr.2.2 _ b.2.1 hb1
    have hlt : ‖((unif E : OE E) : Kbar p)‖ * ‖((unif E : OE E) : Kbar p)‖ <
        ‖((unif E : OE E) : Kbar p)‖ := by nlinarith [hr.2.1]
    nlinarith [norm_nonneg (a : Kbar p), norm_nonneg (b : Kbar p)]

/-- Every nonzero `x ∈ 𝓞_E` is `ϖ^n` times a unit. -/
theorem exists_assoc {x : OE E} (hx : x ≠ 0) : ∃ n : ℕ, Associated (unif E ^ n) x := by
  classical
  set r := ‖((unif E : OE E) : Kbar p)‖ with hr
  have hr0 := unif_norm_pos E
  have hr1 : r < 1 := (isUnif_unif E).2.1
  have hx0 := norm_pos_of_ne hx
  have hex : ∃ k : ℕ, r ^ (k + 1) < ‖(x : Kbar p)‖ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hx0 hr1
    exact ⟨k, lt_of_le_of_lt (pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_succ k)) hk⟩
  set n := Nat.find hex with hn
  have hn1 : r ^ (n + 1) < ‖(x : Kbar p)‖ := Nat.find_spec hex
  have hn2 : ‖(x : Kbar p)‖ ≤ r ^ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero]; exact x.2.2
    · have := Nat.find_min hex (show n - 1 < n by omega)
      push Not at this
      rwa [show n - 1 + 1 = n by omega] at this
  have hdvd : unif E ^ n ∣ x := by
    rw [dvd_iff (pow_ne_zero n (unif_ne_zero E)), Subalgebra.coe_pow, norm_pow]
    exact hn2
  obtain ⟨u, hu⟩ := hdvd
  have hu0 : u ≠ 0 := by rintro rfl; rw [mul_zero] at hu; exact hx hu
  have hunit : IsUnit u := by
    rw [isUnit_iff]
    have hnx : ‖(x : Kbar p)‖ = r ^ n * ‖(u : Kbar p)‖ := by
      rw [hu, Subalgebra.coe_mul, norm_mul, Subalgebra.coe_pow, norm_pow]
    by_contra hne
    have hlt : ‖(u : Kbar p)‖ < 1 := lt_of_le_of_ne u.2.2 hne
    have hle := (isUnif_unif E).2.2 _ u.2.1 hlt
    rw [hnx, pow_succ] at hn1
    have : r ^ n * ‖(u : Kbar p)‖ ≤ r ^ n * r := mul_le_mul_of_nonneg_left hle (by positivity)
    linarith
  exact ⟨n, ⟨hunit.unit, by rw [hu]; rfl⟩⟩

instance dvr_OE : IsDiscreteValuationRing (OE E) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨unif E, irreducible_unif E, fun hx => exists_assoc E hx⟩

/-- `𝔪^{i+1} = {x : ‖x‖ ≤ ‖ϖ‖^{i+1}}`. -/
theorem mem_maximalIdeal_pow {x : OE E} (i : ℕ) :
    x ∈ IsLocalRing.maximalIdeal (OE E) ^ (i + 1) ↔
      ‖(x : Kbar p)‖ ≤ ‖((unif E : OE E) : Kbar p)‖ ^ (i + 1) := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (irreducible_unif E),
    Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    dvd_iff (pow_ne_zero _ (unif_ne_zero E)), Subalgebra.coe_pow, norm_pow]

end DVR

/-! ## §3. `Gal(𝓞_E/ℤ_p)` and the ramification dictionary -/

section Galois

variable [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]

/-- `G_{ℚ_p} → Gal(E/ℚ_p) ≅ Gal(𝓞_E/ℤ_p)` (restriction, then Mathlib's `galRestrict`). -/
def res : GQp p →* (OE E ≃ₐ[ℤ_[p]] OE E) :=
  (galRestrict ℤ_[p] ℚ_[p] E (OE E)).toMonoidHom.comp (AlgEquiv.restrictNormalHom E)

theorem res_apply (σ : GQp p) (x : OE E) : ((res E σ x : OE E) : Kbar p) = σ (x : Kbar p) := by
  have h1 := algebraMap_galRestrict_apply ℤ_[p] (AlgEquiv.restrictNormalHom E σ) x
  have h2 := AlgEquiv.restrictNormal_commutes σ E (algebraMap (OE E) E x)
  rw [← algebraMap_OE_coe, ← algebraMap_OE_coe E x]
  change ((algebraMap (OE E) E (galRestrict ℤ_[p] ℚ_[p] E (OE E)
    (AlgEquiv.restrictNormalHom E σ) x) : E) : Kbar p) = _
  rw [h1]
  exact h2

theorem res_surjective : Function.Surjective (res E) :=
  (galRestrict ℤ_[p] ℚ_[p] E (OE E)).surjective.comp (AlgEquiv.restrictNormalHom_surjective _)

/-- Every `x ∈ E` has `p^k x ∈ 𝓞_E` for some `k`. -/
theorem exists_pow_mul_mem {x : Kbar p} (hx : x ∈ E) : ∃ k : ℕ, (p : Kbar p) ^ k * x ∈ OE E := by
  have hpL : (p : Kbar p) ∈ E := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hp1 : ‖(p : Kbar p)‖ < 1 := isUnif_bot.2.1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖x‖ + 1) by positivity) hp1
  refine ⟨k, E.mul_mem (pow_mem hpL k) hx, ?_⟩
  rw [norm_mul, norm_pow]
  rw [lt_div_iff₀ (by positivity)] at hk
  nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg (p : Kbar p)) k]

theorem res_eq_iff {σ τ : GQp p} : res E σ = res E τ ↔ ∀ x ∈ E, σ x = τ x := by
  constructor
  · intro h x hx
    obtain ⟨k, hk⟩ := exists_pow_mul_mem E hx
    have h1 := res_apply E σ ⟨_, hk⟩
    rw [h, res_apply] at h1
    simp only [map_mul, map_pow, map_natCast] at h1
    have hp0 : ((p : Kbar p)) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    exact (mul_left_cancel₀ hp0 h1).symm
  · intro h
    ext x
    rw [res_apply, res_apply, h _ x.2.1]

theorem ramSet_iff {σ : GQp p} {i : ℕ} :
    σ ∈ ramSet E i ↔ res E σ ∈ PkgI6.lowerRam ℤ_[p] (OE E) i := by
  rw [PkgI6.mem_lowerRam]
  constructor
  · rintro ⟨ϖ, hϖ, hb⟩ b
    rw [mem_maximalIdeal_pow, Subalgebra.coe_sub, res_apply, ← (isUnif_unif E).norm_eq hϖ]
    exact hb b b.2.1 b.2.2
  · intro h
    refine ⟨_, isUnif_unif E, fun x hx hx1 => ?_⟩
    have := (mem_maximalIdeal_pow E i).1 (h ⟨x, hx, hx1⟩)
    rwa [Subalgebra.coe_sub, res_apply] at this

theorem ramSetR_iff {σ : GQp p} {t : ℝ} :
    σ ∈ ramSetR E t ↔ res E σ ∈ PkgI6.lowerRamR ℤ_[p] (OE E) t := by
  unfold ramSetR PkgI6.lowerRamR
  split_ifs
  · exact ⟨fun _ => Subgroup.mem_top _, fun _ => trivial⟩
  · exact ramSet_iff E

/-- Two maps that separate the same pairs have images of the same cardinality. -/
theorem card_image_eq {α β γ : Type*} (F : α → β) (G : α → γ) (hFG : ∀ a b, F a = F b ↔ G a = G b)
    (S : Set α) : Nat.card (F '' S) = Nat.card (G '' S) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun y => ⟨G y.2.choose, Set.mem_image_of_mem _ y.2.choose_spec.1⟩) ⟨?_, ?_⟩)
  · intro y1 y2 h
    have h' : G y1.2.choose = G y2.2.choose := congrArg Subtype.val h
    apply Subtype.ext
    rw [← y1.2.choose_spec.2, ← y2.2.choose_spec.2]
    exact (hFG _ _).2 h'
  · rintro ⟨_, a, ha, rfl⟩
    refine ⟨⟨F a, a, ha, rfl⟩, Subtype.ext ?_⟩
    exact (hFG _ _).1 (⟨F a, a, ha, rfl⟩ : F '' S).2.choose_spec.2

theorem coe_lowerRamR (t : ℝ) :
    (PkgI6.lowerRamR ℤ_[p] (OE E) t : Set (OE E ≃ₐ[ℤ_[p]] OE E)) = res E '' ramSetR E t := by
  ext s
  constructor
  · intro hs
    obtain ⟨σ, rfl⟩ := res_surjective E s
    exact ⟨σ, (ramSetR_iff E).2 hs, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact (ramSetR_iff E).1 hσ

theorem card_lowerRamR (t : ℝ) :
    Nat.card (PkgI6.lowerRamR ℤ_[p] (OE E) t) = ramCardR E t := by
  rw [← SetLike.coe_sort_coe, coe_lowerRamR, ramCardR]
  refine (card_image_eq (restr E) (res E) (fun a b => ?_) _).symm
  rw [restr_eq_iff', res_eq_iff]
where
  restr_eq_iff' {a b : GQp p} : restr E a = restr E b ↔ ∀ x ∈ E, a x = b x :=
    ⟨fun h x hx => congrFun h ⟨x, hx⟩, fun h => funext fun x => h x x.2⟩

theorem ramCardR_zero : ramCardR E 0 = ramCard E 0 := by
  unfold ramCardR ramSetR ramCard
  rw [if_neg (by norm_num)]
  simp

theorem herbrandPhi_eq : PkgI6.herbrandPhi ℤ_[p] (OE E) = phiAt E := by
  funext u
  unfold PkgI6.herbrandPhi phiAt
  congr 1
  funext t
  rw [card_lowerRamR, card_lowerRamR, ramCardR_zero]

theorem upperSet_iff {σ : GQp p} {v : ℝ} :
    σ ∈ upperSet E v ↔ res E σ ∈ PkgI6.upperRam ℤ_[p] (OE E) v := by
  unfold upperSet PkgI6.upperRam
  rw [herbrandPhi_eq]
  exact ramSetR_iff E

end Galois

/-! ## §4. `HerbrandUpper` from `PkgI6.HerbrandQuotient` -/

section Final

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

instance perfect_residue : PerfectField (IsLocalRing.ResidueField ℤ_[p]) := by
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod p) PadicInt.residueField.symm.toEquiv
  infer_instance

theorem isGalois_frac [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E] :
    IsGalois (FractionRing ℤ_[p]) (FractionRing (OE E)) := by
  refine IsGalois.of_equiv_equiv (F := ℚ_[p]) (E := E)
    (f := (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.toRingEquiv)
    (g := (FractionRing.algEquiv (OE E) E).symm.toRingEquiv) ?_
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
  ext a
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes]
  rw [← IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] E, IsScalarTower.algebraMap_apply ℤ_[p] (OE E) E,
    AlgEquiv.commutes]
  rw [← IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) (FractionRing (OE E)),
    ← IsScalarTower.algebraMap_apply ℤ_[p] (OE E) (FractionRing (OE E))]

instance isSeparable_frac [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E] :
    Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (OE E)) :=
  have := isGalois_frac E
  inferInstance

variable {L M : Fld p}

theorem OE_mono (h : L ≤ M) : OE L ≤ OE M := fun _ hx => ⟨h hx.1, hx.2⟩

/-- Verbatim copy of `Swan.HerbrandUpper` (scratch/swan/Swan.lean §6). -/
def HerbrandUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L M : Fld p), IsFinGal L → IsFinGal M → L ≤ M → ∀ v : ℝ, 0 < v →
    restr L '' upperSet M v = restr L '' upperSet L v

/-- **`HerbrandUpper` from the kernel leaf I6.8** (proved by t-different). -/
theorem herbrandUpper_of_quotient (hHQ : PkgI6.HerbrandQuotient) : HerbrandUpper := by
  intro p _ L M hL hM hLM v _
  have : FiniteDimensional ℚ_[p] L := hL.1
  have : IsGalois ℚ_[p] L := hL.2
  have : FiniteDimensional ℚ_[p] M := hM.1
  have : IsGalois ℚ_[p] M := hM.2
  have := isGalois_frac L
  have := isGalois_frac M
  let _ : Algebra (OE L) (OE M) := (Subalgebra.inclusion (OE_mono hLM)).toRingHom.toAlgebra
  have : IsScalarTower ℤ_[p] (OE L) (OE M) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  have : FaithfulSMul (OE L) (OE M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (Subalgebra.inclusion_injective _)
  have : Module.IsTorsionFree (OE L) (OE M) := FaithfulSMul.to_isTorsionFree (OE L) (OE M)
  -- the restriction `Gal(𝓞_M) → Gal(𝓞_L)`
  have hagree : ∀ σ τ : GQp p, res M σ = res M τ → res L σ = res L τ := fun σ τ h =>
    (res_eq_iff L).2 fun x hx => (res_eq_iff M).1 h x (hLM hx)
  have hsec : ∀ s, res M (Function.surjInv (res_surjective M) s) = s :=
    Function.surjInv_eq (res_surjective M)
  let r : (OE M ≃ₐ[ℤ_[p]] OE M) →* (OE L ≃ₐ[ℤ_[p]] OE L) :=
    { toFun := fun s => res L (Function.surjInv (res_surjective M) s)
      map_one' := by
        rw [← map_one (res L)]
        exact hagree _ _ (by rw [hsec, map_one])
      map_mul' := fun s t => by
        rw [← map_mul (res L)]
        exact hagree _ _ (by rw [hsec, map_mul, hsec, hsec]) }
  have hr_res : ∀ σ, r (res M σ) = res L σ := fun σ => hagree _ _ (hsec _)
  have hr : ∀ s c, algebraMap (OE L) (OE M) (r s c) = s (algebraMap (OE L) (OE M) c) := by
    intro s c
    obtain ⟨σ, rfl⟩ := res_surjective M s
    rw [hr_res]
    apply Subtype.ext
    change ((res L σ c : OE L) : Kbar p) = ((res M σ ⟨c, OE_mono hLM c.2⟩ : OE M) : Kbar p)
    rw [res_apply, res_apply]
  have key := hHQ ℤ_[p] (OE L) (OE M) r hr v
  ext y
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have h1 : res L σ ∈ PkgI6.upperRam ℤ_[p] (OE L) v := by
      rw [key, ← hr_res]
      exact Subgroup.mem_map_of_mem r ((upperSet_iff M).1 hσ)
    exact ⟨σ, (upperSet_iff L).2 h1, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    have h1 := (upperSet_iff L).1 hσ
    rw [key] at h1
    obtain ⟨s, hs, hrs⟩ := h1
    obtain ⟨τ, rfl⟩ := res_surjective M s
    rw [hr_res] at hrs
    refine ⟨τ, (upperSet_iff M).2 hs, funext fun x => ?_⟩
    exact (res_eq_iff L).1 hrs x x.2

end Final

end SwanBridge

end

/-! ## The three glue Props of G15, unconditionally -/

/-- **`SwanIndependent` (every `p`), `SwanIntegral` (L8) and `AdaptedExists` (every `p`) are
theorems**: `Swan.swan_main` with the leaf `HerbrandUpper` discharged by
`SwanBridge.herbrandUpper_of_quotient` from `PkgI6.herbrandQuotient` (t-different's proof of the
kernel leaf I6.8). -/
theorem Swan.swan_proved :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  Swan.swan_main (SwanBridge.herbrandUpper_of_quotient PkgI6.herbrandQuotient)

theorem Swan.swanIndependent_proved (p : ℕ) [Fact p.Prime] : LadicCond.SwanIndependent (p := p) :=
  Swan.swan_proved.1 p

theorem Swan.swanIntegral_proved : LadicCond.SwanIntegral := Swan.swan_proved.2.1

theorem Swan.adaptedExists_proved (p : ℕ) [Fact p.Prime] : LadicCond.AdaptedExists (p := p) :=
  Swan.swan_proved.2.2 p


/-! ## g0-assemble2: unram-tate (scratch/unram-tate/TateBridge.lean lines 1038-1942, verbatim; lines 1-1036 are
g0-mod-field's ModField.lean, i.e. part 75) -/

/-!
# unram-tate: `TateBridge` reduced to named glue pieces

Everything above `end G0ModField` is `scratch/g0-mod-field/ModField.lean` verbatim (lines 1-1036),
so `G0ModField.TateBridge` is the statement as written there. Below: the operators
`ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(φ)` (`opV`, a ring homomorphism, proved), the quaternion matrix units
(`matrixUnits_of_quat`, copied from scratch/unram-tate/QuatUnits.lean), five named glue Props, and
the assembly `tateBridge_of_pieces` (proved).
-/

namespace UnramTate

open G0ModField

/-! ## The Tate functor on additive maps of points -/

section Ops

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]

/-- `A(\bar K)` as an additive group. -/
abbrev PtA : Type := Additive (A.Pt (AlgebraicClosure K))

/-- `ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(φ)` on `Vb A ℓ = ℚ̄_ℓ ⊗ V_ℓ(A)`, for an additive endomorphism `φ` of
`A(\bar K)` (pkg-I3's `Tate.map`, base changed twice). -/
noncomputable def opV (φ : PtA A →+ PtA A) : Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ) :=
  ((PkgI3.Tate.map (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange (PadicAlgCl ℓ)

theorem tateMap_comp (φ ψ : PtA A →+ PtA A) :
    PkgI3.Tate.map (ℓ := ℓ) (φ.comp ψ) = (PkgI3.Tate.map (ℓ := ℓ) φ).comp (PkgI3.Tate.map ψ) := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl

theorem tateMap_add (φ ψ : PtA A →+ PtA A) :
    PkgI3.Tate.map (ℓ := ℓ) (φ + ψ) = PkgI3.Tate.map φ + PkgI3.Tate.map ψ := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl

theorem tateMap_zero : PkgI3.Tate.map (ℓ := ℓ) (0 : PtA A →+ PtA A) = 0 := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl

theorem tateMap_id : PkgI3.Tate.map (ℓ := ℓ) (AddMonoidHom.id (PtA A)) = LinearMap.id := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n; rfl

/-- `opV` is a ring homomorphism `End(A(\bar K)) → End_{ℚ̄_ℓ}(Vb A ℓ)`. -/
noncomputable def opVHom :
    AddMonoid.End (PtA A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ) where
  toFun := opV A ℓ
  map_one' := by
    show opV A ℓ (AddMonoidHom.id _) = 1
    simp only [opV, tateMap_id, LinearMap.baseChange_id]; rfl
  map_mul' f g := by
    show opV A ℓ (f.comp g) = opV A ℓ f * opV A ℓ g
    unfold opV
    rw [tateMap_comp A ℓ f g, LinearMap.baseChange_comp, LinearMap.baseChange_comp]; rfl
  map_zero' := by
    show opV A ℓ 0 = 0
    simp only [opV, tateMap_zero, LinearMap.baseChange_zero]
  map_add' f g := by
    show opV A ℓ (f + g) = opV A ℓ f + opV A ℓ g
    have h1 : PkgI3.Tate.map (ℓ := ℓ) (f + g : AddMonoid.End (PtA A)) =
        PkgI3.Tate.map f + PkgI3.Tate.map g := tateMap_add A ℓ f g
    unfold opV
    rw [h1, LinearMap.baseChange_add, LinearMap.baseChange_add]

/-- The Tate action is `opV` of the Galois action on points. -/
theorem tate_eq_opV (σ : Field.absoluteGaloisGroup K) :
    GaloisCopy.tate A ℓ σ = opV A ℓ (MonoidHom.toAdditive (A.galAct σ)) := rfl

end Ops

/-- Conjugation by an additive equivalence, a ring homomorphism of endomorphism rings. -/
def conjE {M N : Type*} [AddCommGroup M] [AddCommGroup N] (Θ : M ≃+ N) :
    AddMonoid.End M →+* AddMonoid.End N where
  toFun f := Θ.toAddMonoidHom.comp (f.comp Θ.symm.toAddMonoidHom)
  map_one' := DFunLike.ext _ _ fun x => by
    show Θ (Θ.symm x) = x
    exact Θ.apply_symm_apply x
  map_mul' f g := DFunLike.ext _ _ fun x => by
    show Θ (f (g (Θ.symm x))) = Θ (f (Θ.symm (Θ (g (Θ.symm x)))))
    rw [AddEquiv.symm_apply_apply]
  map_zero' := DFunLike.ext _ _ fun x => by
    show Θ 0 = 0
    exact map_zero Θ
  map_add' f g := DFunLike.ext _ _ fun x => by
    show Θ (f (Θ.symm x) + g (Θ.symm x)) = Θ (f (Θ.symm x)) + Θ (g (Θ.symm x))
    exact map_add Θ _ _

theorem conjE_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N] (Θ : M ≃+ N)
    (f : AddMonoid.End M) (x : N) : conjE Θ f x = Θ (f (Θ.symm x)) := rfl

/-! ## Matrix units (copied from scratch/unram-tate/QuatUnits.lean, proved there) -/

section Quat

open GlueDescent

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

theorem quat_words (P J : Module.End E V) (hPP : P * P = P) (hPJ : P * J = J - J * P)
    (hJJ : J * J = (-3 : E) • (1 : Module.End E V)) :
    (∀ X, P * (P * X) = P * X) ∧ (∀ X, P * (J * X) = J * X - J * (P * X)) ∧
      (∀ X, J * (J * X) = (-3 : E) • X) := by
  refine ⟨fun X => by rw [← _root_.mul_assoc, hPP], fun X => by rw [← _root_.mul_assoc, hPJ, sub_mul, _root_.mul_assoc],
    fun X => by rw [← _root_.mul_assoc, hJJ, smul_mul_assoc, _root_.one_mul]⟩

theorem matrixUnits_of_quat (s : E) (hs : s ^ 2 = 2) (h2 : (2 : E) ≠ 0) (h3 : (3 : E) ≠ 0)
    (I J : Module.End E V) (hI : I * I = (2 : E) • (1 : Module.End E V))
    (hJ : J * J = (-3 : E) • (1 : Module.End E V)) (hIJ : I * J = -(J * I)) :
    ∃ u : MatrixUnits2 E V, ∀ (i j : Fin 2) (T : Module.End E V), Commute T I → Commute T J →
      Commute T (u.e i j) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact h2 hs.symm
  set X : Module.End E V := s⁻¹ • I with hXdef
  have hXX : X * X = 1 := by
    rw [hXdef, smul_mul_smul_comm, hI, smul_smul]
    have : s⁻¹ * s⁻¹ * 2 = 1 := by rw [← hs]; field_simp
    rw [this, one_smul]
  have hXJ : X * J = -(J * X) := by
    rw [hXdef, smul_mul_assoc, hIJ, mul_smul_comm, smul_neg]
  set P : Module.End E V := (2 : E)⁻¹ • (1 + X) with hPdef
  have hPP : P * P = P := by
    rw [hPdef, smul_mul_smul_comm, add_mul, _root_.one_mul, mul_add, _root_.mul_one, hXX]
    rw [show (1 + X + (X + 1) : Module.End E V) = (2 : E) • (1 + X) by
      rw [two_smul]; abel, smul_smul]
    congr 1; field_simp
  have hPJ : P * J = J - J * P := by
    rw [hPdef, smul_mul_assoc, mul_smul_comm, add_mul, _root_.one_mul, hXJ, mul_add, _root_.mul_one]
    have h12 : (1 : E) - 2⁻¹ = 2⁻¹ := by field_simp; norm_num
    rw [show J - (2 : E)⁻¹ • (J + J * X) = ((1 : E) - 2⁻¹) • J + (2 : E)⁻¹ • (-(J * X)) by module,
      h12, ← smul_add]
  obtain ⟨wPP, wPJ, wJJ⟩ := quat_words P J hPP hPJ hJ
  let c : E := -(3 : E)⁻¹
  let e : Fin 2 → Fin 2 → Module.End E V := fun i j =>
    if i = 0 then (if j = 0 then P else P * J) else (if j = 0 then c • (J * P) else 1 - P)
  have hc : c * (-3 : E) = 1 := by simp only [c]; field_simp
  refine ⟨⟨e, ?_, ?_⟩, ?_⟩
  · intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp only [e, Fin.zero_eta, Fin.mk_one, Fin.isValue, ite_true, one_ne_zero, zero_ne_one,
        ite_false, _root_.mul_assoc, mul_sub, sub_mul, _root_.mul_one, _root_.one_mul, smul_mul_assoc, mul_smul_comm,
        wPP, wPJ, wJJ, hPP, hPJ, hJ, smul_smul, smul_sub, sub_self, hc, one_smul, mul_zero,
        smul_zero, sub_zero, zero_sub, add_zero, zero_add, neg_zero] <;>
      first | rfl | abel | (simp only [sub_sub_cancel, sub_self, smul_zero]) | skip
  · show P + (1 - P) = 1
    abel
  · intro i j T hTI hTJ
    have hTX : Commute T X := hTI.smul_right _
    have hTP : Commute T P := ((Commute.one_right T).add_right hTX).smul_right _
    fin_cases i <;> fin_cases j
    · exact hTP
    · exact hTP.mul_right hTJ
    · exact (hTJ.mul_right hTP).smul_right _
    · exact (Commute.one_right T).sub_right hTP

end Quat

/-! ## The order elements `i`, `j` of `𝒪` -/

/-- `i ∈ 𝒪`. -/
def iO : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `(1 + j)/2 ∈ 𝒪`. -/
def hO : LeafQM.O := ⟨LeafQM.ofInt ![0, 0, 1, 0], ⟨_, rfl⟩⟩
/-- `j = 2·(1+j)/2 - 1 ∈ 𝒪`. -/
def jO : LeafQM.O := hO + hO - 1

theorem iO_sq : iO * iO = 1 + 1 := by
  apply Subtype.ext
  simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_one, iO]
  ext <;> simp [LeafQM.ofInt] <;> norm_num

theorem jO_sq : jO * jO = -(1 + 1 + 1) := by
  apply Subtype.ext
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, Subring.coe_add, Subring.coe_neg,
    Subring.coe_one, jO, hO]
  ext <;> simp [LeafQM.ofInt] <;> norm_num

theorem iO_jO : iO * jO = -(jO * iO) := by
  apply Subtype.ext
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, Subring.coe_add, Subring.coe_neg,
    Subring.coe_one, jO, hO, iO]
  ext <;> simp [LeafQM.ofInt] <;> norm_num

/-! ## The named glue pieces -/

/-- **Glue piece TB-i (points of a base change; `\overline{L'} ≅ ℚ̄` over `L'`).** For
`L ≤ L'` with `L'/ℚ` finite Galois and `A/L`: an additive bijection
`Θ : A(ℚ̄) ≅ A_{L'}(\overline{L'})` and `h ∈ G_ℚ` such that `Θ` carries the action of
`h · resQ(σ) · h⁻¹` on `A(ℚ̄)` (an `L`-automorphism of `ℚ̄`) to the action of `σ ∈ G_{L'}` on
`A_{L'}(\overline{L'})`. Proof plan: `A_{L'}(Ω) = A(Ω)` for every `L'`-algebra `Ω` (universal
property of `Over.pullback`, compatible with the group law since the pullback functor is
monoidal), and `Θ` is induced by an `L'`-isomorphism `φ : \overline{L'} ≅ ℚ̄`
(`IsAlgClosure.equiv`); then `h = φ ∘ g` for the embedding `g : ℚ̄ → \overline{L'}` of
`Field.absoluteGaloisGroup.map` (`resQ_comm'`). Not in Mathlib v4.35 as such. -/
def TatePoints : Prop :=
  ∀ (L L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L') (A : PkgI3.AbVar L),
    ∃ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      ∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)

/-- **Glue piece TB-ii (base change of endomorphisms).** For `K ≤ L` and `A/K`, a ring
homomorphism `End_K(A) → End_L(A_L)` (`f ↦ f_L`: `Over.pullback` is a monoidal functor, so it
maps monoid morphisms to monoid morphisms and preserves composition, identities and the
pointwise sum). -/
def EndBaseChange : Prop :=
  ∀ (K L : IF) (hKL : K ≤ L) (A : PkgI3.AbVar K),
    Nonempty (PkgI3.AbVar.End A →+*
      PkgI3.AbVar.End (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)))

/-- **Glue piece TB-iii (scalars into `ℚ̄_ℓ`; algebra).** The data of B1/B2 (`a > 0` real,
`c = n/d`, `ε`, `β` complex, with `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}` and `∂β = ε`, both constant
on cosets of the open subgroup `G_{L'}` and `1` on it) give `gam : G_ℚ → ℚ̄_ℓ^×` with `∂gam = c`,
constant on `G_{L'}`-cosets and `1` on `G_{L'}`. Proof plan: `gam_ℂ = β/a` satisfies
`gam_σ gam_τ = c(σ,τ) gam_{στ}`; it takes finitely many values (cosets of `G_{L'}`, finite index),
each algebraic (`gam_σ^r ∈ ℚ^×` for `σ^r ∈ G_{L'}`), so they generate a number field
`F ⊆ ℂ`; embed `F → ℚ̄_ℓ` (`IsAlgClosed.lift`). -/
def ScalarTransfer : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (ℓ : ℕ) [Fact ℓ.Prime] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ),
    (∀ σ τ, d σ τ ≠ 0) →
    (∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
    (∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ)) →
    (∀ σ, 0 < a σ) →
    (∀ σ, ∀ k ∈ GQL L', a (σ * k) = a σ ∧ β (σ * k) = β σ) →
    (∀ k ∈ GQL L', a k = 1 ∧ β k = 1) →
    ∃ gam : GQ → PadicAlgCl ℓ, (∀ σ, gam σ ≠ 0) ∧
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ)) ∧
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) ∧ (∀ k ∈ GQL L', gam k = 1)

/-- **Glue piece TB-iv (continuity of the Tate representation over `ℚ̄_ℓ`).** For a number
field `K` and `A/K`, every matrix coefficient `σ ↦ f(ρ_ℓ(σ) v)` of `ℚ̄_ℓ ⊗ V_ℓ(A)` is continuous
on `G_K`. From glue-rho-cont (`ZInQKernel/HDecomp/I3Linalg/RhoCont.lean`,
`continuous_galRep_of_tateModuleFree`: continuity on `V_ℓ(A)`, given the leaf I3.M0
`TateModuleFree`) and the finite dimension of `V_ℓ(A)` (same leaf). -/
def TateCont : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (f : Module.Dual (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ)) (v : GaloisCopy.Vb A ℓ),
    Continuous fun σ : Field.absoluteGaloisGroup K => f (GaloisCopy.tate A ℓ σ v)

/-- **Glue piece TB-v (Galois topology).** For finite Galois `L' ⊆ ℚ̄`, `resQ L' : G_{L'} → G_ℚ`
is an open embedding (continuous by Mathlib, `Field.absoluteGaloisGroup.map` is a continuous
homomorphism; injective; `G_{L'}` compact, `G_ℚ` Hausdorff; image `Fix(L')` open, `ResQRange`). -/
def ResQEmbedding : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'],
    Topology.IsOpenEmbedding (@GaloisCopy.resQ L' _ (numberField_of_fd L'))

/-! ## The assembly -/

/-- `ε(σ, k) = 1` for `k ∈ G_L` (inflation and normalization). -/
theorem eps_right_one (L : IF) (ε : GQ → GQ → ℂˣ) (hεc : IsSignCocycle ε)
    (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1) (σ k : GQ) (hk : k ∈ GQL L) : ε σ k = 1 := by
  have h1 : ε σ k = ε σ 1 :=
    hinf σ σ k 1 (fun _ _ => rfl) (fun x hx => by rw [mem_GQL.mp hk x hx]; rfl)
  have h2 := hεc.2.2 σ 1 1
  rw [_root_.mul_one, _root_.one_mul, h11, _root_.one_mul] at h2
  rw [h1]
  exact mul_left_cancel (a := ε σ 1) (by rw [h2, _root_.mul_one])

set_option maxHeartbeats 1000000 in
/-- **`TateBridge` from the five glue pieces** (and the proved `opVHom`, `matrixUnits_of_quat`,
`resQRange`, glue-descent's `rho_map_mul`). `Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`,
`c = ε' = n/d` at `(hgh⁻¹, hg'h⁻¹)`, `a = 1`, `β' g = gam(hgh⁻¹)`; the matrix units are those of
`I, J`, the images of `i, j ∈ 𝒪` under `opV(Θ ∘ (QM action on A(ℚ̄)) ∘ Θ⁻¹)`. -/
theorem tateBridge_of_pieces (hP : TatePoints) (hE : EndBaseChange) (hS : ScalarTransfer)
    (hC : TateCont) (hR : ResQEmbedding) : TateBridge := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank ℓ _
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, -⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(hE K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := hP L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gam, hgam0, hgamc, hgamcos, hgam1⟩ := hS L' ℓ a β ε n d hd hna hβe ha0
    (fun σ k hk => ⟨(haL σ k (hLL'G k hk)).2.1, by
      have := hβe σ k
      rw [hβL' k hk, _root_.mul_one, eps_right_one L ε hεc hinf h11 σ k (hLL'G k hk),
        _root_.one_mul] at this
      exact this.symm⟩)
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  -- notation
  let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
    (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
  let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
  have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
    show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
    group
  let m' : GQ → AddMonoid.End (PtQ L A) := m
  let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
  let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
    ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
  let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => 1
  let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => gam (cj g)
  -- matrix units
  let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
    R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
  have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
    rw [← map_mul, iO_sq, map_add, map_one, two_smul]
  have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
    rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
    module
  have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
    rw [← map_mul, iO_jO, map_neg, map_mul]
  obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
  have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
    intro g o
    apply Commute.map _ R
    exact hmEnd (cj g) (iot o)
  -- the relations
  have hT : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
    intro g g₂
    have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
      hnd (cj g) (cj g₂)
    have h1 := congrArg R h0
    rw [map_zsmul, map_zsmul, ← hcj] at h1
    have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
      show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
      rw [← map_mul]; exact h1
    have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
        (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
      (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
        (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
    have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
    show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
    rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
    intro g g₂; simp only [a', _root_.one_mul, _root_.mul_one]
  have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
    intro g g₂; simp only [β', c']; rw [hcj]; exact hgamc _ _
  have hβ0 : ∀ g, β' g ≠ 0 := fun g => hgam0 _
  -- `G_{L'}` is normal
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hres : ∀ σ : Field.absoluteGaloisGroup L',
      cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
    intro σ
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
  have hTres : ∀ σ : Field.absoluteGaloisGroup L',
      Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
    intro σ
    have hτ := hres σ
    let σ' : Qbar ≃ₐ[L] Qbar :=
      AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
        (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
    have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
    rw [tate_eq_opV]
    show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
    congr 1
    refine DFunLike.ext _ _ fun x => ?_
    show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
    rw [hm]
    show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
    rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
  have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
      GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
    intro σ
    unfold GlueDescent.rho
    rw [hTres σ]
    simp only [β', a', hgam1 _ (hres σ), inv_one, _root_.mul_one, one_smul]
  refine ⟨Tm, c', c', a', β', uu, _hdim, _hrank, hT, ha, hβ, hβ0, fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
    fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
  -- continuity
  intro f v
  rw [continuous_iff_continuousAt]
  intro g₀
  let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
  have he₀ : Topology.IsOpenEmbedding e₀ :=
    (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
  have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
  have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
      fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
    funext σ
    simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
    rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hT ha hβ hβ0, hrho1, Module.End.mul_apply]
  have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
    rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
  rw [he₀.continuousAt_iff, he₀1] at hc
  exact hc

/-! ## Proofs of two pieces -/

/-- **`ResQEmbedding`, proved** (Mathlib Galois topology): `resQ L'` is continuous, injective
(the embedding `g : ℚ̄ → \overline{L'}` of `resQ_comm'` is onto), `G_{L'}` is compact, so it is a
closed embedding, with open image `Fix(L')` (`resQRange`). -/
theorem resQEmbedding : ResQEmbedding := by
  intro L' _ _
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hIG : IsGalois L' (AlgebraicClosure L') := {}
  haveI : CompactSpace (Field.absoluteGaloisGroup L') :=
    (inferInstance : CompactSpace (AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L'))
  have hcont : Continuous (@GaloisCopy.resQ L' _ hNF) :=
    (Field.absoluteGaloisGroup.map (algebraMap ℚ L')).continuous_toFun
  obtain ⟨g0, hcomm⟩ := resQ_comm' L'
  let g : Qbar →ₐ[ℚ] AlgebraicClosure L' := g0.toRatAlgHom
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L') := by
    haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
    haveI : Algebra.IsAlgebraic L' (AlgebraicClosure L') := AlgebraicClosure.isAlgebraic L'
    exact Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure L') := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure L') :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L') := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure L') := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hinj : Function.Injective (@GaloisCopy.resQ L' _ hNF) := by
    intro σ τ hστ
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := hgbij.2 y
    have h1 := hcomm σ x
    have h2 := hcomm τ x
    rw [hστ] at h1
    exact h1.symm.trans h2
  refine ⟨(hcont.isClosedEmbedding hinj).isEmbedding, ?_⟩
  rw [← MonoidHom.coe_range, resQRange L']
  exact IntermediateField.fixingSubgroup_isOpen L'

set_option maxHeartbeats 1000000 in
/-- **`TateCont`, proved from the leaf I3.M0 `TateModuleFree`** (Mumford §18-19; pkg-I3) and
glue-rho-cont's `continuous_galRep_of_tateModuleFree`: on `ℚ̄_ℓ ⊗ V_ℓ(A)`, `f(ρ(σ)(c ⊗ w)) =
c · f(1 ⊗ ρ_ℓ(σ) w)` and `w ↦ f(1 ⊗ w)` is `ℚ_ℓ`-linear, hence continuous for the module
topology of `V_ℓ(A)`. -/
theorem tateCont_of_tateModuleFree (hT : PkgI3.TateModuleFree) : TateCont := by
  intro K _ _ A ℓ _ f v
  have hℓ : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hρ := (PkgI3.continuous_galRep_of_tateModuleFree hT A ℓ hℓ).1
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact continuous_const
  | tmul c w =>
    let g : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ :=
      (f.restrictScalars ℚ_[ℓ]).comp (TensorProduct.mk ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) 1)
    have hg : Continuous g := IsModuleTopology.continuous_of_linearMap g
    have heq : (fun σ : Field.absoluteGaloisGroup K => f (GaloisCopy.tate A ℓ σ (c ⊗ₜ w))) =
        fun σ => c * g (A.galRep ℓ σ w) := by
      funext σ
      show f ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) (c ⊗ₜ w)) = _
      rw [LinearMap.baseChange_tmul]
      have : c ⊗ₜ[ℚ_[ℓ]] (A.galRep ℓ σ w) = c • ((1 : PadicAlgCl ℓ) ⊗ₜ[ℚ_[ℓ]] (A.galRep ℓ σ w)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this, map_smul, smul_eq_mul]
      rfl
    have h3 := hρ.comp (Continuous.prodMk_left (X := Field.absoluteGaloisGroup K) w)
    have h4 := hg.comp h3
    rw [heq]
    exact continuous_const.mul h4
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

/-- **`ScalarTransfer`, proved** (algebra, no leaf). `γ_ℂ = β/a` has `∂γ_ℂ = n/d`, is constant
on `G_{L'}`-cosets and `1` on `G_{L'}`; `γ_ℂ(σ)^r ∈ ℚ` for `σ^r ∈ G_{L'}` (`r` the order of
`σ|_{L'}`), so every value is algebraic; `ψ : ℚ(γ_ℂ(G_ℚ)) → ℚ̄_ℓ` (`IsAlgClosed.lift`) and
`γ = ψ ∘ γ_ℂ`. -/
theorem scalarTransfer : ScalarTransfer := by
  intro L' _ _ ℓ _ a β ε n d hd hna hβe ha0 hcos hone
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) / ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
  have hgcos : ∀ σ, ∀ k ∈ GQL L', gC (σ * k) = gC σ := by
    intro σ k hk; simp only [gC]; rw [(hcos σ k hk).1, (hcos σ k hk).2]
  have hg1 : ∀ k ∈ GQL L', gC k = 1 := by
    intro k hk; simp only [gC]; rw [(hone k hk).1, (hone k hk).2]; simp
  have hg0 : ∀ σ, gC σ ≠ 0 := fun σ => div_ne_zero (Units.ne_zero _) (ha0' σ)
  have hpow : ∀ (σ : GQ) (k : ℕ), ∃ r : ℚ, gC σ ^ k = (r : ℂ) * gC (σ ^ k) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, hg1 1 (one_mem _)]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q (σ ^ k) σ, ?_⟩
      rw [pow_succ, hr, _root_.mul_assoc, hq, pow_succ]
      push_cast; ring
  have hfin : ∀ σ : GQ, ∃ r : ℕ, 0 < r ∧ σ ^ r ∈ GQL L' := by
    intro σ
    let σ' : Qbar ≃ₐ[ℚ] Qbar := σ
    let s := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' σ'
    have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
    refine ⟨orderOf s, hs.orderOf_pos, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' (σ' ^ orderOf s) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L' _).mp h1 x hx
  have halg : ∀ σ, IsIntegral ℚ (gC σ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨t, ht⟩ := hpow σ r
    rw [hg1 _ hr, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ r - Polynomial.C t, Polynomial.monic_X_pow_sub_C t hr0.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ht]
  let F : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range gC)
  haveI : Algebra.IsAlgebraic ℚ F := IntermediateField.isAlgebraic_adjoin (by
    rintro x ⟨σ, rfl⟩; exact halg σ)
  let ψ : F →ₐ[ℚ] PadicAlgCl ℓ := IsAlgClosed.lift
  have hmem : ∀ σ, gC σ ∈ F := fun σ => IntermediateField.subset_adjoin ℚ _ ⟨σ, rfl⟩
  let gam : GQ → PadicAlgCl ℓ := fun σ => ψ ⟨gC σ, hmem σ⟩
  refine ⟨gam, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    have : (⟨gC σ, hmem σ⟩ : F) = 0 := ψ.toRingHom.injective (h0.trans (map_zero ψ).symm)
    exact congrArg Subtype.val this
  · intro σ τ
    have hF : (⟨gC σ, hmem σ⟩ : F) * ⟨gC τ, hmem τ⟩ =
        algebraMap ℚ F (q σ τ) * ⟨gC (σ * τ), hmem (σ * τ)⟩ := Subtype.ext (hq σ τ)
    show ψ _ * ψ _ = _ * ψ _
    rw [← map_mul, hF, map_mul, AlgHom.commutes]
    congr 1
    simp only [q, map_div₀, map_intCast]
  · intro σ k hk
    exact congrArg ψ (Subtype.ext (hgcos σ k hk))
  · intro k hk
    show ψ _ = 1
    rw [← map_one ψ]
    exact congrArg ψ (Subtype.ext (hg1 k hk))

/-- **`TateBridge` from the two remaining glue pieces and the leaf I3.M0** (`TateModuleFree`). -/
theorem tateBridge_of_points (hP : TatePoints) (hE : EndBaseChange)
    (hT : PkgI3.TateModuleFree) : TateBridge :=
  tateBridge_of_pieces hP hE scalarTransfer (tateCont_of_tateModuleFree hT) resQEmbedding

/-! ## `EndBaseChange` (proof copied from scratch/bp-qmmoduli/QMAbVar.lean L533-557, `endBC`) -/

section BaseChangeEnd

variable {K : Type} [Field K]

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (copied verbatim from bp-qmmoduli's `endBC`):
`End_K(A) → End_L(A_L)`, `f ↦ (Over.pullback (Spec L → Spec K)).map f`, a ring homomorphism
(functoriality, and `Functor.map_mul` for the monoidal functor `Over.pullback`). -/
noncomputable def endBC (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    PkgI3.AbVar.End A →+* PkgI3.AbVar.End (A.baseChange L) where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl

end BaseChangeEnd

/-- **`EndBaseChange`, proved** (bp-qmmoduli's `endBC`). -/
theorem endBaseChange : EndBaseChange := fun K L hKL A =>
  ⟨@endBC K _ A L _ (incAlg hKL)⟩

/-- **`TateBridge` from the one remaining glue piece `TatePoints` and the leaf I3.M0**
(`PkgI3.TateModuleFree`, Mumford). -/
theorem tateBridge_of_tatePoints (hP : TatePoints) (hT : PkgI3.TateModuleFree) : TateBridge :=
  tateBridge_of_points hP endBaseChange hT

/-! ## `TatePoints` (generic parts copied from scratch/unram-tate/BCPoints.lean) -/

section BCPoints

open scoped CategoryTheory.Obj

/-- `Spec L → Spec K`. -/
noncomputable abbrev sK (K L : Type) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

theorem specMap_comp_sK :
    Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ sK K L =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K L Ω]

/-- `Over.map (Spec L → Spec K) (Spec Ω / L) ≅ Spec Ω / K`. -/
noncomputable def ptMapIso :
    (Over.map (sK K L)).obj (PkgI3.AbVar.ptObj (K := L) Ω) ≅ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, PkgI3.AbVar.ptObj, Over.mk_hom]
    erw [Category.id_comp]
    exact (specMap_comp_sK (K := K) (L := L) Ω).symm)

/-- The adjunction bijection is multiplicative. -/
theorem homEquiv_mul (X : Over (Spec (CommRingCat.of L)))
    (p q : (Over.map (sK K L)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (sK K L)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (sK K L)).homEquiv X A.X p *
        (Over.mapPullbackAdj (sK K L)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- **Points of a base change**: `A_L(Ω) ≃* A(Ω)`. -/
noncomputable def bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω where
  toFun p := (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  invFun x := (Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)
  left_inv p := Equiv.apply_symm_apply ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X) p
  right_inv x := by
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)) = x
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  map_mul' p q := by
    obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective p
    obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective q
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
        ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X p' *
          (Over.mapPullbackAdj (sK K L)).homEquiv _ A.X q') = _
    rw [← homEquiv_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      MonObj.comp_mul]

/-- `bcPt` is natural for `L`-automorphisms of `Ω`. -/
theorem bcPt_galAct (σ : Ω ≃ₐ[L] Ω) (p : (A.baseChange L).Pt Ω) :
    bcPt A Ω ((A.baseChange L).galAct σ p) = A.galAct (σ.restrictScalars K) (bcPt A Ω p) := by
  show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      (PkgI3.AbVar.galHom σ ≫ p) =
    PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv ≫
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  have hnat := Adjunction.homEquiv_naturality_left_symm (Over.mapPullbackAdj (sK K L))
    (PkgI3.AbVar.galHom σ) (p : PkgI3.AbVar.ptObj Ω ⟶ (Over.pullback (sK K L)).obj A.X)
  have hsq : (ptMapIso Ω).inv ≫ (Over.map (sK K L)).map (PkgI3.AbVar.galHom σ) =
      PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv := by
    apply Over.OverMorphism.ext
    simp [ptMapIso, PkgI3.AbVar.galHom]
    rfl
  erw [hnat]
  rw [← Category.assoc, hsq, Category.assoc]

end BC

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-isomorphism `φ : Ω ≃ Ω₂`. -/
noncomputable def trHom (φ : Ω ≃ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem trHom_left (φ : Ω ≃ₐ[K] Ω₂) :
    (trHom φ).left = Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) := rfl

theorem trHom_symm_comp (φ : Ω ≃ₐ[K] Ω₂) : trHom φ.symm ≫ trHom φ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (φ.symm : Ω₂ →+* Ω)) ≫
    Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) = 𝟙 (Spec (CommRingCat.of Ω))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (φ.symm : Ω₂ →+* Ω).comp (φ : Ω →+* Ω₂) = RingHom.id Ω by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

theorem trHom_comp_symm (φ : Ω ≃ₐ[K] Ω₂) : trHom φ ≫ trHom φ.symm = 𝟙 _ := by
  simpa using trHom_symm_comp φ.symm

/-- **Transport of points** along `φ : Ω ≃ₐ[K] Ω₂`. -/
noncomputable def trPt (φ : Ω ≃ₐ[K] Ω₂) : A.Pt Ω ≃* A.Pt Ω₂ where
  toFun p := trHom φ ≫ p
  invFun x := trHom φ.symm ≫ x
  left_inv p := by simp [← Category.assoc, trHom_symm_comp]
  right_inv x := by simp [← Category.assoc, trHom_comp_symm]
  map_mul' p q := MonObj.comp_mul _ _ _

/-- `trPt φ` carries the action of `σ` to that of `φσφ⁻¹`. -/
theorem trPt_galAct (φ : Ω ≃ₐ[K] Ω₂) (σ : Ω ≃ₐ[K] Ω) (σ₂ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, σ₂ (φ x) = φ (σ x)) (p : A.Pt Ω) :
    trPt A φ (A.galAct σ p) = A.galAct σ₂ (trPt A φ p) := by
  show trHom φ ≫ PkgI3.AbVar.galHom σ ≫ p = PkgI3.AbVar.galHom σ₂ ≫ trHom φ ≫ p
  have hsq : trHom φ ≫ PkgI3.AbVar.galHom σ = PkgI3.AbVar.galHom σ₂ ≫ trHom φ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ₂ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, ← Category.assoc, hsq]

end Tr


/-- **`TatePoints`, proved.** `Θ = (trPt φ ∘ bcPt)⁻¹` for `φ : \overline{L'} ≃ₐ[L'] ℚ̄`
(`IsAlgClosure.equiv`), and `h = φ ∘ g` for the onto embedding `g : ℚ̄ → \overline{L'}` of
`resQ_comm'`, so that `h · resQ σ · h⁻¹ = φ σ φ⁻¹`. -/
theorem tatePoints : TatePoints := by
  intro L L' _ _ hLL' A
  haveI hNF : NumberField L' := numberField_of_fd L'
  letI iLL' : Algebra L L' := incAlg hLL'
  haveI tLΩ : IsScalarTower L L' (AlgebraicClosure L') := inferInstance
  haveI tLQ : IsScalarTower L L' Qbar := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsAlgebraic L' Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L'
  haveI : IsAlgClosure L' Qbar := ⟨inferInstance, inferInstance⟩
  let φ : AlgebraicClosure L' ≃ₐ[L'] Qbar := IsAlgClosure.equiv L' (AlgebraicClosure L') Qbar
  let φL : AlgebraicClosure L' ≃ₐ[L] Qbar := φ.restrictScalars L
  obtain ⟨g0, hcomm⟩ := resQ_comm' L'
  let g : Qbar →ₐ[ℚ] AlgebraicClosure L' := g0.toRatAlgHom
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L') := by
    haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
    haveI : Algebra.IsAlgebraic L' (AlgebraicClosure L') := AlgebraicClosure.isAlgebraic L'
    exact Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure L') := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure L') :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L') := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure L') := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ge : Qbar ≃+* AlgebraicClosure L' := RingEquiv.ofBijective g0 hgbij
  let hR : Qbar ≃+* Qbar := ge.trans φ.toRingEquiv
  let h : PkgI4.GQ := AlgEquiv.ofRingEquiv (f := hR) (fun q => by
    rw [eq_ratCast (algebraMap ℚ Qbar) q, map_ratCast])
  have hh : ∀ y, h y = φ (g0 y) := fun _ => rfl
  let E := (bcPt (K := L) (L := L') A (AlgebraicClosure L')).trans (trPt A φL)
  refine ⟨E.symm.toAdditive, h, ?_⟩
  intro σ σ' hσ' x
  have hkey : ∀ z, σ' (φL z) = φL ((actK σ).restrictScalars L z) := by
    intro z
    rw [hσ']
    have hinv : h⁻¹ (φ z) = ge.symm z := by
      apply h.injective
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, hh]
      show φ z = φ (g0 (ge.symm z))
      rw [show g0 (ge.symm z) = z from ge.apply_symm_apply z]
    have hres : (@GaloisCopy.resQ L' _ hNF σ) (ge.symm z) = ge.symm (actK σ z) := by
      apply ge.injective
      rw [ge.apply_symm_apply]
      have := hcomm σ (ge.symm z)
      rw [show g0 (ge.symm z) = z from ge.apply_symm_apply z] at this
      exact this
    show h ((@GaloisCopy.resQ L' _ hNF σ) (h⁻¹ (φ z))) = φ (actK σ z)
    rw [hinv, hres, hh]
    show φ (g0 (ge.symm (actK σ z))) = φ (actK σ z)
    rw [show g0 (ge.symm (actK σ z)) = actK σ z from ge.apply_symm_apply (actK σ z)]
  show Additive.ofMul (E.symm (A.galAct σ' (Additive.toMul x))) =
    Additive.ofMul ((A.baseChange L').galAct (actK σ) (E.symm (Additive.toMul x)))
  congr 1
  apply E.injective
  rw [MulEquiv.apply_symm_apply]
  show A.galAct σ' (Additive.toMul x) = trPt A φL (bcPt A (AlgebraicClosure L')
    ((A.baseChange L').galAct (actK σ) (E.symm (Additive.toMul x))))
  rw [bcPt_galAct, trPt_galAct A φL ((actK σ).restrictScalars L) σ' hkey]
  congr 1
  exact (E.apply_symm_apply (Additive.toMul x)).symm

end BCPoints

/-- **`TateBridge` from the leaf I3.M0 alone** (`PkgI3.TateModuleFree`, Mumford §18-19). -/
theorem tateBridge_of_tateModuleFree (hT : PkgI3.TateModuleFree) : TateBridge :=
  tateBridge_of_tatePoints tatePoints hT

/-! ## `UnramifiedSup` in this context (proof copied from scratch/unram-tate/UnramSup.lean) -/

section Sup

open NumberField

instance instGaloisQbar' : IsGalois ℚ (AlgebraicClosure ℚ) := {}

/-- A finite intermediate field is a number field. -/
theorem numberField_of_fd'' (L : IF) [FiniteDimensional ℚ L] : NumberField L :=
  { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

/-- For a finite Galois `L` unramified at `p` and a prime `P ∋ p` of `𝓞 L`, the inertia group
`I(P) ≤ Gal(L/ℚ)` is trivial (`#I(P) = e(P) = 1`). -/
theorem inertia_trivial' (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (p : ℕ)
    (hL : UnramifiedAt L p) (P : Ideal (𝓞 L)) [hP : P.IsPrime] (hpP : ((p : ℤ) : 𝓞 L) ∈ P)
    (g : L ≃ₐ[ℚ] L) (hg : g ∈ P.inertia (L ≃ₐ[ℚ] L)) : g = 1 := by
  haveI : NumberField L := numberField_of_fd'' L
  have he : P.ramificationIdx ℤ = 1 := hL P hP hpP
  have hcard : Nat.card (P.inertia (L ≃ₐ[ℚ] L)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (P.under ℤ) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P (L ≃ₐ[ℚ] L), he]
  have hsub : Subsingleton (P.inertia (L ≃ₐ[ℚ] L)) := (Nat.card_eq_one_iff_unique.mp hcard).1
  have := Subsingleton.elim (⟨g, hg⟩ : P.inertia (L ≃ₐ[ℚ] L)) 1
  exact congrArg Subtype.val this

/-- `𝓞 E → 𝓞 M` for `E ≤ M`. -/
noncomputable def incO' {E M : IF} (h : E ≤ M) : 𝓞 E →+* 𝓞 M :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom

theorem incO'_coe {E M : IF} (h : E ≤ M) (x : 𝓞 E) :
    (((incO' h x : 𝓞 M) : M) : Qbar) = ((x : E) : Qbar) := rfl

/-- **Restriction of inertia.** If `E ≤ M` are finite Galois, `E` unramified at `p`, `Q ∋ p` a
prime of `𝓞 M` and `g ∈ I(Q)`, then a lift `s ∈ G_ℚ` of `g` fixes `E` pointwise. -/
theorem lift_fixes' (E M : IF) [FiniteDimensional ℚ E] [FiniteDimensional ℚ M] [IsGalois ℚ E]
    [IsGalois ℚ M] (hEM : E ≤ M) (p : ℕ) (hE : UnramifiedAt E p) (Q : Ideal (𝓞 M))
    [hQ : Q.IsPrime] (hpQ : ((p : ℤ) : 𝓞 M) ∈ Q) (g : M ≃ₐ[ℚ] M)
    (hg : g ∈ Q.inertia (M ≃ₐ[ℚ] M)) (s : Qbar ≃ₐ[ℚ] Qbar)
    (hs : ∀ y : M, s (y : Qbar) = ((g y : M) : Qbar)) :
    ∀ x ∈ E, s x = x := by
  let QE : Ideal (𝓞 E) := Q.comap (incO' hEM)
  haveI : QE.IsPrime := Ideal.comap_isPrime _ _
  have hpQE : ((p : ℤ) : 𝓞 E) ∈ QE := by
    show incO' hEM ((p : ℤ) : 𝓞 E) ∈ Q
    rw [map_intCast]; exact hpQ
  let gE : E ≃ₐ[ℚ] E := s.restrictNormal E
  have hgE : ∀ x : E, ((gE x : E) : Qbar) = s (x : Qbar) :=
    fun x => AlgEquiv.restrictNormal_commutes s E x
  have hmem : gE ∈ QE.inertia (E ≃ₐ[ℚ] E) := by
    rw [Ideal.mem_inertia]
    intro x
    show incO' hEM (gE • x - x) ∈ Q
    have hx : incO' hEM (gE • x) = g • incO' hEM x := by
      apply Subtype.ext; apply Subtype.ext
      show ((gE (x : E) : E) : Qbar) = ((g ((incO' hEM x : 𝓞 M) : M) : M) : Qbar)
      rw [hgE, ← hs]; rfl
    rw [map_sub, hx]
    exact (Ideal.mem_inertia.mp hg) (incO' hEM x)
  have h1 := inertia_trivial' E p hE QE hpQE gE hmem
  intro x hx
  have := hgE ⟨x, hx⟩
  rw [h1] at this
  exact this.symm

/-- **`UnramifiedSup`, proved** (no leaf). -/
theorem unramifiedSup_mf : G0ModField.UnramifiedSup := by
  intro E K _ _ _ _ p hE hK
  let M : IF := E ⊔ K
  haveI : FiniteDimensional ℚ M := inferInstance
  haveI : IsGalois ℚ M := IsGalois.mk
  haveI : NumberField M := numberField_of_fd'' M
  intro Q hQ hpQ
  have htriv : ∀ g ∈ Q.inertia (M ≃ₐ[ℚ] M), g = 1 := by
    intro g hg
    let s : Qbar ≃ₐ[ℚ] Qbar := g.liftNormal Qbar
    have hs : ∀ y : M, s (y : Qbar) = ((g y : M) : Qbar) :=
      fun y => AlgEquiv.liftNormal_commutes g Qbar y
    have hEf := lift_fixes' E M le_sup_left p hE Q hpQ g hg s hs
    have hKf := lift_fixes' K M le_sup_right p hK Q hpQ g hg s hs
    have hE' : E ≤ IntermediateField.fixedField (Subgroup.zpowers s) :=
      (IntermediateField.le_iff_le _ _).mpr
        ((Subgroup.zpowers_le).mpr ((IntermediateField.mem_fixingSubgroup_iff E s).mpr hEf))
    have hK' : K ≤ IntermediateField.fixedField (Subgroup.zpowers s) :=
      (IntermediateField.le_iff_le _ _).mpr
        ((Subgroup.zpowers_le).mpr ((IntermediateField.mem_fixingSubgroup_iff K s).mpr hKf))
    have hM := sup_le hE' hK'
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    have hy := hM y.2 ⟨s, Subgroup.mem_zpowers s⟩
    rw [← hs]
    exact hy
  have hcard : Nat.card (Q.inertia (M ≃ₐ[ℚ] M)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩, ⟨1⟩⟩
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) Q (M ≃ₐ[ℚ] M),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[ℚ] M) (Q.under ℤ) Q, hcard]


end Sup

/-- **G2 → G4 → G7 with the twist, without `UnramifiedSup`** (g0-mod-field's `fieldDescentUnr`
with `unramifiedSup_mf`). -/
theorem fieldDescentUnr' (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7OutUnr u P :=
  fieldDescentUnr hCover hKer unramifiedSup_mf hHasse hTwo hSq hUnr Y Φ π u P hctx

/-- **Piece 10 without `UnramifiedSup`** (g0-mod-field's `modularConstituent_of_ranges_T14`). -/
theorem modularConstituent_of_ranges_T14' (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hH : PkgI6.BrauerHasse2C) (hR : PkgI6.BrauerReciprocity2C)
    (hC : PkgI6.LocalH2CardC) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG :=
  modularConstituent_of_ranges_T14 hCover hKer unramifiedSup_mf hH hR hC hSq hUnr hRest

end UnramTate

/-! ## g0-assemble2: x1-dirichlet (scratch/x1-dirichlet/Dirichlet.lean lines 2-184 verbatim) -/

/-!
# x1-dirichlet: the glue Prop `DirichletOfFinite` from T17 (`KroneckerWeberCyclic`)

`DirichletOfFinite` is copied verbatim from `scratch/g0-mod-newform/part_new.lean` (lines
727-738; there in namespace `G0ModNewform`, with `open PkgI4 (Qbar GQ LiesOver IsArithFrob …
GaloisChar)`). It is proved here from the leaf T17 in its narrowed form
`TSkolemKW.KW.KroneckerWeberCyclic` (the bundle's field `t17`) and the kernel's proved C8 glue
`TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic`
(`ZInQKernel/HDecomp/Textbook/KroneckerWeberUse.lean`).

New glue proved here:
* `isOpen_ker` (continuity + finite image ⇒ open kernel, through the kernel's
  `isOpen_ker_of_continuous`);
* `exists_preimage_of_pow_eq_one`: roots of unity of `ℚ̄_ℓ` lie in `ιL(ℚ̄)`;
* `cycChar_frob`: an arithmetic Frobenius at a place above `p ∤ m` has mod-`m` cyclotomic
  character `p` (the `m`-th roots of unity are distinct modulo the place, via
  `∑_{i<m} η^i = 0` for an `m`-th root of unity `η ≠ 1`);
* `dirichletOfFinite_of_kroneckerWeberCyclic : KroneckerWeberCyclic → DirichletOfFinite`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace X1Dirichlet

open PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisChar)
open TSkolemKW.KW

/-- **Kronecker–Weber at Frobenius (GLUE, unproved; from T17 `KroneckerWeber`).** A continuous
character `ψ : G_ℚ → ℚ̄_ℓ^×` of finite image is, at arithmetic Frobenius outside a finite set,
a Dirichlet character `ψD mod m` through `ιC`, `ιL`: `ψ` factors through
`Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/m)^×` (T17), arithmetic Frobenius at `p ∤ m` maps to `p`, and the values
(roots of unity) lie in `ιL(ℚ̄)`. -/
def DirichletOfFinite : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ψ : GaloisChar ℓ), (Set.range ψ.toHom).Finite →
    ∀ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
    ∃ (m : ℕ) (ψD : DirichletCharacter ℂ m) (S : Finset ℕ), 0 < m ∧
      ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
        ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
          (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-! ## §1. Roots of unity of `ℚ̄_ℓ` come from `ℚ̄` -/

theorem exists_preimage_of_pow_eq_one {E : Type*} [Field E] [Algebra ℚ E] (ι : Qbar →ₐ[ℚ] E)
    (N : ℕ+) (z : E) (hz : z ^ (N : ℕ) = 1) : ∃ β : Qbar, ι β = z := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_qbar N
  have h : IsPrimitiveRoot (ι ζ) (N : ℕ) := hζ.map_of_injective (RingHom.injective ι.toRingHom)
  obtain ⟨i, -, hi⟩ := h.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

/-! ## §2. Arithmetic Frobenius on roots of unity -/

/-- Roots of unity have valuation `1` at every place. -/
theorem valuation_eq_one_of_pow (v : ValuationSubring Qbar) {n : ℕ} (hn : n ≠ 0) {x : Qbar}
    (hx : x ^ n = 1) : v.valuation x = 1 := by
  have h := congrArg v.valuation hx
  rw [map_pow, map_one] at h
  exact (pow_eq_one_iff_of_nonneg zero_le hn).1 h

/-- **An arithmetic Frobenius at a place above `p ∤ m` has mod-`m` cyclotomic character `p`.** -/
theorem cycChar_frob (m : ℕ+) (p : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ (m : ℕ))
    (v : ValuationSubring Qbar) (τ : GQ) (hv : LiesOver v p) (hτ : IsArithFrob τ v p) :
    ((cycChar m τ : (ZMod m)ˣ) : ZMod m) = (p : ZMod m) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_qbar m
  have hm0 : (m : ℕ) ≠ 0 := m.ne_zero
  have hζm : ζ ^ (m : ℕ) = 1 := hζ.pow_eq_one
  set a := ((cycChar m τ : (ZMod m)ˣ) : ZMod m).val with ha
  have hτζ : τ ζ = ζ ^ a := cycChar_spec m τ ζ hζm
  have hζval : v.valuation ζ = 1 := valuation_eq_one_of_pow v hm0 hζm
  have hζv : ζ ∈ v := (v.valuation_le_one_iff ζ).1 hζval.le
  have hdiff : v.valuation (ζ ^ a - ζ ^ p) < 1 := by
    have := hτ.2 ζ hζv
    rw [hτζ] at this
    exact (v.mem_nonunits_iff).1 this
  have hpv : v.valuation (p : Qbar) < 1 := (v.mem_nonunits_iff).1 hv
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
  have heq : ζ ^ a = ζ ^ p := by
    by_contra hne
    set η := ζ ^ a / ζ ^ p with hηdef
    have hη1 : η ≠ 1 := fun h => hne ((div_eq_one_iff_eq (pow_ne_zero _ hζ0)).1 h)
    have hηm : η ^ (m : ℕ) = 1 := by
      rw [hηdef, div_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm p, pow_mul, pow_mul, hζm,
        one_pow, one_pow, div_one]
    have hηval : v.valuation η = 1 := valuation_eq_one_of_pow v hm0 hηm
    have hηv : v.valuation (η - 1) < 1 := by
      have : η - 1 = (ζ ^ a - ζ ^ p) / ζ ^ p := by
        rw [sub_div, div_self (pow_ne_zero _ hζ0)]
      rw [this, map_div₀, map_pow, hζval, one_pow, div_one]
      exact hdiff
    have hsum : ∑ i ∈ Finset.range (m : ℕ), η ^ i = 0 := by
      rw [geom_sum_eq hη1, hηm, sub_self, zero_div]
    have hmv : v.valuation ((m : ℕ) : Qbar) < 1 := by
      have : ((m : ℕ) : Qbar) = ∑ i ∈ Finset.range (m : ℕ), (1 - η ^ i) := by
        rw [Finset.sum_sub_distrib, hsum, sub_zero]
        simp
      rw [this]
      apply Valuation.map_sum_lt _ one_ne_zero
      intro i _
      have h1 : 1 - η ^ i = -((η - 1) * ∑ j ∈ Finset.range i, η ^ j) := by
        rw [mul_comm, geom_sum_mul]
        ring
      rw [h1, Valuation.map_neg, map_mul]
      have hs : v.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 :=
        Valuation.map_sum_le _ (fun j _ => by rw [map_pow, hηval, one_pow])
      exact (mul_le_of_le_one_right' hs).trans_lt hηv
    -- `p` and `m` are coprime, but both lie in the maximal ideal of `v`
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
    have h1 : ((p : ℤ) * Nat.gcdA p m + ((m : ℕ) : ℤ) * Nat.gcdB p m : ℤ) = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, hcop]
      rfl
    have hint : ∀ k : ℤ, v.valuation (k : Qbar) ≤ 1 := fun k =>
      (v.valuation_le_one_iff _).2 (intCast_mem v k)
    have hlt : v.valuation
        ((((p : ℤ) * Nat.gcdA p m + ((m : ℕ) : ℤ) * Nat.gcdB p m : ℤ)) : Qbar) < 1 := by
      push_cast
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hpv (hint _)
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hmv (hint _)
    rw [h1, Int.cast_one, map_one] at hlt
    exact lt_irrefl _ hlt
  -- `ζ^a = ζ^p` with `ζ` primitive gives `a ≡ p (mod m)`
  have hmod : (a : ZMod m) = (p : ZMod m) := by
    rcases le_total p a with h | h
    · have hd : ζ ^ (a - p) = 1 := by
        have : ζ ^ (a - p) * ζ ^ p = 1 * ζ ^ p := by
          rw [← pow_add, Nat.sub_add_cancel h, one_mul, heq]
        exact mul_right_cancel₀ (pow_ne_zero _ hζ0) this
      have := (hζ.pow_eq_one_iff_dvd _).1 hd
      exact ((ZMod.natCast_eq_natCast_iff p a m).2 ((Nat.modEq_iff_dvd' h).2 this)).symm
    · have hd : ζ ^ (p - a) = 1 := by
        have : ζ ^ (p - a) * ζ ^ a = 1 * ζ ^ a := by
          rw [← pow_add, Nat.sub_add_cancel h, one_mul, heq]
        exact mul_right_cancel₀ (pow_ne_zero _ hζ0) this
      have := (hζ.pow_eq_one_iff_dvd _).1 hd
      exact (ZMod.natCast_eq_natCast_iff a p m).2 ((Nat.modEq_iff_dvd' h).2 this)
  rw [← hmod, ha, ZMod.natCast_zmod_val]

/-! ## §3. `DirichletOfFinite` -/

/-- **`DirichletOfFinite` (GLUE, proved from the leaf T17 in its cyclic form).** -/
theorem dirichletOfFinite_of_kroneckerWeberCyclic (hKW : KroneckerWeberCyclic) :
    DirichletOfFinite := by
  intro ℓ _ ψ hfin ιC ιL
  have hopen : IsOpen (ψ.toHom.ker : Set GQ) :=
    isOpen_ker_of_continuous ψ.toHom ψ.continuous_toHom hfin
  obtain ⟨m, χ, hχ⟩ := dirichletCharacter_of_kroneckerWeberCyclic hKW ψ.toHom hopen
  -- the values of `χ` on units are roots of unity of order dividing `N = #(ℤ/m)ˣ`
  let N : ℕ+ := ⟨Fintype.card (ZMod m)ˣ, Fintype.card_pos⟩
  have hpow : ∀ u : (ZMod m)ˣ, (χ u) ^ (N : ℕ) = 1 := by
    intro u
    have h1 : u ^ (N : ℕ) = 1 := pow_card_eq_one
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  choose β hβ using fun u : (ZMod m)ˣ => exists_preimage_of_pow_eq_one ιL N (χ u) (hpow u)
  have hβ0 : ∀ u, β u ≠ 0 := by
    intro u h
    have := hβ u
    rw [h, map_zero, ← MulChar.coe_toUnitHom] at this
    exact (χ.toUnitHom u).ne_zero this.symm
  have hinj : Function.Injective ιL := RingHom.injective ιL.toRingHom
  let χQ : (ZMod m)ˣ →* Qbarˣ :=
    { toFun := fun u => Units.mk0 (β u) (hβ0 u)
      map_one' := Units.ext (hinj (by simp [hβ]))
      map_mul' := fun u w => Units.ext (hinj (by simp [hβ, map_mul])) }
  let ψD : DirichletCharacter ℂ (m : ℕ) :=
    MulChar.ofUnitHom ((Units.map (ιC : Qbar →* ℂ)).comp χQ)
  refine ⟨m, ψD, (m : ℕ).primeFactors, m.pos, fun p hp hpS => ?_⟩
  have hpm : ¬ p ∣ (m : ℕ) := fun h =>
    hpS (Nat.mem_primeFactors.2 ⟨hp, h, m.ne_zero⟩)
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime p hcop
  have hu : ((u : (ZMod m)ˣ) : ZMod m) = (p : ZMod m) := ZMod.coe_unitOfCoprime p hcop
  refine ⟨β u, ?_, fun v τ hv hτ => ?_⟩
  · rw [← hu, MulChar.ofUnitHom_coe]
    rfl
  · rw [hχ τ, hβ u, cycChar_frob m p hp hpm v τ hv hτ, ← hu]

end X1Dirichlet

end

namespace G0ModNewform
/-- (x1-dirichlet) the two verbatim copies agree. -/
theorem dirichletOfFinite_copy : G0ModNewform.DirichletOfFinite ↔ X1Dirichlet.DirichletOfFinite :=
  Iff.rfl
/-- (x1-dirichlet) `DirichletOfFinite` from T17 (`TextbookLeaves.t17`). -/
theorem dirichletOfFinite_of_t17 (hKW : TSkolemKW.KW.KroneckerWeberCyclic) : DirichletOfFinite :=
  X1Dirichlet.dirichletOfFinite_of_kroneckerWeberCyclic hKW
end G0ModNewform

/-! ## g0-assemble2: mobius-glue (scratch/mobius-glue/MobiusGlue.lean), adapted to Leaves.lean after pin-apply

Changes (all mechanical): (1) its §0 copies of `QMFamily`, `IsFibreOf`, `R1famProps`,
`R1univProps` (lines 47-79, 89-100) are not repeated: pin-apply put the same text into Leaves.lean
(`LeafQM.AV.*`), which the names resolve to; (2) its copy of `MobiusGlue` (stated with
`R1fpPropsU`) is renamed `MobiusGlueU` throughout, because Leaves.lean's `LeafQM.AV.Pin.MobiusGlue`
is stated with the repaired `R1fpProps` (the same six clauses, associated differently);
`mobiusGlue_of_U` below converts; (3) §6 (lines 549-643, qm-pin's comparison lemmas, already in
Leaves.lean) and the two downstream corollaries at lines 1409-1434 are not repeated. -/

/-!
# mobius-glue: the `π`-half of qm-pin's comparison of two triples

Task mobius-glue (2026-11-13). See `docs/research/mobius-glue.md`.

**Main result** (`mobiusGlue_of_curves`): `LeafQM.AV.Pin.MobiusGlueU` (qm-pin §3.2, copied
verbatim from `scratch/qm-pin/QMPin.lean` together with the definitions it uses) follows from

* `CurveRatFactor` (curves): on a proper smooth curve over `ℚ`, a morphism `ρ` to `P¹` that is
  constant on the fibres of a morphism `σ` to `P¹` is a rational function of `σ` on `ℚ̄`-points;
* `CurveSurj` (curves): a morphism to `P¹` with finite fibres on `ℚ̄`-points, from a proper
  smooth curve over `ℚ` with a `ℚ̄`-point, is onto `P¹(ℚ̄)`;
* `ObjBridge.TorsionStructure` (the decomposition's textbook leaf T5, `A(K̄)[n] ≅ (ℤ/n)^{2g}`).

Contents.
* §0 the qm-pin definitions (verbatim).
* §1 an injective rational function on an algebraically closed field of characteristic 0 has
  degree at most one (`Mob.natDegree_le_one_of_injective`, Wronskian argument); one of degree at
  most one without finite pole fixing `0` and `c ≠ 0` is the identity (`Mob.ratEval_eq_self`).
* §2 the named facts; §3 `mobiusGlue_of_curveFacts` (from the curve facts and
  `TwistClassFinite`).
* §4 `TwistClassFinite` from T5 and `AutOInnerFinite` (finitely many level structures per pair via
  the kernel's `Level3.torsor`; transport of level structures; twists by conjugate automorphisms).
* §5-§6 the combined statements and the downstream comparison/transfer (qm-pin §4 copied).
* §7 `AutOInnerFinite` from Skolem–Noether (the kernel's `TSkolemKW.leafSkolemNoether`, through
  an explicit extension of `α ∈ Aut 𝒪` to `B`) and `NormalizerFinite`.
* §8 `NormalizerFinite` proved (`N(𝒪)/ℚ^×𝒪^× = {1, i, j, ij}`, descent on the reduced norm), hence
  `autOInnerFinite`, `twistClassFinite`, `mobiusGlue_of_curves`, `sameTripleMor_of_curves`,
  `pointwise_of_witness_curves`.
No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3


/-- **R1fp, repaired clause list** (to replace `LeafQM.AV.R1fpProps`): the four old clauses and
`R1famProps`. -/
def R1fpPropsPin (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ
/-- The fully repaired clause list: family and universal property. -/
def R1fpPropsU (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  R1fpPropsPin Y Φ ∧ R1univProps Y Φ

/-- **Glue (not compiled; argued in the report §3.4).** Given a morphism `g : Y' → Y` with
`Φ' = Φ ∘ g`, and CM objects of the three kinds, the two morphisms `π'` and `π ∘ g` to `P¹`
agree on `ℚ̄`-points: they have the same fibres (both `R2fpProps`), so `π' = h ∘ π ∘ g` with `h`
a bijection of `P¹(ℚ̄)` which is a morphism (graph argument on each geometric component of
`Y'`), hence a Möbius map, and `h` fixes `0, ∞, −16/27`. Algebraic geometry of curves. -/
def MobiusGlueU : Prop :=
  ∀ (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left) (g : Y' ⟶ Y),
    R1fpPropsU Y Φ → R2fpProps Y Φ π → R1fpPropsU Y' Φ' → R2fpProps Y' Φ' π' →
    ((∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q)) →
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'), Φ' K y = Φ K (y ≫ g)) →
    ∀ y : fieldPt Qbar ⟶ Y', π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g).left

/-! ## §1 Rational functions on `P¹`: an injective one is a Möbius map -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]


open scoped Classical in
/-- The value at a finite point `t` of the rational map `[F : G] : P¹ → P¹`. -/
def ratEval (F G : K[X]) (t : K) : OnePoint K :=
  if G.eval t = 0 then OnePoint.infty else OnePoint.some (F.eval t / G.eval t)

theorem eval_ne_zero_of_coprime {F G : K[X]} (h : IsCoprime F G) {a : K} (hG : G.eval a = 0) :
    F.eval a ≠ 0 := by
  intro hF
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (Polynomial.eval a) huv
  simp [eval_add, eval_mul, hF, hG] at this

/-- The Wronskian `F' G - F G'` of a coprime pair of which one has positive degree is nonzero
(characteristic 0). -/
theorem wronskian_ne_zero [CharZero K] {F G : K[X]} (h : IsCoprime F G)
    (hdeg : F.natDegree ≠ 0 ∨ G.natDegree ≠ 0) :
    derivative F * G - F * derivative G ≠ 0 := by
  intro hW
  have hW' : derivative F * G = F * derivative G := sub_eq_zero.mp hW
  have key : ∀ {P Q : K[X]}, IsCoprime P Q → P ∣ derivative P * Q → P.natDegree = 0 := by
    intro P Q hPQ hd
    have hd' : P ∣ derivative P := hPQ.dvd_of_dvd_mul_right hd
    by_contra hP
    have hne : derivative P ≠ 0 := derivative_ne_zero.mpr hP
    have h1 := natDegree_le_of_dvd hd' hne
    have h2 := natDegree_derivative_lt hP
    omega
  have hF : F.natDegree = 0 := key h ⟨derivative G, hW'⟩
  have hG : G.natDegree = 0 := key h.symm ⟨derivative F, by rw [mul_comm, ← hW', mul_comm]⟩
  rcases hdeg with hdeg | hdeg <;> contradiction

/-- **An injective rational function has degree at most one** (algebraically closed field of
characteristic 0). -/
theorem natDegree_le_one_of_injective [IsAlgClosed K] [CharZero K] {F G : K[X]}
    (hcop : IsCoprime F G) (hinj : ∀ s t : K, ratEval F G s = ratEval F G t → s = t) :
    F.natDegree ≤ 1 ∧ G.natDegree ≤ 1 := by
  classical
  by_contra hcon
  set n := max F.natDegree G.natDegree with hn_def
  have hn : 2 ≤ n := by
    rw [not_and_or] at hcon
    rcases hcon with h | h <;> omega
  set W := derivative F * G - F * derivative G with hW_def
  have hW : W ≠ 0 := wronskian_ne_zero hcop (by omega)
  -- the good values of `c`
  set S : Set K := {c | F.coeff n - c * G.coeff n ≠ 0} with hS_def
  have hS : S.Infinite := by
    have hsub : Sᶜ.Subsingleton := by
      intro c hc d hd
      simp only [hS_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hc hd
      by_cases hG : G.coeff n = 0
      · have hF : F.coeff n ≠ 0 := by
          rcases le_total F.natDegree G.natDegree with h | h
          · have hnG : n = G.natDegree := by omega
            have : G.natDegree ≠ 0 := by omega
            rw [hnG] at hG
            exact absurd (leadingCoeff_eq_zero.mp hG) (by rintro rfl; simp at this)
          · have hnF : n = F.natDegree := by omega
            have : F.natDegree ≠ 0 := by omega
            rw [hnF]
            intro h0
            exact absurd (leadingCoeff_eq_zero.mp h0) (by rintro rfl; simp at this)
        rw [hG, mul_zero, sub_zero] at hc
        exact absurd hc hF
      · have e1 : c = F.coeff n / G.coeff n := by rw [eq_div_iff hG]; linear_combination -hc
        have e2 : d = F.coeff n / G.coeff n := by rw [eq_div_iff hG]; linear_combination -hd
        rw [e1, e2]
    have := hsub.finite.infinite_compl
    rwa [compl_compl] at this
  -- every good `c` is the value at a root of `W`
  have hgood : ∀ c ∈ S, ∃ a, W.IsRoot a ∧ F.eval a / G.eval a = c := by
    intro c hc
    set H := F - C c * G with hH_def
    have hHn : H.natDegree = n := by
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · refine (natDegree_sub_le _ _).trans (max_le (le_max_left _ _) ?_)
        exact (natDegree_C_mul_le _ _).trans (le_max_right _ _)
      · have hc' : F.coeff n - c * G.coeff n ≠ 0 := hc
        simpa [hH_def, coeff_sub, coeff_C_mul] using hc'
    have hH0 : H ≠ 0 := by
      intro h0; rw [h0, natDegree_zero] at hHn; omega
    -- a root of `H` has value `c`
    have hval : ∀ b, H.IsRoot b → G.eval b ≠ 0 ∧ F.eval b / G.eval b = c := by
      intro b hb
      have hb' : F.eval b = c * G.eval b := by
        have := hb; simp only [IsRoot, hH_def, eval_sub, eval_mul, eval_C] at this
        linear_combination this
      have hGb : G.eval b ≠ 0 := by
        intro h0
        exact eval_ne_zero_of_coprime hcop h0 (by rw [hb', h0, mul_zero])
      exact ⟨hGb, by rw [hb']; field_simp⟩
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H (by
      rw [degree_eq_natDegree hH0]; exact_mod_cast (by omega : H.natDegree ≠ 0))
    obtain ⟨hGa, hFa⟩ := hval a ha
    -- all roots of `H` are `a`
    have hall : ∀ b ∈ H.roots, a = b := by
      intro b hb
      have hb' := (mem_roots hH0).mp hb
      obtain ⟨hGb, hFb⟩ := hval b hb'
      apply hinj
      simp only [ratEval, hGa, hGb, ite_false, hFa, hFb]
    have hcount : H.roots.count a = n := by
      rw [Multiset.count_eq_card.mpr hall, IsAlgClosed.card_roots_eq_natDegree, hHn]
    have hmult : 1 < H.rootMultiplicity a := by
      rw [← count_roots]; convert (show 1 < n by omega) using 2
    obtain ⟨-, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot hH0).mp hmult
    refine ⟨a, ?_, hFa⟩
    have hd' : (derivative F).eval a = c * (derivative G).eval a := by
      have := hd
      simp only [IsRoot, hH_def, derivative_sub, derivative_mul, derivative_C, zero_mul,
        zero_add, eval_sub, eval_mul, eval_C] at this
      linear_combination this
    have ha' : F.eval a = c * G.eval a := by
      have := ha; simp only [IsRoot, hH_def, eval_sub, eval_mul, eval_C] at this
      linear_combination this
    simp only [IsRoot, hW_def, eval_sub, eval_mul, hd', ha']
    ring
  -- so the good values lie in a finite set
  have hfin : S.Finite := by
    refine ((W.roots.toFinset.finite_toSet).image (fun a => F.eval a / G.eval a)).subset ?_
    intro c hc
    obtain ⟨a, ha, rfl⟩ := hgood c hc
    exact ⟨a, by simpa [Multiset.mem_toFinset, mem_roots hW] using ha, rfl⟩
  exact hS hfin


/-- **A rational function of degree at most one with no finite pole, fixing `0` and some
`c ≠ 0`, is the identity on `K`.** (With `∞ ↦ ∞`, which "no finite pole" encodes: a Möbius map
fixing `0, ∞, c` is the identity.) -/
theorem ratEval_eq_self [IsAlgClosed K] {F G : K[X]} (hF1 : F.natDegree ≤ 1)
    (hpole : ∀ t, ratEval F G t ≠ OnePoint.infty) (h0 : ratEval F G 0 = OnePoint.some 0)
    {c : K} (hc : c ≠ 0) (hcc : ratEval F G c = OnePoint.some c) :
    ∀ t, ratEval F G t = OnePoint.some t := by
  classical
  have hGne : ∀ t, G.eval t ≠ 0 := fun t ht => hpole t (by simp [ratEval, ht])
  have hG0 : G.natDegree = 0 := by
    by_contra h
    have hG : G ≠ 0 := by rintro rfl; simp at h
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root G (by
      rw [degree_eq_natDegree hG]; exact_mod_cast h)
    exact hGne a ha
  have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero hG0
  have hFX : F = C (F.coeff 1) * X + C (F.coeff 0) := eq_X_add_C_of_natDegree_le_one hF1
  have hd : G.coeff 0 ≠ 0 := by
    have := hGne 0; rwa [hGC, eval_C] at this
  have hval : ∀ t, ratEval F G t =
      OnePoint.some ((F.coeff 1 * t + F.coeff 0) / G.coeff 0) := by
    intro t
    simp only [ratEval, hGne t, ite_false]
    congr 1
    conv_lhs => rw [hFX, hGC]
    simp
  have hb : F.coeff 0 = 0 := by
    have := h0; rw [hval, OnePoint.coe_eq_coe] at this
    simpa [hd] using this
  have ha : F.coeff 1 = G.coeff 0 := by
    have := hcc; rw [hval, OnePoint.coe_eq_coe, hb, add_zero, div_eq_iff hd] at this
    exact mul_right_cancel₀ hc (by rw [this, mul_comm])
  intro t
  rw [hval, hb, ha, add_zero, mul_div_cancel_left₀ _ hd]

end Mob

/-! ## §2 The named facts -/

open Polynomial in
/-- **Curve fact 1 (factorization through a rational function).** On a proper smooth curve
`S/ℚ`, if `ρ : S → P¹` is constant on the fibres of `σ : S → P¹` (on `ℚ̄`-points), then
`ρ = R ∘ σ` on `ℚ̄`-points with finite `σ`-value, for a rational function `R = [F : G]`,
`F, G ∈ ℚ̄[t]` coprime. (On a geometric component `C` where `σ` is nonconstant: the image of
`(σ, ρ) : C → P¹ × P¹` projects bijectively, hence birationally (char. 0), onto the normal
curve `P¹`, so its inverse is a morphism and `R = pr₂ ∘ pr₁⁻¹`; components where `σ` is
constant are absorbed by the fibre condition, or by Lagrange interpolation if every component
is. STANDARD; not in Mathlib.) -/
def CurveRatFactor : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ σ ρ : ToP1 S.left,
      (∀ y₁ y₂ : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left →
        ρ.val (K := Qbar) y₁.left = ρ.val (K := Qbar) y₂.left) →
      ∃ F G : Qbar[X], IsCoprime F G ∧ ∀ (y : fieldPt Qbar ⟶ S) (t : Qbar),
        σ.val (K := Qbar) y.left = OnePoint.some t → ρ.val (K := Qbar) y.left = Mob.ratEval F G t

/-- **Curve fact 2 (surjectivity).** A morphism `σ : S → P¹` from a proper smooth curve `S/ℚ`
with a `ℚ̄`-point, whose fibres on `ℚ̄`-points are finite, is onto `P¹(ℚ̄)`. (The geometric
component through the given point has infinitely many `ℚ̄`-points, so `σ` is nonconstant on
it; its image is closed and irreducible, hence `P¹`; closed points of `P¹_ℚ̄` lift to
`ℚ̄`-points. STANDARD, e.g. Hartshorne II.6.8; not in Mathlib.) -/
def CurveSurj : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    Nonempty (fieldPt Qbar ⟶ S) → ∀ σ : ToP1 S.left,
      (∀ y : fieldPt Qbar ⟶ S, {y' : fieldPt Qbar ⟶ S |
        σ.val (K := Qbar) y'.left = σ.val (K := Qbar) y.left}.Finite) →
      ∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = t

/-- **Moduli fact (finite twist classes).** For a level-3 object `P` over `ℚ̄`, only finitely
many isomorphism classes `[Q]` have `(Q.A, Q.ι)` isomorphic to an `Aut(𝒪)`-twist of
`(P.A, P.ι)`. (The twists of a pair by `α` and by `α ∘ (conjugation by a unit)` are isomorphic
through `ι(u)`, and `Aut(𝒪)` modulo these is the finite group `N(𝒪)/ℚ^×𝒪^×` (Skolem–Noether);
for a fixed pair, `η` is determined by `η(1) ∈ A[3](ℚ̄)`, a finite group. STANDARD; not in
Mathlib.) -/
def TwistClassFinite : Prop :=
  ∀ P : QML3 Qbar, {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧
    ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)}.Finite

/-! ## §3 The reduction -/

/-- **`MobiusGlueU` from the two curve facts and the moduli fact.** -/
theorem mobiusGlue_of_curveFacts (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : TwistClassFinite) : MobiusGlueU := by
  intro Y Y' Φ Φ' π π' g h1 h2 h1' h2' hCM hg y
  set σ : ToP1 Y'.left := π.comp g.left with hσ_def
  have hσ : ∀ y : fieldPt Qbar ⟶ Y', σ.val (K := Qbar) y.left =
      π.val (K := Qbar) (y ≫ g).left := by
    intro y; exact ToP1.val_comp_right π g.left y.left
  rw [← hσ]
  -- representatives
  have hout : ∀ y : fieldPt Qbar ⟶ Y', Φ' Qbar y = M3.mk (Quotient.out (Φ' Qbar y)) :=
    fun y => (Quotient.out_eq _).symm
  -- the two maps have the same fibres
  have hrel : ∀ y₁ y₂ : fieldPt Qbar ⟶ Y', σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left
      ↔ π'.val (K := Qbar) y₁.left = π'.val (K := Qbar) y₂.left := by
    intro y₁ y₂
    rw [hσ, hσ, (h2 (y₁ ≫ g) (y₂ ≫ g) _ _ ((hg Qbar y₁).symm.trans (hout y₁))
      ((hg Qbar y₂).symm.trans (hout y₂))).1, (h2' y₁ y₂ _ _ (hout y₁) (hout y₂)).1]
  -- CM points of `Y'` and the values there
  obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩ := hCM
  have hpt : ∀ P : QML3 Qbar, Φ' Qbar ((Φ' Qbar).symm (M3.mk P)) = M3.mk P :=
    fun P => (Φ' Qbar).apply_symm_apply _
  set y₄ := (Φ' Qbar).symm (M3.mk P₄)
  set y₃ := (Φ' Qbar).symm (M3.mk P₃)
  set y₂ := (Φ' Qbar).symm (M3.mk P₂)
  have hY : ∀ y : fieldPt Qbar ⟶ Y', ∀ P : QML3 Qbar, Φ' Qbar y = M3.mk P →
      Φ Qbar (y ≫ g) = M3.mk P := fun y P hP => (hg Qbar y).symm.trans hP
  have σ₄ : σ.val (K := Qbar) y₄.left = OnePoint.some 0 := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₄)) (hY _ _ (hpt P₄))).2.1 c₄
  have π₄ : π'.val (K := Qbar) y₄.left = OnePoint.some 0 :=
    (h2' _ _ _ _ (hpt P₄) (hpt P₄)).2.1 c₄
  have σ₃ : σ.val (K := Qbar) y₃.left = OnePoint.infty := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₃)) (hY _ _ (hpt P₃))).2.2.1 c₃
  have π₃ : π'.val (K := Qbar) y₃.left = OnePoint.infty :=
    (h2' _ _ _ _ (hpt P₃) (hpt P₃)).2.2.1 c₃
  have σ₂ : σ.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27) := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₂)) (hY _ _ (hpt P₂))).2.2.2 c₂
  have π₂ : π'.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27) :=
    (h2' _ _ _ _ (hpt P₂) (hpt P₂)).2.2.2 c₂
  -- finite fibres
  have hfin : ∀ y : fieldPt Qbar ⟶ Y', {y' : fieldPt Qbar ⟶ Y' |
      σ.val (K := Qbar) y'.left = σ.val (K := Qbar) y.left}.Finite := by
    intro y
    refine ((hT (Quotient.out (Φ' Qbar y))).preimage
      (Set.injOn_of_injective (Φ' Qbar).injective)).subset ?_
    intro y' hy'
    have e : π'.val (K := Qbar) y.left = π'.val (K := Qbar) y'.left :=
      ((hrel y' y).1 hy').symm
    exact ⟨_, hout y', ((h2' y y' _ _ (hout y) (hout y')).1).1 e⟩
  obtain ⟨⟨hprop', hsmooth', hne', -, -⟩, -⟩ := h1'
  have hsurj := hSu Y' hprop' hsmooth' hne' σ hfin
  obtain ⟨F, G, hcop, hFG⟩ := hRF Y' hprop' hsmooth' σ π' (fun y₁ y₂ h => (hrel y₁ y₂).1 h)
  -- the rational function is injective, has no finite pole, and fixes `0` and `-16/27`
  have hinj : ∀ s t : Qbar, Mob.ratEval F G s = Mob.ratEval F G t → s = t := by
    intro s t hst
    obtain ⟨ys, hys⟩ := hsurj (OnePoint.some s)
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : π'.val (K := Qbar) ys.left = π'.val (K := Qbar) yt.left := by
      rw [hFG ys s hys, hFG yt t hyt, hst]
    have := (hrel ys yt).2 e
    rw [hys, hyt] at this
    exact OnePoint.coe_injective this
  have hdeg := Mob.natDegree_le_one_of_injective hcop hinj
  have hpole : ∀ t, Mob.ratEval F G t ≠ OnePoint.infty := by
    intro t ht
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : π'.val (K := Qbar) yt.left = π'.val (K := Qbar) y₃.left := by
      rw [hFG yt t hyt, ht, π₃]
    have := (hrel yt y₃).2 e
    rw [hyt, σ₃] at this
    exact OnePoint.coe_ne_infty t this
  have h0 : Mob.ratEval F G 0 = OnePoint.some 0 := by rw [← hFG y₄ 0 σ₄, π₄]
  have hc : Mob.ratEval F G (-16 / 27) = OnePoint.some (-16 / 27) := by
    rw [← hFG y₂ _ σ₂, π₂]
  have hid := Mob.ratEval_eq_self hdeg.1 hpole h0 (by norm_num) hc
  -- conclusion
  by_cases hinf : σ.val (K := Qbar) y.left = OnePoint.infty
  · rw [hinf]
    rw [← π₃]
    exact (hrel y y₃).1 (by rw [hinf, σ₃])
  · obtain ⟨t, ht⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    rw [← ht, hFG y t ht.symm, hid t]

/-! ## §4 `TwistClassFinite` from the textbook leaf `TorsionStructure` (T5) and an algebra fact -/

/-- **Algebra fact (finiteness of `Aut(𝒪)` modulo inner automorphisms by units).** Every ring
automorphism of `𝒪` is, up to conjugation by a unit of `𝒪`, one of finitely many. (Every
automorphism of `𝒪` extends to `B = 𝒪 ⊗ ℚ`, hence is conjugation by some `x ∈ N(𝒪)`
(Skolem–Noether), and `N(𝒪)/ℚ^×𝒪^×` is finite: for the maximal order of the quaternion algebra
of discriminant 6 it is the Atkin–Lehner group `W ≅ (ℤ/2)²`. STANDARD (Vignéras, *Arithmétique
des algèbres de quaternions*; locator UNVERIFIED); not in Mathlib.) A statement about the concrete
order `O` of the kernel only. -/
def AutOInnerFinite : Prop :=
  ∃ T : Set (O ≃+* O), T.Finite ∧ ∀ α : O ≃+* O, ∃ t ∈ T, ∃ v : Oˣ,
    ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)

section FiniteTwist

variable {K : Type} [Field K]

/-- Every element of `𝒪` is congruent modulo `3𝒪` to some `liftO c`, `c ∈ (ℤ/3)⁴`. -/
theorem exists_liftO_congr (u : O) : ∃ c : Fin 4 → ZMod 3, ∃ k : O, u - liftO c = 3 * k := by
  obtain ⟨n, hn⟩ := u.2
  refine ⟨fun i => (n i : ZMod 3), ⟨ofInt (fun i => n i / 3), ⟨_, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33, liftO]
  rw [hn, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply, ZMod.val_intCast, Nat.cast_ofNat]
  omega

/-- **Finitely many level structures on one `(A, ι)`** (characteristic 0, given the leaf
`TorsionStructure`): by the kernel's torsor glue `Level3.torsor`, a level structure is
`a ↦ η₀(a u₀)`, which depends only on `u₀ mod 3𝒪`. -/
theorem level3_finite (hT : ObjBridge.TorsionStructure) [CharZero K] {A : AbVar K}
    (s : A.dim = 2) (q : QMStr A) : Finite (Level3 q) := by
  rcases isEmpty_or_nonempty (Level3 q) with h | h
  · infer_instance
  · obtain ⟨e₀⟩ := h
    have key : ∀ e : Level3 q, ∃ c : Fin 4 → ZMod 3, ∀ a : O,
        e.eta a = e₀.eta (a * liftO c) := by
      intro e
      obtain ⟨u₀, -, -, hu⟩ := Level3.torsor hT ⟨A, s, q, e₀⟩ e
      obtain ⟨c, k, hk⟩ := exists_liftO_congr u₀
      refine ⟨c, fun a => (hu a).trans ((e₀.eq_iff _ _).2 ⟨a * k, ?_⟩)⟩
      calc a * u₀ - a * liftO c = a * (u₀ - liftO c) := by noncomm_ring
        _ = a * (3 * k) := by rw [hk]
        _ = 3 * (a * k) := by noncomm_ring
    choose f hf using key
    refine Finite.of_injective f fun e e' h => Level3.ext' ?_
    ext a
    rw [hf e a, hf e' a, h]

/-- Transport of a level structure along an isomorphism of QM pairs. -/
def transportLevel {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q')
    (e : Level3 q) : Level3 q' where
  eta := (AbVar.ptMap (L := K) f.φ).toAdditive.comp e.eta
  linear a b := by
    change Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ f.φ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ f.φ.hom) ≫ (q'.iota a).hom)
    rw [e.linear]
    change Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q.iota a).hom) ≫ f.φ.hom) = _
    rw [Category.assoc, f.equivariant a, Category.assoc]
  ker a := by
    rw [← e.ker]
    constructor
    · intro h
      have h' : Additive.toMul (e.eta a) ≫ f.φ.hom = 1 := congrArg Additive.toMul h
      have : Additive.toMul (e.eta a) = 1 := by
        calc Additive.toMul (e.eta a) = Additive.toMul (e.eta a) ≫ f.φ.hom ≫ f.ψ.hom := by
              rw [f.left, Category.comp_id]
          _ = 1 := by rw [← Category.assoc, h', MonObj.one_comp]
      exact congrArg Additive.ofMul this
    · intro h
      change Additive.ofMul (Additive.toMul (e.eta a) ≫ f.φ.hom) = 0
      rw [h]
      change Additive.ofMul ((1 : _ ⟶ _) ≫ f.φ.hom) = 0
      rw [MonObj.one_comp]
      rfl

/-- An object is isomorphic to the transport of its level structure. -/
def QML3.isoTransport (Q : QML3 K) {A' : AbVar K} (s' : A'.dim = 2) {q' : QMStr A'}
    (f : QMIso Q.q q') : Q.Iso ⟨A', s', q', transportLevel f Q.e⟩ where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant := f.equivariant
  level _ := rfl

/-- Twists by `t` and by `v t v⁻¹` (`v ∈ 𝒪^×`) are isomorphic through `ι(v)`. -/
def conjUnitIso {A : AbVar K} (q : QMStr A) (t α : O ≃+* O) (v : Oˣ)
    (hv : ∀ a, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)) : QMIso (q.twist t) (q.twist α) where
  φ := q.iota v
  ψ := q.iota ↑v⁻¹
  left := by
    have : q.iota ↑v⁻¹ * q.iota ↑v = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    exact congrArg AbVar.Hom.hom this
  right := by
    have : q.iota ↑v * q.iota ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact congrArg AbVar.Hom.hom this
  equivariant a := by
    have : q.iota (v : O) * q.iota (t a) = q.iota (α a) * q.iota v := by
      rw [← map_mul, ← map_mul, hv, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    exact congrArg AbVar.Hom.hom this

/-- **`TwistClassFinite` from the leaf `TorsionStructure` and `AutOInnerFinite`.** -/
theorem twistClassFinite_of (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) :
    TwistClassFinite := by
  obtain ⟨T, hTfin, hTα⟩ := hA
  intro P
  let R : (O ≃+* O) → Set (M3 Qbar) := fun t =>
    Set.range (fun e : Level3 (P.q.twist t) => M3.mk ⟨P.A, P.surface, P.q.twist t, e⟩)
  have hR : ∀ t, (R t).Finite := fun t => by
    have := level3_finite hT P.surface (P.q.twist t)
    exact Set.finite_range _
  refine (hTfin.biUnion fun t _ => hR t).subset ?_
  rintro m ⟨Q, rfl, α, ⟨f⟩⟩
  obtain ⟨t, ht, v, hv⟩ := hTα α
  let h : QMIso Q.q (P.q.twist t) := ((conjUnitIso P.q t α v hv).trans f).symm
  refine Set.mem_biUnion ht ⟨transportLevel h Q.e, ?_⟩
  exact Quotient.sound ⟨(QML3.isoTransport Q P.surface h).symm⟩

end FiniteTwist

/-! ## §5 The result -/

/-- **`MobiusGlueU` from two curve facts, the textbook leaf `TorsionStructure` (T5, Mumford §4)
and the algebra fact `AutOInnerFinite`.** -/
theorem mobiusGlue_of_named (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) : MobiusGlueU :=
  mobiusGlue_of_curveFacts hRF hSu (twistClassFinite_of hT hA)

end Pin

end AV

end LeafQM


/-! ## §7 `AutOInnerFinite` from Skolem–Noether (proved in the kernel) and `NormalizerFinite`

(Outside the `open MonObj` scope of §0-§6.) -/

namespace LeafQM

namespace AV

namespace Pin

namespace AutOExt

/-! ### Extension of a ring automorphism of `𝒪` to `B` -/

theorem mem_O_of_int (z0 z1 z2 z3 : ℤ) : (⟨z0, z1, z2, z3⟩ : B) ∈ O := by
  refine ⟨![z0 - z2, z1 - z3, 2 * z2, 2 * z3], ?_⟩
  ext <;> simp [ofInt]

theorem nat_smul_mem (n : ℕ) {x : B} (hx : x ∈ O) : (n : ℚ) • x ∈ O := by
  rw [Algebra.smul_def, map_natCast]
  exact O.mul_mem (natCast_mem O n) hx

theorem den_mul_int (q : ℚ) (k : ℕ) : ∃ z : ℤ, ((k * q.den : ℕ) : ℚ) * q = z :=
  ⟨k * q.num, by push_cast; rw [mul_assoc, Rat.den_mul_eq_num]⟩

/-- Every element of `B` has a positive integer multiple in `𝒪`. -/
theorem exists_nat_smul_mem (b : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O := by
  set m := b.re.den * b.imI.den * b.imJ.den * b.imK.den with hm
  refine ⟨m, by positivity, ?_⟩
  obtain ⟨z0, h0⟩ := den_mul_int b.re (b.imI.den * b.imJ.den * b.imK.den)
  obtain ⟨z1, h1⟩ := den_mul_int b.imI (b.re.den * b.imJ.den * b.imK.den)
  obtain ⟨z2, h2⟩ := den_mul_int b.imJ (b.re.den * b.imI.den * b.imK.den)
  obtain ⟨z3, h3⟩ := den_mul_int b.imK (b.re.den * b.imI.den * b.imJ.den)
  have e : (m : ℚ) • b = ⟨z0, z1, z2, z3⟩ := by
    ext
    · rw [QuaternionAlgebra.re_smul, ← h0, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imI_smul, ← h1, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imJ_smul, ← h2, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imK_smul, ← h3, smul_eq_mul, hm]
  rw [e]
  exact mem_O_of_int z0 z1 z2 z3

variable (α : O ≃+* O)

/-- A chosen positive integer `m` with `m b ∈ 𝒪`. -/
def extDen (b : B) : ℕ := Classical.choose (exists_nat_smul_mem b)

theorem extDen_pos (b : B) : 0 < extDen b := (Classical.choose_spec (exists_nat_smul_mem b)).1

theorem extDen_mem (b : B) : ((extDen b : ℕ) : ℚ) • b ∈ O :=
  (Classical.choose_spec (exists_nat_smul_mem b)).2

/-- `α̃(b) = m⁻¹ α(m b)`. -/
def extFun (b : B) : B := ((extDen b : ℚ)⁻¹) • (α ⟨_, extDen_mem b⟩ : B)

theorem natCast_mul_eq_smul (n : ℕ) (x : B) : (n : B) * x = (n : ℚ) • x := by
  rw [Algebra.smul_def, map_natCast]

theorem alpha_nat_smul (n : ℕ) (x : B) (hx : x ∈ O) (hnx : (n : ℚ) • x ∈ O) :
    (α ⟨_, hnx⟩ : B) = (n : ℚ) • (α ⟨x, hx⟩ : B) := by
  have : (⟨_, hnx⟩ : O) = (n : O) * ⟨x, hx⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [natCast_mul_eq_smul]
  rw [this, map_mul, map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast,
    natCast_mul_eq_smul]

/-- Independence of the choice of `m`. -/
theorem extFun_eq (b : B) (m : ℕ) (hm : 0 < m) (hb : (m : ℚ) • b ∈ O) :
    extFun α b = ((m : ℚ)⁻¹) • (α ⟨_, hb⟩ : B) := by
  have hd : 0 < extDen b := extDen_pos b
  have hdm : (m : ℚ) • ((extDen b : ℚ) • b) ∈ O := nat_smul_mem m (extDen_mem b)
  have hmd : (extDen b : ℚ) • ((m : ℚ) • b) ∈ O := nat_smul_mem (extDen b) hb
  have e1 := alpha_nat_smul α m _ (extDen_mem b) hdm
  have e2 := alpha_nat_smul α (extDen b) _ hb hmd
  have e3 : (⟨_, hdm⟩ : O) = ⟨_, hmd⟩ := Subtype.ext (smul_comm _ _ _)
  rw [e3, e2] at e1
  -- e1 : d • α(m b) = m • α(d b)
  unfold extFun
  have hX : (α ⟨_, extDen_mem b⟩ : B) = ((m : ℚ)⁻¹ * extDen b) • (α ⟨_, hb⟩ : B) := by
    rw [mul_smul, e1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul]
  rw [hX, smul_smul]
  congr 1
  have : (extDen b : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem extFun_coe (a : O) : extFun α a = α a := by
  have h1 : ((1 : ℕ) : ℚ) • (a : B) ∈ O := by simp
  rw [extFun_eq α a 1 one_pos h1]
  have : (⟨_, h1⟩ : O) = a := Subtype.ext (by simp)
  rw [this]; simp

/-- A common multiplier for two elements. -/
theorem common_den (b c : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O ∧ (m : ℚ) • c ∈ O := by
  refine ⟨extDen b * extDen c, Nat.mul_pos (extDen_pos b) (extDen_pos c), ?_, ?_⟩
  · have := nat_smul_mem (extDen c) (extDen_mem b)
    rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this
  · have := nat_smul_mem (extDen b) (extDen_mem c)
    rwa [smul_smul, ← Nat.cast_mul] at this

theorem extFun_add (b c : B) : extFun α (b + c) = extFun α b + extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc : (m : ℚ) • (b + c) ∈ O := by rw [smul_add]; exact O.add_mem hb hc
  rw [extFun_eq α _ m hm hbc, extFun_eq α _ m hm hb, extFun_eq α _ m hm hc, ← smul_add]
  congr 1
  have : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ + ⟨_, hc⟩ := Subtype.ext (by simp [smul_add])
  rw [this, map_add]; rfl

theorem smul_mul_smul' (r s : ℚ) (x y : B) : (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem extFun_mul (b c : B) : extFun α (b * c) = extFun α b * extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc0 : ((m : ℚ) * m) • (b * c) ∈ O := by
    rw [← smul_mul_smul']; exact O.mul_mem hb hc
  have hbc : ((m * m : ℕ) : ℚ) • (b * c) ∈ O := by rw [Nat.cast_mul]; exact hbc0
  have hprod : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ * ⟨_, hc⟩ := by
    apply Subtype.ext
    show ((m * m : ℕ) : ℚ) • (b * c) = ((m : ℚ) • b) * ((m : ℚ) • c)
    rw [smul_mul_smul', Nat.cast_mul]
  have e1 : (α ⟨_, hbc⟩ : B) = (α ⟨_, hb⟩ : B) * (α ⟨_, hc⟩ : B) := by
    rw [hprod, map_mul, MulMemClass.coe_mul]
  rw [extFun_eq α _ (m * m) (Nat.mul_pos hm hm) hbc, extFun_eq α _ m hm hb,
    extFun_eq α _ m hm hc, smul_mul_smul', e1, Nat.cast_mul, mul_inv]

theorem extFun_algebraMap (q : ℚ) : extFun α (algebraMap ℚ B q) = algebraMap ℚ B q := by
  have hq : ((q.den : ℕ) : ℚ) • algebraMap ℚ B q ∈ O := by
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast]
    exact intCast_mem O q.num
  rw [extFun_eq α _ q.den q.den_pos hq]
  have : (⟨_, hq⟩ : O) = (q.num : O) := Subtype.ext (by
    simp only [SubringClass.coe_intCast]
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast])
  rw [this, map_intCast, SubringClass.coe_intCast, ← map_intCast (algebraMap ℚ B),
    Algebra.smul_def, ← map_mul]
  congr 1
  rw [inv_mul_eq_div, Rat.num_div_den]

/-- The extension `α̃ : B → B` as a `ℚ`-algebra map. -/
def extAlgHom : B →ₐ[ℚ] B where
  toFun := extFun α
  map_one' := by simpa using extFun_coe α 1
  map_zero' := by simpa using extFun_coe α 0
  map_add' := extFun_add α
  map_mul' := extFun_mul α
  commutes' := extFun_algebraMap α

theorem extAlgHom_apply (b : B) : extAlgHom α b = extFun α b := rfl

theorem extAlgHom_coe (a : O) : extAlgHom α a = α a := extFun_coe α a

theorem extAlgHom_symm_comp : (extAlgHom α.symm).comp (extAlgHom α) = AlgHom.id ℚ B := by
  refine AlgHom.ext fun b => ?_
  change extAlgHom α.symm (extFun α b) = b
  rw [extFun_eq α b (extDen b) (extDen_pos b) (extDen_mem b), map_smul, extAlgHom_coe,
    RingEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (extDen_pos b).ne'),
    one_smul]

/-- The extension as a `ℚ`-algebra automorphism of `B`. -/
def extAlgEquiv : B ≃ₐ[ℚ] B :=
  AlgEquiv.ofAlgHom (extAlgHom α) (extAlgHom α.symm)
    (by simpa using extAlgHom_symm_comp α.symm) (extAlgHom_symm_comp α)

theorem extAlgEquiv_apply (b : B) : extAlgEquiv α b = extFun α b := rfl

/-! ### `AutOInnerFinite` from Skolem–Noether and the normalizer -/

/-- **Normalizer fact (N(𝒪)/ℚ^×𝒪^× finite).** Every `u ∈ B^×` normalizing `𝒪` is
`q · v · t` with `q ∈ ℚ^×`, `v ∈ 𝒪^×` and `t` in a fixed finite set. -/
def NormalizerFinite : Prop :=
  ∃ T : Set Bˣ, T.Finite ∧ ∀ u : Bˣ, (∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) →
    ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B)

/-- Skolem–Noether (proved in the kernel, `TSkolemKW.leafSkolemNoether`) applied to `α̃`. -/
theorem conj_of_skolem : ∃ u : Bˣ, ∀ b : B, extFun α b = u * b * ((u⁻¹ : Bˣ) : B) := by
  obtain ⟨u, hu⟩ := GlueDescent.B6_inner TSkolemKW.leafSkolemNoether (extAlgEquiv α)
  exact ⟨u, fun b => hu b⟩

/-- Conjugation by a unit of `𝒪`, `a ↦ v⁻¹ a v`. -/
def conjUnit (v : Oˣ) : O ≃+* O where
  toFun a := ((v⁻¹ : Oˣ) : O) * a * v
  invFun a := (v : O) * a * ((v⁻¹ : Oˣ) : O)
  left_inv a := by
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
  right_inv a := by
    simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]
  map_mul' a b := by
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  map_add' a b := by
    simp only [mul_add, add_mul]

theorem key_conj {R : Type*} [Ring R] (x y w w' c c' t : R) (hvv : w' * w = 1) (hcc : c' * c = 1)
    (hc : c * x = x * c) (h : x * (c * w * t) = c * w * t * y) : w' * x * w * t = t * y := by
  have h1 : x * w * t = w * t * y := by
    calc x * w * t = c' * (c * x) * w * t := by rw [← mul_assoc, hcc, one_mul]
      _ = c' * (x * (c * w * t)) := by rw [hc]; simp only [mul_assoc]
      _ = c' * (c * w * t * y) := by rw [h]
      _ = w * t * y := by simp only [← mul_assoc]; rw [hcc, one_mul]
  calc w' * x * w * t = w' * (x * w * t) := by simp only [mul_assoc]
    _ = w' * (w * t * y) := by rw [h1]
    _ = t * y := by simp only [← mul_assoc]; rw [hvv, one_mul]

/-- **`AutOInnerFinite` from the normalizer fact** (with Skolem–Noether from the kernel). -/
theorem autOInnerFinite_of_normalizer (hN : NormalizerFinite) : AutOInnerFinite := by
  classical
  obtain ⟨T, hT, hTu⟩ := hN
  let P : (O ≃+* O) → Bˣ → Prop := fun β t => ∀ a : O, ((β a : O) : B) * t = t * a
  let T' : Set (O ≃+* O) := {β | ∃ t ∈ T, P β t}
  let f : (O ≃+* O) → Bˣ := fun β => if h : ∃ t ∈ T, P β t then Classical.choose h else 1
  have hf : ∀ β ∈ T', f β ∈ T ∧ P β (f β) := by
    intro β hβ
    have hβ' : ∃ t ∈ T, P β t := hβ
    simp only [f, hβ', dite_true]
    exact Classical.choose_spec hβ'
  have hT' : T'.Finite := by
    refine Set.Finite.of_finite_image (f := f) (hT.subset (t := f '' T') ?_) ?_
    · rintro _ ⟨β, hβ, rfl⟩; exact (hf β hβ).1
    · intro β₁ h₁ β₂ h₂ heq
      apply RingEquiv.ext; intro a
      apply Subtype.ext
      have e1 := (hf β₁ h₁).2 a
      have e2 := (hf β₂ h₂).2 a
      rw [heq] at e1
      exact (Units.mul_left_inj (f β₂)).1 (e1.trans e2.symm)
  refine ⟨T', hT', fun α => ?_⟩
  obtain ⟨u, hu⟩ := conj_of_skolem α
  have hback : ∀ b : B, extFun α.symm (extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := hTu u hnorm
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← extFun_coe, hu, Units.inv_mul_cancel_right]
  let β : O ≃+* O := α.trans (conjUnit v)
  have hβ : ∀ a : O, β a = ((v⁻¹ : Oˣ) : O) * α a * v := fun a => rfl
  refine ⟨β, ⟨t, ht, fun a => ?_⟩, v, fun a => ?_⟩
  · have hvv : (((v⁻¹ : Oˣ) : O) : B) * ((v : O) : B) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul]; rfl
    have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq, map_one]
    have h := hrel a
    rw [huq] at h
    rw [hβ, MulMemClass.coe_mul, MulMemClass.coe_mul]
    exact key_conj _ _ _ _ _ _ _ hvv hcc (Algebra.commutes q _) h
  · rw [hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

end AutOExt

/-- **`MobiusGlueU` from the two curve facts, the leaf `TorsionStructure` (T5) and
`NormalizerFinite` (`N(𝒪)/ℚ^×𝒪^×` finite).** Skolem–Noether enters through the kernel's proof
`TSkolemKW.leafSkolemNoether`. -/
theorem mobiusGlue_of_normalizer (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hN : AutOExt.NormalizerFinite) : MobiusGlueU :=
  mobiusGlue_of_named hRF hSu hT (AutOExt.autOInnerFinite_of_normalizer hN)

end Pin

end AV

end LeafQM


/-! ## §8 `NormalizerFinite`, proved: `N(𝒪)/ℚ^×𝒪^×` is represented by `{1, i, j, ij}`

Descent on `|nrd|`. A prime `p ∤ 6` dividing `nrd(u)` of a normalizing `u ∈ 𝒪` divides `u`: an
explicit identity `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`,
`scratch/mobius-glue/py/normalizer_identity.py`). If `2 | nrd(u)` then `u i⁻¹ ∈ 𝒪`, and if
`3 | nrd(u)` then `u j⁻¹ ∈ 𝒪` (checks modulo 2 and 3 by `decide`). -/

namespace LeafQM

namespace AV

namespace Pin

namespace NormO

/-! ### Integer coordinates -/

/-- The reduced norm in the coordinates of `ofInt`. -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 + n 2 ^ 2 - 2 * n 3 ^ 2

/-- The conjugate in the coordinates of `ofInt`. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem mulCoord_conjC (n : Fin 4 → ℤ) : mulCoord n (conjC n) = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem mulCoord_conjC' (n : Fin 4 → ℤ) : mulCoord (conjC n) n = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem nrdZ_mul (n m : Fin 4 → ℤ) : nrdZ (mulCoord n m) = nrdZ n * nrdZ m := by
  simp [mulCoord, nrdZ]; ring

theorem ofInt_scalar (z : ℤ) : ofInt ![z, 0, 0, 0] = algebraMap ℚ B (z : ℚ) := by
  ext <;> simp [ofInt]

theorem smul_ofInt (z : ℤ) (n : Fin 4 → ℤ) : (z : ℚ) • ofInt n = ofInt (fun l => z * n l) := by
  ext <;> simp [ofInt] <;> ring

theorem mem_O_iff (x : B) : x ∈ O ↔ ∃ n, x = ofInt n := Iff.rfl

/-- `(1/z) • ofInt m ∈ 𝒪` forces `z ∣ m`. -/
theorem dvd_of_smul_mem {z : ℤ} (hz : z ≠ 0) {m : Fin 4 → ℤ}
    (h : ((z : ℚ)⁻¹) • ofInt m ∈ O) : ∀ l, z ∣ m l := by
  obtain ⟨w, hw⟩ := h
  have : ofInt m = ofInt (fun l => z * w l) := by
    rw [← smul_ofInt, ← hw, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hz), one_smul]
  have e := AV.ofInt_injective this
  intro l
  exact ⟨w l, congrFun e l⟩

/-! ### The units `i`, `j` of `B` -/

def ei : Fin 4 → ℤ := ![0, 1, 0, 0]
def ej : Fin 4 → ℤ := ![-1, 0, 2, 0]

theorem nrdZ_ei : nrdZ ei = -2 := by simp [nrdZ, ei]
theorem nrdZ_ej : nrdZ ej = 3 := by simp [nrdZ, ej]

def ui : Bˣ where
  val := ofInt ei
  inv := ((2 : ℚ)⁻¹) • ofInt ei
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]

def uj : Bˣ where
  val := ofInt ej
  inv := ((-3 : ℚ)⁻¹) • ofInt ej
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]

/-- The representatives `{1, i, j, ij}` of `N(𝒪)/ℚ^×𝒪^×`. -/
def T : Set Bˣ := {1, ui, uj, ui * uj}

theorem T_finite : T.Finite := by
  simp only [T]
  exact ((((Set.finite_singleton _).insert _).insert _).insert _)

/-! ### Normalizing units -/

/-- `u` normalizes `𝒪`. -/
def IsNorm (u : Bˣ) : Prop :=
  ∀ a ∈ O, (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O ∧ ((u⁻¹ : Bˣ) : B) * a * u ∈ O

theorem IsNorm.mul {u w : Bˣ} (hu : IsNorm u) (hw : IsNorm w) : IsNorm (u * w) := by
  intro a ha
  refine ⟨?_, ?_⟩
  · have := (hu _ (hw a ha).1).1
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this
  · have := (hw _ (hu a ha).2).2
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this

theorem IsNorm.inv {u : Bˣ} (hu : IsNorm u) : IsNorm u⁻¹ := by
  intro a ha
  obtain ⟨h1, h2⟩ := hu a ha
  exact ⟨h2, by simpa using h1⟩

/-- The unit `c ∈ ℚ^×` of `B`. -/
def sc (c : ℚ) (hc : c ≠ 0) : Bˣ where
  val := algebraMap ℚ B c
  inv := algebraMap ℚ B c⁻¹
  val_inv := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  inv_val := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]

theorem isNorm_sc (c : ℚ) (hc : c ≠ 0) : IsNorm (sc c hc) := by
  intro a ha
  have e1 : ((sc c hc : Bˣ) : B) * a * (((sc c hc)⁻¹ : Bˣ) : B) = a := by
    change algebraMap ℚ B c * a * algebraMap ℚ B c⁻¹ = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, mul_one]
  have e2 : (((sc c hc)⁻¹ : Bˣ) : B) * a * ((sc c hc : Bˣ) : B) = a := by
    change algebraMap ℚ B c⁻¹ * a * algebraMap ℚ B c = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, mul_one]
  exact ⟨by rw [e1]; exact ha, by rw [e2]; exact ha⟩

theorem isNorm_ui : IsNorm ui := by
  rintro a ⟨n, rfl⟩
  have e : ((ui : Bˣ) : B) * ofInt n * ((ui⁻¹ : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change ofInt ei * ofInt n * (((2 : ℚ)⁻¹) • ofInt ei) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  have e' : ((ui⁻¹ : Bˣ) : B) * ofInt n * ((ui : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change (((2 : ℚ)⁻¹) • ofInt ei) * ofInt n * ofInt ei = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

theorem isNorm_uj : IsNorm uj := by
  rintro a ⟨n, rfl⟩
  have e : ((uj : Bˣ) : B) * ofInt n * ((uj⁻¹ : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change ofInt ej * ofInt n * (((-3 : ℚ)⁻¹) • ofInt ej) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  have e' : ((uj⁻¹ : Bˣ) : B) * ofInt n * ((uj : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change (((-3 : ℚ)⁻¹) • ofInt ej) * ofInt n * ofInt ej = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

/-! ### The norm of a unit in `𝒪` and its inverse -/

theorem nrdZ_ne_zero (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) : nrdZ n ≠ 0 := by
  intro h0
  have h1 : (u : B) * ofInt (conjC n) = 0 := by
    rw [hu, ofInt_mul, mulCoord_conjC, h0, ofInt_scalar]; simp
  have h2 : ofInt (conjC n) = 0 := by
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) * x) h1
    simpa [← mul_assoc] using this
  have h3 : conjC n = 0 := AV.ofInt_injective (h2.trans ofInt_zero.symm)
  have h4 : n = 0 := by
    funext l
    have e0 := congrFun h3 0; have e1 := congrFun h3 1
    have e2 := congrFun h3 2; have e3 := congrFun h3 3
    simp [conjC] at e0 e1 e2 e3
    fin_cases l <;> simp <;> omega
  have : (u : B) = 0 := by rw [hu, h4, ofInt_zero]
  exact u.ne_zero this

theorem inv_eq (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) :
    ((u⁻¹ : Bˣ) : B) = ((nrdZ n : ℚ)⁻¹) • ofInt (conjC n) := by
  have hN : (nrdZ n : ℚ) ≠ 0 := by exact_mod_cast nrdZ_ne_zero u n hu
  apply Units.inv_eq_of_mul_eq_one_right
  rw [mul_smul_comm, hu, ofInt_mul, mulCoord_conjC, ofInt_scalar, Algebra.smul_def, ← map_mul,
    inv_mul_cancel₀ hN, map_one]

def bas : Fin 4 → (Fin 4 → ℤ) := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- For a normalizing `u = ofInt n`, `nrd(u)` divides every coordinate of `u e_k ū`. -/
theorem nrd_dvd_coords (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (k l : Fin 4) : nrdZ n ∣ mulCoord (mulCoord n (bas k)) (conjC n) l := by
  have h := (hN (ofInt (bas k)) ⟨_, rfl⟩).1
  rw [inv_eq u n hu, mul_smul_comm, hu, ofInt_mul, ofInt_mul] at h
  exact dvd_of_smul_mem (nrdZ_ne_zero u n hu) h l

/-- The identities `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`). -/
theorem six_sq_identities (n : Fin 4 → ℤ) :
    let F := fun k l => mulCoord (mulCoord n (bas k)) (conjC n) l
    6 * n 0 ^ 2 = 2 * F 0 0 + 2 * F 1 1 + 2 * F 1 3 + 2 * F 2 2 - 2 * F 3 1 ∧
    6 * n 1 ^ 2 = -F 1 1 - 2 * F 2 0 + F 3 1 + F 3 3 ∧
    6 * n 2 ^ 2 = 2 * F 0 0 - 2 * F 1 1 + 2 * F 2 2 - 2 * F 3 3 ∧
    6 * n 3 ^ 2 = F 1 1 + F 1 3 - 2 * F 2 0 - F 3 3 := by
  intro F
  simp only [F, mulCoord, bas, conjC]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> ring

/-- A prime `p ≠ 2, 3` dividing `nrd(u)` of a normalizing `u = ofInt n` divides `n`. -/
theorem dvd_of_prime_dvd_nrd (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (hpd : (p : ℤ) ∣ nrdZ n) :
    ∀ l, (p : ℤ) ∣ n l := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hF : ∀ k l, (p : ℤ) ∣ mulCoord (mulCoord n (bas k)) (conjC n) l :=
    fun k l => hpd.trans (nrd_dvd_coords u n hu hN k l)
  have h6 : ¬ (p : ℤ) ∣ 6 := by
    intro h
    have h' : p ∣ 6 := by exact_mod_cast h
    have : p ∣ 2 * 3 := h'
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  obtain ⟨i0, i1, i2, i3⟩ := six_sq_identities n
  have k0 : (p : ℤ) ∣ 6 * n 0 ^ 2 := by
    rw [i0]
    exact dvd_sub (dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 1 3) _))
      (dvd_mul_of_dvd_right (hF 2 2) _)) (dvd_mul_of_dvd_right (hF 3 1) _)
  have k1 : (p : ℤ) ∣ 6 * n 1 ^ 2 := by
    rw [i1]
    exact dvd_add (dvd_add (dvd_sub (dvd_neg.mpr (hF 1 1)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 1)) (hF 3 3)
  have k2 : (p : ℤ) ∣ 6 * n 2 ^ 2 := by
    rw [i2]
    exact dvd_sub (dvd_add (dvd_sub (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 2 2) _))
      (dvd_mul_of_dvd_right (hF 3 3) _)
  have k3 : (p : ℤ) ∣ 6 * n 3 ^ 2 := by
    rw [i3]
    exact dvd_sub (dvd_sub (dvd_add (hF 1 1) (hF 1 3)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 3)
  have key : ∀ l, (p : ℤ) ∣ 6 * n l ^ 2 := by
    intro l; fin_cases l
    exacts [k0, k1, k2, k3]
  intro l
  rcases hpZ.dvd_or_dvd (key l) with h | h
  · exact absurd h h6
  · exact hpZ.dvd_of_dvd_pow h

/-! ### The primes 2 and 3 -/

theorem two_dvd_mulCoord_ei (n : Fin 4 → ℤ) (h : (2 : ℤ) ∣ nrdZ n) :
    ∀ l, (2 : ℤ) ∣ mulCoord n ei l := by
  have hz : ((nrdZ n : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 2,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a = 0 ∧ c = 0 := by
    decide
  obtain ⟨h0, h2⟩ := key _ _ _ _ hz
  have d0 : (2 : ℤ) ∣ n 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h0
  have d2 : (2 : ℤ) ∣ n 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h2
  intro l
  fin_cases l <;> simp [mulCoord, ei] <;> omega

theorem three_dvd_mulCoord_ej (n : Fin 4 → ℤ) (h : (3 : ℤ) ∣ nrdZ n) :
    ∀ l, (3 : ℤ) ∣ mulCoord n ej l := by
  have hz : ((nrdZ n : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 3,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a - c = 0 ∧ b - d = 0 := by
    decide
  obtain ⟨h0, h1⟩ := key _ _ _ _ hz
  have d0 : (3 : ℤ) ∣ n 0 - n 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h0)
  have d1 : (3 : ℤ) ∣ n 1 - n 3 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h1)
  intro l
  fin_cases l <;> simp [mulCoord, ej] <;> omega

/-! ### Closure of `T` under right multiplication by `i` and `j` -/

theorem T_mem_iff (t : Bˣ) : t ∈ T ↔ t = 1 ∨ t = ui ∨ t = uj ∨ t = ui * uj := Iff.rfl

theorem T_mul_ui : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (ui : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, ui, by simp [T], by simp⟩
  · refine ⟨2, two_ne_zero, 1, by simp [T], ?_⟩
    change ofInt ei * ofInt ei = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ei, QuaternionAlgebra.algebraMap_eq]
  · refine ⟨-1, by norm_num, ui * uj, by simp [T], ?_⟩
    change ofInt ej * ofInt ei = _ * (ofInt ei * ofInt ej)
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-2, by norm_num, uj, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ei = _ * ofInt ej
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

theorem T_mul_uj : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (uj : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, uj, by simp [T], by simp⟩
  · exact ⟨1, one_ne_zero, ui * uj, by simp [T], by simp⟩
  · refine ⟨-3, by norm_num, 1, by simp [T], ?_⟩
    change ofInt ej * ofInt ej = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-3, by norm_num, ui, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ej = _ * ofInt ei
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

/-- Rearranging `q v t i = (q c) v t'` for central `c`. -/
theorem rearrange (q c : ℚ) (V Tt I T' : B) (h : Tt * I = algebraMap ℚ B c * T') :
    algebraMap ℚ B q * V * Tt * I = algebraMap ℚ B (q * c) * V * T' := by
  rw [mul_assoc (algebraMap ℚ B q * V), h, ← mul_assoc, mul_assoc (algebraMap ℚ B q),
    ← Algebra.commutes c V, ← mul_assoc, ← map_mul]

theorem mulCoord_smul_right (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord n (fun l => z * m l) = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem mulCoord_smul_left (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord (fun l => z * n l) m = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem nrdZ_smul (n : Fin 4 → ℤ) (z : ℤ) : nrdZ (fun l => z * n l) = z ^ 2 * nrdZ n := by
  simp [nrdZ]; ring

/-! ### The descent -/

theorem descent (m : ℕ) : ∀ (u : Bˣ) (n : Fin 4 → ℤ), (u : B) = ofInt n →
    (nrdZ n).natAbs = m → IsNorm u →
    ∃ q : ℚ, q ≠ 0 ∧ ∃ v : Oˣ, ∃ t ∈ T, (u : B) = algebraMap ℚ B q * ((v : O) : B) * t := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro u n hu hm hN
  have hN0 := nrdZ_ne_zero u n hu
  by_cases h1 : m = 1
  · have hsq : nrdZ n * nrdZ n = 1 := by
      have : (nrdZ n).natAbs = 1 := hm.trans h1
      rcases Int.natAbs_eq_iff.mp this with h | h <;> rw [h] <;> norm_num
    set w : Fin 4 → ℤ := fun l => nrdZ n * conjC n l with hw_def
    have hw1 : mulCoord n w = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_right, mulCoord_conjC]
      funext l; fin_cases l <;> simp [hsq]
    have hw2 : mulCoord w n = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_left, mulCoord_conjC']
      funext l; fin_cases l <;> simp [hsq]
    let v : Oˣ :=
      ⟨⟨ofInt n, n, rfl⟩, ⟨ofInt w, w, rfl⟩,
        Subtype.ext (by
          change ofInt n * ofInt w = 1
          rw [ofInt_mul, hw1, ofInt_one]),
        Subtype.ext (by
          change ofInt w * ofInt n = 1
          rw [ofInt_mul, hw2, ofInt_one])⟩
    refine ⟨1, one_ne_zero, v, 1, by simp [T], ?_⟩
    rw [map_one, one_mul, Units.val_one, mul_one]
    exact hu
  · have hm0 : m ≠ 0 := by
      rintro rfl; exact hN0 (Int.natAbs_eq_zero.mp hm)
    set p := m.minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime h1
    have hpd : (p : ℤ) ∣ nrdZ n := by
      rw [Int.natCast_dvd, hm]; exact Nat.minFac_dvd m
    have hp1 : 2 ≤ p := hp.two_le
    by_cases hp2 : p = 2
    · have h2 : (2 : ℤ) ∣ nrdZ n := by rw [hp2] at hpd; exact_mod_cast hpd
      have hc := two_dvd_mulCoord_ei n h2
      set n' : Fin 4 → ℤ := fun l => mulCoord n ei l / 2 with hn'_def
      have hn' : mulCoord n ei = fun l => 2 * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hc l)).symm
      have hu' : ((u * ui⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((2 : ℚ)⁻¹) • ofInt ei) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ei = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * ui⁻¹ : Bˣ) : B) * ((ui : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ei
        rw [hmul, nrdZ_ei] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h2' : (-2 : ℤ).natAbs = 2 := rfl
        rw [← hm, e, Int.natAbs_mul, h2']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * ui⁻¹) n' hu' rfl (hN.mul isNorm_ui.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_ui t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * ui⁻¹ : Bˣ) : B) * ui := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    by_cases hp3 : p = 3
    · have h3 : (3 : ℤ) ∣ nrdZ n := by rw [hp3] at hpd; exact_mod_cast hpd
      have hc := three_dvd_mulCoord_ej n h3
      set n' : Fin 4 → ℤ := fun l => -(mulCoord n ej l / 3) with hn'_def
      have hn' : mulCoord n ej = fun l => (-3) * n' l := by
        funext l
        simp only [hn'_def]
        rw [mul_neg, neg_mul, neg_neg, Int.mul_ediv_cancel' (hc l)]
      have hu' : ((u * uj⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((-3 : ℚ)⁻¹) • ofInt ej) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ej = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * uj⁻¹ : Bˣ) : B) * ((uj : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ej
        rw [hmul, nrdZ_ej] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h3' : (3 : ℤ).natAbs = 3 := rfl
        rw [← hm, e, Int.natAbs_mul, h3']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * uj⁻¹) n' hu' rfl (hN.mul isNorm_uj.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_uj t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * uj⁻¹ : Bˣ) : B) * uj := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    · have hdiv := dvd_of_prime_dvd_nrd u n hu hN p hp hp2 hp3 hpd
      set n' : Fin 4 → ℤ := fun l => n l / p with hn'_def
      have hn' : n = fun l => (p : ℤ) * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hdiv l)).symm
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpi : ((p : ℚ)⁻¹) ≠ 0 := inv_ne_zero hp0
      have hu' : ((sc _ hpi * u : Bˣ) : B) = ofInt n' := by
        change algebraMap ℚ B ((p : ℚ)⁻¹) * u = _
        rw [← Algebra.smul_def, hu, hn', ← smul_ofInt, smul_smul]
        push_cast
        rw [inv_mul_cancel₀ hp0, one_smul]
      have hlt : (nrdZ n').natAbs < m := by
        have e : nrdZ n = (p : ℤ) ^ 2 * nrdZ n' := by rw [hn', nrdZ_smul]
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        rw [← hm, e, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        have : 4 ≤ p ^ 2 := by nlinarith
        have : (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs := by
          have : 1 * (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          simpa using this
        exact this
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (sc _ hpi * u) n' hu' rfl ((isNorm_sc _ hpi).mul hN)
      refine ⟨p * q, mul_ne_zero hp0 hq, v, t, ht, ?_⟩
      have : (u : B) = algebraMap ℚ B (p : ℚ) * ((sc _ hpi * u : Bˣ) : B) := by
        change _ = _ * (algebraMap ℚ B ((p : ℚ)⁻¹) * u)
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one, one_mul]
      rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

/-! ### `NormalizerFinite` -/

/-- **`N(𝒪)/ℚ^×𝒪^×` is finite** (represented by `{1, i, j, ij}`). -/
theorem normalizerFinite : AutOExt.NormalizerFinite := by
  refine ⟨T, T_finite, fun u hu => ?_⟩
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

end NormO

open CategoryTheory AlgebraicGeometry

/-- **`AutOInnerFinite`, proved** (Skolem–Noether from the kernel, the normalizer from §8). -/
theorem autOInnerFinite : AutOInnerFinite :=
  AutOExt.autOInnerFinite_of_normalizer NormO.normalizerFinite

/-- **`TwistClassFinite` from the leaf `TorsionStructure` alone.** -/
theorem twistClassFinite (hT : ObjBridge.TorsionStructure) : TwistClassFinite :=
  twistClassFinite_of hT autOInnerFinite

/-- **Main result: `MobiusGlueU` from the two curve facts and the textbook leaf
`TorsionStructure` (T5).** -/
theorem mobiusGlue_of_curves (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) : MobiusGlueU :=
  mobiusGlue_of_curveFacts hRF hSu (twistClassFinite hT)

/-- **The comparison of two triples from the curve facts and T5.** -/

/-- (g0-assemble2) the repaired `R1fpProps` of Leaves.lean gives mobius-glue's `R1fpPropsU`. -/
theorem r1fpPropsU_of {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpProps Y Φ) : R1fpPropsU Y Φ :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩

/-- (g0-assemble2) mobius-glue's `MobiusGlueU` gives Leaves.lean's `MobiusGlue`. -/
theorem mobiusGlue_of_U (h : MobiusGlueU) : MobiusGlue := by
  intro Y Y' Φ Φ' π π' g h1 h2 h1' h2' hCM hΦ y
  exact h Y Y' Φ Φ' π π' g (r1fpPropsU_of h1) h2 (r1fpPropsU_of h1') h2' hCM hΦ y

/-- **`MobiusGlue` (Leaves.lean's) from the two curve facts and T5** (mobius-glue). -/
theorem mobiusGlue_of_curves' (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_U (mobiusGlue_of_curves hRF hSu hT)

end Pin

end AV

end LeafQM

/-! ## g0-assemble2: curve-facts (scratch/curve-facts/CurveFacts.lean lines 3-38 and 84-end, verbatim; its §0
(lines 39-83) copies `Mob.ratEval`, `CurveRatFactor`, `CurveSurj` from mobius-glue, defined in part a55) -/

/-!
# curve-facts: `CurveRatFactor` and `CurveSurj` reduced to per-component curve facts

Task curve-facts (2026-11-13). See `docs/research/curve-facts.md`.

`CurveRatFactor` and `CurveSurj` are copied verbatim from `scratch/mobius-glue/MobiusGlue.lean`
(§2), together with `Mob.ratEval` (§1 there). Everything else they use (`ToP1`, `ToP1.val`,
`fieldPt`, `Qbar`) is imported from `ZInQKernel.HDecomp.QM.Pairs`, where mobius-glue took it from.

**Main results.**
* `curveSurj_of_comp : GeomCompInfinite → GeomCompConstOrOnto → CurveSurj`;
* `curveRatFactor_of_comp : GeomCompConstOrOnto → GeomCompRatFactor → CurveRatFactor`, using
  `geomCompFinite` (proved here from Mathlib: `S_ℚ̄` is a Noetherian scheme, so it has finitely
  many irreducible, hence connected, components) and `Mob.exists_interp` (proved here: rational
  interpolation of values in `P¹` at finitely many nodes by a coprime pair).

The named facts are stated over genuine definitions only: the base change
`S_ℚ̄ = S ×_{Spec ℚ} Spec ℚ̄` (Mathlib's `pullback`), the `ℚ̄`-point of `S_ℚ̄` induced by a
`ℚ̄`-point of `S` (`pullback.lift`), its point (`Scheme.SpecToEquivOfField`), and Mathlib's
`connectedComponent` in the underlying space of `S_ℚ̄`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits
open PkgI3

/-! ## §1 Geometric components (genuine definitions) -/

/-- `S_ℚ̄ = S ×_{Spec ℚ} Spec ℚ̄` (Mathlib's pullback). -/
abbrev bcQbar (S : Over (Spec (CommRingCat.of ℚ))) : Scheme.{0} :=
  pullback S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))

/-- The `ℚ̄`-point `Spec ℚ̄ → S_ℚ̄` (a section over `Spec ℚ̄`) induced by a `ℚ̄`-point of `S`
over `ℚ`. -/
def bcPt {S : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt Qbar ⟶ S) :
    Spec (CommRingCat.of Qbar) ⟶ bcQbar S :=
  pullback.lift y.left (𝟙 _) ((Over.w y).trans (Category.id_comp _).symm)

/-- **The geometric component of a `ℚ̄`-point `y` of `S`**: the connected component of the
underlying space of `S_ℚ̄` containing the (closed) point of `S_ℚ̄` at which `bcPt y` sits. For
`S` smooth over `ℚ` the connected components of `S_ℚ̄` are its irreducible components (smooth
implies normal implies locally irreducible). -/
def geomComp {S : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt Qbar ⟶ S) : Set (bcQbar S) :=
  connectedComponent (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1

/-! ## §2 The named facts -/

/-- **(C1) A geometric component of a smooth curve has infinitely many `ℚ̄`-points.**
Glue (STANDARD): a connected component `C` of `S_ℚ̄` is a smooth curve over `ℚ̄` (a nonempty
scheme of finite type over `ℚ̄` of dimension 1); its closed points are its `ℚ̄`-points
(Nullstellensatz) and there are infinitely many of them (a Jacobson scheme with finitely many
closed points is a finite discrete set, of dimension 0); a `ℚ̄`-point of `S_ℚ̄` over `ℚ̄` is
`bcPt y` for a unique `ℚ̄`-point `y` of `S` over `ℚ` (universal property of the pullback).
Properness is not needed. Not in Mathlib v4.35 (no dimension theory of smooth morphisms). -/
def GeomCompInfinite : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ y₀ : fieldPt Qbar ⟶ S, {y : fieldPt Qbar ⟶ S | geomComp y = geomComp y₀}.Infinite

/-- **(C2) Constant or onto on a geometric component** (Hartshorne, *Algebraic Geometry*,
Prop. II.6.8: a morphism from a complete nonsingular curve to a curve is constant or
surjective; UNVERIFIED numbering, cited so in mobius-glue). On the geometric component of `y₀`,
`σ` either takes the single value `σ(y₀)` at every `ℚ̄`-point, or takes every value of
`P¹(ℚ̄)`. Textbook leaf (published; applied to the connected component of `S_ℚ̄`, a complete
nonsingular curve over `ℚ̄`, with the dictionary between `ℚ̄`-points of `S` and closed points of
`S_ℚ̄`). Not in Mathlib v4.35 (Mathlib has `IsProper → IsClosedMap`, but no `P¹` as a scheme
and no dimension theory of curves). -/
def GeomCompConstOrOnto : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ (σ : ToP1 S.left) (y₀ : fieldPt Qbar ⟶ S),
      (∀ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ →
        σ.val (K := Qbar) y.left = σ.val (K := Qbar) y₀.left) ∨
      (∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
        σ.val (K := Qbar) y.left = t)

open Polynomial in
/-- **(C3) Factorization on one geometric component where `σ` is nonconstant.** If `σ` is
nonconstant on the geometric component `C` of `y₀` and `ρ` is constant on the `σ`-fibres in `C`
(on `ℚ̄`-points), then `ρ = [F : G] ∘ σ` on the `ℚ̄`-points of `C` with finite `σ`-value, for
coprime `F, G ∈ ℚ̄[t]`. Textbook (STANDARD): `σ|_C : C → P¹` is finite of some degree `n`, and
`ℚ̄(σ) ⊆ ℚ̄(σ, ρ) ⊆ ℚ̄(C)`; the normalization `D` of the image of `(σ, ρ)` is a smooth complete
curve with `D → P¹` finite of degree `[ℚ̄(σ, ρ) : ℚ̄(σ)]`, separable (char. 0), so its general
fibre has that many points (Hartshorne II.6.9 and IV.2.2, UNVERIFIED numbering); the fibre
condition makes the general fibre a single point, so `ℚ̄(σ, ρ) = ℚ̄(σ)`, `ρ = R(σ)` in `ℚ̄(C)`,
and two morphisms `C → P¹` agreeing generically agree (C reduced, `P¹` separated).
Classified as glue (a standard consequence of textbook theorems, not one printed theorem). Not
in Mathlib v4.35 (no degree of a finite morphism of curves, no fibre count). -/
def GeomCompRatFactor : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ (σ ρ : ToP1 S.left) (y₀ : fieldPt Qbar ⟶ S),
      (∃ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
        σ.val (K := Qbar) y.left ≠ σ.val (K := Qbar) y₀.left) →
      (∀ y₁ y₂ : fieldPt Qbar ⟶ S, geomComp y₁ = geomComp y₀ → geomComp y₂ = geomComp y₀ →
        σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left →
        ρ.val (K := Qbar) y₁.left = ρ.val (K := Qbar) y₂.left) →
      ∃ F G : Qbar[X], IsCoprime F G ∧ ∀ (y : fieldPt Qbar ⟶ S) (t : Qbar),
        geomComp y = geomComp y₀ → σ.val (K := Qbar) y.left = OnePoint.some t →
        ρ.val (K := Qbar) y.left = Mob.ratEval F G t

/-- **(C4) Finitely many geometric components.** Proved below (`geomCompFinite`). -/
def GeomCompFinite : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom →
    (Set.range (geomComp (S := S))).Finite

/-! ## §3 `GeomCompFinite`, from Mathlib -/

theorem geomCompFinite : GeomCompFinite := by
  intro S hP
  have : IsNoetherian (bcQbar S) := { }
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := bcQbar S)
  classical
  refine (hfin.image (fun Z => if h : Z.Nonempty then connectedComponent h.some else ∅)).subset ?_
  rintro _ ⟨y, rfl⟩
  set x := (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1 with hx
  have hne : (irreducibleComponent x).Nonempty := ⟨x, mem_irreducibleComponent⟩
  refine ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, ?_⟩
  simp only [dite_eq_left hne]
  exact (connectedComponent_eq (irreducibleComponent_subset_connectedComponent hne.some_mem)).symm

/-! ## §4 Rational interpolation by a coprime pair -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]

theorem isCoprime_X_sub_C_of_eval_one {F : K[X]} {a : K} (h : F.eval a = 1) :
    IsCoprime F (X - C a) := by
  have e := modByMonic_add_div F (X - C a)
  rw [modByMonic_X_sub_C_eq_C_eval, h, map_one] at e
  exact ⟨1, -(F /ₘ (X - C a)), by linear_combination (-1 : K[X]) * e⟩

/-- **Rational interpolation.** Any assignment of values in `P¹(K)` to finitely many nodes
`t ∈ T ⊆ K` is realised by `[F : G]` with `F, G` coprime. -/
theorem exists_interp (T : Finset K) (r : K → OnePoint K) :
    ∃ F G : K[X], IsCoprime F G ∧ ∀ t ∈ T, ratEval F G t = r t := by
  classical
  set Tinf := T.filter (fun t => r t = OnePoint.infty) with hTinf
  set G : K[X] := ∏ a ∈ Tinf, (X - C a) with hG
  have hGeval : ∀ t, G.eval t = ∏ a ∈ Tinf, (t - a) := by
    intro t; simp [hG, eval_prod]
  have hG0 : ∀ t ∈ Tinf, G.eval t = 0 := by
    intro t ht; rw [hGeval]; exact Finset.prod_eq_zero ht (sub_self t)
  have hGne : ∀ t, t ∉ Tinf → G.eval t ≠ 0 := by
    intro t ht; rw [hGeval, Finset.prod_ne_zero_iff]
    intro a ha e; exact ht (by rwa [sub_eq_zero.mp e])
  let w : K → K := fun t =>
    if h : ∃ v : K, r t = OnePoint.some v then h.choose * G.eval t else 1
  set F : K[X] := Lagrange.interpolate T id w with hF
  have hFeval : ∀ t ∈ T, F.eval t = w t := fun t ht =>
    Lagrange.eval_interpolate_at_node (v := id) w (Set.injOn_id _) ht
  refine ⟨F, G, ?_, ?_⟩
  · refine IsCoprime.prod_right fun a ha => isCoprime_X_sub_C_of_eval_one ?_
    have haT : a ∈ T := (Finset.mem_filter.mp ha).1
    have hra : r a = OnePoint.infty := (Finset.mem_filter.mp ha).2
    rw [hFeval a haT]
    have : ¬ ∃ v : K, r a = OnePoint.some v := by
      rintro ⟨v, hv⟩; rw [hra] at hv; exact OnePoint.infty_ne_coe v hv
    simp only [w, dite_eq_right this]
  · intro t ht
    by_cases hti : t ∈ Tinf
    · rw [(Finset.mem_filter.mp hti).2]; simp [ratEval, hG0 t hti]
    · have hrt : r t ≠ OnePoint.infty := fun e => hti (Finset.mem_filter.mpr ⟨ht, e⟩)
      have hex : ∃ v : K, r t = OnePoint.some v := by
        induction h : r t using OnePoint.rec with
        | infty => exact absurd h hrt
        | coe v => exact ⟨v, rfl⟩
      have hGt := hGne t hti
      rw [ratEval, ite_eq_right hGt, hFeval t ht]
      simp only [w, dite_eq_left hex]
      rw [mul_div_cancel_right₀ _ hGt]
      exact hex.choose_spec.symm

end Mob

/-! ## §5 The reductions -/

/-- **`CurveSurj` from (C1) and (C2).** -/
theorem curveSurj_of_comp (h1 : GeomCompInfinite) (h2 : GeomCompConstOrOnto) : CurveSurj := by
  intro S hP hS ⟨y₀⟩ σ hfin t
  rcases h2 S hP hS σ y₀ with hc | ho
  · exact absurd ((hfin y₀).subset fun y hy => hc y hy) (h1 S hP hS y₀)
  · obtain ⟨y, -, hy⟩ := ho t
    exact ⟨y, hy⟩

/-- **`CurveRatFactor` from (C2) and (C3)** (with (C4), proved, and rational interpolation). -/
theorem curveRatFactor_of_comp (h2 : GeomCompConstOrOnto) (h3 : GeomCompRatFactor) :
    CurveRatFactor := by
  classical
  intro S hP hS σ ρ hfib
  by_cases hnc : ∃ y₀ y : fieldPt Qbar ⟶ S, geomComp y = geomComp y₀ ∧
      σ.val (K := Qbar) y.left ≠ σ.val (K := Qbar) y₀.left
  · -- a component on which `σ` is nonconstant: it is onto, and carries the rational function
    obtain ⟨y₀, hne⟩ := hnc
    obtain ⟨F, G, hcop, hR⟩ := h3 S hP hS σ ρ y₀ hne (fun y₁ y₂ _ _ h => hfib y₁ y₂ h)
    refine ⟨F, G, hcop, fun y t hy => ?_⟩
    rcases h2 S hP hS σ y₀ with hc | ho
    · obtain ⟨y', hy', hne'⟩ := hne
      exact absurd (hc y' hy') hne'
    · obtain ⟨y', hy'c, hy't⟩ := ho (OnePoint.some t)
      rw [hfib y y' (hy.trans hy't.symm)]
      exact hR y' t hy'c hy't
  · -- `σ` constant on every component: finitely many values; interpolate
    push Not at hnc
    have hV : (Set.range fun y : fieldPt Qbar ⟶ S => σ.val (K := Qbar) y.left).Finite := by
      refine ((geomCompFinite S hP).image (fun c => if h : ∃ y : fieldPt Qbar ⟶ S,
        geomComp y = c then σ.val (K := Qbar) h.choose.left else OnePoint.infty)).subset ?_
      rintro _ ⟨y, rfl⟩
      have h : ∃ y' : fieldPt Qbar ⟶ S, geomComp y' = geomComp y := ⟨y, rfl⟩
      refine ⟨geomComp y, ⟨y, rfl⟩, ?_⟩
      simp only [dite_eq_left h]
      exact (hnc h.choose y h.choose_spec.symm).symm
    have hT : {t : Qbar | (OnePoint.some t) ∈
        Set.range fun y : fieldPt Qbar ⟶ S => σ.val (K := Qbar) y.left}.Finite :=
      hV.preimage (OnePoint.coe_injective.injOn)
    let r : Qbar → OnePoint Qbar := fun t =>
      if h : ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = OnePoint.some t then
        ρ.val (K := Qbar) h.choose.left else OnePoint.infty
    obtain ⟨F, G, hcop, hFG⟩ := Mob.exists_interp hT.toFinset r
    refine ⟨F, G, hcop, fun y t hy => ?_⟩
    have hmem : t ∈ hT.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨y, hy⟩
    have h : ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = OnePoint.some t := ⟨y, hy⟩
    rw [hFG t hmem]
    simp only [r, dite_eq_left h]
    exact hfib y h.choose (hy.trans h.choose_spec.symm)

/-- **Both curve facts from (C1), (C2), (C3).** -/
theorem curveFacts_of_comp (h1 : GeomCompInfinite) (h2 : GeomCompConstOrOnto)
    (h3 : GeomCompRatFactor) : CurveRatFactor ∧ CurveSurj :=
  ⟨curveRatFactor_of_comp h2 h3, curveSurj_of_comp h1 h2⟩

/-! ## §6 (C1) from "no isolated points" -/

/-- **(C1a) A scheme smooth of relative dimension 1 over a field has no isolated point.**
Glue (STANDARD): every point of `X` has an open neighbourhood étale over `𝔸¹_K`, so every
irreducible component of `X` has dimension 1 and every nonempty open of `X` is infinite; an open
point would be a nonempty finite open. Stated for any field `K` and any `X` (the use below is
`X = S_ℚ̄`, `K = ℚ̄`). Not in Mathlib v4.35 (no dimension theory of smooth morphisms). -/
def SmoothCurveNoIsolatedPoint : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    SmoothOfRelativeDimension 1 f → ∀ x : X, ¬ IsOpen ({x} : Set X)

/-- In a Noetherian space, connected components are open. -/
theorem isOpen_connectedComponent_of_noetherian {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (x : α) : IsOpen (connectedComponent x) := by
  classical
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)
  have hc : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents α | ¬ Z ⊆ connectedComponent x}, Z := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hz
      exact ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z,
        fun h => hz (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZC⟩, hzZ⟩ hzC
      apply hZC
      have : Z ⊆ connectedComponent z := hZ.1.isConnected.subset_connectedComponent hzZ
      rwa [← connectedComponent_eq hzC] at this
  rw [← isClosed_compl_iff, hc]
  exact (hfin.subset fun Z hZ => hZ.1).isClosed_biUnion fun Z hZ =>
    isClosed_of_mem_irreducibleComponents Z hZ.1

/-- In a Jacobson space, a nonempty open set with finitely many closed points contains an open
point. -/
theorem exists_isOpen_singleton_of_finite_closedPoints {α : Type*} [TopologicalSpace α]
    [JacobsonSpace α] {U : Set α} (hU : IsOpen U) (hne : U.Nonempty)
    (hfin : (U ∩ closedPoints α).Finite) : ∃ z, IsOpen ({z} : Set α) := by
  classical
  set F := U ∩ closedPoints α with hF
  have hclosed : ∀ G ⊆ F, IsClosed G := by
    intro G hG
    rw [← G.biUnion_of_singleton]
    exact (hfin.subset hG).isClosed_biUnion fun w hw => mem_closedPoints_iff.mp (hG hw).2
  have hFc : IsClosed F := hclosed F le_rfl
  -- `U ⊆ F`: otherwise `U \ F` is a nonempty open with no closed point
  have hUF : U ⊆ F := by
    by_contra hsub
    obtain ⟨z, hzU, hzF⟩ := Set.not_subset.mp hsub
    obtain ⟨w, ⟨hwU, hwF⟩, hwc⟩ := nonempty_inter_closedPoints (Z := U ∩ Fᶜ)
      ⟨z, hzU, hzF⟩ (hU.inter hFc.isOpen_compl).isLocallyClosed
    exact hwF ⟨hwU, hwc⟩
  obtain ⟨z, hz⟩ := hne
  refine ⟨z, ?_⟩
  have hrest : IsClosed (F \ {z}) := hclosed _ Set.sdiff_subset
  have : ({z} : Set α) = U ∩ (F \ {z})ᶜ := by
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff,
      not_and, not_not]
    constructor
    · rintro rfl; exact ⟨hz, fun _ => rfl⟩
    · rintro ⟨hwU, h⟩; exact h (hUF hwU)
  rw [this]; exact hU.inter hrest.isOpen_compl

/-- **(C1) from (C1a).** -/
theorem geomCompInfinite_of (h : SmoothCurveNoIsolatedPoint) : GeomCompInfinite := by
  intro S hP hS y₀
  classical
  let f : bcQbar S ⟶ Spec (CommRingCat.of Qbar) :=
    pullback.snd S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))
  have : IsNoetherian (bcQbar S) := { }
  have : LocallyOfFiniteType f := by
    show LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have hsm : SmoothOfRelativeDimension 1 f := by
    show SmoothOfRelativeDimension 1 (pullback.snd _ _); infer_instance
  have : JacobsonSpace (bcQbar S) := LocallyOfFiniteType.jacobsonSpace f
  set x₀ := (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y₀)).1 with hx₀
  -- the closed points of the component of `x₀` are infinitely many
  have hCinf : (connectedComponent x₀ ∩ closedPoints (bcQbar S)).Infinite := by
    intro hfin
    obtain ⟨z, hz⟩ := exists_isOpen_singleton_of_finite_closedPoints
      (isOpen_connectedComponent_of_noetherian x₀) ⟨x₀, mem_connectedComponent⟩ hfin
    exact h Qbar (bcQbar S) f hsm z hz
  -- each of them comes from a `ℚ̄`-point of `S` in the component
  intro hfin
  apply hCinf
  refine (hfin.image fun y => (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1).subset ?_
  rintro x ⟨hxC, hxc⟩
  let p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S := pointOfClosedPoint f x hxc
  have hp : p ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hxc
  let y : fieldPt Qbar ⟶ S := Over.homMk (p ≫ pullback.fst _ _) (by
    change (p ≫ pullback.fst _ _) ≫ S.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ f) ≫ _ = _
    rw [hp, Category.id_comp])
  have hy : bcPt y = p := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans hp.symm
  have hpt : (Scheme.SpecToEquivOfField Qbar (bcQbar S) (bcPt y)).1 = x := by
    rw [hy]; exact pointOfClosedPoint_apply f x hxc _
  refine ⟨y, ?_, hpt⟩
  show geomComp y = geomComp y₀
  unfold geomComp
  rw [hpt, ← hx₀]
  exact (connectedComponent_eq hxC).symm

/-- **Both curve facts from (C1a), (C2), (C3).** -/
theorem curveFacts_of_named (h1 : SmoothCurveNoIsolatedPoint) (h2 : GeomCompConstOrOnto)
    (h3 : GeomCompRatFactor) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_comp (geomCompInfinite_of h1) h2 h3

/-! ## §7 C2 and C3 over an algebraically closed field (Hartshorne's setting)

The leaves C2 and C3 are restated for a proper smooth curve `X` over an arbitrary algebraically
closed field `K`, its `K`-points (sections `p : Spec K → X` of the structure map) and a connected
component of `X`. `GeomCompConstOrOnto` and `GeomCompRatFactor` follow by base change to `ℚ̄`. -/

/-- The point of `X` at which a field point `p : Spec K → X` sits. -/
abbrev ptOf {K : Type} [Field K] {X : Scheme.{0}} (p : Spec (CommRingCat.of K) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField K X p).1

/-- **(C2K) Constant or onto on a connected component** (Hartshorne, *Algebraic Geometry*,
Prop. II.6.8, UNVERIFIED numbering: a morphism from a complete nonsingular curve over an
algebraically closed field to a curve is constant or surjective; here applied to a connected
component of `X`, a complete nonsingular irreducible curve, and the target `P¹`, whose closed
points are its `K`-points). Textbook leaf. -/
def ConstOrOntoAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → σ.val p = σ.val p₀) ∨
      (∀ t : OnePoint K, ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p = t)

open Polynomial in
/-- **(C3K) Factorization on a connected component where `σ` is nonconstant**, over an
algebraically closed field of characteristic 0 (in characteristic `p` the Frobenius
`σ = ρ^p` is a counterexample). Glue (a standard consequence of textbook results, see
`docs/research/curve-facts.md` §3). -/
def RatFactorAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p₁ p₂ : Spec (CommRingCat.of K) ⟶ X, p₁ ≫ f = 𝟙 _ → p₂ ≫ f = 𝟙 _ →
        connectedComponent (ptOf p₁) = connectedComponent (ptOf p₀) →
        connectedComponent (ptOf p₂) = connectedComponent (ptOf p₀) →
        σ.val p₁ = σ.val p₂ → ρ.val p₁ = ρ.val p₂) →
      ∃ F G : K[X], IsCoprime F G ∧ ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
        σ.val p = OnePoint.some t → ρ.val p = Mob.ratEval F G t

section Dictionary

variable {S : Over (Spec (CommRingCat.of ℚ))}

/-- The structure map `S_ℚ̄ → Spec ℚ̄`. -/
abbrev bcSnd (S : Over (Spec (CommRingCat.of ℚ))) : bcQbar S ⟶ Spec (CommRingCat.of Qbar) :=
  pullback.snd S.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))

theorem bcPt_snd (y : fieldPt Qbar ⟶ S) : bcPt y ≫ bcSnd S = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The `ℚ̄`-point of `S` over `ℚ` underlying a section of `S_ℚ̄ → Spec ℚ̄`. -/
def ptOfSection (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _) :
    fieldPt Qbar ⟶ S :=
  Over.homMk (p ≫ pullback.fst _ _) (by
    change (p ≫ pullback.fst _ _) ≫ S.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ bcSnd S) ≫ _ = _
    rw [hp, Category.id_comp])

theorem bcPt_ptOfSection (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _) :
    bcPt (ptOfSection p hp) = p := by
  apply pullback.hom_ext
  · exact pullback.lift_fst _ _ _
  · exact (pullback.lift_snd _ _ _).trans hp.symm

/-- `σ(y) = (σ ∘ pr₁)(bcPt y)`. -/
theorem val_bcPt (σ : ToP1 S.left) (y : fieldPt Qbar ⟶ S) :
    (σ.comp (pullback.fst _ _)).val (bcPt y) = σ.val (K := Qbar) y.left := by
  rw [ToP1.val_comp_right]
  exact congrArg _ (pullback.lift_fst _ _ _)

end Dictionary

/-- **C2 from C2K.** -/
theorem geomCompConstOrOnto_of (h : ConstOrOntoAlgClosed) : GeomCompConstOrOnto := by
  intro S hP hS σ y₀
  have hPf : IsProper (bcSnd S) := inferInstance
  have hSf : SmoothOfRelativeDimension 1 (bcSnd S) := inferInstance
  rcases h Qbar (bcQbar S) (bcSnd S) hPf hSf (σ.comp (pullback.fst _ _)) (bcPt y₀)
    (bcPt_snd y₀) with hc | ho
  · left
    intro y hy
    rw [← val_bcPt, ← val_bcPt]
    exact hc (bcPt y) (bcPt_snd y) hy
  · right
    intro t
    obtain ⟨p, hp, hcc, hv⟩ := ho t
    refine ⟨ptOfSection p hp, ?_, ?_⟩
    · show connectedComponent (ptOf (bcPt (ptOfSection p hp))) = _
      rw [bcPt_ptOfSection]; exact hcc
    · rw [← val_bcPt, bcPt_ptOfSection]; exact hv

/-- **C3 from C3K.** -/
theorem geomCompRatFactor_of (h : RatFactorAlgClosed) : GeomCompRatFactor := by
  intro S hP hS σ ρ y₀ hne hfib
  have hPf : IsProper (bcSnd S) := inferInstance
  have hSf : SmoothOfRelativeDimension 1 (bcSnd S) := inferInstance
  have hcc : ∀ (p : Spec (CommRingCat.of Qbar) ⟶ bcQbar S) (hp : p ≫ bcSnd S = 𝟙 _),
      geomComp (ptOfSection p hp) = connectedComponent (ptOf p) := by
    intro p hp
    show connectedComponent (ptOf (bcPt (ptOfSection p hp))) = _
    rw [bcPt_ptOfSection]
  obtain ⟨F, G, hcop, hR⟩ := h Qbar (bcQbar S) (bcSnd S) hPf hSf (σ.comp (pullback.fst _ _))
    (ρ.comp (pullback.fst _ _)) (bcPt y₀) (bcPt_snd y₀) (by
      obtain ⟨y, hy, hv⟩ := hne
      refine ⟨bcPt y, bcPt_snd y, hy, ?_⟩
      rw [val_bcPt, val_bcPt]; exact hv) (by
      intro p₁ p₂ hp₁ hp₂ h₁ h₂ hv
      have e₁ := val_bcPt σ (ptOfSection p₁ hp₁)
      have e₂ := val_bcPt σ (ptOfSection p₂ hp₂)
      have f₁ := val_bcPt ρ (ptOfSection p₁ hp₁)
      have f₂ := val_bcPt ρ (ptOfSection p₂ hp₂)
      rw [bcPt_ptOfSection] at e₁ e₂ f₁ f₂
      rw [f₁, f₂]
      refine hfib _ _ ((hcc p₁ hp₁).trans h₁) ((hcc p₂ hp₂).trans h₂) ?_
      rw [← e₁, ← e₂]; exact hv)
  refine ⟨F, G, hcop, fun y t hy ht => ?_⟩
  rw [← val_bcPt] at ht ⊢
  exact hR (bcPt y) (bcPt_snd y) hy t ht

/-- **Both curve facts from C1a, C2K, C3K** (the leaves in Hartshorne's setting). -/
theorem curveFacts_of_algClosed (h1 : SmoothCurveNoIsolatedPoint) (h2 : ConstOrOntoAlgClosed)
    (h3 : RatFactorAlgClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_named h1 (geomCompConstOrOnto_of h2) (geomCompRatFactor_of h3)

/-! ## §8 C1a from the dimension of local rings at closed points -/

/-- **(C1b) Local rings of a smooth curve at closed points have dimension 1.** If `X → Spec K`
is smooth of relative dimension 1 over a field `K` and `x` is a closed point, then
`dim 𝒪_{X,x} = 1` (STANDARD: smooth of relative dimension `n` over a field means `dim_x X = n`
at every point, and at a closed point of a scheme locally of finite type over a field
`dim 𝒪_{X,x} = dim_x X`; e.g. Stacks, *Morphisms*, smooth morphisms and dimension of fibres,
UNVERIFIED tags). Glue (dimension theory), not in Mathlib v4.35; Mathlib has
`ringKrullDim_stalk_eq_coheight` (Stacks 02IZ), used below. -/
def SmoothStalkDimOne : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    SmoothOfRelativeDimension 1 f → ∀ x : X, IsClosed ({x} : Set X) →
      ringKrullDim (X.presheaf.stalk x) = 1

/-- **C1a from C1b.** An open point is closed (Jacobson) and has no proper generalization, so its
local ring has dimension `coheight x = 0`. -/
theorem smoothCurveNoIsolatedPoint_of (h : SmoothStalkDimOne) : SmoothCurveNoIsolatedPoint := by
  intro K _ X f hf x hx
  have : Smooth f := hf.smooth
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hc : IsClosed ({x} : Set X) := isClosed_singleton_of_isLocallyClosed_singleton hx.isLocallyClosed
  have hd := h K X f hf x hc
  rw [ringKrullDim_stalk_eq_coheight] at hd
  have hmax : IsMax x := by
    intro y hxy
    have hyx : y ⤳ x := hxy
    have : y ∈ ({x} : Set X) := hyx.mem_open hx rfl
    rw [Set.mem_singleton_iff.mp this]
  rw [Order.coheight_eq_zero.mpr hmax] at hd
  exact absurd hd (by decide)

/-- **Both curve facts from C1b, C2K, C3K.** -/
theorem curveFacts_of_leaves (h1 : SmoothStalkDimOne) (h2 : ConstOrOntoAlgClosed)
    (h3 : RatFactorAlgClosed) : CurveRatFactor ∧ CurveSurj :=
  curveFacts_of_algClosed (smoothCurveNoIsolatedPoint_of h1) h2 h3

end Pin

end AV

end LeafQM

end


/-! ## g0-assemble2: fs5-nocm (scratch/fs5-nocm/partB, partD, partE, partG, partH, partI, verbatim except three
edits forced by pin-apply, which made Leaves.lean's `R1fpProps` the repaired six-clause list (=`R1fpPropsFull`,
same text): `R1fpPropsFull.old` is now `h` itself; in `fibreComTrivialFull_of_own` the conversions
`(r1fpPropsFull_iff _ _).1` to mobius-glue's `R1fpPropsU` are dropped, since Leaves.lean's
`pointwise_of_witness_mor` takes `R1fpProps`. The qm-pin copies of its FS5NoCM.lean are Leaves.lean's.) -/
noncomputable section

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin ZInQ ZInQ.JHeight PkgI3

/-! ## §B The statement -/

/-- **FS5 as stated by g0-fibresimple** (verbatim from `scratch/g0-fibresimple/FibreSimple.lean`,
`HSyn.G0Split.FibreComTrivial`, with the old `R1fpProps`; kept for reference: g0-fibresimple §2
shows that the old clause list does not pin `Φ`, so this form is not a consequence of the leaves).

**Glue piece FS5 = G6 (NoCM, rv-h-cm §7.2, on the actual fibre object).** For `u ∉ 𝒞` and an
object `P` of `Y₃` at a `ℚ̄`-point over `J(u)`, the centralizer `End_𝒪(P.A)` is `ℤ` (the point is
not a CM point). -/
def FibreComTrivial : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-- **`R1fpProps` after qm-pin's full edit** (text of `scratch/qm-pin/QM-Leaves-full.patch`,
lines 63-70: the four old clauses, `R1famProps` and `R1univProps`). After the integration this is
`LeafQM.AV.R1fpProps`. -/
def R1fpPropsFull (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ ∧ R1univProps Y Φ

theorem r1fpPropsFull_iff (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) :
    R1fpPropsFull Y Φ ↔ R1fpPropsU Y Φ :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨⟨a, b, c, d, e⟩, f⟩, fun ⟨⟨a, b, c, d, e⟩, f⟩ => ⟨a, b, c, d, e, f⟩⟩

theorem R1fpPropsFull.old {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpPropsFull Y Φ) : R1fpProps Y Φ := h

/-- **FS5 with the repaired QM clauses** (the statement this task proves): `FibreComTrivial`
verbatim, with `R1fpProps` read as after qm-pin's full edit (`R1fpPropsFull`). -/
def FibreComTrivialFull : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpPropsFull Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-- The clause list of the leaf bundle `LeafQM.AV.R1R2fp` on one witness, with `R1fpProps` as
after qm-pin's full edit. -/
def R1R2fpFullProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left) : Prop :=
  R1fpPropsFull Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧
    CMExists X Ψ ∧ R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

/-- **The leaf bundle `LeafQM.AV.R1R2fp` after qm-pin's full edit** (same text, `R1fpProps`
repaired). -/
def R1R2fpFull : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆

theorem R1R2fp_of_full (h : R1R2fpFull) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, h⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1.old, h⟩

/-- **FS5 for the leaf's own triple** (the restatement that qm-pin's `pointwise_of_witness_mor`
allows): for every witness `(Y, Φ, X, Ψ, fY, π₆)` of the repaired leaf bundle, the objects over
`J(u)`, `u ∉ 𝒞`, of the triple `(Y, Φ, π₆ ∘ fY)` have `End_𝒪 = ℤ`. Quantified over all witnesses
(not a `Classical.choice` of one), so it is a statement about the published data, not about a
choice. -/
def FibreComTrivialOwn : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      (π₆.comp fY.left).val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A)

/-! ## §C The named Props NoCM needs -/

/-- **NoCM input N1a (glue; G5-G6, rv-h-cm §7.2 "the CM order"): `End_𝒪(A)` is `ℤ` or an order in
an imaginary quadratic field.** For a QM pair `(A, ι)` over `ℚ̄`, either every element of the
centralizer `com ι = End_𝒪(A)` is an integer, or `com ι` is isomorphic to a subring `R` of the
ring of integers of an imaginary quadratic field `k`, of finite index (`conductor R ≠ 0`).
*Why true* (STANDARD): by Yu's dichotomy (leaf T27, `PkgI3.QMDichotomyYu`, in characteristic 0)
`End⁰(A) ≅ B` or `≅ M₂(k)` with `k` imaginary quadratic; the centralizer of `B` is `ℚ`, resp. the
centre `k` (FS4's argument, `centralizerOfMatrixEnd0_of_homFree`); `com ι = End(A) ∩ com⁰` is a
finitely generated (T6) subring of `ℚ`, resp. of `k`, of rank 1, resp. 2, and integral over `ℤ`,
hence `ℤ`, resp. an order of `k`. Glue; **proved** from T27 and T6 in §G-§H
(`comIntOrQuadOrder_of_leaves`). -/
def ComIntOrQuadOrder : Prop :=
  ∀ P : QMPair Qbar, (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A)) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k) (_ : NumberField.IsTotallyComplex k),
      Module.finrank ℚ k = 2 ∧ ∃ R : Subring k, R ≤ (integralClosure ℤ k).toSubring ∧
        conductor R ≠ 0 ∧ Nonempty (com P.q ≃+* R)

/-- **NoCM input N1b (leaf; "(Emb)" of rv-h-cm §7.2 and rv-nocm §1.2): the CM order has conductor
prime to 6.** If `End_𝒪(A) ≅ R` for an order `R` of an imaginary quadratic field `k`, then the
conductor of `R` is prime to `6 = disc B`.
*Published statement*: the CM points of `X₀(D, 1)` by `R` correspond to optimal embeddings
`R ↪ 𝒪` (Jordan, thesis (Harvard 1981) §3; González–Rotger, J. Math. Soc. Japan 58 (2006) §5;
locators UNVERIFIED), and an order of conductor `f` embeds optimally in the maximal order of the
quaternion division algebra over `ℚ_p` only if `p ∤ f` and `p` does not split in `k` (Vignéras,
*Arithmétique des algèbres de quaternions*, LNM 800, Ch. II §3 / Ch. III §5, theorem numbers
UNVERIFIED; for `p ∤ f`: `k ∩ 𝒪_p = 𝒪_{k,p}` because `𝒪_p` is the set of integral elements).
A consequence of the published statements (only the conductor half is kept). **Proved** in §I
from the leaf `CMOptimalEmbedding` (Shimura's description of CM points), `cmConductorCoprime6_of`. -/
def CMConductorCoprime6 : Prop :=
  ∀ (P : QMPair Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      conductor R ≠ 0 → Nonempty (com P.q ≃+* R) → Nat.Coprime (conductor R) 6

/-- **NoCM input N2 (glue; the Kummer model of `X₆ → X₆/W ≅ P¹`, rv-h-cm §2.3-2.4,
`GlueRepo.PR.fibre_iff`).** On the leaf bundle's `X₆`, for a rational value `j₀ ∉ {0, −16/27}`
of `π₆` (so `t₀ = 1 + 27 j₀/16 ∉ {0, 1, ∞}`):
(i) every `ℚ̄`-point `x` over `j₀` has residue field `ℚ(x) = ℚ(a, b)` for any `a, b ∈ ℚ̄` with
`a² = −t₀`, `b² = 3(t₀ − 1)`;
(ii) the fibre over `j₀` has (at least) four distinct `ℚ̄`-points.
*Why true* (argued; Elkies, "Shimura curve computations", ANTS-III, LNCS 1423 (1998), the curve
`X*(6)` and its double covers (section number UNVERIFIED); the constants `c₀ = −1`, `c₁ = 3` are
derived in rv-h-cm §2.3 and checked against González–Rotger Thm 5.12 on all 24 rows of Elkies'
table, rv-nocm §1.3 Part B (VERIFIED there)): `ℚ(X₆) = ℚ(t)(y₁, y₂)`, `y₁² = −t`,
`y₂² = 3(t − 1)`, with `W ≅ (ℤ/2)²` acting by the sign changes; the affine model is smooth over
`t ∉ {0, 1, ∞}`, so the points over `t₀` are `(t₀, ±a, ±b)` (four, as `ab ≠ 0`) with residue field
generated by their coordinates. On an arbitrary witness of the bundle the statement is the same
statement, transported: with the repaired `R1fpProps` the witness `Y` maps to the genuine `Y₃`
with `Φ = Φ₃ ∘ g`, `π = π₃ ∘ g` (qm-pin `phi_part`, mobius-glue), `fY` is onto `X(ℚ̄)` (`X6Surj`),
`Ψ(fY y) = [forget (Φ y)]` (`X6Props`), and a residue field is the fixed field of the Galois
stabilizer of the point, which `Ψ` matches with the stabilizer of the pair (Galois-equivariance in
`X6Props`). Glue: geometry of an explicit curve plus the identification (not compiled). -/
def X6KummerFibre : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ →
    ∀ j₀ : ℚ, j₀ ≠ 0 → j₀ ≠ -16 / 27 →
      (∀ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
        ∀ a b : Qbar, a ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) →
          b ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1) →
          residueImage (X := X.left) x.left = IntermediateField.adjoin ℚ {a, b}) ∧
      ∃ f : Fin 4 → (fieldPt Qbar ⟶ X), Function.Injective f ∧
        ∀ i, π₆.val (K := Qbar) (f i).left = OnePoint.some (algebraMap ℚ Qbar j₀)


/-! ## §D Arithmetic -/

/-- In a number field containing a square root `ι` of `−1`, the prime `2` is not inert:
`(1 + ι)² = 2ι ∈ (2)` but `(1 + ι)/2` is not integral (its fourth power is `−1/4`). -/
theorem two_not_prime_of_sqrt_neg_one {k : Type} [Field k] [NumberField k] (ι : k)
    (hι : ι ^ 2 = -1) : ¬ (Ideal.span {(2 : NumberField.RingOfIntegers k)}).IsPrime := by
  intro hP
  have hint : IsIntegral ℤ ι := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow 2).add_of_left
        (by rw [Polynomial.degree_one, Polynomial.degree_X_pow]; norm_num)
    · simp [hι]
  let ιO : NumberField.RingOfIntegers k := ⟨ι, hint⟩
  have hsq : (1 + ιO) ^ 2 = 2 * ιO := by
    apply NumberField.RingOfIntegers.ext
    simp only [map_pow, map_add, map_one, map_mul, map_ofNat]
    change (1 + ι) ^ 2 = 2 * ι
    linear_combination hι
  have hmem : (1 + ιO) ^ 2 ∈ Ideal.span {(2 : NumberField.RingOfIntegers k)} := by
    rw [hsq]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hP.mem_of_pow_mem 2 hmem)
  have hck : (c : k) * 2 = 1 + ι := congrArg (fun z : NumberField.RingOfIntegers k => (z : k)) hc
  have h4 : (c : k) ^ 4 = algebraMap ℚ k (-1 / 4) := by
    have : (c : k) ^ 4 = -1 / 4 := by
      linear_combination (1 / 16 : k) * ((c * 2) ^ 3 + (c * 2) ^ 2 * (1 + ι) +
        (c * 2) * (1 + ι) ^ 2 + (1 + ι) ^ 3) * hck + (1 / 16 : k) * (ι ^ 2 + 4 * ι + 5) * hι
    rw [this]; simp
  have hI : IsIntegral ℤ (algebraMap ℚ k (-1 / 4)) := by
    rw [← h4]; exact (NumberField.RingOfIntegers.isIntegral_coe c).pow 4
  have hI' : IsIntegral ℤ (-1 / 4 : ℚ) :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ k).restrictScalars ℤ)
      (algebraMap ℚ k).injective).mp hI
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI'
  have : (n : ℚ) * 4 = -1 := by
    rw [show (n : ℚ) = algebraMap ℤ ℚ n from rfl, hn]; norm_num
  have : n * 4 = -1 := by exact_mod_cast this
  omega

/-- `[ℚ(i) : ℚ] = 2` inside `ℚ̄`. -/
theorem finrank_adjoin_sqrt_neg_one (i : Qbar) (hi : i ^ 2 = -1) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) = 2 := by
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1 : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])
  have hmp : minpoly ℚ i = Polynomial.X ^ 2 - Polynomial.C (-1 : ℚ) := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ ?_).symm
    · simp [hi]
    · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
  have hint : IsIntegral ℚ i := Algebra.IsIntegral.isIntegral i
  rw [IntermediateField.adjoin.finrank hint, hmp, Polynomial.natDegree_X_pow_sub_C]

/-- `ℚ(i h₁, i h₂) = ℚ(i)` for rational `h₁ ≠ 0`, `h₂`. -/
theorem adjoin_pair_eq (i : Qbar) (h₁ h₂ : ℚ) (hh : h₁ ≠ 0) :
    IntermediateField.adjoin ℚ {i * algebraMap ℚ Qbar h₁, i * algebraMap ℚ Qbar h₂} =
      IntermediateField.adjoin ℚ {i} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with rfl | rfl <;>
      exact mul_mem (IntermediateField.mem_adjoin_simple_self ℚ i)
        (IntermediateField.algebraMap_mem _ _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h0 : algebraMap ℚ Qbar h₁ ≠ 0 := by simpa using hh
    have hm : i * algebraMap ℚ Qbar h₁ ∈ IntermediateField.adjoin ℚ
        {i * algebraMap ℚ Qbar h₁, i * algebraMap ℚ Qbar h₂} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    have := mul_mem hm (IntermediateField.algebraMap_mem _ (h₁⁻¹))
    rwa [map_inv₀, mul_assoc, mul_inv_cancel₀ h0, mul_one] at this

/-- The Elkies identities at `t(u)` (`GlueRepo.PR.t_eq`, `t_sub_one`), in `ℚ̄`: with `i² = −1`,
`(i H/G³)² = −t(u)` and `(i·540F/G³)² = 3(t(u) − 1)`, `t(u) = 1 + 27 J(u)/16`. -/
theorem elkies_sq (u : ℚ) (i : Qbar) (hi : i ^ 2 = -1) :
    (i * algebraMap ℚ Qbar (GlueRepo.PR.Hq u / GlueRepo.PR.Gq u ^ 3)) ^ 2 =
        -algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) ∧
      (i * algebraMap ℚ Qbar (540 * GlueRepo.PR.Fq u / GlueRepo.PR.Gq u ^ 3)) ^ 2 =
        3 * (algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) - 1) := by
  have ht : (1 + 27 * Jmap u / 16 : ℚ) = (GlueRepo.PR.Hq u / GlueRepo.PR.Gq u ^ 3) ^ 2 := by
    rw [div_pow, ← pow_mul]; exact GlueRepo.PR.t_eq u
  have ht1 : (1 + 27 * Jmap u / 16 : ℚ) - 1 =
      -3 * (180 * GlueRepo.PR.Fq u / GlueRepo.PR.Gq u ^ 3) ^ 2 := GlueRepo.PR.t_sub_one u
  constructor
  · rw [ht, mul_pow, hi, map_pow]; ring
  · have e : algebraMap ℚ Qbar (1 + 27 * Jmap u / 16) - 1 =
        algebraMap ℚ Qbar ((1 + 27 * Jmap u / 16 : ℚ) - 1) := by rw [map_sub, map_one]
    rw [e, ht1, mul_pow, hi]
    simp only [map_mul, map_pow, map_neg, map_div₀, map_ofNat]
    ring


/-! ## §E NoCM on the leaf's own witness, and FS5 -/

/-- **NoCM on the leaf bundle's witness** (rv-h-cm §7.2 with the corrected count of rv-nocm §1.1).
Let `y` be a `ℚ̄`-point of the witness `Y` over `J(u)`, `u ∉ 𝒞`, with object `P`, and
`x = fY(y) ∈ X₆`. If `End_𝒪(P.A) ≅ R` were an order of an imaginary quadratic `k` (N1a), its
conductor is prime to 6 (N1b). The residue field of `x` is `ℚ(i)` (N2 (i) with the Elkies
identities), so R5 (`R5ptProps`) gives `2 = h(R)` if `b(k) = 0`, and `2 = 2h(R)` with
`k ↪ ℚ(i)` if `b(k) ≥ 1`; in the second case `k ≅ ℚ(i)`, where `2` ramifies, so `b(k) = 1`.
Either way `#CM(R) = 2^{b(k)} h(R) = 2` (R5fpCount). But the four points of the fibre over
`J(u)` (N2 (ii)) are pairwise distinct points of `X₆`, hence (`Ψ` bijective) four distinct
classes, and each is an `Aut(𝒪)`-twist of `P` (`R2X6Props`), hence CM by `R` (`com_twist`,
`comEquiv`): `#CM(R) ≥ 4`. Contradiction; so `End_𝒪(P.A) = ℤ`. -/
theorem nocm_on_witness (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (hW : R1R2fpFullProps Y Φ X Ψ fY π₆)
    (u : ℚ) (hu : u ∉ contactSet) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar)
    (hP : Φ Qbar y = M3.mk P)
    (hv : (π₆.comp fY.left).val (K := Qbar) y.left =
      OnePoint.some (algebraMap ℚ Qbar (Jmap u))) :
    ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A) := by
  obtain ⟨h1, hh, hX, h2, hE, hrec, hS, h5⟩ := hW
  have hx : Ψ (y ≫ fY) = Quotient.mk _ P.forget := hX.2.2.2.2.2 y P hP
  have hv' : π₆.val (K := Qbar) (y ≫ fY).left =
      OnePoint.some (algebraMap ℚ Qbar (Jmap u)) := by
    exact (ToP1.val_comp_right π₆ fY.left y.left).symm.trans hv
  rcases hA P.forget with hZ | ⟨k, _, _, _, hk2, R, hR, hc0, ⟨e⟩⟩
  · exact hZ
  exfalso
  have hcop : Nat.Coprime (conductor R) 6 := hB P.forget k hk2 R hR hc0 ⟨e⟩
  obtain ⟨hdeg, hemb⟩ := h5 k hk2 R hR hcop (y ≫ fY) P.forget hx ⟨e⟩
  -- the fibre over `J(u)` (N2) and its residue field `ℚ(i)`
  obtain ⟨hres, f, hf, hfv⟩ := hK Y Φ X Ψ fY π₆ ⟨h1, hh, hX, h2, hE, hrec, hS, h5⟩ (Jmap u)
    (GlueRepo.PR.J_ne_zero hu) (GlueRepo.PR.J_ne_branch u)
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) two_pos
  obtain ⟨ha, hb⟩ := elkies_sq u i hi
  have hresEq : residueImage (X := X.left) (y ≫ fY).left = IntermediateField.adjoin ℚ {i} := by
    rw [hres _ hv' _ _ ha hb]
    exact adjoin_pair_eq i _ _ (GlueRepo.PR.h₁_ne_zero u)
  have hfin : Module.finrank ℚ (residueImage (X := X.left) (y ≫ fY).left) = 2 := by
    rw [hresEq]; exact finrank_adjoin_sqrt_neg_one i hi
  rw [hfin] at hdeg
  -- four distinct classes with CM by `R`
  have hcount := hC k hk2 R hR hcop ⟨P.forget, ⟨e⟩⟩
  have hmemS : ∀ j : Fin 4, ∃ P' : QMPair Qbar, Quotient.mk _ P' = Ψ (f j) ∧
      Nonempty (com P'.q ≃+* R) := by
    intro j
    refine ⟨Quotient.out (Ψ (f j)), Quotient.out_eq _, ?_⟩
    have hQ : Ψ (f j) = Quotient.mk _ (Quotient.out (Ψ (f j))) := (Quotient.out_eq _).symm
    obtain ⟨α, ⟨g⟩⟩ := ((h2 (y ≫ fY) (f j) P.forget _ hx hQ).1).1 (hv'.trans (hfv j).symm)
    exact ⟨((comEquiv g).symm.trans (RingEquiv.subringCongr (com_twist P.forget.q α))).trans e⟩
  let F : Fin 4 → {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} :=
    fun j => ⟨Ψ (f j), hmemS j⟩
  have hFinj : Function.Injective F := fun a b hab =>
    hf (Ψ.injective (congrArg Subtype.val hab))
  -- `#CM(R) = 2`
  have hcard2 : Nat.card {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} = 2 := by
    rw [hcount]
    by_cases hb0 : inertCount6 k = 0
    · simp only [hb0, ↓reduceIte] at hdeg
      rw [hb0]; omega
    · simp only [hb0, ↓reduceIte] at hdeg
      have hh1 : Nat.card (CommRing.Pic R) = 1 := by omega
      obtain ⟨e'⟩ := hemb hb0
      have hik : i ∈ residueImage (X := X.left) (y ≫ fY).left := by
        rw [hresEq]; exact IntermediateField.mem_adjoin_simple_self ℚ i
      have : FiniteDimensional ℚ (residueImage (X := X.left) (y ≫ fY).left) :=
        Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
      have hsurj : Function.Surjective e'.toLinearMap := by
        rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hk2, hfin])]
        exact e'.toRingHom.injective
      obtain ⟨ι, hι⟩ := hsurj ⟨i, hik⟩
      have hι2 : ι ^ 2 = -1 := by
        apply e'.toRingHom.injective
        change e' (ι ^ 2) = e' (-1)
        rw [map_pow, map_neg, map_one]
        have : e' ι = ⟨i, hik⟩ := hι
        rw [this]
        apply Subtype.ext
        simp [hi]
      have h2n := two_not_prime_of_sqrt_neg_one ι hι2
      have hb1 : inertCount6 k = 1 := by
        have : inertCount6 k ≤ 1 := by
          unfold inertCount6
          simp only [h2n, ↓reduceIte]
          split_ifs <;> omega
        omega
      rw [hb1, hh1]; norm_num
  have hfinS : Finite {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} :=
    Nat.finite_of_card_ne_zero (by rw [hcard2]; norm_num)
  have := Nat.card_le_card_of_injective F hFinj
  rw [hcard2, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- **FS5 for the leaf's own triple, from NoCM's inputs.** -/
theorem fibreComTrivialOwn_of (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialOwn :=
  fun _ _ _ _ _ _ hW u hu y P hP hv => nocm_on_witness hA hB hK hC hW u hu y P hP hv

/-- **From the leaf's own triple to every triple** (qm-pin's `pointwise_of_witness_mor`, with
`MobiusGlue` and the CM objects of the bundle, `cm_objects_of_R1R2fp`). -/
theorem fibreComTrivialFull_of_own (hL : R1R2fpFull) (hM : MobiusGlue)
    (hO : FibreComTrivialOwn) : FibreComTrivialFull := by
  obtain ⟨Y₀, Φ₀, X, Ψ, fY, π₆, hW⟩ := hL
  have hCM := cm_objects_of_R1R2fp (R1R2fp_of_full ⟨Y₀, Φ₀, X, Ψ, fY, π₆, hW⟩)
  have h1 : R1fpProps Y₀ Φ₀ := hW.1
  have h2 : R2fpProps Y₀ Φ₀ (π₆.comp fY.left) := R2fpProps_of_X6 hW.2.2.1 hW.2.2.2.1
  have key := pointwise_of_witness_mor hM hCM h1 h2
    (fun t P => ∀ u : ℚ, u ∉ contactSet → t = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A))
    (fun t y P hP ht u hu htu => hO Y₀ Φ₀ X Ψ fY π₆ hW u hu y P hP (ht.trans htu))
  intro Y Φ π h1' h2' u hu y P hP hv
  exact key Y Φ π h1' h2' _ y P hP hv u hu rfl

/-- **FS5 with the repaired QM clauses, proved** from the leaf bundle (after qm-pin's full edit),
`MobiusGlue` (proved by mobius-glue from `CurveRatFactor`, `CurveSurj` and T5), N1a, N1b, N2 and
the leaf R5fpCount. -/
theorem fibreComTrivialFull_of (hL : R1R2fpFull) (hM : MobiusGlue) (hA : ComIntOrQuadOrder)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) :
    FibreComTrivialFull :=
  fibreComTrivialFull_of_own hL hM (fibreComTrivialOwn_of hA hB hK hC)

end FS5NoCM


/-! ## §G N1a split: the case `End⁰(A) ≅ B` proved from T6; the CM case named

The block from `B6_isUnit` to `qm_embeds_end0` is copied verbatim from
`scratch/g0-fibresimple/olean/Tail.lean` (lines 40-116, proved there). -/

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3
open scoped Quaternion TensorProduct

/-- `B = (2, -3)_ℚ` is a division algebra: every nonzero element is a unit (the norm form
`a² - 2b² + 3c² - 6d²` is anisotropic, `GlueDescent.aniso_rat`). -/
theorem B6_isUnit (x : ℍ[ℚ, 2, -3]) (hx : x ≠ 0) : IsUnit x := by
  set n := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 with hn_def
  have hn : n ≠ 0 := fun h0 => by
    obtain ⟨h1, h2, h3, h4⟩ := GlueDescent.aniso_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext h1 h2 h3 h4)
  have hs : star x * x = algebraMap ℚ ℍ[ℚ, 2, -3] n := GlueDescent.B6_star_mul x
  have hs' : x * star x = algebraMap ℚ ℍ[ℚ, 2, -3] n := by
    rw [QuaternionAlgebra.mul_star_eq_coe]
    congr 1
    simp [QuaternionAlgebra.re_mul]
    ring
  refine ⟨⟨x, n⁻¹ • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, hs', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  · rw [smul_mul_assoc, hs, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]

/-- Division transported along an algebra isomorphism. -/
theorem division_of_algEquiv {D E : Type*} [Ring D] [Ring E] [Algebra ℚ D] [Algebra ℚ E]
    (e : D ≃ₐ[ℚ] E) (hE : ∀ x : E, x ≠ 0 → IsUnit x) : ∀ x : D, x ≠ 0 → IsUnit x := by
  intro x hx
  have h1 : e x ≠ 0 := by
    intro h; apply hx; rw [← e.symm_apply_apply x, h, map_zero]
  have := (hE (e x) h1).map e.symm
  rwa [e.symm_apply_apply] at this

/-! ## §2 Proved glue: a QM structure gives `B →ₐ[ℚ] End⁰(A)` -/

/-- `i ∈ 𝒪`. -/
def oi : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `j = 2·(1+j)/2 - 1 ∈ 𝒪`. -/
def oj : LeafQM.O := ⟨LeafQM.ofInt ![-1, 0, 2, 0], ⟨_, rfl⟩⟩

theorem coe_two_O : ((2 : LeafQM.O) : LeafQM.B) = 2 := map_ofNat LeafQM.O.subtype 2
theorem coe_three_O : ((3 : LeafQM.O) : LeafQM.B) = 3 := map_ofNat LeafQM.O.subtype 3

theorem oi_mul_oi : oi * oi = 2 := by
  apply Subtype.ext
  rw [coe_two_O, Subring.coe_mul]
  ext <;> simp [oi, LeafQM.ofInt] <;> rfl

theorem oj_mul_oj : oj * oj = -3 := by
  apply Subtype.ext
  rw [Subring.coe_neg, coe_three_O, Subring.coe_mul]
  ext <;> simp [oj, LeafQM.ofInt] <;> rfl

theorem oj_mul_oi : oj * oi = -(oi * oj) := by
  apply Subtype.ext
  rw [Subring.coe_neg, Subring.coe_mul, Subring.coe_mul]
  ext <;> simp [oi, oj, LeafQM.ofInt]

/-- **Glue (proved): the QM structure gives `B ↪ End⁰(A)`.** For a QM structure
`ι : 𝒪 → End_k(A)` (`LeafQM.AV.QMStr`), the elements `1 ⊗ ι(i)`, `1 ⊗ ι(j)` of
`End⁰(A) = ℚ ⊗ End(A)` satisfy `i² = 2`, `j² = -3`, `ji = -ij`, so `B = ℍ[ℚ,2,-3]` maps to
`End⁰(A)` (`QuaternionAlgebra.Basis.liftHom`). This is Yu's hypothesis "`B` embeds in `End⁰(A)`"
(injectivity is automatic: `B` is simple and `End⁰(A) ≠ 0` when a QM structure exists). -/
def qmBasis {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    QuaternionAlgebra.Basis (PkgI3.AbVar.End0 A) (2 : ℚ) 0 (-3) :=
  let g : LeafQM.O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A).toRingHom.comp
      q.iota
  { i := g oi
    j := g oj
    k := g oi * g oj
    i_mul_i := by
      rw [← map_mul, oi_mul_oi, map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
        map_ofNat]
    j_mul_j := by
      rw [← map_mul, oj_mul_oj, map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
        map_ofNat]
    i_mul_j := rfl
    j_mul_i := by
      rw [← map_mul, oj_mul_oi, map_neg, map_mul, zero_smul, zero_sub] }

theorem qm_embeds_end0 {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) :=
  ⟨(qmBasis q).liftHom⟩

/-- The centre of `B = ℍ[ℚ, 2, -3]` is `ℚ`. -/
theorem B6_central_eq (z : ℍ[ℚ, 2, -3]) (hz : ∀ y : ℍ[ℚ, 2, -3], z * y = y * z) :
    z = algebraMap ℚ _ z.re := by
  have hi := hz ⟨0, 1, 0, 0⟩
  have hj := hz ⟨0, 0, 1, 0⟩
  have hi2 := congrArg QuaternionAlgebra.imJ hi
  have hi3 := congrArg QuaternionAlgebra.imK hi
  have hj1 := congrArg QuaternionAlgebra.imI hj
  have hj3 := congrArg QuaternionAlgebra.imK hj
  simp at hi2 hi3 hj1 hj3
  ext <;> simp <;> linarith

/-- `m ↦ 1 ⊗ m`, `End(A) → End⁰(A)`, is injective when `End(A)` is a free `ℤ`-module (T6). -/
theorem tmul_one_injective {k : Type} [Field k] {A : PkgI3.AbVar k}
    (hfree : Module.Free ℤ (PkgI3.AbVar.End A)) (m : PkgI3.AbVar.End A)
    (hm : (1 : ℚ) ⊗ₜ[ℤ] m = 0) : m = 0 := by
  let f := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) f).mp hm
  rw [Submonoid.smul_def] at hs'
  exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')

/-- **N1a, case `End⁰(A) ≅ B` (proved from T6).** If `End⁰(A) ≅ ℍ[ℚ, 2, -3]` for an abelian
variety with a QM structure `q`, then every element of `com q = End_𝒪(A)` is an integer: `1 ⊗ φ`
commutes with the image of `B`, which is all of `End⁰(A)` (an injective map of 4-dimensional
`ℚ`-spaces), so it is a rational scalar `c` (`B6_central_eq`); `φ` is integral over `ℤ` (`End(A)`
is a finitely generated `ℤ`-module, T6), hence so is `c`, so `c ∈ ℤ`; and `m ↦ 1 ⊗ m` is
injective (T6). -/
theorem com_int_of_end0_quat (hHF : PkgI3.HomFreeFinite) {k : Type} [Field k]
    {A : PkgI3.AbVar k} (q : QMStr A) (e : PkgI3.AbVar.End0 A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) :
    ∀ φ ∈ com q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End A) := by
  intro φ hφ
  obtain ⟨hfree, hfin, -, -⟩ := hHF k A A
  let L : ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A := (qmBasis q).liftHom
  have : Nontrivial (PkgI3.AbVar.End0 A) := e.toRingEquiv.nontrivial
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    have := (B6_isUnit b hb0).map L
    rw [hb] at this
    exact not_isUnit_zero this
  have : FiniteDimensional ℚ (PkgI3.AbVar.End0 A) :=
    LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have hLsurj : Function.Surjective L.toLinearMap := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [QuaternionAlgebra.finrank_eq_four, e.toLinearEquiv.finrank_eq,
        QuaternionAlgebra.finrank_eq_four])]
    exact hLinj
  set x : PkgI3.AbVar.End0 A := (1 : ℚ) ⊗ₜ[ℤ] φ with hx
  have e1 : ∀ a b : PkgI3.AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (a * b) = ((1 : ℚ) ⊗ₜ[ℤ] a) * ((1 : ℚ) ⊗ₜ[ℤ] b) := by
    intro a b; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hcomm_g : ∀ a : LeafQM.O, Commute x ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) := by
    intro a
    rw [com, Subring.mem_centralizer_iff] at hφ
    have h := hφ (q.iota a) ⟨a, rfl⟩
    show x * _ = _ * x
    rw [hx, ← e1, ← e1, h]
  have hcomm : ∀ y : PkgI3.AbVar.End0 A, x * y = y * x := by
    intro y
    obtain ⟨b, rfl⟩ := hLsurj y
    change Commute x ((qmBasis q).lift b)
    simp only [QuaternionAlgebra.Basis.lift]
    have h0 : Commute x (algebraMap ℚ (PkgI3.AbVar.End0 A) b.re) := (Algebra.commutes _ _).symm
    exact ((h0.add_right ((hcomm_g oi).smul_right _)).add_right
      ((hcomm_g oj).smul_right _)).add_right (((hcomm_g oi).mul_right (hcomm_g oj)).smul_right _)
  -- `x` is a rational scalar
  have hex : e x = algebraMap ℚ _ (e x).re := by
    apply B6_central_eq
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hcomm]
  set c : ℚ := (e x).re
  have hxc : x = algebraMap ℚ _ c := by
    apply e.injective; rw [hex, AlgEquiv.commutes]
  -- `c` is an integer
  have hint : IsIntegral ℤ φ := Algebra.IsIntegral.isIntegral φ
  obtain ⟨p, hpm, hp⟩ := hint
  have hpc : Polynomial.aeval c p = 0 := by
    have h1 : Polynomial.aeval x p = 0 := by
      have := Polynomial.aeval_algHom_apply
        (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A)
        φ p
      rw [← Polynomial.aeval_def] at hp
      rw [hp, map_zero] at this
      exact this
    rw [hxc, Polynomial.aeval_algebraMap_apply] at h1
    exact (algebraMap ℚ (PkgI3.AbVar.End0 A)).injective (h1.trans (map_zero _).symm)
  have hcint : IsIntegral ℤ c := ⟨p, hpm, by rw [← Polynomial.aeval_def]; exact hpc⟩
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hcint
  refine ⟨n, sub_eq_zero.mp (tmul_one_injective hfree _ ?_)⟩
  have h1 : (1 : ℚ) ⊗ₜ[ℤ] (n : PkgI3.AbVar.End A) = (n : PkgI3.AbVar.End0 A) :=
    map_intCast (Algebra.TensorProduct.includeRight :
      PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) n
  have h2 : algebraMap ℚ (PkgI3.AbVar.End0 A) c = (n : PkgI3.AbVar.End0 A) := by
    rw [← hn, show algebraMap ℤ ℚ n = (n : ℚ) from rfl, map_intCast]
  rw [TensorProduct.tmul_sub, ← hx, hxc, h1, h2, sub_self]


/-- **N1a-CM (glue; G6, the CM case of Yu's dichotomy): the CM order.** If
`End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, for a QM abelian surface `(A, ι)` over `ℚ̄`, then
`com ι = End_𝒪(A)` is isomorphic to a subring of finite index of `𝒪_k`, `k` imaginary quadratic.
*Why true* (STANDARD linear algebra; Shimura): `B ⊗ ℚ(√d) ≅ M₂(ℚ(√d))` (`B ⊗ k` is central simple
of `k`-dimension 4 and maps to `M₂(k)`), so the centralizer of `B` in `End⁰(A)` is the centre
`k = ℚ(√d)`; `com ι = End(A) ∩ k` is a finitely generated `ℤ`-module (T6) of integral elements
(`End(A)` is finite over `ℤ`), containing `ℤ` and a non-integer `n√d` (FS4,
`centralizerOfMatrixEnd0_of_homFree`), hence a subring of finite index of `𝒪_k`. Glue;
**proved** from T6 in §H (`comOfMatrixEnd0_of_homFree`). -/
def ComOfMatrixEnd0 : Prop :=
  ∀ (A : AbVar Qbar) (q : QMStr A) (d : ℚ), d < 0 →
    Nonempty (AbVar.End0 A ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    ∃ (k : Type) (_ : Field k) (_ : NumberField k) (_ : NumberField.IsTotallyComplex k),
      Module.finrank ℚ k = 2 ∧ ∃ R : Subring k, R ≤ (integralClosure ℤ k).toSubring ∧
        conductor R ≠ 0 ∧ Nonempty (com q ≃+* R)

/-- **N1a from T27 (Yu), T6 and N1a-CM.** -/
theorem comIntOrQuadOrder_of (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite)
    (hCM : ComOfMatrixEnd0) : ComIntOrQuadOrder := by
  intro P
  rcases PkgI3.qmDichotomy_B6 t27 Qbar P.A P.surface B6_isUnit (qm_embeds_end0 P.q) with
    he | ⟨d, hd, hM⟩
  · obtain ⟨e⟩ := he
    exact Or.inl (com_int_of_end0_quat t6 P.q e)
  · exact Or.inr (hCM P.A P.q d hd hM)

/-- **FS5 with the repaired clauses, from the leaves and named glue**: the bundle, R5fpCount,
T27, T6 (in `TextbookLeaves`), N1b, and the glue `MobiusGlue`, N1a-CM, N2. -/
theorem fibreComTrivialFull_of_leaves (hL : R1R2fpFull) (hM : MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hCM : ComOfMatrixEnd0)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of hL hM (comIntOrQuadOrder_of t27 t6 hCM) hB hK hC

end FS5NoCM


/-! ## §H N1a-CM proved from T6 (`End_𝒪(A)` is an order of `ℚ(√d)` when `End⁰(A) ≅ M₂(ℚ(√d))`) -/

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3
open scoped Quaternion TensorProduct

section LinAlg

variable {K : Type} [Field K]

local notation "M2" => Matrix (Fin 2) (Fin 2) K

theorem quat_comm_I (I J : M2) (hI : I * I = (2 : K) • 1) (hJI : J * I = -(I * J))
    (a b c d : K) :
    I * (a • 1 + b • I + c • J + d • (I * J)) - (a • 1 + b • I + c • J + d • (I * J)) * I =
      (2 * c) • (I * J) + (4 * d) • J := by
  have r1 : I * (I * J) = (2 : K) • J := by rw [← mul_assoc, hI, smul_mul_assoc, one_mul]
  have r2 : (I * J) * I = -((2 : K) • J) := by
    rw [mul_assoc, hJI, mul_neg, ← mul_assoc, hI, smul_mul_assoc, one_mul]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hI, r1, r2, hJI]
  module

theorem quat_comm_J (I J : M2) (hI : I * I = (2 : K) • 1) (hJ : J * J = (-3 : K) • 1)
    (hJI : J * I = -(I * J)) (a b c d : K) :
    J * (a • 1 + b • I + c • J + d • (I * J)) - (a • 1 + b • I + c • J + d • (I * J)) * J =
      (-2 * b) • (I * J) + (6 * d) • I := by
  have r3 : (I * J) * J = (-3 : K) • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]
  have r4 : J * (I * J) = (3 : K) • I := by
    rw [← mul_assoc, hJI, neg_mul, mul_assoc, hJ, mul_smul_comm, mul_one, neg_smul]; module
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hJ, r3, r4, hJI]
  module

/-- **A matrix commuting with `I` and `J` is scalar**, if `I² = 2`, `J² = −3`, `JI = −IJ` in
`M₂(K)`, `2, 3 ≠ 0` in `K` (then `1, I, J, IJ` is a `K`-basis of `M₂(K)`). -/
theorem commute_quat_scalar (I J : M2) (hI : I * I = (2 : K) • 1) (hJ : J * J = (-3 : K) • 1)
    (hJI : J * I = -(I * J)) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (Y : M2) (hYI : I * Y = Y * I) (hYJ : J * Y = Y * J) : ∃ a : K, Y = a • (1 : M2) := by
  have r3 : (I * J) * J = (-3 : K) • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]
  have hinj : Function.Injective (fun x : K => x • (1 : M2)) := smul_left_injective K one_ne_zero
  have hIns : ∀ s : K, I ≠ s • (1 : M2) := by
    intro s hs
    have hc : I * J = J * I := by rw [hs, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hJI] at hc
    have h0 : I * J = 0 := by
      have : (2 : K) • (I * J) = 0 := by
        rw [two_smul]; nth_rewrite 2 [hc]; exact add_neg_cancel _
      exact (smul_eq_zero.mp this).resolve_left h2
    have hI0 : I = 0 := by
      have := r3; rw [h0, zero_mul] at this
      exact (smul_eq_zero.mp this.symm).resolve_left (neg_ne_zero.mpr h3)
    apply h2; apply hinj; simp only; rw [← hI, hI0, mul_zero, zero_smul]
  -- `(2c)•IJ + (4d)•J = 0 → c = 0 ∧ d = 0`
  have kill : ∀ c d : K, (2 * c) • (I * J) + (4 * d) • J = 0 → c = 0 ∧ d = 0 := by
    intro c d h
    have h' := congrArg (· * J) h
    simp only [add_mul, smul_mul_assoc, r3, hJ, zero_mul] at h'
    have hc : c = 0 := by
      by_contra hc
      have h6 : (-6 * c : K) ≠ 0 := mul_ne_zero (by
        rw [show (-6 : K) = -(2 * 3) by norm_num]; exact neg_ne_zero.mpr (mul_ne_zero h2 h3)) hc
      apply hIns ((-6 * c)⁻¹ * (12 * d))
      have : (-6 * c) • I = (12 * d) • (1 : M2) := by
        have e : (-6 * c) • I - (12 * d) • (1 : M2) =
            (2 * c) • (-3 : K) • I + (4 * d) • (-3 : K) • (1 : M2) := by module
        rw [h'] at e; exact sub_eq_zero.mp e
      rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ h6, one_smul]
    subst hc
    refine ⟨rfl, ?_⟩
    have : (-12 * d) • (1 : M2) = 0 := by
      have e : (-12 * d) • (1 : M2) = ((2 : K) * 0) • (-3 : K) • I + (4 * d) • (-3 : K) • (1 : M2) := by
        module
      rw [e]; exact h'
    have h12 : (-12 * d : K) = 0 := hinj (by simpa using this)
    have : (12 : K) ≠ 0 := by
      have : (12 : K) = 2 * 2 * 3 := by norm_num
      rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h3
    have := mul_eq_zero.mp (show (-12 : K) * d = 0 from h12)
    rcases this with h | h
    · exact absurd (neg_eq_zero.mp h) ‹(12 : K) ≠ 0›
    · exact h
  let v : Fin 4 → M2 := ![1, I, J, I * J]
  have hsum : ∀ g : Fin 4 → K, ∑ i, g i • v i = g 0 • 1 + g 1 • I + g 2 • J + g 3 • (I * J) := by
    intro g; simp [Fin.sum_univ_four, v]
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [hsum] at hg
    have hI0 := quat_comm_I I J hI hJI (g 0) (g 1) (g 2) (g 3)
    rw [hg, mul_zero, zero_mul, sub_zero] at hI0
    obtain ⟨hg2, hg3⟩ := kill _ _ hI0.symm
    rw [hg2, hg3, zero_smul, zero_smul, add_zero, add_zero] at hg
    have hg1 : g 1 = 0 := by
      by_contra hg1
      apply hIns (-(g 1)⁻¹ * g 0)
      have hb : g 1 • I = -(g 0 • (1 : M2)) := eq_neg_of_add_eq_zero_right hg
      calc I = (g 1)⁻¹ • (g 1 • I) := by rw [smul_smul, inv_mul_cancel₀ hg1, one_smul]
        _ = (-(g 1)⁻¹ * g 0) • 1 := by rw [hb]; module
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := hinj (by simpa using hg)
    intro i; fin_cases i <;> assumption
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])
  have hY : Y ∈ Submodule.span K (Set.range v) := hspan ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hY
  rw [hsum] at hg
  subst hg
  have hI0 := quat_comm_I I J hI hJI (g 0) (g 1) (g 2) (g 3)
  rw [hYI, sub_self] at hI0
  obtain ⟨hg2, hg3⟩ := kill _ _ hI0.symm
  have hJ0 := quat_comm_J I J hI hJ hJI (g 0) (g 1) (g 2) (g 3)
  rw [hYJ, sub_self, hg3, mul_zero, zero_smul, add_zero] at hJ0
  have hg1 : g 1 = 0 := by
    have h' := congrArg (· * J) hJ0
    simp only [smul_mul_assoc, r3, zero_mul, smul_smul] at h'
    by_contra hg1
    apply hIns 0
    have hne : (-2 * g 1 * -3 : K) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hg1) (neg_ne_zero.mpr h3)
    rw [zero_smul]
    exact (smul_eq_zero.mp h'.symm).resolve_left hne
  refine ⟨g 0, ?_⟩
  rw [hg1, hg2, hg3]; simp

section AdjRoot

open Polynomial

variable (d : ℚ)

/-- `X² − d` is irreducible over `ℚ` for `d < 0`. -/
theorem irred_sq_sub (hd : d < 0) : Irreducible (X ^ 2 - C d : ℚ[X]) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])

theorem monic_sq_sub : (X ^ 2 - C d : ℚ[X]).Monic := monic_X_pow_sub_C _ two_ne_zero

theorem finrank_adjRoot : Module.finrank ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) = 2 := by
  rw [(AdjoinRoot.powerBasis' (monic_sq_sub d)).finrank]
  exact natDegree_X_pow_sub_C

theorem finite_adjRoot : Module.Finite ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) :=
  (AdjoinRoot.powerBasis' (monic_sq_sub d)).finite

theorem root_sq : (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])) ^ 2 =
    algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) d := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C d : ℚ[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.mp h

/-- For `d < 0`, `ℚ(√d)` (as `AdjoinRoot`, with its field structure) is a totally complex
quadratic number field. -/
theorem adjRoot_numberField (hd : d < 0) :
    letI : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) := ⟨irred_sq_sub d hd⟩
    NumberField (AdjoinRoot (X ^ 2 - C d : ℚ[X])) ∧
      NumberField.IsTotallyComplex (AdjoinRoot (X ^ 2 - C d : ℚ[X])) := by
  let : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) := ⟨irred_sq_sub d hd⟩
  have : CharZero (AdjoinRoot (X ^ 2 - C d : ℚ[X])) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X]))).injective
  have := finite_adjRoot d
  refine ⟨{}, ⟨fun v => ?_⟩⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  rintro ⟨φ, hφ, -⟩
  have h2 : (hφ.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X]))) ^ 2 = (d : ℝ) := by
    have := congrArg hφ.embedding (root_sq d)
    rwa [map_pow, eq_ratCast (algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X]))) d,
      map_ratCast] at this
  have hd' : (d : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (hφ.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])))]

end AdjRoot


end LinAlg

local notation "Kd[" d "]" => AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)

/-- `root` is not rational: `x + y·√d = 0` with `x, y ∈ ℚ` forces `x = y = 0` (`d < 0`). -/
theorem root_lin_indep (d : ℚ) (hd : d < 0) (x y : ℚ)
    (h : algebraMap ℚ Kd[d] x + algebraMap ℚ Kd[d] y * AdjoinRoot.root _ = 0) : x = 0 ∧ y = 0 := by
  have : Nontrivial Kd[d] := AdjoinRoot.nontrivial _ (by
    rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num)
  have hinj := (algebraMap ℚ Kd[d]).injective
  by_cases hy : y = 0
  · subst hy
    simp only [map_zero, zero_mul, add_zero] at h
    exact ⟨hinj (h.trans (map_zero _).symm), rfl⟩
  · exfalso
    have h1 : algebraMap ℚ Kd[d] y * AdjoinRoot.root _ = -algebraMap ℚ Kd[d] x := by
      linear_combination h
    have h2 : (algebraMap ℚ Kd[d] y * AdjoinRoot.root _) ^ 2 = (algebraMap ℚ Kd[d] x) ^ 2 := by
      rw [h1]; ring
    rw [mul_pow, root_sq, ← map_pow, ← map_mul, ← map_pow] at h2
    have h3 := hinj h2
    have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg x]

/-- The same with integer coefficients. -/
theorem root_lin_indep_int (d : ℚ) (hd : d < 0) (a c : ℤ)
    (h : a • (1 : Kd[d]) + c • AdjoinRoot.root _ = 0) : a = 0 ∧ c = 0 := by
  have := root_lin_indep d hd a c (by
    rw [map_intCast, map_intCast]; rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at h; exact h)
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- **N1a-CM proved from T6.** If `End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, then `End_𝒪(A)` is isomorphic
to a subring of finite index of `𝒪_k`, `k = ℚ(√d)`: `1 ⊗ φ` (`φ ∈ End_𝒪(A)`) commutes with the
images `I, J` of `i, j ∈ 𝒪` (`I² = 2`, `J² = −3`, `JI = −IJ`), hence is a scalar
(`commute_quat_scalar`); `φ ↦` that scalar is an injective ring map `ψ` (T6); its image `R`
consists of integral elements (T6: `End(A)` is finite over `ℤ`), and contains `1` and `s√d`,
`s ≠ 0` (FS4's localization step), so it has rank 2 in `𝒪_k` and finite index. -/
theorem comOfMatrixEnd0_of_homFree (hHF : PkgI3.HomFreeFinite) : ComOfMatrixEnd0 := by
  intro A q d hd hM
  obtain ⟨e⟩ := hM
  letI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) :=
    ⟨irred_sq_sub d hd⟩
  obtain ⟨hNF, hTC⟩ := adjRoot_numberField d hd
  obtain ⟨hfree, hfin, -, -⟩ := hHF Qbar A A
  let g : LeafQM.O →+* AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] AbVar.End A).toRingHom.comp
      q.iota
  have e1 : ∀ a b : AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (a * b) = ((1 : ℚ) ⊗ₜ[ℤ] a) * ((1 : ℚ) ⊗ₜ[ℤ] b) := by
    intro a b; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hI : e (g oi) * e (g oi) = (2 : Kd[d]) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    rw [← map_mul, ← map_mul, oi_mul_oi, map_ofNat, map_ofNat, Algebra.smul_def, mul_one,
      map_ofNat]
  have hJ : e (g oj) * e (g oj) = (-3 : Kd[d]) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    rw [← map_mul, ← map_mul, oj_mul_oj, map_neg, map_neg, map_ofNat, map_ofNat,
      Algebra.smul_def, mul_one, map_neg, map_ofNat]
  have hJI : e (g oj) * e (g oi) = -(e (g oi) * e (g oj)) := by
    rw [← map_mul, ← map_mul, oj_mul_oi, map_neg, map_neg, map_mul, map_mul]
  have hcommφ : ∀ φ ∈ com q, ∀ a : LeafQM.O,
      ((1 : ℚ) ⊗ₜ[ℤ] φ) * g a = g a * ((1 : ℚ) ⊗ₜ[ℤ] φ) := by
    intro φ hφ a
    rw [com, Subring.mem_centralizer_iff] at hφ
    show ((1 : ℚ) ⊗ₜ[ℤ] φ) * ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) = ((1 : ℚ) ⊗ₜ[ℤ] q.iota a) * _
    rw [← e1, ← e1, hφ _ ⟨a, rfl⟩]
  have hsc : ∀ φ ∈ com q, e ((1 : ℚ) ⊗ₜ[ℤ] φ) =
      (e ((1 : ℚ) ⊗ₜ[ℤ] φ) 0 0) • (1 : Matrix (Fin 2) (Fin 2) Kd[d]) := by
    intro φ hφ
    obtain ⟨a, ha⟩ := commute_quat_scalar (e (g oi)) (e (g oj)) hI hJ hJI two_ne_zero
      three_ne_zero (e ((1 : ℚ) ⊗ₜ[ℤ] φ))
      (by rw [← map_mul, ← map_mul, hcommφ φ hφ oi])
      (by rw [← map_mul, ← map_mul, hcommφ φ hφ oj])
    rw [ha]; simp
  -- the scalar map `ψ : End_𝒪(A) → ℚ(√d)`
  let ψ : com q →+* Kd[d] :=
    { toFun := fun φ => e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) 0 0
      map_one' := by
        simp only [OneMemClass.coe_one]
        rw [← Algebra.TensorProduct.one_def, map_one, Matrix.one_apply_eq]
      map_mul' := fun φ φ' => by
        simp only [MulMemClass.coe_mul]
        rw [e1, map_mul, hsc φ φ.2, hsc φ' φ'.2, smul_mul_smul_comm, one_mul]
        simp
      map_zero' := by simp
      map_add' := fun φ φ' => by simp [TensorProduct.tmul_add] }
  have hψ : ∀ φ : com q, e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) = ψ φ • 1 := fun φ => hsc φ φ.2
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ0
    have h0 : e ((1 : ℚ) ⊗ₜ[ℤ] (φ : AbVar.End A)) = 0 := by rw [hψ, hφ0, zero_smul]
    rw [← map_zero e] at h0
    exact Subtype.ext (tmul_one_injective hfree _ (e.injective h0))
  -- an element `s√d` in the image (FS4's localization step)
  set c' : AbVar.End0 A :=
    e.symm ((AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) •
      (1 : Matrix (Fin 2) (Fin 2) Kd[d])) with hc'
  have hcen : ∀ x : AbVar.End0 A, c' * x = x * c' := by
    intro x
    apply e.injective
    rw [map_mul, map_mul, hc', e.apply_symm_apply, smul_mul_assoc, one_mul, mul_smul_comm,
      mul_one]
  let f := TensorProduct.mk ℤ ℚ (AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := AbVar.End A) (S := ℚ))
  obtain ⟨⟨φ₀, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) f c'
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] φ₀ = (s : ℤ) • c' := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hφ₀ : φ₀ ∈ com q := by
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have key : (1 : ℚ) ⊗ₜ[ℤ] (q.iota a * φ₀ - φ₀ * q.iota a) = 0 := by
      rw [TensorProduct.tmul_sub, e1, e1, hs', mul_smul_comm, smul_mul_assoc, ← smul_sub,
        hcen, sub_self, smul_zero]
    exact sub_eq_zero.mp (tmul_one_injective hfree _ key)
  have hw : ψ ⟨φ₀, hφ₀⟩ = (s : ℤ) • AdjoinRoot.root _ := by
    change e ((1 : ℚ) ⊗ₜ[ℤ] φ₀) 0 0 = _
    rw [hs', map_zsmul, hc', e.apply_symm_apply]
    simp
  -- the order `R = ψ(End_𝒪(A))`
  have hRint : ψ.range ≤ (integralClosure ℤ Kd[d]).toSubring := by
    rintro _ ⟨φ, rfl⟩
    have h1 : IsIntegral ℤ (φ : AbVar.End A) := Algebra.IsIntegral.isIntegral _
    have h2 : IsIntegral ℤ φ :=
      (isIntegral_algHom_iff ((com q).subtype.toIntAlgHom) Subtype.val_injective).mp h1
    exact h2.map ψ.toIntAlgHom
  refine ⟨Kd[d], inferInstance, hNF, hTC, finrank_adjRoot d, ψ.range, hRint, ?_,
    ⟨RingEquiv.ofBijective ψ.rangeRestrict
      ⟨fun a b h => hψinj (congrArg Subtype.val h), ψ.rangeRestrict_surjective⟩⟩⟩
  -- finite index: `R ∩ 𝒪_k` has rank 2 (it contains `1` and `s√d`)
  let fO : NumberField.RingOfIntegers Kd[d] →+ Kd[d] :=
    (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d]).toAddMonoidHom
  have hrange : (integralClosure ℤ Kd[d]).toSubring.toAddSubgroup =
      (⊤ : AddSubgroup (NumberField.RingOfIntegers Kd[d])).map fO := by
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
    · rintro ⟨y, -, rfl⟩; exact y.2
  unfold LeafQM.AV.conductor
  suffices hsuff : (ψ.range.toAddSubgroup.comap fO).index ≠ 0 by
    convert hsuff using 1
    rw [← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap, ← hrange]
    rfl
  let N' : Submodule ℤ (NumberField.RingOfIntegers Kd[d]) :=
    (ψ.range.toAddSubgroup.comap fO).toIntSubmodule
  have hw' : IsIntegral ℤ ((s : ℤ) •
      AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ)) := by
    rw [← hw]; exact hRint ⟨_, rfl⟩
  let w' : NumberField.RingOfIntegers Kd[d] := ⟨_, hw'⟩
  have h1N : (1 : NumberField.RingOfIntegers Kd[d]) ∈ N' := by
    show fO 1 ∈ ψ.range
    rw [show fO 1 = 1 from map_one (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d])]
    exact ψ.range.one_mem
  have hwN : w' ∈ N' := ⟨⟨φ₀, hφ₀⟩, hw⟩
  have hv : LinearIndependent ℤ ![(⟨1, h1N⟩ : N'), ⟨w', hwN⟩] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have hK := congrArg (fun z : N' => fO (z : NumberField.RingOfIntegers Kd[d])) hab
    simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_zsmul, Submodule.coe_zero,
      map_zero] at hK
    have e1' : fO 1 = 1 := map_one (algebraMap (NumberField.RingOfIntegers Kd[d]) Kd[d])
    have e2' : fO w' = (s : ℤ) •
        AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ) := rfl
    rw [e1', e2', smul_smul] at hK
    obtain ⟨ha, hbs⟩ := root_lin_indep_int d hd _ _ hK
    exact ⟨ha, (mul_eq_zero.mp hbs).resolve_right hs0⟩
  have hfr : Module.finrank ℤ N' = Module.finrank ℤ (NumberField.RingOfIntegers Kd[d]) := by
    apply le_antisymm (Submodule.finrank_le N')
    rw [NumberField.RingOfIntegers.rank, finrank_adjRoot]
    simpa using hv.fintype_card_le_finrank
  have := Submodule.finiteQuotientOfFreeOfRankEq N' hfr
  exact AddSubgroup.index_ne_zero_of_finite (hH := this)

/-- **N1a proved from the leaves T27 (Yu) and T6.** -/
theorem comIntOrQuadOrder_of_leaves (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) :
    ComIntOrQuadOrder :=
  comIntOrQuadOrder_of t27 t6 (comOfMatrixEnd0_of_homFree t6)

/-- **FS5 with the repaired clauses, from the leaves and named glue**: the bundle, R5fpCount,
T27, T6 and N1b (leaves), and `MobiusGlue` and N2 (glue). -/
theorem fibreComTrivialFull_of_leaves' (hL : R1R2fpFull) (hM : MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of hL hM (comIntOrQuadOrder_of_leaves t27 t6) hB hK hC

end FS5NoCM


/-! ## §I N1b reduced to Shimura's description of CM points (`CMOptimalEmbedding`)

`R = φ⁻¹(𝒪)` for an embedding `φ : k → B` forces `(f(R), 6) = 1`: N5's `𝒪` is the set of
integral elements of `B_p` for `p = 2, 3` (finite checks `check2`, `check3` modulo `p²`). -/

namespace FS5NoCM


set_option maxRecDepth 100000 in
theorem check3 : ∀ a b c d : ZMod 9,
    a ^ 2 + a * c + c ^ 2 + 7 * (b ^ 2 + b * d + d ^ 2) = 0 →
      3 ∣ a.val ∧ 3 ∣ b.val ∧ 3 ∣ c.val ∧ 3 ∣ d.val := by decide

set_option maxRecDepth 100000 in
theorem check2 : ∀ a b c d : ZMod 4,
    a ^ 2 + a * c + c ^ 2 + 2 * (b ^ 2 + b * d + d ^ 2) = 0 →
      2 ∣ a.val ∧ 2 ∣ b.val ∧ 2 ∣ c.val ∧ 2 ∣ d.val := by decide

open LeafQM

/-- The reduced norm of `ofInt n`, as an integer quadratic form. -/
def Qf (n : Fin 4 → ℤ) : ℤ := n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)

theorem nrd_ofInt (n : Fin 4 → ℤ) : ofInt n * star (ofInt n) = algebraMap ℚ B (Qf n : ℚ) := by
  ext <;> simp [ofInt, Qf, QuaternionAlgebra.algebraMap_eq] <;> ring

/-- `p² ∣ nrd(ofInt n)` forces `p ∣ n` for `p = 2, 3` (`𝒪_p` is the set of integral elements of
the ramified `B_p`; a finite check modulo `p²`). -/
theorem dvd_of_sq_dvd_Qf (p : ℕ) (hp : p = 2 ∨ p = 3) (n : Fin 4 → ℤ) (h : (p : ℤ) ^ 2 ∣ Qf n) :
    ∀ i, (p : ℤ) ∣ n i := by
  rcases hp with rfl | rfl
  · have h0 : ((Qf n : ℤ) : ZMod 4) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    have e : ((n 0 : ℤ) : ZMod 4) ^ 2 + (n 0 : ZMod 4) * (n 2 : ZMod 4) + (n 2 : ZMod 4) ^ 2 +
        2 * ((n 1 : ZMod 4) ^ 2 + (n 1 : ZMod 4) * (n 3 : ZMod 4) + (n 3 : ZMod 4) ^ 2) = 0 := by
      have h4 : (4 : ZMod 4) = 0 := by decide
      rw [← h0]; simp only [Qf]; push_cast
      linear_combination (((n 1 : ZMod 4) ^ 2 + (n 1 : ZMod 4) * (n 3 : ZMod 4) +
        (n 3 : ZMod 4) ^ 2)) * h4
    obtain ⟨a, b, c, d⟩ := check2 _ _ _ _ e
    have key : ∀ m : ℤ, 2 ∣ ((m : ZMod 4)).val → (2 : ℤ) ∣ m := by
      intro m hm
      have hv : (((m : ZMod 4)).val : ℤ) = m % 4 := ZMod.val_intCast m
      have h2 : (2 : ℤ) ∣ m % 4 := by
        have := Int.natCast_dvd_natCast.mpr hm
        rwa [hv] at this
      omega
    intro i; fin_cases i
    · exact key _ a
    · exact key _ b
    · exact key _ c
    · exact key _ d
  · have h0 : ((Qf n : ℤ) : ZMod 9) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    have e : ((n 0 : ℤ) : ZMod 9) ^ 2 + (n 0 : ZMod 9) * (n 2 : ZMod 9) + (n 2 : ZMod 9) ^ 2 +
        7 * ((n 1 : ZMod 9) ^ 2 + (n 1 : ZMod 9) * (n 3 : ZMod 9) + (n 3 : ZMod 9) ^ 2) = 0 := by
      have h9 : (9 : ZMod 9) = 0 := by decide
      rw [← h0]; simp only [Qf]; push_cast
      linear_combination (((n 1 : ZMod 9) ^ 2 + (n 1 : ZMod 9) * (n 3 : ZMod 9) +
        (n 3 : ZMod 9) ^ 2)) * h9
    obtain ⟨a, b, c, d⟩ := check3 _ _ _ _ e
    have key : ∀ m : ℤ, 3 ∣ ((m : ZMod 9)).val → (3 : ℤ) ∣ m := by
      intro m hm
      have hv : (((m : ZMod 9)).val : ℤ) = m % 9 := ZMod.val_intCast m
      have h2 : (3 : ℤ) ∣ m % 9 := by
        have := Int.natCast_dvd_natCast.mpr hm
        rwa [hv] at this
      omega
    intro i; fin_cases i
    · exact key _ a
    · exact key _ b
    · exact key _ c
    · exact key _ d

theorem ofInt_nsmul (p : ℕ) (w : Fin 4 → ℤ) : ofInt (fun i => (p : ℤ) * w i) = (p : ℚ) • ofInt w := by
  ext <;> simp [ofInt] <;> ring

theorem mul_star_comm (x : B) : star x * x = x * star x := by
  ext <;> simp <;> ring

/-- **Optimal embeddings have conductor prime to 6** (the algebra behind N1b). If `R ⊆ 𝒪_k` is
the preimage `φ⁻¹(𝒪)` of N5's maximal order under an embedding `φ : k → B` and has finite index,
then `p ∤ [𝒪_k : R]` for `p = 2, 3`: otherwise some `y ∈ 𝒪_k ∖ R` has `p y ∈ R`, so
`φ(p y) = ofInt v ∈ 𝒪`; `nrd φ(y) ∈ ℤ` (its minimal polynomial is that of `y`, integral), so
`p² ∣ nrd(ofInt v)`, hence `p ∣ v` (`dvd_of_sq_dvd_Qf`) and `φ(y) ∈ 𝒪`, i.e. `y ∈ R`. -/
theorem not_dvd_conductor_of_optimal {k : Type} [Field k] [NumberField k]
    (φ : k →ₐ[ℚ] B) (R : Subring k) (hR : R = O.comap φ.toRingHom)
    (hc0 : AV.conductor R ≠ 0) (p : ℕ) (hp : p = 2 ∨ p = 3) : ¬ p ∣ AV.conductor R := by
  intro hdvd
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  set L := (integralClosure ℤ k).toSubring.toAddSubgroup with hL
  set H := R.toAddSubgroup.addSubgroupOf L with hH
  have hidx : H.index = AV.conductor R := rfl
  have hcard : Nat.card (↥L ⧸ H) = AV.conductor R := by rw [← AddSubgroup.index_eq_card, hidx]
  have hfin : Finite (↥L ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hc0)
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := ↥L ⧸ H) p (by rw [hcard]; exact hdvd)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective g
  have hyR : (y : k) ∉ R := by
    intro hy
    have h0 : ((y : ↥L) : ↥L ⧸ H) = 0 := (QuotientAddGroup.eq_zero_iff y).mpr hy
    rw [h0, addOrderOf_zero] at hg
    exact hpp.one_lt.ne hg
  have hpy : p • (y : k) ∈ R := by
    have h1 : p • ((y : ↥L) : ↥L ⧸ H) = 0 := by rw [← hg]; exact addOrderOf_nsmul_eq_zero _
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h1
    exact h1
  have hyint : IsIntegral ℤ (y : k) := y.2
  have hynq : (y : k) ∉ Set.range (algebraMap ℚ k) := by
    rintro ⟨q, hq⟩
    have hqi : IsIntegral ℤ q :=
      (isIntegral_algHom_iff ((Algebra.ofId ℚ k).restrictScalars ℤ)
        (algebraMap ℚ k).injective).mp (by rw [← hq] at hyint; exact hyint)
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqi
    apply hyR
    rw [← hq, ← hm]
    have : algebraMap ℚ k (algebraMap ℤ ℚ m) = (m : k) := by simp
    rw [this]; exact intCast_mem R m
  set x : B := φ (y : k) with hx
  have hxint : IsIntegral ℤ x := hyint.map (φ.restrictScalars ℤ)
  have hxnq : x ∉ Set.range (algebraMap ℚ B) := by
    rintro ⟨q, hq⟩
    apply hynq
    refine ⟨q, φ.injective ?_⟩
    change φ (algebraMap ℚ k q) = φ y
    rw [AlgHom.commutes]; exact hq
  -- the minimal polynomial of `x` is `X² − t X + n`, with integer coefficients
  set t : ℚ := 2 * x.re with ht
  set n : ℚ := (x * star x).re with hn
  have hxx : x * star x = algebraMap ℚ B n := by
    rw [hn, QuaternionAlgebra.mul_star_eq_coe]; rfl
  have hsum : x + star x = algebraMap ℚ B t := by
    rw [QuaternionAlgebra.self_add_star', ht]; simp
  have hP : Polynomial.aeval x (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (-t) * Polynomial.X + Polynomial.C n) = 0 := by
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X,
      map_one, one_mul, map_neg]
    rw [← hsum, ← hxx, ← mul_star_comm]
    noncomm_ring
  have hPm : (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X +
      Polynomial.C n).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_quadratic one_ne_zero]
  have hPd : (Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 + Polynomial.C (-t) * Polynomial.X +
      Polynomial.C n).natDegree = 2 := Polynomial.natDegree_quadratic one_ne_zero
  have hxintQ : IsIntegral ℚ x := hxint.tower_top
  have hmin : minpoly ℚ x = Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (-t) * Polynomial.X + Polynomial.C n := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxintQ) hPm
      (minpoly.dvd ℚ x hP) ?_).symm
    rw [hPd]
    exact (minpoly.two_le_natDegree_iff hxintQ).mpr hxnq
  have hmin' : minpoly ℚ x = (minpoly ℤ (y : k)).map (algebraMap ℤ ℚ) := by
    rw [hx, minpoly.algHom_eq φ φ.injective]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hyint
  obtain ⟨N, hN⟩ : ∃ N : ℤ, (N : ℚ) = n := by
    refine ⟨(minpoly ℤ (y : k)).coeff 0, ?_⟩
    have := congrArg (fun P : Polynomial ℚ => P.coeff 0) (hmin.symm.trans hmin')
    simp only [Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at this
    simpa using this.symm
  -- `φ(p y) = p x ∈ 𝒪`, so `p² ∣ nrd`, so `x ∈ 𝒪`
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hz : (p : ℚ) • x ∈ O := by
    have h1 : p • (y : k) ∈ O.comap φ.toRingHom := hR ▸ hpy
    have h2 : φ (p • (y : k)) ∈ O := h1
    rwa [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at h2
  obtain ⟨v, hv⟩ := hz
  have hQ : (Qf v : ℚ) = (p : ℚ) ^ 2 * N := by
    have h1 := nrd_ofInt v
    rw [← hv, star_smul, smul_mul_smul_comm, hxx, Algebra.smul_def, ← map_mul] at h1
    rw [hN, ← (algebraMap ℚ B).injective h1, star_trivial]; ring
  have hQ' : (p : ℤ) ^ 2 ∣ Qf v := ⟨N, by exact_mod_cast hQ⟩
  choose w hw using dvd_of_sq_dvd_Qf p hp v hQ'
  have hvw : v = fun i => (p : ℤ) * w i := funext hw
  have hxw : x = ofInt w := by
    apply smul_right_injective B hp0
    simp only
    rw [hv, hvw, ofInt_nsmul]
  apply hyR
  rw [hR]
  exact ⟨w, hxw⟩

/-- **N1b′ (leaf; Shimura's description of CM points on `X₀(6,1)`).** If `End_𝒪(A) ≅ R` for an order
`R` of an imaginary quadratic `k`, then `R` is the preimage `φ⁻¹(𝒪)` of N5's maximal order under
some `ℚ`-embedding `φ : k → B`.
*Published statement*: for `(A, ι)` over `ℂ` with CM, `A = ℂ²/𝒪 v_τ` and `End_𝒪(A) ≅ φ_τ(k) ∩ 𝒪`,
where `φ_τ : k → B` is the embedding whose image fixes `τ ∈ ℍ` (Shimura, Ann. of Math. 85 (1967);
Jordan, thesis (Harvard 1981) §3; González–Rotger, J. Math. Soc. Japan 58 (2006) §5; locators
UNVERIFIED); in characteristic 0 the same holds over `ℚ̄`. Transport to the given `k ⊇ R`: an
isomorphism `R ≅ φ_τ(k) ∩ 𝒪` extends to the fraction fields `k ≅ k_τ` (`R` has rank 2), and the
composite embedding pulls `𝒪` back to `R`. A consequence of the published statement (up to
replacing `B` by `B^op ≅ B`, which preserves `𝒪`). -/
def CMOptimalEmbedding : Prop :=
  ∀ (P : AV.QMPair AV.Qbar) (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 → ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring →
      AV.conductor R ≠ 0 → Nonempty (AV.com P.q ≃+* R) →
        ∃ φ : k →ₐ[ℚ] B, R = O.comap φ.toRingHom

theorem cmConductorCoprime6_of (h : CMOptimalEmbedding) : CMConductorCoprime6 := by
  intro P k _ _ _ hk2 R hR hc0 he
  obtain ⟨φ, hφ⟩ := h P k hk2 R hR hc0 he
  have h2 := not_dvd_conductor_of_optimal φ R hφ hc0 2 (Or.inl rfl)
  have h3 := not_dvd_conductor_of_optimal φ R hφ hc0 3 (Or.inr rfl)
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
  exact ⟨(Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)),
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))⟩


/-- **FS5 with the repaired clauses, from leaves and named glue**: the bundle, R5fpCount, T27, T6,
N1b′ `CMOptimalEmbedding` (leaves), and `MobiusGlue`, N2 (glue). -/
theorem fibreComTrivialFull_of_leaves'' (hL : R1R2fpFull) (hM : LeafQM.AV.Pin.MobiusGlue)
    (t27 : PkgI3.QMDichotomyYu) (t6 : PkgI3.HomFreeFinite) (hE : CMOptimalEmbedding)
    (hK : X6KummerFibre) (hC : LeafQM.AV.R5fpCount) : FibreComTrivialFull :=
  fibreComTrivialFull_of_leaves' hL hM t27 t6 (cmConductorCoprime6_of hE) hK hC

end FS5NoCM


end

