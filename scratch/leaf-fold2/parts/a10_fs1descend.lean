-- (leaf-fold2: copied from scratch/g0-assemble2/parts/a10_fs1descend.lean; 0 HDec name-resolution edits)
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
