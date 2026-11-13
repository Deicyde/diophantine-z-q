/-! ## rv-gluepieces2 check (b): proofs of three fields, pasted verbatim, applied to G0Assemble's constants.
fs1-descend (FiniteDescends.lean L22-117), unram-tate (UnramSup.lean L16-127), (metrization's field 6: see c6). -/

section RvFS1
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
end RvFS1

section RvUnram
open NumberField GlueDescent.B2Q

namespace UnramTate

/-- `ℚ̄`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- Intermediate fields of `ℚ̄/ℚ` (copied from g0-mod-field, `G0ModField.IF`). -/
abbrev IF : Type := IntermediateField ℚ Qbar

instance : IsGalois ℚ Qbar := {}

/-- **Compositum of unramified fields (STANDARD; remaining, not in Mathlib v4.35).** If `E`
and `K` are finite over `ℚ` and unramified at `p`, so is `E ⊔ K` (Neukirch, *Algebraic Number
Theory*, I (8.?)/III, UNVERIFIED locator; a prime is unramified in a compositum iff it is in both
factors, for Galois factors). -/
def UnramifiedSup : Prop :=
  ∀ (E K : IF) [FiniteDimensional ℚ E] [FiniteDimensional ℚ K] [IsGalois ℚ E] [IsGalois ℚ K]
    (p : ℕ), UnramifiedAt E p → UnramifiedAt K p → UnramifiedAt (E ⊔ K) p

/-- A finite intermediate field is a number field. -/
theorem numberField_of_fd' (L : IF) [FiniteDimensional ℚ L] : NumberField L :=
  { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

/-- For a finite Galois `L` unramified at `p` and a prime `P ∋ p` of `𝓞 L`, the inertia group
`I(P) ≤ Gal(L/ℚ)` is trivial (`#I(P) = e(P) = 1`). -/
theorem inertia_trivial (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (p : ℕ)
    (hL : UnramifiedAt L p) (P : Ideal (𝓞 L)) [hP : P.IsPrime] (hpP : ((p : ℤ) : 𝓞 L) ∈ P)
    (g : L ≃ₐ[ℚ] L) (hg : g ∈ P.inertia (L ≃ₐ[ℚ] L)) : g = 1 := by
  haveI : NumberField L := numberField_of_fd' L
  have he : P.ramificationIdx ℤ = 1 := hL P hP hpP
  have hcard : Nat.card (P.inertia (L ≃ₐ[ℚ] L)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (P.under ℤ) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P (L ≃ₐ[ℚ] L), he]
  have hsub : Subsingleton (P.inertia (L ≃ₐ[ℚ] L)) := (Nat.card_eq_one_iff_unique.mp hcard).1
  have := Subsingleton.elim (⟨g, hg⟩ : P.inertia (L ≃ₐ[ℚ] L)) 1
  exact congrArg Subtype.val this

/-- `𝓞 E → 𝓞 M` for `E ≤ M`. -/
noncomputable def incO {E M : IF} (h : E ≤ M) : 𝓞 E →+* 𝓞 M :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom

theorem incO_coe {E M : IF} (h : E ≤ M) (x : 𝓞 E) :
    (((incO h x : 𝓞 M) : M) : Qbar) = ((x : E) : Qbar) := rfl

/-- **Restriction of inertia.** If `E ≤ M` are finite Galois, `E` unramified at `p`, `Q ∋ p` a
prime of `𝓞 M` and `g ∈ I(Q)`, then a lift `s ∈ G_ℚ` of `g` fixes `E` pointwise. -/
theorem lift_fixes (E M : IF) [FiniteDimensional ℚ E] [FiniteDimensional ℚ M] [IsGalois ℚ E]
    [IsGalois ℚ M] (hEM : E ≤ M) (p : ℕ) (hE : UnramifiedAt E p) (Q : Ideal (𝓞 M))
    [hQ : Q.IsPrime] (hpQ : ((p : ℤ) : 𝓞 M) ∈ Q) (g : M ≃ₐ[ℚ] M)
    (hg : g ∈ Q.inertia (M ≃ₐ[ℚ] M)) (s : Qbar ≃ₐ[ℚ] Qbar)
    (hs : ∀ y : M, s (y : Qbar) = ((g y : M) : Qbar)) :
    ∀ x ∈ E, s x = x := by
  let QE : Ideal (𝓞 E) := Q.comap (incO hEM)
  haveI : QE.IsPrime := Ideal.comap_isPrime _ _
  have hpQE : ((p : ℤ) : 𝓞 E) ∈ QE := by
    show incO hEM ((p : ℤ) : 𝓞 E) ∈ Q
    rw [map_intCast]; exact hpQ
  let gE : E ≃ₐ[ℚ] E := s.restrictNormal E
  have hgE : ∀ x : E, ((gE x : E) : Qbar) = s (x : Qbar) :=
    fun x => AlgEquiv.restrictNormal_commutes s E x
  have hmem : gE ∈ QE.inertia (E ≃ₐ[ℚ] E) := by
    rw [Ideal.mem_inertia]
    intro x
    show incO hEM (gE • x - x) ∈ Q
    have hx : incO hEM (gE • x) = g • incO hEM x := by
      apply Subtype.ext; apply Subtype.ext
      show ((gE (x : E) : E) : Qbar) = ((g ((incO hEM x : 𝓞 M) : M) : M) : Qbar)
      rw [hgE, ← hs]; rfl
    rw [map_sub, hx]
    exact (Ideal.mem_inertia.mp hg) (incO hEM x)
  have h1 := inertia_trivial E p hE QE hpQE gE hmem
  intro x hx
  have := hgE ⟨x, hx⟩
  rw [h1] at this
  exact this.symm

/-- **`UnramifiedSup`, proved** (no leaf). -/
theorem unramifiedSup : UnramifiedSup := by
  intro E K _ _ _ _ p hE hK
  let M : IF := E ⊔ K
  haveI : FiniteDimensional ℚ M := inferInstance
  haveI : IsGalois ℚ M := IsGalois.mk
  haveI : NumberField M := numberField_of_fd' M
  intro Q hQ hpQ
  have htriv : ∀ g ∈ Q.inertia (M ≃ₐ[ℚ] M), g = 1 := by
    intro g hg
    let s : Qbar ≃ₐ[ℚ] Qbar := g.liftNormal Qbar
    have hs : ∀ y : M, s (y : Qbar) = ((g y : M) : Qbar) :=
      fun y => AlgEquiv.liftNormal_commutes g Qbar y
    have hEf := lift_fixes E M le_sup_left p hE Q hpQ g hg s hs
    have hKf := lift_fixes K M le_sup_right p hK Q hpQ g hg s hs
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

end UnramTate
end RvUnram

-- (metrization's ExtLine.lean + part_dim.lean moved to c6_metrization.lean, which already contains them;
-- `RvGP2.metrizationDimUnique` is proved there.)

namespace RvGP2

/-- Field 3 of `GluePieces2` is a theorem (fs1-descend's proof, verbatim statement). -/
theorem finiteDescends : G0FibreSimple.FiniteDescends := FS1Descend.finiteDescends

/-- Field 14 of `GluePieces2` is a theorem (unram-tate's proof, verbatim statement). -/
theorem unramifiedSup : G0ModField.UnramifiedSup := UnramTate.unramifiedSup


end RvGP2

#print axioms RvGP2.finiteDescends
#print axioms RvGP2.unramifiedSup
