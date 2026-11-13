/-! ## rv-gluepieces2 check (b): proofs of three fields, pasted verbatim, applied to G0Assemble's constants.
fs1-descend (FiniteDescends.lean L22-117), unram-tate (UnramSup.lean L16-127), metrization (ExtLine.lean body + part_dim.lean). -/

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

section RvMetDim
-- scratch/metrization/ExtLine.lean (minus import and #print lines), then part_dim.lean

/-!
# metrization: the degree of a Hodge line is unique (pure algebra)

For a flat `R`-algebra `F` that is a field and any `R`-module `C`: if `F ⊗_R ⋀^g_R C` and
`F ⊗_R ⋀^{g'}_R C` are both `F`-lines and `0 < g`, `0 < g'`, then `g = g'`.
(Applied with `R = 𝓞_L`, `F = L`, `C = 𝔪_ξ/𝔪_ξ²`: `hodgeSpace g` determines `g ≥ 1`.)
-/

open scoped TensorProduct

namespace ZInQ.Metrization

variable {R F C : Type*} [CommRing R] [Field F] [Algebra R F] [AddCommGroup C] [Module R C]

/-- If `F ⊗ ⋀^n C ≠ 0` (positive finrank) some `1 ⊗ v₁ ∧ ⋯ ∧ vₙ` is nonzero. -/
theorem exists_one_tmul_ιMulti_ne_zero (n : ℕ)
    (h : Module.finrank F (F ⊗[R] ⋀[R]^n C) ≠ 0) :
    ∃ v : Fin n → C, (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R n v ≠ 0 := by
  by_contra! hv
  apply h
  have hall : ∀ x : F ⊗[R] ⋀[R]^n C, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m =>
      have hm : m ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
        rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        rw [show a ⊗ₜ[R] exteriorPower.ιMulti R n v =
          a • ((1 : F) ⊗ₜ[R] exteriorPower.ιMulti R n v) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], hv v, smul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, hx, hy, add_zero]
      | smul r x _ hx => rw [TensorProduct.tmul_smul, hx, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  haveI : Subsingleton (F ⊗[R] ⋀[R]^n C) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- The core: `F ⊗ ⋀^g C` and `F ⊗ ⋀^{g+n} C` cannot both be lines when `g, n ≥ 1`. -/
theorem not_finrank_one_of_add [Module.Flat R F] {g n : ℕ} (hg : 0 < g) (hn : 0 < n)
    (h : Module.finrank F (F ⊗[R] ⋀[R]^g C) = 1)
    (h' : Module.finrank F (F ⊗[R] ⋀[R]^(g + n) C) = 1) : False := by
  obtain ⟨v, hv⟩ := exists_one_tmul_ιMulti_ne_zero (R := R) (F := F) (C := C) (g + n)
    (by rw [h']; exact one_ne_zero)
  -- `Z = 1 ⊗ ιMulti v ≠ 0` in `F ⊗ ⋀ C` (flatness)
  let ι' : ⋀[R]^(g + n) C →ₗ[R] ExteriorAlgebra R C := (⋀[R]^(g + n) C).subtype
  have hinj : Function.Injective (ι'.lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι' Subtype.val_injective
  have hZ : (1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v ≠ 0 := by
    intro h0
    apply hv
    apply hinj
    rw [LinearMap.lTensor_tmul, map_zero]
    exact h0
  let a : Fin g → C := fun i => v (Fin.castAdd n i)
  let b : Fin n → C := fun j => v (Fin.natAdd g j)
  have hab : Fin.append a b = v := Fin.append_castAdd_natAdd
  let i0 : Fin g := ⟨0, hg⟩
  let j0 : Fin n := ⟨0, hn⟩
  let a' : Fin g → C := Function.update a i0 (b j0)
  let b' : Fin n → C := Function.update b j0 (a i0)
  have hp : (Fin.castAdd n i0 : Fin (g + n)) ≠ Fin.natAdd g j0 := by
    intro hc
    have := congrArg Fin.val hc
    simp [i0, j0] at this
    omega
  -- the four products
  have h1 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a' b) = 0 := by
    apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
    intro hi
    apply hp
    apply hi
    simp [a', Fin.append_left, Fin.append_right]
  have h2 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a b') = 0 := by
    apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
    intro hi
    apply hp
    apply hi
    simp [b', Fin.append_left, Fin.append_right]
  have hswap : Fin.append a' b' = v ∘ Equiv.swap (Fin.castAdd n i0) (Fin.natAdd g j0) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left, Function.comp_apply]
      by_cases hi : i = i0
      · subst hi
        rw [Equiv.swap_apply_left]
        simp [a', b]
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · simp [a', hi, a]
        · exact fun hc => hi (Fin.castAdd_injective _ _ hc)
        · intro hc
          have := congrArg Fin.val hc
          simp at this
          omega
    · rw [Fin.append_right, Function.comp_apply]
      by_cases hj : j = j0
      · subst hj
        rw [Equiv.swap_apply_right]
        simp [b', a]
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · simp [b', hj, b]
        · intro hc
          have := congrArg Fin.val hc
          simp at this
          omega
        · exact fun hc => hj (Fin.natAdd_injective _ _ hc)
  have h3 : ExteriorAlgebra.ιMulti R (g + n) (Fin.append a' b') =
      -ExteriorAlgebra.ιMulti R (g + n) v := by
    rw [hswap]
    exact (ExteriorAlgebra.ιMulti R (g + n)).map_swap v hp
  -- the two wedge maps, base changed
  let Φ := (LinearMap.mulRight R (ExteriorAlgebra.ιMulti R n b) ∘ₗ (⋀[R]^g C).subtype).baseChange F
  let Ψ := (LinearMap.mulRight R (ExteriorAlgebra.ιMulti R n b') ∘ₗ (⋀[R]^g C).subtype).baseChange F
  set XS : F ⊗[R] ⋀[R]^g C := (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R g a
  set XT : F ⊗[R] ⋀[R]^g C := (1 : F) ⊗ₜ[R] exteriorPower.ιMulti R g a'
  have hΦS : Φ XS = (1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v := by
    simp only [Φ, XS, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      hab]
  have hΨS : Ψ XS = 0 := by
    simp only [Ψ, XS, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      h2, TensorProduct.tmul_zero]
  have hΨT : Ψ XT = -((1 : F) ⊗ₜ[R] ExteriorAlgebra.ιMulti R (g + n) v) := by
    simp only [Ψ, XT, LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe, LinearMap.mulRight_apply, ExteriorAlgebra.ιMulti_mul_ιMulti,
      h3, TensorProduct.tmul_neg]
  have hXS : XS ≠ 0 := by
    intro h0
    apply hZ
    rw [← hΦS, h0, map_zero]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' XS hXS).mp h XT
  apply hZ
  have : Ψ XT = 0 := by rw [← hc, map_smul, hΨS, smul_zero]
  rw [hΨT, neg_eq_zero] at this
  exact this

/-- **The degree of a Hodge line is unique.** -/
theorem eq_of_finrank_one [Module.Flat R F] {g g' : ℕ} (hg : 0 < g) (hg' : 0 < g')
    (h : Module.finrank F (F ⊗[R] ⋀[R]^g C) = 1)
    (h' : Module.finrank F (F ⊗[R] ⋀[R]^g' C) = 1) : g = g' := by
  rcases lt_trichotomy g g' with hlt | heq | hgt
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact (not_finrank_one_of_add hg (Nat.succ_pos n) h h').elim
  · exact heq
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    exact (not_finrank_one_of_add hg' (Nat.succ_pos n) h' h).elim

end ZInQ.Metrization



/-! ## metrization (2026-11-13): `MetrizationDimUnique`, proved -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- A discrete `ℤ`-submodule of `ℂ^g`, `g ≥ 1`, is not all of `ℂ^g`. -/
theorem exists_not_mem_of_discrete {g : ℕ} (hg : 0 < g) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] : ∃ z, z ∉ Λ := by
  by_contra! hall
  let e : Fin g → ℂ := Pi.single ⟨0, hg⟩ 1
  let f : ℝ → Λ := fun t => ⟨(t : ℂ) • e, hall _⟩
  have hf : Continuous f :=
    Continuous.subtype_mk (Complex.continuous_ofReal.smul continuous_const) _
  have h1 := PreconnectedSpace.constant inferInstance hf (x := 0) (y := 1)
  have h2 := congrArg (fun x : Λ => (x : Fin g → ℂ) ⟨0, hg⟩) h1
  simp [f, e] at h2

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A metrization of dimension `g ≥ 1` has a nontrivial complex point at every `τ`. -/
theorem metrized_exists_pts_ne_one {g : ℕ} (hg : 0 < g) (M : MetrizedModel A L g)
    (τ : L →+* ℂ) : ∃ p : M.model.Pts τ, p ≠ 1 := by
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  haveI := M.hodge.periods_discrete τ
  obtain ⟨z, hz⟩ := exists_not_mem_of_discrete hg (M.hodge.periods τ)
  exact ⟨Φ z, fun h => hz ((hΦ.2.1 z).mp h)⟩

/-- A metrization of dimension `0` forces `𝒢(ℂ)_τ` to be trivial (`Φ : ℂ⁰ → 𝒢(ℂ)_τ` is onto). -/
theorem metrized_pts_subsingleton (M : MetrizedModel A L 0) (τ : L →+* ℂ) :
    Subsingleton (M.model.Pts τ) := by
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  refine ⟨fun p q => ?_⟩
  obtain ⟨z, rfl⟩ := hΦ.2.2.1 p
  obtain ⟨w, rfl⟩ := hΦ.2.2.1 q
  rw [Subsingleton.elim z w]

/-- **`MetrizationDimUnique`, proved.** Two metrizations of one group model have the same
dimension. For `g, g' ≥ 1`: `hodgeSpace g = L ⊗ ⋀^g C` is a line for at most one `g ≥ 1`
(`eq_of_finrank_one`, `L` flat over `𝓞_L`). For `g = 0 < g'`: the dimension-`0` uniformization
makes `𝒢(ℂ)_τ` trivial, the dimension-`g'` one (discrete kernel) makes it nontrivial. -/
theorem metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique := by
  intro K _ A L _ _ _ g g' M M' h
  obtain ⟨τ⟩ := (inferInstance : Nonempty (L →+* ℂ))
  have key : ∀ {g g' : ℕ} (M : MetrizedModel A L g) (M' : MetrizedModel A L g'),
      M.model = M'.model → g = 0 → g' = 0 := by
    intro g g' M M' h hg0
    subst hg0
    by_contra hg'
    obtain ⟨p, hp⟩ := metrized_exists_pts_ne_one (Nat.pos_of_ne_zero hg') M' τ
    have hs := metrized_pts_subsingleton M τ
    rw [h] at hs
    exact hp (Subsingleton.elim _ _)
  by_cases hg : g = 0
  · rw [hg, key M M' h hg]
  by_cases hg' : g' = 0
  · rw [hg', key M' M h.symm hg']
  haveI : Module.Flat (𝓞 L) L := IsLocalization.flat L (nonZeroDivisors (𝓞 L))
  have h1 := M.hodge.finrank_eq_one
  have h2 := M'.hodge.finrank_eq_one
  rw [← h] at h2
  exact eq_of_finrank_one (R := 𝓞 L) (F := L) (C := M.model.cotangent)
    (Nat.pos_of_ne_zero hg) (Nat.pos_of_ne_zero hg') h1 h2

end ZInQ.Metrization

#print axioms ZInQ.Metrization.metrizationDimUnique
end RvMetDim

namespace RvGP2

/-- Field 3 of `GluePieces2` is a theorem (fs1-descend's proof, verbatim statement). -/
theorem finiteDescends : G0FibreSimple.FiniteDescends := FS1Descend.finiteDescends

/-- Field 14 of `GluePieces2` is a theorem (unram-tate's proof, verbatim statement). -/
theorem unramifiedSup : G0ModField.UnramifiedSup := UnramTate.unramifiedSup

/-- Field 6 of `GluePieces2` is a theorem (metrization's proof). -/
theorem metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique :=
  ZInQ.Metrization.metrizationDimUnique

end RvGP2

#print axioms RvGP2.finiteDescends
#print axioms RvGP2.unramifiedSup
#print axioms RvGP2.metrizationDimUnique
