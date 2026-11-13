import ZInQKernel.Contrib.BrauerCohomology.Functoriality
import ZInQKernel.HDecomp.Conductor.I6Base

set_option autoImplicit false

/-!
# The bundle forms of T14/T15 are equivalent to the cochain forms consumed by the glue

`ZInQKernel/HDecomp/Conductor/I6Base.lean` states the three Brauer leaves twice:

* over Mathlib's `continuousCohomology 2 (Z2 ℚ)` with `loc F 2 = ContinuousCohomology.map
  (Field.absoluteGaloisGroup.map (algebraMap ℚ F)) (𝟙 _) 2` (`BrauerHasse2`, `BrauerReciprocity2`,
  `LocalH2Card`; these are the frozen reference targets T14a, T14b, T15 verbatim), and
* over continuous inhomogeneous `ZMod 2`-valued cochains with `resC F` (`BrauerHasse2C`,
  `BrauerReciprocity2C`, `LocalH2CardC`), which is what `cob_of_same_finite_support` and the
  descent glue consume.

They are not definitionally equal. Using the comparison of `Comparison.lean`/`Functoriality.lean`
(absolute Galois groups of characteristic-zero fields are compact, hence locally compact), this file
proves the three equivalences

* `brauerHasse2_iff : BrauerHasse2 ↔ BrauerHasse2C`,
* `brauerReciprocity2_iff : BrauerReciprocity2 ↔ BrauerReciprocity2C`,
* `localH2Card_iff : LocalH2Card ↔ LocalH2CardC`,

for every prime (including `p = 2`) and for the real place, with no hypothesis. The localization
maps on both sides are the *same* term `Field.absoluteGaloisGroup.map (algebraMap ℚ F)` (with the
choice of embedding of algebraic closures made by Mathlib), so no independence-of-embedding argument
is needed. The coefficients are `ZMod 2` with the discrete topology and trivial action on both
sides; over any field of characteristic `≠ 2` this is canonically `μ₂ = {±1}`.
-/

open CategoryTheory PkgI6

namespace ZInQ.Contrib.BrauerCohomology

/-- The absolute Galois group of a field of characteristic zero is compact (it is profinite). -/
theorem compactSpace_absoluteGaloisGroup (K : Type*) [Field K] [CharZero K] :
    CompactSpace (Field.absoluteGaloisGroup K) :=
  inferInstanceAs (CompactSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))

theorem locallyCompactSpace_absoluteGaloisGroup (K : Type*) [Field K] [CharZero K] :
    LocallyCompactSpace (Field.absoluteGaloisGroup K) :=
  have := compactSpace_absoluteGaloisGroup K
  inferInstance

scoped instance (K : Type*) [Field K] [CharZero K] :
    LocallyCompactSpace (Field.absoluteGaloisGroup K) :=
  locallyCompactSpace_absoluteGaloisGroup K

/-- The coefficient module of `PkgI6.loc F`: `ℤ/2` with the action of `G_F` restricted from
`G_ℚ` (trivial). -/
noncomputable abbrev Z2res (F : Type) [Field F] [Algebra ℚ F] :
    TopRep ℤ (Field.absoluteGaloisGroup F) :=
  TopRep.res (Field.absoluteGaloisGroup.map (algebraMap ℚ F) :
    Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup ℚ) (Z2 ℚ)

theorem isTrivialAction_Z2 (K : Type) [Field K] : IsTrivialAction (Z2 K) := fun _ _ => rfl

theorem isTrivialAction_Z2res (F : Type) [Field F] [Algebra ℚ F] :
    IsTrivialAction (Z2res F) := fun _ _ => rfl

/-- `PkgI6.IsCocycle2` is the inhomogeneous cocycle predicate, verbatim. -/
theorem isCocycle2_iff {G : Type*} [Group G] [TopologicalSpace G] (ε : G → G → ZMod 2) :
    IsCocycle2 ε ↔ IsInhCocycle2 ε := Iff.rfl

/-- `PkgI6.IsCoboundary2` is the inhomogeneous coboundary predicate, verbatim. -/
theorem isCoboundary2_iff {G : Type*} [Group G] [TopologicalSpace G] (ε : G → G → ZMod 2) :
    IsCoboundary2 ε ↔ IsInhCoboundary2 ε := Iff.rfl

/-- The class in `H²(G_ℚ, ℤ/2)` (Mathlib's `continuousCohomology 2 (Z2 ℚ)`) of a continuous
`ZMod 2`-valued inhomogeneous 2-cocycle in the sense of `PkgI6.IsCocycle2`. -/
noncomputable abbrev clsQ (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2)
    (hε : IsCocycle2 ε) : continuousCohomology 2 (Z2 ℚ) :=
  cls (isTrivialAction_Z2 ℚ) ε hε

/-- **Localization against restriction of cochains.** `PkgI6.loc F 2` sends the class of `ε` to
the class of `PkgI6.resC F ε`. -/
theorem loc_clsQ (F : Type) [Field F] [Algebra ℚ F]
    (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2) (hε : IsCocycle2 ε) :
    (loc F 2).hom (clsQ ε hε) = cls (isTrivialAction_Z2res F) (resC F ε) (hε.resC F) :=
  map_cls (isTrivialAction_Z2 ℚ) (isTrivialAction_Z2res F)
    (Field.absoluteGaloisGroup.map (algebraMap ℚ F)) (𝟙 _) ε hε

theorem loc_clsQ_eq_zero_iff (F : Type) [Field F] [Algebra ℚ F]
    (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2) (hε : IsCocycle2 ε) :
    (loc F 2).hom (clsQ ε hε) = 0 ↔ IsCoboundary2 (resC F ε) := by
  rw [loc_clsQ]
  exact cls_eq_zero_iff _ _ _

theorem clsQ_eq_zero_iff
    (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2) (hε : IsCocycle2 ε) :
    clsQ ε hε = 0 ↔ IsCoboundary2 ε :=
  cls_eq_zero_iff _ _ _

theorem clsQ_surjective (x : continuousCohomology 2 (Z2 ℚ)) :
    ∃ ε, ∃ hε : IsCocycle2 ε, clsQ ε hε = x :=
  cls_surjective (isTrivialAction_Z2 ℚ) x

/-- **T14(a), bundle form ↔ cochain form.** -/
theorem brauerHasse2_iff : BrauerHasse2 ↔ BrauerHasse2C := by
  constructor
  · intro h ε hε hinf hp
    refine (clsQ_eq_zero_iff ε hε).1 (h (clsQ ε hε) ?_ ?_)
    · exact (loc_clsQ_eq_zero_iff ℝ ε hε).2 hinf
    · intro p _
      exact (loc_clsQ_eq_zero_iff ℚ_[p] ε hε).2 (hp p)
  · intro h x hinf hp
    obtain ⟨ε, hε, rfl⟩ := clsQ_surjective x
    refine (clsQ_eq_zero_iff ε hε).2 (h ε hε ?_ ?_)
    · exact (loc_clsQ_eq_zero_iff ℝ ε hε).1 hinf
    · intro p _
      exact (loc_clsQ_eq_zero_iff ℚ_[p] ε hε).1 (hp p)

open Classical in
/-- The set of primes where a class is locally nonzero is the set of primes where a representing
cocycle is locally not a coboundary. -/
theorem badPrimes_clsQ
    (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2) (hε : IsCocycle2 ε) :
    {p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩; (locP (p : ℕ)).hom (clsQ ε hε) ≠ 0} =
      {p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        ¬ IsCoboundary2 (resC ℚ_[(p : ℕ)] ε)} := by
  ext p
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact not_congr (loc_clsQ_eq_zero_iff ℚ_[(p : ℕ)] ε hε)

/-- **T14(b), bundle form ↔ cochain form.** -/
theorem brauerReciprocity2_iff : BrauerReciprocity2 ↔ BrauerReciprocity2C := by
  constructor
  · intro h ε hε
    obtain ⟨h1, h2⟩ := h (clsQ ε hε)
    rw [badPrimes_clsQ ε hε] at h1 h2
    refine ⟨h1, ?_⟩
    by_cases hb : IsCoboundary2 (resC ℝ ε)
    · rw [ite_eq_left ((loc_clsQ_eq_zero_iff ℝ ε hε).2 hb)] at h2
      rw [ite_eq_left hb]
      exact h2
    · rw [ite_eq_right (fun h' => hb ((loc_clsQ_eq_zero_iff ℝ ε hε).1 h'))] at h2
      rw [ite_eq_right hb]
      exact h2
  · intro h x
    obtain ⟨ε, hε, rfl⟩ := clsQ_surjective x
    obtain ⟨h1, h2⟩ := h ε hε
    rw [badPrimes_clsQ ε hε]
    refine ⟨h1, ?_⟩
    by_cases hb : IsCoboundary2 (resC ℝ ε)
    · rw [ite_eq_left hb] at h2
      rw [ite_eq_left ((loc_clsQ_eq_zero_iff ℝ ε hε).2 hb)]
      exact h2
    · rw [ite_eq_right hb] at h2
      rw [ite_eq_right (fun h' => hb ((loc_clsQ_eq_zero_iff ℝ ε hε).1 h'))]
      exact h2

/-- **Local `H²` has two elements: bundle form ↔ cochain form, at one place.** -/
theorem natCard_Z2res_eq_two_iff (F : Type) [Field F] [Algebra ℚ F] [CharZero F] :
    Nat.card (continuousCohomology 2 (Z2res F)) = 2 ↔
      H2TwoClasses (Field.absoluteGaloisGroup F) :=
  natCard_eq_two_iff (isTrivialAction_Z2res F)

/-- **T15, bundle form ↔ cochain form** (all primes including `2`, and the real place). -/
theorem localH2Card_iff : LocalH2Card ↔ LocalH2CardC := by
  constructor
  · rintro ⟨hp, hinf⟩
    exact ⟨fun p _ => (natCard_Z2res_eq_two_iff ℚ_[p]).1 (hp p),
      (natCard_Z2res_eq_two_iff ℝ).1 hinf⟩
  · rintro ⟨hp, hinf⟩
    exact ⟨fun p _ => (natCard_Z2res_eq_two_iff ℚ_[p]).2 (hp p),
      (natCard_Z2res_eq_two_iff ℝ).2 hinf⟩

/-- T14 (both parts) in bundle form is equivalent to its cochain form. -/
theorem t14_bundle_iff_cochain :
    (BrauerHasse2 ∧ BrauerReciprocity2) ↔ (BrauerHasse2C ∧ BrauerReciprocity2C) :=
  and_congr brauerHasse2_iff brauerReciprocity2_iff

/-- **The Brauer step of B2 on cochains, from the bundle forms.** `PkgI6.cob_of_same_finite_support`
(consumed by the descent glue) with its three cochain hypotheses supplied by the bundle targets
T14a, T14b, T15 through the comparison. -/
theorem cob_of_same_finite_support_of_bundle (hH : BrauerHasse2) (hR : BrauerReciprocity2)
    (hC : LocalH2Card) (ε₁ ε₂ : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2)
    (c₁ : IsCocycle2 ε₁) (c₂ : IsCocycle2 ε₂)
    (h : ∀ (p : ℕ) [Fact p.Prime],
      IsCoboundary2 (resC ℚ_[p] ε₁) ↔ IsCoboundary2 (resC ℚ_[p] ε₂)) :
    IsCoboundary2 (ε₁ - ε₂) :=
  cob_of_same_finite_support (brauerHasse2_iff.1 hH) (brauerReciprocity2_iff.1 hR)
    (localH2Card_iff.1 hC) ε₁ ε₂ c₁ c₂ h

end ZInQ.Contrib.BrauerCohomology
