import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.SmoothSourceDescent
import ZInQKernel.HDecomp.Objects

/-!
# smooth-regular: smooth = regular = geometrically regular over a field

Task smooth-regular (2026-11-16). Report: `docs/research/smooth-regular.md`; log: `scratch/smooth-regular/log.md`.

For a scheme `X` locally of finite type over a field `K` (structure map `f : X ⟶ Spec K`):

* `smooth_iff_isRegularLocalRing_stalk` (`K` perfect): `f` is smooth iff every local ring of `X` is regular
  (Stacks 00TV / 00TT; tags UNVERIFIED, no network);
* `smooth_iff_nonsingular` (`K` perfect): iff the local rings at the closed points are regular ("nonsingular");
* `smooth_iff_geometricallyRegular` (any `K`): iff `X_L` is regular for every field extension `L/K`;
* `smooth_iff_nonsingularAfter_algebraicClosure` (any `K`): iff `X_{K̄}` is nonsingular (regular at closed
  points), the classical "nonsingular variety over `K̄`";
* `smooth_tfae_perfect`: over a perfect field, smooth ⇔ regular ⇔ geometrically regular.

The ⇒ directions are the vendored `Smooth.isRegularLocalRing_stalk` (Jacobian-Challenge); the ⇐ direction at a
point is the vendored `Algebra.FormallySmooth.localization_of_isRegularLocalRing` with Mathlib's
`Algebra.FormallySmooth.of_perfectField` for the residue field; closed points suffice because the smooth locus is
open and `X` is a Jacobson space; over a non-perfect `K` the statement over `K̄` descends along the fpqc cover
`Spec K̄ → Spec K` (Mathlib's `MorphismProperty.of_pullback_snd_of_descendsAlong`).

Dictionary for abelian varieties: `abVarOfNonsingular` / `abVarOfNonsingularAfter` package a proper, geometrically
integral group scheme which is nonsingular (over `K`, resp. over `K̄`) as a `PkgI3.AbVar`, and
`exists_abVar_iff_nonsingular` / `exists_abVar_iff_nonsingularAfter` show that an existential over `PkgI3.AbVar`
is equivalent to the same existential over nonsingular complete group varieties.

No `sorry`, no `axiom`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ZInQ.Contrib.SmoothRegular

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over a perfect field, a point with regular local ring is in the smooth locus. -/
theorem mem_smoothLocus_of_isRegularLocalRing {K : Type u} [Field K] [PerfectField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {x : X}
    [IsRegularLocalRing (X.presheaf.stalk x)] : x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen (⊤ : (Spec (.of K)).Opens) := isAffineOpen_top _
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := le_top
  have hft := f.finiteType_appLE hU hV hVU
  algebraize [(f.appLE ⊤ V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ hU V hV hVU hxV]
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : IsRegularLocalRing (Localization.AtPrime q) := by
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
    have := hV.isLocalization_stalk ⟨x, hxV⟩
    exact .of_ringEquiv (IsLocalization.algEquiv q.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime q)).toRingEquiv
  let e : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let : Algebra K Γ(X, V) := ((f.appLE ⊤ V hVU).hom.comp e.toRingHom).toAlgebra
  have : Algebra.FiniteType K Γ(X, V) :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ e.surjective)
  have : Algebra.EssFiniteType K (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    inferInstanceAs (Algebra.EssFiniteType K (Localization.AtPrime q ⧸ _))
  have h : Algebra.FormallySmooth K (Localization.AtPrime q) :=
    Algebra.FormallySmooth.localization_of_isRegularLocalRing (k := K) q
  change Algebra.FormallySmooth Γ(Spec (.of K), ⊤) (Localization.AtPrime q)
  rw [← RingHom.formallySmooth_algebraMap] at h ⊢
  have heq : algebraMap K (Localization.AtPrime q) =
      (algebraMap Γ(Spec (.of K), ⊤) (Localization.AtPrime q)).comp e.toRingHom := by
    rw [IsScalarTower.algebraMap_eq K Γ(X, V), IsScalarTower.algebraMap_eq Γ(Spec (.of K), ⊤)
      Γ(X, V)]
    rfl
  rw [heq] at h
  have := RingHom.FormallySmooth.respectsIso.2 _ e.symm h
  convert this using 1
  refine RingHom.ext fun a ↦ ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]

/-- **Regular ⇒ smooth over a perfect field** (Stacks 00TV, scheme form). -/
theorem smooth_of_isRegularLocalRing_stalk {K : Type u} [Field K] [PerfectField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (h : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) : Smooth f := by
  rw [← f.smoothLocus_eq_top_iff]
  refine top_le_iff.mp fun x _ ↦ ?_
  have := h x
  exact mem_smoothLocus_of_isRegularLocalRing f

/-- **Smooth ⇔ regular over a perfect field** (Stacks 00TV with 00TT; scheme form). -/
theorem smooth_iff_isRegularLocalRing_stalk {K : Type u} [Field K] [PerfectField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    Smooth f ↔ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
  ⟨fun _ x ↦ Smooth.isRegularLocalRing_stalk f x, smooth_of_isRegularLocalRing_stalk f⟩

/-- The structure map `Spec L → Spec K` of a field extension. -/
noncomputable abbrev specMap (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Spec (.of L) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- `X_L := X ×_K L` is **regular** (all its local rings are regular local rings). -/
def RegularAfter {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (L : Type u) [Field L] [Algebra K L] : Prop :=
  ∀ x : ↥(pullback f (specMap K L)), IsRegularLocalRing ((pullback f (specMap K L)).presheaf.stalk x)

/-- `X` is **geometrically regular** over `K`: `X_L` is regular for every field extension `L/K`
(Stacks 038U asks this for finitely generated `L/K`; every `L` here, a priori stronger). -/
def GeometricallyRegular {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L], RegularAfter f L

theorem regularAfter_of_smooth {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [Smooth f] (L : Type u) [Field L] [Algebra K L] : RegularAfter f L := by
  unfold RegularAfter
  intro x
  have : Smooth (pullback.snd f (specMap K L)) := inferInstance
  exact Smooth.isRegularLocalRing_stalk (pullback.snd f (specMap K L)) x

theorem geometricallyRegular_of_smooth {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] : GeometricallyRegular f :=
  fun L _ _ ↦ regularAfter_of_smooth f L

/-- **Regular over an algebraic closure ⇒ smooth**, over any field: `X_{K̄}` is smooth over the
perfect field `K̄` by 00TV, and smoothness descends along the fpqc cover `Spec K̄ → Spec K`. -/
theorem smooth_of_regularAfter_algebraicClosure {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (h : RegularAfter f (AlgebraicClosure K)) : Smooth f := by
  let g := specMap K (AlgebraicClosure K)
  have hsnd : Smooth (pullback.snd f g) := smooth_of_isRegularLocalRing_stalk _ h
  have : Surjective g := ⟨fun _ ↦ ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  have : Flat g := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, inferInstance⟩ hsnd

/-- **Smooth ⇔ geometrically regular**, over any field (Stacks 038V / 00TT; UNVERIFIED tags). -/
theorem smooth_iff_geometricallyRegular {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] : Smooth f ↔ GeometricallyRegular f :=
  ⟨fun _ ↦ geometricallyRegular_of_smooth f,
    fun h ↦ smooth_of_regularAfter_algebraicClosure f (h _)⟩

/-- **Smooth ⇔ regular over `K̄`**, over any field. -/
theorem smooth_iff_regularAfter_algebraicClosure {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    Smooth f ↔ RegularAfter f (AlgebraicClosure K) :=
  ⟨fun _ ↦ regularAfter_of_smooth f _, smooth_of_regularAfter_algebraicClosure f⟩

/-- **Over a perfect field: smooth ⇔ regular ⇔ geometrically regular.** -/
theorem smooth_tfae_perfect {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    List.TFAE [Smooth f, ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x),
      GeometricallyRegular f] := by
  tfae_have 1 ↔ 2 := smooth_iff_isRegularLocalRing_stalk f
  tfae_have 1 ↔ 3 := smooth_iff_geometricallyRegular f
  tfae_finish

/-- `X` is **nonsingular** over `K`: the local ring of `X` at every closed point is regular. -/
def Nonsingular {K : Type u} [Field K] {X : Scheme.{u}} (_f : X ⟶ Spec (.of K)) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → IsRegularLocalRing (X.presheaf.stalk x)

/-- `X_L := X ×_K L` is **nonsingular** (its local rings at closed points are regular). -/
def NonsingularAfter {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (L : Type u) [Field L] [Algebra K L] : Prop :=
  Nonsingular (pullback.snd f (specMap K L))

/-- **Nonsingular ⇒ smooth over a perfect field**: the smooth locus is open, contains every closed
point (00TV), and a nonempty locally closed subset of the Jacobson space `X` has a closed point. -/
theorem smooth_of_nonsingular {K : Type u} [Field K] [PerfectField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (h : Nonsingular f) :
    Smooth f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  rw [← f.smoothLocus_eq_top_iff]
  by_contra hne
  obtain ⟨x, hxZ, hx⟩ := nonempty_inter_closedPoints (Z := (f.smoothLocus : Set X)ᶜ)
    (Set.nonempty_compl.2 fun h ↦ hne (TopologicalSpace.Opens.ext
      (h.trans TopologicalSpace.Opens.coe_top.symm)))
    f.smoothLocus.isOpen.isClosed_compl.isLocallyClosed
  have := h x hx
  exact hxZ (mem_smoothLocus_of_isRegularLocalRing f)

theorem nonsingular_of_smooth {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [Smooth f] : Nonsingular f :=
  fun x _ ↦ Smooth.isRegularLocalRing_stalk f x

/-- **Smooth ⇔ nonsingular over a perfect field.** -/
theorem smooth_iff_nonsingular {K : Type u} [Field K] [PerfectField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] : Smooth f ↔ Nonsingular f :=
  ⟨fun _ ↦ nonsingular_of_smooth f, smooth_of_nonsingular f⟩

theorem nonsingularAfter_of_smooth {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [Smooth f] (L : Type u) [Field L] [Algebra K L] : NonsingularAfter f L :=
  nonsingular_of_smooth _

/-- **`X_{K̄}` nonsingular ⇒ `X` smooth**, over any field. -/
theorem smooth_of_nonsingularAfter_algebraicClosure {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (h : NonsingularAfter f (AlgebraicClosure K)) : Smooth f := by
  let g := specMap K (AlgebraicClosure K)
  have hsnd : Smooth (pullback.snd f g) := smooth_of_nonsingular _ h
  have : Surjective g := ⟨fun _ ↦ ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  have : Flat g := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, inferInstance⟩ hsnd

/-- **Smooth ⇔ `X_{K̄}` nonsingular**, over any field. -/
theorem smooth_iff_nonsingularAfter_algebraicClosure {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    Smooth f ↔ NonsingularAfter f (AlgebraicClosure K) :=
  ⟨fun _ ↦ nonsingularAfter_of_smooth f _, smooth_of_nonsingularAfter_algebraicClosure f⟩

/-! ## Dictionary for abelian varieties -/

/-- The abelian variety (`PkgI3.AbVar`) given by a proper, geometrically integral group scheme over a
perfect field `K` that is nonsingular (Mumford's "complete nonsingular group variety"). Only `X` and
its group law are data; the other fields of `PkgI3.AbVar` are propositions. -/
noncomputable def abVarOfNonsingular {K : Type u} [Field K] [PerfectField K]
    (X : Over (Spec (CommRingCat.of K))) [GrpObj X] [IsProper X.hom] [GeometricallyIntegral X.hom]
    (h : Nonsingular X.hom) : PkgI3.AbVar K :=
  { X := X, smooth := smooth_of_nonsingular X.hom h }

/-- The abelian variety (`PkgI3.AbVar`) given by a proper, geometrically integral group scheme over a
field `K` that is nonsingular over `K̄`. -/
noncomputable def abVarOfNonsingularAfter {K : Type u} [Field K]
    (X : Over (Spec (CommRingCat.of K))) [GrpObj X] [IsProper X.hom] [GeometricallyIntegral X.hom]
    (h : NonsingularAfter X.hom (AlgebraicClosure K)) : PkgI3.AbVar K :=
  { X := X, smooth := smooth_of_nonsingularAfter_algebraicClosure X.hom h }

@[simp] theorem abVarOfNonsingular_X {K : Type u} [Field K] [PerfectField K]
    (X : Over (Spec (CommRingCat.of K))) [GrpObj X] [IsProper X.hom] [GeometricallyIntegral X.hom]
    (h : Nonsingular X.hom) : (abVarOfNonsingular X h).X = X := rfl

@[simp] theorem abVarOfNonsingularAfter_X {K : Type u} [Field K]
    (X : Over (Spec (CommRingCat.of K))) [GrpObj X] [IsProper X.hom] [GeometricallyIntegral X.hom]
    (h : NonsingularAfter X.hom (AlgebraicClosure K)) : (abVarOfNonsingularAfter X h).X = X := rfl

/-- Every abelian variety is its own nonsingular packaging. -/
theorem abVarOfNonsingular_self {K : Type u} [Field K] [PerfectField K] (A : PkgI3.AbVar K) :
    abVarOfNonsingular A.X (nonsingular_of_smooth A.X.hom) = A := by
  cases A; rfl

theorem abVarOfNonsingularAfter_self {K : Type u} [Field K] (A : PkgI3.AbVar K) :
    abVarOfNonsingularAfter A.X (nonsingularAfter_of_smooth A.X.hom _) = A := by
  cases A; rfl

/-- **An existential over abelian variety is an existential over nonsingular complete group
varieties** (perfect field). -/
theorem exists_abVar_iff_nonsingular {K : Type u} [Field K] [PerfectField K]
    (Q : PkgI3.AbVar K → Prop) :
    (∃ A, Q A) ↔ ∃ (X : Over (Spec (CommRingCat.of K))) (_ : GrpObj X) (_ : IsProper X.hom)
      (_ : GeometricallyIntegral X.hom) (h : Nonsingular X.hom), Q (abVarOfNonsingular X h) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A.X, inferInstance, inferInstance, inferInstance, nonsingular_of_smooth A.X.hom,
      (abVarOfNonsingular_self A).symm ▸ hA⟩
  · rintro ⟨X, _, _, _, h, hQ⟩
    exact ⟨_, hQ⟩

/-- Same over any field, with nonsingularity over `K̄`. -/
theorem exists_abVar_iff_nonsingularAfter {K : Type u} [Field K] (Q : PkgI3.AbVar K → Prop) :
    (∃ A, Q A) ↔ ∃ (X : Over (Spec (CommRingCat.of K))) (_ : GrpObj X) (_ : IsProper X.hom)
      (_ : GeometricallyIntegral X.hom) (h : NonsingularAfter X.hom (AlgebraicClosure K)),
      Q (abVarOfNonsingularAfter X h) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A.X, inferInstance, inferInstance, inferInstance, nonsingularAfter_of_smooth A.X.hom _,
      (abVarOfNonsingularAfter_self A).symm ▸ hA⟩
  · rintro ⟨X, _, _, _, h, hQ⟩
    exact ⟨_, hQ⟩

end ZInQ.Contrib.SmoothRegular
