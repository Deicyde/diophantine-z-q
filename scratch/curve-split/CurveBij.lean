import ZInQKernel.HDecomp.QM.Pairs
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.SmoothFibre.Basic

/-! # curve-split: row H-85 `ModelGlue.CurveBijIso`

`CurveBijIso` is copied verbatim (docstring and `def`) from `scratch/model-glue/ModelGlue6.lean`
(namespace `ModelGlue`, under `open LeafQM.AV`; it uses only `fieldPt` and `Qbar` from
`ZInQKernel/HDecomp/QM/Pairs.lean`).

Split:
* Part A (proved): `CurveBijIso` from its version over an algebraically closed field of
  characteristic 0 (`CurveBijIsoClosed`), by fpqc descent of isomorphisms along
  `Spec ℚ̄ → Spec ℚ` (Mathlib, `descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`,
  Stacks 02L4).
* Part B: `CurveBijIsoClosed` from the published leaf `BijToNormalIsIso` (a bijective morphism of
  irreducible varieties onto a normal variety in characteristic 0 is an isomorphism; Springer,
  Borel) and the reduction from proper smooth curves to integral ones.

No `sorry`, no `axiom`. -/

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace ModelGlue

open LeafQM.AV

/-- **Textbook leaf: a bijection on `ℚ̄`-points between proper smooth curves over `ℚ` is an
isomorphism** (not proved here). A morphism `g : S → Y` over `ℚ` of proper smooth curves (smooth
of relative dimension 1) that induces a bijection `S(ℚ̄) → Y(ℚ̄)` is an isomorphism.
STANDARD (locators UNVERIFIED): `g` is quasi-finite (injective on `ℚ̄`-points; a positive-
dimensional fibre has infinitely many) and proper, hence finite (EGA III 4.4.2 / Hartshorne
III Ex. 11.2); in characteristic 0 it is generically étale, so the number of `ℚ̄`-points of a
general fibre over a component of `Y_ℚ̄` is the degree there (Hartshorne II.6.9, III.10.7), so
each degree is 1 and `g` is finite birational onto the normal `Y`, hence an isomorphism
(Hartshorne I.6.12 / II.6.7). -/
def CurveBijIso : Prop :=
  ∀ (S Y : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ g : S ⟶ Y,
    Function.Bijective (fun s : fieldPt Qbar ⟶ S => s ≫ g) → IsIso g

end ModelGlue

namespace CurveSplit

open LeafQM.AV ModelGlue

/-- `Spec k`. -/
abbrev SpecK (k : Type) [Field k] : Scheme := Spec (CommRingCat.of k)

/-- `Spec k` over itself: morphisms `kPt k ⟶ X` in `Over (Spec k)` are the `k`-points of `X`. -/
abbrev kPt (k : Type) [Field k] : Over (SpecK k) := Over.mk (𝟙 (SpecK k))

/-- **`CurveBijIso` over an algebraically closed field of characteristic `0`** (intermediate
statement). -/
def CurveBijIsoClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (T Z : Over (SpecK k)),
    IsProper T.hom → SmoothOfRelativeDimension 1 T.hom → IsProper Z.hom →
    SmoothOfRelativeDimension 1 Z.hom → ∀ h : T ⟶ Z,
      Function.Bijective (fun t : kPt k ⟶ T => t ≫ h) → IsIso h

/-! ## Part A: descent from `ℚ̄` to `ℚ` -/

section PartA

variable {S Y : Over (Spec (CommRingCat.of ℚ))} (g : S ⟶ Y)

/-- `Spec ℚ̄ → Spec ℚ`. -/
abbrev bQ : SpecK Qbar ⟶ Spec (CommRingCat.of ℚ) := (fieldPt Qbar).hom

/-- The base change `g_ℚ̄ : S_ℚ̄ → Y_ℚ̄`. -/
abbrev bcMap : pullback S.hom bQ ⟶ pullback Y.hom bQ :=
  pullback.map S.hom bQ Y.hom bQ g.left (𝟙 _) (𝟙 _) (by simp [Over.w g]) (by simp)

theorem bcMap_snd : bcMap g ≫ pullback.snd Y.hom bQ = pullback.snd S.hom bQ := by
  simp [bcMap]

theorem bcMap_fst : bcMap g ≫ pullback.fst Y.hom bQ = pullback.fst S.hom bQ ≫ g.left := by
  simp [bcMap]

/-- The square `S_ℚ̄ → Y_ℚ̄ → Y`, `S_ℚ̄ → S → Y` is a pullback. -/
theorem bcMap_isPullback :
    IsPullback (bcMap g) (pullback.fst S.hom bQ) (pullback.fst Y.hom bQ) g.left := by
  refine IsPullback.of_right ?_ (bcMap_fst g) (IsPullback.of_hasPullback Y.hom bQ).flip
  rw [bcMap_snd, Over.w g]
  exact (IsPullback.of_hasPullback S.hom bQ).flip

instance : Subsingleton (Spec (CommRingCat.of ℚ)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum ℚ))

instance : Nonempty (SpecK Qbar) := inferInstanceAs (Nonempty (PrimeSpectrum Qbar))

instance bQ_surjective : Surjective bQ :=
  ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

instance bQ_flat : Flat bQ := by
  show Flat (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  simp only [CommRingCat.hom_ofHom]
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

/-- A `ℚ̄`-point of `W_ℚ̄` gives a `ℚ̄`-point of `W` over `ℚ`. -/
def toS {W : Over (Spec (CommRingCat.of ℚ))} (t : kPt Qbar ⟶ Over.mk (pullback.snd W.hom bQ)) :
    fieldPt Qbar ⟶ W :=
  Over.homMk (show (fieldPt Qbar).left ⟶ W.left from t.left ≫ pullback.fst W.hom bQ) (by
    have h1 : t.left ≫ pullback.snd W.hom bQ = 𝟙 _ := by simpa using Over.w t
    show (t.left ≫ pullback.fst W.hom bQ) ≫ W.hom = bQ
    rw [Category.assoc, pullback.condition, ← Category.assoc, h1, Category.id_comp])

theorem toS_left {W : Over (Spec (CommRingCat.of ℚ))}
    (t : kPt Qbar ⟶ Over.mk (pullback.snd W.hom bQ)) :
    (toS t).left = t.left ≫ pullback.fst W.hom bQ := rfl

theorem sec_snd {W : Over (Spec (CommRingCat.of ℚ))}
    (t : kPt Qbar ⟶ Over.mk (pullback.snd W.hom bQ)) :
    t.left ≫ pullback.snd W.hom bQ = 𝟙 _ := by simpa using Over.w t

/-- The `ℚ̄`-points correspond (compatibly with `g`). -/
theorem bij_bc (hb : Function.Bijective (fun s : fieldPt Qbar ⟶ S => s ≫ g)) :
    Function.Bijective (fun t : kPt Qbar ⟶ Over.mk (pullback.snd S.hom bQ) =>
      t ≫ (Over.homMk (bcMap g) (bcMap_snd g) :
        Over.mk (pullback.snd S.hom bQ) ⟶ Over.mk (pullback.snd Y.hom bQ))) := by
  have hcomp : ∀ t : kPt Qbar ⟶ Over.mk (pullback.snd S.hom bQ),
      toS (t ≫ (Over.homMk (bcMap g) (bcMap_snd g) :
        Over.mk (pullback.snd S.hom bQ) ⟶ Over.mk (pullback.snd Y.hom bQ))) = toS t ≫ g := by
    intro t
    ext1
    change (t.left ≫ bcMap g) ≫ pullback.fst Y.hom bQ = (t.left ≫ pullback.fst S.hom bQ) ≫ g.left
    rw [Category.assoc, bcMap_fst, Category.assoc]
  constructor
  · intro t₁ t₂ he
    have h1 : toS t₁ ≫ g = toS t₂ ≫ g := by
      rw [← hcomp, ← hcomp]
      exact congrArg toS he
    have h2 := congrArg CommaMorphism.left (hb.1 h1)
    change t₁.left ≫ pullback.fst S.hom bQ = t₂.left ≫ pullback.fst S.hom bQ at h2
    ext1
    apply pullback.hom_ext
    · exact h2
    · rw [sec_snd t₁, sec_snd t₂]
  · intro z
    obtain ⟨s, hs⟩ := hb.2 (toS z)
    have hsw : s.left ≫ S.hom = 𝟙 (SpecK Qbar) ≫ bQ := by
      rw [Category.id_comp]; exact Over.w s
    let s' : SpecK Qbar ⟶ S.left := s.left
    let l : SpecK Qbar ⟶ pullback S.hom bQ := pullback.lift s' (𝟙 (SpecK Qbar)) hsw
    have hl1 : l ≫ pullback.fst S.hom bQ = s' := pullback.lift_fst _ _ _
    have hl2 : l ≫ pullback.snd S.hom bQ = 𝟙 _ := pullback.lift_snd _ _ _
    refine ⟨Over.homMk l hl2, ?_⟩
    have h3 := congrArg CommaMorphism.left hs
    change s' ≫ g.left = z.left ≫ pullback.fst Y.hom bQ at h3
    ext1
    change l ≫ bcMap g = z.left
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, ← Category.assoc, hl1]
      exact h3
    · rw [Category.assoc, bcMap_snd, hl2, sec_snd z]; rfl

/-- **Part A (proved): `CurveBijIso` from `CurveBijIsoClosed`.** -/
theorem curveBijIso_of_closed (h : CurveBijIsoClosed) : CurveBijIso := by
  intro S Y hPS hSS hPY hSY g hb
  have hiso : IsIso (Over.homMk (bcMap g) (bcMap_snd g) :
      Over.mk (pullback.snd S.hom bQ) ⟶ Over.mk (pullback.snd Y.hom bQ)) :=
    h Qbar _ _ (by show IsProper (pullback.snd S.hom bQ); infer_instance)
      (by show SmoothOfRelativeDimension 1 (pullback.snd S.hom bQ); infer_instance)
      (by show IsProper (pullback.snd Y.hom bQ); infer_instance)
      (by show SmoothOfRelativeDimension 1 (pullback.snd Y.hom bQ); infer_instance) _ (bij_bc g hb)
  have hiso' : IsIso (bcMap g) := by
    have := (Over.forget _).map_isIso (Over.homMk (bcMap g) (bcMap_snd g) :
      Over.mk (pullback.snd S.hom bQ) ⟶ Over.mk (pullback.snd Y.hom bQ))
    simpa using this
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (pullback.fst Y.hom bQ) := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : IsIso g.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme)
      (bcMap_isPullback g) hQ hiso'
  have : IsIso ((Over.forget _).map g) := this
  exact isIso_of_reflects_iso g (Over.forget _)

end PartA

section Topo

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- In a Jacobson space of dimension `≤ 1`, the closure of a non-closed point is an irreducible
component. -/
theorem closure_mem_irreducibleComponents [JacobsonSpace X] (hdim : topologicalKrullDim X ≤ 1)
    {a : X} (ha : ¬ IsClosed ({a} : Set X)) : closure {a} ∈ irreducibleComponents X := by
  let A : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
  obtain ⟨p, hpA, hpc⟩ := nonempty_inter_closedPoints (Z := closure ({a} : Set X))
    ⟨a, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hpc' : IsClosed ({p} : Set X) := hpc
  let P : TopologicalSpace.IrreducibleCloseds X := ⟨{p}, isIrreducible_singleton, hpc'⟩
  have hPA : P < A := by
    refine lt_of_le_of_ne ?_ ?_
    · show ({p} : Set X) ⊆ closure {a}
      exact Set.singleton_subset_iff.mpr hpA
    · intro h
      have h' : ({p} : Set X) = closure {a} := congrArg (fun Z : TopologicalSpace.IrreducibleCloseds X => (Z : Set X)) h
      apply ha
      have : a ∈ ({p} : Set X) := h' ▸ subset_closure rfl
      rw [Set.mem_singleton_iff.mp this]; exact hpc'
  have hmax : IsMax A := by
    rcases (Order.krullDim_le_one_iff.mp hdim) A with h | h
    · exact absurd (h hPA.le) (not_le_of_gt hPA)
    · exact h
  refine ⟨isIrreducible_singleton.closure, fun s hs hsub => ?_⟩
  let S : TopologicalSpace.IrreducibleCloseds X := ⟨closure s, hs.closure, isClosed_closure⟩
  have hAS : A ≤ S := hsub.trans subset_closure
  have := hmax hAS
  exact subset_closure.trans this

/-- **Bijectivity from closed points.** A continuous closed map `f : X → Y` of Jacobson spaces,
`X` T₀ of dimension `≤ 1` with pairwise disjoint irreducible components, which maps closed points
to closed points, is injective on closed points and hits every closed point, is bijective. -/
theorem bijective_of_closedPoints [JacobsonSpace X] [JacobsonSpace Y] [T0Space X]
    {f : X → Y} (hc : Continuous f) (hcl : IsClosedMap f) (hdim : topologicalKrullDim X ≤ 1)
    (hdisj : ∀ Z₁ ∈ irreducibleComponents X, ∀ Z₂ ∈ irreducibleComponents X,
      (Z₁ ∩ Z₂).Nonempty → Z₁ = Z₂)
    (hcp : ∀ x, IsClosed ({x} : Set X) → IsClosed ({f x} : Set Y))
    (hinj : ∀ x y, IsClosed ({x} : Set X) → IsClosed ({y} : Set X) → f x = f y → x = y)
    (hsurj : ∀ y, IsClosed ({y} : Set Y) → ∃ x, f x = y) :
    Function.Bijective f := by
  -- the image of the closure of a point is the closure of its image
  have himg : ∀ a : X, f '' closure {a} = closure {f a} := by
    intro a
    refine le_antisymm ?_ ?_
    · exact image_closure_subset_closure_image hc |>.trans (by rw [Set.image_singleton])
    · rw [(hcl _ isClosed_closure).closure_subset_iff, Set.singleton_subset_iff]
      exact ⟨a, subset_closure rfl, rfl⟩
  -- a non-closed point has a non-closed image
  have hnc : ∀ a : X, ¬ IsClosed ({a} : Set X) → ¬ IsClosed ({f a} : Set Y) := by
    intro a ha hfa
    obtain ⟨p, hpA, hpc⟩ := nonempty_inter_closedPoints (Z := closure ({a} : Set X))
      ⟨a, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hloc : IsLocallyClosed (closure ({a} : Set X) \ {p}) :=
      (isClosed_closure (s := ({a} : Set X))).isLocallyClosed.inter
        (hpc : IsClosed ({p} : Set X)).isOpen_compl.isLocallyClosed
    have hne : (closure ({a} : Set X) \ {p}).Nonempty := by
      refine ⟨a, subset_closure rfl, fun h => ha ?_⟩
      rw [Set.mem_singleton_iff.mp h]; exact hpc
    obtain ⟨q, ⟨hqA, hqp⟩, hqc⟩ := nonempty_inter_closedPoints hne hloc
    have h1 : f p ∈ closure ({f a} : Set Y) := himg a ▸ ⟨p, hpA, rfl⟩
    have h2 : f q ∈ closure ({f a} : Set Y) := himg a ▸ ⟨q, hqA, rfl⟩
    rw [hfa.closure_eq, Set.mem_singleton_iff] at h1 h2
    exact hqp (hinj q p hqc hpc (h2.trans h1.symm))
  -- a non-closed point is the generic point of its component; generic points are unique
  have hgen : ∀ a b : X, ¬ IsClosed ({a} : Set X) → b ∈ closure {a} →
      ¬ IsClosed ({b} : Set X) → b = a := by
    intro a b ha hb hbc
    have hA := closure_mem_irreducibleComponents hdim ha
    have hB := closure_mem_irreducibleComponents hdim hbc
    have hBA : closure ({b} : Set X) ⊆ closure {a} :=
      (isClosed_closure.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hb)
    have heq : closure ({b} : Set X) = closure {a} := hB.eq_of_subset hA.1 hBA |>.symm ▸ rfl
    exact (inseparable_iff_closure_eq.mpr heq).eq
  constructor
  · intro a b hab
    by_cases ha : IsClosed ({a} : Set X) <;> by_cases hb : IsClosed ({b} : Set X)
    · exact hinj a b ha hb hab
    · exact absurd (hab ▸ hcp a ha) (hnc b hb)
    · exact absurd (hab ▸ hcp b hb) (hnc a ha)
    · -- both are generic points of components
      have hA := closure_mem_irreducibleComponents hdim ha
      have hB := closure_mem_irreducibleComponents hdim hb
      obtain ⟨p, hpA, hpc⟩ := nonempty_inter_closedPoints (Z := closure ({a} : Set X))
        ⟨a, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
      have hfp : f p ∈ f '' closure ({b} : Set X) := by
        rw [himg b, ← hab, ← himg a]; exact ⟨p, hpA, rfl⟩
      obtain ⟨b', hb'B, hfb'⟩ := hfp
      have hb'c : IsClosed ({b'} : Set X) := by
        by_contra hb'c
        have := hgen b b' hb hb'B hb'c
        subst this
        exact hnc a ha (hab ▸ hfb' ▸ hcp p hpc)
      have hpb : b' = p := hinj b' p hb'c hpc hfb'
      have hAB := hdisj _ hA _ hB ⟨p, hpA, hpb ▸ hb'B⟩
      exact (inseparable_iff_closure_eq.mpr hAB).eq
  · intro y
    have hrange : IsClosed (Set.range f) := by
      rw [← Set.image_univ]; exact hcl _ isClosed_univ
    have hall : closedPoints Y ⊆ Set.range f := fun y hy => hsurj y hy
    have : closure (closedPoints Y) ⊆ Set.range f := hrange.closure_subset_iff.mpr hall
    have hcl' : closure (closedPoints Y) = Set.univ := by
      have := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := Y) (S := Set.univ)
        isClosed_univ.isLocallyClosed
      rwa [Set.univ_inter, closure_univ] at this
    exact this (hcl' ▸ Set.mem_univ y)

end Topo

/-! ## Part B: from proper smooth curves to integral varieties -/

/-- **Leaf: a bijective morphism onto a normal variety in characteristic `0` is an isomorphism**
(published). Let `k` be an algebraically closed field of characteristic `0` and `f : X → Y` a
morphism of irreducible varieties over `k` (integral separated schemes of finite type over `k`)
with `Y` normal. If `f` is bijective on `k`-points (= closed points), then `f` is an isomorphism.

Sources (theorem numbers UNVERIFIED, no network): T. A. Springer, *Linear Algebraic Groups*,
2nd ed. (Birkhäuser 1998), Cor. 5.2.8 ("a bijective separable morphism of irreducible varieties
onto a normal variety is an isomorphism"; in characteristic `0` every dominant morphism is
separable); A. Borel, *Linear Algebraic Groups*, 2nd ed., AG.18.2 (Zariski's main theorem, with
the degree of a dominant quasi-finite separable morphism equal to the number of points of a general
fibre, AG.18.4). The display with "separable" dropped because `char k = 0` (a specialization),
`k`, `X`, `Y` in universe `0`, "variety" read as integral, separated, of finite type over `k`,
"normal" as Mathlib-free `IsNormalScheme` (every stalk integrally closed; the stalks of an integral
scheme are domains). -/
def BijToNormalIsIso : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y : Over (SpecK k)),
    IsIntegral X.left → IsIntegral Y.left → IsSeparated X.hom → IsSeparated Y.hom →
    LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom → QuasiCompact X.hom →
    QuasiCompact Y.hom → ZInQ.Contrib.CurvesG.IsNormalScheme Y.left →
    ∀ f : X ⟶ Y, Function.Bijective (fun x : kPt k ⟶ X => x ≫ f) → IsIso f

section Curves

open IsLocalRing

/-- **A Noetherian local ring of Krull dimension 1 with principal maximal ideal is a domain.**
Copied from `scratch/curve-glue/CIproof.lean.part` (`CurveGlueCI.isDomain_of_dim_one`). -/
theorem isDomain_of_dim_one {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (hspan : (maximalIdeal R).spanFinrank = 1) : IsDomain R := by
  classical
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan'⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
  rw [hspan] at hs
  obtain ⟨π, rfl⟩ := Set.encard_eq_one.1 (by exact_mod_cast hs)
  have hπ : ∀ n : ℕ, π ^ n ≠ 0 := by
    intro n hn
    have hsub : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := by
      intro p
      refine le_antisymm (le_maximalIdeal p.2.ne_top) ?_
      rw [← hspan', Ideal.span_le, Set.singleton_subset_iff]
      exact p.2.mem_of_pow_mem n (by rw [hn]; exact p.asIdeal.zero_mem)
    have : Subsingleton (PrimeSpectrum R) :=
      ⟨fun p q => PrimeSpectrum.ext ((hsub p).trans (hsub q).symm)⟩
    have h0 : ringKrullDim R = 0 := Order.krullDim_eq_zero
    rw [hdim] at h0
    norm_num at h0
  have hdec : ∀ a : R, a ≠ 0 → ∃ (n : ℕ) (u : R), IsUnit u ∧ a = π ^ n * u := by
    intro a ha
    have hex : ∃ k : ℕ, a ∉ maximalIdeal R ^ k := by
      by_contra! h
      apply ha
      have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
      rw [← Submodule.mem_bot R, ← this, Submodule.mem_iInf]
      exact h
    let k := Nat.find hex
    have hk : a ∉ maximalIdeal R ^ k := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      apply hk
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hmem : a ∈ maximalIdeal R ^ n := by
      have := Nat.find_min hex (show n < k by omega)
      push Not at this
      exact this
    rw [← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨u, hu⟩ := hmem
    refine ⟨n, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    have hum : u ∈ maximalIdeal R := (mem_maximalIdeal u).2 hu'
    rw [← hspan', Ideal.mem_span_singleton'] at hum
    obtain ⟨w, hw⟩ := hum
    apply hk
    rw [hn, ← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨w, by rw [← hu, ← hw]; ring⟩
  have : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨n, u, hu, rfl⟩ := hdec a hne.1
    obtain ⟨m, v, hv, rfl⟩ := hdec b hne.2
    have : π ^ (n + m) * (u * v) = 0 := by rw [← hab]; ring
    exact hπ (n + m) ((hu.mul hv).mul_left_eq_zero.mp this)
  exact NoZeroDivisors.to_isDomain R

/-- **Two irreducible components meeting at a point with a domain stalk coincide.** Copied from
`scratch/curve-glue/CIproof.lean.part`. -/
theorem irreducibleComponent_eq_of_isDomain_stalk {X : Scheme} {Z₁ Z₂ : Set X}
    (h₁ : Z₁ ∈ irreducibleComponents X) (h₂ : Z₂ ∈ irreducibleComponents X) {y : X}
    (hy₁ : y ∈ Z₁) (hy₂ : y ∈ Z₂) (hdom : IsDomain (X.presheaf.stalk y)) : Z₁ = Z₂ := by
  let G : Set X := Set.range (X.fromSpecStalk y)
  have hG : IsIrreducible G := by
    have : IrreducibleSpace (Spec (X.presheaf.stalk y)) := PrimeSpectrum.irreducibleSpace
    show IsIrreducible (Set.range (X.fromSpecStalk y))
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (X.fromSpecStalk y).continuous.continuousOn
  have key : ∀ Z ∈ irreducibleComponents X, y ∈ Z → Z = closure G := by
    intro Z hZ hyZ
    have hcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hgen := hZ.1.isGenericPoint_genericPoint hcl
    have hspec : hZ.1.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, hgen.def]; exact hyZ
    have hmem : hZ.1.genericPoint ∈ G := by
      show _ ∈ Set.range (X.fromSpecStalk y)
      rw [Scheme.range_fromSpecStalk]; exact hspec
    have hsub : Z ⊆ closure G := by
      rw [← hgen.def]
      exact closure_mono (Set.singleton_subset_iff.2 hmem)
    exact (hZ.eq_of_subset hG.closure hsub)
  rw [key Z₁ h₁ hy₁, key Z₂ h₂ hy₂]

variable {k : Type} [Field k]

/-- The local ring at a closed point of a smooth curve over a field is a discrete valuation ring
(domain, integrally closed). -/
theorem stalk_closed_normal {X : Scheme} (f : X ⟶ SpecK k) [SmoothOfRelativeDimension 1 f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨h1, h2⟩ := ZInQ.Contrib.Dim.ringKrullDim_stalk_of_smoothOfRelativeDimension f 1 x hx
  have hd : IsDomain (X.presheaf.stalk x) :=
    isDomain_of_dim_one (by exact_mod_cast h1) (by exact_mod_cast h2)
  have h3 := ZInQ.Contrib.Dim.finrank_cotangentSpace_of_smoothOfRelativeDimension f 1 x hx
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp h3
  exact ⟨hd, inferInstance⟩

/-- A smooth scheme over a field is reduced. -/
theorem isReduced_of_smooth {X : Scheme} (f : X ⟶ SpecK k) [Smooth f] : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hU : IsAffineOpen (⊤ : (SpecK k).Opens) := isAffineOpen_top _
    have hVU : V ≤ f ⁻¹ᵁ ⊤ := by simp
    have hsm := f.smooth_appLE hU hV hVU
    let _ : Field Γ(SpecK k, ⊤) :=
      (ZInQ.Contrib.Dim.isField_sections_spec k ⊤ Set.univ_nonempty).toField
    let _ : Algebra Γ(SpecK k, ⊤) Γ(X, V) := (f.appLE ⊤ V hVU).hom.toAlgebra
    have : Algebra.Smooth Γ(SpecK k, ⊤) Γ(X, V) := hsm
    have : _root_.IsReduced Γ(X, V) := ZInQ.SmoothFibre.isReduced_of_smooth_of_field Γ(SpecK k, ⊤) _
    let x' : V := ⟨x, hxV⟩
    have hloc := hV.isLocalization_stalk x'
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
    exact isReduced_localizationPreserves (hV.primeIdealOf x').asIdeal.primeCompl
      (X.presheaf.stalk x') ‹_›
  exact isReduced_of_isReduced_stalk X

/-- The irreducible components of a smooth curve over a field are pairwise disjoint. -/
theorem components_disjoint {X : Scheme} (f : X ⟶ SpecK k) [SmoothOfRelativeDimension 1 f] :
    ∀ Z₁ ∈ irreducibleComponents X, ∀ Z₂ ∈ irreducibleComponents X,
      (Z₁ ∩ Z₂).Nonempty → Z₁ = Z₂ := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  intro Z₁ h₁ Z₂ h₂ hne
  have hcl : IsClosed (Z₁ ∩ Z₂) :=
    (isClosed_of_mem_irreducibleComponents Z₁ h₁).inter
      (isClosed_of_mem_irreducibleComponents Z₂ h₂)
  obtain ⟨y, ⟨hy₁, hy₂⟩, hyc⟩ := nonempty_inter_closedPoints hne hcl.isLocallyClosed
  exact irreducibleComponent_eq_of_isDomain_stalk h₁ h₂ hy₁ hy₂
    (stalk_closed_normal f y (mem_closedPoints_iff.mp hyc)).1

/-- The irreducible component of a point of a quasi-compact smooth curve over a field is open. -/
theorem isOpen_irreducibleComponent {X : Scheme} (f : X ⟶ SpecK k)
    [SmoothOfRelativeDimension 1 f] [CompactSpace X] (x : X) :
    IsOpen (irreducibleComponent x) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  have hdisj := components_disjoint f
  set Z := irreducibleComponent x with hZ
  have hZmem := irreducibleComponent_mem_irreducibleComponents x
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have hcompl : Zᶜ = ⋃ Z' ∈ {Z' ∈ irreducibleComponents X | Z' ≠ Z}, Z' := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hz
      refine ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩,
        mem_irreducibleComponent⟩
      intro h
      exact hz (h ▸ mem_irreducibleComponent)
    · rintro ⟨Z', ⟨hZ', hne⟩, hzZ'⟩ hzZ
      exact hne (hdisj Z' hZ' Z hZmem ⟨z, hzZ', hzZ⟩)
  rw [← isClosed_compl_iff, hcompl]
  exact (hfin.subset fun Z' hZ' => hZ'.1).isClosed_biUnion fun Z' hZ' =>
    isClosed_of_mem_irreducibleComponents Z' hZ'.1

/-- A smooth curve over a field has topological dimension `≤ 1`. -/
theorem topDim_le_one {X : Scheme} (f : X ⟶ SpecK k) [SmoothOfRelativeDimension 1 f] :
    topologicalKrullDim X ≤ 1 := by
  rcases isEmpty_or_nonempty X with hE | hN
  · have : IsEmpty (TopologicalSpace.IrreducibleCloseds X) :=
      ⟨fun Z => hE.elim Z.2.nonempty.some⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  · rw [ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1]
    rfl

/-- An integral smooth curve over a field is normal. -/
theorem isNormal_of_integral {X : Scheme} (f : X ⟶ SpecK k) [SmoothOfRelativeDimension 1 f]
    [IsIntegral X] : ZInQ.Contrib.CurvesG.IsNormalScheme X := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  intro x
  by_cases hx : IsClosed ({x} : Set X)
  · exact (stalk_closed_normal f x hx).2
  · have hC := closure_mem_irreducibleComponents (topDim_le_one f) hx
    have huniv : closure ({x} : Set X) = Set.univ :=
      (hC.eq_of_subset (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _)).symm ▸ rfl
    have hgx : IsGenericPoint x Set.univ := huniv
    have : x = genericPoint X := hgx.eq (genericPoint_spec X)
    subst this
    show IsIntegrallyClosed X.functionField
    infer_instance

end Curves


section Assembly

variable {k : Type} [Field k] [IsAlgClosed k]

/-- **Closed points versus `k`-points** (proved, from Mathlib's `pointEquivClosedPoint`). A
morphism bijective on `k`-points maps closed points to closed points, injectively, onto the closed
points. -/
theorem closedPoint_facts {T Z : Over (SpecK k)} [LocallyOfFiniteType T.hom]
    [LocallyOfFiniteType Z.hom] (h : T ⟶ Z)
    (hb : Function.Bijective (fun t : kPt k ⟶ T => t ≫ h)) :
    (∀ x : T.left, IsClosed ({x} : Set T.left) → IsClosed ({h.left x} : Set Z.left)) ∧
    (∀ x y : T.left, IsClosed ({x} : Set T.left) → IsClosed ({y} : Set T.left) →
      h.left x = h.left y → x = y) ∧
    (∀ y : Z.left, IsClosed ({y} : Set Z.left) → ∃ x, h.left x = y) := by
  have hw : h.left ≫ Z.hom = T.hom := Over.w h
  let pt : SpecK k := (IsLocalRing.closedPoint k : PrimeSpectrum k)
  have hc : ∀ (x : T.left) (hx : IsClosed ({x} : Set T.left)),
      (pointOfClosedPoint T.hom x hx ≫ h.left) ≫ Z.hom = 𝟙 _ := by
    intro x hx
    rw [Category.assoc, hw, pointOfClosedPoint_comp]
  have hval : ∀ (x : T.left) (hx : IsClosed ({x} : Set T.left)),
      (pointOfClosedPoint T.hom x hx ≫ h.left) pt = h.left x := by
    intro x hx
    rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  let P : ∀ x : T.left, IsClosed ({x} : Set T.left) → (kPt k ⟶ T) := fun x hx =>
    Over.homMk (pointOfClosedPoint T.hom x hx) (by simp)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have := ((pointEquivClosedPoint Z.hom) ⟨_, hc x hx⟩).2
    change (pointOfClosedPoint T.hom x hx ≫ h.left) pt ∈ closedPoints Z.left at this
    rw [hval x hx] at this
    exact this
  · intro x y hx hy hxy
    have h1 : P x hx ≫ h = P y hy ≫ h := by
      ext1
      exact ext_of_apply_closedPoint_eq Z.hom (hc x hx) (hc y hy)
        ((hval x hx).trans (hxy.trans (hval y hy).symm))
    have h2 := congrArg CommaMorphism.left (hb.1 h1)
    change pointOfClosedPoint T.hom x hx = pointOfClosedPoint T.hom y hy at h2
    have h3 := congrArg (fun g : SpecK k ⟶ T.left => g pt) h2
    simp only [pointOfClosedPoint_apply] at h3
    exact h3
  · intro y hy
    obtain ⟨t, ht⟩ := hb.2 (Over.homMk (pointOfClosedPoint Z.hom y hy) (by simp))
    have h2 := congrArg CommaMorphism.left ht
    change t.left ≫ h.left = pointOfClosedPoint Z.hom y hy at h2
    refine ⟨t.left pt, ?_⟩
    have h3 := congrArg (fun g : SpecK k ⟶ Z.left => g pt) h2
    simp only [Scheme.Hom.comp_apply, pointOfClosedPoint_apply] at h3
    exact h3

omit [IsAlgClosed k] in
/-- `k`-points of the restriction of `h` over an open `W`. -/
theorem bij_restrict {T Z : Over (SpecK k)} (h : T ⟶ Z) (W : Z.left.Opens)
    (hb : Function.Bijective (fun t : kPt k ⟶ T => t ≫ h)) :
    Function.Bijective (fun t : kPt k ⟶ Over.mk ((h.left ⁻¹ᵁ W).ι ≫ T.hom) =>
      t ≫ (Over.homMk (h.left ∣_ W) (by
        simp only [Over.mk_hom, morphismRestrict_ι_assoc, Over.w h]) :
        Over.mk ((h.left ⁻¹ᵁ W).ι ≫ T.hom) ⟶ Over.mk (W.ι ≫ Z.hom))) := by
  set V := h.left ⁻¹ᵁ W
  let up : (kPt k ⟶ Over.mk (V.ι ≫ T.hom)) → (kPt k ⟶ T) := fun t =>
    Over.homMk (show (kPt k).left ⟶ T.left from t.left ≫ V.ι) (by
      have := Over.w t
      simp only [Over.mk_hom] at this ⊢
      rw [Category.assoc, this])
  constructor
  · intro t₁ t₂ he
    have he' := congrArg CommaMorphism.left he
    change t₁.left ≫ (h.left ∣_ W) = t₂.left ≫ (h.left ∣_ W) at he'
    have h1 : up t₁ ≫ h = up t₂ ≫ h := by
      ext1
      change (t₁.left ≫ V.ι) ≫ h.left = (t₂.left ≫ V.ι) ≫ h.left
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, he',
        Category.assoc]
    have h2 := congrArg CommaMorphism.left (hb.1 h1)
    change t₁.left ≫ V.ι = t₂.left ≫ V.ι at h2
    ext1
    exact (cancel_mono V.ι).mp h2
  · intro w
    let z : kPt k ⟶ Z := Over.homMk (show (kPt k).left ⟶ Z.left from w.left ≫ W.ι) (by
      have := Over.w w
      simp only [Over.mk_hom] at this ⊢
      rw [Category.assoc, this])
    obtain ⟨t, ht⟩ := hb.2 z
    have ht' := congrArg CommaMorphism.left ht
    change t.left ≫ h.left = w.left ≫ W.ι at ht'
    have hrange : Set.range t.left ⊆ Set.range V.ι := by
      rintro _ ⟨a, rfl⟩
      rw [Scheme.Opens.range_ι]
      show h.left (t.left a) ∈ W
      rw [← Scheme.Hom.comp_apply, ht', Scheme.Hom.comp_apply]
      exact (w.left a).2
    let t' : (kPt k).left ⟶ V.toScheme := IsOpenImmersion.lift V.ι t.left hrange
    have ht'fac : t' ≫ V.ι = t.left := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk t' (by
      have := Over.w t
      simp only [Over.mk_hom] at this ⊢
      rw [← Category.assoc, ht'fac, this]), ?_⟩
    ext1
    change t' ≫ (h.left ∣_ W) = w.left
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, ht'fac, ht']

variable [CharZero k]

/-- **The restriction of `h` over an irreducible open `W` is an isomorphism** (proved from the
leaf), once `h` is a homeomorphism. -/
theorem restrict_isIso (hL : BijToNormalIsIso) {T Z : Over (SpecK k)} [IsProper T.hom]
    [IsProper Z.hom] [SmoothOfRelativeDimension 1 T.hom] [SmoothOfRelativeDimension 1 Z.hom]
    (h : T ⟶ Z) (hb : Function.Bijective (fun t : kPt k ⟶ T => t ≫ h)) (W : Z.left.Opens)
    (hW : IsIrreducible (W : Set Z.left)) (hhomeo : IsHomeomorph h.left) :
    IsIso (h.left ∣_ W) := by
  set V := h.left ⁻¹ᵁ W with hVdef
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hsmW : SmoothOfRelativeDimension 1 (W.ι ≫ Z.hom) := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := 1) W.ι Z.hom
    rwa [zero_add] at this
  have hsmV : SmoothOfRelativeDimension 1 (V.ι ≫ T.hom) := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := 1) V.ι T.hom
    rwa [zero_add] at this
  have : Smooth (W.ι ≫ Z.hom) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (V.ι ≫ T.hom) := SmoothOfRelativeDimension.smooth 1 _
  -- integrality of `W`
  have : IrreducibleSpace W.toScheme := Subtype.irreducibleSpace hW
  have : IsReduced W.toScheme := isReduced_of_smooth (W.ι ≫ Z.hom)
  have hIW : IsIntegral W.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  -- integrality of `V`
  have hV : IsIrreducible (V : Set T.left) := by
    let e := hhomeo.homeomorph h.left
    have : (V : Set T.left) = e.symm '' (W : Set Z.left) := by
      rw [Homeomorph.image_symm]; rfl
    rw [this]
    exact hW.image _ e.symm.continuous.continuousOn
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hV
  have : IsReduced V.toScheme := isReduced_of_smooth (V.ι ≫ T.hom)
  have hIV : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hN : ZInQ.Contrib.CurvesG.IsNormalScheme W.toScheme := isNormal_of_integral (W.ι ≫ Z.hom)
  have hcomm : (h.left ∣_ W) ≫ (Over.mk (W.ι ≫ Z.hom)).hom = (Over.mk (V.ι ≫ T.hom)).hom := by
    simp only [Over.mk_hom]
    rw [morphismRestrict_ι_assoc, Over.w h]
  let H : Over.mk (V.ι ≫ T.hom) ⟶ Over.mk (W.ι ≫ Z.hom) := Over.homMk (h.left ∣_ W) hcomm
  have hH : IsIso H := hL k (Over.mk (V.ι ≫ T.hom)) (Over.mk (W.ι ≫ Z.hom)) hIV hIW
    (by simp only [Over.mk_hom]; infer_instance) (by simp only [Over.mk_hom]; infer_instance)
    (by simp only [Over.mk_hom]; infer_instance) (by simp only [Over.mk_hom]; infer_instance)
    (by simp only [Over.mk_hom]; infer_instance) (by simp only [Over.mk_hom]; infer_instance)
    hN H (bij_restrict h W hb)
  exact (Over.forget _).map_isIso H

end Assembly

/-- **Part B (proved from the leaf): `CurveBijIsoClosed`.** -/
theorem curveBijIsoClosed_of_leaf (hL : BijToNormalIsIso) : CurveBijIsoClosed := by
  intro k _ _ _ T Z hPT hST hPZ hSZ h hb
  have : Smooth T.hom := SmoothOfRelativeDimension.smooth 1 T.hom
  have : Smooth Z.hom := SmoothOfRelativeDimension.smooth 1 Z.hom
  have : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
  have : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have hw : h.left ≫ Z.hom = T.hom := Over.w h
  have : IsProper h.left := by
    have : IsProper (h.left ≫ Z.hom) := by rw [hw]; infer_instance
    exact IsProper.of_comp h.left Z.hom
  obtain ⟨hcp, hinj, hsurj⟩ := closedPoint_facts h hb
  have hbij : Function.Bijective h.left :=
    bijective_of_closedPoints h.left.continuous h.left.isClosedMap (topDim_le_one T.hom)
      (components_disjoint T.hom) hcp hinj hsurj
  have hhomeo : IsHomeomorph h.left :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨h.left.continuous, h.left.isClosedMap, hbij⟩
  have hiso : IsIso h.left := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (fun z : Z.left =>
        (⟨irreducibleComponent z, isOpen_irreducibleComponent Z.hom z⟩ : Z.left.Opens)) ?_ ?_
    · rw [eq_top_iff]
      intro z _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, mem_irreducibleComponent⟩
    · intro z
      exact restrict_isIso hL h hb _ isIrreducible_irreducibleComponent hhomeo
  have : IsIso ((Over.forget _).map h) := hiso
  exact isIso_of_reflects_iso h (Over.forget _)

/-- **H-85 `CurveBijIso` from the published leaf `BijToNormalIsIso`** (proved). -/
theorem curveBijIso_of_leaf (hL : BijToNormalIsIso) : CurveBijIso :=
  curveBijIso_of_closed (curveBijIsoClosed_of_leaf hL)

end CurveSplit

#print axioms CurveSplit.curveBijIso_of_closed
#print axioms CurveSplit.curveBijIso_of_leaf
