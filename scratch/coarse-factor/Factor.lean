import ZInQKernel.HDecomp.QM.Pairs
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.SmoothFibre.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.FieldTheory.PrimitiveElement

/-! # coarse-factor: `FactorThroughSurj` (descent along a morphism surjective on `ℚ̄`-points)

Proof: the scheme-theoretic image `Z` of `(f, f') : Y → X ×_ℚ X'` maps to `X` by a finite morphism
(Mathlib's Stacks 0AH8 at every closed point) that is bijective on `ℚ̄`-points; `X` is a smooth curve,
so over each irreducible affine open the ring map is an isomorphism (`bijective_of_points`), hence
`Z ≅ X` and `h = (Z ≅ X)⁻¹ ≫ pr₂`.

Copied verbatim from `scratch/curve-split/CurveBij.lean`: sections `Topo` and `Curves`, `isIntegrallyClosed_of_normal`,
`isLocalization_of_cofinal`, `bijective_of_unramifiedAt`, `bijective_of_finrank_eq_one`;
`isDedekindDomain_sections` with the section variables `[IsAlgClosed k] [CharZero k]` dropped (unused).
No `sorry`, no `axiom`. -/

set_option linter.all false

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace CoarseFactorAG

/-- `Spec k`. -/
abbrev SpecK (k : Type) [Field k] : Scheme := Spec (CommRingCat.of k)

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

section PartC

/-- The ring of sections of a normal integral scheme over a nonempty affine open is integrally
closed. -/
theorem isIntegrallyClosed_of_normal {Y : Scheme} [IsIntegral Y]
    (hN : ZInQ.Contrib.CurvesG.IsNormalScheme Y) {V : Y.Opens} (hV : IsAffineOpen V)
    [Nonempty V] : IsIntegrallyClosed Γ(Y, V) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP => ?_
  let y : PrimeSpectrum Γ(Y, V) := ⟨P, hP.isPrime⟩
  have hy : hV.fromSpec y ∈ V := by
    have h := hV.range_fromSpec
    rw [Set.ext_iff] at h
    exact (h _).mp ⟨y, rfl⟩
  let _ := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨hV.fromSpec y, hy⟩
  have hloc : IsLocalization.AtPrime (Y.presheaf.stalk (hV.fromSpec y)) P :=
    hV.isLocalization_stalk' y hy
  have : IsIntegrallyClosed (Y.presheaf.stalk (hV.fromSpec y)) := hN _
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (Y.presheaf.stalk (hV.fromSpec y))
      (Localization.AtPrime P)).toRingEquiv

end PartC

section Ded

variable {k : Type} [Field k]

/-- The sections of a smooth integral curve over a nonempty affine open form a Dedekind domain. -/
theorem isDedekindDomain_sections {W : Scheme} (sW : W ⟶ SpecK k)
    [SmoothOfRelativeDimension 1 sW] [IsIntegral W] {U : W.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : IsDedekindDomain Γ(W, U) := by
  have : Smooth sW := SmoothOfRelativeDimension.smooth 1 sW
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : IsNoetherianRing Γ(W, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsIntegrallyClosed Γ(W, U) := isIntegrallyClosed_of_normal (isNormal_of_integral sW) hU
  have hsmU : SmoothOfRelativeDimension 1 (U.ι ≫ sW) := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := 1) U.ι sW
    rwa [zero_add] at this
  have hdU := topDim_le_one (U.ι ≫ sW)
  have hdim : ringKrullDim Γ(W, U) ≤ 1 := by
    have e1 : topologicalKrullDim (Spec Γ(W, U)) = ringKrullDim Γ(W, U) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    have e2 : topologicalKrullDim U.toScheme = topologicalKrullDim (Spec Γ(W, U)) :=
      IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso hU.isoSpec).isHomeomorph
    rw [← e1, ← e2]
    exact hdU
  have : Ring.KrullDimLE 1 Γ(W, U) := Ring.krullDimLE_iff.mpr (by exact_mod_cast hdim)
  have : Ring.DimensionLEOne Γ(W, U) := ⟨fun hp hpp => hpp.isMaximal_of_ne_bot hp⟩
  exact { }

end Ded

section Pts

variable {K : Type} [Field K] [IsAlgClosed K]

/-- **`K`-points lift along a locally-of-finite-type morphism** through any nonempty closed subset
of the fibre product. -/
theorem exists_lift_of_closed {T S : Scheme.{0}} (t : T ⟶ S) [LocallyOfFiniteType t]
    (a : Spec (CommRingCat.of K) ⟶ S) (F : Set ↥(pullback t a)) (hF : IsClosed F)
    (hne : F.Nonempty) :
    ∃ y : Spec (CommRingCat.of K) ⟶ T, y ≫ t = a ∧
      ∀ u : ↥(Spec (CommRingCat.of K)), y u ∈ (pullback.fst t a) '' F := by
  have : JacobsonSpace ↥(pullback t a) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd t a)
  obtain ⟨q, hqF, hqc⟩ := nonempty_inter_closedPoints hne hF.isLocallyClosed
  have hq : IsClosed ({q} : Set ↥(pullback t a)) := mem_closedPoints_iff.mp hqc
  let s := pointOfClosedPoint (pullback.snd t a) q hq
  refine ⟨s ≫ pullback.fst t a, ?_, fun u => ⟨q, hqF, ?_⟩⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
      Category.id_comp]
  · rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]

/-- `K`-points lift along a surjective locally-of-finite-type morphism. -/
theorem exists_lift_of_surjective {T S : Scheme.{0}} (t : T ⟶ S) [LocallyOfFiniteType t]
    [Surjective t] (a : Spec (CommRingCat.of K) ⟶ S) :
    ∃ y : Spec (CommRingCat.of K) ⟶ T, y ≫ t = a := by
  obtain ⟨q, -⟩ := (pullback.snd t a).surjective
    ((IsLocalRing.closedPoint K : PrimeSpectrum K) : ↥(Spec (CommRingCat.of K)))
  obtain ⟨y, hy, -⟩ := exists_lift_of_closed t a Set.univ isClosed_univ ⟨q, trivial⟩
  exact ⟨y, hy⟩

/-- A `K`-point through a prescribed closed point `y` with `t y = a(pt)`. -/
theorem exists_lift_at {T S : Scheme.{0}} (t : T ⟶ S) [LocallyOfFiniteType t]
    (a : Spec (CommRingCat.of K) ⟶ S) (y : T) (hy : IsClosed ({y} : Set T))
    (u : ↥(Spec (CommRingCat.of K))) (hya : t y = a u) :
    ∃ b : Spec (CommRingCat.of K) ⟶ T, b ≫ t = a ∧ b u = y := by
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := a) y u hya
  obtain ⟨b, hb, hb'⟩ := exists_lift_of_closed t a (pullback.fst t a ⁻¹' {y})
    (hy.preimage (pullback.fst t a).continuous) ⟨q, hq⟩
  obtain ⟨q', hq', hq'y⟩ := hb' u
  exact ⟨b, hb, hq'y.symm.trans hq'⟩

end Pts

section Alg

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]

/-- A maximal ideal of a finitely generated `ℚ`-algebra is the kernel of a map to `Ω`. -/
theorem exists_hom_ker_eq {R : Type*} [CommRing R] [Algebra ℚ R] [Algebra.FiniteType ℚ R]
    (m : Ideal R) [m.IsMaximal] : ∃ φ : R →+* Ω, RingHom.ker φ = m := by
  letI := Ideal.Quotient.field m
  have : Module.Finite ℚ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ m)
  let τ : (R ⧸ m) →ₐ[ℚ] Ω := IsAlgClosed.lift
  refine ⟨τ.toRingHom.comp (Ideal.Quotient.mk m), ?_⟩
  rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp τ.toRingHom.injective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- Extension of a map `A → Ω` with kernel `m` to a map `B → Ω` with kernel a given maximal `M`
over `m` (`B` integral over `A`). -/
theorem exists_extend {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (m : Ideal A) [m.IsMaximal] (M : Ideal B) [M.IsMaximal]
    (hM : M.comap (algebraMap A B) = m) (ψ : A →+* Ω) (hψ : RingHom.ker ψ = m) :
    ∃ φ : B →+* Ω, RingHom.ker φ = M ∧ φ.comp (algebraMap A B) = ψ := by
  have : M.LiesOver m := ⟨hM.symm⟩
  letI := Ideal.Quotient.field m
  letI := Ideal.Quotient.field M
  let σ : A ⧸ m →+* Ω := Ideal.Quotient.lift m ψ (fun a ha => by rw [← RingHom.mem_ker, hψ]; exact ha)
  letI : Algebra (A ⧸ m) Ω := σ.toAlgebra
  have : Algebra.IsIntegral (A ⧸ m) (B ⧸ M) := inferInstance
  let τ : (B ⧸ M) →ₐ[A ⧸ m] Ω := IsAlgClosed.lift
  refine ⟨τ.toRingHom.comp (Ideal.Quotient.mk M), ?_, ?_⟩
  · rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp τ.toRingHom.injective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  · ext a
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    have : Ideal.Quotient.mk M (algebraMap A B a) =
        algebraMap (A ⧸ m) (B ⧸ M) (Ideal.Quotient.mk m a) := rfl
    rw [this, τ.commutes]
    rfl


/-! Copied verbatim from `scratch/curve-split/CurveBij.lean` (Part D). -/

/-- A localization at a smaller cofinal submonoid. -/
theorem isLocalization_of_cofinal {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M N : Submonoid R) (h₁ : M ≤ N) (h₂ : ∀ n ∈ N, ∃ m ∈ M, n ∣ m) [IsLocalization N S] :
    IsLocalization M S := by
  refine ⟨fun m => IsLocalization.map_units S ⟨m.1, h₁ m.2⟩, fun z => ?_, fun {x y} h => ?_⟩
  · obtain ⟨⟨b, n⟩, hz⟩ := IsLocalization.surj N z
    obtain ⟨m, hm, c, hc⟩ := h₂ n.1 n.2
    refine ⟨⟨b * c, ⟨m, hm⟩⟩, ?_⟩
    simp only at hz ⊢
    rw [hc, map_mul, map_mul, ← mul_assoc, hz]
  · obtain ⟨n, hn⟩ := (IsLocalization.eq_iff_exists N S).mp h
    obtain ⟨m, hm, c, hc⟩ := h₂ n.1 n.2
    refine ⟨⟨m, hm⟩, ?_⟩
    simp only
    rw [hc, mul_comm (n : R) c, mul_assoc, mul_assoc, hn]

/-- **A finite flat injective algebra over a domain, unramified at a prime `q` alone over `p` with
trivial residue extension, is an isomorphism.** -/
theorem bijective_of_unramifiedAt {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [Module.Finite A B] [Module.Flat A B]
    (hinj : Function.Injective (algebraMap A B)) (p : Ideal A) [p.IsPrime] (q : Ideal B)
    [q.IsPrime] [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q)]
    (huniq : p.primesOver B = {q}) [Algebra.IsUnramifiedAt A q]
    (hres : Function.Surjective (algebraMap p.ResidueField q.ResidueField)) :
    Function.Bijective (algebraMap A B) := by
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have hinj' := Localization.localRingHom_injective_of_primesOver_eq_singleton huniq
  have hsurj' := Localization.localRingHom_surjective_of_primesOver_eq_singleton huniq hres
  have hbij : Function.Bijective
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [Localization.AtPrime.algebraMap_eq]; exact ⟨hinj', hsurj'⟩
  -- `B_q` is the localization of `B` at `p`
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl)
      (Localization.AtPrime q) := by
    refine isLocalization_of_cofinal _ q.primeCompl ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact fun h => ha ((Ideal.mem_of_liesOver q p a).mpr h)
    · intro n hn
      obtain ⟨r, hr, hdvd⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton huniq n hn
      exact ⟨algebraMap A B r, ⟨r, hr, rfl⟩, hdvd⟩
  have hbc := IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p)
    (IsScalarTower.toAlgHom A B (Localization.AtPrime q)).toLinearMap
  have hrk := Module.rankAtStalk_isBaseChange hbc (IsLocalRing.closedPoint (Localization.AtPrime p))
  have hcomap : (IsLocalRing.closedPoint (Localization.AtPrime p)).comap
      (algebraMap A (Localization.AtPrime p)) = ⟨p, inferInstance⟩ := by
    ext1
    exact Localization.AtPrime.under_maximalIdeal
  rw [hcomap] at hrk
  have e : Localization.AtPrime q ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
    (LinearEquiv.ofBijective (Algebra.linearMap _ _) hbij).symm
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_self] at hrk
  apply Module.algebraMap_bijective_of_rankAtStalk
  ext P
  rw [Pi.one_apply]
  have e1 := Module.rankAtStalk_eq_of_le_of_finite_of_flat' B (bot_le : (⊥ : Ideal A) ≤ P.asIdeal)
  have e2 := Module.rankAtStalk_eq_of_le_of_finite_of_flat' B (bot_le : (⊥ : Ideal A) ≤ p)
  rw [← e1, e2]
  exact hrk.symm.trans (by simp)



/-- An algebra of fields of dimension `1` is bijective. -/
theorem bijective_of_finrank_eq_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h : Module.finrank K L = 1) : Function.Bijective (algebraMap K L) := by
  refine ⟨(algebraMap K L).injective, fun x => ?_⟩
  have htop : (⊤ : IntermediateField K L) = ⊥ := by
    rw [← IntermediateField.finrank_eq_one_iff, IntermediateField.finrank_top', h]
  have hx : x ∈ (⊥ : IntermediateField K L) := htop ▸ IntermediateField.mem_top
  exact IntermediateField.mem_bot.mp hx

/-- **Main algebraic lemma.** `A` a Dedekind domain finitely generated over `ℚ`, `B` a reduced finite
`A`-algebra such that `Spec B → Spec A` is bijective on `Ω`-points. Then `A → B` is an isomorphism. -/
theorem bijective_of_points {A B : Type} [CommRing A] [CommRing B] [IsDedekindDomain A]
    [Algebra ℚ A] [Algebra.FiniteType ℚ A] [Algebra A B] [Module.Finite A B] [IsReduced B]
    (hI : ∀ φ₁ φ₂ : B →+* Ω, φ₁.comp (algebraMap A B) = φ₂.comp (algebraMap A B) → φ₁ = φ₂)
    (hS : ∀ ψ : A →+* Ω, ∃ φ : B →+* Ω, φ.comp (algebraMap A B) = ψ) :
    Function.Bijective (algebraMap A B) := by
  letI : Algebra ℚ B := ((algebraMap A B).comp (algebraMap ℚ A)).toAlgebra
  haveI : IsScalarTower ℚ A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A B := inferInstance
  haveI : Algebra.FiniteType ℚ B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI hJA : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ)
  haveI hJB : IsJacobsonRing B := isJacobsonRing_of_isIntegral (R := A)
  -- uniqueness of the maximal ideal over a maximal ideal
  have huniqM : ∀ M M' : Ideal B, M.IsMaximal → M'.IsMaximal →
      M.comap (algebraMap A B) = M'.comap (algebraMap A B) → M = M' := by
    intro M M' hM hM' e
    have hm : (M.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (Algebra.IsIntegral.isIntegral) M
    obtain ⟨ψ, hψ⟩ := exists_hom_ker_eq (Ω := Ω) (M.comap (algebraMap A B))
    obtain ⟨φ, hφ, hφψ⟩ := exists_extend _ M rfl ψ hψ
    obtain ⟨φ', hφ', hφψ'⟩ := exists_extend _ M' e.symm ψ hψ
    rw [← hφ, ← hφ', hI φ φ' (hφψ.trans hφψ'.symm)]
  -- injectivity
  have hinj : Function.Injective (algebraMap A B) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    have hle : RingHom.ker (algebraMap A B) ≤ (⊥ : Ideal A).jacobson := by
      refine le_sInf fun J ⟨_, hJ⟩ => ?_
      obtain ⟨ψ, hψ⟩ := exists_hom_ker_eq (Ω := Ω) J
      obtain ⟨φ, hφ⟩ := hS ψ
      intro a ha
      rw [← hψ, RingHom.mem_ker, ← hφ, RingHom.comp_apply, (RingHom.mem_ker).mp ha, map_zero]
    rw [hJA.out Ideal.isRadical_bot_of_noZeroDivisors] at hle
    exact le_bot_iff.mp hle
  -- `B` is a domain
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  obtain ⟨Q0, -, hQ0, hQ0u⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (⊥ : Ideal A)
    (⊥ : Ideal B) (by
      rw [Ideal.under, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj])
  have hQ0le : Q0 ≤ (⊥ : Ideal B).jacobson := by
    refine le_sInf fun M ⟨_, hM⟩ => ?_
    have hm : (M.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (Algebra.IsIntegral.isIntegral) M
    obtain ⟨Q', hQ'0, hQ', hQ'u⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      (M.comap (algebraMap A B)) Q0 (by rw [hQ0u]; exact bot_le)
    have hQ'm : Q'.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (Algebra.IsIntegral.isIntegral) Q'
        (by rw [show Q'.comap (algebraMap A B) = Q'.under A from rfl, hQ'u]; exact hm)
    rw [huniqM M Q' hM hQ'm hQ'u.symm]
    exact hQ'0
  rw [hJB.out Ideal.isRadical_bot] at hQ0le
  have hQ0bot : Q0 = ⊥ := le_bot_iff.mp hQ0le
  haveI : (⊥ : Ideal B).IsPrime := hQ0bot ▸ hQ0
  haveI : IsDomain B := IsDomain.of_bot_isPrime B
  have : Module.Flat A B := inferInstance
  have : CharZero A := charZero_of_injective_algebraMap (algebraMap ℚ A).injective
  -- an unramified maximal ideal
  have hO := Algebra.isOpen_unramifiedLocus (R := A) (A := B)
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus A B :=
    Algebra.isUnramifiedAt_bot
  have : JacobsonSpace (PrimeSpectrum B) := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp hJB
  obtain ⟨Q, hQO, hQc⟩ := nonempty_inter_closedPoints ⟨_, hbot⟩ hO.isLocallyClosed
  have hQmax : Q.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal Q).mp hQc
  set q := Q.asIdeal with hqdef
  set p := q.comap (algebraMap A B) with hpdef
  have hpmax : p.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (Algebra.IsIntegral.isIntegral) q
  have : q.LiesOver p := ⟨rfl⟩
  have : Algebra.IsUnramifiedAt A q := hQO
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  have huniq : p.primesOver B = {q} := by
    ext Q'
    constructor
    · rintro ⟨hQ'p, hQ'lo⟩
      have hQ'm : Q'.IsMaximal :=
        Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (Algebra.IsIntegral.isIntegral) Q'
          (by rw [show Q'.comap (algebraMap A B) = Q'.under A from rfl, ← hQ'lo.over]; exact hpmax)
      exact huniqM Q' q hQ'm hQmax (by rw [show Q'.comap (algebraMap A B) = Q'.under A from rfl,
        ← hQ'lo.over])
    · rintro rfl
      exact ⟨inferInstance, inferInstance⟩
  -- `κ(q) = κ(p)`
  have hres : Function.Surjective (algebraMap p.ResidueField q.ResidueField) := by
    obtain ⟨ψ, hψ⟩ := exists_hom_ker_eq (Ω := Ω) p
    let σ : p.ResidueField →+* Ω := Ideal.ResidueField.lift p ψ (by rw [hψ]) (by
      intro s hs
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
      intro h0
      exact hs (hψ ▸ (RingHom.mem_ker).mpr h0))
    letI : Algebra p.ResidueField Ω := σ.toAlgebra
    letI : Algebra ℚ p.ResidueField := ((algebraMap A _).comp (algebraMap ℚ A)).toAlgebra
    haveI : CharZero p.ResidueField :=
      charZero_of_injective_algebraMap (algebraMap ℚ p.ResidueField).injective
    have hcard := AlgHom.card p.ResidueField q.ResidueField Ω
    have hsub : Subsingleton (q.ResidueField →ₐ[p.ResidueField] Ω) := by
      refine ⟨fun τ₁ τ₂ => ?_⟩
      have key : ∀ τ : q.ResidueField →ₐ[p.ResidueField] Ω,
          ((τ : q.ResidueField →+* Ω).comp (algebraMap B q.ResidueField)).comp (algebraMap A B) =
            σ.comp (algebraMap A p.ResidueField) := by
        intro τ
        ext a
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        rw [← IsScalarTower.algebraMap_apply A B q.ResidueField,
          IsScalarTower.algebraMap_apply A p.ResidueField q.ResidueField, τ.commutes]
        rfl
      have h := hI _ _ ((key τ₁).trans (key τ₂).symm)
      exact AlgHom.coe_ringHom_injective (Ideal.ResidueField.ringHom_ext h)
    have h1 : Module.finrank p.ResidueField q.ResidueField = 1 := by
      have hle : Fintype.card (q.ResidueField →ₐ[p.ResidueField] Ω) ≤ 1 :=
        Fintype.card_le_one_iff_subsingleton.mpr hsub
      have hpos := Module.finrank_pos (R := p.ResidueField) (M := q.ResidueField)
      omega
    exact (bijective_of_finrank_eq_one h1).2
  exact bijective_of_unramifiedAt hinj p q huniq hres

end Alg


section Sch

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]

/-- **Affine case.** A finite morphism from a reduced scheme onto an affine integral smooth curve
over `ℚ`, bijective on `Ω`-points, is an isomorphism. -/
theorem isIso_affine {Z U : Scheme.{0}} (q : Z ⟶ U) [IsAffine U] [IsIntegral U]
    (sU : U ⟶ SpecK ℚ) [SmoothOfRelativeDimension 1 sU] [IsReduced Z] [IsFinite q]
    (hI : ∀ a b : Spec (CommRingCat.of Ω) ⟶ Z, a ≫ q = b ≫ q → a = b)
    (hS : ∀ c : Spec (CommRingCat.of Ω) ⟶ U, ∃ a, a ≫ q = c) : IsIso q := by
  haveI : IsAffine Z := isAffine_of_isAffineHom q
  let A := Γ(U, ⊤)
  let B := Γ(Z, ⊤)
  letI : Algebra A B := q.appTop.hom.toAlgebra
  have : Nonempty (⊤ : U.Opens) := by
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    exact ⟨⟨u, trivial⟩⟩
  haveI : IsDedekindDomain A := isDedekindDomain_sections sU (isAffineOpen_top U)
  haveI : Smooth sU := SmoothOfRelativeDimension.smooth 1 sU
  have hft := sU.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top U) (by simp)
  let e : CommRingCat.of ℚ ⟶ Γ(SpecK ℚ, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv
  letI : Algebra ℚ A := ((sU.appLE ⊤ ⊤ (by simp)).hom.comp e.hom).toAlgebra
  haveI : Algebra.FiniteType ℚ A := by
    have : (e.hom).FiniteType := RingHom.FiniteType.of_surjective _
      ((ConcreteCategory.bijective_of_isIso e).2)
    exact RingHom.FiniteType.comp hft this
  haveI : Module.Finite A B := q.finite_app ⊤ (isAffineOpen_top U)
  have hbij := bijective_of_points (Ω := Ω) (A := A) (B := B) ?_ ?_
  · have h1 : IsIso q.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    have : IsIso (Spec.map q.appTop) := inferInstance
    exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (arrowIsoSpecΓOfIsAffine q)).mpr this
  · intro φ₁ φ₂ hφ
    have key : ∀ φ : B →+* Ω, (Spec.map (CommRingCat.ofHom φ) ≫ Z.isoSpec.inv) ≫ q =
        Spec.map (CommRingCat.ofHom (φ.comp (algebraMap A B))) ≫ U.isoSpec.inv := by
      intro φ
      rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp]
      rfl
    have h := hI _ _ ((key φ₁).trans ((congrArg (fun χ : A →+* Ω =>
      Spec.map (CommRingCat.ofHom χ) ≫ U.isoSpec.inv) hφ).trans (key φ₂).symm))
    have h2 := Spec.map_injective (cancel_mono _ |>.mp h)
    exact congrArg CommRingCat.Hom.hom h2
  · intro ψ
    obtain ⟨a, ha⟩ := hS (Spec.map (CommRingCat.ofHom ψ) ≫ U.isoSpec.inv)
    let φ' : B ⟶ CommRingCat.of Ω := Spec.preimage (a ≫ Z.isoSpec.hom)
    refine ⟨φ'.hom, ?_⟩
    have : Spec.map (q.appTop ≫ φ') = Spec.map (CommRingCat.ofHom ψ) := by
      rw [Spec.map_comp, Spec.map_preimage, Category.assoc, Scheme.isoSpec_hom_naturality,
        ← Category.assoc, ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

/-- `Ω`-point injectivity passes to restrictions over opens. -/
theorem restrict_inj {Z W : Scheme.{0}} (p : Z ⟶ W) (V : W.Opens)
    (hI : ∀ a b : Spec (CommRingCat.of Ω) ⟶ Z, a ≫ p = b ≫ p → a = b) :
    ∀ a b : Spec (CommRingCat.of Ω) ⟶ (p ⁻¹ᵁ V).toScheme, a ≫ p ∣_ V = b ≫ p ∣_ V → a = b := by
  intro a b h
  have h' : (a ≫ (p ⁻¹ᵁ V).ι) ≫ p = (b ≫ (p ⁻¹ᵁ V).ι) ≫ p := by
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, h,
      Category.assoc]
  exact (cancel_mono (p ⁻¹ᵁ V).ι).mp (hI _ _ h')

/-- `Ω`-point surjectivity passes to restrictions over opens. -/
theorem restrict_surj {Z W : Scheme.{0}} (p : Z ⟶ W) (V : W.Opens)
    (hS : ∀ c : Spec (CommRingCat.of Ω) ⟶ W, ∃ a, a ≫ p = c) :
    ∀ c : Spec (CommRingCat.of Ω) ⟶ V.toScheme, ∃ a, a ≫ p ∣_ V = c := by
  intro c
  obtain ⟨a, ha⟩ := hS (c ≫ V.ι)
  have hr : Set.range a ⊆ Set.range (p ⁻¹ᵁ V).ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    show p (a u) ∈ V
    rw [← Scheme.Hom.comp_apply, ha, Scheme.Hom.comp_apply]
    exact (c u).2
  let a' := IsOpenImmersion.lift (p ⁻¹ᵁ V).ι a hr
  refine ⟨a', (cancel_mono V.ι).mp ?_⟩
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac, ha]

/-- **Global case.** A finite morphism from a reduced scheme onto a quasi-compact smooth curve over
`ℚ`, bijective on `Ω`-points, is an isomorphism. -/
theorem isIso_of_points {Z W : Scheme.{0}} (p : Z ⟶ W) (sW : W ⟶ SpecK ℚ)
    [SmoothOfRelativeDimension 1 sW] [CompactSpace W] [IsReduced Z] [IsFinite p]
    (hI : ∀ a b : Spec (CommRingCat.of Ω) ⟶ Z, a ≫ p = b ≫ p → a = b)
    (hS : ∀ c : Spec (CommRingCat.of Ω) ⟶ W, ∃ a, a ≫ p = c) : IsIso p := by
  haveI : Smooth sW := SmoothOfRelativeDimension.smooth 1 sW
  haveI : IsReduced W := isReduced_of_smooth sW
  let I := {U : W.affineOpens // ((U : W.Opens) : Set W).Nonempty ∧
    IsIrreducible ((U : W.Opens) : Set W)}
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun U : I => U.1.1) ?_ fun U => ?_
  · rw [eq_top_iff]
    intro w _
    obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVC⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (mem_irreducibleComponent (x := w)) (isOpen_irreducibleComponent sW w)
    have hirr : IsIrreducible (V : Set W) :=
      ⟨⟨w, hwV⟩, isIrreducible_irreducibleComponent.isPreirreducible.open_subset V.2 hVC⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, ⟨w, hwV⟩, hirr⟩, hwV⟩
  · show IsIso (p ∣_ U.1.1)
    set V : W.Opens := U.1.1 with hVdef
    haveI : IsAffine V.toScheme := U.1.2
    haveI : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace U.2.2
    haveI : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    have hsm : SmoothOfRelativeDimension 1 (V.ι ≫ sW) := by
      have := smoothOfRelativeDimension_comp (n := 0) (m := 1) V.ι sW
      rwa [zero_add] at this
    exact isIso_affine (Ω := Ω) (p ∣_ V) (V.ι ≫ sW) (restrict_inj p V hI) (restrict_surj p V hS)

end Sch

end CoarseFactorAG
