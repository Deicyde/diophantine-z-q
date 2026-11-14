import ZInQKernel.OneProof.H.LPrefix
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.SmoothFibre.Basic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-! # coarse-factor: `CoarseFactor` (qm-glue (d)) from the leaf-forms already in use

Part 1 (`namespace CoarseFactorAG`, = `Factor.lean`): `FactorThroughSurj` is a theorem
(`CoarseFactorAG.factorThroughSurj`). Part 2 (`namespace HDec.QMSplit.Moduli`, = `Reduction.lean`):
`CoarseFactor` and `CanonicalCoarseX6` verbatim from `scratch/qm-glue/ModuliCompare.lean`,
`coarseFactor_of : PairsLift → FactorThroughSurj → CoarseFactor`. Part 3: `CoarseFactor` from
`CanonicalCoarseX6` alone and from `R1R2fpRep` alone. No `sorry`, no `axiom`. -/

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

section Main

open HDec.LeafQM.AV

/-- `IsFinite` is local at the target (the instance is not found by type class search, the affine
property being a non-`outParam`). -/
theorem isZariskiLocalAtTarget_isFinite : IsZariskiLocalAtTarget @IsFinite.{0} :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop

/-- Any two morphisms `Spec K ⟶ Spec ℚ` agree. -/
theorem specQ_hom_ext {K : Type} [Field K] (u v : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) :
    u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v]
  congr 1
  ext1
  exact Subsingleton.elim _ _

/-- A scheme morphism `Spec ℚ̄ ⟶ X.left` as a `ℚ̄`-point over `ℚ`. -/
def toPt {X : Over (Spec (CommRingCat.of ℚ))} (c : Spec (CommRingCat.of Qbar) ⟶ X.left) :
    fieldPt Qbar ⟶ X :=
  Over.homMk c (specQ_hom_ext _ _)

/-- The scheme-theoretic image of a reduced scheme is reduced. -/
theorem isReduced_image {Y P : Scheme.{0}} (g : Y ⟶ P) [QuasiCompact g] [IsReduced Y] :
    IsReduced g.image := by
  have : ∀ z : g.image, _root_.IsReduced (g.image.presheaf.stalk z) := by
    intro z
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      P.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.imageι z)) isOpen_univ
    let V : g.image.Opens := g.imageι ⁻¹ᵁ U
    have hV : IsAffineOpen V := hU.preimage g.imageι
    have hred : _root_.IsReduced Γ(g.image, V) :=
      isReduced_of_injective _ (Scheme.Hom.toImage_app_injective g ⟨U, hU⟩)
    let z' : V := ⟨z, hzU⟩
    have hloc := hV.isLocalization_stalk z'
    let _ := TopCat.Presheaf.algebra_section_stalk g.image.presheaf z'
    exact isReduced_localizationPreserves (hV.primeIdealOf z').asIdeal.primeCompl
      (g.image.presheaf.stalk z') hred
  exact isReduced_of_isReduced_stalk _

/-- **GLUE (algebraic geometry of curves over `ℚ`; descent along a surjective morphism).** Let `Y`, `X`,
`X'` be proper smooth curves over `ℚ`, `f : Y → X` surjective on `ℚ̄`-points and `f' : Y → X'` constant on
the `ℚ̄`-fibres of `f`. Then `f' = f ≫ h` for some `h : X → X'`. (In characteristic 0; textbook: the
scheme-theoretic image `Z` of `(f, f') : Y → X × X'` maps finitely and bijectively, with trivial residue
extensions at closed points, onto the normal curve `X`, hence isomorphically; `h = pr₂ ∘ (pr₁|_Z)⁻¹`.) -/
def FactorThroughSurj : Prop :=
  ∀ (Y X X' : Over (Spec (CommRingCat.of ℚ))), IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    IsProper X.hom → SmoothOfRelativeDimension 1 X.hom → IsProper X'.hom →
    SmoothOfRelativeDimension 1 X'.hom → ∀ (f : Y ⟶ X) (f' : Y ⟶ X'),
    (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ f = x) →
    (∀ y y' : fieldPt Qbar ⟶ Y, y ≫ f = y' ≫ f → y ≫ f' = y' ≫ f') →
      ∃ h : X ⟶ X', f ≫ h = f'

/-- **`FactorThroughSurj` is a theorem.** -/
theorem factorThroughSurj : FactorThroughSurj := by
  intro Y X X' hPY hSY hPX hSX hPX' hSX' f f' hsurj hconst
  haveI := hPY; haveI := hSY; haveI := hPX; haveI := hSX; haveI := hPX'; haveI := hSX'
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : IsReduced Y.left := isReduced_of_smooth Y.hom
  let g : Y.left ⟶ pullback X.hom X'.hom :=
    pullback.lift f.left f'.left (by rw [Over.w f, Over.w f'])
  have hgfst : g ≫ pullback.fst X.hom X'.hom = f.left := pullback.lift_fst _ _ _
  have hgsnd : g ≫ pullback.snd X.hom X'.hom = f'.left := pullback.lift_snd _ _ _
  haveI : IsProper (g ≫ pullback.fst X.hom X'.hom) := by
    rw [hgfst]
    have : IsProper (f.left ≫ X.hom) := by rw [Over.w f]; infer_instance
    exact IsProper.of_comp f.left X.hom
  haveI : IsProper g := IsProper.of_comp g (pullback.fst X.hom X'.hom)
  let Z := g.image
  let t : Y.left ⟶ Z := g.toImage
  let ι : Z ⟶ pullback X.hom X'.hom := g.imageι
  have htι : t ≫ ι = g := g.toImage_imageι
  let p : Z ⟶ X.left := ι ≫ pullback.fst X.hom X'.hom
  have htp : t ≫ p = f.left := by
    show t ≫ ι ≫ _ = _
    rw [← Category.assoc, htι, hgfst]
  haveI : IsReduced Z := isReduced_image g
  haveI : IsProper p := by
    show IsProper (ι ≫ pullback.fst X.hom X'.hom)
    infer_instance
  haveI : LocallyOfFiniteType (p ≫ X.hom) := inferInstance
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace (p ≫ X.hom)
  haveI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  -- `t` is surjective and locally of finite type
  haveI : LocallyOfFiniteType t := by
    have : t ≫ (p ≫ X.hom) = Y.hom := by
      rw [← Category.assoc, htp, Over.w f]
    have : LocallyOfFiniteType (t ≫ (p ≫ X.hom)) := by rw [this]; infer_instance
    exact locallyOfFiniteType_of_comp t (p ≫ X.hom)
  haveI : Surjective t := by
    have : IsProper t := by
      have : t ≫ (p ≫ X.hom) = Y.hom := by
        rw [← Category.assoc, htp, Over.w f]
      have : IsProper (t ≫ (p ≫ X.hom)) := by rw [this]; infer_instance
      exact IsProper.of_comp t (p ≫ X.hom)
    refine ⟨fun z => ?_⟩
    have hd : DenseRange t := t.denseRange
    have hc : IsClosed (Set.range t) := t.isClosedMap.isClosed_range
    have : z ∈ Set.range t := by rw [← hc.closure_eq, hd.closure_range]; trivial
    exact this
  -- `ℚ̄`-points
  have hI : ∀ a b : Spec (CommRingCat.of Qbar) ⟶ Z, a ≫ p = b ≫ p → a = b := by
    intro a b hab
    obtain ⟨ya, hya⟩ := exists_lift_of_surjective t a
    obtain ⟨yb, hyb⟩ := exists_lift_of_surjective t b
    have hf : toPt (X := Y) ya ≫ f = toPt (X := Y) yb ≫ f := by
      ext1
      show ya ≫ f.left = yb ≫ f.left
      rw [← htp, ← Category.assoc, hya, hab, ← hyb, Category.assoc]
    have hf' := congrArg CommaMorphism.left (hconst _ _ hf)
    change ya ≫ f'.left = yb ≫ f'.left at hf'
    apply (cancel_mono ι).mp
    apply pullback.hom_ext
    · show a ≫ p = b ≫ p
      exact hab
    · rw [← hya, ← hyb]
      simp only [Category.assoc, reassoc_of% htι, hgsnd, hf']
  have hS : ∀ c : Spec (CommRingCat.of Qbar) ⟶ X.left, ∃ a, a ≫ p = c := by
    intro c
    obtain ⟨y, hy⟩ := hsurj (toPt c)
    refine ⟨y.left ≫ t, (Category.assoc _ _ _).trans ?_⟩
    rw [htp]
    exact congrArg CommaMorphism.left hy
  -- closed fibres are single points
  have hpt : ∀ z₁ z₂ : Z, IsClosed ({z₁} : Set Z) → IsClosed ({z₂} : Set Z) → p z₁ = p z₂ →
      z₁ = z₂ := by
    intro z₁ z₂ h₁ h₂ e
    let u : ↥(Spec (CommRingCat.of Qbar)) :=
      ((IsLocalRing.closedPoint Qbar : PrimeSpectrum Qbar) : ↥(Spec (CommRingCat.of Qbar)))
    obtain ⟨a₁, -, ha₁⟩ := exists_lift_at (p ≫ X.hom) (fieldPt Qbar).hom z₁ h₁ u
      (Subsingleton.elim _ _)
    obtain ⟨a₂, ha₂p, ha₂⟩ := exists_lift_at p (a₁ ≫ p) z₂ h₂ u
      (by
        have h1 : (a₁ ≫ p) u = p z₁ := by rw [Scheme.Hom.comp_apply, ha₁]
        exact (h1.trans e).symm)
    rw [← ha₁, ← ha₂, hI a₂ a₁ ha₂p]
  have hfib : ∀ s : X.left, IsClosed ({s} : Set X.left) → (p ⁻¹' {s}).Subsingleton := by
    intro s hs
    have hF : IsClosed (p ⁻¹' {s}) := hs.preimage p.continuous
    have hsub : (p ⁻¹' {s} ∩ closedPoints Z).Subsingleton := by
      rintro z₁ ⟨hz₁, hc₁⟩ z₂ ⟨hz₂, hc₂⟩
      exact hpt z₁ z₂ hc₁ hc₂ (hz₁.trans hz₂.symm)
    rw [← closure_inter_closedPoints hF]
    rcases hsub.eq_empty_or_singleton with h | ⟨z, hz⟩
    · rw [h, closure_empty]; exact Set.subsingleton_empty
    · rw [hz]
      have hzc : z ∈ closedPoints Z := (hz ▸ Set.mem_singleton z).2
      rw [(mem_closedPoints_iff.mp hzc).closure_eq]
      exact Set.subsingleton_singleton
  -- `p` is finite
  haveI : IsFinite p := by
    have hloc : ∀ s : closedPoints X.left, ∃ U : X.left.Opens, s.1 ∈ U ∧ IsFinite (p ∣_ U) := by
      intro s
      have H : (g '' ((g ≫ pullback.fst X.hom X'.hom) ⁻¹' {s.1})).Finite := by
        refine ((hfib s.1 (mem_closedPoints_iff.mp s.2)).image ι).finite.subset ?_
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨t y, ?_, ?_⟩
        · show p (t y) = s.1
          rw [← Scheme.Hom.comp_apply, htp, ← hgfst]; exact hy
        · rw [← Scheme.Hom.comp_apply, htι]
      exact exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage g
        (pullback.fst X.hom X'.hom) s.1 H
    choose U hU hfin using hloc
    haveI := isZariskiLocalAtTarget_isFinite
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite) U ?_ hfin
    rw [eq_top_iff]
    intro x _
    haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
    obtain ⟨s, hs, hsc⟩ := nonempty_inter_closedPoints ⟨x, subset_closure (Set.mem_singleton x)⟩
      isClosed_closure.isLocallyClosed
    have hxs : x ⤳ s := specializes_iff_mem_closure.mpr hs
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨s, hsc⟩, hxs.mem_open (U ⟨s, hsc⟩).2 (hU ⟨s, hsc⟩)⟩
  have hiso : IsIso p := isIso_of_points (Ω := Qbar) p X.hom hI hS
  refine ⟨Over.homMk (inv p ≫ ι ≫ pullback.snd X.hom X'.hom) ?_, ?_⟩
  · show (inv p ≫ ι ≫ pullback.snd X.hom X'.hom) ≫ X'.hom = X.hom
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc ι,
      show ι ≫ pullback.fst X.hom X'.hom = p from rfl, IsIso.inv_hom_id_assoc]
  · ext1
    show f.left ≫ inv p ≫ ι ≫ pullback.snd X.hom X'.hom = f'.left
    rw [← htp, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, htι, hgsnd]

end Main

end CoarseFactorAG


set_option autoImplicit false

noncomputable section

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **GLUE (descent of the forgetful map; project).** Two coarse witnesses `(X, Ψ, fY)`, `(X', Ψ', fY')` over
the same fine witness `(Y, Φ)` are related by a morphism `h : X → X'` compatible with the moduli bijections
on `ℚ̄`-points. What it needs: `fY` is finite and surjective (on `ℚ̄`-points every QM pair has a level-3
structure, `A[3] ≅ 𝒪/3𝒪` as `𝒪`-modules), `X` is a normal curve, and `fY'` is constant on the fibres of `fY`
(both are the forgetful map on `ℚ̄`-points); in characteristic 0 a morphism constant on the fibres of a finite
surjective morphism onto a normal variety factors through it (`X` is the quotient of `Y` by the deck group:
SGA 1, Exp. V, Prop. 1.8 and Cor. 1.5; Mumford, *Abelian varieties*, §7, Thm; Stacks, the universal property
of a geometric quotient by a finite group; locators UNVERIFIED). Algebraic geometry of curves, not done here. -/
def CoarseFactor : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X X' : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (Ψ' : (fieldPt Qbar ⟶ X') ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (fY' : Y ⟶ X'),
    R1fpProps Y Φ → X6Props Y Φ X Ψ fY → X6Props Y Φ X' Ψ' fY' →
      ∃ h : X ⟶ X', ∀ x : fieldPt Qbar ⟶ X, Ψ' (x ≫ h) = Ψ x

/-- **LEAF-form (the canonical model `Y₃` and its coarse quotient `X₆ = Y₃/G`).** Some fine witness carries
a coarse witness with the forgetful map onto `X₆(ℚ̄)`, and `X₆` geometrically connected. Published: Shimura,
Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971), Thm 4.21 and §2
(`π₀(X₆ ⊗ ℚ̄) = ℤ̂^×/nrd(𝒪̂^×) = 1`); the quotient of a projective curve by a finite group (SGA 1, Exp. V,
Prop. 1.8); locators UNVERIFIED; the audit's "qualified consequence" caveat of `CanonicalModelY3` applies. -/
def CanonicalCoarseX6 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x) ∧
      LeafAdopt.R1pi0Props X

/-! ## The smaller Props -/

/-- **Every QM pair over `ℚ̄` carries a level-3 structure, up to isomorphism** (step: surjectivity of the
forgetful map `Y₃(ℚ̄) → X₆(ℚ̄)`). Published content: for an abelian surface over an algebraically closed field
of characteristic 0 with QM by the maximal order `𝒪`, `A[3]` is free of rank one over `𝒪/3𝒪` (over `ℂ`,
`H₁(A, ℤ)` is a projective, hence free, left `𝒪`-module of rank one); a generator `v` gives `η(a) = a v`.
Not used as a leaf here: it is *derived* (`pairsLift_of_canonical`, `pairsLift_of_rep`) from the leaf-forms
already in use (`CanonicalCoarseX6`, `R1R2fpRep`), whose forgetful map is surjective on `ℚ̄`-points. -/
def PairsLift : Prop :=
  ∀ Q : QMPair Qbar, ∃ P : QML3 Qbar, Quotient.mk (pairSetoid Qbar) P.forget = Quotient.mk _ Q

/-- **GLUE (algebraic geometry of curves over `ℚ`; descent along a surjective morphism).** Let `Y`, `X`,
`X'` be proper smooth curves over `ℚ`, `f : Y → X` surjective on `ℚ̄`-points and `f' : Y → X'` constant on
the `ℚ̄`-fibres of `f`. Then `f' = f ≫ h` for some `h : X → X'`. (In characteristic 0; textbook: the
scheme-theoretic image `Z` of `(f, f') : Y → X × X'` maps finitely and bijectively, with trivial residue
extensions at closed points, onto the normal curve `X`, hence isomorphically; `h = pr₂ ∘ (pr₁|_Z)⁻¹`.) -/
def FactorThroughSurj : Prop :=
  ∀ (Y X X' : Over (Spec (CommRingCat.of ℚ))), IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    IsProper X.hom → SmoothOfRelativeDimension 1 X.hom → IsProper X'.hom →
    SmoothOfRelativeDimension 1 X'.hom → ∀ (f : Y ⟶ X) (f' : Y ⟶ X'),
    (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ f = x) →
    (∀ y y' : fieldPt Qbar ⟶ Y, y ≫ f = y' ≫ f → y ≫ f' = y' ≫ f') →
      ∃ h : X ⟶ X', f ≫ h = f'

/-! ## Proofs -/

/-- `PairsLift` from any coarse witness whose forgetful map is onto `X(ℚ̄)`. -/
theorem pairsLift_of_witness {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} (h6 : X6Props Y Φ X Ψ fY)
    (hs : ∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x) : PairsLift := by
  intro Q
  obtain ⟨y, hy⟩ := hs (Ψ.symm (Quotient.mk _ Q))
  obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ Qbar y)
  refine ⟨P, ?_⟩
  rw [← h6.2.2.2.2.2 y P hP.symm, hy, Equiv.apply_symm_apply]

theorem pairsLift_of_canonical (h : CanonicalCoarseX6) : PairsLift := by
  obtain ⟨Y, Φ, X, Ψ, fY, -, h6, hs, -⟩ := h
  exact pairsLift_of_witness h6 hs

theorem pairsLift_of_rep (h : LeafAdopt.R1R2fpRep) : PairsLift := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, h6, -, -, hs, -, -⟩ := h
  exact pairsLift_of_witness h6 hs.2

/-- **`CoarseFactor` from `PairsLift` and `FactorThroughSurj`.** -/
theorem coarseFactor_of (hL : PairsLift) (hF : FactorThroughSurj) : CoarseFactor := by
  intro Y Φ X X' Ψ Ψ' fY fY' h1 h6 h6'
  have hval : ∀ y : fieldPt Qbar ⟶ Y, Ψ (y ≫ fY) = Ψ' (y ≫ fY') := by
    intro y
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ Qbar y)
    rw [h6.2.2.2.2.2 y P hP.symm, h6'.2.2.2.2.2 y P hP.symm]
  have hsurj : ∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x := by
    intro x
    obtain ⟨Q, hQ⟩ := Quotient.exists_rep (Ψ x)
    obtain ⟨P, hP⟩ := hL Q
    obtain ⟨y, hy⟩ := h1.2.2.2.2.2 |> fun _ => (Φ Qbar).surjective (M3.mk P)
    refine ⟨y, Ψ.injective ?_⟩
    rw [h6.2.2.2.2.2 y P hy, hP, hQ]
  have hconst : ∀ y y' : fieldPt Qbar ⟶ Y, y ≫ fY = y' ≫ fY → y ≫ fY' = y' ≫ fY' := by
    intro y y' e
    apply Ψ'.injective
    rw [← hval, ← hval, e]
  obtain ⟨h, hh⟩ := hF Y X X' h1.1 h1.2.1 h6.1 h6.2.1 h6'.1 h6'.2.1 fY fY' hsurj hconst
  refine ⟨h, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := hsurj x
  rw [Category.assoc, hh, hval]

/-- `CoarseFactor` from the leaf-form `CanonicalCoarseX6` (already a hypothesis of qm-glue's
`r1r2fpRep_of_canonical`) and the AG glue. -/
theorem coarseFactor_of_canonical (hC : CanonicalCoarseX6) (hF : FactorThroughSurj) : CoarseFactor :=
  coarseFactor_of (pairsLift_of_canonical hC) hF

/-- `CoarseFactor` from the bundle leaf `R1R2fpRep` (the hypothesis of qm-glue's
`x6ConicModel_of_canonical'`) and the AG glue. -/
theorem coarseFactor_of_rep (hR : LeafAdopt.R1R2fpRep) (hF : FactorThroughSurj) : CoarseFactor :=
  coarseFactor_of (pairsLift_of_rep hR) hF

end HDec.QMSplit.Moduli


namespace HDec.QMSplit.Moduli

/-- `FactorThroughSurj` here is the same statement as in Part 1. -/
theorem factorThroughSurj_proof : FactorThroughSurj := by
  intro Y X X' a b c d e f₁ f f' h1 h2
  exact CoarseFactorAG.factorThroughSurj Y X X' a b c d e f₁ f f' h1 h2

/-- **`CoarseFactor` from the leaf-form `CanonicalCoarseX6`** (a hypothesis of qm-glue's
`r1r2fpRep_of_canonical`, which can therefore drop `hF : CoarseFactor`). -/
theorem coarseFactor_of_canonical' (hC : CanonicalCoarseX6) : CoarseFactor :=
  coarseFactor_of_canonical hC factorThroughSurj_proof

/-- **`CoarseFactor` from the bundle leaf `R1R2fpRep`** (the hypothesis `hR` of qm-glue's
`x6ConicModel_of_canonical'`, which can therefore drop `hF : CoarseFactor`). -/
theorem coarseFactor_of_rep' (hR : LeafAdopt.R1R2fpRep) : CoarseFactor :=
  coarseFactor_of_rep hR factorThroughSurj_proof

end HDec.QMSplit.Moduli


/-! ## Part 4: curve-split's `CurveBijIso` (verbatim from `scratch/curve-split/CurveBij.lean`, with
`open LeafQM.AV` read as `open HDec.LeafQM.AV`) and qm-glue's `CoarseCompare`, `coarseCompare_of` (verbatim) -/

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace ModelGlue

open HDec.LeafQM.AV

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

open HDec.LeafQM.AV ModelGlue

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

/-! ## Part B': the leaf `BijToNormalIsIso` replaced by two classical theorems -/

/-- **Leaf: Zariski's Main Theorem, original form** (published). A birational morphism `f : X → Y`
of varieties over an algebraically closed field `k` with finite fibres, `Y` normal, is an open
immersion. Sources (numbers UNVERIFIED): D. Mumford, *The Red Book of Varieties and Schemes*,
Ch. III §9, "Zariski's Main Theorem (original form)"; EGA III₁ 4.4.9; Hartshorne III.11.4 and
V.5.2 for related forms. "Variety": integral, separated, of finite type over `k`; "birational":
dominant with `f^* : K(Y) → K(X)` bijective (Tau Ceti's `Scheme.Hom.functionFieldMap`); "finite
fibres": every set-theoretic fibre is finite. -/
def ZMTOriginal : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X Y : Over (SpecK k)) [IsIntegral X.left]
    [IsIntegral Y.left], IsSeparated X.hom → IsSeparated Y.hom → LocallyOfFiniteType X.hom →
    LocallyOfFiniteType Y.hom → QuasiCompact X.hom → QuasiCompact Y.hom →
    ZInQ.Contrib.CurvesG.IsNormalScheme Y.left → ∀ (f : X ⟶ Y) [IsDominant f.left],
      Function.Bijective f.left.functionFieldMap → (∀ y : Y.left, (f.left ⁻¹' {y}).Finite) →
      IsOpenImmersion f.left

/-- **Leaf: the degree is the number of points of a general fibre** (published). Let `k` be an
algebraically closed field of characteristic `0` and `f : X → Y` a dominant morphism of varieties
over `k` with `dim X = dim Y`. Then there is a nonempty open `U ⊆ Y` such that every closed point
`y ∈ U` has exactly `[K(X) : K(Y)]` closed points in its fibre. Sources (numbers UNVERIFIED):
J. E. Humphreys, *Linear Algebraic Groups*, §4.6 (`|φ⁻¹(y)| = [K(X):K(Y)]_s` on a dense open for
a dominant morphism of irreducible varieties of the same dimension); I. R. Shafarevich, *Basic
Algebraic Geometry 1*, Ch. II §6.3 (degree of a finite map and the number of preimages);
A. Borel, *Linear Algebraic Groups*, AG.18.4. In characteristic `0` the separable degree is the
degree (a specialization). -/
def DegreeGeneralFibre : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y : Over (SpecK k)) [IsIntegral X.left]
    [IsIntegral Y.left], IsSeparated X.hom → IsSeparated Y.hom → LocallyOfFiniteType X.hom →
    LocallyOfFiniteType Y.hom → QuasiCompact X.hom → QuasiCompact Y.hom →
    ∀ (f : X ⟶ Y) [IsDominant f.left], topologicalKrullDim X.left = topologicalKrullDim Y.left →
      letI := f.left.functionFieldMap.hom.toAlgebra
      ∃ U : Y.left.Opens, (U : Set Y.left).Nonempty ∧ ∀ y ∈ U, IsClosed ({y} : Set Y.left) →
        Nat.card {x : X.left // f.left x = y ∧ IsClosed ({x} : Set X.left)} =
          Module.finrank Y.left.functionField X.left.functionField

/-- An algebra of fields of dimension `1` is bijective. -/
theorem bijective_of_finrank_eq_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h : Module.finrank K L = 1) : Function.Bijective (algebraMap K L) := by
  refine ⟨(algebraMap K L).injective, fun x => ?_⟩
  have htop : (⊤ : IntermediateField K L) = ⊥ := by
    rw [← IntermediateField.finrank_eq_one_iff, IntermediateField.finrank_top', h]
  have hx : x ∈ (⊥ : IntermediateField K L) := htop ▸ IntermediateField.mem_top
  exact IntermediateField.mem_bot.mp hx

section Assembly2

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-- **The restriction of `h` over an irreducible open `W` is an isomorphism** (proved from
`ZMTOriginal` and `DegreeGeneralFibre`), once `h` is a homeomorphism. -/
theorem restrict_isIso' (hZ : ZMTOriginal) (hD : DegreeGeneralFibre) {T Z : Over (SpecK k)}
    [IsProper T.hom] [IsProper Z.hom] [SmoothOfRelativeDimension 1 T.hom]
    [SmoothOfRelativeDimension 1 Z.hom] (h : T ⟶ Z) (W : Z.left.Opens)
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
  have : JacobsonSpace W.toScheme := LocallyOfFiniteType.jacobsonSpace (W.ι ≫ Z.hom)
  have : IrreducibleSpace W.toScheme := Subtype.irreducibleSpace hW
  have : IsReduced W.toScheme := isReduced_of_smooth (W.ι ≫ Z.hom)
  have hIW : IsIntegral W.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
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
  -- the restriction is bijective on points
  set f := h.left ∣_ W with hfdef
  have hfapp : ∀ x : V.toScheme, (f x).1 = h.left x.1 := fun x =>
    morphismRestrict_base_coe h.left W x
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hhomeo.injective
    rw [← hfapp, ← hfapp, hab]
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hhomeo.surjective y.1
    have hxV : x ∈ V := by
      show h.left x ∈ W
      rw [hx]; exact y.2
    refine ⟨(⟨x, hxV⟩ : V.toScheme), Subtype.ext ?_⟩
    exact (hfapp _).trans hx
  have : IsDominant f := ⟨hsurj.denseRange⟩
  -- dimensions
  have hWne : Nonempty W.toScheme := ⟨⟨_, hW.nonempty.some_mem⟩⟩
  have hVne : Nonempty V.toScheme := ⟨(hsurj (Classical.arbitrary _)).choose⟩
  have hdW := ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension (W.ι ≫ Z.hom) 1
  have hdV := ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension (V.ι ≫ T.hom) 1
  have hcomm : f ≫ (Over.mk (W.ι ≫ Z.hom)).hom = (Over.mk (V.ι ≫ T.hom)).hom := by
    simp only [Over.mk_hom, hfdef]
    rw [morphismRestrict_ι_assoc, Over.w h]
  let H : Over.mk (V.ι ≫ T.hom) ⟶ Over.mk (W.ι ≫ Z.hom) := Over.homMk f hcomm
  have : IsDominant H.left := ‹IsDominant f›
  have : IsIntegral (Over.mk (V.ι ≫ T.hom)).left := hIV
  have : IsIntegral (Over.mk (W.ι ≫ Z.hom)).left := hIW
  -- the degree is `1`
  have hsep1 : IsSeparated (Over.mk (V.ι ≫ T.hom)).hom := by simp only [Over.mk_hom]; infer_instance
  have hsep2 : IsSeparated (Over.mk (W.ι ≫ Z.hom)).hom := by simp only [Over.mk_hom]; infer_instance
  have hft1 : LocallyOfFiniteType (Over.mk (V.ι ≫ T.hom)).hom := by
    simp only [Over.mk_hom]; infer_instance
  have hft2 : LocallyOfFiniteType (Over.mk (W.ι ≫ Z.hom)).hom := by
    simp only [Over.mk_hom]; infer_instance
  have hqc1 : QuasiCompact (Over.mk (V.ι ≫ T.hom)).hom := by simp only [Over.mk_hom]; infer_instance
  have hqc2 : QuasiCompact (Over.mk (W.ι ≫ Z.hom)).hom := by simp only [Over.mk_hom]; infer_instance
  obtain ⟨U, hUne, hU⟩ := hD k (Over.mk (V.ι ≫ T.hom)) (Over.mk (W.ι ≫ Z.hom)) hsep1 hsep2 hft1
    hft2 hqc1 hqc2 H (by simp only [Over.mk_left]; rw [hdV, hdW])
  have : JacobsonSpace (Over.mk (W.ι ≫ Z.hom)).left := ‹JacobsonSpace W.toScheme›
  obtain ⟨y, hyU, hyc⟩ := nonempty_inter_closedPoints hUne U.isOpen.isLocallyClosed
  have hyc' : IsClosed ({y} : Set W.toScheme) := hyc
  have hcard := hU y hyU hyc'
  obtain ⟨x0, hx0⟩ := hsurj y
  have hx0c : IsClosed ({x0} : Set V.toScheme) := by
    have : (f ⁻¹' {y}) = {x0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx => hinj (hx.trans hx0.symm), fun hx => hx ▸ hx0⟩
    rw [← this]
    exact hyc'.preimage f.continuous
  have h1 : Nat.card {x : V.toScheme // H.left x = y ∧ IsClosed ({x} : Set V.toScheme)} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨x0, hx0, hx0c⟩, fun ⟨x, hx, _⟩ => ?_⟩
    exact Subtype.ext (hinj (hx.trans hx0.symm))
  let _ := H.left.functionFieldMap.hom.toAlgebra
  have hfr : Module.finrank (Over.mk (W.ι ≫ Z.hom)).left.functionField
      (Over.mk (V.ι ≫ T.hom)).left.functionField = 1 := hcard.symm.trans h1
  have hbij : Function.Bijective H.left.functionFieldMap :=
    bijective_of_finrank_eq_one hfr
  have hfin : ∀ y : W.toScheme, (H.left ⁻¹' {y}).Finite := fun y =>
    Set.Subsingleton.finite fun a ha b hb => hinj (ha.trans hb.symm)
  have hoi : IsOpenImmersion H.left :=
    hZ k (Over.mk (V.ι ≫ T.hom)) (Over.mk (W.ι ≫ Z.hom)) hsep1 hsep2 hft1 hft2 hqc1 hqc2 hN H
      hbij hfin
  have : IsOpenImmersion f := hoi
  exact (isIso_iff_isOpenImmersion_and_surjective f).mpr ⟨this, ⟨hsurj⟩⟩

end Assembly2

/-- **Part B' (proved from ZMT and the degree formula): `CurveBijIsoClosed`.** -/
theorem curveBijIsoClosed_of_zmt (hZ : ZMTOriginal) (hD : DegreeGeneralFibre) :
    CurveBijIsoClosed := by
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
      exact restrict_isIso' hZ hD h _ isIrreducible_irreducibleComponent hhomeo
  have : IsIso ((Over.forget _).map h) := hiso
  exact isIso_of_reflects_iso h (Over.forget _)

/-- **H-85 `CurveBijIso` from Zariski's Main Theorem (original form) and the degree formula**
(proved). -/
theorem curveBijIso_of_zmt (hZ : ZMTOriginal) (hD : DegreeGeneralFibre) : CurveBijIso :=
  curveBijIso_of_closed (curveBijIsoClosed_of_zmt hZ hD)

/-! ## Part C: `ZMTOriginal` proved from Mathlib's Zariski Main Theorem (Stacks 03GW)

For a birational quasi-finite separated morphism of finite type `f : X → Y` with `Y` normal: the
relative normalization `Y'` of `Y` in `X` is `Y` itself (the integral closure of a normal
`Γ(Y, V)` in `Γ(X, f⁻¹V) ⊆ K(X) = K(Y)` is `Γ(Y, V)`), and Mathlib's
`Scheme.Hom.exists_isIso_morphismRestrict_toNormalization` makes `X → Y'` an open immersion on
the quasi-finite locus, which is all of `X`. -/

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

/-- **The integral closure of `Γ(Y, V)` in `Γ(X, f⁻¹V)` is `Γ(Y, V)`** for a birational
morphism of integral schemes with `Y` normal. -/
theorem algebraMap_integralClosure_bijective {X Y : Scheme} (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] [IsDominant f] (hN : ZInQ.Contrib.CurvesG.IsNormalScheme Y)
    (hφ : Function.Bijective f.functionFieldMap) {V : Y.Opens} (hV : IsAffineOpen V)
    [Nonempty V] :
    letI := (f.app V).hom.toAlgebra
    Function.Bijective (algebraMap Γ(Y, V) (integralClosure Γ(Y, V) Γ(X, f ⁻¹ᵁ V))) := by
  letI := (f.app V).hom.toAlgebra
  have key := f.germToFunctionField_functionFieldMap V
  have key' : ∀ a : Γ(Y, V), f.functionFieldMap (Y.germToFunctionField V a) =
      X.germToFunctionField (f ⁻¹ᵁ V) (f.app V a) := fun a =>
    congrArg (fun g => g.hom a) key
  have hgY := Scheme.germToFunctionField_injective Y V
  have hgX := Scheme.germToFunctionField_injective X (f ⁻¹ᵁ V)
  constructor
  · intro a b hab
    have h1 : f.app V a = f.app V b := congrArg Subtype.val hab
    apply hgY
    apply hφ.1
    rw [key', key', h1]
  · rintro ⟨s, hs⟩
    obtain ⟨a, ha⟩ := hφ.2 (X.germToFunctionField (f ⁻¹ᵁ V) s)
    have : IsIntegrallyClosed Γ(Y, V) := isIntegrallyClosed_of_normal hN hV
    have := functionField_isFractionRing_of_isAffineOpen Y V hV
    have hai : IsIntegral Γ(Y, V) a := by
      obtain ⟨p, hpm, hp⟩ := hs
      refine ⟨p, hpm, ?_⟩
      apply hφ.1
      rw [map_zero]
      have h2 : (f.functionFieldMap.hom).comp (algebraMap Γ(Y, V) Y.functionField) =
          (X.germToFunctionField (f ⁻¹ᵁ V)).hom.comp (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) := by
        ext c
        exact key' c
      have ha' : f.functionFieldMap.hom a = (X.germToFunctionField (f ⁻¹ᵁ V)).hom s := ha
      change f.functionFieldMap.hom (Polynomial.eval₂ (algebraMap Γ(Y, V) Y.functionField) a p) = 0
      rw [Polynomial.hom_eval₂, h2, ha', ← Polynomial.hom_eval₂]
      change X.germToFunctionField (f ⁻¹ᵁ V) (Polynomial.eval₂ _ s p) = 0
      rw [show Polynomial.eval₂ (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) s p = 0 from hp, map_zero]
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hai
    refine ⟨b, Subtype.ext ?_⟩
    show f.app V b = s
    apply hgX
    rw [← key']
    change f.functionFieldMap (algebraMap Γ(Y, V) Y.functionField b) = _
    rw [hb, ha]

/-- **The relative normalization of a normal target along a birational morphism is the target**
(proved). -/
theorem isIso_fromNormalization {X Y : Scheme} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [QuasiCompact f] [QuasiSeparated f]
    (hN : ZInQ.Contrib.CurvesG.IsNormalScheme Y) (hφ : Function.Bijective f.functionFieldMap) :
    IsIso f.fromNormalization := by
  have hall : ∀ (V : Y.Opens) (hV : IsAffineOpen V), (V : Set Y).Nonempty →
      IsIso (f.fromNormalization.app V) := by
    intro V hV hne
    have : Nonempty V := ⟨⟨hne.some, hne.some_mem⟩⟩
    rw [f.fromNormalization_app hV]
    have hb := algebraMap_integralClosure_bijective f hN hφ hV
    have : IsIso (CommRingCat.ofHom (letI := (f.app V).hom.toAlgebra;
        algebraMap Γ(Y, V) (integralClosure Γ(Y, V) Γ(X, f ⁻¹ᵁ V)))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hb
    infer_instance
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun V : {V : Y.affineOpens // ((V : Y.Opens) : Set Y).Nonempty} => V.1.1) ?_ fun V => ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, ⟨y, hyW⟩⟩, hyW⟩
  · have hVa : IsAffine V.1.1.toScheme := V.1.2
    show IsIso (f.fromNormalization ∣_ V.1.1)
    have hA : IsAffine (f.fromNormalization ⁻¹ᵁ V.1.1).toScheme := V.1.2.preimage f.fromNormalization
    have hV' : IsAffineOpen (V.1.1.ι ''ᵁ ⊤) := by
      rw [Scheme.Opens.ι_image_top]; exact V.1.2
    have hne : ((V.1.1.ι ''ᵁ ⊤ : Y.Opens) : Set Y).Nonempty := by
      rw [Scheme.Opens.ι_image_top]; exact V.2
    have h1 := hall _ hV' hne
    have happ : IsIso (f.fromNormalization ∣_ V.1.1).appTop := by
      rw [morphismRestrict_appTop]
      exact IsIso.comp_isIso' h1 (Functor.map_isIso _ _)
    exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (arrowIsoSpecΓOfIsAffine (f.fromNormalization ∣_ V.1.1))).mpr
      (inferInstanceAs (IsIso (Spec.map _)))

/-- **`ZMTOriginal`, proved** (from Mathlib's `Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`,
Stacks 03GW, and `isIso_fromNormalization`). -/
theorem zmtOriginal : ZMTOriginal := by
  intro k _ _ X Y _ _ hsX hsY hfX hfY hqX hqY hN f _ hφ hfin
  have hw : f.left ≫ Y.hom = X.hom := Over.w f
  have : IsSeparated (f.left ≫ Y.hom) := by rw [hw]; exact hsX
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [hw]; exact hfX
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [hw]; exact hqX
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  have hlqf : LocallyQuasiFinite f.left :=
    locallyQuasiFinite_iff_finite_preimage_singleton.mpr hfin
  obtain ⟨U, hUiso, hUpre⟩ := f.left.exists_isIso_morphismRestrict_toNormalization
  have htop : f.left.toNormalization ⁻¹ᵁ U = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    show x ∈ (f.left.toNormalization ⁻¹ᵁ U).1
    rw [hUpre]
    exact f.left.quasiFiniteAt x
  have hoi : IsOpenImmersion f.left.toNormalization := by
    have h1 : (f.left.toNormalization ∣_ U) ≫ U.ι =
        (f.left.toNormalization ⁻¹ᵁ U).ι ≫ f.left.toNormalization := morphismRestrict_ι _ _
    have h2 : IsIso (f.left.toNormalization ⁻¹ᵁ U).ι := by
      rw [htop]
      exact (X.left.topIso.isIso_hom)
    have h3 : IsOpenImmersion ((f.left.toNormalization ⁻¹ᵁ U).ι ≫ f.left.toNormalization) := by
      rw [← h1]; infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion _ _).mp h3
  have := isIso_fromNormalization f.left hN hφ
  rw [← f.left.toNormalization_fromNormalization]
  infer_instance

/-- **H-85 `CurveBijIso` from the degree formula alone** (ZMT proved). -/
theorem curveBijIso_of_degree (hD : DegreeGeneralFibre) : CurveBijIso :=
  curveBijIso_of_zmt zmtOriginal hD

end PartC

/-! ## Part D: `CurveBijIso` with no leaf

The restriction `V → W` of `h` over a component is finite and a homeomorphism. On a nonempty affine
open `U ⊆ W`, `A = Γ(W, U)` is a Dedekind domain and `B = Γ(V, f⁻¹U)` a finite torsion-free (hence
flat) `A`-algebra; the unramified locus of `B/A` is open and contains the generic point
(characteristic 0, Mathlib `Algebra.isUnramifiedAt_bot`), so it contains a maximal ideal `q`; `q` is
the only prime over `p = q ∩ A` (bijectivity on points) and `κ(q) = κ(p)` (Nullstellensatz), so
`A_p ≅ B_q`, the rank of `B` over `A` is `1`, and `A ≅ B`. -/

section PartD

open IsLocalRing

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


variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

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

/-- **A finite morphism of integral curves over `k`, bijective on points, onto a smooth curve, is
bijective on sections over nonempty affine opens** (proved). -/
theorem app_bijective_of_finite_bijective {V W : Scheme} (sV : V ⟶ SpecK k) (sW : W ⟶ SpecK k)
    [SmoothOfRelativeDimension 1 sW] [IsIntegral V] [IsIntegral W] (f : V ⟶ W)
    (hf : f ≫ sW = sV) [IsFinite f] (hbij : Function.Bijective f) (U : W.Opens)
    (hU : IsAffineOpen U) (hne : (U : Set W).Nonempty) : Function.Bijective (f.app U) := by
  have : Smooth sW := SmoothOfRelativeDimension.smooth 1 sW
  have : IsDominant f := ⟨hbij.2.denseRange⟩
  have : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  have hUf : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let A := Γ(W, U)
  let B := Γ(V, f ⁻¹ᵁ U)
  letI : Algebra A B := (f.app U).hom.toAlgebra
  -- finite
  have hfin : Module.Finite A B := by
    have h1 := f.isIntegral_app U hU
    have h2 := f.finiteType_appLE hU hUf le_rfl
    rw [Scheme.Hom.appLE_eq_app] at h2
    exact RingHom.IsIntegral.to_finite h1 h2
  -- injective
  have hinj : Function.Injective (algebraMap A B) := by
    intro a b hab
    have key := f.germToFunctionField_functionFieldMap U
    have key' : ∀ c : A, f.functionFieldMap (W.germToFunctionField U c) =
        V.germToFunctionField (f ⁻¹ᵁ U) (f.app U c) := fun c => congrArg (fun g => g.hom c) key
    have hab' : f.app U a = f.app U b := hab
    apply Scheme.germToFunctionField_injective W U
    apply f.functionFieldMap.hom.injective
    change f.functionFieldMap (W.germToFunctionField U a) =
      f.functionFieldMap (W.germToFunctionField U b)
    rw [key', key', hab']
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have : IsDedekindDomain A := isDedekindDomain_sections sW hU
  have : Module.Flat A B := inferInstance
  have : CharZero A := charZero_of_injective_ringHom
    ((sW.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).injective
  -- an unramified maximal ideal
  have hO := Algebra.isOpen_unramifiedLocus (R := A) (A := B)
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus A B :=
    Algebra.isUnramifiedAt_bot
  let _ : Field Γ(SpecK k, ⊤) :=
    (ZInQ.Contrib.Dim.isField_sections_spec k ⊤ Set.univ_nonempty).toField
  have hJA : IsJacobsonRing A := (sW.finiteType_appLE (isAffineOpen_top _) hU (by simp)).isJacobsonRing
  have hJB : IsJacobsonRing B := isJacobsonRing_of_isIntegral (R := A)
  have : JacobsonSpace (PrimeSpectrum B) := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp hJB
  obtain ⟨Q, hQO, hQc⟩ := nonempty_inter_closedPoints ⟨_, hbot⟩ hO.isLocallyClosed
  have hQmax : Q.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal Q).mp hQc
  set q := Q.asIdeal with hqdef
  set p := q.comap (algebraMap A B) with hpdef
  have : q.LiesOver p := ⟨rfl⟩
  have : Algebra.IsUnramifiedAt A q := hQO
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  -- `q` is the only prime over `p`
  have hpt : ∀ P : Spec Γ(V, f ⁻¹ᵁ U), f (hUf.fromSpec P) =
      hU.fromSpec (Spec.map (f.app U) P) := by
    intro P
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec f hU hUf le_rfl
    rw [Scheme.Hom.appLE_eq_app] at h1
    rw [← Scheme.Hom.comp_apply, ← h1, Scheme.Hom.comp_apply]
  have huniq : p.primesOver B = {q} := by
    ext Q'
    constructor
    · rintro ⟨hQ'p, hQ'lo⟩
      let P' : Spec Γ(V, f ⁻¹ᵁ U) := (⟨Q', hQ'p⟩ : PrimeSpectrum B)
      let P0 : Spec Γ(V, f ⁻¹ᵁ U) := Q
      have hcomap : Spec.map (f.app U) P' = Spec.map (f.app U) P0 := by
        rw [Spec.map_apply, Spec.map_apply]
        exact PrimeSpectrum.ext hQ'lo.over.symm
      have h1 : hUf.fromSpec P' = hUf.fromSpec P0 :=
        hbij.1 (by rw [hpt, hpt, hcomap])
      have h2 := hUf.fromSpec.isOpenEmbedding.injective h1
      exact congrArg PrimeSpectrum.asIdeal h2
    · rintro rfl
      exact ⟨inferInstance, inferInstance⟩
  -- `κ(q) = κ(p)` (Nullstellensatz)
  have hres : Function.Surjective (algebraMap p.ResidueField q.ResidueField) := by
    have : IsAlgClosed Γ(SpecK k, ⊤) := IsAlgClosed.of_ringEquiv k _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    let g0 : Γ(SpecK k, ⊤) →+* A := (sW.appLE ⊤ U (by simp)).hom
    have hg0 : g0.FiniteType := sW.finiteType_appLE (isAffineOpen_top _) hU (by simp)
    let c : Γ(SpecK k, ⊤) →+* q.ResidueField :=
      (algebraMap B q.ResidueField).comp ((algebraMap A B).comp g0)
    have hcft : c.FiniteType := by
      refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.comp ?_ hg0)
      · exact RingHom.FiniteType.of_surjective _ (Ideal.algebraMap_residueField_surjective q)
      · exact (RingHom.Finite.finiteType (f := algebraMap A B) hfin)
    letI := c.toAlgebra
    have : Algebra.FiniteType Γ(SpecK k, ⊤) q.ResidueField := hcft
    have hcfin : Module.Finite Γ(SpecK k, ⊤) q.ResidueField :=
      finite_of_finite_type_of_isJacobsonRing _ _
    have hcint : c.IsIntegral := RingHom.Finite.to_isIntegral hcfin
    have hcbij := IsAlgClosed.ringHom_bijective_of_isIntegral c hcint
    intro z
    obtain ⟨t, rfl⟩ := hcbij.2 z
    refine ⟨algebraMap A p.ResidueField (g0 t), ?_⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B q.ResidueField]
    rfl
  exact bijective_of_unramifiedAt hinj p q huniq hres

/-- **A finite morphism of integral curves over `k`, bijective on points, onto a smooth curve, is an
isomorphism** (proved). -/
theorem isIso_of_finite_bijective {V W : Scheme} (sV : V ⟶ SpecK k) (sW : W ⟶ SpecK k)
    [SmoothOfRelativeDimension 1 sW] [IsIntegral V] [IsIntegral W] (f : V ⟶ W)
    (hf : f ≫ sW = sV) [IsFinite f] (hbij : Function.Bijective f) : IsIso f := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun U : {U : W.affineOpens // ((U : W.Opens) : Set W).Nonempty} => U.1.1) ?_ fun U => ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, ⟨y, hyU⟩⟩, hyU⟩
  · have hVa : IsAffine U.1.1.toScheme := U.1.2
    show IsIso (f ∣_ U.1.1)
    have hA : IsAffine (f ⁻¹ᵁ U.1.1).toScheme := U.1.2.preimage f
    have hV' : IsAffineOpen (U.1.1.ι ''ᵁ ⊤) := by
      rw [Scheme.Opens.ι_image_top]; exact U.1.2
    have hne : ((U.1.1.ι ''ᵁ ⊤ : W.Opens) : Set W).Nonempty := by
      rw [Scheme.Opens.ι_image_top]; exact U.2
    have h1 : IsIso (f.app (U.1.1.ι ''ᵁ ⊤)) := (ConcreteCategory.isIso_iff_bijective _).mpr
      (app_bijective_of_finite_bijective sV sW f hf hbij _ hV' hne)
    have happ : IsIso (f ∣_ U.1.1).appTop := by
      rw [morphismRestrict_appTop]
      exact IsIso.comp_isIso' h1 (Functor.map_isIso _ _)
    exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (arrowIsoSpecΓOfIsAffine (f ∣_ U.1.1))).mpr (inferInstanceAs (IsIso (Spec.map _)))

/-- **The restriction of `h` over an irreducible open `W` is an isomorphism** (proved, no leaf),
once `h` is a homeomorphism. -/
theorem restrict_isIso_noleaf {T Z : Over (SpecK k)} [IsProper T.hom] [IsProper Z.hom]
    [SmoothOfRelativeDimension 1 T.hom] [SmoothOfRelativeDimension 1 Z.hom] (h : T ⟶ Z)
    (W : Z.left.Opens) (hW : IsIrreducible (W : Set Z.left)) (hhomeo : IsHomeomorph h.left) :
    IsIso (h.left ∣_ W) := by
  set V := h.left ⁻¹ᵁ W with hVdef
  have hw : h.left ≫ Z.hom = T.hom := Over.w h
  have : IsProper h.left := by
    have : IsProper (h.left ≫ Z.hom) := by rw [hw]; infer_instance
    exact IsProper.of_comp h.left Z.hom
  have hsmW : SmoothOfRelativeDimension 1 (W.ι ≫ Z.hom) := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := 1) W.ι Z.hom
    rwa [zero_add] at this
  have hsmV : SmoothOfRelativeDimension 1 (V.ι ≫ T.hom) := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := 1) V.ι T.hom
    rwa [zero_add] at this
  have : Smooth (W.ι ≫ Z.hom) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (V.ι ≫ T.hom) := SmoothOfRelativeDimension.smooth 1 _
  have : IrreducibleSpace W.toScheme := Subtype.irreducibleSpace hW
  have : IsReduced W.toScheme := isReduced_of_smooth (W.ι ≫ Z.hom)
  have hIW : IsIntegral W.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hV : IsIrreducible (V : Set T.left) := by
    let e := hhomeo.homeomorph h.left
    have : (V : Set T.left) = e.symm '' (W : Set Z.left) := by
      rw [Homeomorph.image_symm]; rfl
    rw [this]
    exact hW.image _ e.symm.continuous.continuousOn
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hV
  have : IsReduced V.toScheme := isReduced_of_smooth (V.ι ≫ T.hom)
  have hIV : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  set f := h.left ∣_ W with hfdef
  have hfapp : ∀ x : V.toScheme, (f x).1 = h.left x.1 := fun x =>
    morphismRestrict_base_coe h.left W x
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hhomeo.injective
    rw [← hfapp, ← hfapp, hab]
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hhomeo.surjective y.1
    have hxV : x ∈ V := by
      show h.left x ∈ W
      rw [hx]; exact y.2
    refine ⟨(⟨x, hxV⟩ : V.toScheme), Subtype.ext ?_⟩
    exact (hfapp _).trans hx
  have : LocallyOfFiniteType f := inferInstance
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_injective hinj
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  have hcomm : f ≫ (W.ι ≫ Z.hom) = V.ι ≫ T.hom := by
    rw [hfdef, morphismRestrict_ι_assoc, Over.w h]
  exact isIso_of_finite_bijective (V.ι ≫ T.hom) (W.ι ≫ Z.hom) f hcomm ⟨hinj, hsurj⟩

/-- **`CurveBijIsoClosed`, proved with no leaf.** -/
theorem curveBijIsoClosed_proved : CurveBijIsoClosed := by
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
      exact restrict_isIso_noleaf h _ isIrreducible_irreducibleComponent hhomeo
  have : IsIso ((Over.forget _).map h) := hiso
  exact isIso_of_reflects_iso h (Over.forget _)

/-- **H-85 `ModelGlue.CurveBijIso`, proved** (no leaf: Mathlib and `ZInQKernel/` only). -/
theorem curveBijIso : CurveBijIso :=
  curveBijIso_of_closed curveBijIsoClosed_proved

end PartD

end CurveSplit


namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **The comparison of coarse witnesses**: an isomorphism `X ≅ X'` compatible with the moduli bijections. -/
def CoarseCompare : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X X' : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (Ψ' : (fieldPt Qbar ⟶ X') ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (fY' : Y ⟶ X'),
    R1fpProps Y Φ → X6Props Y Φ X Ψ fY → X6Props Y Φ X' Ψ' fY' →
      ∃ g : X ≅ X', ∀ x : fieldPt Qbar ⟶ X, Ψ' (x ≫ g.hom) = Ψ x

/-- **`CoarseCompare` from `CoarseFactor` and `CurveBijIso`** (the factor map is bijective on `ℚ̄`-points since
`Ψ`, `Ψ'` are bijections; both curves are proper and smooth of relative dimension 1). -/
theorem coarseCompare_of (hF : CoarseFactor) (hB : ModelGlue.CurveBijIso) : CoarseCompare := by
  intro Y Φ X X' Ψ Ψ' fY fY' h1 h6 h6'
  obtain ⟨h, hh⟩ := hF Y Φ X X' Ψ Ψ' fY fY' h1 h6 h6'
  have hbij : Function.Bijective (fun x : fieldPt Qbar ⟶ X => x ≫ h) := by
    have e : (fun x : fieldPt Qbar ⟶ X => x ≫ h) = Ψ'.symm ∘ Ψ := by
      funext x
      simp only [Function.comp]
      rw [← hh x, Equiv.symm_apply_apply]
    rw [e]; exact Ψ'.symm.bijective.comp Ψ.bijective
  haveI := hB X X' h6.1 h6.2.1 h6'.1 h6'.2.1 h hbij
  exact ⟨asIso h, hh⟩

/-- **`CoarseCompare` from the leaf-form `CanonicalCoarseX6` alone** (`CoarseFactor` by Part 3,
`CurveBijIso` by curve-split). -/
theorem coarseCompare_of_canonical (hC : CanonicalCoarseX6) : CoarseCompare :=
  coarseCompare_of (coarseFactor_of_canonical' hC) CurveSplit.curveBijIso

/-- **`CoarseCompare` from the bundle leaf `R1R2fpRep` alone.** -/
theorem coarseCompare_of_rep (hR : LeafAdopt.R1R2fpRep) : CoarseCompare :=
  coarseCompare_of (coarseFactor_of_rep' hR) CurveSplit.curveBijIso

end HDec.QMSplit.Moduli

#print axioms CoarseFactorAG.factorThroughSurj
#print axioms HDec.QMSplit.Moduli.coarseFactor_of
#print axioms HDec.QMSplit.Moduli.coarseFactor_of_canonical'
#print axioms HDec.QMSplit.Moduli.coarseFactor_of_rep'
#print axioms CurveSplit.curveBijIso
#print axioms HDec.QMSplit.Moduli.coarseCompare_of_canonical
#print axioms HDec.QMSplit.Moduli.coarseCompare_of_rep
