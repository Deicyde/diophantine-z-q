import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.CanonicalDegree
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.Dim.Basic
import ZInQKernel.Contrib.RLeaf.BelyiX1
import ZInQKernel.Contrib.RLeaf.T40
import ZInQKernel.Contrib.HDecomp.ModCurves.X1Belyi
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.SmoothFibre.Basic
import ZInQKernel.Contrib.OneProof.Genus.DimJac

/-! (genus-fold) Part 2 of `scratch/genus-route/Closed.lean` (its lines 688-2459): the constant-field theorem and curve-split's genus bound. Namespace `GenusRoute` renamed `GenusFold`. -/

set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section
open CategoryTheory AlgebraicGeometry





-- genus-route (LocalDer.lean, verbatim) follows

/-! # genus-route: `dim J₁(N) ≤ N²` without `GenusX1Field` and without `X0Transitive`

The single proof uses T34 (`DimJ1Genus`, assembled from `DimJacobianEqGenus` and `GenusX1Field`) only
through `LeafModCurves.dim_J1_le` (`dim J₁(N) ≤ N²`), at its two consumers (TailD E2 and
`javanpeykarJ1`). This file proves that bound, `DimJ1Le`, from

* `DimJacobianEqGenus` (kernel `ZInQ.Contrib.CurvesG`, proved outright by dimjac-glue) and
* `RiemannHurwitzQj` (leaf: Stichtenoth Thm 3.4.13 with Thm 3.5.1, over Mathlib's valuation subrings),

with no other hypothesis: `dimJ1Le_of_rh_curve`.

Contents.
1. (copied from `scratch/curve-split/CurveBij.lean`, verbatim up to the namespace) integral smooth
   curves over a field are normal.
2. (new, proved) `constantFieldIsQ_of_curve`: `ℚ` is algebraically closed in the function field of a
   smooth proper geometrically connected integral curve over `ℚ`. This replaces curve-split's use of
   `X0Transitive` (through `x1ConstantField_of_x0Transitive`): the constant field of `K_N` is read off
   from the model `X` of `X₁(N)` that `IsJ1` already provides.
3. (copied from `scratch/curve-split/GenusBound.lean`, verbatim up to the namespace `CurveSplit` →
   `GenusFold`) `belyiGenusBound_of_rh : RiemannHurwitzQj → BelyiGenusBound` (the fundamental identity
   at `j = 0, 1728, ∞` is proved there from Mathlib).
4. (new, proved) `dimJ1Le_of_rh_curve : DimJacobianEqGenus → RiemannHurwitzQj → DimJ1Le`.
5. (new, proved; `GenusElem.lean` only) `dimJ1Le_of_localDerivation : DimJacobianEqGenus →
   LocalDerivation → DimJ1Le`: the genus bound `g(K_N) ≤ [K_N : ℚ(j)]` from the local leaf
   `LocalDerivation` (`d/dπ` preserves `𝒪_P` for a local parameter `π`), with no Riemann–Hurwitz:
   holomorphic differentials are `h · dj` with `h` in an explicit space `V`, and `V` injects into
   `OF / j·OF ≅ ℚ^d` (`OF` the integral closure of `ℚ[j]`).
6. (new, proved; `LocalDer.lean`) `localDerivation : LocalDerivation`, hence
   `dimJ1Le_of_dimJacobianEqGenus : DimJacobianEqGenus → DimJ1Le` (no literature leaf). Proof: `d/dj`
   exists (`Ω_{F/ℚ} = F·dj ≠ 0`, since `F/ℚ` is not formally unramified); it is bounded on `𝒪_P` (a
   `ℚ[j]`-basis of `OF` and `𝒪_P = OF_𝔭`); the residue field `OF/𝔭` is finite over `ℚ` (Zariski) with a
   primitive element `θ̄`; writing `x = p(θ) + π y`, `g(θ) = π z` improves the bound step by step, which
   forces `δ_j(π) ≠ 0` and `δ_j(𝒪_P) ⊆ δ_j(π)·𝒪_P`; `δ = δ_j / δ_j(π)`. Places over `∞`: twist `j ↦ 1/j`.

No `sorry`, no `axiom`. -/

noncomputable section





namespace GenusFold

open CategoryTheory AlgebraicGeometry Limits Polynomial
open scoped TensorProduct

/-- `⊤` is nonempty on a nonempty scheme. -/
instance instNonemptyTop (X : Scheme) [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Nonempty.some ‹_›, trivial⟩⟩

/-- `Spec k`. -/
abbrev SpecK (k : Type) [Field k] : Scheme := Spec (CommRingCat.of k)

/-! ## Normality of integral smooth curves (copied verbatim from `scratch/curve-split/CurveBij.lean`) -/

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


/-! ## Algebraic elements of the function field are global sections -/

section Sections

/-- **Gluing (proved).** On an integral scheme, an element of the function field that comes from
`Γ(X, U)` for every nonempty affine open `U` comes from `Γ(X, ⊤)`. -/
theorem exists_global_section {X : Scheme} [IsIntegral X] (y : X.functionField)
    (h : ∀ U : X.Opens, IsAffineOpen U → ∀ [Nonempty U],
      ∃ s : Γ(X, U), X.germToFunctionField U s = y) :
    ∃ s : Γ(X, ⊤), X.germToFunctionField ⊤ s = y := by
  let ι := {U : X.Opens // IsAffineOpen U ∧ Nonempty U}
  let V : ι → X.Opens := fun i => i.1
  have hne : ∀ i : ι, Nonempty (V i) := fun i => i.2.2
  have h' : ∀ i : ι, ∃ s : Γ(X, V i), X.germToFunctionField (V i) s = y :=
    fun i => @h i.1 i.2.1 i.2.2
  choose sf hsf using h'
  have hcover : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW, ⟨⟨x, hxW⟩⟩⟩, hxW⟩
  have hinter : ∀ i j : ι, Nonempty ((V i ⊓ V j : X.Opens) : Set X) := by
    intro i j
    obtain ⟨x, hx⟩ := nonempty_preirreducible_inter (V i).isOpen (V j).isOpen
      ⟨_, (hne i).some.2⟩ ⟨_, (hne j).some.2⟩
    exact ⟨⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V sf := by
    intro i j
    apply @Scheme.germToFunctionField_injective X _ (V i ⊓ V j) (hinter i j)
    change X.presheaf.germ _ _ _ (X.presheaf.map _ (sf i)) =
      X.presheaf.germ _ _ _ (X.presheaf.map _ (sf j))
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    exact (hsf i).trans (hsf j).symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) hcover sf hcompat
  let s' : Γ(X, ⊤) := s
  refine ⟨s', ?_⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let i : ι := ⟨W, hW, ⟨⟨x, hxW⟩⟩⟩
  have := hne i
  have hsi : X.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op s' = sf i := hs i
  rw [← hsf i, ← hsi, X.presheaf.germ_res_apply]

/-- **Integrality (proved).** On a normal integral scheme, an element of the function field
integral over `Γ(X, U)` for every nonempty affine open `U` is a global section. -/
theorem exists_global_of_isIntegral {X : Scheme} [IsIntegral X]
    (hN : ZInQ.Contrib.CurvesG.IsNormalScheme X) (y : X.functionField)
    (hy : ∀ U : X.Opens, IsAffineOpen U → ∀ [Nonempty U], IsIntegral Γ(X, U) y) :
    ∃ s : Γ(X, ⊤), X.germToFunctionField ⊤ s = y := by
  apply exists_global_section
  intro U hU _
  haveI := isIntegrallyClosed_of_normal hN hU
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hy U hU)
  exact ⟨s, hs⟩

end Sections

/-! ## The constant field -/

section ConstField

/-- Morphisms to `Spec ℚ` are unique. -/
theorem hom_specQ_ext {X : Scheme} (f g : X ⟶ SpecK ℚ) : f = g := by
  apply ext_of_isAffine
  have h : f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom =
      g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom := RingHom.ext_rat _ _
  ext a
  have := congrArg (fun φ => φ ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom a)) h
  simpa using this

/-- The prime spectrum of a field is a single point. -/
theorem subsingleton_primeSpectrum_field (A : Type) [Field A] : Subsingleton (PrimeSpectrum A) := by
  refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
  have hp : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top p.asIdeal).resolve_right p.2.ne_top
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.2.ne_top
  rw [hp, hq]

/-- **Two distinct roots give two points (proved).** If a polynomial `q` over `ℚ` with `ℚ[T]/(q)`
a field has two distinct roots in `ℚ̄`, then `Spec (ℚ̄ ⊗ ℚ[T]/(q))` has two distinct points. -/
theorem not_subsingleton_of_roots (q : ℚ[X]) [Fact (Irreducible q)] {α β : AlgebraicClosure ℚ}
    (hα : q.eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) α = 0)
    (hβ : q.eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) β = 0) (hne : α ≠ β) :
    ¬ Subsingleton (PrimeSpectrum (AlgebraicClosure ℚ ⊗[ℚ] AdjoinRoot q)) := by
  intro hS
  let Qb := AlgebraicClosure ℚ
  have hα' : q.eval₂ ((Algebra.ofId ℚ Qb : ℚ →ₐ[ℚ] Qb) : ℚ →+* Qb) α = 0 := hα
  have hβ' : q.eval₂ ((Algebra.ofId ℚ Qb : ℚ →ₐ[ℚ] Qb) : ℚ →+* Qb) β = 0 := hβ
  let χ : ∀ γ : Qb, q.eval₂ ((Algebra.ofId ℚ Qb : ℚ →ₐ[ℚ] Qb) : ℚ →+* Qb) γ = 0 → (Qb ⊗[ℚ] AdjoinRoot q →ₐ[ℚ] Qb) :=
    fun γ hγ => Algebra.TensorProduct.productMap (AlgHom.id ℚ Qb)
        (AdjoinRoot.liftAlgHom q (Algebra.ofId ℚ Qb) γ hγ)
  let P : ∀ γ : Qb, q.eval₂ ((Algebra.ofId ℚ Qb : ℚ →ₐ[ℚ] Qb) : ℚ →+* Qb) γ = 0 → PrimeSpectrum (Qb ⊗[ℚ] AdjoinRoot q) :=
    fun γ hγ => ⟨RingHom.ker (χ γ hγ : Qb ⊗[ℚ] AdjoinRoot q →+* Qb), RingHom.ker_isPrime _⟩
  let z : Qb ⊗[ℚ] AdjoinRoot q := 1 ⊗ₜ AdjoinRoot.root q - α ⊗ₜ 1
  have hz : ∀ γ (hγ : q.eval₂ ((Algebra.ofId ℚ Qb : ℚ →ₐ[ℚ] Qb) : ℚ →+* Qb) γ = 0), χ γ hγ z = γ - α := by
    intro γ hγ
    have e1 : χ γ hγ (1 ⊗ₜ AdjoinRoot.root q) = γ := by
      change (1 : Qb) * AdjoinRoot.liftAlgHom q (Algebra.ofId ℚ Qb) γ hγ (AdjoinRoot.root q) = γ
      rw [AdjoinRoot.liftAlgHom_root, one_mul]
    have e2 : χ γ hγ (α ⊗ₜ 1) = α := by
      change α * AdjoinRoot.liftAlgHom q (Algebra.ofId ℚ Qb) γ hγ 1 = α
      rw [map_one, mul_one]
    simp only [z, map_sub, e1, e2]
  have h1 : z ∈ (P α hα').asIdeal := by
    show (χ α hα' : Qb ⊗[ℚ] AdjoinRoot q →+* Qb) z = 0
    simp [hz α hα']
  have h2 : z ∉ (P β hβ').asIdeal := by
    show ¬ (χ β hβ' : Qb ⊗[ℚ] AdjoinRoot q →+* Qb) z = 0
    simp only [AlgHom.coe_toRingHom, hz β hβ']
    exact sub_ne_zero.mpr hne.symm
  exact h2 (Subsingleton.elim (P α hα') (P β hβ') ▸ h1)

/-- **The constant field of a smooth geometrically connected integral curve over `ℚ` is `ℚ`
(proved).** An element of `K(X)` algebraic over `ℚ` is rational. -/
theorem algebraic_mem_range {X : Scheme} (p : X ⟶ SpecK ℚ) [IsIntegral X]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] (ι : ℚ →+* X.functionField) (y : X.functionField) (f : ℚ[X])
    (hf : f ≠ 0) (hy : f.eval₂ ι y = 0) : y ∈ Set.range ι := by
  letI : Algebra ℚ X.functionField := ι.toAlgebra
  have hint : IsIntegral ℚ y := (show IsAlgebraic ℚ y from ⟨f, hf, by rwa [aeval_def]⟩).isIntegral
  have hN := isNormal_of_integral p
  let ιΓ : ℚ →+* Γ(X, ⊤) := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
  have hyU : ∀ U : X.Opens, IsAffineOpen U → ∀ [Nonempty U], IsIntegral Γ(X, U) y := by
    intro U hU _
    let g : ℚ →+* Γ(X, U) := (X.presheaf.map (homOfLE le_top).op).hom.comp ιΓ
    refine ⟨(minpoly ℚ y).map g, (minpoly.monic hint).map g, ?_⟩
    rw [eval₂_map]
    have : (algebraMap Γ(X, U) X.functionField).comp g = algebraMap ℚ X.functionField :=
      RingHom.ext_rat _ _
    rw [this, ← aeval_def, minpoly.aeval]
  obtain ⟨s, hs⟩ := exists_global_of_isIntegral hN y hyU
  set q := minpoly ℚ y with hqdef
  haveI : Fact (Irreducible q) := ⟨minpoly.irreducible hint⟩
  have hqs : q.eval₂ ιΓ s = 0 := by
    apply X.germToFunctionField_injective ⊤
    rw [map_zero, hom_eval₂, hs]
    have : (X.germToFunctionField ⊤).hom.comp ιΓ = algebraMap ℚ X.functionField :=
      RingHom.ext_rat _ _
    rw [this, ← aeval_def, minpoly.aeval]
  let A := AdjoinRoot q
  let ψ : A →+* Γ(X, ⊤) := AdjoinRoot.lift ιΓ s hqs
  let φ : X ⟶ Spec (CommRingCat.of A) := X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  let π : Spec (CommRingCat.of A) ⟶ SpecK ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ A))
  let Qb := AlgebraicClosure ℚ
  let ι' : SpecK Qb ⟶ SpecK ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ Qb))
  have hp : p = φ ≫ π := hom_specQ_ext _ _
  haveI : GeometricallyConnected (φ ≫ π) := hp ▸ inferInstance
  have hc1 : ConnectedSpace ↥(pullback (φ ≫ π) ι') :=
    GeometricallyConnected.geometrically_connectedSpace ι' (pullback.fst _ _) (pullback.snd _ _)
      (IsPullback.of_hasPullback _ _)
  have hc2 : ConnectedSpace ↥(pullback φ (pullback.fst π ι')) :=
    (pullbackRightPullbackFstIso π ι' φ).hom.homeomorph.connectedSpace_iff.mpr hc1
  haveI : Subsingleton (Spec (CommRingCat.of A)) := subsingleton_primeSpectrum_field A
  haveI : Surjective φ := ⟨fun a => ⟨(inferInstance : Nonempty X).some, Subsingleton.elim _ _⟩⟩
  have hsurj : Function.Surjective (pullback.snd φ (pullback.fst π ι')) :=
    (inferInstance : Surjective (pullback.snd φ (pullback.fst π ι'))).surj
  have hc3 : ConnectedSpace ↥(pullback π ι') :=
    hsurj.connectedSpace (pullback.snd φ (pullback.fst π ι')).continuous
  have hc4 : ConnectedSpace ↥(pullback ι' π) :=
    (pullbackSymmetry π ι').hom.homeomorph.connectedSpace_iff.mp hc3
  have hc5 : ConnectedSpace (PrimeSpectrum (Qb ⊗[ℚ] A)) :=
    (pullbackSpecIso ℚ Qb A).hom.homeomorph.connectedSpace_iff.mp hc4
  haveI : IsArtinianRing (Qb ⊗[ℚ] A) := IsArtinianRing.of_finite Qb (Qb ⊗[ℚ] A)
  have hsub : Subsingleton (PrimeSpectrum (Qb ⊗[ℚ] A)) :=
    ⟨fun a b => isPreconnected_univ.subsingleton (Set.mem_univ a) (Set.mem_univ b)⟩
  have hdeg : q.natDegree ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have hsep : q.Separable := (minpoly.irreducible hint).separable
    have hcard := card_rootSet_eq_natDegree (K := Qb) hsep (IsAlgClosed.splits _)
    obtain ⟨⟨α, hα⟩, ⟨β, hβ⟩, hne⟩ := Fintype.exists_pair_of_one_lt_card (by rw [hcard]; omega)
    have hα' := (mem_rootSet.mp hα).2
    have hβ' := (mem_rootSet.mp hβ).2
    rw [aeval_def] at hα' hβ'
    exact not_subsingleton_of_roots q hα' hβ' (fun h => hne (Subtype.ext h)) hsub
  have h1 : q.natDegree = 1 := le_antisymm hdeg (minpoly.natDegree_pos hint)
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h1
  exact ⟨c, hc⟩

end ConstField

/-- **`ConstantFieldIsQ` for every field isomorphic to the function field of a curve (proved).**
For a smooth proper geometrically connected integral curve `X/ℚ` and a field `F ≅ K(X)` over
`ℚ(j)`, `ℚ` is algebraically closed in `F`. -/
theorem constantFieldIsQ_of_curve (X : Over LeafModCurves.SpecQ) (hC : LeafModCurves.IsCurve X)
    [IsIntegral X.left] (F : Type) [Field F] [Algebra LeafModCurves.Qj F]
    (e : X.left.functionField ≃+* F) : X1Belyi.ConstantFieldIsQ F := by
  rintro x ⟨f, hf, hx⟩
  haveI : SmoothOfRelativeDimension 1 X.hom := hC.smooth
  haveI : GeometricallyConnected X.hom := hC.geomConnected
  let ι : ℚ →+* X.left.functionField := e.symm.toRingHom.comp (X1Belyi.ratHom F)
  have hy : f.eval₂ ι (e.symm x) = 0 := by
    have := hom_eval₂ f (X1Belyi.ratHom F) e.symm.toRingHom x
    rw [hx, map_zero] at this
    exact this.symm
  obtain ⟨c, hc⟩ := algebraic_mem_range X.hom ι (e.symm x) f hf hy
  refine ⟨c, ?_⟩
  have := congrArg e hc
  simpa [ι] using this

end GenusFold







namespace GenusFold

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

/-- **GLUE (lit-composite): the Riemann–Hurwitz bound for Belyi functions.** Let `F` be a finite
extension of `ℚ(j)` (`Qj = RatFunc ℚ`) in which `ℚ` is algebraically closed, and suppose
`t = j/1728` is a Belyi function on `F` over `ℚ` (`IsBelyiFunction`: unramified over every finite
place of `ℚ(t)` other than `t = 0, 1`). Then `2 g(F) + 1 ≤ [F : ℚ(j)]`, `g = fieldGenus`.

Why true (STANDARD): Riemann–Hurwitz (Stichtenoth, *Algebraic function fields and codes*, Thm
3.4.13, with Dedekind's different theorem Thm 3.5.1 in characteristic 0; Hartshorne IV.2.4
geometrically; numbers UNVERIFIED) gives `2g − 2 = −2d + Σ_P (e_P − 1) deg P`, the sum over the
places above `t = 0, 1, ∞` only; at each of these three degree-one places the fundamental
identity `Σ_{P|Q} e_P f_P = d` (Stichtenoth Thm 3.1.11) gives `Σ_{P|Q} (e_P − 1) f_P ≤ d − 1`; so
`2g − 2 ≤ d − 3`. Also needed: the places of `F/ℚ` are discrete valuation rings (Stichtenoth Thm
1.1.6) to read `IsBelyiFunction` as `e_P = 1`, and `fieldGenus` (holomorphic differentials) is the
Riemann–Roch genus (Stichtenoth Thm 1.5.15 / Chevalley; UNVERIFIED). A Lean proof needs Lean
statements of these four textbook results over Mathlib's `ValuationSubring` (places, `e_P` as the
index of `Uₚ·ℚ(t)ˣ` in `Fˣ`, `deg P` as the `ℚ`-dimension of the residue field) and about 400
lines of valuation-theoretic glue. -/
def BelyiGenusBound : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → IsBelyiFunction ℚ F (algebraMap Qj F (RatFunc.X / 1728)) →
      2 * fieldGenus F + 1 ≤ Module.finrank Qj F

/-- **The genus bound that the proof uses** (weaker than `GenusX1Field`): `g(K_N) ≤ N²`. -/
def GenusX1Le : Prop :=
  ∀ (N : ℕ) (P : EjBar.toAffine.Point), 0 < N → addOrderOf P = N →
    fieldGenus (fieldX1 P) ≤ N ^ 2

/-- **The conclusion of `LeafModCurves.dim_J1_le`** (`dim J₁(N) ≤ N²`), the only use of T34. -/
def DimJ1Le : Prop :=
  ∀ (N : ℕ) (J : PkgI3.AbVar ℚ), 0 < N → IsJ1 N J →
    ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2

/-- `GenusX1Field → GenusX1Le` (proved, from `genus_Gamma1_le`). -/
theorem genusX1Le_of_genusX1Field (h : GenusX1Field) : GenusX1Le := by
  intro N P hN hP
  have : NeZero N := ⟨hN.ne'⟩
  have h1 := h N P hN hP
  have h2 := genus_Gamma1_le N
  rw [← h1] at h2
  exact_mod_cast h2

/-- **`DimJ1Le` from the first half of T34 and the genus bound** (proved). -/
theorem dimJ1Le_of (h1 : DimJacobianEqGenus) (h2 : GenusX1Le) : DimJ1Le := by
  rintro N J hN ⟨X, P₀, aj, ⟨hC, hI, P, hP, he⟩, hJ⟩
  exact ⟨fieldGenus (fieldX1 P), h1 X hC P₀ J aj hJ hI (fieldX1 P) he, h2 N P hN hP⟩

/-- `K_N` is finite over `ℚ(j)`. -/
instance fieldX1_finiteDimensional (P : EjBar.toAffine.Point) :
    FiniteDimensional Qj (fieldX1 P) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (xCoord P))

/-- **`GenusX1Le` from the Riemann–Hurwitz bound for Belyi functions and `X₀(N)`-transitivity**
(proved; `BelyiX1` and the constant field are kernel theorems). -/
theorem genusX1Le_of_belyi (hB : BelyiGenusBound) (h0 : ZInQ.RLeaf.X0Transitive) :
    GenusX1Le := by
  intro N P hN hP
  obtain ⟨hBel, hdeg⟩ := ZInQ.RLeaf.belyiX1 N P hN hP
  have hK := ZInQ.RLeaf.x1ConstantField_of_x0Transitive h0 N P hN hP
  have := hB (fieldX1 P) hK hBel
  omega

/-- **`DimJ1Le` (the use of T34) from `DimJacobianEqGenus`, `BelyiGenusBound` and
`X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_belyi (h1 : DimJacobianEqGenus) (hB : BelyiGenusBound)
    (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of h1 (genusX1Le_of_belyi hB h0)

/-! ## `BelyiGenusBound` from three textbook theorems

Places of a function field `F/ℚ` are Mathlib `ValuationSubring`s; the ramification index over
`ℚ(j)` is the index of `U_P · ℚ(j)ˣ` in `Fˣ` (`Fˣ/U_P` is the value group), the degree of a place
is the `ℚ`-dimension of its residue field. -/

section RH

variable (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- A place of `F/ℚ`: a proper valuation subring containing `ℚ`. -/
structure Place where
  w : ValuationSubring F
  ne_top : w ≠ ⊤
  rat_mem : ∀ c : ℚ, algebraMap ℚ F c ∈ w

variable {F}

theorem Place.ext' {P Q : Place F} (h : P.w = Q.w) : P = Q := by
  cases P; cases Q; cases h; rfl

/-- `ℚ → κ(P)`. -/
def Place.ratHom (P : Place F) : ℚ →+* IsLocalRing.ResidueField P.w :=
  (IsLocalRing.residue P.w).comp ((algebraMap ℚ F).codRestrict P.w.toSubring P.rat_mem)

/-- The degree `[κ(P) : ℚ]` of a place. -/
def Place.deg (P : Place F) : ℕ :=
  @Module.finrank ℚ (IsLocalRing.ResidueField P.w) _ _ P.ratHom.toModule

/-- The ramification index `e(P | P ∩ ℚ(j))`: the index of `U_P · ℚ(j)ˣ` in `Fˣ`. -/
def Place.ramIdx (P : Place F) : ℕ :=
  (P.w.unitGroup ⊔ (Units.map (algebraMap Qj F : Qj →* F)).range).index

/-- The Belyi coordinate `t = j/1728` in `F`. -/
abbrev tF : F := algebraMap Qj F (RatFunc.X / 1728)

variable (F)

/-- **Leaf: Riemann–Hurwitz for `F/ℚ(j)`** (published). For `F` finite over `ℚ(j)` with
constant field `ℚ`: only finitely many places ramify, and
`2 g(F) − 2 = [F : ℚ(j)] · (2·0 − 2) + Σ_P (e_P − 1) deg P`.
Source: Stichtenoth, *Algebraic Function Fields and Codes* (2nd ed.), Thm 3.4.13 (Hurwitz genus
formula, `g(ℚ(j)) = 0`) with Thm 3.5.1 (Dedekind's different theorem: `d(P) = e_P − 1` in
characteristic 0); Hartshorne IV.2.4 geometrically (numbers UNVERIFIED). The genus is
`fieldGenus` (the dimension of the holomorphic differentials, which equals the Riemann–Roch genus:
Stichtenoth Thm 1.5.15 / Hartshorne II.8, UNVERIFIED): a composite of these printed statements. -/
def RiemannHurwitzQj : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F →
      ∃ h : (Function.support fun P : Place F => ((P.ramIdx : ℤ) - 1) * P.deg).Finite,
        2 * (fieldGenus F : ℤ) - 2 =
          -2 * (Module.finrank Qj F : ℤ) + ∑ P ∈ h.toFinset, ((P.ramIdx : ℤ) - 1) * P.deg

/-- **Leaf: the fundamental identity at the places `j = 0`, `j = 1728`, `j = ∞` of `ℚ(j)`**
(published). For `F` finite over `ℚ(j)` and `Q` one of these three places of degree one, finitely
many places `P` of `F` lie over `Q` and `Σ_{P|Q} e_P deg P = [F : ℚ(j)]`.
Source: Stichtenoth Thm 3.1.11 (`Σ e(P|Q) f(P|Q) = [F : ℚ(j)]`) with `deg P = f(P|Q) deg Q` and
`deg Q = 1` (Stichtenoth §3.1; numbers UNVERIFIED). `P` lies over `j = 0` iff `t ∈ 𝔪_P`, over
`j = 1728` iff `t − 1 ∈ 𝔪_P`, over `j = ∞` iff `t ∉ 𝒪_P` (`t = j/1728`). -/
def FundamentalIdentityQj : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ∀ Z ∈ ({{P : Place F | tF ∈ P.w ∧ tF ∈ P.w.nonunits},
        {P : Place F | tF ∈ P.w ∧ tF - 1 ∈ P.w.nonunits},
        {P : Place F | tF ∉ P.w}} : Set (Set (Place F))),
      ∃ h : Z.Finite, ∑ P ∈ h.toFinset, P.ramIdx * P.deg = Module.finrank Qj F

/-- **Leaf: places of a function field are discrete valuation rings** (published). Every place
`P` of `F/ℚ` has a uniformizer `π`: `π ∈ 𝒪_P` is not a unit, and every `x ∈ Fˣ` is `π^n` times a
unit of `𝒪_P`. Source: Stichtenoth Thm 1.1.6 with Def. 1.1.4 / Thm 1.1.5 (numbers UNVERIFIED). -/
def PlacesAreDVR : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ∀ P : Place F, ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup

end RH

section Glue

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- Valuation of a `ℤ`-power of a unit. -/
theorem val_zpow (A : ValuationSubring F) (x : Fˣ) (n : ℤ) :
    A.valuation ((x ^ n : Fˣ) : F) = A.valuation (x : F) ^ n := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]

/-- **`e_P = 1` when a uniformizer comes from `ℚ(j)`** (proved). If `P` has a uniformizer `π` and
`s = r ∈ ℚ(j)ˣ` is a non-unit of `𝒪_P` dividing every element of `𝔪_P`, then `e_P = 1`. -/
theorem ramIdx_eq_one (P : Place F) (π : Fˣ) (hπ : (π : F) ∈ P.w) (hπu : π ∉ P.w.unitGroup)
    (hdvr : ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup) (r : Qj) (hr0 : r ≠ 0)
    (hs : algebraMap Qj F r ∈ P.w.nonunits)
    (hgen : ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = algebraMap Qj F r * y) : P.ramIdx = 1 := by
  set v := P.w.valuation
  set s : Fˣ := Units.map (algebraMap Qj F : Qj →* F) (Units.mk0 r hr0) with hsdef
  have hsval : (s : F) = algebraMap Qj F r := rfl
  have hsrange : s ∈ (Units.map (algebraMap Qj F : Qj →* F)).range := ⟨_, rfl⟩
  -- `v π < 1`
  have hvπ1 : v π ≤ 1 := (P.w.valuation_le_one_iff _).mpr hπ
  have hvπne : v π ≠ 1 := fun h => hπu ((P.w.mem_unitGroup_iff π).mpr h)
  have hvπ : v π < 1 := lt_of_le_of_ne hvπ1 hvπne
  have hvπ0 : 0 < v π := (Valuation.pos_iff v).mpr π.ne_zero
  have hanti := zpow_right_strictAnti₀ hvπ0 hvπ
  -- `v(x) = v(π)^n` from the uniformizer
  have hval : ∀ x : Fˣ, ∃ n : ℤ, v x = v π ^ n := by
    intro x
    obtain ⟨n, hn⟩ := hdvr x
    refine ⟨n, ?_⟩
    have h1 : v ((x * π ^ (-n) : Fˣ) : F) = 1 := (P.w.mem_unitGroup_iff _).mp hn
    rw [Units.val_mul, map_mul, val_zpow, zpow_neg] at h1
    have hne : v π ^ n ≠ 0 := (zpow_pos hvπ0 n).ne'
    calc v x = v x * ((v π ^ n)⁻¹ * v π ^ n) := by rw [inv_mul_cancel₀ hne, mul_one]
      _ = v π ^ n := by rw [← mul_assoc, h1, one_mul]
  -- `v(s) = v(π)`
  obtain ⟨m, hm⟩ := hval s
  have hvs : v s < 1 := (P.w.mem_nonunits_iff).mp (hsval ▸ hs)
  have hπn : (π : F) ∈ P.w.nonunits := (P.w.mem_nonunits_iff).mpr hvπ
  obtain ⟨y, hy, hπy⟩ := hgen _ hπn
  have hvy : v y ≤ 1 := (P.w.valuation_le_one_iff _).mpr hy
  have hle : v π ≤ v s := by
    rw [hπy, map_mul, ← hsval]
    exact mul_le_of_le_one_right zero_le hvy
  have hm1 : m = 1 := by
    have h1 : v π ^ (1 : ℤ) ≤ v π ^ m := by rw [zpow_one, ← hm]; exact hle
    have h2 : v π ^ m < v π ^ (0 : ℤ) := by rw [zpow_zero, ← hm]; exact hvs
    have h3 : m ≤ 1 := hanti.le_iff_ge.mp h1
    have h4 : 0 < m := hanti.lt_iff_gt.mp h2
    omega
  rw [hm1, zpow_one] at hm
  -- every unit lies in `U_P · ℚ(j)ˣ`
  rw [Place.ramIdx, Subgroup.index_eq_one, eq_top_iff]
  intro x _
  obtain ⟨n, hn⟩ := hval x
  have hu : x * s ^ (-n) ∈ P.w.unitGroup := by
    rw [P.w.mem_unitGroup_iff, Units.val_mul, map_mul, val_zpow, hm, hn, zpow_neg,
      mul_inv_cancel₀ (zpow_pos hvπ0 n).ne']
  have : x = (x * s ^ (-n)) * s ^ n := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem _ hsrange n))

end Glue

section Glue2

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

theorem algebraMap_rat_comp : (algebraMap Qj F).comp (algebraMap ℚ Qj) = algebraMap ℚ F :=
  RingHom.ext_rat _ _

theorem mul_mem_nonunits (A : ValuationSubring F) {a b : F} (ha : a ∈ A) (hb : b ∈ A.nonunits) :
    a * b ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hb ⊢
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le ((A.valuation_le_one_iff a).mpr ha)) hb

/-- Polynomials over `ℚ` at an element of `𝒪_P` stay in `𝒪_P`. -/
theorem aeval_mem (P : Place F) {z : F} (hz : z ∈ P.w) (p : Polynomial ℚ) :
    Polynomial.aeval z p ∈ P.w := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (P.rat_mem _) (Subring.pow_mem _ hz _)

/-- `ℚ(j)`-polynomials at an element of `𝒪_P`, when `ℚ(j) ⊆ 𝒪_P`. -/
theorem aeval_mem_Qj (P : Place F) (himg : ∀ r : Qj, algebraMap Qj F r ∈ P.w) {z : F}
    (hz : z ∈ P.w) (p : Polynomial Qj) : Polynomial.aeval z p ∈ P.w := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (himg _) (Subring.pow_mem _ hz _)

/-- The polynomials over `ℚ` vanishing at the place `P` (when `t ∈ 𝒪_P`). -/
def polyIdeal (P : Place F) (ht : (tF : F) ∈ P.w) : Ideal (Polynomial ℚ) where
  carrier := {p | Polynomial.aeval (tF : F) p ∈ P.w.nonunits}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact P.w.nonunits.add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact P.w.nonunits.zero_mem
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
    exact mul_mem_nonunits P.w (aeval_mem P ht c) hx

theorem polyIdeal_isPrime (P : Place F) (ht : (tF : F) ∈ P.w) : (polyIdeal P ht).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    show Polynomial.aeval (tF : F) 1 ∉ P.w.nonunits
    rw [map_one, ValuationSubring.mem_nonunits_iff, map_one]
    exact lt_irrefl _
  · intro a b hab
    have ha := (P.w.valuation_le_one_iff _).mpr (aeval_mem P ht a)
    have hb := (P.w.valuation_le_one_iff _).mpr (aeval_mem P ht b)
    change Polynomial.aeval (tF : F) (a * b) ∈ P.w.nonunits at hab
    change Polynomial.aeval (tF : F) a ∈ P.w.nonunits ∨ Polynomial.aeval (tF : F) b ∈ P.w.nonunits
    rw [map_mul, ValuationSubring.mem_nonunits_iff, map_mul] at hab
    rw [ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff]
    by_contra h
    push_neg at h
    have h1 := le_antisymm ha h.1
    have h2 := le_antisymm hb h.2
    rw [h1, h2, one_mul] at hab
    exact lt_irrefl _ hab

/-- `ℚ[j] → F`, through `ℚ(j)`, is evaluation at `1728 t`. -/
theorem algebraMap_poly (p : Polynomial ℚ) :
    algebraMap Qj F (algebraMap (Polynomial ℚ) Qj p) =
      Polynomial.aeval (tF : F) (p.comp (Polynomial.C 1728 * Polynomial.X)) := by
  have h1728 : Polynomial.aeval (tF : F) (Polynomial.C (1728 : ℚ) * Polynomial.X) =
      algebraMap Qj F RatFunc.X := by
    rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp only [map_ofNat]
    rw [tF, ← map_ofNat (algebraMap Qj F) 1728, ← map_mul]
    congr 1
    field_simp
  have h2 : algebraMap Qj F (algebraMap (Polynomial ℚ) Qj p) =
      Polynomial.aeval (algebraMap Qj F RatFunc.X) p := by
    have : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
        (Polynomial.aeval (algebraMap Qj F RatFunc.X)).toRingHom := by
      refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
      simp [RatFunc.algebraMap_X]
    exact congrArg (fun φ : Polynomial ℚ →+* F => φ p) this
  rw [h2, Polynomial.aeval_comp]
  exact (congrArg (fun z => Polynomial.aeval z p) h1728).symm

theorem comp_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) :
    p.comp (Polynomial.C 1728 * Polynomial.X) ≠ 0 := by
  intro h
  have h2 := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X _ (by norm_num), mul_one,
    Polynomial.natDegree_zero] at h2
  have h3 := congrArg Polynomial.leadingCoeff h
  rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_C_mul_X _ (by norm_num)]; norm_num),
    Polynomial.leadingCoeff_zero] at h3
  simp only [Polynomial.leadingCoeff_C_mul_X, mul_eq_zero, pow_eq_zero_iff', Polynomial.leadingCoeff_eq_zero] at h3
  tauto

/-- **The ideal of a place is nonzero** (proved): otherwise `ℚ(j) ⊆ 𝒪_P`, and then `𝒪_P = F`
since `F` is algebraic over `ℚ(j)` (an element outside `𝒪_P` has an inverse in `𝔪_P` whose minimal
polynomial has a nonzero constant term in `𝔪_P ∩ ℚ(j) = 0`). -/
theorem polyIdeal_ne_bot [FiniteDimensional Qj F] (P : Place F) (ht : (tF : F) ∈ P.w)
    (htr : Transcendental ℚ (tF : F)) : polyIdeal P ht ≠ ⊥ := by
  intro hbot
  have hunit : ∀ p : Polynomial ℚ, p ≠ 0 → (Polynomial.aeval (tF : F) p)⁻¹ ∈ P.w := by
    intro p hp
    have h2 : Polynomial.aeval (tF : F) p ∉ P.w.nonunits := fun h => by
      have : p ∈ polyIdeal P ht := h
      rw [hbot, Ideal.mem_bot] at this
      exact hp this
    have h0 : Polynomial.aeval (tF : F) p ≠ 0 := fun h0 => htr ⟨p, hp, h0⟩
    rw [ValuationSubring.mem_nonunits_iff_or] at h2
    push_neg at h2
    exact h2.2
  have himg : ∀ r : Qj, algebraMap Qj F r ∈ P.w := by
    intro r
    rw [← RatFunc.num_div_denom r, map_div₀, algebraMap_poly, algebraMap_poly, div_eq_mul_inv]
    exact Subring.mul_mem _ (aeval_mem P ht _) (hunit _ (comp_ne_zero (RatFunc.denom_ne_zero r)))
  obtain ⟨x, hx⟩ : ∃ x, x ∉ P.w := by
    by_contra h
    push_neg at h
    exact P.ne_top (eq_top_iff.mpr fun x _ => h x)
  have hx0 : x ≠ 0 := fun h => hx (h ▸ P.w.zero_mem)
  have hy : x⁻¹ ∈ P.w.nonunits := (P.w.inv_mem_nonunits_iff).mpr (Or.inr hx)
  have hyw : x⁻¹ ∈ P.w := P.w.nonunits_subset hy
  have hy0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
  have hint : IsIntegral Qj x⁻¹ := IsIntegral.of_finite Qj _
  set p := minpoly Qj x⁻¹
  have hc0 := minpoly.coeff_zero_ne_zero hint hy0
  have hev : Polynomial.aeval x⁻¹ p = 0 := minpoly.aeval Qj _
  have hsplit := Polynomial.X_mul_divX_add p
  rw [← hsplit, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hev
  have hc : algebraMap Qj F (p.coeff 0) = -(x⁻¹ * Polynomial.aeval x⁻¹ p.divX) := by
    linear_combination hev
  have hcn : algebraMap Qj F (p.coeff 0) ∈ P.w.nonunits := by
    rw [hc, mul_comm]
    exact P.w.nonunits.neg_mem (mul_mem_nonunits P.w (aeval_mem_Qj P himg hyw _) hy)
  have hcinv : (algebraMap Qj F (p.coeff 0))⁻¹ ∈ P.w := by
    rw [← map_inv₀]; exact himg _
  rw [ValuationSubring.mem_nonunits_iff_or] at hcn
  rcases hcn with h | h
  · exact hc0 ((map_eq_zero_iff _ (algebraMap Qj F).injective).mp h)
  · exact h hcinv

/-- A nonzero prime ideal of `ℚ[X]` contains a monic irreducible polynomial. -/
theorem exists_monic_irreducible_mem (I : Ideal (Polynomial ℚ)) [hI : I.IsPrime] (h0 : I ≠ ⊥) :
    ∃ q : Polynomial ℚ, q.Monic ∧ Irreducible q ∧ q ∈ I := by
  set g := Submodule.IsPrincipal.generator I
  have hg0 : g ≠ 0 := by
    intro h
    apply h0
    rw [← Submodule.IsPrincipal.span_singleton_generator I]
    simp [g, h]
  have hgp : Prime g := Submodule.IsPrincipal.prime_generator_of_isPrime I h0
  refine ⟨g * Polynomial.C g.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hg0, ?_, ?_⟩
  · refine (irreducible_mul_isUnit ?_).mpr hgp.irreducible
    exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg0)))
  · exact I.mul_mem_right _ (Submodule.IsPrincipal.generator_mem I)

end Glue2

section Glue3

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- `ℚ(j) → F` commutes with evaluating `ℚ`-polynomials. -/
theorem algebraMap_aeval (z : Qj) (q : Polynomial ℚ) :
    algebraMap Qj F (Polynomial.aeval z q) = Polynomial.aeval (algebraMap Qj F z) q := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, algebraMap_rat_comp]

/-- **Every place lies over `j = 0`, `j = 1728`, `j = ∞`, or is unramified** (proved from the
Belyi property and the uniformizer leaf). -/
theorem place_cases [FiniteDimensional Qj F] (hB : IsBelyiFunction ℚ F (tF : F))
    (hD : PlacesAreDVR) (P : Place F) :
    ((tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits) ∨ ((tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits) ∨
      (tF : F) ∉ P.w ∨ P.ramIdx = 1 := by
  by_cases ht : (tF : F) ∈ P.w
  · have hpr := polyIdeal_isPrime P ht
    obtain ⟨q, hqm, hqi, hqI⟩ := exists_monic_irreducible_mem (polyIdeal P ht)
      (polyIdeal_ne_bot P ht hB.1)
    have hqI' : Polynomial.aeval (tF : F) q ∈ P.w.nonunits := hqI
    by_cases hX : q = Polynomial.X
    · left
      rw [hX, Polynomial.aeval_X] at hqI'
      exact ⟨ht, hqI'⟩
    by_cases hX1 : q = Polynomial.X - 1
    · right; left
      rw [hX1, map_sub, Polynomial.aeval_X, map_one] at hqI'
      exact ⟨ht, hqI'⟩
    right; right; right
    have hgen := hB.2 P.w P.rat_mem ht q hqm hqi hX hX1 hqI'
    obtain ⟨π, hπ, hπu, hdvr⟩ := hD F P
    set r : Qj := Polynomial.aeval (RatFunc.X / 1728 : Qj) q with hr
    have hrq : algebraMap Qj F r = Polynomial.aeval (tF : F) q := by
      rw [hr, algebraMap_aeval]
    have hr0 : r ≠ 0 := by
      intro h0
      have : Polynomial.aeval (tF : F) q = 0 := by rw [← hrq, h0, map_zero]
      exact hB.1 ⟨q, hqm.ne_zero, this⟩
    refine ramIdx_eq_one P π hπ hπu hdvr r hr0 (hrq ▸ hqI') ?_
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hgen x hx
    exact ⟨y, hy, hrq ▸ hxy⟩
  · right; right; left
    exact ht

/-- Variant of `place_cases` with uniformizers only at places containing `t`. -/
theorem place_cases' [FiniteDimensional Qj F] (hB : IsBelyiFunction ℚ F (tF : F))
    (hD : ∀ P : Place F, (tF : F) ∈ P.w → ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup) (P : Place F) :
    ((tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits) ∨ ((tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits) ∨
      (tF : F) ∉ P.w ∨ P.ramIdx = 1 := by
  by_cases ht : (tF : F) ∈ P.w
  · have hpr := polyIdeal_isPrime P ht
    obtain ⟨q, hqm, hqi, hqI⟩ := exists_monic_irreducible_mem (polyIdeal P ht)
      (polyIdeal_ne_bot P ht hB.1)
    have hqI' : Polynomial.aeval (tF : F) q ∈ P.w.nonunits := hqI
    by_cases hX : q = Polynomial.X
    · left
      rw [hX, Polynomial.aeval_X] at hqI'
      exact ⟨ht, hqI'⟩
    by_cases hX1 : q = Polynomial.X - 1
    · right; left
      rw [hX1, map_sub, Polynomial.aeval_X, map_one] at hqI'
      exact ⟨ht, hqI'⟩
    right; right; right
    have hgen := hB.2 P.w P.rat_mem ht q hqm hqi hX hX1 hqI'
    obtain ⟨π, hπ, hπu, hdvr⟩ := hD P ht
    set r : Qj := Polynomial.aeval (RatFunc.X / 1728 : Qj) q with hr
    have hrq : algebraMap Qj F r = Polynomial.aeval (tF : F) q := by
      rw [hr, algebraMap_aeval]
    have hr0 : r ≠ 0 := by
      intro h0
      have : Polynomial.aeval (tF : F) q = 0 := by rw [← hrq, h0, map_zero]
      exact hB.1 ⟨q, hqm.ne_zero, this⟩
    refine ramIdx_eq_one P π hπ hπu hdvr r hr0 (hrq ▸ hqI') ?_
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hgen x hx
    exact ⟨y, hy, hrq ▸ hxy⟩
  · right; right; left
    exact ht

/-- **`BelyiGenusBound` from Riemann–Hurwitz, the fundamental identity and the uniformizer leaf**
(proved). -/
theorem belyiGenusBound_of_leaves (hRH : RiemannHurwitzQj) (hFI : FundamentalIdentityQj)
    (hD : PlacesAreDVR) : BelyiGenusBound := by
  classical
  intro F _ _ _ _ hK hB
  obtain ⟨hsupp, hRHeq⟩ := hRH F hK
  set Z0 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits} with hZ0
  set Z1 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits} with hZ1
  set Zi : Set (Place F) := {P | (tF : F) ∉ P.w} with hZi
  obtain ⟨h0, hs0⟩ := hFI F Z0 (by simp [hZ0])
  obtain ⟨h1, hs1⟩ := hFI F Z1 (by simp [hZ1])
  obtain ⟨hi, hsi⟩ := hFI F Zi (by simp [hZi])
  set f : Place F → ℤ := fun P => ((P.ramIdx : ℤ) - 1) * P.deg with hf
  set A := h0.toFinset ∪ h1.toFinset ∪ hi.toFinset with hA
  have hsub : hsupp.toFinset ⊆ A := by
    intro P hP
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hP
    rcases place_cases hB hD P with h | h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)
    · exfalso
      apply hP
      show ((P.ramIdx : ℤ) - 1) * P.deg = 0
      rw [h]
      simp
  have hsum : ∑ P ∈ hsupp.toFinset, f P = ∑ P ∈ A, f P :=
    Finset.sum_subset hsub fun P _ hP => by
      rwa [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hP
  have hd01 : Disjoint h0.toFinset h1.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP0 hP1
    rw [Set.Finite.mem_toFinset] at hP0 hP1
    have h1n : (1 : F) ∈ P.w.nonunits := by
      have := P.w.nonunits.sub_mem hP0.2 hP1.2
      rwa [sub_sub_cancel] at this
    rw [ValuationSubring.mem_nonunits_iff, map_one] at h1n
    exact lt_irrefl _ h1n
  have hd : Disjoint (h0.toFinset ∪ h1.toFinset) hi.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP hPi
    rw [Set.Finite.mem_toFinset] at hPi
    rcases Finset.mem_union.mp hP with hP | hP <;> rw [Set.Finite.mem_toFinset] at hP
    · exact hPi hP.1
    · exact hPi hP.1
  rw [hA, Finset.sum_union hd, Finset.sum_union hd01] at hsum
  have hdpos : 0 < Module.finrank Qj F := Module.finrank_pos
  have part : ∀ (Z : Set (Place F)) (hZ : Z.Finite),
      ∑ P ∈ hZ.toFinset, P.ramIdx * P.deg = Module.finrank Qj F →
        ∑ P ∈ hZ.toFinset, f P ≤ (Module.finrank Qj F : ℤ) - 1 := by
    intro Z hZ hs
    have e1 : ∑ P ∈ hZ.toFinset, f P =
        ((∑ P ∈ hZ.toFinset, P.ramIdx * P.deg : ℕ) : ℤ) - ∑ P ∈ hZ.toFinset, (P.deg : ℤ) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun P _ => ?_
      simp only [hf]
      ring
    rw [e1, hs]
    obtain ⟨P, hP, hne⟩ : ∃ P ∈ hZ.toFinset, P.ramIdx * P.deg ≠ 0 := by
      by_contra hc
      push_neg at hc
      rw [Finset.sum_eq_zero hc] at hs
      omega
    have hdeg : 1 ≤ P.deg := Nat.pos_of_ne_zero fun h => hne (by rw [h, mul_zero])
    have : (1 : ℤ) ≤ ∑ P ∈ hZ.toFinset, (P.deg : ℤ) :=
      le_trans (by exact_mod_cast hdeg)
        (Finset.single_le_sum (f := fun P : Place F => (P.deg : ℤ)) (fun P _ => by positivity) hP)
    linarith
  have p0 := part Z0 h0 hs0
  have p1 := part Z1 h1 hs1
  have pi := part Zi hi hsi
  have key : 2 * (fieldGenus F : ℤ) + 1 ≤ Module.finrank Qj F := by
    have := hRHeq
    rw [hsum] at this
    linarith
  exact_mod_cast key

/-- **`DimJ1Le` (the use of T34) from textbook leaves and `X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_textbook (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj)
    (hFI : FundamentalIdentityQj) (hD : PlacesAreDVR) (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of_belyi h1 (belyiGenusBound_of_leaves hRH hFI hD) h0

end Glue3

section Glue4

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- **Places containing `j` are discrete valuation rings** (proved; replaces `PlacesAreDVR` where it
is used). With `R` the integral closure of `ℚ[j]` in `F` (a Dedekind domain with fraction field
`F`), `R ⊆ 𝒪_P`, `𝔭 = R ∩ 𝔪_P` is a nonzero prime, and a uniformizer of the DVR `R_𝔭 ⊆ 𝒪_P` is a
uniformizer of `𝒪_P`. -/
theorem exists_uniformizer [FiniteDimensional Qj F] (P : Place F) (ht : (tF : F) ∈ P.w) :
    ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup := by
  classical
  set v := P.w.valuation
  -- `j ∈ 𝒪_P`
  have hs : algebraMap Qj F RatFunc.X ∈ P.w := by
    have : algebraMap Qj F RatFunc.X = algebraMap ℚ F 1728 * (tF : F) := by
      rw [tF, ← algebraMap_rat_comp, RingHom.comp_apply, ← map_mul]
      congr 1
      rw [map_ofNat]
      field_simp
    rw [this]
    exact Subring.mul_mem _ (P.rat_mem _) ht
  letI : Algebra (Polynomial ℚ) F := ((algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
  have : IsScalarTower (Polynomial ℚ) Qj F := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsSeparable Qj F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  set R := integralClosure (Polynomial ℚ) F
  have : IsDedekindDomain R := integralClosure.isDedekindDomain (Polynomial ℚ) Qj F
  have : IsFractionRing R F :=
    IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial ℚ) Qj F R
  -- `ℚ[j] ⊆ 𝒪_P`
  have hpoly : ∀ p : Polynomial ℚ, algebraMap (Polynomial ℚ) F p ∈ P.w := by
    intro p
    have : algebraMap (Polynomial ℚ) F p = Polynomial.aeval (algebraMap Qj F RatFunc.X) p := by
      change (algebraMap Qj F) (algebraMap (Polynomial ℚ) Qj p) = _
      have h2 : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
          (Polynomial.aeval (algebraMap Qj F RatFunc.X)).toRingHom := by
        refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
        simp [RatFunc.algebraMap_X]
      exact congrArg (fun φ : Polynomial ℚ →+* F => φ p) h2
    rw [this]
    exact aeval_mem P hs p
  -- `R ⊆ 𝒪_P` (valuation rings are integrally closed)
  let φ : Polynomial ℚ →+* P.w := (algebraMap (Polynomial ℚ) F).codRestrict P.w.toSubring hpoly
  have hRw : ∀ r : R, (r : F) ∈ P.w := by
    rintro ⟨x, hx⟩
    obtain ⟨p, hpm, hp⟩ := hx
    have hint : IsIntegral P.w x := ⟨p.map φ, hpm.map φ, by
      rw [Polynomial.eval₂_map]; exact hp⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    show x ∈ P.w
    rw [← hy]; exact y.2
  -- the prime `𝔭 = R ∩ 𝔪_P`
  let ψ : R →+* P.w := (R.val.toRingHom).codRestrict P.w.toSubring hRw
  set 𝔭 : Ideal R := (IsLocalRing.maximalIdeal P.w).comap ψ with h𝔭def
  have h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hmem𝔭 : ∀ r : R, r ∈ 𝔭 ↔ (r : F) ∈ P.w.nonunits := by
    intro r
    rw [h𝔭def, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  have hunit : ∀ r : R, r ∉ 𝔭 → ((r : F))⁻¹ ∈ P.w := by
    intro r hr
    rw [hmem𝔭, ValuationSubring.mem_nonunits_iff_or] at hr
    push_neg at hr
    exact hr.2
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro hbot
    apply P.ne_top
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : b ∉ 𝔭 := by
      rw [hbot, Ideal.mem_bot]
      intro h; exact nonZeroDivisors.coe_ne_zero ⟨b, hb⟩ h
    rw [div_eq_mul_inv]
    exact Subring.mul_mem _ (hRw a) (hunit b hb0)
  -- the DVR `R_𝔭 ⊆ F`
  have hle : 𝔭.primeCompl ≤ nonZeroDivisors R := Ideal.primeCompl_le_nonZeroDivisors 𝔭
  set Rp := Localization.subalgebra.ofField F 𝔭.primeCompl hle with hRpdef
  have : IsLocalRing Rp := IsLocalization.AtPrime.isLocalRing Rp 𝔭
  have : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h𝔭ne Rp
  have hRpw : ∀ y : Rp, (y : F) ∈ P.w := by
    rintro ⟨y, hy⟩
    obtain ⟨a, b, hb, rfl⟩ := hy
    exact Subring.mul_mem _ (hRw a) (hunit b hb)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rp
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  -- units of `R_𝔭` are units of `𝒪_P`
  have hU : ∀ u : Rpˣ, v ((u : Rp) : F) = 1 := by
    intro u
    have h1 : v ((u : Rp) : F) ≤ 1 := (P.w.valuation_le_one_iff _).mpr (hRpw u)
    have h2 : v (((u⁻¹ : Rpˣ) : Rp) : F) ≤ 1 := (P.w.valuation_le_one_iff _).mpr (hRpw _)
    have h3 : ((u : Rp) : F) * (((u⁻¹ : Rpˣ) : Rp) : F) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have h4 : v ((u : Rp) : F) * v (((u⁻¹ : Rpˣ) : Rp) : F) = 1 := by rw [← map_mul, h3, map_one]
    by_contra hne
    have hlt : v ((u : Rp) : F) < 1 := lt_of_le_of_ne h1 hne
    have : v ((u : Rp) : F) * v (((u⁻¹ : Rpˣ) : Rp) : F) < 1 :=
      lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt h2) le_rfl
    rw [h4] at this
    exact lt_irrefl _ this
  refine ⟨Units.mk0 (ϖ : F) hϖ0, hRpw ϖ, ?_, ?_⟩
  · -- `ϖ ∈ 𝔪_P`
    rw [ValuationSubring.mem_unitGroup_iff]
    obtain ⟨⟨a, s'⟩, hϖeq⟩ := IsLocalization.mk'_surjective (S := Rp) 𝔭.primeCompl ϖ
    have hϖmax : ϖ ∈ IsLocalRing.maximalIdeal Rp :=
      (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
    rw [← hϖeq, IsLocalization.AtPrime.mk'_mem_maximal_iff Rp 𝔭] at hϖmax
    have hϖeq' : IsLocalization.mk' Rp a s' = ϖ := hϖeq
    have hspec := IsLocalization.mk'_spec Rp a s'
    rw [hϖeq'] at hspec
    have hF : (ϖ : F) * ((s' : R) : F) = ((a : R) : F) := congrArg Subtype.val hspec
    have ha : v ((a : R) : F) < 1 := (P.w.mem_nonunits_iff).mp ((hmem𝔭 a).mp hϖmax)
    have hs1 : v ((s' : R) : F) = 1 := by
      have h1 : v ((s' : R) : F) ≤ 1 := (P.w.valuation_le_one_iff _).mpr (hRw s')
      have h2 : ((s' : R) : F) ∉ P.w.nonunits := (hmem𝔭 s').not.mp s'.2
      rw [ValuationSubring.mem_nonunits_iff, not_lt] at h2
      exact le_antisymm h1 h2
    intro hv
    have : v ((a : R) : F) = 1 := by
      rw [← hF, map_mul, hs1, mul_one]
      exact hv
    rw [this] at ha
    exact lt_irrefl _ ha
  · intro x
    obtain ⟨a, b, hb, hab0⟩ := IsFractionRing.div_surjective (A := Rp) (x : F)
    have hab : ((a : Rp) : F) / ((b : Rp) : F) = x := hab0
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Subalgebra.coe_zero, zero_div] at hab
      exact x.ne_zero hab.symm
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    obtain ⟨n, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨(m : ℤ) - n, ?_⟩
    rw [ValuationSubring.mem_unitGroup_iff]
    have hxe : ((x * Units.mk0 (ϖ : F) hϖ0 ^ (-((m : ℤ) - n)) : Fˣ) : F) =
        ((u : Rp) : F) * (((u' : Rp) : F))⁻¹ := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, ← hab, hu, hu']
      push_cast
      have hu0 : ((u' : Rp) : F) ≠ 0 := fun h => u'.ne_zero (Subtype.ext h)
      rw [neg_sub, zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast]
      field_simp
    rw [hxe, map_mul, map_inv₀, hU, hU, inv_one, mul_one]

/-- **`BelyiGenusBound` from Riemann–Hurwitz and the fundamental identity** (proved; the uniformizers
at the places containing `t` are `exists_uniformizer`). -/
theorem belyiGenusBound_of_rh_fi (hRH : RiemannHurwitzQj) (hFI : FundamentalIdentityQj) :
    BelyiGenusBound := by
  classical
  intro F _ _ _ _ hK hB
  obtain ⟨hsupp, hRHeq⟩ := hRH F hK
  set Z0 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits} with hZ0
  set Z1 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits} with hZ1
  set Zi : Set (Place F) := {P | (tF : F) ∉ P.w} with hZi
  obtain ⟨h0, hs0⟩ := hFI F Z0 (by simp [hZ0])
  obtain ⟨h1, hs1⟩ := hFI F Z1 (by simp [hZ1])
  obtain ⟨hi, hsi⟩ := hFI F Zi (by simp [hZi])
  set f : Place F → ℤ := fun P => ((P.ramIdx : ℤ) - 1) * P.deg with hf
  set A := h0.toFinset ∪ h1.toFinset ∪ hi.toFinset with hA
  have hsub : hsupp.toFinset ⊆ A := by
    intro P hP
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hP
    rcases place_cases' hB (fun P ht => exists_uniformizer P ht) P with h | h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)
    · exfalso
      apply hP
      show ((P.ramIdx : ℤ) - 1) * P.deg = 0
      rw [h]
      simp
  have hsum : ∑ P ∈ hsupp.toFinset, f P = ∑ P ∈ A, f P :=
    Finset.sum_subset hsub fun P _ hP => by
      rwa [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hP
  have hd01 : Disjoint h0.toFinset h1.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP0 hP1
    rw [Set.Finite.mem_toFinset] at hP0 hP1
    have h1n : (1 : F) ∈ P.w.nonunits := by
      have := P.w.nonunits.sub_mem hP0.2 hP1.2
      rwa [sub_sub_cancel] at this
    rw [ValuationSubring.mem_nonunits_iff, map_one] at h1n
    exact lt_irrefl _ h1n
  have hd : Disjoint (h0.toFinset ∪ h1.toFinset) hi.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP hPi
    rw [Set.Finite.mem_toFinset] at hPi
    rcases Finset.mem_union.mp hP with hP | hP <;> rw [Set.Finite.mem_toFinset] at hP
    · exact hPi hP.1
    · exact hPi hP.1
  rw [hA, Finset.sum_union hd, Finset.sum_union hd01] at hsum
  have hdpos : 0 < Module.finrank Qj F := Module.finrank_pos
  have part : ∀ (Z : Set (Place F)) (hZ : Z.Finite),
      ∑ P ∈ hZ.toFinset, P.ramIdx * P.deg = Module.finrank Qj F →
        ∑ P ∈ hZ.toFinset, f P ≤ (Module.finrank Qj F : ℤ) - 1 := by
    intro Z hZ hs
    have e1 : ∑ P ∈ hZ.toFinset, f P =
        ((∑ P ∈ hZ.toFinset, P.ramIdx * P.deg : ℕ) : ℤ) - ∑ P ∈ hZ.toFinset, (P.deg : ℤ) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun P _ => ?_
      simp only [hf]
      ring
    rw [e1, hs]
    obtain ⟨P, hP, hne⟩ : ∃ P ∈ hZ.toFinset, P.ramIdx * P.deg ≠ 0 := by
      by_contra hc
      push_neg at hc
      rw [Finset.sum_eq_zero hc] at hs
      omega
    have hdeg : 1 ≤ P.deg := Nat.pos_of_ne_zero fun h => hne (by rw [h, mul_zero])
    have : (1 : ℤ) ≤ ∑ P ∈ hZ.toFinset, (P.deg : ℤ) :=
      le_trans (by exact_mod_cast hdeg)
        (Finset.single_le_sum (f := fun P : Place F => (P.deg : ℤ)) (fun P _ => by positivity) hP)
    linarith
  have p0 := part Z0 h0 hs0
  have p1 := part Z1 h1 hs1
  have pi := part Zi hi hsi
  have key : 2 * (fieldGenus F : ℤ) + 1 ≤ Module.finrank Qj F := by
    have := hRHeq
    rw [hsum] at this
    linarith
  exact_mod_cast key

/-- **`DimJ1Le` (the use of T34) from `DimJacobianEqGenus`, Riemann–Hurwitz, the fundamental
identity and `X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_rh_fi (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj)
    (hFI : FundamentalIdentityQj) (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of_belyi h1 (belyiGenusBound_of_rh_fi hRH hFI) h0

end Glue4

/-! ## `FundamentalIdentityQj` from Mathlib's fundamental identity for Dedekind domains -/

section Glue5

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F]

/-- The coordinate `j` in `F`. -/
abbrev sF : F := algebraMap Qj F RatFunc.X

theorem algebraMap_poly_eq (p : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) F p = Polynomial.aeval (sF : F) p := by
  rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) Qj F]
  have h2 : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
      (Polynomial.aeval (sF : F)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    simp [RatFunc.algebraMap_X]
  exact congrArg (fun φ : Polynomial ℚ →+* F => φ p) h2

/-- The integral closure of `ℚ[j]` lies in every place containing `j`. -/
theorem intCl_mem (P : Place F) (hs : (sF : F) ∈ P.w) (r : integralClosure (Polynomial ℚ) F) :
    (r : F) ∈ P.w := by
  have hpoly : ∀ p : Polynomial ℚ, algebraMap (Polynomial ℚ) F p ∈ P.w := fun p => by
    rw [algebraMap_poly_eq]; exact aeval_mem P hs p
  let φ : Polynomial ℚ →+* P.w := (algebraMap (Polynomial ℚ) F).codRestrict P.w.toSubring hpoly
  obtain ⟨x, hx⟩ := r
  obtain ⟨p, hpm, hp⟩ := hx
  have hint : IsIntegral P.w x := ⟨p.map φ, hpm.map φ, by
    rw [Polynomial.eval₂_map]; exact hp⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  show x ∈ P.w
  rw [← hy]; exact y.2

theorem isSeparable_Qj [FiniteDimensional Qj F] : Algebra.IsSeparable Qj F :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem isDedekind_intCl [FiniteDimensional Qj F] :
    IsDedekindDomain (integralClosure (Polynomial ℚ) F) :=
  haveI := isSeparable_Qj (F := F)
  integralClosure.isDedekindDomain (Polynomial ℚ) Qj F

theorem isFractionRing_intCl [FiniteDimensional Qj F] :
    IsFractionRing (integralClosure (Polynomial ℚ) F) F :=
  haveI := isSeparable_Qj (F := F)
  IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial ℚ) Qj F _

attribute [local instance] isDedekind_intCl isFractionRing_intCl

variable [FiniteDimensional Qj F]

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- The center on `OF` of a place containing `j`, a height-one prime. -/
noncomputable def centerHS (P : Place F) (hs : (sF : F) ∈ P.w) : HeightOneSpectrum OF where
  asIdeal := (IsLocalRing.maximalIdeal P.w).comap
    ((OF).val.toRingHom.codRestrict P.w.toSubring (intCl_mem P hs))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro hbot
    apply P.ne_top
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OF) x
    have hb0 : (b : F) ∉ P.w.nonunits := by
      intro h
      have : b ∈ (IsLocalRing.maximalIdeal P.w).comap
          ((OF).val.toRingHom.codRestrict P.w.toSubring (intCl_mem P hs)) := by
        rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; exact h
      rw [hbot, Ideal.mem_bot] at this
      exact nonZeroDivisors.coe_ne_zero ⟨b, hb⟩ this
    rw [ValuationSubring.mem_nonunits_iff_or] at hb0
    push_neg at hb0
    rw [div_eq_mul_inv]
    exact Subring.mul_mem _ (intCl_mem P hs a) hb0.2

theorem mem_centerHS (P : Place F) (hs : (sF : F) ∈ P.w) (r : OF) :
    r ∈ (centerHS P hs).asIdeal ↔ (r : F) ∈ P.w.nonunits := by
  change r ∈ Ideal.comap _ _ ↔ _
  rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

/-- A place containing `j` is the valuation ring of its center. -/
theorem w_eq_valuationSubring (P : Place F) (hs : (sF : F) ∈ P.w) :
    P.w = ((centerHS P hs).valuation F).valuationSubring := by
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  symm
  refine ValuationSubring.eq_of_le_of_ne_top _ ?_ P.ne_top
  rintro x hx
  obtain ⟨a, b, hb, rfl⟩ := hx
  have hb0 : (b : F) ∉ P.w.nonunits := (mem_centerHS P hs b).not.mp hb
  rw [ValuationSubring.mem_nonunits_iff_or] at hb0
  push_neg at hb0
  exact Subring.mul_mem _ (intCl_mem P hs a) hb0.2

/-- The place of a height-one prime of `OF`. -/
noncomputable def placeOf (w : HeightOneSpectrum OF) : Place F where
  w := (w.valuation F).valuationSubring
  ne_top := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]; infer_instance
  rat_mem c := by
    have hr : ((Polynomial.C c : Polynomial ℚ) : Polynomial ℚ) ∈ (⊤ : Subalgebra (Polynomial ℚ) (Polynomial ℚ)) :=
      trivial
    let r : OF := algebraMap (Polynomial ℚ) OF (Polynomial.C c)
    have : algebraMap ℚ F c = algebraMap OF F r := by
      change _ = algebraMap (Polynomial ℚ) F (Polynomial.C c)
      rw [algebraMap_poly_eq, Polynomial.aeval_C]
    rw [this]
    exact (Valuation.mem_valuationSubring_iff _ _).mpr (HeightOneSpectrum.valuation_le_one _ _)

theorem sF_mem_placeOf (w : HeightOneSpectrum OF) : (sF : F) ∈ (placeOf w).w := by
  have : (sF : F) = algebraMap OF F (algebraMap (Polynomial ℚ) OF Polynomial.X) := by
    change _ = algebraMap (Polynomial ℚ) F Polynomial.X
    rw [algebraMap_poly_eq, Polynomial.aeval_X]
  rw [this]
  exact (Valuation.mem_valuationSubring_iff _ _).mpr (HeightOneSpectrum.valuation_le_one _ _)

theorem placeOf_centerHS (P : Place F) (hs : (sF : F) ∈ P.w) : placeOf (centerHS P hs) = P :=
  Place.ext' (w_eq_valuationSubring P hs).symm

theorem centerHS_placeOf (w : HeightOneSpectrum OF) :
    centerHS (placeOf w) (sF_mem_placeOf w) = w := by
  ext r
  rw [mem_centerHS, ValuationSubring.mem_nonunits_iff_or,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  change (r : F) = 0 ∨ ((r : F))⁻¹ ∉ (w.valuation F).valuationSubring ↔ _
  rw [Valuation.mem_valuationSubring_iff, map_inv₀, not_le]
  by_cases hr : (r : F) = 0
  · have : algebraMap OF F r = 0 := hr
    simp [hr, this]
  · have h0 : w.valuation F (algebraMap OF F r) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact hr
    change _ ↔ w.valuation F (r : F) < 1
    rw [one_lt_inv_iff₀]
    simp only [hr, false_or]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨zero_lt_iff.mpr h0, h⟩

/-- The prime `(j − a)` of `ℚ[j]`. -/
noncomputable abbrev pa (a : ℚ) : Ideal (Polynomial ℚ) := Ideal.span {Polynomial.X - Polynomial.C a}

theorem pa_isMaximal (a : ℚ) : (pa a).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Polynomial.irreducible_X_sub_C a)

theorem pa_ne_bot (a : ℚ) : pa a ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact Polynomial.X_sub_C_ne_zero a

/-- The places over `j = a`. -/
def Zfin (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] (a : ℚ) : Set (Place F) :=
  {P | (sF : F) ∈ P.w ∧ (sF : F) - algebraMap ℚ F a ∈ P.w.nonunits}

theorem algebraMap_X_sub_C (a : ℚ) :
    ((algebraMap (Polynomial ℚ) OF (Polynomial.X - Polynomial.C a) : OF) : F) =
      (sF : F) - algebraMap ℚ F a := by
  have : ((algebraMap (Polynomial ℚ) OF (Polynomial.X - Polynomial.C a) : OF) : F) =
      algebraMap (Polynomial ℚ) F (Polynomial.X - Polynomial.C a) := rfl
  rw [this, algebraMap_poly_eq, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]

theorem placeOf_mem_Zfin_iff (a : ℚ) (w : HeightOneSpectrum OF) :
    placeOf w ∈ Zfin F a ↔ w.asIdeal ∈ (pa a).primesOver OF := by
  have hpm := pa_isMaximal a
  have key : (sF : F) - algebraMap ℚ F a ∈ (placeOf w).w.nonunits ↔
      algebraMap (Polynomial ℚ) OF (Polynomial.X - Polynomial.C a) ∈ w.asIdeal := by
    conv_rhs => rw [← centerHS_placeOf w]
    rw [mem_centerHS, algebraMap_X_sub_C]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨w.isPrime, ⟨?_⟩⟩
    have hle : pa a ≤ w.asIdeal.under (Polynomial ℚ) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact key.mp h
    exact hpm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  · rintro ⟨-, hlo⟩
    refine ⟨sF_mem_placeOf w, key.mpr ?_⟩
    have : Polynomial.X - Polynomial.C a ∈ w.asIdeal.under (Polynomial ℚ) := by
      rw [← hlo.over]; exact Ideal.subset_span rfl
    exact this

theorem faithful_intCl : FaithfulSMul (Polynomial ℚ) OF := by
  have hinjF : Function.Injective (algebraMap (Polynomial ℚ) F) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial ℚ) Qj F]
    exact (algebraMap Qj F).injective.comp (IsFractionRing.injective (Polynomial ℚ) Qj)
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply hinjF
  exact congrArg (fun z : OF => (z : F)) hxy

/-- `ℤᵐ⁰ˣ` is generated by `exp (-1)`, of infinite order. -/
theorem zpowers_exp_neg_one :
    Subgroup.zpowers (Units.mk0 (WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  refine ⟨-WithZero.log (u : WithZero (Multiplicative ℤ)), ?_⟩
  ext
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [← WithZero.exp_zsmul, show (-WithZero.log (u : WithZero (Multiplicative ℤ))) • (-1 : ℤ) =
    WithZero.log (u : WithZero (Multiplicative ℤ)) by simp, WithZero.exp_log u.ne_zero]

theorem orderOf_exp_neg_one :
    orderOf (Units.mk0 (WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero) = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn h
  have h2 := congrArg (fun u : (WithZero (Multiplicative ℤ))ˣ => (u : WithZero (Multiplicative ℤ))) h
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h2
  rw [← WithZero.exp_nsmul, ← WithZero.exp_zero] at h2
  have h3 := WithZero.exp_injective h2
  simp at h3
  omega

/-- `e_P` is Mathlib's ramification index. -/
theorem ramIdx_placeOf (a : ℚ) (w : HeightOneSpectrum OF) (hw : w.asIdeal ∈ (pa a).primesOver OF) :
    (placeOf w).ramIdx = Ideal.ramificationIdx' (pa a) w.asIdeal := by
  have hlo : w.asIdeal.LiesOver (pa a) := hw.2
  have := faithful_intCl (F := F)
  have : Module.IsTorsionFree (Polynomial ℚ) OF := inferInstance
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (pa a) w.asIdeal (pa_ne_bot a)]
  set e := w.asIdeal.ramificationIdx (Polynomial ℚ) with he
  let vp : HeightOneSpectrum (Polynomial ℚ) := ⟨pa a, (pa_isMaximal a).isPrime, pa_ne_bot a⟩
  have : w.asIdeal.LiesOver vp.asIdeal := hlo
  have hlies : ∀ x : Qj, vp.valuation Qj x ^ e = w.valuation F (algebraMap Qj F x) :=
    fun x => HeightOneSpectrum.valuation_liesOver F vp w x
  let v := w.valuation F
  let φ : Fˣ →* (WithZero (Multiplicative ℤ))ˣ := Units.map (v : F →*₀ WithZero (Multiplicative ℤ))
  have hφ : ∀ x : Fˣ, (φ x : WithZero (Multiplicative ℤ)) = v x := fun x => rfl
  have hker : φ.ker = (placeOf w).w.unitGroup := by
    ext x
    rw [MonoidHom.mem_ker, Units.ext_iff, hφ, Units.val_one]
    exact (Valuation.mem_unitGroup_iff (v := v) (x := x)).symm
  have hsurj : Function.Surjective φ := by
    intro u
    obtain ⟨x, hx⟩ := HeightOneSpectrum.valuation_surjective (K := F) w (u : WithZero (Multiplicative ℤ))
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact u.ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext (by rw [hφ]; exact hx)⟩
  set Rg := (Units.map (algebraMap Qj F : Qj →* F)).range with hRg
  have hH : (placeOf w).w.unitGroup ⊔ Rg = (Subgroup.map φ Rg).comap φ := by
    rw [Subgroup.comap_map_eq, hker, sup_comm]
  set g : (WithZero (Multiplicative ℤ))ˣ := Units.mk0 (WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero
  have hmap : Subgroup.map φ Rg = Subgroup.zpowers (g ^ (e : ℤ)) := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      have hy0 : vp.valuation Qj (y : Qj) ≠ 0 := by
        rw [Valuation.ne_zero_iff]; exact y.ne_zero
      obtain ⟨n, hn⟩ : (Units.mk0 _ hy0) ∈ Subgroup.zpowers g := by
        rw [zpowers_exp_neg_one]; trivial
      refine ⟨n, Units.ext ?_⟩
      simp only [Units.val_zpow_eq_zpow_val] at hn ⊢
      rw [hφ]
      change _ = v (algebraMap Qj F (y : Qj))
      rw [← hlies, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      have hn' := congrArg (fun u : (WithZero (Multiplicative ℤ))ˣ => (u : WithZero (Multiplicative ℤ))) hn
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hn'
      rw [hn']
    · rw [Subgroup.zpowers_le]
      obtain ⟨π, hπ⟩ := vp.valuation_exists_uniformizer Qj
      have hπ0 : π ≠ 0 := by
        rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
      refine ⟨Units.map (algebraMap Qj F : Qj →* F) (Units.mk0 π hπ0), ⟨_, rfl⟩, Units.ext ?_⟩
      rw [hφ]
      change v (algebraMap Qj F π) = _
      rw [← hlies, hπ, Units.val_zpow_eq_zpow_val, Units.val_mk0, zpow_natCast]
  rw [Place.ramIdx, hH, Subgroup.index_comap_of_surjective _ hsurj, hmap,
    Subgroup.index_zpowers_zpow zpowers_exp_neg_one, orderOf_exp_neg_one]
  simp

/-- `deg P` is Mathlib's inertia degree. -/
theorem deg_placeOf (a : ℚ) (w : HeightOneSpectrum OF) (hw : w.asIdeal ∈ (pa a).primesOver OF) :
    (placeOf w).deg = Ideal.inertiaDeg' (pa a) w.asIdeal := by
  have hlo : w.asIdeal.LiesOver (pa a) := hw.2
  have hmax : w.asIdeal.IsMaximal := w.isMaximal
  have hpm := pa_isMaximal a
  have hc : Ideal.comap (algebraMap (Polynomial ℚ) OF) w.asIdeal = pa a := hlo.over.symm
  rw [Ideal.inertiaDeg', dif_pos hc]
  let A := HeightOneSpectrum.valuationSubringAtPrime F w
  have hAB : A = (w.valuation F).valuationSubring :=
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring w
  let e1 : A ≃+* (placeOf w).w := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hAB)
  let e2 : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField (placeOf w).w :=
    IsLocalRing.ResidueField.mapEquiv e1
  let e3 : (OF ⧸ w.asIdeal) ≃+* IsLocalRing.ResidueField A :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal w.asIdeal A).toRingEquiv
  let j : IsLocalRing.ResidueField (placeOf w).w ≃+* OF ⧸ w.asIdeal := (e3.trans e2).symm
  let i : ℚ ≃+* Polynomial ℚ ⧸ pa a := (Polynomial.quotientSpanXSubCAlgEquiv a).symm.toRingEquiv
  letI := (placeOf w).ratHom.toAlgebra
  exact Algebra.finrank_eq_of_equiv_equiv i j (RingHom.ext_rat _ _)

theorem centerHS_congr {P Q : Place F} (h : P = Q) (hP : (sF : F) ∈ P.w) (hQ : (sF : F) ∈ Q.w) :
    centerHS P hP = centerHS Q hQ := by
  subst h; rfl

/-- **The fundamental identity at `j = a`** (proved from Mathlib's for Dedekind domains). -/
theorem fundamentalIdentity_fin (a : ℚ) :
    ∃ h : (Zfin F a).Finite, ∑ P ∈ h.toFinset, P.ramIdx * P.deg = Module.finrank Qj F := by
  classical
  have hpm := pa_isMaximal a
  have hp0 := pa_ne_bot a
  have hinjF : Function.Injective (algebraMap (Polynomial ℚ) F) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial ℚ) Qj F]
    exact (algebraMap Qj F).injective.comp (IsFractionRing.injective (Polynomial ℚ) Qj)
  have : FaithfulSMul (Polynomial ℚ) OF := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply hinjF
    have h1 := congrArg (fun z : OF => (z : F)) hxy
    exact h1
  have : Module.IsTorsionFree (Polynomial ℚ) OF := inferInstance
  have : Module.Finite (Polynomial ℚ) OF := by
    have := isSeparable_Qj (F := F)
    exact IsIntegralClosure.finite (Polynomial ℚ) Qj F OF
  set S := IsDedekindDomain.primesOverFinset (pa a) OF with hS
  have hmemS : ∀ 𝔓, 𝔓 ∈ S ↔ 𝔓 ∈ (pa a).primesOver OF := fun 𝔓 =>
    IsDedekindDomain.mem_primesOverFinset_iff hp0 OF
  let G : ∀ 𝔓 ∈ S, Place F := fun 𝔓 h𝔓 =>
    placeOf ⟨𝔓, ((hmemS 𝔓).mp h𝔓).1, by
      have := ((hmemS 𝔓).mp h𝔓).2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot hp0 𝔓⟩
  have hG : ∀ 𝔓 h𝔓, G 𝔓 h𝔓 ∈ Zfin F a := fun 𝔓 h𝔓 =>
    (placeOf_mem_Zfin_iff a _).mpr ((hmemS 𝔓).mp h𝔓)
  have hZ : Zfin F a = Set.range (fun x : S => G x.1 x.2) := by
    ext P
    constructor
    · intro hP
      have hs := hP.1
      set w := centerHS P hs
      have hPw : placeOf w = P := placeOf_centerHS P hs
      have hw : w.asIdeal ∈ S := (hmemS _).mpr ((placeOf_mem_Zfin_iff a w).mp (hPw ▸ hP))
      refine ⟨⟨w.asIdeal, hw⟩, ?_⟩
      show placeOf _ = P
      convert hPw
    · rintro ⟨x, rfl⟩
      exact hG x.1 x.2
  have hfin : (Zfin F a).Finite := hZ ▸ Set.finite_range _
  refine ⟨hfin, ?_⟩
  rw [← Ideal.sum_ramification_inertia (S := OF) (p := pa a) Qj F hp0]
  symm
  refine Finset.sum_bij G (fun 𝔓 h𝔓 => (Set.Finite.mem_toFinset _).mpr (hG 𝔓 h𝔓)) ?_ ?_ ?_
  · intro 𝔓₁ h₁ 𝔓₂ h₂ he
    have := centerHS_congr he (sF_mem_placeOf _) (sF_mem_placeOf _)
    rw [centerHS_placeOf, centerHS_placeOf] at this
    exact congrArg HeightOneSpectrum.asIdeal this
  · intro P hP
    rw [Set.Finite.mem_toFinset, hZ] at hP
    obtain ⟨⟨𝔓, h𝔓⟩, rfl⟩ := hP
    exact ⟨𝔓, h𝔓, rfl⟩
  · intro 𝔓 h𝔓
    rw [ramIdx_placeOf a _ ((hmemS 𝔓).mp h𝔓), deg_placeOf a _ ((hmemS 𝔓).mp h𝔓)]

end Glue5

section Twist

theorem invX_hφ : (nonZeroDivisors (Polynomial ℚ)) ≤
    (nonZeroDivisors Qj).comap (Polynomial.aeval (RatFunc.X⁻¹ : Qj) : Polynomial ℚ →ₐ[ℚ] Qj).toRingHom := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h0
  have h : IsAlgebraic ℚ (RatFunc.X⁻¹ : Qj) := ⟨p, nonZeroDivisors.ne_zero hp, h0⟩
  apply RatFunc.transcendental_X (K := ℚ)
  convert IsAlgebraic.inv_iff.mp h
  exact Subsingleton.elim _ _

/-- `j ↦ 1/j` on `ℚ(j)`. -/
noncomputable def invXHom : Qj →+* Qj :=
  RatFunc.liftRingHom (Polynomial.aeval (RatFunc.X⁻¹ : Qj) : Polynomial ℚ →ₐ[ℚ] Qj).toRingHom invX_hφ

theorem invXHom_algebraMap (p : Polynomial ℚ) :
    invXHom (algebraMap (Polynomial ℚ) Qj p) = Polynomial.aeval (RatFunc.X⁻¹ : Qj) p := by
  have := RatFunc.liftRingHom_apply_div'
    (φ := (Polynomial.aeval (RatFunc.X⁻¹ : Qj) : Polynomial ℚ →ₐ[ℚ] Qj).toRingHom)
    (hφ := invX_hφ) p 1
  simpa [invXHom] using this

theorem invXHom_X : invXHom (RatFunc.X : Qj) = RatFunc.X⁻¹ := by
  have := invXHom_algebraMap Polynomial.X
  rwa [RatFunc.algebraMap_X, Polynomial.aeval_X] at this

theorem invXHom_invXHom (x : Qj) : invXHom (invXHom x) = x := by
  have h : (invXHom.comp invXHom).comp (algebraMap (Polynomial ℚ) Qj) =
      (RingHom.id Qj).comp (algebraMap (Polynomial ℚ) Qj) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, RatFunc.algebraMap_X,
      invXHom_X, map_inv₀, inv_inv]
  exact congrArg (fun φ : Qj →+* Qj => φ x)
    (IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℚ)) h)

/-- `j ↦ 1/j` as a ring automorphism. -/
noncomputable def invXEquiv : Qj ≃+* Qj :=
  RingEquiv.ofRingHom invXHom invXHom
    (RingHom.ext fun x => invXHom_invXHom x) (RingHom.ext fun x => invXHom_invXHom x)

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F]

/-- The twisted `ℚ(j)`-algebra structure `c · x = (1/j ↦ ...)`: `j` acts as `1/j`. -/
@[reducible] noncomputable def twistAlg : Algebra Qj F :=
  ((algebraMap Qj F).comp invXEquiv.toRingHom).toAlgebra

theorem twist_finrank :
    @Module.finrank Qj F _ _ (twistAlg (F := F)).toModule = Module.finrank Qj F :=
  @Algebra.finrank_eq_of_equiv_equiv Qj F _ _ (twistAlg (F := F)) Qj F _ _ _ invXEquiv
    (RingEquiv.refl F) rfl

theorem twist_finiteDimensional : @FiniteDimensional Qj F _ _ (twistAlg (F := F)).toModule := by
  have h0 : 0 < @Module.finrank Qj F _ _ (twistAlg (F := F)).toModule := by
    rw [twist_finrank]; exact Module.finrank_pos
  exact @FiniteDimensional.of_finrank_pos Qj F _ _ (twistAlg (F := F)).toModule h0

theorem twist_ramIdx (P : Place F) : @Place.ramIdx F _ (twistAlg (F := F)) _ P = P.ramIdx := by
  unfold Place.ramIdx
  congr 2
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Units.map invXEquiv.toRingHom.toMonoidHom y, Units.ext rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map invXEquiv.toRingHom.toMonoidHom y, Units.ext ?_⟩
    change (algebraMap Qj F) (invXEquiv (invXEquiv (y : Qj))) = _
    rw [show invXEquiv (invXEquiv (y : Qj)) = (y : Qj) from invXHom_invXHom _]
    rfl

end Twist

section FI

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

theorem mul_rat_mem_iff (P : Place F) {c : ℚ} (hc : c ≠ 0) (x : F) :
    (algebraMap ℚ F c * x ∈ P.w ↔ x ∈ P.w) ∧
      (algebraMap ℚ F c * x ∈ P.w.nonunits ↔ x ∈ P.w.nonunits) := by
  have hv : P.w.valuation (algebraMap ℚ F c) = 1 := by
    have h1 := (P.w.valuation_le_one_iff _).mpr (P.rat_mem c)
    have h2 := (P.w.valuation_le_one_iff _).mpr (P.rat_mem c⁻¹)
    rw [map_inv₀, map_inv₀] at h2
    have h0 : P.w.valuation (algebraMap ℚ F c) ≠ 0 := by
      rw [Valuation.ne_zero_iff, map_ne_zero_iff _ (algebraMap ℚ F).injective]; exact hc
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)
  refine ⟨?_, ?_⟩
  · rw [← P.w.valuation_le_one_iff, ← P.w.valuation_le_one_iff, map_mul, hv, one_mul]
  · rw [ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff, map_mul, hv, one_mul]

end FI

section FIfinal

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

theorem tF_eq_mul : (tF : F) = algebraMap ℚ F (1 / 1728) * (sF : F) := by
  rw [tF, sF, ← algebraMap_rat_comp, RingHom.comp_apply, ← map_mul]
  congr 1
  rw [map_div₀, map_one, map_ofNat]
  ring

theorem tF_sub_one_eq_mul :
    (tF : F) - 1 = algebraMap ℚ F (1 / 1728) * ((sF : F) - algebraMap ℚ F 1728) := by
  rw [tF_eq_mul, mul_sub, ← map_mul]
  norm_num

/-- The fundamental identity at a finite place, with the `ℚ[j]`-structure built in. -/
theorem fundamentalIdentity_fin' [FiniteDimensional Qj F] (a : ℚ) :
    ∃ h : (Zfin F a).Finite, ∑ P ∈ h.toFinset, P.ramIdx * P.deg = Module.finrank Qj F := by
  letI : Algebra (Polynomial ℚ) F :=
    ((algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
  have : IsScalarTower (Polynomial ℚ) Qj F := IsScalarTower.of_algebraMap_eq' rfl
  exact fundamentalIdentity_fin a

theorem sF_twist : @sF F _ (twistAlg (F := F)) = (sF : F)⁻¹ := by
  show (algebraMap Qj F) (invXEquiv RatFunc.X) = (sF : F)⁻¹
  rw [show invXEquiv (RatFunc.X : Qj) = RatFunc.X⁻¹ from invXHom_X, map_inv₀]

theorem zfin_twist : @Zfin F _ (twistAlg (F := F)) _ 0 = {P : Place F | (tF : F) ∉ P.w} := by
  have hsF0 : (sF : F) ≠ 0 := by
    rw [sF, map_ne_zero_iff _ (algebraMap Qj F).injective]; exact RatFunc.X_ne_zero
  ext P
  show (@sF F _ (twistAlg (F := F)) ∈ P.w ∧ @sF F _ (twistAlg (F := F)) - algebraMap ℚ F 0 ∈
    P.w.nonunits) ↔ (tF : F) ∉ P.w
  rw [sF_twist, map_zero, sub_zero, tF_eq_mul, (mul_rat_mem_iff P (by norm_num) _).1]
  constructor
  · rintro ⟨-, h2⟩
    rw [ValuationSubring.inv_mem_nonunits_iff] at h2
    exact h2.resolve_left hsF0
  · intro h2
    have h3 : (sF : F)⁻¹ ∈ P.w.nonunits := (P.w.inv_mem_nonunits_iff).mpr (Or.inr h2)
    exact ⟨P.w.nonunits_subset h3, h3⟩

/-- **The fundamental identity at `j = ∞`** (proved: the fundamental identity at `j = 0` for the
twisted structure `j ↦ 1/j`). -/
theorem fundamentalIdentity_inf [FiniteDimensional Qj F] :
    ∃ h : {P : Place F | (tF : F) ∉ P.w}.Finite,
      ∑ P ∈ h.toFinset, P.ramIdx * P.deg = Module.finrank Qj F := by
  obtain ⟨h, hs⟩ := @fundamentalIdentity_fin' F _ (twistAlg (F := F)) _ twist_finiteDimensional 0
  have h' : {P : Place F | (tF : F) ∉ P.w}.Finite := zfin_twist (F := F) ▸ h
  refine ⟨h', ?_⟩
  have hfs : h'.toFinset = h.toFinset := by
    ext P
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, zfin_twist]
  rw [hfs, ← twist_finrank, ← hs]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [twist_ramIdx]

/-- **`FundamentalIdentityQj`, proved** (from Mathlib's fundamental identity for Dedekind domains). -/
theorem fundamentalIdentityQj : FundamentalIdentityQj := by
  intro F _ _ _ _ Z hZ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
  rcases hZ with rfl | rfl | rfl
  · have hZ0 : {P : Place F | (tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits} = Zfin F 0 := by
      ext P
      simp only [Zfin, Set.mem_setOf_eq, map_zero, sub_zero]
      rw [tF_eq_mul, (mul_rat_mem_iff P (by norm_num) _).1, (mul_rat_mem_iff P (by norm_num) _).2]
    rw [hZ0]
    exact fundamentalIdentity_fin' 0
  · have hZ1 : {P : Place F | (tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits} = Zfin F 1728 := by
      ext P
      simp only [Zfin, Set.mem_setOf_eq]
      rw [tF_sub_one_eq_mul, tF_eq_mul, (mul_rat_mem_iff P (by norm_num) _).1,
        (mul_rat_mem_iff P (by norm_num) _).2]
    rw [hZ1]
    exact fundamentalIdentity_fin' 1728
  · exact fundamentalIdentity_inf

/-- **`BelyiGenusBound` from Riemann–Hurwitz alone** (proved). -/
theorem belyiGenusBound_of_rh (hRH : RiemannHurwitzQj) : BelyiGenusBound :=
  belyiGenusBound_of_rh_fi hRH fundamentalIdentityQj

/-- **`DimJ1Le` (the use of T34) from `DimJacobianEqGenus`, Riemann–Hurwitz and
`X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_rh (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj)
    (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of_belyi h1 (belyiGenusBound_of_rh hRH) h0

end FIfinal

end GenusFold



namespace GenusFold

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

/-- **`DimJ1Le` (the only use of T34) from `DimJacobianEqGenus` and Riemann–Hurwitz alone**
(proved). No `GenusX1Field`, no `X0Transitive`: the constant field of `K_N` comes from the model of
`X₁(N)` carried by `IsJ1` (`constantFieldIsQ_of_curve`), the Belyi function and the degree bound
`[K_N : ℚ(j)] ≤ N²` from the kernel theorem `ZInQ.RLeaf.belyiX1`, and `2g + 1 ≤ [K_N : ℚ(j)]` from
`belyiGenusBound_of_rh`. -/
theorem dimJ1Le_of_rh_curve (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj) : DimJ1Le := by
  rintro N J hN ⟨X, P₀, aj, ⟨hC, hI, P, hP, he⟩, hJ⟩
  have hK : ConstantFieldIsQ (fieldX1 P) := constantFieldIsQ_of_curve X hC (fieldX1 P) he.some
  obtain ⟨hBel, hdeg⟩ := ZInQ.RLeaf.belyiX1 N P hN hP
  have hB := belyiGenusBound_of_rh hRH (fieldX1 P) hK hBel
  exact ⟨fieldGenus (fieldX1 P), h1 X hC P₀ J aj hJ hI (fieldX1 P) he, by omega⟩

/-- **The genus bound for every model (proved)**: for a model `X` of `X₁(N)` (`IsX1Model`), the genus
of `K_N` is at most `(N² − 1)/2`, from Riemann–Hurwitz alone. -/
theorem genus_le_of_model (hRH : RiemannHurwitzQj) (N : ℕ) (hN : 0 < N) (X : Over SpecQ)
    (hX : IsX1Model N X) : ∃ P : EjBar.toAffine.Point, addOrderOf P = N ∧
      2 * fieldGenus (fieldX1 P) + 1 ≤ N ^ 2 := by
  obtain ⟨hC, hI, P, hP, he⟩ := hX
  have hK : ConstantFieldIsQ (fieldX1 P) := constantFieldIsQ_of_curve X hC (fieldX1 P) he.some
  obtain ⟨hBel, hdeg⟩ := ZInQ.RLeaf.belyiX1 N P hN hP
  have hB := belyiGenusBound_of_rh hRH (fieldX1 P) hK hBel
  exact ⟨P, hP, by omega⟩

end GenusFold
