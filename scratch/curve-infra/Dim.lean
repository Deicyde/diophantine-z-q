import Mathlib

set_option linter.style.haveILetI false

open Order

universe u

namespace CurveInfra

/-- Copied verbatim from g0-dim (`scratch/g0-dim/part_dim.lean`). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    have h : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) h
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- Noether normalization data for a domain of finite type: `dim R = s = trdeg_K R`. -/
theorem exists_dim_eq_trdeg (K : Type u) [Field K] (R : Type u) [CommRing R] [IsDomain R]
    [Algebra K R] [Algebra.FiniteType K R] :
    ∃ s : ℕ, ringKrullDim R = s ∧ Algebra.trdeg K R = s := by
  obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
  letI := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) R :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr ginj
  refine ⟨s, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]
  · rw [← trdeg_add_eq K (MvPolynomial (Fin s) K) (A := R), MvPolynomial.trdeg_of_isDomain,
      trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := R)]
    simp

/-- Transcendence degree is unchanged by passing to a localization (e.g. the fraction field). -/
theorem trdeg_eq_of_isLocalization (K : Type*) [Field K] (R : Type u) [CommRing R] [IsDomain R]
    [Algebra K R] (F : Type u) [Field F] [Algebra R F] [Algebra K F] [IsScalarTower K R F]
    [IsFractionRing R F] : Algebra.trdeg K F = Algebra.trdeg K R := by
  haveI : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
  haveI : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsFractionRing.injective R F)
  rw [← trdeg_add_eq K R (A := F), trdeg_eq_zero (R := R) (A := F), add_zero]


/-! ## §2. Schemes -/

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

/-- Copied verbatim from g0-dim (`scratch/g0-dim/part_dim.lean`). -/
theorem topologicalKrullDim_eq_iSup_of_openEmbedding {X : Type*} [TopologicalSpace X] {ι : Type*}
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ krullDim {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} := q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

/-- Copied verbatim from g0-dim (`scratch/g0-dim/part_dim.lean`). -/
theorem scheme_dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

/-- Copied verbatim from g0-dim (`scratch/g0-dim/part_dim.lean`). -/
theorem spec_dim (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R

/-- The top open of a nonempty scheme is nonempty. -/
instance nonempty_top (X : Scheme.{u}) [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Nonempty.some inferInstance, trivial⟩⟩

/-- The `K`-algebra structure on the function field of an integral scheme `X` over `Spec K`,
through `K ≅ Γ(Spec K, ⊤) → Γ(X, ⊤) → K(X)`. -/
noncomputable abbrev fnFieldAlgebra (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) : Algebra K X.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤).hom.toAlgebra

/-- The `K`-algebra structure on `Γ(X, U)` through `f`. -/
noncomputable abbrev secAlgebra (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : Algebra K Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

/-- On a nonempty affine open `U` of an integral `X` locally of finite type over `K`:
`dim U = trdeg_K K(X)`. -/
theorem dim_affineOpen_eq_trdeg (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] :
    letI := fnFieldAlgebra K X f
    topologicalKrullDim U = ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞) := by
  letI := fnFieldAlgebra K X f
  letI := secAlgebra K X f U
  have hft : Algebra.FiniteType K Γ(X, U) := by
    have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    exact h1.comp h2
  haveI : IsScalarTower K Γ(X, U) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤).hom x =
      (X.germToFunctionField U).hom
        (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top).hom x)
    rw [← CommRingCat.comp_apply]
    congr 2
    simp only [Category.assoc, Scheme.Hom.appLE, Scheme.Hom.appTop]
    congr 2
    exact (X.presheaf.germ_res (homOfLE le_top) _ _).symm
  haveI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨s, hdim, htr⟩ := exists_dim_eq_trdeg K Γ(X, U)
  rw [trdeg_eq_of_isLocalization K Γ(X, U) X.functionField, htr, Cardinal.toENat_nat]
  rw [show topologicalKrullDim U = topologicalKrullDim U.toScheme from rfl,
    scheme_dim_eq_of_iso hU.isoSpec, spec_dim, hdim]
  norm_cast

/-- **(AD), general form, proved.** For an integral scheme `X` locally of finite type over a
field `K`, `dim X = trdeg_K K(X)`. -/
theorem dim_eq_trdeg (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] :
    letI := fnFieldAlgebra K X f
    topologicalKrullDim X = ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞) := by
  letI := fnFieldAlgebra K X f
  let ι := {U : X.Opens // IsAffineOpen U ∧ (U : Set X).Nonempty}
  have hcov : ∀ x : X, ∃ i : ι, x ∈ Set.range (fun y : (i.1 : Set X) => (y : X)) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV, ⟨x, hxV⟩⟩, ⟨x, hxV⟩, rfl⟩
  rw [topologicalKrullDim_eq_iSup_of_openEmbedding (Y := fun i : ι => (i.1 : Set X))
    (fun i y => (y : X)) (fun i => i.1.isOpen.isOpenEmbedding_subtypeVal) hcov]
  haveI : Nonempty ι := by
    obtain ⟨i, -⟩ := hcov (Nonempty.some inferInstance)
    exact ⟨i⟩
  have : ∀ i : ι, topologicalKrullDim (i.1 : Set X) =
      ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞) := by
    intro i
    haveI : Nonempty i.1 := i.2.2.to_subtype
    exact dim_affineOpen_eq_trdeg K X f i.1 i.2.1
  simp only [this, ciSup_const]


/-! ## §3. The named statements and their proofs -/

/-- **(AD), general form: dimension equals transcendence degree.** Step (AD) of curve-glue's
image-plane step, in the general form cited by curve-glue §6 and §8 ("the Krull dimension of a
finitely generated `K`-domain equals the transcendence degree of its fraction field").
For an integral scheme `X` locally of finite type over a field `K`, the Krull dimension of `X`
equals the transcendence degree over `K` of its function field `K(X)` (with the `K`-algebra
structure induced by `f`). Source (STANDARD; numbering UNVERIFIED): Hartshorne, *Algebraic
Geometry*, I Prop. 1.7, Thm. 1.8A and Ex. II.3.20; the Stacks Project, *Commutative Algebra*,
section "Dimension of finite type algebras over fields". Glue: proved here from Mathlib's Noether
normalization (`exists_finite_inj_algHom_of_fg`, Stacks 00OW). -/
def DimEqTrdeg : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f],
    letI := fnFieldAlgebra K X f
    topologicalKrullDim X = ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞)

/-- **(AD), affine algebraic form.** For a domain `R` of finite type over a field `K`,
`dim R = trdeg_K Frac(R)`. Same source as `DimEqTrdeg`. Glue: proved here. -/
def DimEqTrdegAlg : Prop :=
  ∀ (K R : Type) [Field K] [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R],
    ringKrullDim R = ((Algebra.trdeg K (FractionRing R)).toENat : WithBot ℕ∞)

/-- **Two elements of a field of transcendence degree one are algebraically dependent.** The
function-field content of curve-glue's `AlgDep` (two rational functions on a curve satisfy a
nonzero polynomial relation). Source (STANDARD): definition of transcendence degree
(Stacks 030G, as tagged in Mathlib's `Algebra.trdeg`). Glue: proved here. -/
def AlgDepOfTrdegOne : Prop :=
  ∀ (K F : Type) [Field K] [Field F] [Algebra K F], Algebra.trdeg K F = 1 →
    ∀ a b : F, ∃ P : MvPolynomial (Fin 2) K, P ≠ 0 ∧ MvPolynomial.aeval ![a, b] P = 0

theorem dimEqTrdeg : DimEqTrdeg := by
  intro K _ X _ f _
  exact dim_eq_trdeg K X f

theorem dimEqTrdegAlg : DimEqTrdegAlg := by
  intro K R _ _ _ _ _
  obtain ⟨s, hdim, htr⟩ := exists_dim_eq_trdeg K R
  rw [trdeg_eq_of_isLocalization K R (FractionRing R), htr, Cardinal.toENat_nat, hdim]
  norm_cast

theorem algDepOfTrdegOne : AlgDepOfTrdegOne := by
  intro K F _ _ _ h a b
  by_contra hne
  push Not at hne
  have hind : AlgebraicIndependent K ![a, b] := by
    rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
    intro P hP
    by_contra h0
    exact hne P h0 hP
  have := hind.cardinalMk_le_trdeg
  rw [h, Cardinal.mk_fin] at this
  norm_num at this

end CurveInfra

#print axioms CurveInfra.dimEqTrdeg
#print axioms CurveInfra.dimEqTrdegAlg
#print axioms CurveInfra.algDepOfTrdegOne
