import ZInQKernel.Contrib.Dim.IntegralHom
import ZInQKernel.Contrib.Dim.MvPolynomial

/-!
# Krull dimension equals transcendence degree for domains of finite type over a field

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task dim-contrib, 2026-11-13,
adopting task curve-infra, `scratch/curve-infra/`). Mathlib only.

## Main results

Let `K` be a field and `R` a domain of finite type over `K`.

* `ZInQ.Contrib.Dim.exists_ringKrullDim_eq_and_trdeg_eq`: there is `s : ℕ` with `dim R = s` and
  `trdeg_K R = s` (Noether normalization).
* `ZInQ.Contrib.Dim.trdeg_eq_of_isFractionRing`: `trdeg_K Frac(R) = trdeg_K R` (for any domain `R`).
* `ZInQ.Contrib.Dim.ringKrullDim_eq_trdeg_fractionRing`: `dim R = trdeg_K Frac(R)`.
* `ZInQ.Contrib.Dim.exists_aeval_eq_zero_of_trdeg_le_one`: two elements of a field of
  transcendence degree at most one over `K` satisfy a nonzero polynomial relation over `K`.

Sources (STANDARD; numbering UNVERIFIED): Hartshorne, *Algebraic Geometry*, I Prop. 1.7 and
Thm. 1.8A; the Stacks Project, *Commutative Algebra*, section "Dimension of finite type algebras
over fields". The one deep input is Noether normalization, Mathlib's
`exists_finite_inj_algHom_of_fg` (Stacks 00OW).

The named statements `DimEqTrdegAlg` and `AlgDepOfTrdegOne` are curve-infra's, unchanged.
-/

namespace ZInQ.Contrib.Dim

universe u v

/-- **Noether normalization data.** A domain `R` of finite type over a field `K` has
`dim R = s = trdeg_K R` for some `s : ℕ`. -/
theorem exists_ringKrullDim_eq_and_trdeg_eq (K : Type u) [Field K] (R : Type v) [CommRing R]
    [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] :
    ∃ s : ℕ, ringKrullDim R = s ∧ Algebra.trdeg K R = s := by
  obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
  let := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
  have : IsScalarTower K (MvPolynomial (Fin s) K) R :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  have : FaithfulSMul (MvPolynomial (Fin s) K) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr ginj
  refine ⟨s, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_fin]
  · have h := lift_trdeg_add_eq K (MvPolynomial (Fin s) K) R
    rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := R)] at h
    simpa using h.symm

/-- **Transcendence degree is unchanged by passing to the fraction field.** -/
theorem trdeg_eq_of_isFractionRing (K : Type*) [Field K] (R : Type u) [CommRing R] [IsDomain R]
    [Algebra K R] (F : Type u) [Field F] [Algebra R F] [Algebra K F] [IsScalarTower K R F]
    [IsFractionRing R F] : Algebra.trdeg K F = Algebra.trdeg K R := by
  have : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
  have : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsFractionRing.injective R F)
  rw [← trdeg_add_eq K R (A := F), trdeg_eq_zero (R := R) (A := F), add_zero]

/-- **Dimension equals transcendence degree.** For a domain `R` of finite type over a field `K`,
`dim R = trdeg_K R`. -/
theorem ringKrullDim_eq_trdeg (K : Type u) [Field K] (R : Type v) [CommRing R] [IsDomain R]
    [Algebra K R] [Algebra.FiniteType K R] :
    ringKrullDim R = ((Algebra.trdeg K R).toENat : WithBot ℕ∞) := by
  obtain ⟨s, hdim, htr⟩ := exists_ringKrullDim_eq_and_trdeg_eq K R
  rw [htr, Cardinal.toENat_nat, hdim]
  rfl

/-- **Dimension equals transcendence degree of the fraction field.** For a domain `R` of finite
type over a field `K`, `dim R = trdeg_K Frac(R)`. -/
theorem ringKrullDim_eq_trdeg_fractionRing (K : Type u) [Field K] (R : Type v) [CommRing R]
    [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] :
    ringKrullDim R = ((Algebra.trdeg K (FractionRing R)).toENat : WithBot ℕ∞) := by
  rw [trdeg_eq_of_isFractionRing K R (FractionRing R), ringKrullDim_eq_trdeg K R]

/-- **Two elements of a field of transcendence degree at most one are algebraically dependent.**
If `trdeg_K F ≤ 1` then for all `a b : F` there is a nonzero `P ∈ K[X, Y]` with `P(a, b) = 0`. -/
theorem exists_aeval_eq_zero_of_trdeg_le_one (K F : Type*) [Field K] [Field F] [Algebra K F]
    (h : Algebra.trdeg K F ≤ 1) (a b : F) :
    ∃ P : MvPolynomial (Fin 2) K, P ≠ 0 ∧ MvPolynomial.aeval ![a, b] P = 0 := by
  by_contra hne
  push Not at hne
  have hind : AlgebraicIndependent K ![a, b] := by
    rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
    intro P hP
    by_contra h0
    exact hne P h0 hP
  have h1 := hind.lift_cardinalMk_le_trdeg
  simp only [Cardinal.mk_fin, Cardinal.lift_natCast] at h1
  have h2 : Cardinal.lift.{0} (Algebra.trdeg K F) ≤ 1 := by simpa using h
  exact absurd (h1.trans h2) (by norm_num)

/-! ## Named statements (curve-infra) -/

/-- **(AD), affine algebraic form.** For a domain `R` of finite type over a field `K`,
`dim R = trdeg_K Frac(R)`. Source as in the module docstring. Glue: proved here
(`dimEqTrdegAlg`). -/
def DimEqTrdegAlg : Prop :=
  ∀ (K R : Type) [Field K] [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R],
    ringKrullDim R = ((Algebra.trdeg K (FractionRing R)).toENat : WithBot ℕ∞)

/-- **Two elements of a field of transcendence degree one are algebraically dependent.** The
function-field content of curve-glue's `AlgDep` (two rational functions on a curve satisfy a
nonzero polynomial relation). Source (STANDARD): definition of transcendence degree
(Stacks 030G, as tagged in Mathlib's `Algebra.trdeg`). Glue: proved here (`algDepOfTrdegOne`;
`exists_aeval_eq_zero_of_trdeg_le_one` is the same with `trdeg ≤ 1`). -/
def AlgDepOfTrdegOne : Prop :=
  ∀ (K F : Type) [Field K] [Field F] [Algebra K F], Algebra.trdeg K F = 1 →
    ∀ a b : F, ∃ P : MvPolynomial (Fin 2) K, P ≠ 0 ∧ MvPolynomial.aeval ![a, b] P = 0

theorem dimEqTrdegAlg : DimEqTrdegAlg := by
  intro K R _ _ _ _ _
  exact ringKrullDim_eq_trdeg_fractionRing K R

theorem algDepOfTrdegOne : AlgDepOfTrdegOne := by
  intro K F _ _ _ h
  exact exists_aeval_eq_zero_of_trdeg_le_one K F h.le

end ZInQ.Contrib.Dim
