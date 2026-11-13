# t25-newform: leaf T25 `PkgI4.NewformOfEigenform` proved

## Main result (VERIFIED: compiled, axioms printed)

`ZInQKernel/Contrib/T25/NewformOfEigenform.lean`:

```lean
theorem T25.newformOfEigenform_leaf : PkgI4.NewformOfEigenform
```

where (`ZInQKernel/HDecomp/ModCurves/C9.lean:384`, verbatim copy of
`scratch/h-decomposition/Leaves.lean:4592`)

```lean
def NewformOfEigenform : Prop :=
  ∀ (M : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ M) (g : CF M k),
    0 < M → IsNormalizedEigenform g χ →
    ∃ (N : ℕ) (χ' : DirichletCharacter ℂ N) (f : CF N k), 0 < N ∧ N ∣ M ∧ IsNewform f χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → coeff f p = coeff g p
```

`#print axioms` (scratch/t25-newform/Axioms.lean):

```
'T25.newformOfEigenform_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'T25.newformOfEigenform' depends on axioms: [propext, Classical.choice, Quot.sound]
'T25.newform_coeff_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'T25.heckeTCuspNat_eq_coeff_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'T25.not_mem_oldSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'T25.oldSpace_le_map_cuspFormsOld' depends on axioms: [propext, Classical.choice, Quot.sound]
'T25.mem_cuspFormCharSpace_of_hasNebentypus' depends on axioms: [propext, Classical.choice, Quot.sound]
'T25.hasNebentypus_of_mem_cuspFormCharSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build: `lake build ZInQKernel.Contrib.T25.NewformOfEigenform` — Build completed successfully.

## Declarations (ZInQKernel/Contrib/T25/Bridge.lean, namespace `T25`)

All proved, no `sorry`. `CF`, `coeff`, `HasNebentypus`, `IsNormalizedEigenform`, `oldSpace`,
`IsNewform`, `scaleH` are the `PkgI4` definitions of `ZInQKernel/HDecomp/Conductor/LadicCond.lean`.

- `slash_SL_eq_mapGL (f : ℍ → ℂ) (γ : SL(2, ℤ)) : f ∣[k] γ = f ∣[k] mapGL ℝ γ`
- `mem_cuspFormCharSpace_of_hasNebentypus [NeZero N] {f : CF N k} {χ : DirichletCharacter ℂ N}
  (h : HasNebentypus f χ) : f ∈ cuspFormCharSpace k (MulChar.toUnitHom χ)`
- `hasNebentypus_of_mem_cuspFormCharSpace [NeZero N] {f : CF N k} {χ₀ : (ZMod N)ˣ →* ℂˣ}
  (h : f ∈ cuspFormCharSpace k χ₀) : HasNebentypus f (MulChar.ofUnitHom χ₀)`
- `coeff_zero (f : CF N k) : coeff f 0 = 0`
- `heckeTCuspNat_eq_coeff_smul [NeZero N] {g : CF N k} {χ} (hg : IsNormalizedEigenform g χ)
  {p} (hp : p.Prime) (hpN : Nat.Coprime p N) : heckeTCuspNat k p g = coeff g p • g`
- `coeL N k : CF N k →ₗ[ℂ] (ℍ → ℂ)` (coercion as a linear map)
- `scaleGL_smul_eq_scaleH (d : ℕ+) (τ) : TauCeti.scaleGL (d : ℕ) • τ = scaleH d τ`
- `oldSpace_le_map_cuspFormsOld [NeZero N] : oldSpace N k ≤ (TauCeti.cuspFormsOld N k).map (coeL N k)`
- `not_mem_oldSpace [NeZero N] {f : CF N k} (hnew : f ∈ TauCeti.cuspFormsNew N k) (h0 : f ≠ 0) :
  ⇑f ∉ oldSpace N k`
- `newform_coeff_mul [NeZero N] (f : Newform N k) (m n : ℕ) (hn : 0 < n) :
  coeff f.toCuspForm m * coeff f.toCuspForm n = ∑ d ∈ (Nat.gcd m n).divisors,
  (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) d * (d : ℂ) ^ (k - 1) * coeff f.toCuspForm (m * n / d ^ 2)`
- `newformOfEigenform` : the unfolded body of `PkgI4.NewformOfEigenform`.

## Proof

Given `g` with `IsNormalizedEigenform g χ` at level `M`:
1. `g ≠ 0` (`a₁ = 1`); `g ∈ cuspFormCharSpace k (toUnitHom χ)` (bridge (ii)); the leaf identity at
   `(p, m)` is Tau Ceti's `T_p` recurrence, so `T_p g = a_p(g) g` for `p ∤ M` (bridge (iii), TC
   `heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul`).
2. TC `Newform.exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul` (Decomposition.lean;
   Diamond–Shurman Prop. 5.8.4, eigenvalue half) gives `N ∣ M` and a TC `Newform N k` `f` with
   eigenvalue `a_p(g)` at every `p ∤ M`.
3. `f` is a leaf newform with `χ' = MulChar.ofUnitHom f.χ`: nebentypus by (ii); `a₁ = 1` is
   `f.isNorm`; the identity for all `m, n ≥ 1` from `Newform.toEigenform` (TC FullEigenform.lean:
   newforms are eigen at the bad primes too) and TC's divisor-sum formula
   `qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0` (no multiplicative-function
   algebra needed); not in the leaf's `oldSpace` since its generators `τ ↦ f(dτ)` (`M < N`,
   `dM ∣ N`) are TC `levelRaise d` images in `cuspFormsOld` (TC condition `M ≠ N`, `dM ∣ N`), and
   `disjoint_cuspFormsOld_cuspFormsNew`.
4. `a_p(f)` = eigenvalue of `f` at `p` (`toEigenform_eigenvalue_eq_qExpansion_coeff`) = `a_p(g)`.

Notion comparison (VERIFIED by the proof): the leaf's `CF N k` is literally Tau Ceti's
`CuspForm ((Gamma1 N).map (mapGL ℝ)) k` (Mathlib's coercion is `Subgroup.map (mapGL ℝ)`); the
diamond label is the lower-right entry in both; Tau Ceti's newform (Petersson-new, `a₁ = 1`,
good-prime eigen) implies the leaf's (full coefficient identities, not in the span-old space).
No difference changes the statement.

## Vendored Tau Ceti modules (206, from ~/tc-oct16 commit 5a01f5fe3621, ~46.1k lines)

The oct16 import closure of `TauCeti.NumberTheory.ModularForms.Newforms.Decomposition` (216
modules, 204 not yet vendored), plus `Newforms.FullEigenform` and
`HeckeSlash.Nebentypus.CoefficientFormula`. Copied with `tcport.py` (provenance line, Tau Ceti
copyright header kept), under `ZInQKernel/Contrib/TauCeti/`. One fix:
`NumberTheory/ModularForms/Basic.lean`, `[IsSMulApply R (ModularForm Γ k)]` (and the `CuspForm`
and `Γ'` variants, 6 binders) given the explicit `UpperHalfPlane ℂ` arguments that Mathlib 56a00585
requires. All build at our pins. Module list:

```
TauCeti.Algebra.BigOperators.Finset.Fiber
TauCeti.Algebra.Group.Subgroup.Centralizer
TauCeti.Algebra.GroupWithZero.Divisibility
TauCeti.Algebra.LinearRecurrence.OrderTwo
TauCeti.Analysis.Analytic.Order
TauCeti.Analysis.Complex.AtInfinity
TauCeti.Analysis.Complex.Coordinates
TauCeti.Analysis.Complex.Periodic
TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
TauCeti.Analysis.Complex.UpperHalfPlane.Measure
TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
TauCeti.Analysis.Complex.UpperHalfPlane.QExpansion.Order
TauCeti.Analysis.Complex.UpperHalfPlane.Topology
TauCeti.Data.Int.Fin2Tuple
TauCeti.Data.Int.LinearCongruence
TauCeti.Data.Nat.Factorization.Basic
TauCeti.Data.Nat.Factorization.GcdSplit
TauCeti.Data.Nat.Factorization.PrimePowerProd.Basic
TauCeti.Data.Nat.Factorization.PrimePowerProd.DivisorTable
TauCeti.Data.Nat.Prime.FactorsProd
TauCeti.Data.ZMod.OnePoint
TauCeti.GroupTheory.DoubleCoset.Basic
TauCeti.GroupTheory.DoubleCoset.Inv
TauCeti.GroupTheory.DoubleCoset.Normalizer
TauCeti.LinearAlgebra.Complex.Determinant
TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
TauCeti.LinearAlgebra.Matrix.Diagonal
TauCeti.LinearAlgebra.Matrix.Divisibility
TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Adjugate
TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DoubleCoset
TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MoebiusZMod
TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo
TauCeti.LinearAlgebra.Matrix.SmithNormalForm
TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Equivalence
TauCeti.LinearAlgebra.Matrix.Triangular
TauCeti.MeasureTheory.Group.FundamentalDomain
TauCeti.MeasureTheory.Integral.Bochner.Basic
TauCeti.MeasureTheory.Measure.Lebesgue.Complex
TauCeti.NumberTheory.ArithmeticFunction.PrimeRecurrence
TauCeti.NumberTheory.DirichletCharacter.Basic
TauCeti.NumberTheory.HeckeRing.Associativity
TauCeti.NumberTheory.HeckeRing.Basic
TauCeti.NumberTheory.HeckeRing.Commutativity
TauCeti.NumberTheory.HeckeRing.GL2.CosetDecomposition
TauCeti.NumberTheory.HeckeRing.GL2.Delta0
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.AtkinLehner
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.BadPrimeCoset
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.CoprimeRepresentative
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.CosetMap
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Coset
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Elem
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimeCosets
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimePower
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.ScalarMul
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DoubleCoset
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.ElementaryDivisors
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.NebentypusChar
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.UpperTriFactorization
TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.UpperUnit
TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.Basic
TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.CoprimeCosets
TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.DiamondCosets
TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.UpperTriCosets
TauCeti.NumberTheory.HeckeRing.GL2.PairCoset
TauCeti.NumberTheory.HeckeRing.GLn.Basic
TauCeti.NumberTheory.HeckeRing.GLn.CosetDecomposition
TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets
TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution
TauCeti.NumberTheory.HeckeRing.LinearExtension
TauCeti.NumberTheory.HeckeRing.Multiplication
TauCeti.NumberTheory.HeckeRing.Multiplicity.Basic
TauCeti.NumberTheory.HeckeRing.Multiplicity.Equiv
TauCeti.NumberTheory.HeckeRing.Multiplicity.Handedness
TauCeti.NumberTheory.HeckeRing.Multiplicity.Support
TauCeti.NumberTheory.HeckeRing.Multiplicity.Unit
TauCeti.NumberTheory.HeckeRing.Normalizer
TauCeti.NumberTheory.HeckeRing.One
TauCeti.NumberTheory.HeckeRing.StabConjugation
TauCeti.NumberTheory.Modular
TauCeti.NumberTheory.ModularForms.Basic
TauCeti.NumberTheory.ModularForms.BoundedAtCusp
TauCeti.NumberTheory.ModularForms.CharacterDecomp
TauCeti.NumberTheory.ModularForms.ConductorDichotomy
TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Units
TauCeti.NumberTheory.ModularForms.CuspDescent
TauCeti.NumberTheory.ModularForms.Cusps.Basic
TauCeti.NumberTheory.ModularForms.Cusps.Rat.Basic
TauCeti.NumberTheory.ModularForms.Cusps.Rat.Slash
TauCeti.NumberTheory.ModularForms.Degeneracy
TauCeti.NumberTheory.ModularForms.DiamondOperators
TauCeti.NumberTheory.ModularForms.GaloisProd
TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Basic
TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Eigenvector
TauCeti.NumberTheory.ModularForms.HeckeSlash.Basic
TauCeti.NumberTheory.ModularForms.HeckeSlash.Composition
TauCeti.NumberTheory.ModularForms.HeckeSlash.CuspRing
TauCeti.NumberTheory.ModularForms.HeckeSlash.Cusps
TauCeti.NumberTheory.ModularForms.HeckeSlash.Degeneracy
TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.Basic
TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.QExpansion
TauCeti.NumberTheory.ModularForms.HeckeSlash.Diamond
TauCeti.NumberTheory.ModularForms.HeckeSlash.Form
TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma0
TauCeti.NumberTheory.ModularForms.HeckeSlash.Gamma1
TauCeti.NumberTheory.ModularForms.HeckeSlash.Holomorphic
TauCeti.NumberTheory.ModularForms.HeckeSlash.Independence
TauCeti.NumberTheory.ModularForms.HeckeSlash.Invariance
TauCeti.NumberTheory.ModularForms.HeckeSlash.LevelSupported
TauCeti.NumberTheory.ModularForms.HeckeSlash.ModularForm
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Basic
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CharRing
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Composite
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Composition
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Cusps
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.EigenFromPrimes
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Eigenvector
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Holomorphic
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Independence
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Invariance
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.ModularForm
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.One
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Basic
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Power
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Recurrence
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Ring
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Scalar
TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
TauCeti.NumberTheory.ModularForms.HeckeSlash.Prime
TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence
TauCeti.NumberTheory.ModularForms.HeckeSlash.Reindex
TauCeti.NumberTheory.ModularForms.HeckeSlash.Ring
TauCeti.NumberTheory.ModularForms.HeckeSlash.Trace
TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Cusps
TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.DoubleCoset
TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Holomorphic
TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Infty
TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Invariance
TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.LevelRaise
TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.ModularForm
TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Periodic
TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion
TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.Sum
TauCeti.NumberTheory.ModularForms.Newforms.AtkinLehner
TauCeti.NumberTheory.ModularForms.Newforms.Basic
TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Basic
TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Descent
TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Dichotomy
TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
TauCeti.NumberTheory.ModularForms.Newforms.Descent.Action
TauCeti.NumberTheory.ModularForms.Newforms.Descent.Basic
TauCeti.NumberTheory.ModularForms.Newforms.Descent.CharacterSpace
TauCeti.NumberTheory.ModularForms.Newforms.Descent.Coefficient
TauCeti.NumberTheory.ModularForms.Newforms.Descent.Cosets
TauCeti.NumberTheory.ModularForms.Newforms.Descent.CuspForm
TauCeti.NumberTheory.ModularForms.Newforms.Descent.Cusps
TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelCommute
TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelRaise.Basic
TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelRaise.Commute
TauCeti.NumberTheory.ModularForms.Newforms.Descent.Sum
TauCeti.NumberTheory.ModularForms.Newforms.EigenFromPrimes
TauCeti.NumberTheory.ModularForms.Newforms.Eigenform
TauCeti.NumberTheory.ModularForms.Newforms.EigenvalueExtension
TauCeti.NumberTheory.ModularForms.Newforms.EigenvectorVanishing
TauCeti.NumberTheory.ModularForms.Newforms.Hecke.Stability
TauCeti.NumberTheory.ModularForms.Newforms.MainLemma
TauCeti.NumberTheory.ModularForms.Newforms.Nebentypus
TauCeti.NumberTheory.ModularForms.Newforms.Newform
TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis
TauCeti.NumberTheory.ModularForms.Newforms.PeterssonAdjoint
TauCeti.NumberTheory.ModularForms.Newforms.QSupport
TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue
TauCeti.NumberTheory.ModularForms.Newforms.SquarefreeDecomposition
TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne
TauCeti.NumberTheory.ModularForms.Norm.Trace
TauCeti.NumberTheory.ModularForms.Petersson.Adjoint
TauCeti.NumberTheory.ModularForms.Petersson.Basic
TauCeti.NumberTheory.ModularForms.Petersson.Eigenbasis
TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
TauCeti.NumberTheory.ModularForms.Petersson.Hecke
TauCeti.NumberTheory.ModularForms.Petersson.Normal
TauCeti.NumberTheory.ModularForms.Petersson.Orthogonal
TauCeti.NumberTheory.ModularForms.Petersson.Trace
TauCeti.NumberTheory.ModularForms.Petersson.Unitary
TauCeti.NumberTheory.ModularForms.QExpansion.Basic
TauCeti.NumberTheory.ModularForms.QExpansion.Order
TauCeti.NumberTheory.ModularForms.SlashActionRat
TauCeti.NumberTheory.ModularForms.SlashAdjugate
TauCeti.NumberTheory.ModularForms.SturmBound
TauCeti.NumberTheory.ModularForms.WithCenter
TauCeti.Order.Filter.ZeroAndBoundedAtFilter
TauCeti.RingTheory.PowerSeries.Support
TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
TauCeti.Topology.DiscreteSeparation
TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
```
