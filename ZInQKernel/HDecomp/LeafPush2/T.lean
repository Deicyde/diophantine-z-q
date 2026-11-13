import ZInQKernel.HDecomp.LeafPush2.R3
import ZInQKernel.HDecomp.Conductor.LadicCond

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from
`scratch/leaf-push2/LeafPush2.lean`, T10-T12.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

namespace ZInQ.LeafPush2

open NumberField MeasureTheory

/-! Part I of the draft (def-faltings §§1-18 and H5, a verbatim copy) is imported from
`ZInQKernel.HDecomp.Faltings.Height`, namespace `ZInQ.DefFaltings`; the copies of
leaf-modcurves' curve definitions are `LeafModCurves`'s, from
`ZInQKernel.HDecomp.ModCurves.Leaves`. -/
open ZInQ.DefFaltings
open LeafModCurves (IsCurve IsJacobian JacobianExists IsBelyiFunction)
/-! `IsComplexConj` (a duplicate in the draft) is `PkgI4`'s, from
`ZInQKernel.HDecomp.Conductor.LadicCond` (same body; `PkgI4.GQ` is an abbrev of
`AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`). -/
open PkgI4 (IsComplexConj)

section TSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-- **AN3 for abelian varieties (textbook leaf; the analytic half of T11/T12).** Every abelian
variety over a field `K` and every `σ : K → ℂ`: `A(ℂ)_σ` has an analytic uniformization by
`ℂ^g`, `g = dim A`, with kernel a full lattice (Mumford, *Abelian varieties*, §1, with GAGA,
Serre 1956, for the complex Lie group structure; UNVERIFIED numbers). The `AbVar` analogue of
def-faltings' `AnalyticUniformizationExists`. -/
def UniformizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (σ : K →+* ℂ) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A σ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization σ Λ Φ

/-- **T11(a), Riemann/GAGA for endomorphisms (textbook leaf).** For an abelian variety over `ℂ`
with a uniformization `Φ` (kernel `Λ`) at `σ = id`, the endomorphisms of `A` are exactly the
`ℂ`-linear maps of `ℂ^g` preserving `Λ`: each such `M` is induced by a unique endomorphism `f`
(`Φ(Mz) = f ∘ Φ(z)`), and each `f` is induced by some `M`. (Mumford §1 and §2, Birkenhake–Lange
Prop. 1.2.1 for complex tori; GAGA, Serre 1956, for "holomorphic ⇒ algebraic"; UNVERIFIED
numbers.) With `ℚ ⊗`, this is `End⁰(A_ℂ) = End(H₁(A(ℂ),ℚ))` ∩ (Hodge endomorphisms), the form of
T11 used at G5/G10. -/
def T11a_RiemannEnd : Prop :=
  ∀ (A : AbVar ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → IsUniformization (RingHom.id ℂ) Λ Φ →
    (∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z ∈ Λ, M z ∈ Λ) →
      ∃! f : AbVar.End A, ∀ z, Φ (M z) = Φ z ≫ f.hom) ∧
    (∀ f : AbVar.End A, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, Φ (M z) = Φ z ≫ f.hom)

/-- **T11(b), rigidity (textbook leaf).** For abelian varieties over an algebraically closed field
`k` of characteristic 0 and an extension `k → L`, every homomorphism `A_L → B_L` descends uniquely
to a homomorphism `A → B` (Conrad 2006, §3; Milne 1986 §20; UNVERIFIED numbers). With `k = ℚ̄`,
`L = ℂ` this is `Hom_ℚ̄ = Hom_ℂ`. -/
def T11b_Rigidity : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (L : Type) [Field L] [Algebra k L]
    (A B : AbVar k) (ψ : (A.baseChange L).X ⟶ (B.baseChange L).X), IsMonHom ψ →
    ∃! φ : A.X ⟶ B.X, IsMonHom φ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map φ = ψ

/-- **T12, in the form used at G10 (oddness).** For an abelian variety `A/ℚ` of dimension `g`,
complex conjugation acts on `V_ℓ(A)` with `+1`- and `−1`-eigenspaces of dimension `g` each.
Not a single published statement: Artin's comparison `V_ℓ(A) ≅ H₁(A(ℂ),ℚ) ⊗ ℚ_ℓ` compatibly with
complex conjugation (SGA 4 XI 4.4; for abelian varieties elementary through `ℂ^g/Λ`: the
`ℓⁿ`-torsion of `A(ℂ)` is `Φ(ℓ⁻ⁿΛ)`, and `A(ℚ̄)[ℓⁿ] → A(ℂ)[ℓⁿ]` is bijective by T5), plus the
computation that an antiholomorphic involution of `ℂ^g/Λ` acts on `Λ ⊗ ℝ = ℂ^g` with eigenspaces
of real dimension `g` (`ℂ^g = W ⊕ iW`). A **glue target** from `UniformizationExists`, T5, T26
(`V_ℓ` finite of rank `2g`) and the antiholomorphy of complex conjugation on `A(ℂ)` for `A/ℚ`. -/
def T12_ComplexConjEigen : Prop :=
  ∀ (A : AbVar ℚ) (g : ℕ), A.dim = (g : WithBot ℕ∞) → ∀ (ℓ : ℕ) [Fact ℓ.Prime]
    (c : Field.absoluteGaloisGroup ℚ), IsComplexConj c →
    Module.finrank ℚ_[ℓ] (LinearMap.ker (AbVar.galRep ℓ A c - 1)) = g ∧
      Module.finrank ℚ_[ℓ] (LinearMap.ker (AbVar.galRep ℓ A c + 1)) = g

/-- Sanity: complex conjugations exist in `G_ℚ` (so T12's quantifier over `c` is not empty). -/
theorem exists_isComplexConj : ∃ c : Field.absoluteGaloisGroup ℚ, IsComplexConj c := by
  obtain ⟨emb⟩ : Nonempty (AlgebraicClosure ℚ →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra (AlgebraicClosure ℚ) ℂ := emb.toRingHom.toAlgebra
  have : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
    IsScalarTower.of_algebraMap_eq (fun x => (emb.commutes x).symm)
  let χ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  refine ⟨χ.restrictNormal (AlgebraicClosure ℚ), emb, fun x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes χ (AlgebraicClosure ℚ) x

/-- **T10, the part statable in Mathlib v4.35 (not the form used).** Mathlib has `ℓ`-adic
cohomology as pro-étale cohomology, `Scheme.EllAdicCohomology X ℓ n` (Bhatt–Scholze 2015,
Def. 6.8.1; `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean`), but only as an abelian group:
no `ℤ_ℓ`-module structure and no pullback maps, hence no Galois action. `ℓ ≠ char K` as in
Milne's theorem. What is statable is the
underlying group isomorphism `H¹(A_K̄, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)`: a consequence of Milne 1986,
Thm 15.1(a) (UNVERIFIED number) together with the comparison of pro-étale and classical `ℓ`-adic
cohomology for qcqs schemes (Bhatt–Scholze 2015 §5.6, UNVERIFIED number; Mathlib's docstring
announces this comparison as future work). The form used (derive R10's Tate-module form) needs
the Galois-equivariant version: `ℤ_ℓ`-linearity and functoriality of `EllAdicCohomology` in `X`. -/
def T10_groupIso : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    Nonempty ((A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 ≃+
      Module.Dual ℤ_[ℓ] (A.T ℓ))

end TSec

end ZInQ.LeafPush2
