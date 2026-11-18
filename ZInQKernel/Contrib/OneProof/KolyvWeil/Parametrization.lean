import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois
import ZInQKernel.HDecomp.Conductor.LadicCond

/-!
# Weak Weil parametrizations over ℚ

We use the function field presentation of the smooth projective modular curve. The level is fixed
by the elliptic curve's local Artin conductors, including the wild terms at 2 and 3.
-/

namespace ZInQ.Manuscript.KolyvWeil

open scoped MatrixGroups
open PkgI4 (GQp)

noncomputable section

/-- The rational function field of the smooth projective curve `X₀(N)`:
ℚ(j(q), j(q^N)) in ℚ((q)). Reuse the general definition from the vendored Anthropic FLT
`Definitions/Def_ModularCurve_X0.lean` (the cusp is ∞). -/
abbrev X0FunctionField (N : ℕ+) := ↥(ModularCurve.modularFunctionField (N : ℕ))

/-- The type of nonconstant ℚ-morphisms `X₀(N) → E`, encoded by pullback on function fields.
For smooth projective integral curves a ℚ-embedding of function fields determines such a
morphism uniquely: take the dominant rational map and extend it across the DVRs of the source
by properness. Every ℚ-algebra map between these fields is injective. -/
abbrev NonconstantX0Map (N : ℕ+) (E : WeierstrassCurve ℚ) :=
  E.toAffine.FunctionField →ₐ[ℚ] X0FunctionField N

/-- The coordinate representation of `G_{ℚ_p}` on `V_ℓ(E)` in a chosen integral Tate basis.
The action is Tau Ceti's action on the Tate module of the local base change, with matrices
mapped from ℤ_ℓ to ℚ_ℓ. -/
private def localTateRep (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] : GQp p →* GL (Fin 2) ℚ_[ℓ] := by
  classical
  let W := E.baseChange ℚ_[p]
  have hℓ : (ℓ : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  let b := Module.Basis.ofEquivFun
    (Classical.choice ((W.baseChange (PadicAlgCl p)).nonempty_linearEquiv_tateModule hℓ))
  let ρ := W.tateModuleGaloisRepresentation (K := PadicAlgCl p) ℓ
  exact (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[ℓ] ℚ_[ℓ])).comp
    ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ).toHomUnits

/-- The local elliptic conductor exponent: the Artin conductor (inertia codimension plus Swan)
of its rational Tate module. Choose ℓ = 3 at p = 2, and ℓ = 2 otherwise, so always ℓ ≠ p. -/
def localConductorExponent (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) [Fact p.Prime] : ℚ :=
  if p = 2 then
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    LadicCond.condExp (localTateRep E p 3)
  else
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    LadicCond.condExp (localTateRep E p 2)

/-- `N = N_E`: at each prime p the exponent of p in the positive integer N is the local elliptic
conductor exponent. This pins down the level without choosing a default for `N_E` or rounding
any local exponent. -/
def IsConductor (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ+) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ((N : ℕ).factorization p : ℚ) = localConductorExponent E p

/-- The factorization condition fixes at most one positive level. -/
theorem IsConductor.unique {E : WeierstrassCurve ℚ} [E.IsElliptic] {M N : ℕ+}
    (hM : IsConductor E M) (hN : IsConductor E N) : M = N := by
  apply Subtype.ext
  apply Nat.factorization_inj M.ne_zero N.ne_zero
  ext p
  by_cases hp : p.Prime
  · let _ : Fact p.Prime := ⟨hp⟩
    exact_mod_cast (hM p).trans (hN p).symm
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Weak Weil hypothesis (Kolyvagin, MPI/90-69 p. 3; BCDT, Introduction (6) p. 3):
there is a nonconstant ℚ-morphism `X₀(N_E) → E` at the conductor of E. -/
def HasWeakWeilParametrization (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∃ N : ℕ+, IsConductor E N ∧ Nonempty (NonconstantX0Map N E)

end

end ZInQ.Manuscript.KolyvWeil
