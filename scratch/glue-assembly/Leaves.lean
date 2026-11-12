import Mathlib

/-!
# The leaves of the glue cluster that Mathlib can state over genuine definitions

Of the literature inputs of C8, C10, E1, E3, E4 and F2 (`docs/research/glue-assembly.md` §2),
only these two can be stated faithfully with Mathlib's objects. Everything else needs abelian
varieties over number fields with Tate modules, Faltings heights, Néron models, or ℓ-adic Galois
representations of `G_ℚ` with Frobenius elements, which Mathlib does not have.
-/

namespace GlueAssembly

/-- **Kronecker–Weber** (C8, last step: the finite twisting character is a Dirichlet character).
Every finite abelian Galois extension of `ℚ` embeds in a cyclotomic field. Washington,
*Introduction to cyclotomic fields*, 2nd ed., Thm 14.1 (locator UNVERIFIED). Proved in Lean in
Tau Ceti (`TauCeti.ClassFieldTheory.kroneckerWeber`, per `docs/research/prereq-survey.md`; its
exact statement not compared with this one). -/
def KroneckerWeber : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K],
    (∀ a b : K ≃ₐ[ℚ] K, a * b = b * a) →
      ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)

/-- **Brauer–Nesbitt in characteristic zero** (C9, C10: identification of `r₃`, `r₅` with the
modular representations from equal traces). Two finite-dimensional semisimple representations of
a group over a field of characteristic `0` with the same character are equivalent. Curtis–Reiner,
*Representation theory of finite groups and associative algebras* (1962), (30.12)/(30.16);
Bourbaki, *Algèbre* VIII (locators UNVERIFIED). Not found in Mathlib or the libraries of the
prerequisite survey. -/
def BrauerNesbittCharZero : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E]
    (V W : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (ρ : Representation E G V) (σ : Representation E G W),
    ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation →
    (∀ g, LinearMap.trace E V (ρ g) = LinearMap.trace E W (σ g)) →
    Nonempty (Representation.Equiv ρ σ)

end GlueAssembly
