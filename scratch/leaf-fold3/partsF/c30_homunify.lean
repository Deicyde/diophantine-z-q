-- (leaf-fold3) written here: HomLatticeCorr verbatim from ZInQKernel/Contrib/HomUnify/Corr.lean, with its two proofs
/-! ## leaf-fold3: hom-unify's single leaf `HomLatticeCorr` (ZInQKernel/Contrib/HomUnify/Corr.lean)

The definition is `ZInQ.HomUnify.HomLatticeCorr` of `ZInQKernel/Contrib/HomUnify/Corr.lean`, verbatim; here it is
over this file's `PkgI3.AbVar`, `ZInQ.LeafPush2.CPts` and `ZInQ.LeafPush2.IsUniformization` (as in hom-unify's
own assembly, `scratch/hom-unify/parts/H20_bundle.lean`). The two consequences are Corr.lean's proofs, verbatim:
`HomLinearLift` is its first clause and leaf-push2's `T11a_RiemannEnd` (T11(a)) its two clauses at `B = A`. -/

section HomUnifyLF3

namespace HomUnify

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3
open ZInQ.LeafPush2 (CPts IsUniformization)

/-- **The analytic representation of homomorphisms (textbook LEAF; the single leaf proposed by
hom-unify for T11(a) in `Hom` form).** Let `A`, `B` be abelian varieties over a field `K`,
`σ : K → ℂ`, and `Φ_A : ℂ^g → A(ℂ)_σ`, `Φ_B : ℂ^h → B(ℂ)_σ` analytic uniformizations with kernels
`Λ_A`, `Λ_B` (`g = dim A`, `h = dim B`).
1. (lifting) every homomorphism `f : A → B` lifts to a `ℂ`-linear `M : ℂ^g → ℂ^h` with
   `Φ_B(Mz) = f(Φ_A(z))`;
2. (realization, over `ℂ`) if `K = ℂ` and `σ = id`, every `ℂ`-linear `M : ℂ^g → ℂ^h` with
   `MΛ_A ⊆ Λ_B` is induced in this way by a unique homomorphism `f : A → B`.

Together: `Hom(A_ℂ, B_ℂ) ≅ {M ∈ Hom_ℂ(ℂ^g, ℂ^h) : MΛ_A ⊆ Λ_B}`, `f ↦ ρ_a(f)`, and for general `K`
the analytic representation of `f` is that of `f_ℂ`. Sources (all UNVERIFIED numbers):
Birkenhake–Lange, *Complex abelian varieties*, §1.2 (Prop. 1.2.1: homomorphisms of complex tori
`ℂ^g/Λ → ℂ^h/Λ'` are exactly the maps induced by `ℂ`-linear `M` with `MΛ ⊆ Λ'`, and the analytic
representation is injective); Mumford, *Abelian varieties*, §1 (the complex torus `A(ℂ)`) and
§3 (`A ↦ A^an` is fully faithful on abelian varieties); Serre, GAGA (1956) / Chow, for
"holomorphic ⇒ algebraic" in 2.; holomorphy of algebraic morphisms for 1. -/
def HomLatticeCorr : Prop :=
  (∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom) ∧
  (∀ (A B : PkgI3.AbVar ℂ) (g h : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
    (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin h → ℂ) → CPts B (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
    ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
      ∃! f : PkgI3.AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom)

/-- **`HomLinearLift` from `HomLatticeCorr` (proved):** its first clause, verbatim. -/
theorem homLinearLift_of_corr (h : HomLatticeCorr) : G0Galois.HomLinearLift := h.1

/-- **leaf-push2's `T11a_RiemannEnd` from `HomLatticeCorr` (proved):** both clauses at `B = A`,
`Φ_B = Φ_A`, `K = ℂ`, `σ = id` (`End A` is `Hom A A`). -/
theorem t11a_riemannEnd_of_corr (h : HomLatticeCorr) : ZInQ.LeafPush2.T11a_RiemannEnd :=
  fun A g Λ Φ hA hU =>
    ⟨fun M hM => h.2 A A g g Λ Λ Φ Φ hA hA hU hU M hM,
     fun f => h.1 ℂ A A (RingHom.id ℂ) g g Λ Λ Φ Φ hA hA hU hU f⟩

end HomUnify

end HomUnifyLF3
