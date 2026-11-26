import ZInQKernel.Contrib.OneProof.LiteratureCriteria.DS965Places
import ZInQKernel.Contrib.OneProof.ModularFrobeniusDual

/-! # The geometric polynomial and the arithmetic prime-ideal convention -/

namespace ModularFrobeniusDual

open Matrix Polynomial
open ZInQ.Contrib.ChebFD.C10 (Zbar)
open ZInQ.Contrib.ChebFD.HSyn (Qbar GQ gZ LiesOver IsArithFrob zbarLoc liesOver_and_isArithFrob)

/-- A full polynomial on geometric Frobenius at valuation places gives the full arithmetic
polynomial on the contragredient at primes of the algebraic integers. The trace remains on
geometric Frobenius of the original representation. `R` is any nontrivial commutative ring and
`φ : R →+* S` any ring hom; `φ` enters only through the trace. -/
theorem arithmetic_atPrime_and_geometric_trace {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] (φ : R →+* S) (ρ : GQ →* GL (Fin 2) R) (a b : R)
    {p : ℕ} (hp : p.Prime) (P : Ideal Zbar) [P.IsPrime]
    (hP : P.under ℤ = Ideal.span {(p : ℤ)}) (σ : GQ)
    (hσ : ∀ x : Zbar, gZ σ x - x ^ p ∈ P)
    (hgeom : ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
      (ρ τ⁻¹ : Matrix (Fin 2) (Fin 2) R).charpolyRev = 1 - C a * X + C b * X ^ 2) :
    (dual ρ σ : Matrix (Fin 2) (Fin 2) R).charpoly = X ^ 2 - C a * X + C b ∧
      φ (ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) R).trace = φ a := by
  obtain ⟨hv, hF⟩ := liesOver_and_isArithFrob P σ p hp hP (fun x y hy => by
    have he : gZ σ x - x ^ p = y := by
      apply Subtype.ext
      push_cast
      exact hy.symm
    exact he ▸ hσ x)
  have h := charpoly_of_eulerPolynomial _ a b (hgeom (zbarLoc P p hp hP) σ hv hF)
  exact ⟨(charpoly_dual ρ σ).trans h, (arithmetic_charpoly_and_geometric_trace φ ρ σ a b h).2⟩

end ModularFrobeniusDual
