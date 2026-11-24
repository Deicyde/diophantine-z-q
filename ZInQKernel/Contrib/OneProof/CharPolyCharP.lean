import ZInQKernel.Contrib.OneProof.CharPolyCharP.Algebra
import ZInQKernel.Contrib.OneProof.DegHomogPolyC
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
import ZInQKernel.Contrib.OneProof.UniformizationLeafAll

/-!
# charpoly-p: `CharPolyIndepOfEllAlgClosed` from the polynomiality of the degree alone

Task charpoly-p (2026-11-17), report `docs/research/charpoly-p.md`, scratch `scratch/charpoly-p/`.

deg-det proved the field `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (Mumford §19 Thm 4) from deg-det's
`DegHomogPoly` (`deg` is a homogeneous polynomial function of degree `2g` on `End(A)`), the then-open field
`mumfordTorsionAlgClosed` and `homFreeFiniteAlgClosed` (Mumford §19 Thm 3), of which only `End(A)` finite over
`ℤ` was used. On the current base `mumfordTorsionAlgClosed` is proved
(`ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`), and `homFreeFiniteAlgClosed` is no longer an
open field (it is proved only in characteristic `0`). This file removes the finiteness input
(`CharPolyCharP/Algebra.lean`: polynomials of bounded degree in `φ` instead of `ℤ[X]/(R)`, and `q`-adic
integrality of `P₀` from `deg(φ^m − q) ∈ ℤ`), so that

* `charPoly_of_degPoly`: over one algebraically closed field `k` and one `A`, the polynomiality of `deg` on
  `End(A)` alone gives `∃ P ∈ ℤ[X]` monic with `charpoly V_ℓ(φ) = P` for every `ℓ ≠ char k`;
* `charPolyIndepOfEllAlgClosed_of_degHomogPoly'`: the field from deg-det's `DegHomogPoly` alone;
* `charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb'`: the field from degpoly-proof's `DegHomogPolyNoEmb`
  alone (`DegHomogPoly` restricted to the fields with no ring homomorphism to `ℂ`: characteristic `p > 0`, or
  characteristic `0` and transcendence degree above the continuum); the fields with `k → ℂ` are
  degpoly-proof's `CharPolyLattice.charPolyIndepOfEllC` (proved from `uniformizationLeafAll_proof` and
  `mumfordTorsionAlgClosed_proof`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Polynomial
open scoped TensorProduct

noncomputable section

namespace ZInQ.Contrib.OneProof.CharPolyCharP

open ZInQ.Contrib.OneProof.CharPolyEll ZInQ.Contrib.OneProof.DegDet

variable {k : Type} [Field k] [IsAlgClosed k]

/-- The polynomiality of `deg` on `End(A)` for one abelian variety (the body of `DegHomogPoly` at `k, A`). -/
def DegPolyAt (A : PkgI3.AbVar k) : Prop :=
  ∀ (r : ℕ) (e : Fin r → PkgI3.AbVar.End A),
    ∃ (g : ℕ) (N : MvPolynomial (Fin r) ℚ), A.dim = (g : WithBot ℕ∞) ∧ N.IsHomogeneous (2 * g) ∧
      ∀ x : Fin r → ℤ, ((degEnd (∑ i, x i • e i) : ℕ) : ℚ) = MvPolynomial.eval (fun i => (x i : ℚ)) N

theorem natCast_withBot_injective {g g' : ℕ} (h : ((g : ℕ∞) : WithBot ℕ∞) = ((g' : ℕ∞) : WithBot ℕ∞)) :
    g = g' := by
  exact_mod_cast h

/-- **Mumford §19 Thm 4 (ℓ-independence) at one `A` from the polynomiality of `deg` alone.** -/
theorem charPoly_of_degPoly (A : PkgI3.AbVar k) (hP : DegPolyAt A) (φ : PkgI3.AbVar.End A) :
    ∃ P : ℤ[X], P.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ]) := by
  classical
  obtain ⟨g, -, hg, -⟩ := hP 0 Fin.elim0
  -- every family gives the same `g`
  have hfam : ∀ D : ℕ, ∃ N : MvPolynomial (Fin (D + 1)) ℚ, N.IsHomogeneous (2 * g) ∧
      ∀ x : Fin (D + 1) → ℤ, ((degEnd (∑ i, x i • φ ^ (i : ℕ)) : ℕ) : ℚ) =
        MvPolynomial.eval (fun i => (x i : ℚ)) N := by
    intro D
    obtain ⟨g', N, hg', hN, hpoly⟩ := hP (D + 1) (fun i => φ ^ (i : ℕ))
    have : g' = g := natCast_withBot_injective (hg'.symm.trans hg)
    subst this
    exact ⟨N, hN, hpoly⟩
  obtain ⟨N, hN, hpoly⟩ := hfam (2 * g + 1)
  have hmul : ∀ ψ χ : PkgI3.AbVar.End A, degEnd ψ ≠ 0 → degEnd χ ≠ 0 →
      degEnd (ψ * χ) = degEnd ψ * degEnd χ := fun ψ χ hψ hχ =>
    degEnd_mul_of_isIsogeny ψ χ (isIsogenyMor_of_degEnd_ne_zero hψ) (isIsogenyMor_of_degEnd_ne_zero hχ)
  obtain ⟨Z, hZm, hZ⟩ := P0D_int (φ := φ) (deg := degEnd) (by omega) hN hpoly (degEnd_one A) hmul hfam
  refine ⟨Z, hZm, fun ℓ _ hℓ I _ _ b => ?_⟩
  rw [← rho_apply b φ]
  have h := charpoly_eq_P0D (φ := φ) (deg := degEnd) (by omega : 2 * g ≤ 2 * g + 1) hN hpoly
    (degEnd_one A) hmul (rho b) (card_basis_V ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof A ℓ hℓ g hg b)
    (fun χ hχ => by
      rw [rho_apply]
      exact norm_deg_le_norm_det ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof A χ hχ ℓ hℓ b)
  rw [← h, ← hZ, Polynomial.map_map]
  congr 1

/-- **The field from deg-det's `DegHomogPoly` alone** (no `homFreeFiniteAlgClosed`). -/
theorem charPolyIndepOfEllAlgClosed_of_degHomogPoly' (hP : DegHomogPoly) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed :=
  fun k _ _ A φ => charPoly_of_degPoly A (hP k A) φ

/-- **degpoly-proof's `CharPolyIndepOfEllAlgClosedNoEmb` from `DegHomogPolyNoEmb` alone.** -/
theorem charPolyIndepOfEllAlgClosedNoEmb_of_degHomogPolyNoEmb (HR : DegPolyC.DegHomogPolyNoEmb) :
    CharPolyLattice.CharPolyIndepOfEllAlgClosedNoEmb :=
  fun k _ _ he A φ => charPoly_of_degPoly A (HR k he A) φ

/-- **The field from `DegHomogPolyNoEmb` alone**: the fields with a ring homomorphism to `ℂ` by
degpoly-proof's period-lattice argument (`uniformizationLeafAll_proof`, `mumfordTorsionAlgClosed_proof`). -/
theorem charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb' (HR : DegPolyC.DegHomogPolyNoEmb) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed :=
  CharPolyLattice.charPolyIndepOfEllAlgClosed_of_noEmb uniformizationLeafAll_proof
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
    (charPolyIndepOfEllAlgClosedNoEmb_of_degHomogPolyNoEmb HR)

end ZInQ.Contrib.OneProof.CharPolyCharP

#print axioms ZInQ.Contrib.OneProof.CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb'
#print axioms ZInQ.Contrib.OneProof.CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPoly'
