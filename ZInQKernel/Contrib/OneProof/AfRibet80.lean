import ZInQKernel.Contrib.OneProof.R16CoreYDS965
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed

/-!
# `afCharpolyDS965` as Ribet prints it: trace and determinant of Frobenius on `V_ℓ(A_f)`

The row `afCharpolyDS965` (`AfTateLam.AfCharpolyDS965`) states that every Frobenius at `p ∤ Nℓ` acting on
`V_λ(A_f) = K_{f,λ} ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A_f)` has characteristic polynomial `X² − a_p X + χ(p) p`. Its source was
Diamond–Shurman, Thm 9.6.5 at `k = 2`; the human reading of the row (issue #14 comment 7121091136) rated it a
consequence because Diamond–Shurman print the `k = 2` characteristic equation without proof or citation, for a
representation transported to `A_f`.

Ribet, *Twists of modular forms and endomorphisms of abelian varieties*, Math. Ann. 253 (1980), 43–62, §4,
pp. 50–51, states the same fact on Shimura's quotient `A_f` itself, with its sources: `V = V_l(A_f)` is a free
`E ⊗ ℚ_l`-module of rank 2, and the image of a Frobenius element at `p ∤ lN` has trace `a_p` and determinant
`ε(p) p`, computed relative to `E ⊗ ℚ_l`, "because of the Eichler-Shimura relation (see [15, Sect. 1] and
[18, Chap. 7])"; the proof of (4.1) on p. 51 introduces "the decomposition `V = ∏ V_λ` induced by the decomposition
of `E ⊗ ℚ_l` as a product of `l`-adic fields `E_λ`".

* `AfRibet80TraceDetLam`: Ribet's statement read on each factor `V_λ`: `V_λ` has dimension 2 over `E_λ`, and the
  trace and determinant of Frobenius are the images of `a_p` and `ε(p) p`.
* `charpoly_eq_iff_trace_det`: on a finite-dimensional space, `charpoly = X² − t X + d` if and only if the
  dimension is 2, the trace is `t` and the determinant is `d`.
* `afCharpolyDS965_iff_ribet80`: the row and the leaf are equivalent (finiteness of `V_ℓ(A)` from Mumford's torsion
  theorem, proved: `ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`). So the leaf is not stronger
  than the row.
-/

set_option autoImplicit false

noncomputable section

namespace AfTateLam

open scoped TensorProduct
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open IsDedekindDomain NumberField

namespace Ribet80

/-- **Ribet, *Twists of modular forms and endomorphisms of abelian varieties*, Math. Ann. 253 (1980), 43–62, §4,
pp. 50–51, on each `λ`-factor.**

* p. 50: "Let f be a newform on Γ₁(N) and let ε : (ℤ/Nℤ)* → ℂ* be its (Nebentypus) character. As in [12], we
  regard ε as a character on G = Gal(ℚ̄/ℚ), and we may view it as taking values in the coefficient field E of f.
  Let A = A_f be the factor of J₁(N) attached to f (Sect. 2). Let l be a prime (fixed in what follows), and let
  V = V_l(A) be the usual ℚ_l-adic Tate module attached to A. Then V is simultaneously, and compatibly, a
  ℚ_l[G]-module and a free E ⊗ ℚ_l-module of rank 2. The action of G on V is thus described by a map
  ρ : G → Aut_{E⊗ℚ} V ≃ GL(2, E ⊗ ℚ_l),"
* p. 51: "which is known to be the l-adic representation attached to f, because of the Eichler-Shimura relation
  (see [15, Sect. 1] and [18, Chap. 7]). This means that ρ is unramified at each prime p not dividing lN and that
  the image under ρ of a Frobenius element φ_p ∈ G for such a prime p has trace (resp. determinant) equal to a_p
  [resp. ε(p)p]. Here we calculate trace and determinant relative to E ⊗ ℚ_l, i.e., by viewing V as a free
  E ⊗ ℚ_l-module rather than a ℚ_l-vector space."
* p. 51, proof of Proposition (4.1): "We introduce the decomposition V = ∏ V_λ induced by the decomposition of
  E ⊗ ℚ_l as a product of l-adic fields E_λ."

Lean form, over the row's objects (`AtFrobLam`: `A_f` as in `AfShimura`, for any model of `X₁(N)`):
`V_λ = E_λ ⊗_{ℚ_ℓ ⊗ E} V_ℓ(A_f)` (`R16Used.tensorModule`, `rhoLam`) is the `λ`-factor of `V`; it has dimension 2
over `E_λ = λ.adicCompletion E` (the free rank-2 clause, on the factor), and for `p ∤ Nℓ` and a Frobenius `σ` at `p`
the trace and determinant of `σ` on `V_λ` are the images of `a_p` and `ε(p) p` (the trace and determinant over
`E ⊗ ℚ_ℓ`, on the factor). Reading steps: the statement is read on each factor `V_λ` of the printed decomposition;
`ε(p)` is an element `c` of `E` with `c = χ(p)` in `ℂ`; unramifiedness is dropped. -/
def AfRibet80TraceDetLam : Prop :=
  AtFrobLam fun N χ f A θ _ ℓ _ lam _ p σ =>
    letI := R16Used.tensorModule ℓ A θ
    letI := (rhoLam ℓ lam).toAlgebra
    Module.finrank (lam.adicCompletion (coeffField f))
        (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ) = 2 ∧
    ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
      LinearMap.trace (lam.adicCompletion (coeffField f))
          (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ) (frobLam ℓ A θ lam σ) =
        algebraMap (coeffField f) (lam.adicCompletion (coeffField f)) ⟨coeff f p, coeff_mem_coeffField f p⟩ ∧
      LinearMap.det (frobLam ℓ A θ lam σ) =
        algebraMap (coeffField f) (lam.adicCompletion (coeffField f)) (c * (p : coeffField f))

/-- On a finite-dimensional vector space, the characteristic polynomial is `X² − t X + d` exactly when the dimension
is 2, the trace is `t` and the determinant is `d`. -/
theorem charpoly_eq_iff_trace_det {F M : Type*} [Field F] [AddCommGroup M] [Module F M] [Module.Finite F M]
    (g : M →ₗ[F] M) (t d : F) :
    g.charpoly = Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d ↔
      Module.finrank F M = 2 ∧ LinearMap.trace F M g = t ∧ LinearMap.det g = d := by
  constructor
  · intro h
    obtain ⟨hdet, hrk⟩ := det_finrank_of_charpoly g t d h
    refine ⟨hrk, ?_, hdet⟩
    let b := Module.finBasisOfFinrankEq F M hrk
    rw [LinearMap.trace_eq_matrix_trace F b g, Matrix.trace_eq_neg_charpoly_coeff,
      LinearMap.charpoly_toMatrix g b, h]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
  · rintro ⟨hrk, ht, hd⟩
    let b := Module.finBasisOfFinrankEq F M hrk
    rw [← LinearMap.charpoly_toMatrix g b, Matrix.charpoly_fin_two, ← LinearMap.trace_eq_matrix_trace F b g,
      LinearMap.det_toMatrix b g, ht, hd]

/-- The row gives the leaf (finiteness of `V_ℓ(A)` from Mumford's torsion theorem). -/
theorem afRibet80_of_afCharpolyDS965 (hM : AvSplit.MumfordTorsionAlgClosed) (h : AfCharpolyDS965) :
    AfRibet80TraceDetLam := by
  have hT : TateModuleFree := T5Torsion.TateFree.tateModuleFree_of_torsionStructure
    (AvSplit.torsionStructure_of_mumford hM)
  intro N χ f hN hf X _ jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct _ ℓ _ lam _ p hp hpN σ hσ
  have := finiteDimensional_V hT A ℓ
  let := R16Used.tensorModule ℓ A θ
  let := (rhoLam ℓ lam).toAlgebra
  have := isScalarTower_tensor (ℓ := ℓ) A θ
  have : Module.Finite (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ)
  let : Module.Free (lam.adicCompletion (coeffField f))
      (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ) :=
    Module.Free.of_divisionRing (lam.adicCompletion (coeffField f))
      (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ)
  have : Module.Finite (lam.adicCompletion (coeffField f))
      (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ) := inferInstance
  obtain ⟨c, hc, hch⟩ := h N χ f hN hf X jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct ℓ lam
    p hp hpN σ hσ
  obtain ⟨hrk, htr, hdet⟩ := (charpoly_eq_iff_trace_det _ _ _).1 hch
  exact ⟨hrk, c, hc, htr, hdet⟩

/-- The leaf gives the row. -/
theorem afCharpolyDS965_of_afRibet80 (h : AfRibet80TraceDetLam) : AfCharpolyDS965 := by
  intro N χ f hN hf X _ jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct _ ℓ _ lam _ _ p hp hpN σ hσ
  obtain ⟨hrk, c, hc, htr, hdet⟩ := h N χ f hN hf X jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct ℓ lam
    p hp hpN σ hσ
  exact ⟨c, hc, (charpoly_eq_iff_trace_det _ _ _).2 ⟨hrk, htr, hdet⟩⟩

/-- **The row `afCharpolyDS965` is equivalent to Ribet's statement on the `λ`-factors.** -/
theorem afCharpolyDS965_iff_ribet80 : AfCharpolyDS965 ↔ AfRibet80TraceDetLam :=
  ⟨afRibet80_of_afCharpolyDS965 ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof,
    afCharpolyDS965_of_afRibet80⟩

end Ribet80

end AfTateLam
