import ZInQKernel.Contrib.OneProof.R16Split
import ZInQKernel.Contrib.OneProof.AfTateLambda

/-!
# `r16CoreY` from Diamond–Shurman's Theorem 9.6.5 at weight 2 (the characteristic equation on `A_f`)

Task r16-det. r16-close (`ZInQKernel/Contrib/OneProof/R16CoreYSatDet.lean`) discharged `R16Split.R16CoreY`
from four printed leaves and the glue `AfTateLam.AfDetLambda` (`det ρ_{f,λ}(Frob_p) = χ(p)p`), because
Diamond–Shurman's Theorem 9.5.4 prints only that `ρ_{f,λ}(Frob_𝔭)` *satisfies* `x² − a_p x + χ(p)p = 0`.

The printed characteristic equation of the Section 9.5 realization is Diamond–Shurman, *A First Course in
Modular Forms*, GTM 228, **Theorem 9.6.5 at `k = 2`** (corrected fourth printing, 2016, p. 404):
for a normalized eigenform `f ∈ S_k(N, χ)` and `λ ∣ ℓ`, `ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})` is unramified at
`p ∤ ℓN` and *the characteristic equation* of `ρ_{f,λ}(Frob_𝔭)` is `x² − a_p(f)x + χ(p)p^{k−1} = 0`. On the
same page Diamond–Shurman identify the weight-2 case with the construction of Section 9.5: Section 9.5
constructed `ρ_{f,λ}` for `k = 2` but did not prove its irreducibility or that the equation is the
characteristic equation. So for `k = 2` the theorem is a statement about the `λ`-component
`e_λ V_ℓ(A_f)` of Exercise 9.5.2(a), which is aftate-fix2's `V_λ = K_{f,λ} ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A_f)`.
(Human reading of this row in a print copy, issue #14 comment 7121091136: Theorem 9.6.5 at
`k = 2`, the p. 404 paragraph after it, and Section 9.5 at pp. 395–402. It rates the row a
consequence, GLUE: Diamond–Shurman print the `k = 2` characteristic equation without proof or
citation, and Section 9.5 proves only that `ρ_{f,λ}(Frob_𝔭)` satisfies it.)

* `AfTateLam.AfCharpolyDS965` (consequence, GLUE): DS Thm 9.6.5 at `k = 2` for the Section 9.5
  realization, over `K_{f,λ}`, universally over DS's `A_f`. Its statement is aftate-fix2's
  `AfTateLam.AfTateDSLambda` verbatim (`afCharpolyDS965_iff : … ↔ AfTateDSLambda := Iff.rfl`); only the
  source changes (9.6.5 with its weight-2 identification, not 9.5.4).
* `afDetLambda_of_ds965`: r16-close's glue `AfDetLambda` is a direct consequence (the constant coefficient
  of a degree-2 characteristic polynomial is the determinant; finiteness of `V_ℓ(A)` from Mumford's torsion
  theorem). Not needed by the fold.
* `r16CoreY_of_ds965`: `R16CoreY` from `HeckeJ1DS`, `AfShimura`, `AfCharpolyDS965`, `IgusaGL2DS` and
  Mumford's torsion theorem.

No `sorry`, no `axiom`, no build-time code.
-/

noncomputable section

namespace AfTateLam

open scoped TensorProduct
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open IsDedekindDomain NumberField

/-- **GLUE (Diamond–Shurman Thm 9.6.5 at `k = 2`, for the Section 9.5 realization on `A_f`, over
`K_{f,λ}`).** For every `(A, π, θ)` that is DS's `(A_f, J₁(N) ↠ A_f, K_f-action)` (`AfShimura`'s
characterization, for any model `X` of `X₁(N)`, generators, rational point, Jacobian and Hecke operators as
in `HeckeJ1DS`), every prime `ℓ` and every place `λ ∣ ℓ` of `K_f`: for `p ∤ Nℓ` every arithmetic Frobenius
`σ` at `p` acting on `V_λ(A_f) = K_{f,λ} ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A_f)` (`frobLam`, the representation `ρ_{f,λ}`
of DS §9.5, Exercise 9.5.2(a)) has characteristic polynomial `X² − a_p(f) X + χ(p) p` over
`K_{f,λ} = λ.adicCompletion K_f`.

Source: Diamond–Shurman, *A First Course in Modular Forms*, GTM 228, Theorem 9.6.5 ("the characteristic
equation of `ρ_{f,λ}(Frob_𝔭)` is `x² − a_p(f)x + χ(p)p^{k−1} = 0`"), with the identification on the same
page that for `k = 2` the representation is the one constructed in Section 9.5 (corrected fourth
printing, 2016, p. 404); `ρ_{f,λ}` and `V_ℓ(A_f)` as in Lemma 9.5.3, Theorem 9.5.4 and
Exercise 9.5.2(a) (2016 printing, §9.5 at pp. 397–402). Weakening: newforms only, `N ≥ 2`;
irreducibility and unramifiedness dropped. `K_f` a number field and finiteness of `V_λ` are the
print's presuppositions (instance arguments). The statement is `AfTateDSLambda` verbatim.

Dictionary audit (hecke-pin, `ZInQKernel/Contrib/OneProof/HeckePin.lean`): the hypotheses are about DS's
objects: `IsHeckeT`/`IsDiamond` pin `T_p`, `⟨d⟩` (`AfTateLam.HeckePin.isHeckeT_unique`,
`isDiamond_unique`), `KillsIf` is DS's `I_f` (`killsIf_iff_IfDS_of_leaves`), `(A, π)` is unique up to
unique isomorphism (`isAfQuotient_unique`) and `θ` is unique (`theta_unique`). Inputs: `X1TauPoints`,
`AbelJacobiX1` (leaf candidates) and the glue `ConstOnTauPoints`. -/
def AfCharpolyDS965 : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
    ∀ (A : AbVar ℚ) (π : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
      IsAfQuotient χ f tp δ A π → IsAfAction χ f tp δ π θ →
    ∀ [NumberField (coeffField f)] (ℓ : ℕ) [Fact ℓ.Prime]
      (lam : HeightOneSpectrum (𝓞 (coeffField f))) [lam.asIdeal.LiesOver (vQ ℓ).asIdeal],
      letI := R16Used.tensorModule ℓ A θ
      letI := (rhoLam ℓ lam).toAlgebra
      letI : Module.Free (lam.adicCompletion (coeffField f))
          (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ) :=
        Module.Free.of_divisionRing (lam.adicCompletion (coeffField f))
          (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ)
      ∀ [Module.Finite (lam.adicCompletion (coeffField f))
          (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ)],
      ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        ∃ c : coeffField f, (c : ℂ) = χ (p : ZMod N) ∧
          LinearMap.charpoly (frobLam ℓ A θ lam σ) =
            ((Polynomial.X : Polynomial (lam.adicCompletion (coeffField f))) ^ 2 -
              Polynomial.C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
                ⟨coeff f p, coeff_mem_coeffField f p⟩) * Polynomial.X +
              Polynomial.C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
                (c * (p : coeffField f))) : Polynomial (lam.adicCompletion (coeffField f)))

/-- The new leaf is aftate-fix2's `AfTateDSLambda`, verbatim. -/
theorem afCharpolyDS965_iff : AfCharpolyDS965 ↔ AfTateDSLambda := Iff.rfl

/-- The determinant and the dimension from a characteristic polynomial `X² − C t X + C d`. -/
theorem det_finrank_of_charpoly {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    [Module.Free F M] [Module.Finite F M] (g : M →ₗ[F] M) (t d : F)
    (h : g.charpoly = Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C d) :
    LinearMap.det g = d ∧ Module.finrank F M = 2 := by
  have hdeg : Module.finrank F M = 2 := by
    rw [← LinearMap.charpoly_natDegree g, h]
    compute_degree!
  refine ⟨?_, hdeg⟩
  rw [LinearMap.det_eq_sign_charpoly_coeff, h, hdeg]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]

/-- **r16-close's determinant glue is a consequence of DS Thm 9.6.5 at `k = 2`.** -/
theorem afDetLambda_of_ds965 (hM : AvSplit.MumfordTorsionAlgClosed) (h : AfCharpolyDS965) :
    AfDetLambda := by
  have hT : TateModuleFree := T5Torsion.TateFree.tateModuleFree_of_torsionStructure
    (AvSplit.torsionStructure_of_mumford hM)
  intro N χ f hN hf X _ jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct _ ℓ _ lam _ p hp hpN σ hσ
  have := finiteDimensional_V hT A ℓ
  letI := R16Used.tensorModule ℓ A θ
  letI := (rhoLam ℓ lam).toAlgebra
  have := isScalarTower_tensor (ℓ := ℓ) A θ
  have : Module.Finite (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] coeffField f) (A.V ℓ)
  letI : Module.Free (lam.adicCompletion (coeffField f))
      (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ) :=
    Module.Free.of_divisionRing (lam.adicCompletion (coeffField f))
      (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ)
  have : Module.Finite (lam.adicCompletion (coeffField f))
      (lam.adicCompletion (coeffField f) ⊗[ℚ_[ℓ] ⊗[ℚ] coeffField f] A.V ℓ) := inferInstance
  obtain ⟨c, hc, hch⟩ := h N χ f hN hf X jX tX hC hG P₀ J aj hJ tp δ htp hδ A π θ hQ hAct ℓ lam
    p hp hpN σ hσ
  exact ⟨c, hc, (det_finrank_of_charpoly _ _ _ hch).1⟩

/-- **`r16CoreY` from the printed leaves (r16-det).** `HeckeJ1DS` (Diamond–Shurman §6.3, §7.9),
`AfShimura` (Shimura 1973 Thm 1), `AfCharpolyDS965` (Diamond–Shurman Thm 9.6.5 at `k = 2` for the
Section 9.5 realization), `X1Igusa.IgusaGL2DS` (Diamond–Shurman Thm 7.6.3) and Mumford's torsion theorem. -/
theorem r16CoreY_of_ds965 (h1 : HeckeJ1DS) (h2 : AfShimura) (h3 : AfCharpolyDS965)
    (hI : X1Igusa.IgusaGL2DS) (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY :=
  r16CoreY_of_printed h1 h2 h3 hI hM

end AfTateLam
