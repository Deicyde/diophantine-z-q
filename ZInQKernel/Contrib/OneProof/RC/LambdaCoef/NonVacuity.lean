import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Obstruction
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Rank
import ZInQKernel.Contrib.OneProof.RC.CoefModules.NonVacuity

/-!
# Lane RC28 round 2, part 7: non-vacuity of the `Λ`-adic structures

Manuscript `diophantine_zq.tex` (11/5), tex 1760–1830 (the curves `E_ℓ : y² = x(x−ℓ)(x+3ℓ)`),
tex 2723–2727 (finite coefficients), 2747 (`Λ = ℤ₂[[t]]`), 2836–2838 (`T = T₂E`), 2780–2791 (the
finite characters `Ψ_i`, `α_i`) and tex 4976–5200.

The following examples instantiate the generic interfaces. The finite-support examples use
S = ∅ and assert no nonzero Tate module or fibre. Rank-two and nonzero-fibre examples below use
S = univ, so they do not discharge finite-support arithmetic hypotheses. The configuration
family has zero class and functional and no switching primes.

* `IsContChar` for the trivial character and for `α = χ_h Ψ` with `χ_h` the quadratic character of
  a square root in `K_S` and `ξ` trivial (`isContChar_one`, `isContChar_alphaLam`);
* `IsHeightOneOdd (t)` (`isHeightOneOdd_span_X`, `Fibre.lean`);
* the fibre `V_(t)` of `E_1` over `ℚ` with the full, zero and unramified conditions, genuine Galois
  Selmer data (`IsGaloisSelData`) for the finite set `S = ∅`, and the genuine configuration family
  at `(t)` (`IsGenuineFamilyAt`);
* `HasFullTwoTorsion K Set.univ W` for every elliptic `W` (`TateBasis.lean`), so `T_2E ≅ ℤ₂²` is
  not vacuous; for finite `S` it is the GLUE input (Néron–Ogg–Shafarevich); there the fibre is a
  `2`-dimensional `k(𝔭)`-vector space, not `2`-power torsion, and its Selmer complex has a nonzero
  degree-one term (the round-1 obstruction disappears on a genuine example).

Kinds: PROVED (instances and `example`s).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LambdaCoef

open NumberField IsDedekindDomain PowerSeries
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.Wiring (ResAt IsGaloisSelData IsGenuineFamilyAt)
open ZInQ.Manuscript.RC.CoefModules (curveEll isElliptic_curveEll quadChar KS)
open scoped PowerSeries.WithPiTopology

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The trivial character is continuous.** Kind: PROVED. -/
instance isContChar_one : IsContChar (1 : GKS K S →* Lambdaˣ) :=
  ⟨by simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const⟩

/-- The square root `1` of `1` in `K_S`. -/
theorem one_sq_eq : (1 : KS K S) ^ 2 = algebraMap K (KS K S) 1 := by simp

/-- **`α = χ_1 Ψ_0`**, the `Λ`-adic character attached to the square root `1` and the trivial
`ℤ₂`-character: a genuine instance of the construction `lambdaChar` (tex 2780–2791). -/
abbrev alphaLam (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) :
    GKS K S →* Lambdaˣ :=
  lambdaChar (quadChar (1 : KS K S) one_sq_eq one_ne_zero) 1

/-- `α = χ_1 Ψ_0` is continuous. Kind: PROVED. -/
instance isContChar_alphaLam : IsContChar (alphaLam K S) := inferInstance

/-- The elliptic curve `E_1 : y² = x(x − 1)(x + 3)` over `ℚ`. -/
abbrev curveE1 : WeierstrassCurve ℚ := curveEll (1 : ℚ)

instance : curveE1.IsElliptic := isElliptic_curveEll one_ne_zero

/-- The empty set of places of `ℚ`. -/
abbrev S0 : Set (HeightOneSpectrum (𝓞 ℚ)) := ∅

/-- The prime `(t)` of `Λ`. -/
abbrev Pt0 : Ideal Lambda := Ideal.span {(X : Lambda)}

/-- **Non-vacuity of the fibre with all its instances**: the genuine Galois action on
`V_(t)(E_1)` is continuous. -/
example : ContinuousSMul (GKS ℚ S0) (VP ℚ S0 curveE1 Pt0 (alphaLam ℚ S0)) := inferInstance

example : ContinuousConstSMul (ResAt Pt0) (VP ℚ S0 curveE1 Pt0 (alphaLam ℚ S0)) := inferInstance

/-- Non-vacuity of `𝕋` with its continuous action. -/
example : ContinuousSMul (GKS ℚ S0) (TLam ℚ S0 curveE1 (alphaLam ℚ S0)) := inferInstance

/-- **The full, zero and unramified fibre Selmer data of `E_1` at `(t)` are genuine Galois Selmer
data.** Kind: PROVED. -/
theorem isGaloisSelData_example :
    IsGaloisSelData (fibreRelaxed (S := S0) curveE1 Pt0 (alphaLam ℚ S0)) ∧
      IsGaloisSelData (fibreStrict (S := S0) curveE1 Pt0 (alphaLam ℚ S0)) ∧
        IsGaloisSelData (fibreUr (S := S0) curveE1 Pt0 (alphaLam ℚ S0)) :=
  ⟨isGaloisSelData_fibreRelaxed _ _ _ Set.finite_empty,
    isGaloisSelData_fibreStrict _ _ _ Set.finite_empty,
    isGaloisSelData_fibreUr _ _ _ Set.finite_empty⟩

/-- **The configuration family of `E_1` at `(t)` is genuine.** Kind: PROVED. -/
theorem isGenuineFamilyAt_example :
    IsGenuineFamilyAt Pt0 (fibreFamily (S := S0) curveE1 Pt0 (alphaLam ℚ S0)
      (fibreUrConditions curveE1 Pt0 (alphaLam ℚ S0))) :=
  isGenuineFamilyAt_fibreFamily _ _ _ Set.finite_empty _ (fibreUr_injective _ _ _)

/-- **`E[2^∞] ⊆ E(K_S)` is not vacuous** (`S` all places, `K_S = K̄`). -/
example : HasFullTwoTorsion ℚ Set.univ curveE1 := inferInstance

/-- The Tate module of `E_1` over `K̄ = ℚ_univ` has a `ℤ₂`-basis of size `2`. -/
example : Module.finrank ℤ_[2] (TateS ℚ Set.univ curveE1) = 2 := finrank_tate

/-- The fibre of `E_1` at `(t)` (over `K̄`) is a `2`-dimensional vector space over the
characteristic-zero field `k((t))`. -/
example : Module.finrank (ResAt Pt0) (VP ℚ Set.univ curveE1 Pt0 (alphaLam ℚ Set.univ)) = 2 :=
  finrank_vp _

/-- **The round-1 obstruction disappears on a genuine example**: the fibre is not `2`-power
torsion and its genuine Selmer complex has a nonzero degree-one term. -/
example : ¬ ∃ n : ℕ, ∀ v : VP ℚ Set.univ curveE1 Pt0 (alphaLam ℚ Set.univ), (2 ^ n : ℕ) • v = 0 :=
  not_two_pow_torsion _ _ _

example : Nontrivial ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx
    (fibreRelaxed (S := Set.univ) curveE1 Pt0 (alphaLam ℚ Set.univ))).toCC.X 1) :=
  nontrivial_selCx_one _ _ _ _

end ZInQ.Manuscript.RC.LambdaCoef
