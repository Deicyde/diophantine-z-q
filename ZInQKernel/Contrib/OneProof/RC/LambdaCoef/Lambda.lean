import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Topology
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Characters
import ZInQKernel.Contrib.OneProof.RC.Uniform.LambdaHalf
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.NumberTheory.Padics.MahlerBasis

/-!
# Lane RC28 round 2, part 2: `Λ = ℤ₂[[t]]`, its topology, and the `Λ`-adic character `α = χ_h Ψ`

Manuscript `diophantine_zq.tex` (11/5): `Λ = ℤ₂[[t]]` at tex 1834 and 2747; the text's finite
moving characters `Ψ_i = (1+t)^{ξ_i}` and `α_i = χ_h Ψ_i` at tex 2780–2791. Here
`Ψ = (1+t)^ξ` is built from a supplied continuous `ℤ₂`-valued character `ξ` (no ring-class tower
is supplied here) and `α = χ_h Ψ`; neither is a global moving character asserted at
tex 2780–2785. Tex 4976–5200: `R = Λ_𝔭`.

* `Λ = Lambda = ℤ_[2]⟦t⟧` (the tree's `ZInQ.Manuscript.RC.Uniform.Lambda`) with the product
  topology on coefficients (Mathlib's `PowerSeries.WithPiTopology`; it is the `(2, t)`-adic topology),
  a topological ring (`lambda_isTopologicalRing`).
* `onePlusTPow a = (1 + t)^a = Σ_k (a choose k) t^k` for `a ∈ ℤ₂` (Mathlib's binomial series over the
  binomial ring `ℤ_[2]`): `onePlusTPow_add`, `onePlusTPow_zero`, `onePlusTPow_natCast`
  (`= (1 + t)^d` for `d ∈ ℕ`), `continuous_onePlusTPow` (Mahler: `a ↦ (a choose k)` is continuous);
  `onePlusTPowHom : ℤ₂ → Λˣ` (multiplicative).
* `movingChar ξ = Ψ = (1 + t)^ξ` for a continuous `ξ : G_{K,S} → ℤ₂`; `lambdaChar χ ξ = χ · Ψ`, with
  `χ = χ_h` the quadratic character of lane RC28 round 1; `continuous_lambdaChar`.

Kinds: definitions and PROVED.
-/

/-!
This is a conditional construction for one supplied continuous Λ-valued character on a fixed
G_{K,S}. Its finite levels are the compatible reductions of that character. The manuscript's
moving characters have conductor primes varying with precision and need not be reductions of
one character (tex 2737–2741, 4269–4277). No identification with the retained inner-limit Selmer
diagrams is proved here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LambdaCoef

open NumberField IsDedekindDomain PowerSeries Filter Topology
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (charMul charMul_apply intUnitsTo IsOpenKer)
open scoped PowerSeries.WithPiTopology

/-- **`Λ` with the product topology is a topological ring.** Kind: PROVED (Mathlib). -/
theorem lambda_isTopologicalRing : IsTopologicalRing Lambda :=
  PowerSeries.WithPiTopology.instIsTopologicalRing ℤ_[2]

attribute [local instance] lambda_isTopologicalRing

/-! ### `(1 + t)^a` for `a ∈ ℤ₂` -/

/-- **`(1 + t)^a = Σ_k (a choose k) t^k`** for `a ∈ ℤ₂`. -/
def onePlusTPow (a : ℤ_[2]) : Lambda := binomialSeries ℤ_[2] a

theorem coeff_onePlusTPow (a : ℤ_[2]) (n : ℕ) : coeff n (onePlusTPow a) = Ring.choose a n := by
  rw [onePlusTPow, binomialSeries_coeff, smul_eq_mul, mul_one]

/-- `(1 + t)^(a + b) = (1 + t)^a (1 + t)^b`. Kind: PROVED. -/
theorem onePlusTPow_add (a b : ℤ_[2]) : onePlusTPow (a + b) = onePlusTPow a * onePlusTPow b :=
  binomialSeries_add a b

theorem onePlusTPow_zero : onePlusTPow 0 = 1 := binomialSeries_zero

/-- For `d ∈ ℕ`, `(1 + t)^d` is the usual power. Kind: PROVED. -/
theorem onePlusTPow_natCast (d : ℕ) : onePlusTPow d = (1 + X) ^ d := binomialSeries_nat d

/-- **`a ↦ (1 + t)^a` is continuous** (coefficientwise: Mahler's `a ↦ (a choose k)`). Kind:
PROVED. -/
theorem continuous_onePlusTPow : Continuous onePlusTPow := by
  refine continuous_iff_continuousAt.mpr fun a => ?_
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  simp only [coeff_onePlusTPow]
  exact (PadicInt.continuous_choose d).tendsto a

/-- **`a ↦ (1 + t)^a` as a homomorphism `ℤ₂ → Λˣ`.** -/
def onePlusTPowHom : Multiplicative ℤ_[2] →* Lambdaˣ where
  toFun a := ⟨onePlusTPow (Multiplicative.toAdd a), onePlusTPow (-Multiplicative.toAdd a),
    by rw [← onePlusTPow_add, add_neg_cancel, onePlusTPow_zero],
    by rw [← onePlusTPow_add, neg_add_cancel, onePlusTPow_zero]⟩
  map_one' := Units.ext onePlusTPow_zero
  map_mul' a b := Units.ext (onePlusTPow_add _ _)

theorem coe_onePlusTPowHom (a : Multiplicative ℤ_[2]) :
    ((onePlusTPowHom a : Lambdaˣ) : Lambda) = onePlusTPow (Multiplicative.toAdd a) := rfl

/-! ### The `Λ`-adic character `α = χ_h Ψ` -/

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The moving character `Ψ = (1 + t)^ξ`** (tex 2786–2791) of a character `ξ : G_{K,S} → ℤ₂`
(a supplied continuous `ℤ₂`-valued character; no ring-class tower is supplied here). -/
def movingChar (ξ : GKS K S →* Multiplicative ℤ_[2]) : GKS K S →* Lambdaˣ :=
  onePlusTPowHom.comp ξ

theorem coe_movingChar (ξ : GKS K S →* Multiplicative ℤ_[2]) (σ : GKS K S) :
    ((movingChar ξ σ : Lambdaˣ) : Lambda) = onePlusTPow (Multiplicative.toAdd (ξ σ)) := rfl

/-- `Ψ` is continuous for a continuous `ξ`. Kind: PROVED. -/
theorem continuous_movingChar (ξ : GKS K S →* Multiplicative ℤ_[2])
    (hξ : Continuous fun σ => Multiplicative.toAdd (ξ σ)) :
    Continuous fun σ => ((movingChar ξ σ : Lambdaˣ) : Lambda) :=
  continuous_onePlusTPow.comp hξ

/-- **The `Λ`-adic character `α = χ · Ψ`** (the text's finite `α_i = χ_h Ψ_i`: tex 2780–2791). -/
def lambdaChar (χ : GKS K S →* ℤˣ) (ξ : GKS K S →* Multiplicative ℤ_[2]) : GKS K S →* Lambdaˣ :=
  charMul ((intUnitsTo Lambda).comp χ) (movingChar ξ)

theorem coe_lambdaChar (χ : GKS K S →* ℤˣ) (ξ : GKS K S →* Multiplicative ℤ_[2]) (σ : GKS K S) :
    ((lambdaChar χ ξ σ : Lambdaˣ) : Lambda) =
      ((χ σ : ℤ) : Lambda) * onePlusTPow (Multiplicative.toAdd (ξ σ)) := by
  rw [lambdaChar, charMul_apply, Units.val_mul]
  rfl

/-- A character with open kernel is continuous into any topological monoid of units, read in the
ring. Kind: PROVED. -/
theorem continuous_int_of_isOpenKer (χ : GKS K S →* ℤˣ) [hχ : IsOpenKer χ] :
    Continuous fun σ => ((χ σ : ℤ) : Lambda) := by
  refine continuous_iff_continuousAt.mpr fun σ₀ => ?_
  have hopen : IsOpen ((fun σ => σ₀⁻¹ * σ) ⁻¹' (χ.ker : Set (GKS K S))) :=
    (continuous_const.mul continuous_id).isOpen_preimage _ hχ.isOpen_ker
  have hmem : σ₀ ∈ (fun σ => σ₀⁻¹ * σ) ⁻¹' (χ.ker : Set (GKS K S)) := by
    simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact χ.ker.one_mem
  refine (continuousAt_const (y := ((χ σ₀ : ℤ) : Lambda))).congr ?_
  filter_upwards [hopen.mem_nhds hmem] with σ hσ
  have h : χ (σ₀⁻¹ * σ) = 1 := (MonoidHom.mem_ker).mp hσ
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  rw [h]

/-- **`α = χ Ψ` is continuous** (`χ` with open kernel, `ξ` continuous). Kind: PROVED. -/
theorem continuous_lambdaChar (χ : GKS K S →* ℤˣ) [IsOpenKer χ]
    (ξ : GKS K S →* Multiplicative ℤ_[2]) (hξ : Continuous fun σ => Multiplicative.toAdd (ξ σ)) :
    Continuous fun σ => ((lambdaChar χ ξ σ : Lambdaˣ) : Lambda) := by
  simp only [coe_lambdaChar]
  exact (continuous_int_of_isOpenKer χ).mul (continuous_onePlusTPow.comp hξ)

end ZInQ.Manuscript.RC.LambdaCoef
