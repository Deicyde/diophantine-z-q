import ZInQKernel.Contrib.OneProof.GrossZagierHeegner
import ZInQKernel.Contrib.GZStatements.Weak

/-!
# gz-hl3: the `C_d` form `GZStatements.GrossZagierHeegnerCd` from `C_d`-restricted leaves

Task gz-hl3 (2026-11-15). `ZInQ.GZStatements.GrossZagierHeegnerCd` (gz-statements' proposed
replacement for `hL3`, not adopted by the owner) is `GZDecomp.GrossZagierHeegner` for
`E = C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)` squarefree. Its split is the general one restricted to
`C_d`, except that the modular parametrization of `C_d` comes from Shimura's theorem on CM curves
(`ShimuraCMParamCd`) instead of Eichler–Shimura plus Faltings' isogeny theorem. Each restricted
leaf is implied by the corresponding general leaf (`…Cd_of_…`).
-/

noncomputable section

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZHL3

/-- **Modular parametrization of `C_d` (Shimura's theorem for CM curves), analytic form.** For
`d ≡ 5 (mod 8)` squarefree, `C_d : y² = x³ − d²x` has a `ℚ`-rational modular parametrization
`τ ↦ weierPt C_d L (c φ_f(τ))`, `c ∈ ℚ^×`, from any newform `f` with `aₙ(f) = aₙ(C_d)`.

Source: G. Shimura, *On elliptic curves with complex multiplication as factors of the Jacobians of
modular function fields*, Nagoya Math. J. 43 (1971), 199–208 (an elliptic curve over `ℚ` with
complex multiplication is a `ℚ`-quotient of `J₀(N)`, `N` its conductor; UNVERIFIED statement and
numbers), with the rationality of the pullback of the invariant differential (as in
`StrongWeilCurve`). Implied by the general leaves (`shimuraCMParamCd_of_leaves`). -/
def ShimuraCMParamCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → EichlerShimuraParamAt (shortCurve (-(d : ℚ) ^ 2))

/-- `HeegnerPointRationalAt C_d`, `d ≡ 5 (mod 8)` squarefree. -/
def HeegnerPointRationalCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeegnerPointRationalAt (shortCurve (-(d : ℚ) ^ 2))

/-- `GrossZagierFormulaAt C_d`, `d ≡ 5 (mod 8)` squarefree. -/
def GrossZagierFormulaCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → GrossZagierFormulaAt (shortCurve (-(d : ℚ) ^ 2))

/-- `GrossConjugationAt C_d`, `d ≡ 5 (mod 8)` squarefree. -/
def GrossConjugationCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → GrossConjugationAt (shortCurve (-(d : ℚ) ^ 2))

/-- **`GZStatements.GrossZagierHeegnerCd` from the `C_d`-restricted leaves.** -/
theorem grossZagierHeegnerCd_of_leaves (hU : WeierstrassUniformization)
    (hES : ShimuraCMParamCd) (hHP : HeegnerPointRationalCd) (hGZ : GrossZagierFormulaCd)
    (hGC : GrossConjugationCd) : ZInQ.GZStatements.GrossZagierHeegnerCd := by
  intro d hd hsq
  have := shortCurve_cd_isElliptic (d := d) (by omega)
  exact heegner_at hU _ (hES d hd hsq) (hHP d hd hsq) (hGZ d hd hsq) (hGC d hd hsq)

/-! The restricted leaves are weaker than the general ones. -/

theorem shimuraCMParamCd_of_leaves (hU : WeierstrassUniformization) (hSW : StrongWeilCurve)
    (hI : IsogenyLattice) : ShimuraCMParamCd := fun d hd _ => by
  have := shortCurve_cd_isElliptic (d := d) (by omega)
  exact eichlerShimuraParamAt_of_leaves hU hSW hI _

theorem heegnerPointRationalCd_of (h : HeegnerPointRational) : HeegnerPointRationalCd :=
  fun d hd _ => by
    have := shortCurve_cd_isElliptic (d := d) (by omega)
    exact h _

theorem grossZagierFormulaCd_of (h : GrossZagierFormula) : GrossZagierFormulaCd :=
  fun d hd _ => by
    have := shortCurve_cd_isElliptic (d := d) (by omega)
    exact h _

theorem grossConjugationCd_of (h : GrossConjugation) : GrossConjugationCd :=
  fun d hd _ => by
    have := shortCurve_cd_isElliptic (d := d) (by omega)
    exact h _

end ZInQ.GZHL3
