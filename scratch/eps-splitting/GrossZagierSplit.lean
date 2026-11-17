import ZInQKernel.Contrib.OneProof.GrossZagierScheme
import ZInQKernel.Contrib.OneProof.GrossZagierSplit.QuadSplit

/-!
# eps-splitting: the Gross–Zagier leaf with the twist and the Heegner hypothesis by splitting in `K`

Task eps-splitting (2026-11-17). Report: `docs/research/eps-splitting.md`; scratch and log:
`scratch/eps-splitting/`.

hgz-steps' leaf `ZInQ.GZSch.GrossZagierCurveCd` states the Heegner hypothesis as `ε_D(p) = 1` and
the twist as `f ⊗ ε_D`, with `ε_D` the Kronecker symbol `(D/·)` (`ZInQ.HGZSteps.epsD`).
Gross–Zagier phrase both through `K = ℚ(√D)`: every prime `p ∣ N` splits in `K`, and `ε` is the
quadratic character of `K`. The new leaf `GrossZagierCurveCdSplit` says exactly that, over
`IsSplitIn K p` (two distinct primes of `𝓞 K` over `p`) and `quadChar K` (the completely
multiplicative function whose value at a prime is `1`, `−1`, `0` as `p` splits, is inert, ramifies).

`grossZagierAlgOptCd_of_split : GrossZagierCurveCdSplit → GZAlg.GrossZagierAlgOptCd` (the binder
`hGZ` of `frozenTarget`) goes through `grossZagierCurveCd_of_split`, which uses
`ZInQ.EpsSplit.splitType_epsD` and `ZInQ.EpsSplit.quadChar_eq_epsD` (Kummer–Dedekind for
`𝓞_K = ℤ[(D + √D)/2]`). The converse `grossZagierCurveCdSplit_of_curveCd` shows that the two leaves
are equivalent, so the new one is not stronger.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter Topology HeckeRing.GL2
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZSplit

open ZInQ.GZSch ZInQ.GZAlg ZInQ.GZDict2

/-- **The Gross–Zagier formula for a modular parametrization `π : X₀(N) → E`, with the Heegner
hypothesis and the twist through `K = ℚ(√D)` (Gross–Zagier 1986, Thm I.6.3 and Ch. V Thm 2.1;
positive constant forgotten).**

As `ZInQ.GZSch.GrossZagierCurveAt` (hgz-steps), except:

* `K` (a quadratic field with `δ ∈ K`, `δ² = D`, i.e. `K = ℚ(√D)`) is introduced before the
  Heegner hypothesis, which reads: **every prime `p ∣ N` splits in `K`** (`IsSplitIn K p`: two
  distinct prime ideals of `𝓞 K` lie over `p`);
* the twist is by **the quadratic character `ε` of `K`** (`quadChar K`: completely multiplicative,
  `ε(p) = 1, −1, 0` as `p` splits, is inert, ramifies in `K`), so `G` continues `L(f ⊗ ε, s)` and
  `L(E/K, s) = L(f, s) L(f ⊗ ε, s)`.

Source: B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84
(1986), 225–320, Thm I.6.3 and Ch. V §2 (Thm 2.1), for any modular parametrization
`π : X₀(N) → E` with `π(∞) = 0` (fixed in V §2, p. 310). Weaker than the print: the constant is
replaced by `∃ κ > 0`, and `y` may be any nonzero multiple of `y_K`. -/
def GrossZagierCurveAtSplit (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) →
    ∀ (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX →
    ZInQ.Contrib.CurvesG.IsNormalScheme X → topologicalKrullDim X = 1 →
    ∀ ι : X.functionField ≃+* X0Field N,
    ∀ π : X ⟶ ESch E, π ≫ toSpecQ E = sX →
    (∃ p₁ p₂ : X, π p₁ ≠ π p₂) →
    (∀ p : X, IsCuspInfty N ι p → π p ∉ (chartZ E).opensRange) →
    ∀ D β : ℤ, ZInQ.GZDecomp.IsOddImagFundDisc D → D < -4 →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    (∀ p : ℕ, p.Prime → p ∣ N → ZInQ.EpsSplit.IsSplitIn K p) →
    (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ (R : Type) [Fintype R] (τ : R → ℍ), ZInQ.GZModuli.IsHeegnerPointReps N D β τ →
    ∀ x : R → (Spec (CommRingCat.of ℂ) ⟶ X), (∀ r, IsPointAt N ι (τ r) (x r)) →
    ∀ ιK : K →ₐ[ℚ] ℂ, ιK δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ n : ℤ, n ≠ 0 →
    ∀ y : (E⁄K).Point, WeierstrassCurve.Affine.Point.map ιK y = n • ∑ r, ptOf E (x r ≫ π) →
    ∀ F G : ℂ → ℂ, ZInQ.GZDecomp.IsEntireCont (ZInQ.GZDecomp.coeff f) 2 F →
      ZInQ.GZDecomp.IsEntireCont
        (fun m => ZInQ.GZDecomp.coeff f m * (ZInQ.EpsSplit.quadChar K m : ℂ)) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

/-- **The leaf of the `C_d` route, curve form with the twist by splitting in `K`**:
`GrossZagierCurveAtSplit E'` for every short model `E'` in the isogeny class of
`C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)` squarefree. -/
def GrossZagierCurveCdSplit : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], ZInQ.GZOptimal.IsShortModel E' →
      (∀ n : ℕ, n ≠ 0 → E'.LFunction n = (ZInQ.shortCurve (-(d : ℚ) ^ 2)).LFunction n) →
      GrossZagierCurveAtSplit E'

theorem isFundamentalDiscr_of_isOddImagFundDisc {D : ℤ} (hD : ZInQ.GZDecomp.IsOddImagFundDisc D) :
    Int.IsFundamentalDiscr D :=
  Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨hD.2.1, hD.2.2⟩)

/-- The twisted coefficients agree: `a_m ε_K(m) = a_m ε_D(m)`. -/
theorem twist_quadChar_eq {N : ℕ} [NeZero N] (f : Newform N 2) {D : ℤ}
    (hD : ZInQ.GZDecomp.IsOddImagFundDisc D) {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {δ : K} (hδ : δ ^ 2 = (D : K)) :
    (fun m => ZInQ.GZDecomp.coeff f m * (ZInQ.EpsSplit.quadChar K m : ℂ)) =
      fun m => ZInQ.GZDecomp.coeff f m * (ZInQ.HGZSteps.epsD D m : ℂ) := by
  funext m
  rw [ZInQ.EpsSplit.quadChar_eq_epsD (isFundamentalDiscr_of_isOddImagFundDisc hD) hD.1 hK hδ]

/-- **The `ε_D` leaf from the splitting leaf** (one curve). -/
theorem grossZagierCurveAt_of_split {E : WeierstrassCurve ℚ} (h : GrossZagierCurveAtSplit E) :
    GrossZagierCurveAt E := by
  intro N _ f hχ hf X _ sX hprop hN hdim ι π hπ hnc hcusp D β hD hD4 hH hβ R _ τ hτ x hx
    K _ _ _ hK δ hδ ιK hιK n hn y hy F G hF hG
  refine h N f hχ hf X sX hprop hN hdim ι π hπ hnc hcusp D β hD hD4 K hK δ hδ ?_ hβ R τ hτ x hx
    ιK hιK n hn y hy F G hF ?_
  · intro p hp hpN
    exact (ZInQ.EpsSplit.epsD_eq_one_iff_isSplitIn (isFundamentalDiscr_of_isOddImagFundDisc hD)
      hD.1 hK hδ hp).mp (hH p hp hpN)
  · rw [twist_quadChar_eq f hD hK hδ]; exact hG

/-- **The splitting leaf from the `ε_D` leaf** (one curve): the two leaves are equivalent. -/
theorem grossZagierCurveAtSplit_of_curveAt {E : WeierstrassCurve ℚ} (h : GrossZagierCurveAt E) :
    GrossZagierCurveAtSplit E := by
  intro N _ f hχ hf X _ sX hprop hN hdim ι π hπ hnc hcusp D β hD hD4 K _ _ _ hK δ hδ hH hβ R _ τ
    hτ x hx ιK hιK n hn y hy F G hF hG
  refine h N f hχ hf X sX hprop hN hdim ι π hπ hnc hcusp D β hD hD4 ?_ hβ R τ hτ x hx K hK δ hδ
    ιK hιK n hn y hy F G hF ?_
  · intro p hp hpN
    exact (ZInQ.EpsSplit.epsD_eq_one_iff_isSplitIn (isFundamentalDiscr_of_isOddImagFundDisc hD)
      hD.1 hK hδ hp).mpr (hH p hp hpN)
  · rw [← twist_quadChar_eq f hD hK hδ]; exact hG

theorem grossZagierCurveCd_of_split (h : GrossZagierCurveCdSplit) : GrossZagierCurveCd :=
  fun d hd hsq E' _ hE' hL => grossZagierCurveAt_of_split (h d hd hsq E' hE' hL)

theorem grossZagierCurveCdSplit_of_curveCd (h : GrossZagierCurveCd) : GrossZagierCurveCdSplit :=
  fun d hd hsq E' _ hE' hL => grossZagierCurveAtSplit_of_curveAt (h d hd hsq E' hE' hL)

/-- **What `frozenTarget` reads (`hGZ`), from the splitting leaf.** -/
theorem grossZagierAlgOptCd_of_split (h : GrossZagierCurveCdSplit) : GZAlg.GrossZagierAlgOptCd :=
  grossZagierAlgOptCd_of_curve (grossZagierCurveCd_of_split h)

end ZInQ.GZSplit
