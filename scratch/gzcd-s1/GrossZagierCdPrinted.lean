import ZInQKernel.Contrib.OneProof.GrossZagierSplitUnique
import ZInQKernel.Contrib.OneProof.GrossZagierCdPrinted.Discr
import ZInQKernel.Contrib.OneProof.TYZThm33Curve.Normal

/-!
# gzcd-s1: the Gross–Zagier leaf `hGZ` in printed form

Task gzcd-s1 (2026-11-17). Report: `docs/research/gzcd-s1.md`; scratch and log: `scratch/gzcd-s1/`.

The binder `hGZ` of `frozenTarget` has type hgz-steps' `ZInQ.GZSch.GrossZagierCurveCd`. The strict
leaf review (queue12, 2026-11-17) rated it GLUE (consequence) on three steps: S1 (the leaf ranges
over every normal proper model of `X₀(N)`), G4(b) (`V₊(Z) ∩ ESch E = {O}`) and S2 (`ε_D` versus the
splitting character). h33-d1 proved S1 (`GZUnique.model_transfer`) and G4(b); eps-splitting proved
S2 for `K` given by a square root of `D`. This file adds the last bridge, the field `K` given by
its discriminant (`NumberField.discr K = D`, `GZDiscr.discr_eq_of_sq`, `GZDiscr.exists_sq_eq_discr`),
and states the leaf `GrossZagierCurveCdPrinted`:

* `π(∞) = O` literally (`O = H33D1.ptO E`, by G4(b));

* one normal proper model `(X, ι)` of `X₀(N)` (some model, not every model);
* `K` an imaginary quadratic field of discriminant `D` (no chosen `√D`), every `p ∣ N` split in `K`,
  the twist by the quadratic character of `K`;
* any embedding `ιK : K → ℂ`.

Main results:
* `grossZagierCurveCd_iff_printed : GZSch.GrossZagierCurveCd ↔ GrossZagierCurveCdPrinted`: the
  current type of `hGZ` is equivalent in Lean to the printed form;
* `grossZagierAlgOptCd_of_printed`: the binder `hGZ` read by `frozenTarget`, from the printed leaf.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter Topology HeckeRing.GL2
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZCdPrinted

open ZInQ.GZSch ZInQ.GZAlg ZInQ.GZDict2 ZInQ.GZSplit ZInQ.GZUnique ZInQ.GZSplitUnique

/-- **The Gross–Zagier statement on one model `(X, ι)` of `X₀(N)`, with `K` given by its
discriminant**: eps-splitting's / h33-d1's `GZSplitBody` with the binders `δ : K, δ² = D` and
`ιK δ = i √|D|` replaced by `NumberField.discr K = D` and an arbitrary embedding `ιK`, and
`π(∞) ∉ D₊(Z)` replaced by `π(∞) = O` (`H33D1.ptO E = [0 : 1 : 0]`; equivalent by G4(b),
`H33D1.not_mem_chartZ_iff`). -/
def GZPrintedBody (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N] (f : Newform N 2) (X : Scheme.{0})
    [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ)) (ι : X.functionField ≃+* X0Field N) : Prop :=
    ∀ π : X ⟶ ESch E, π ≫ toSpecQ E = sX →
    (∃ p₁ p₂ : X, π p₁ ≠ π p₂) →
    (∀ p : X, IsCuspInfty N ι p → π p = ZInQ.H33D1.ptO E) →
    ∀ D β : ℤ, ZInQ.GZDecomp.IsOddImagFundDisc D → D < -4 →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    NumberField.discr K = D →
    (∀ p : ℕ, p.Prime → p ∣ N → ZInQ.EpsSplit.IsSplitIn K p) →
    (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ (R : Type) [Fintype R] (τ : R → ℍ), ZInQ.GZModuli.IsHeegnerPointReps N D β τ →
    ∀ x : R → (Spec (CommRingCat.of ℂ) ⟶ X), (∀ r, IsPointAt N ι (τ r) (x r)) →
    ∀ ιK : K →ₐ[ℚ] ℂ,
    ∀ n : ℤ, n ≠ 0 →
    ∀ y : (E⁄K).Point, WeierstrassCurve.Affine.Point.map ιK y = n • ∑ r, ptOf E (x r ≫ π) →
    ∀ F G : ℂ → ℂ, ZInQ.GZDecomp.IsEntireCont (ZInQ.GZDecomp.coeff f) 2 F →
      ZInQ.GZDecomp.IsEntireCont
        (fun m => ZInQ.GZDecomp.coeff f m * (ZInQ.EpsSplit.quadChar K m : ℂ)) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

/-- An embedding of `K ∋ δ₀`, `δ₀² = D < 0`, sends `δ₀` or `-δ₀` to `i √|D|`. -/
theorem exists_sqrt_embedding {K : Type} [Field K] [CharZero K] {D : ℤ} (hneg : D < 0) {δ₀ : K}
    (hδ₀ : δ₀ ^ 2 = (D : K)) (ιK : K →ₐ[ℚ] ℂ) :
    ∃ δ : K, δ ^ 2 = (D : K) ∧ ιK δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) := by
  have hsq : (ιK δ₀) ^ 2 = (Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)) ^ 2 := by
    rw [← map_pow, hδ₀, map_intCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (by have : (D : ℝ) < 0 := by exact_mod_cast hneg
                       linarith)]
    push_cast; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact ⟨δ₀, hδ₀, h⟩
  · exact ⟨-δ₀, by rw [neg_sq, hδ₀], by rw [map_neg, h, neg_neg]⟩

/-- **The two bodies agree** (on every model). -/
theorem gzPrintedBody_iff (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N] (f : Newform N 2)
    (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ))
    (ι : X.functionField ≃+* X0Field N) :
    GZPrintedBody E N f X sX ι ↔ GZSplitBody E N f X sX ι := by
  constructor
  · intro h π hπ hnc hcusp D β hD hD4 K _ _ _ hK δ hδ hH hβ R _ τ hτ x hx ιK _ n hn y hy
      F G hF hG
    exact h π hπ hnc (fun p hp => (ZInQ.H33D1.not_mem_chartZ_iff E _).mp (hcusp p hp)) D β hD hD4 K hK
      (GZDiscr.discr_eq_of_sq (isFundamentalDiscr_of_isOddImagFundDisc hD) hD.1 hK hδ)
      hH hβ R τ hτ x hx ιK n hn y hy F G hF hG
  · intro h π hπ hnc hcusp D β hD hD4 K _ _ _ hK hdisc hH hβ R _ τ hτ x hx ιK n hn y hy
      F G hF hG
    obtain ⟨δ₀, hδ₀⟩ := GZDiscr.exists_sq_eq_discr hK
    rw [hdisc] at hδ₀
    obtain ⟨δ, hδ, hιδ⟩ := exists_sqrt_embedding hD.1 hδ₀ ιK
    exact h π hπ hnc (fun p hp => (ZInQ.H33D1.not_mem_chartZ_iff E _).mpr (hcusp p hp)) D β hD hD4 K hK δ hδ hH hβ R τ hτ x hx ιK hιδ n hn y hy F G hF hG

/-- **Leaf (Gross–Zagier, printed form): the Gross–Zagier formula for a modular parametrization
`π : X₀(N) → E`, on one model of `X₀(N)`, for the imaginary quadratic field `K` of discriminant
`D`** (Gross–Zagier 1986, Thm I.6.3 and Ch. V Thm 2.1; positive constant forgotten).

* `E/ℚ` has the L-series of the newform `f` of level `N`, trivial character.
* `X₀(N)` is represented by **some** integral normal scheme `X`, proper of dimension `1` over `ℚ`,
  with function field `ι : K(X) ≃ ℚ(X₀(N)) = ℚ(j, j_N) ⊂ ℚ((q))` (the canonical model `X₀(N)/ℚ`
  is one; Shimura 1971 §6.7, UNVERIFIED locator).
* `π : X ⟶ ESch E` (`ESch E = Proj ℚ[X, Y, Z]/(F_E)`) is any nonconstant morphism over `ℚ` with
  `π(∞) = O` (`O = [0 : 1 : 0]`, the point `H33D1.ptO E`).
* `D < −4` an odd fundamental discriminant, `K` the imaginary quadratic field of discriminant `D`
  (`NumberField.discr K = D`), every prime `p ∣ N` split in `K`, `β² ≡ D (mod 4N)`.
* `x_r : Spec ℂ ⟶ X` the Heegner points `τ_r` of discriminant `D` and residue `β`.
* `ιK : K → ℂ` an embedding, `y ∈ E(K)` with `ιK(y) = n · Σ_r π(x_r)`, `n ≠ 0`.
* `F`, `G` the entire continuations of `L(f, s)` and of `L(f ⊗ ε_K, s)`, `ε_K` the quadratic
  character of `K` (`EpsSplit.quadChar K`: `1`, `−1`, `0` at split, inert, ramified primes).

Then `L'(E/K, 1) = (F G)'(1) = κ · ĥ(y)` for some real `κ > 0`.

Source: B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84
(1986), 225–320, Thm I.6.3 and Ch. V §2 (Thm 2.1), for any modular parametrization with
`π(∞) = 0` (V §2, p. 310). Weaker than the print: `∃ κ > 0` for the constant, `y` any nonzero
multiple of `y_K`, one model. -/
def GrossZagierCurveAtPrinted (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX ∧
      ZInQ.Contrib.CurvesG.IsNormalScheme X ∧ topologicalKrullDim X = 1 ∧
      ∃ ι : X.functionField ≃+* X0Field N, GZPrintedBody E N f X sX ι

/-- **Leaf of the `C_d` route (printed form)**: `GrossZagierCurveAtPrinted E'` for every short
model `E'` in the isogeny class of `C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)` squarefree. -/
def GrossZagierCurveCdPrinted : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], ZInQ.GZOptimal.IsShortModel E' →
      (∀ n : ℕ, n ≠ 0 → E'.LFunction n = (ZInQ.shortCurve (-(d : ℚ) ^ 2)).LFunction n) →
      GrossZagierCurveAtPrinted E'

theorem grossZagierCurveAtPrinted_iff (E : WeierstrassCurve ℚ) :
    GrossZagierCurveAtPrinted E ↔ GrossZagierCurveAtSplitSome E := by
  unfold GrossZagierCurveAtPrinted GrossZagierCurveAtSplitSome
  simp only [gzPrintedBody_iff]

theorem grossZagierCurveCdPrinted_iff : GrossZagierCurveCdPrinted ↔ GrossZagierCurveCdSplitSome := by
  unfold GrossZagierCurveCdPrinted GrossZagierCurveCdSplitSome
  simp only [grossZagierCurveAtPrinted_iff]

/-- **The current type of `hGZ` is equivalent to the printed one-model leaf.** -/
theorem grossZagierCurveCd_iff_printed : GrossZagierCurveCd ↔ GrossZagierCurveCdPrinted := by
  rw [grossZagierCurveCdPrinted_iff]
  constructor
  · intro h d hd hsq E' _ hE' hL
    exact grossZagierCurveAtSplitSome_of_all E' (grossZagierCurveCdSplit_of_curveCd h d hd hsq E' hE' hL)
  · intro h
    exact grossZagierCurveCd_of_split (grossZagierCurveCdSplit_of_some h)

/-- **`hGZ` (hgz-steps' type) from the printed leaf.** -/
theorem grossZagierCurveCd_of_printed (h : GrossZagierCurveCdPrinted) : GrossZagierCurveCd :=
  grossZagierCurveCd_iff_printed.mpr h

/-- **What `frozenTarget` reads through `hGZ`, from the printed leaf.** -/
theorem grossZagierAlgOptCd_of_printed (h : GrossZagierCurveCdPrinted) : GZAlg.GrossZagierAlgOptCd :=
  grossZagierAlgOptCd_of_curve (grossZagierCurveCd_of_printed h)

end ZInQ.GZCdPrinted
