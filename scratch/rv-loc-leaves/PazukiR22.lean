import Mathlib

/-!
# pkg-I5: the Arakelov package (h-trust E2-E4, F3) — what can be stated in Lean today

Draft for `docs/research/pkg-I5.md`. Mathlib-only (no project imports).

Contents.

1. `thomaePoint`: the eighth powers of the ten even theta constants of a genus-2 curve, up to
   one common factor, as polynomials in the six branch points (Thomae's formula). With it a
   theta height of a genus-2 Jacobian is an elementary height (`thetaHeightThomae`).
2. `hypGram`, `hypVol`: the Faltings (archimedean) metric on `H⁰(J, Ω^g)` of a hyperelliptic
   Jacobian as a Lebesgue integral over `ℂ`.
3. `faltingsHeightEC`: the stable Faltings height of an elliptic curve over a number field, in
   Faltings' original normalization, as a closed formula over Mathlib objects. Not used by H (the
   CM branch is empty, h-cm); it fixes conventions and was checked numerically
   (`ec_height_check.py`: Deligne's minimum at `j = 0`, and the 5-isogeny 11a1 → 11a3).
4. `Genus2Eq.Good`, `faltingsHeightGood`: the Faltings height of the Jacobian of a genus-2 curve
   with a smooth Weierstrass model over `𝓞 K` (everywhere good reduction of the curve).
5. Leaves statable today: `BostEC`, `BostGoodGenus2`, `PazukiGoodGenus2` (the last one is a
   composite: Pazuki 2012 Cor. 1.3(2) read through Thomae's formula and the good-model
   identification of item 4).
6. Glue proved here: `f3_numerics` (N5 L934-947 bookkeeping), `thomaePoint_add_const`,
   `thomaePoint_smul`.

What is NOT statable today, and why, is in `docs/research/pkg-I5.md` §§2-4: every theorem of
the transfer (Javanpeykar, Gaudron–Rémond, Faltings Lemma 5 with additivity) needs the stable
Faltings height of abelian varieties of dimension up to `N²` (`J₁(N)` and the complement `Z`),
isogenies with their degrees, and (for Javanpeykar) the Jacobian of `X₁(N)` and Belyi degrees.
-/

namespace ZInQ.PkgI5

open Complex MeasureTheory Polynomial NumberField

/-! ## 1. The Thomae point of a genus-2 curve -/

/-- The ten even theta characteristics of a genus-2 curve with branch points `a₀,…,a₅` correspond
to the splittings of the six branch points into two triples. We index a splitting by the triple
containing `0`, i.e. by the pair `{p, q} ⊂ {1,…,5}`. -/
def evenPair : Fin 10 → Fin 6 × Fin 6 :=
  ![(1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

/-- The triple containing `0` of the `m`-th splitting. -/
def evenTriple (m : Fin 10) : Finset (Fin 6) := {0, (evenPair m).1, (evenPair m).2}

/-- `∏_{i<j ∈ S} (aᵢ − aⱼ)`. -/
def tripleProd {F : Type*} [CommRing F] (a : Fin 6 → F) (S : Finset (Fin 6)) : F :=
  ∏ p ∈ (S ×ˢ S).filter (fun p => p.1 < p.2), (a p.1 - a p.2)

/-- **The Thomae point.** `Θ_T(a) = (∏_{i<j∈T}(aᵢ−aⱼ) · ∏_{i<j∈Tᶜ}(aᵢ−aⱼ))²` for the ten
splittings `{T, Tᶜ}`. By Thomae's formula (STANDARD: Thomae 1870; Mumford, *Tata Lectures on
Theta II*, Ch. IIIa §8, locator UNVERIFIED), for `C : y² = c·∏(x − aᵢ)` the fourth powers of the
even theta constants of a period matrix of `C` are `±κ·∏_{i<j∈T}(aᵢ−aⱼ)∏_{i<j∈Tᶜ}(aᵢ−aⱼ)` with one
`κ ≠ 0`; so the eighth powers are `κ²·Θ_T(a)`. The signs disappear in the eighth powers.
Exact identities (`thomae_check.py`, VERIFIED): `∑_T Θ_T = I₄/a₀⁴` (Igusa–Clebsch, by the
definition of `I₄` as a sum over splittings) and `∏_T Θ_T = (disc f / a₀¹⁰)⁴`. -/
def thomaePoint {F : Type*} [CommRing F] (a : Fin 6 → F) : Fin 10 → F := fun m =>
  (tripleProd a (evenTriple m) * tripleProd a (evenTriple m)ᶜ) ^ 2

/-- Absolute logarithmic Weil height (sup norms) of a point of projective space over a number
field: Mathlib's `Height.logHeight` divided by `[K : ℚ]`. -/
noncomputable def absLogHeight {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]
    (z : ι → K) : ℝ :=
  Height.logHeight z / Module.finrank ℚ K

/-- **Theta height of a genus-2 Jacobian through Thomae's formula**: the absolute height of the
point of the ten even theta constants, computed as `h([Θ_T]) / 8`. Since
`Height.logHeight (z ^ 8) = 8 * Height.logHeight z` (`Height.logHeight_pow`), this is exactly the
sup-norm height of `[θ_m(0, τ)]_{m even}`; Pazuki's `h_Θ` uses Euclidean norms at the infinite
places, which dominate (N5 L936-938). -/
noncomputable def thetaHeightThomae {K : Type*} [Field K] [NumberField K] (a : Fin 6 → K) : ℝ :=
  absLogHeight (thomaePoint a) / 8

/-- Translating the branch points does not change the Thomae point (glue, proved). -/
theorem thomaePoint_add_const {F : Type*} [CommRing F] (a : Fin 6 → F) (c : F) :
    thomaePoint (fun i => a i + c) = thomaePoint a := by
  funext m
  simp only [thomaePoint, tripleProd, add_sub_add_right_eq_sub]

theorem tripleProd_mul {F : Type*} [CommRing F] (a : Fin 6 → F) (c : F) (S : Finset (Fin 6)) :
    tripleProd (fun i => c * a i) S =
      c ^ ((S ×ˢ S).filter (fun p => p.1 < p.2)).card * tripleProd a S := by
  simp only [tripleProd, ← mul_sub, Finset.prod_mul_distrib, Finset.prod_const]

theorem card_evenTriple (m : Fin 10) :
    ((evenTriple m ×ˢ evenTriple m).filter (fun p => p.1 < p.2)).card = 3 ∧
    (((evenTriple m)ᶜ ×ˢ (evenTriple m)ᶜ).filter (fun p => p.1 < p.2)).card = 3 := by
  fin_cases m <;> decide

/-- Scaling the branch points by `λ` scales the Thomae point by `λ¹²` (glue, proved). With
translation invariance and the inversion `x ↦ 1/x` this is the `PGL₂`-invariance of the
projective Thomae point, i.e. its independence of the model of the curve. -/
theorem thomaePoint_smul {F : Type*} [CommRing F] (a : Fin 6 → F) (c : F) :
    thomaePoint (fun i => c * a i) = c ^ 12 • thomaePoint a := by
  funext m
  obtain ⟨h1, h2⟩ := card_evenTriple m
  simp only [thomaePoint, tripleProd_mul, h1, h2, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## 2. The Faltings metric of a hyperelliptic Jacobian, as a Lebesgue integral -/

/-- For `C : y² + h(x) y = f(x)` over `ℂ` put `P = 4f + h²`, so that `(2y + h)² = P(x)`, and
`ωᵢ = xⁱ dx / (2y + h)` (`0 ≤ i < g`), a basis of `H⁰(C, Ω¹)`. Then
`(i/2) ∫_{C(ℂ)} ωᵢ ∧ ω̄ⱼ = 2 ∫_ℂ xⁱ x̄ʲ / |P(x)| dλ(x)` (two sheets over `ℂ`; `(i/2) dx∧dx̄ = dλ`).
The factor 2 was checked numerically for `g = 1` against PARI periods (`area_check.py`). -/
noncomputable def hypGram (P : ℂ[X]) (i j : ℕ) : ℂ :=
  2 * ∫ x : ℂ, x ^ i * (starRingEnd ℂ x) ^ j / ((‖P.eval x‖ : ℝ) : ℂ)

/-- `‖ω₁ ∧ ⋯ ∧ ω_g‖²` in Faltings' original metric `(i/2)^g ∫_{J(ℂ)} η ∧ η̄`, by the identity
`(i/2)^g ∫_J |ω₁∧⋯∧ω_g|² = det((i/2)∫_C ωᵢ∧ω̄ⱼ)` (Riemann bilinear relations: both sides equal
`|det Ω₁|² det Im τ`; STANDARD). -/
noncomputable def hypVol (g : ℕ) (P : ℂ[X]) : ℝ :=
  (Matrix.of fun i j : Fin g => hypGram P i j).det.re

/-! ## 3. Elliptic curves: the stable Faltings height as a closed formula -/

/-- The sum of the finite local terms of the height of `x`:
`∑_{v finite} log max(1, |x|_v) = h(x)·[K:ℚ] − ∑_{σ : K → ℂ} log max(1, |σ x|)`. -/
noncomputable def finiteHeightPart {K : Type*} [Field K] [NumberField K] (x : K) : ℝ :=
  Height.logHeight₁ x - ∑ σ : K →+* ℂ, Real.log (max 1 ‖σ x‖)

/-- **Stable Faltings height of an elliptic curve** (original Faltings normalization
`(i/2)∫ω∧ω̄`), for an elliptic `W` over a number field `K`, `ω = dx/(2y + a₁x + a₃)`:

`h_F(E) = (1/(12[K:ℚ])) (∑_{v fin} log⁺|j|_v − ∑_σ log|σΔ|) − (1/(2[K:ℚ])) ∑_σ log Area_σ`,

`Area_σ = 2 ∫_ℂ dλ/|σ(4x³ + b₂x² + 2b₄x + b₆)|`. Derivation: Faltings' definition with the Néron
differential at the semistable places, `ord_v Δ_min = max(0, −ord_v j)` there, and the product
formula. Equivalent to Silverman, *Heights and elliptic curves* (1986), Prop. 1.1, and to
Barquero-Sanchez–Cadwallader–Cannon–Genao–Masri 2017 eq. (6.2) (both locators: N5 and
height/AUDIT item 2). VERIFIED numerically (`ec_height_check.py`): the two formulas agree on
seven curves, `j = 0` gives `−1.321117 = −0.748752 − ½ log π` (Deligne's minimum, shifted to
Faltings' normalization), and 11a1, 11a3 differ by `0.80472 = ½ log 5` (Faltings Lemma 5 with
equality for the 5-isogeny). -/
noncomputable def faltingsHeightEC {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] : ℝ :=
  let d : ℝ := Module.finrank ℚ K
  let P : K[X] := 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆
  (finiteHeightPart W.j - ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) / (12 * d) -
    (∑ σ : K →+* ℂ, Real.log (hypVol 1 (P.map σ))) / (2 * d)

/-- **Leaf (Bost 1996, as recorded in Gaudron–Rémond 2014 §9: `h_F(A) ≥ −(3/2) dim A`), at
`g = 1`.** A consequence of the published bound (dimension 1). Not used by H. -/
def BostEC : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic],
    -(3 / 2 : ℝ) ≤ faltingsHeightEC W

/-! ## 4. Genus 2 with everywhere good reduction -/

/-- A genus-2 Weierstrass equation `y² + h(x) y = f(x)` over a ring `R`. -/
structure Genus2Eq (R : Type*) [CommRing R] where
  f : R[X]
  h : R[X]
  deg_f : f.natDegree ≤ 6
  deg_h : h.natDegree ≤ 3

namespace Genus2Eq

variable {R : Type*} [CommRing R]

/-- `P = 4f + h²`, so that `(2y + h)² = P`. -/
noncomputable def P (E : Genus2Eq R) : R[X] := 4 * E.f + E.h ^ 2

/-- The discriminant of `P` as a binary sextic (`P` of degree 5 has a branch point at `∞`). -/
noncomputable def binDisc (E : Genus2Eq R) : R :=
  if E.P.natDegree = 6 then E.P.discr
  else if E.P.natDegree = 5 then E.P.leadingCoeff ^ 2 * E.P.discr else 0

/-- **Smooth Weierstrass model over `𝓞 K`.** Liu's discriminant `2⁻¹² disc₆(4f + h²)` is a
unit (Lockhart 1994, Def. 1.6; Liu 1996: then the Weierstrass model is smooth over `𝓞 K`;
locators UNVERIFIED). Stated without division: `disc₆(P) = 2¹²·u` with `u` a unit. -/
def Good {K : Type*} [Field K] [NumberField K] (E : Genus2Eq (𝓞 K)) : Prop :=
  ∃ u : (𝓞 K)ˣ, E.binDisc = 2 ^ 12 * (u : 𝓞 K)

end Genus2Eq

/-- **Faltings height of `Jac C` for a good equation**: `h_F = −(1/(2[K:ℚ])) ∑_σ log ‖ω₀∧ω₁‖²_σ`.
For a smooth Weierstrass model `𝒞/𝓞 K` the Néron model of `Jac C` is the abelian scheme
`Pic⁰_{𝒞/𝓞K}` (BLR 9.5 Thm 4) and its invariant differentials are
`∧²H⁰(𝒞, ω) = 𝓞K · (dx/(2y+h)) ∧ (x dx/(2y+h))` (Lockhart 1994 / Liu 1996), so the
non-archimedean term vanishes. Locators UNVERIFIED; the identification is the bridge on which the
leaves below rest. Base-change invariant, hence equal to the stable height. -/
noncomputable def faltingsHeightGood {K : Type*} [Field K] [NumberField K]
    (E : Genus2Eq (𝓞 K)) : ℝ :=
  -(∑ σ : K →+* ℂ, Real.log (hypVol 2 ((E.P.map (algebraMap (𝓞 K) K)).map σ))) /
    (2 * Module.finrank ℚ K)

/-- **Leaf (Bost's lower bound at `g = 2`, good equations).** -/
def BostGoodGenus2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : Genus2Eq (𝓞 K)), E.Good →
    -3 ≤ faltingsHeightGood E

/-- Pazuki's constant at `g = 2`, `r = 2` (N5 L942-944): `C₂ = 1000·2⁴·(log 2⁴)⁵`. -/
noncomputable def pazukiC2 : ℝ := 1000 * 2 ^ 4 * (Real.log (2 ^ 4)) ^ 5

/-- **Leaf (composite): Pazuki 2012, Cor. 1.3(2), `g = r = 2`, Deligne metric, for genus-2
Jacobians with a good equation, the theta height computed by Thomae's formula.**
`h_Θ(Jac C) ≤ ½X_D + C₂ log(X_D + 2)`, `X_D = max(1, h_F + log π)` (N5's reading, h-trust F3,
ASTRA-READ). The roots `a` of `P` live in a number field `L ⊇ K`. Faithfulness rests on
(i) Pazuki's corollary, (ii) Thomae's formula (`thomaePoint`), (iii) sup norms ≤ Euclidean
norms, (iv) `faltingsHeightGood` = the stable Faltings height. Restricted to everywhere good
reduction of the curve, it does not cover all QM surfaces (pkg-I5.md §3.3). -/
def PazukiGoodGenus2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : Genus2Eq (𝓞 K)), E.Good →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] (a : Fin 6 → L),
      E.P.natDegree = 6 →
      (E.P.map (algebraMap (𝓞 K) K)).map (algebraMap K L) =
        Polynomial.C (algebraMap K L (algebraMap (𝓞 K) K E.P.leadingCoeff)) *
          ∏ i, (X - Polynomial.C (a i)) →
      thetaHeightThomae a ≤
        max 1 (faltingsHeightGood E + Real.log Real.pi) / 2 +
          pazukiC2 * Real.log (max 1 (faltingsHeightGood E + Real.log Real.pi) + 2)

/-! ## 5. Glue: N5's F3 bookkeeping (L934-947) -/

/-- From Pazuki's bound to `h([z_m]) ≤ 10000·2²⁴·max(1, h_F)`. Proved. -/
theorem f3_numerics {hF hθ : ℝ}
    (hP : hθ ≤ max 1 (hF + Real.log Real.pi) / 2 +
      pazukiC2 * Real.log (max 1 (hF + Real.log Real.pi) + 2)) :
    hθ ≤ 10000 * 2 ^ 24 * max 1 hF := by
  set X := max 1 hF with hX
  set XD := max 1 (hF + Real.log Real.pi) with hXD
  have hX1 : 1 ≤ X := le_max_left _ _
  have hXD1 : 1 ≤ XD := le_max_left _ _
  have hlogpi : Real.log Real.pi ≤ 2 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have hXD3 : XD ≤ 3 * X := by
    refine max_le (by linarith) ?_
    linarith [le_max_right 1 hF]
  have hlog2 : Real.log (XD + 2) ≤ 2 * XD := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < XD + 2)
    linarith
  have hC2 : pazukiC2 ≤ 1000 * 2 ^ 24 := by
    have hl : Real.log (2 ^ 4 : ℝ) ≤ 15 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2 ^ 4)
      linarith [show ((2 : ℝ) ^ 4) = 16 by norm_num]
    have hl0 : 0 ≤ Real.log (2 ^ 4 : ℝ) := Real.log_nonneg (by norm_num)
    have : (Real.log (2 ^ 4 : ℝ)) ^ 5 ≤ 15 ^ 5 := pow_le_pow_left₀ hl0 hl 5
    unfold pazukiC2
    nlinarith
  have hC0 : 0 ≤ pazukiC2 := by unfold pazukiC2; positivity
  have hlogXD : 0 ≤ Real.log (XD + 2) := Real.log_nonneg (by linarith)
  calc hθ ≤ XD / 2 + pazukiC2 * Real.log (XD + 2) := hP
    _ ≤ XD / 2 + 1000 * 2 ^ 24 * (2 * XD) := by
        gcongr
    _ ≤ 10000 * 2 ^ 24 * X := by nlinarith

end ZInQ.PkgI5

#print axioms ZInQ.PkgI5.f3_numerics
#print axioms ZInQ.PkgI5.thomaePoint_smul
#print axioms ZInQ.PkgI5.thomaePoint_add_const

/-! ## rv-loc-leaves: R22 (Pazuki) after the locator audit

The audit (docs/research/locators.md, R22 and notes §2) read Pazuki, Bull. SMF 140 (2012),
Cor. 1.3(2): with `H_Θ = max(1, h_Θ)`, `H_D = max(1, h_D)`,
`|H_Θ − H_D/2| ≤ C₂ log(min(H_Θ, H_D) + 2)`, `C₂ = 1000·r^{2g}(log r^{2g})⁵`, and Deligne's metric,
`h_D = h_F + (g/2) log π` (`= h_F + log π` for `g = 2`). The three "consequence steps" it lists
(drop the absolute value, bound the minimum by `H_D`, then `h_Θ ≤ H_Θ` and `H_D ≤ X_D`) are proved
below, so the leaf `PazukiGoodGenus2` (with `log π`) and its hardened form (with `+3`) are
consequences of the literal corollary at `g = r = 2`. -/

namespace ZInQ.PkgI5

open Polynomial NumberField

/-- **The literal Cor. 1.3(2) at `g = r = 2`**, for real numbers: `hθ` a theta height, `hD` the
Deligne-normalized Faltings height. -/
def PazukiLiteral (hθ hD : ℝ) : Prop :=
  |max 1 hθ - max 1 hD / 2| ≤ pazukiC2 * Real.log (min (max 1 hθ) (max 1 hD) + 2)

theorem pazukiC2_nonneg : 0 ≤ pazukiC2 := by unfold pazukiC2; positivity

theorem log_pi_le_three : Real.log Real.pi ≤ 3 := by
  have h4 : Real.log Real.pi ≤ Real.log 4 :=
    Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9]

/-- `X ↦ X/2 + C₂ log(X + 2)` is monotone on `X ≥ 1`. -/
theorem pazuki_rhs_mono {X Y : ℝ} (hX : 1 ≤ X) (hXY : X ≤ Y) :
    X / 2 + pazukiC2 * Real.log (X + 2) ≤ Y / 2 + pazukiC2 * Real.log (Y + 2) := by
  have := Real.log_le_log (by linarith) (by linarith : X + 2 ≤ Y + 2)
  have := mul_le_mul_of_nonneg_left this pazukiC2_nonneg
  linarith

/-- **The audit's consequence steps, proved.** From the literal corollary with `h_D = h_F + log π`
and any `X_D ≥ max(1, h_D)` (the bound must dominate the truncated Deligne height, not `h_F`):
`h_Θ ≤ X_D/2 + C₂ log(X_D + 2)`. -/
theorem pazuki_upper_of_literal {hθ hF XD : ℝ}
    (h : PazukiLiteral hθ (hF + Real.log Real.pi))
    (hXD : max 1 (hF + Real.log Real.pi) ≤ XD) :
    hθ ≤ XD / 2 + pazukiC2 * Real.log (XD + 2) := by
  set HT := max 1 hθ
  set HD := max 1 (hF + Real.log Real.pi)
  have hHD1 : 1 ≤ HD := le_max_left _ _
  have hHT1 : 1 ≤ HT := le_max_left _ _
  have h1 : HT - HD / 2 ≤ pazukiC2 * Real.log (min HT HD + 2) := (le_abs_self _).trans h
  have h2 : Real.log (min HT HD + 2) ≤ Real.log (HD + 2) :=
    Real.log_le_log (by linarith [le_min hHT1 hHD1]) (by linarith [min_le_right HT HD])
  have h3 := mul_le_mul_of_nonneg_left h2 pazukiC2_nonneg
  have h4 : hθ ≤ HT := le_max_right _ _
  have h5 := pazuki_rhs_mono hHD1 hXD
  linarith

/-- The `log π` form (pkg-I5's `PazukiGoodGenus2` shape) from the literal corollary. -/
theorem pazuki_logpi_of_literal {hθ hF : ℝ} (h : PazukiLiteral hθ (hF + Real.log Real.pi)) :
    hθ ≤ max 1 (hF + Real.log Real.pi) / 2 +
      pazukiC2 * Real.log (max 1 (hF + Real.log Real.pi) + 2) :=
  pazuki_upper_of_literal h le_rfl

/-- The hardened `+3` form from the literal corollary (`log π ≤ 3`). -/
theorem pazuki_plus3_of_literal {hθ hF : ℝ} (h : PazukiLiteral hθ (hF + Real.log Real.pi)) :
    hθ ≤ max 1 (hF + 3) / 2 + pazukiC2 * Real.log (max 1 (hF + 3) + 2) :=
  pazuki_upper_of_literal h (max_le_max le_rfl (by linarith [log_pi_le_three]))

/-- **R22, hardened (rv-leaves-a §3.3), recompiled here.** -/
def PazukiGoodGenus2' : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : Genus2Eq (𝓞 K)), E.Good →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] (a : Fin 6 → L),
      E.P.natDegree = 6 →
      (E.P.map (algebraMap (𝓞 K) K)).map (algebraMap K L) =
        Polynomial.C (algebraMap K L (algebraMap (𝓞 K) K E.P.leadingCoeff)) *
          ∏ i, (X - Polynomial.C (a i)) →
      thetaHeightThomae a ≤
        max 1 (faltingsHeightGood E + 3) / 2 +
          pazukiC2 * Real.log (max 1 (faltingsHeightGood E + 3) + 2)

/-- **R22 in the literal form of Cor. 1.3(2)** (absolute value, truncated heights, minimum inside
the logarithm, Deligne's `h_D = h_F + log π`), for the same objects as `PazukiGoodGenus2`. -/
def PazukiGoodGenus2Literal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : Genus2Eq (𝓞 K)), E.Good →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] (a : Fin 6 → L),
      E.P.natDegree = 6 →
      (E.P.map (algebraMap (𝓞 K) K)).map (algebraMap K L) =
        Polynomial.C (algebraMap K L (algebraMap (𝓞 K) K E.P.leadingCoeff)) *
          ∏ i, (X - Polynomial.C (a i)) →
      PazukiLiteral (thetaHeightThomae a) (faltingsHeightGood E + Real.log Real.pi)

theorem pazukiGoodGenus2_of_literal (h : PazukiGoodGenus2Literal) : PazukiGoodGenus2 :=
  fun K _ _ E hE L _ _ _ a hd hf => pazuki_logpi_of_literal (h K E hE L a hd hf)

theorem pazukiGoodGenus2'_of_literal (h : PazukiGoodGenus2Literal) : PazukiGoodGenus2' :=
  fun K _ _ E hE L _ _ _ a hd hf => pazuki_plus3_of_literal (h K E hE L a hd hf)

theorem pazukiGoodGenus2'_of_pazukiGoodGenus2 (h : PazukiGoodGenus2) : PazukiGoodGenus2' := by
  intro K _ _ E hE L _ _ _ a hd hf
  refine (h K E hE L a hd hf).trans (pazuki_rhs_mono (le_max_left _ _) ?_)
  exact max_le_max le_rfl (by linarith [log_pi_le_three])

end ZInQ.PkgI5

#print axioms ZInQ.PkgI5.pazuki_upper_of_literal
#print axioms ZInQ.PkgI5.pazukiGoodGenus2_of_literal
#print axioms ZInQ.PkgI5.pazukiGoodGenus2'_of_literal
#print axioms ZInQ.PkgI5.pazukiGoodGenus2'_of_pazukiGoodGenus2
