import ZInQKernel.Contrib.TYZGenus.ShimuraField

/-!
# tyz-cm: Shimura reciprocity for modular functions on `Γ₀(N)` (the leaf) and its `X₀(32)` instance

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

`ShimuraRecip.lean` states the main theorem of complex multiplication for Heegner points of
`X₀(32)` in Gross's form (`ShimuraReciprocityPic`) directly over x0-32's eta-quotient
parametrization `X0.phiC`. This file separates the general theorem from the `X₀(32)`-specific
input:

* `IsRatModFn N g`: `g : ℍ → ℂ` is a modular function for `Γ₀(N)`, holomorphic on `ℍ`,
  meromorphic at every cusp, with rational `q`-expansion at `∞`, i.e. an element of `ℚ(X₀(N))`
  with no poles on `ℍ`;
* the leaf `ShimuraReciprocityModFn` (Gross's form of the main theorem of CM for the values of
  such functions at Heegner points of level `N`); it does not mention the eta model;
* `shimuraReciprocityPic_of`: `ShimuraReciprocityPic` from the leaf and
  `IsRatModFn 32 x`, `IsRatModFn 32 y` for x0-32's coordinate functions;
* `isRatModFn_xC_of`, `isRatModFn_yC_of`: those two facts from x0-32's leaf
  `X0.EtaModelInvariant` (`Γ₀(32)`-invariance), the `q`-expansion facts `XQExpRational`,
  `YQExpRational` and the cusp-growth fact `EtaCuspGrowth` (proved or reduced in later files).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

/-- **`g : ℍ → ℂ` is an element of `ℚ(X₀(N))` without poles on `ℍ`**: `g` is invariant under
`Γ₀(N)`; at every cusp `γ∞` (`γ ∈ SL₂(ℤ)`) it has at most a pole (`g(γτ) = O(e^{2πk Im τ})` as
`Im τ → ∞`); and its `q`-expansion at `∞` is a Laurent series in `q = e^{2πiτ}` with rational
coefficients converging on all of `ℍ` (`q^k g(τ) = Σ_{n ≥ 0} a_n qⁿ`, `a_n ∈ ℚ`), which also makes
`g` holomorphic on `ℍ`. By the `q`-expansion principle these are exactly the functions of
`ℚ(X₀(N)) = ℚ(j, j_N)` that are regular on `ℍ` (Shimura 1971, Prop. 6.9 and Thm. 6.23 for the
rational structure; Diamond–Shurman, *A first course in modular forms*, §7.5–7.7; UNVERIFIED
numbers). -/
def IsRatModFn (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ τ : UpperHalfPlane, g (γ • τ) = g τ) ∧
  (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ k : ℕ,
      (fun τ : UpperHalfPlane => g (γ • τ)) =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (2 * Real.pi * k * τ.im)) ∧
  ∃ (k : ℕ) (a : ℕ → ℚ), ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => (a n : ℂ) * cexp (2 * Real.pi * I * τ) ^ n)
      (cexp (2 * Real.pi * I * τ) ^ k * g τ)

/-- **Leaf SHIMURA-MODFN (main theorem of complex multiplication for the values of modular
functions on `X₀(N)` at Heegner points; Gross's form).** Let `g ∈ ℚ(X₀(N))` be regular on `ℍ`
(`IsRatModFn N g`). Let `K = ℚ(√−m)` (`m` squarefree), `O = ℤ + f𝓞_K` the order of discriminant
`D`, `H_O` its ring class field, `e : Kˢ → ℚ̄` inducing on `K` the normalized embedding
`√−m ↦ i√m` (through cm-points' `ιC : ℚ̄ → ℂ`), `J` an ideal of `𝓞_K` prime to `f`, and
`ρ ∈ Gal(ℚ̄/ℚ)` acting on `e(H_O)` as the Artin symbol of the class of `J ∩ O`. For Heegner forms
`Q, Q'` of level `N` and discriminant `D` with
`κ(J ∩ O)·(⟨1,τ_{Q'}⟩, ⟨1/N,τ_{Q'}⟩) = c·(⟨1,τ_Q⟩, ⟨1/N,τ_Q⟩)` for one `c ∈ ℂ`, the values
`g(τ_Q)`, `g(τ_{Q'})` are algebraic and `ρ` maps the first to the second.

Content: `τ_Q` is the point `(ℂ/L, L_N/L)` of `X₀(N)`, `L = ⟨1, τ_Q⟩`, `L_N = ⟨1/N, τ_Q⟩`. By the
main theorem of CM (Shimura 1971, Thm. 5.4; Silverman, *Advanced topics*, GTM 151, Thm. II.8.2),
for `σ ∈ Aut(ℂ)` extending `ρ`, `(ℂ/L, L_N/L)^σ ≅ (ℂ/𝔟⁻¹L, 𝔟⁻¹L_N/𝔟⁻¹L)`, `𝔟 = J ∩ O` (the idele
`s` of `J` has `[s, K] = Art(J)` and `s⁻¹L = 𝔟⁻¹L`, `s⁻¹L_N = 𝔟⁻¹L_N`, since `J` is prime to the
conductor); the right side is `τ_{Q'}`. Since `X₀(N)_ℚ` (the model with function field the
functions with rational `q`-expansion) is the coarse moduli space of pairs `(E, C)` (Shimura 1971,
§6.7 and Thm. 6.23; Deligne–Rapoport; Diamond–Shurman, Ch. 7; UNVERIFIED numbers),
`σ(g(x)) = g(σ(x))` for `g ∈ ℚ(X₀(N))` regular at `x`. Gross, *Heegner points on `X₀(N)`*, in
*Modular forms* (Durham 1983), 1984, §3, states the combination as
`σ_𝔟(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔞𝔟⁻¹])`. Refereed (textbook / survey); theorem numbers UNVERIFIED
(from memory, no network on this host). Normalization: Tau Ceti's Artin map sends the class of a
prime to the arithmetic Frobenius, and `j(𝔞)^{Art 𝔭} = j(𝔭⁻¹𝔞)` (Cox, *Primes of the form
x² + ny²*, Cor. 11.37, UNVERIFIED). No Heegner condition `(f, N) = 1` or `gcd(A/N, B, NC) = 1` is
needed. -/
def ShimuraReciprocityModFn : Prop :=
  ∀ (N : ℕ) (g : UpperHalfPlane → ℂ), IsRatModFn N g →
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'

/-! ## From the leaf to `ShimuraReciprocityPic` -/

section Pic
open WeierstrassCurve.Affine

theorem nonsingular_iff_C {a b : Qbar} :
    X0.curveAC.toAffine.Nonsingular (ιC a) (ιC b) ↔ curveAbar.toAffine.Nonsingular a b :=
  baseChange_nonsingular (W := curveA) (f := ιCA) ιCA.injective a b

theorem nonsingular_iff_gal (ρ : GalQ) {a b : Qbar} :
    curveAbar.toAffine.Nonsingular (ρ a) (ρ b) ↔ curveAbar.toAffine.Nonsingular a b :=
  baseChange_nonsingular (W := curveA) (f := ρ.toAlgHom) ρ.injective a b

open Classical in
/-- **The Heegner point from algebraic preimages of its coordinates.** -/
theorem heegnerPt_of_alg {D : ℤ} (Q : HeegnerForm 32 D) {a b : Qbar}
    (ha : ιC a = X0.xC Q.tauH) (hb : ιC b = X0.yC Q.tauH) :
    heegnerPt Q = if h : curveAbar.toAffine.Nonsingular a b then .some a b h else 0 := by
  split_ifs with h
  · apply heegnerPt_eq
    have h' : X0.curveAC.toAffine.Nonsingular (X0.xC Q.tauH) (X0.yC Q.tauH) := by
      rw [← ha, ← hb]; exact nonsingular_iff_C.2 h
    simp only [toC, X0.phiC, h', ↓reduceDIte]
    simp only [Point.map_some, Point.some.injEq]
    exact ⟨ha, hb⟩
  · apply heegnerPt_eq
    have h' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC Q.tauH) (X0.yC Q.tauH) := by
      rw [← ha, ← hb]; exact fun h'' => h (nonsingular_iff_C.1 h'')
    simp only [X0.phiC, h', ↓reduceDIte, map_zero]

/-- **`ShimuraReciprocityPic` from the general leaf and the rationality of `x, y`.** -/
theorem shimuraReciprocityPic_of (hS : ShimuraReciprocityModFn)
    (hx : IsRatModFn 32 fun τ => X0.xC τ) (hy : IsRatModFn 32 fun τ => X0.yC τ) :
    ShimuraReciprocityPic := by
  intro m f _ _ hsq e he J ρ hρ D hD Q Q' c hL hLN
  obtain ⟨a, a', ha, ha', haa⟩ := hS 32 _ hx m f hsq e he J ρ hρ D hD Q Q' c hL hLN
  obtain ⟨b, b', hb, hb', hbb⟩ := hS 32 _ hy m f hsq e he J ρ hρ D hD Q Q' c hL hLN
  rw [heegnerPt_of_alg Q ha hb, heegnerPt_of_alg Q' ha' hb', ← haa, ← hbb]
  by_cases h : curveAbar.toAffine.Nonsingular a b
  · have h' : curveAbar.toAffine.Nonsingular (ρ a) (ρ b) := (nonsingular_iff_gal ρ).2 h
    simp only [h, h', ↓reduceDIte]
    rfl
  · have h' : ¬ curveAbar.toAffine.Nonsingular (ρ a) (ρ b) := fun h'' =>
      h ((nonsingular_iff_gal ρ).1 h'')
    simp only [h, h', ↓reduceDIte, map_zero]

end Pic

/-! ## The `X₀(32)`-specific input -/

/-- **`q`-expansion of `x` (rational).** `q²·x(τ) = Σ_{n ≥ 0} a_n qⁿ` on `ℍ` with `a_n ∈ ℚ`
(indeed `a_n ∈ ℤ`, `x = q⁻² + 2 + …`): `x = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) + 2` and
`η(dτ) = q^{d/24}∏(1 − q^{dn})`, `(2·2 + 16 − 4 − 2·32)/24 = −2`. Elementary (glue). -/
def XQExpRational : Prop :=
  ∃ a : ℕ → ℚ, ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => (a n : ℂ) * cexp (2 * Real.pi * I * τ) ^ n)
      (cexp (2 * Real.pi * I * τ) ^ 2 * X0.xC τ)

/-- **`q`-expansion of `y` (rational).** `q³·y(τ) = Σ_{n ≥ 0} b_n qⁿ` on `ℍ` with `b_n ∈ ℚ`
(`y = −q⁻³ + …`): `y = −η(8τ)⁴η(16τ)²/(η(4τ)²η(32τ)⁴)`, `(32 + 32 − 8 − 128)/24 = −3`.
Elementary (glue). -/
def YQExpRational : Prop :=
  ∃ b : ℕ → ℚ, ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => (b n : ℂ) * cexp (2 * Real.pi * I * τ) ^ n)
      (cexp (2 * Real.pi * I * τ) ^ 3 * X0.yC τ)

/-- **Leaf X0-CUSPGROWTH (`x, y` are meromorphic at every cusp of `Γ₀(32)`).** For every
`γ ∈ SL₂(ℤ)`, `x(γτ)` and `y(γτ)` are `O(e^{2πk Im τ})` as `Im τ → ∞`, for some `k`.
Source: eta quotients are meromorphic at all cusps, with Ligozat's order formula
`ord_{c/d} = (N/24)·Σ_δ gcd(d,δ)² r_δ / (gcd(d, N/d)·d·δ)` (Ligozat 1975, op. cit.; Ono, *The web
of modularity*, CBMS 102, Thm. 1.65; UNVERIFIED numbers); x0-32 VERIFIED the orders
(poles only at `∞`). Follows from `|η(γw)| = |cw + d|^{1/2}|η(w)|` (`γ ∈ SL₂(ℤ)`) and the product
expansion. Textbook (refereed). -/
def EtaCuspGrowth : Prop :=
  ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ k : ℕ,
    (fun τ : UpperHalfPlane => X0.xC (γ • τ : UpperHalfPlane)) =O[UpperHalfPlane.atImInfty] (fun τ => Real.exp (2 * Real.pi * k * τ.im)) ∧
    (fun τ : UpperHalfPlane => X0.yC (γ • τ : UpperHalfPlane)) =O[UpperHalfPlane.atImInfty] (fun τ => Real.exp (2 * Real.pi * k * τ.im))

theorem isRatModFn_xC_of (hI : X0.EtaModelInvariant) (hG : EtaCuspGrowth) (hq : XQExpRational) :
    IsRatModFn 32 fun τ => X0.xC τ := by
  refine ⟨fun γ hγ τ => (hI γ hγ τ).1, fun γ => ?_, ⟨2, hq⟩⟩
  obtain ⟨k, hk, -⟩ := hG γ
  exact ⟨k, hk⟩

theorem isRatModFn_yC_of (hI : X0.EtaModelInvariant) (hG : EtaCuspGrowth) (hq : YQExpRational) :
    IsRatModFn 32 fun τ => X0.yC τ := by
  refine ⟨fun γ hγ τ => (hI γ hγ τ).2, fun γ => ?_, ⟨3, hq⟩⟩
  obtain ⟨k, -, hk⟩ := hG γ
  exact ⟨k, hk⟩

/-- **The CM leaf from the general Shimura reciprocity law for `ℚ(X₀(N))`**, x0-32's
`Γ₀(32)`-invariance leaf, cusp growth and the rational `q`-expansions of `x, y`. -/
theorem cmFieldOfDefinition_of_modFn (hS : ShimuraReciprocityModFn) (hI : X0.EtaModelInvariant)
    (hG : EtaCuspGrowth) (hx : XQExpRational) (hy : YQExpRational) :
    CMFieldOfDefinition ringClassFieldD :=
  cmFieldOfDefinition_of
    (shimuraReciprocityPic_of hS (isRatModFn_xC_of hI hG hx) (isRatModFn_yC_of hI hG hy))

end ZInQ.Contrib.TYZGenus.Shimura
