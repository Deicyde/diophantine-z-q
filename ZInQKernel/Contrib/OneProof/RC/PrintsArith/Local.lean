import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Basic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Division
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction

/-!
# Local arithmetic prints: Edixhoven, Lang, Silverman IV.2.3 and IV.3.2

Lane RC9. Three local facts cited in Section 8 of the manuscript (`diophantine_zq.tex`):

* **Edixhoven**, *Néron models and tame ramification*, Compositio Math. 81 (1992), 291–306,
  **Theorem 5.3 (p. 299) and Remark 5.4.1 (p. 300)** (read: Numdam scan). Use: tex 4117–4130 in
  `ex:arith-central-calibration`: at `p ∣ k`, the component group of the ramified twist of the
  good-reduction curve `E₀ = E^{(h)}` is `Ẽ₀[2]`, so its rational component number is
  `#E[2]^{Fr_p}` (`t_p = 2` for `E_ℓ`).
* **Lang**, *Algebraic groups over finite fields*, Amer. J. Math. 78 (1956), 555–563,
  **Theorem 1 and its corollary** (print NOT read: not freely available; statement from the standard
  secondary sources, UNVERIFIED as a locator). Use: tex 3043–3046, (H10): `H¹` of the connected
  smooth special fiber over a finite residue field vanishes.
* **Silverman**, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer GTM 106 (2009),
  **IV.2.3 and IV.3.2(a)**, pp. 122–124 (print NOT read here: statements from the standard
  edition, UNVERIFIED as locators). Uses: tex 3048–3051 (graded pieces of the formal group are
  additive copies of the residue field) and tex 3177–3182 (multiplication by `2^a` is invertible on
  the formal group over a local field of odd residue characteristic).

Contents:
* `EdixhovenTwistComponents` (PRINT with GLUE, consequence form over genuine definitions: the
  index `[W(ℚ_p) : W₀(ℚ_p)]` of the points with nonsingular reduction, vendored Tau Ceti
  `WeierstrassCurve.Affine.nonsingularReduction`);
* `LangThm1` (PRINT, consequence form over genuine definitions: Mathlib's points of a Weierstrass
  curve over a finite field and its Galois cohomology cocycles);
* `silverman_IV_2_3` and `kerReduction_uniquely_divisible` (PROVED: vendored Tau Ceti
  `WeierstrassCurve.FormalGroupPoint.nsmul_bijective`, `WeierstrassCurve.nsmul_kerReduction_bijective`);
* `SilvermanIV_3_2a` (the print over genuine definitions: Tau Ceti's formal group points) and
  `silverman_IV_3_2a` (PROVED: vendored Tau Ceti `WeierstrassCurve.formalAddEval_sub_add_mem`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsArith

open scoped WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53

/-! ### Edixhoven: the component group of a tamely ramified quadratic twist -/

/-- Equality on `ℚ_p` is decided classically (for the point arithmetic of `nonsingularReduction`). -/
instance (p : ℕ) [Fact p.Prime] : DecidableEq ℚ_[p] := Classical.decEq _

/-- **The rational component index `[W(ℚ_p) : W₀(ℚ_p)]`** of a Weierstrass curve `W/ℚ_p` with
`p`-integral coefficients: the index of the subgroup of points whose reduction (on the given integral
model) is a nonsingular point of the reduced curve (vendored Tau Ceti
`WeierstrassCurve.Affine.nonsingularReduction`, Silverman VII.2). For a minimal model this is the
Tamagawa number `c_p = #Φ(𝔽_p)` (Kodaira–Néron; Silverman, *Advanced Topics*, IV.9.2; GLUE). -/
def componentIndex (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ_[p])
    [WeierstrassCurve.IsIntegral (Padic.mulValuation (p := p)).valuationSubring W] : ℕ :=
  (WeierstrassCurve.Affine.nonsingularReduction (Padic.mulValuation (p := p)) W.toAffine).index

/-- **Edixhoven, Compositio Math. 81 (1992), Theorem 5.3 (p. 299) and Remark 5.4.1 (p. 300)**, in
the consequence form used at tex 4117–4127 (PRINT with GLUE). The print: *for a DVR `D` with
`μ_n ⊆ D`, `n` prime to the residue characteristic, a totally ramified Galois extension `K'/K` of
degree `n` and an abelian variety `A/K` with Néron models `𝒜/D`, `𝒜'/D'`, the special fiber `𝒜_k`
has a filtration with `Gr⁰𝒜_k = (𝒜'_k)^{μ_n}`* (Thm. 5.3), *and `Φ` is the group of connected
components of `(𝒜'_k)^{μ_n}`* (Rem. 5.4.1, as `F¹𝒜_k` is connected). For `A = E₀^{(k)}`, `E₀` with
good reduction at an odd `p`, `p ∣ k` squarefree, `K' = ℚ_p(√k)`, `n = 2`: `𝒜'_k = Ẽ₀` with `μ₂`
acting by `[-1]`, so `Φ ≅ Ẽ₀[2]` (tex 4121–4124).

Lean form (DEPARTURE: Néron models and component groups are absent from Mathlib): for `E₀/ℤ` with
`p ∤ Δ(E₀)`, `p` odd, `k` squarefree with `p ∣ k`, the twisted model `qtwist E₀ k` (the shared top
layer's `E₀^{(k)}`; `p`-integral, and minimal since `v_p(Δ) = 6 < 12`) has rational component index
`#Ẽ₀(𝔽_p)[2]`. This combines the print with (GLUE) `[E(ℚ_p) : E₀(ℚ_p)] = #Φ(𝔽_p)` for a minimal
model and `Φ ≅ Ẽ₀[2]` as finite étale `𝔽_p`-group schemes (tex 4125–4127). For `E₀ = E_{hℓ}` and
`p ∣ k`, `p ∤ 6hℓ`, the right side is `4` (full rational two-torsion), `t_p = 2`. The use matches
the print's hypotheses (`μ₂ ⊆ ℤ_p`, `2` prime to `p`, `ℚ_p(√k)/ℚ_p` totally ramified of degree 2). -/
def EdixhovenTwistComponents : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ E₀ : WeierstrassCurve ℤ, ¬ (p : ℤ) ∣ E₀.Δ →
    ∀ k : ℤ, Squarefree k → (p : ℤ) ∣ k →
    ∀ hW : WeierstrassCurve.IsIntegral (Padic.mulValuation (p := p)).valuationSubring
        ((qtwist (E₀.baseChange ℚ) k).baseChange ℚ_[p]),
      @componentIndex p _ ((qtwist (E₀.baseChange ℚ) k).baseChange ℚ_[p]) hW =
        Nat.card {P : (E₀.map (Int.castRingHom (ZMod p))).toAffine.Point // 2 • P = 0}

/-! ### Lang: `H¹` of a connected group over a finite field -/

/-- **Lang, Amer. J. Math. 78 (1956), Theorem 1 and its corollary** (PRINT, consequence form;
locator as the manuscript cites it, print not read: UNVERIFIED). The theorem: *for a connected
algebraic group `G` over a finite field `k`, the Lang map `x ↦ x⁻¹ F(x)` is surjective on
`G(k̄)`*; the corollary: *`H¹(k, G) = 0`*.

Lean form (DEPARTURE: algebraic groups are absent from Mathlib): the case of `G = W_ns`, the group
of nonsingular points of a Weierstrass cubic `W` over `k` (an elliptic curve, a split or nonsplit
torus, or `𝔾_a`: always connected; Mathlib's `Point` type is exactly `W_ns` with its group law), in
the cohomological form for a finite extension `k'/k`: every `1`-cocycle
`c : Gal(k'/k) → W_ns(k')` is a coboundary. This is Lang's corollary composed with the injectivity
of inflation `H¹(Gal(k'/k), G(k')) → H¹(k, G)` (GLUE).

Use: tex 3043–3046 ((H10)): "reduce a cocycle to the connected smooth special fiber. Lang's theorem
makes its `H¹` over the finite residue field zero; inflation–restriction then makes its `H¹` for
the finite residue extension zero". For a minimal Weierstrass model the identity component of the
Néron special fiber is `W̃_ns` (Silverman, *Advanced Topics*, IV.9; GLUE). The use matches. -/
def LangThm1 : Prop :=
  ∀ (k k' : Type) [Field k] [Fintype k] [Field k'] [Fintype k'] [DecidableEq k'] [Algebra k k']
    (W : WeierstrassCurve k) (c : (k' ≃ₐ[k] k') → (W⁄k').toAffine.Point),
    (∀ σ τ : k' ≃ₐ[k] k',
      c (σ * τ) = c σ + WeierstrassCurve.Affine.Point.map σ.toAlgHom (c τ)) →
    ∃ P : (W⁄k').toAffine.Point, ∀ σ : k' ≃ₐ[k] k',
      c σ = WeierstrassCurve.Affine.Point.map σ.toAlgHom P - P

/-! ### Silverman IV.2.3 and IV.3.2: the formal group -/

section FormalGroup

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]

/-- **Silverman IV.2.3(b), evaluated** (PROVED: vendored Tau Ceti
`WeierstrassCurve.FormalGroupPoint.nsmul_bijective`): if the integer `n` is a unit of the complete
coefficient ring `O`, multiplication by `n` is an automorphism of the formal group of a Weierstrass
curve evaluated on an adic ideal `I`. Use: tex 3177–3180 ("multiplication by `2^a` has an integral
formal inverse because `ℓ` is odd"). -/
theorem silverman_IV_2_3 (W : WeierstrassCurve O) (I : Ideal O) [Fact (IsAdic I)] {n : ℕ}
    (hn : IsUnit (n : O)) : Function.Bijective (fun P : W.FormalGroupPoint I ↦ n • P) :=
  WeierstrassCurve.FormalGroupPoint.nsmul_bijective hn

/-- **Silverman IV.3.2(a)** (PRINT over genuine definitions: Tau Ceti's formal group points). The
print: *for each `n ≥ 1` the identity map on sets `𝓜^n → 𝓜^n` induces an isomorphism of groups
`F(𝓜^n)/F(𝓜^{n+1}) ≅ 𝓜^n/𝓜^{n+1}`.* Lean form: its content, that on parameters in `I^n` the
formal addition agrees with ring addition modulo `I^{n+1}` (so the identity map is additive modulo
`I^{n+1}`, with kernel `F(I^{n+1})`), for a complete ring with adic ideal `I` (the maximal ideal of
a complete local ring in the print). Use: tex 3048–3051 ("each successive formal quotient is an
additive copy of the residue field of `F'`"). -/
def SilvermanIV_3_2a : Prop :=
  ∀ (O : Type) [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
    [IsTopologicalRing O] [IsLinearTopology O O] (W : WeierstrassCurve O) (I : Ideal O)
    [Fact (IsAdic I)] (n : ℕ), 1 ≤ n → ∀ P Q : W.FormalGroupPoint I,
      (P : O) ∈ I ^ n → (Q : O) ∈ I ^ n →
        ((P + Q : W.FormalGroupPoint I) : O) - ((P : O) + (Q : O)) ∈ I ^ (n + 1)

/-- **Silverman IV.3.2(a) holds** (PROVED: vendored Tau Ceti
`WeierstrassCurve.formalAddEval_sub_add_mem`, "the group law is `t₁ + t₂` to first order": on
parameters of `I^n` the formal addition deviates from ring addition by an element of
`I^{2n} ⊆ I^{n+1}`). So this print needs no leaf. -/
theorem silverman_IV_3_2a : SilvermanIV_3_2a := by
  intro O _ _ _ _ _ _ _ W I _ n hn P Q hP hQ
  rw [WeierstrassCurve.FormalGroupPoint.coe_add]
  exact Ideal.pow_le_pow_right (by omega)
    (W.formalAddEval_sub_add_mem (Fact.out : IsAdic I) hP hQ)

end FormalGroup

section KerReduction

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)
  (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- **The kernel of reduction over a local field is uniquely divisible by integers prime to the
residue characteristic** (PROVED: vendored Tau Ceti `WeierstrassCurve.nsmul_kerReduction_bijective`;
Silverman IV.2.3 with VII.2.2). This is the form used at tex 3176–3182: in the "upper local field"
(the completion of the number field `H_{f n_I ℓ}` at a place above the odd prime `ℓ`), the
discrepancy of a lifted residue `2^a`-division point lies in the kernel of reduction, where
`2^a ∉ u` (`u` above `ℓ` odd) acts bijectively. -/
theorem kerReduction_uniquely_divisible {n : ℕ} (hn : (n : A) ∉ u.asIdeal) :
    Function.Bijective (fun P : C.kerReduction u ↦ n • P) :=
  WeierstrassCurve.nsmul_kerReduction_bijective u C hn

end KerReduction

end ZInQ.Manuscript.RC.PrintsArith
