import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Basic
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.CornutJetchev

/-!
# Heegner points, cusps and CM reduction: Cai–Chen–Liu, Elkik (Manin–Drinfeld), Cornut–Jetchev

Lane RC9. The finite Heegner descent (`ex:arith-finite-heegner`, tex 2834–3410) and the odd theta
comparison (App. F, `ex:app-theta-comparison`, tex 9103–9405) cite three prints about modular
curves and CM points:

* **Cai–Chen–Liu**, *Heegner points on modular curves*, Trans. AMS 370 (2018), 3721–3743,
  **Theorem 2.15**, p. 3730 (read: AI reading of the journal page). Use: tex 2914–2936, the
  norm relations (4.1) for `y_d = π(x_d)`.
* **Elkik**, *Le théorème de Manin–Drinfeld*, Astérisque 183 (1990), 59–67, **Théorème, p. 59**
  (read: Numdam scan). Use: tex 2937–2946, finiteness of the cuspidal subgroup `𝒞_N` of `J₀(N)`.
* **Cornut–Jetchev**, *Liftings of reduction maps for quaternion algebras*, preprint,
  arXiv:1012.0725v1 (3 December 2010; the same text as the author's web page PDF), **Theorem 3.1**
  (§3.5, p. 9), with §§3.1–3.4 (pp. 4–8), Lemma 2.1 (p. 4), Corollary 3.2 (p. 9) and §§4.9–4.10
  (p. 15) (read: §§2–3.5, 4.9–4.10). Use: tex 2522–2533 ((3.8)) and App. F tex 9195–9295. The one
  PRINT statement of Theorem 3.1 (general `κ`) is `CJSetting.Thm31` (`PrintsArith/CornutJetchev.lean`,
  Lane RC27); the `κ = 1` bijection used here, `CJReductionData.Thm3_1KappaOne`, is DERIVED from it
  (`CJReductionData.thm3_1KappaOne_of_print`).

**What is genuine.** `ManinDrinfeld` is stated over genuine definitions in its analytic form
(cusp forms, the action of `SL₂(ℤ)` on `ℍ`, path integrals): DEPARTURE of form, since `J₀(N)` and
divisor classes on `X_Γ` are absent from Mathlib; equivalent to the print by the Abel–Jacobi theorem
(GLUE). The Cornut–Jetchev hypothesis checks of App. F (`cj_kappa_eq_one`, `cj_H2`,
`cj_inert`) are PROVED, and they discharge H.2, H.3 and `κ = 1` in the derivation of the `κ = 1`
bijection from the print (`CJReductionData.PrintRealization`, `thm3_1KappaOne_of_print`).

**What is an interface.** Modular curves `X₀(N)` as curves over `ℚ`, CM points, ring class fields,
Hecke correspondences, the modular parametrization `π : X₀(N) → E` and supersingular reduction do
not exist in Mathlib. `HeegnerPointData` and `CJReductionData` carry exactly the objects and
properties the proof uses; `CJReductionData.PrintRealization` records how the latter sits inside the
print's objects at the manuscript's specialization (non-vacuity: `cjToyRealization`). **Vacuity:** the norm relations alone are satisfied by the zero system
(`HeegnerPointData.zero_normRelations`); in the proof the anchor is Cai–Shu–Tian's height formula
(stated by the shared top layer, `CST.CSTThm11Split`), so `CCLThm2_15AppliedWithUnits` is parametric
in an anchor predicate. **Sizing a genuine definition:** `X₀(N)` over `ℚ` (or its analytic uniformization
plus `ℂ/Λ_E ≅ E(ℂ)`), ring class fields (class field theory for imaginary quadratic orders), CM
theory (Shimura reciprocity, to place `x_d` in `X₀(N)(H_d)`), Hecke correspondences, `J₀(N)` and
the parametrization `φ`; for Cornut–Jetchev also adelic quaternion algebras, Eichler orders and the
Deuring correspondence. Each is a multi-thousand-line project.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsArith

open scoped WeierstrassCurve
open UpperHalfPlane Complex

/-! ### Elkik: the theorem of Manin–Drinfeld (analytic form) -/

/-- The point `r + i t` of `ℍ` for `t > 0`. -/
def vertPoint (r t : ℝ) (ht : 0 < t) : ℍ :=
  ⟨(r : ℂ) + (t : ℂ) * Complex.I, by simpa using ht⟩

/-- **`∫_r^{i∞} f(z) dz`** along the vertical ray `z = r + i t`, `t ∈ (0, ∞)`, from the cusp `r ∈ ℚ`
(`none` is the cusp `∞`, where the integral is `0`). For a cusp form the integrand is integrable
(exponential decay at both ends). -/
def cuspRayIntegral (f : ℍ → ℂ) : Option ℚ → ℂ
  | none => 0
  | some r => ∫ t in Set.Ioi (0 : ℝ), (if ht : 0 < t then f (vertPoint r t ht) else 0) * Complex.I

/-- The segment from `z` to `w` stays in `ℍ`. -/
theorem segPoint_im_pos (z w : ℍ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < (((1 - t : ℝ) : ℂ) * (z : ℂ) + ((t : ℝ) : ℂ) * (w : ℂ)).im := by
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  have hz := z.im_pos
  have hw := w.im_pos
  rcases lt_or_eq_of_le ht.2 with h | h
  · have h1 : 0 < (1 - t) * (z : ℂ).im := mul_pos (by linarith) hz
    have h2 : 0 ≤ t * (w : ℂ).im := mul_nonneg ht.1 hw.le
    linarith
  · subst h; simpa using hw

/-- The point `(1 - t) z + t w` of `ℍ` for `t ∈ [0, 1]` (and `z` otherwise). -/
def segPoint (z w : ℍ) (t : ℝ) : ℍ :=
  if ht : t ∈ Set.Icc (0 : ℝ) 1 then
    ⟨((1 - t : ℝ) : ℂ) * (z : ℂ) + ((t : ℝ) : ℂ) * (w : ℂ), segPoint_im_pos z w ht⟩
  else z

/-- **`∫_z^w f(z) dz`** along the segment from `z` to `w` in `ℍ`. For `w = γ z` with `γ ∈ Γ` and
`f` a weight-two cusp form for `Γ`, these are the periods of `f`; they form the period lattice
`H₁(X_Γ, ℤ) ⊆ S₂(Γ)^∨`. -/
def segmentIntegral (f : ℍ → ℂ) (z w : ℍ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (segPoint z w t) * ((w : ℂ) - (z : ℂ))

/-- **Elkik, *Le théorème de Manin–Drinfeld*, Astérisque 183 (1990), Théorème, p. 59** (PRINT):
*si `Γ` est un sous-groupe de congruence, la classe de tout diviseur de degré `0` de `X_Γ` à support
dans les pointes est un élément de torsion de `Pic⁰(X_Γ)`.*

Lean form (DEPARTURE of form, analytic): divisor classes on `X_Γ` and `Pic⁰(X_Γ) = J_Γ` are absent
from Mathlib. By the Abel–Jacobi theorem (GLUE), `Pic⁰(X_Γ) ≅ S₂(Γ)^∨ / H₁(X_Γ, ℤ)` sends
`[r] - [s]` to `f ↦ ∫_s^r f(z) dz` (up to the factor `2πi`), and `H₁(X_Γ, ℤ)` is the image of
`γ ↦ (f ↦ ∫_{z₀}^{γz₀} f(z) dz)`, `γ ∈ Γ`. So torsion of `[r] - [s]` is: some `m ≥ 1` and some
`γ ∈ Γ` with `m ∫_s^r f(z) dz = ∫_i^{γ i} f(z) dz` for every `f ∈ S₂(Γ)`. Cusps are
`ℙ¹(ℚ) = ℚ ∪ {∞}` (`Option ℚ`); degree-zero cuspidal divisors are generated by the `[r] - [s]`.

Use: tex 2937–2942: the subgroup `𝒞_N ⊆ J₀(N)(ℚ̄)` generated by `[c] - [∞]` is finite (a finitely
generated torsion group; `X₀(N)` has finitely many cusps), so one `C_π` kills `φ(𝒞_N)`. `Γ₀(N)` is a
congruence subgroup: the use matches. -/
def ManinDrinfeld : Prop :=
  ∀ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ), CongruenceSubgroup.IsCongruenceSubgroup Γ →
    ∀ r s : Option ℚ, ∃ m : ℕ, 0 < m ∧ ∃ γ ∈ Γ,
      ∀ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2,
        (m : ℂ) * (cuspRayIntegral f s - cuspRayIntegral f r) =
          segmentIntegral f UpperHalfPlane.I (γ • UpperHalfPlane.I)

/-! ### Heegner points and the norm relations of Cai–Chen–Liu -/

/-- **Heegner point data for `E` (interface).** For an imaginary quadratic field `K = ℚ(√D_K)`
split at every prime of `2N` (the manuscript's setting, tex 2839–2844):
* `H d ⊆ ℚ̄`: the ring class field of conductor `d` (`Gal(H_d/K) ≅ Pic(𝒪_d)`);
* `y d = π(x_d) ∈ E(ℚ̄)`: the image under the modular parametrization of the CM point
  `x_d ∈ X₀(N)(H_d)` chosen by compatible proper ideal lattices and fixed orientations at `N`
  (tex 2915–2917);
* `relGal d ℓ`: elements of `G_ℚ` restricting to the elements of `Gal(H_{dℓ}/H_d)`;
* `frob d q`: an element of `G_ℚ` restricting to the Frobenius `σ_q` at one of the two primes above
  a split `q` in `Gal(H_d/K)` (the other is `σ_q⁻¹`, tex 2931–2932).
ABSTRACT: none of these objects is defined from `E` here. -/
structure HeegnerPointData (E : WeierstrassCurve ℚ) where
  /-- The discriminant of `K`. -/
  DK : ℤ
  /-- The conductor of `E`. -/
  N : ℕ
  /-- The ring class field `H_d`. -/
  H : ℕ → IntermediateField ℚ Qbar
  /-- `y_d = π(x_d)`. -/
  y : ℕ → (E⁄Qbar).toAffine.Point
  /-- Lifts of the elements of `Gal(H_{dℓ}/H_d)`. -/
  relGal : ℕ → ℕ → Finset GalQ
  /-- A lift of the Frobenius `σ_q ∈ Gal(H_d/K)`. -/
  frob : ℕ → ℕ → GalQ

/-- The admissible pairs of Cai–Chen–Liu §2.3 as the manuscript takes them (tex 2920–2921): the
old conductor `d` prime to `2N D_K`, the new prime `ℓ ∉ prime(6 d N D_K)`. -/
def HeegnerPointData.Admissible {E : WeierstrassCurve ℚ} (D : HeegnerPointData E) (d ℓ : ℕ) :
    Prop :=
  0 < d ∧ Nat.Coprime d (2 * D.N * D.DK.natAbs) ∧ ℓ.Prime ∧ ¬ ℓ ∣ 6 * d * D.N * D.DK.natAbs

/-- **The unweighted norm relations (4.1)** (tex 2924–2929), after the check that the unit factor
is one: `Tr_{H_{dℓ}/H_d} y_{dℓ} = a_ℓ y_d` at an inert `ℓ` (`(D_K/ℓ) = -1`), and
`Tr_{H_{dq}/H_d} y_{dq} = (a_q - σ_q - σ_q⁻¹) y_d` at a split `q` (`(D_K/q) = 1`). -/
def HeegnerPointData.NormRelations {E : WeierstrassCurve ℚ} (D : HeegnerPointData E) : Prop :=
  (∀ d ℓ : ℕ, D.Admissible d ℓ → jacobiSym D.DK ℓ = -1 →
    ∑ τ ∈ D.relGal d ℓ, WeierstrassCurve.Affine.Point.map τ.toAlgHom (D.y (d * ℓ)) =
      (E.LFunction ℓ : ℤ) • D.y d) ∧
  (∀ d q : ℕ, D.Admissible d q → jacobiSym D.DK q = 1 →
    ∑ τ ∈ D.relGal d q, WeierstrassCurve.Affine.Point.map τ.toAlgHom (D.y (d * q)) =
      (E.LFunction q : ℤ) • D.y d -
        WeierstrassCurve.Affine.Point.map (D.frob d q).toAlgHom (D.y d) -
        WeierstrassCurve.Affine.Point.map (D.frob d q)⁻¹.toAlgHom (D.y d))

/-- **Vacuity of the bare norm relations**: the zero system satisfies them. -/
theorem HeegnerPointData.zero_normRelations {E : WeierstrassCurve ℚ} (DK : ℤ) (N : ℕ)
    (H : ℕ → IntermediateField ℚ Qbar) (relGal : ℕ → ℕ → Finset GalQ) (frob : ℕ → ℕ → GalQ) :
    (HeegnerPointData.mk (E := E) DK N H (fun _ => 0) relGal frob).NormRelations := by
  refine ⟨fun d ℓ _ _ => ?_, fun d q _ _ => ?_⟩ <;> simp [zsmul_zero]

open scoped NumberField in
/-- The printed factor `uₘ`. At `m = 1` this is the index of the image of the integral
units in the units of the maximal order. -/
def cclUnitFactor (K : Type*) [Field K] [NumberField K] (m : ℕ) : ℕ :=
  if m = 1 then (Units.map (algebraMap ℤ (𝓞 K)).toMonoidHom).range.index else 1

/-- The inert and split norm relations through the elliptic quotient, with the printed
factor. The full old conductor `d` is the print's `c`, so both relations use `u₁`. -/
def HeegnerPointData.NormRelationsWithUnits {E : WeierstrassCurve ℚ} (D : HeegnerPointData E)
    (K : Type*) [Field K] [NumberField K] : Prop :=
  (∀ d ℓ : ℕ, D.Admissible d ℓ → jacobiSym D.DK ℓ = -1 →
    cclUnitFactor K 1 •
      (∑ τ ∈ D.relGal d ℓ, WeierstrassCurve.Affine.Point.map τ.toAlgHom (D.y (d * ℓ))) =
      (E.LFunction ℓ : ℤ) • D.y d) ∧
  (∀ d q : ℕ, D.Admissible d q → jacobiSym D.DK q = 1 →
    cclUnitFactor K 1 •
      (∑ τ ∈ D.relGal d q, WeierstrassCurve.Affine.Point.map τ.toAlgHom (D.y (d * q))) =
      (E.LFunction q : ℤ) • D.y d -
        WeierstrassCurve.Affine.Point.map (D.frob d q).toAlgHom (D.y d) -
        WeierstrassCurve.Affine.Point.map (D.frob d q)⁻¹.toAlgHom (D.y d))

/-- Cai–Chen–Liu, Trans. Amer. Math. Soc. 370 (2018), Thm 2.15, p. 3730
(read: AI reading of the journal page), through the elliptic quotient (tex 2914–2936).
The theorem weights the relative point trace by `uₘ`, with `uₘ = 1` for `m ≠ 1` and
`u₁ = [𝒪_K^× : ℤ^×]`. At split level `X_K(N) = X₀(N)` and the condition (∗) is `(d, N) = 1`.

The application uses six GLUE identifications.
* With `c = d` and `m = 1`, the print's `H_m` has conductor `cm`, and the new prime is
  outside `6dND_K`.
* The decomposition law identifies the Jacobi symbol with inertness or splitting.
* At a split prime, the Artin symbol of the rational principal ideal is trivial, so
  Frobenius at the conjugate prime is `σ_q⁻¹` (tex 2931–2932).
* The CM points come from one global compatible family of proper ideal lattices with the
  fixed orientations at level `N` (tex 2915–2917).
* The CM ring class fields agree with the vendored class-field-theory ring class fields.
* The analytic map `phiAn` represents the algebraic parametrization over `ℚ` sending
  `∞` to zero. Hecke equivariance and the degree of `T_q[∞]` give the relation without a
  cusp term (tex 2836–2838, 2933–2936).

The anchor supplies the realization of the points and the field and Galois dictionary.
This replaces the unweighted applied witness on the staged chain. -/
def CCLThm2_15AppliedWithUnits (E : WeierstrassCurve ℚ) (K : Type*) [Field K] [NumberField K]
    (Anchor : HeegnerPointData E → Prop) : Prop :=
  ∃ D : HeegnerPointData E, D.NormRelationsWithUnits K ∧ Anchor D

/-! ### Cornut–Jetchev: the reduction bijection and the hypothesis checks of App. F -/

-- `cjNUnram` (Lemma 2.1, unramified case) and `cjNUnram_zero` now live in
-- `PrintsArith/CornutJetchev.lean` (same namespace), next to the print they feed.

/-- **`κ = 1` in Theorem 3.1 for the manuscript's specialization** (PROVED; tex 9225–9243): with
`F_CJ = ℚ`, `K_CJ = ℚ(√(D h_*))`, `B_CJ = M₂(ℚ)`, `S = {ℓ₀}`, both fine conductors `(1)`, so
`|Gal(K[c]/K[c_S])| = 1`, and `κ = 1 · N_{ℓ₀}(v(c'), v(c''), v(n)) = N_{ℓ₀}(0, 0, 0) = 1`
(`ℓ₀ ∤ N`, `ℓ₀` inert in `K_CJ`). -/
theorem cj_kappa_eq_one (ℓ₀ : ℕ) : 1 * cjNUnram ℓ₀ 0 0 0 = 1 := by
  rw [cjNUnram_zero, one_mul]

/-- **Hypothesis H.2 of Cornut–Jetchev §3.1** for the specialization (PROVED; tex 9204–9205):
`|S| + |Ram_f(B)| + [F : ℚ] = 1 + 0 + 1` is even. (H.1 holds since `M₂(ℚ)` is unramified
everywhere.) -/
theorem cj_H2 : Even (1 + 0 + 1) := ⟨1, rfl⟩

/-- **Hypothesis H.3 of Cornut–Jetchev §3.1** for the specialization, in its inert case (PROVED;
tex 9206–9210): `(D h_*/ℓ₀) = (D/ℓ₀)(h_*/ℓ₀) = 1 · (-1) = -1`, so `ℓ₀` is inert in
`ℚ(√(D h_*))` (for `ℓ₀` odd and prime to `D h_*`). -/
theorem cj_inert {D h : ℤ} {ℓ₀ : ℕ} (hD : jacobiSym D ℓ₀ = 1) (hh : jacobiSym h ℓ₀ = -1) :
    jacobiSym (D * h) ℓ₀ = -1 := by
  rw [jacobiSym.mul_left, hD, hh, one_mul]

/-- **The data of Cornut–Jetchev's Theorem 3.1 in the manuscript's application (interface).**
`Pic = Pic(𝒪_F)`, `F = ℚ(√(D h_*))`; `CMPts`: the conductor-one CM points of `X₀(N)` with the fixed
orientation tuple at the primes of `N` (a `Pic`-torsor, tex 9156–9169); `Emb`: the target
`c_{S,f}^{-1}(1,1) ∩ ψ_{S'}^{-1}(e)`, i.e. the `R_z^×`-classes of optimal embeddings `𝒪_F → R_z`,
`z` over the supersingular set, with the fixed orientation tuple and the fixed sign at `ℓ₀`
(§§3.3–3.4, 3.6); `red = θ_S`, which §§4.9–4.10 identify with geometric reduction at the chosen
place above `ℓ₀` (tex 9265–9272). ABSTRACT. -/
structure CJReductionData where
  /-- `Pic(𝒪_F)`. -/
  Pic : Type
  [commGroup : CommGroup Pic]
  [fintype : Fintype Pic]
  /-- The conductor-one CM points with the fixed orientation tuple. -/
  CMPts : Type
  [actCM : MulAction Pic CMPts]
  /-- The sign fiber of oriented optimal embeddings (target torsor). -/
  Emb : Type
  [actEmb : MulAction Pic Emb]
  /-- `θ_S`, the reduction map. -/
  red : CMPts → Emb

attribute [instance] CJReductionData.commGroup CJReductionData.fintype CJReductionData.actCM
  CJReductionData.actEmb

/-- **The conclusion of Cornut–Jetchev's Theorem 3.1 (§3.5, p. 9) with `κ = 1`, as the manuscript
uses it** (tex 9245–9263): *by restriction, `θ_S` induces a surjective `κ`-to-`1` correspondence
`c_f^{-1}(c', c'') → c_{S,f}^{-1}(c'_S, c''_S) ∩ ψ_{S'}^{-1}(e_{S'}(c', c''))`*; with `κ = 1`
(`cj_kappa_eq_one`) and the orientation tuple fixed, an equivariant bijection of `Pic`-torsors
(tex 9256–9261: "Theorem 3.1 gives a bijection onto one such sign, not onto both … The resulting map
is an equivariant bijection of the source class-group torsor onto the target torsor").
**Kind: DERIVED (no longer a PRINT leaf).** It is PROVED from the one PRINT statement
`CJSetting.Thm31` by `CJReductionData.thm3_1KappaOne_of_print`, for `D` realized inside the print's
objects (`CJReductionData.PrintRealization`). The definition is kept so that statements over it
(`sum_red_eq`) still typecheck. Note: Corollary 4.1 (p. 15) counts conjugate *pairs* of optimal
embeddings; the manuscript uses the sign fiber of Theorem 3.1 instead (tex 9368–9370), which is the
print's own formulation. -/
def CJReductionData.Thm3_1KappaOne (D : CJReductionData) : Prop :=
  Function.Bijective D.red ∧ ∀ (a : D.Pic) (x : D.CMPts), D.red (a • x) = a • D.red x

/-- **The exact finite-sum identity of App. F (tex 9279–9286), combinatorial core** (PROVED from
the conclusion of Theorem 3.1): for any weight `P` on the target and any `χ` on `Pic`, summing over
the class-group torsor commutes with reduction. -/
theorem CJReductionData.sum_red_eq (D : CJReductionData) (hD : D.Thm3_1KappaOne) {A : Type*}
    [AddCommGroup A] (P : D.Emb → A) (χ : D.Pic → ℤ) (x₀ : D.CMPts) :
    ∑ a : D.Pic, χ a • P (D.red (a • x₀)) = ∑ a : D.Pic, χ a • P (a • D.red x₀) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hD.2 a x₀]

/-! ### The `κ = 1` bijection derived from the print (Lane RC27) -/

/-- **How `D` sits inside the objects of Cornut–Jetchev at the manuscript's specialization
(interface; tex 9150–9169, 9195–9263).** The print's objects `P` (§§3.1–3.4) with:
* the specialization of tex 9195–9243: `F_CJ = ℚ`, `K_CJ = F = ℚ(√(D h_*))`, `B_CJ = M₂(ℚ)` (no finite
  ramification, `[ℚ : ℚ] = 1`), `S = {ℓ₀}`, `ℓ₀ ∤ N` (`v_{ℓ₀}(𝔫) = 0`), `(D/ℓ₀) = 1`,
  `(h_*/ℓ₀) = −1`; both fine conductors `(1)` at `c₀` (`v_{ℓ₀}(c') = v_{ℓ₀}(c'') = 0`,
  `|Gal(F[c]/F[c_S])| = 1`, tex 9225–9243);
* `inert_of_jacobi` (GLUE, the decomposition law in `ℚ(√(D h_*))` for the odd prime `ℓ₀ ∤ D h_*`):
  `(D h_*/ℓ₀) = −1` makes `ℓ₀` inert (tex 9206–9210);
* the orientation tuples at the primes of `N` (`orX`, `orY`; tex 9136–9149): `θ_S` preserves them,
  since its map on local orbit data away from `S` is the bijection of the print's (8) (§3.2, p. 6;
  tex 9258–9260: "Away from `ℓ₀` its map on local orbit data is a bijection, so we may also restrict
  to the chosen orientations");
* `ιX`, `ιY`: `D.CMPts` is the part of `c_f⁻¹(c₀)` with the fixed tuple `o₀` and `D.Emb` the part of
  the target `c_{S,f}⁻¹(c₀,S) ∩ ψ_{S'}⁻¹(e_{S'}(c₀))` with that tuple (tex 9156–9169, 9260–9261);
* `art`: the Galois action on these conductor-one points factors through `Pic(𝒪_F)` (print §3.3,
  p. 7: the stabilizer is `F^× 𝒪̂_F^×`; tex 9163–9169), compatibly with both embeddings;
* `red_eq`: `D.red` is `θ_S` restricted (tex 9266–9272).
ABSTRACT. Non-vacuity: `cjToyRealization`. -/
structure CJReductionData.PrintRealization (D : CJReductionData) where
  /-- The print's objects (§§3.1–3.4). -/
  P : CJSetting
  /-- The place `ℓ₀` of `F_CJ = ℚ`. -/
  ℓ₀ : P.Pl
  /-- The rational prime `ℓ₀`. -/
  p₀ : ℕ
  /-- The parameter `D`. -/
  Dpar : ℤ
  /-- The genus partner `h_*`. -/
  hstar : ℤ
  hS : P.S = {ℓ₀}
  hRamB : P.RamB = ∅
  hdegF : P.degF = 1
  hq : P.q ℓ₀ = p₀
  hD : jacobiSym Dpar p₀ = 1
  hh : jacobiSym hstar p₀ = -1
  /-- GLUE: the decomposition law at the odd prime `ℓ₀ ∤ D h_*`. -/
  inert_of_jacobi : jacobiSym (Dpar * hstar) p₀ = -1 → P.ty ℓ₀ = .inert
  /-- The pair of fine conductors `((1), (1))`. -/
  c₀ : P.C
  hval₁ : P.val₁ c₀ ℓ₀ = 0
  hval₂ : P.val₂ c₀ ℓ₀ = 0
  hvn : P.vn ℓ₀ = 0
  hgal : P.galIdx c₀ = 1
  /-- The orientation tuples at the primes of `N`. -/
  Or : Type
  orX : P.X → Or
  orY : P.Y → Or
  /-- The fixed orientation tuple. -/
  o₀ : Or
  or_θ : ∀ x, orY (P.θ x) = orX x
  ιX : D.CMPts → P.X
  ιY : D.Emb → P.Y
  ιX_injective : Function.Injective ιX
  ιY_injective : Function.Injective ιY
  ιX_range : ∀ x, x ∈ Set.range ιX ↔ P.cf x = c₀ ∧ orX x = o₀
  ιY_range : ∀ y, y ∈ Set.range ιY ↔ y ∈ CJSetting.Target c₀ ∧ orY y = o₀
  /-- The Galois action on conductor-one points through `Pic(𝒪_F)`. -/
  art : P.Gal → D.Pic
  art_surjective : Function.Surjective art
  ιX_smul : ∀ g x, ιX (art g • x) = g • ιX x
  ιY_smul : ∀ g y, ιY (art g • y) = g • ιY y
  red_eq : ∀ x, ιY (D.red x) = P.θ (ιX x)

namespace CJReductionData.PrintRealization

variable {D : CJReductionData} (R : D.PrintRealization)

/-- **H.1 for the specialization** (PROVED; tex 9203–9204): `Ram_f M₂(ℚ) = ∅`. -/
theorem h1 : R.P.H1 := by
  unfold CJSetting.H1; rw [R.hRamB]; exact Finset.disjoint_empty_left _

/-- **H.2 for the specialization** (PROVED from `cj_H2`; tex 9204–9205): `1 + 0 + 1` is even. -/
theorem h2 : R.P.H2 := by
  unfold CJSetting.H2
  rw [R.hS, R.hRamB, R.hdegF, Finset.card_singleton, Finset.card_empty]
  exact cj_H2

/-- **`ℓ₀` is inert in `F`** (PROVED from `cj_inert` and the decomposition law; tex 9206–9210). -/
theorem ty_ℓ₀ : R.P.ty R.ℓ₀ = .inert :=
  R.inert_of_jacobi (cj_inert R.hD R.hh)

/-- **H.3 for the specialization** (PROVED; tex 9206–9210): `ℓ₀` is inert. -/
theorem h3 : R.P.H3 := by
  intro v hv
  rw [R.hS, Finset.mem_singleton] at hv
  subst hv
  exact Or.inl R.ty_ℓ₀

/-- **The parity condition at `c₀`** (PROVED; tex 9233–9234): `0 − 0 ≡ v_{ℓ₀}(N) = 0 (mod 2)`. -/
theorem parity₀ : R.P.Parity R.c₀ := by
  intro v hv _
  rw [R.hS, Finset.mem_singleton] at hv
  subst hv
  rw [R.hval₁, R.hval₂, R.hvn]
  exact ⟨0, rfl⟩

/-- **`κ = 1` at `c₀`** (PROVED from `cj_kappa_eq_one`; tex 9235–9243):
`κ = |Gal(F[1]/F[1])| · N_{ℓ₀}(0, 0, 0) = 1 · 1`. -/
theorem kappa₀ : R.P.kappa R.c₀ = 1 := by
  unfold CJSetting.kappa
  rw [R.hS, Finset.prod_singleton, R.hgal, R.ty_ℓ₀, R.hval₁, R.hval₂, R.hvn, R.hq]
  exact cj_kappa_eq_one R.p₀

end CJReductionData.PrintRealization

/-- **The `κ = 1` bijection, DERIVED from the print** (PROVED; tex 9195–9263). If `D` is realized
inside the objects of Cornut–Jetchev at the manuscript's specialization, then Theorem 3.1
(`CJSetting.Thm31`, general `κ`) gives `D.Thm3_1KappaOne`: H.1–H.3, the parity condition and `κ = 1`
are the PROVED specialization checks (`cj_H2`, `cj_inert`, `cj_kappa_eq_one`), so `θ_S` is a bijection
of `c_f⁻¹(c₀)` onto the sign fibre; it preserves the orientation tuple, hence restricts to a bijection
`D.CMPts → D.Emb`; and it is equivariant (§3.2), hence so is `D.red` for `Pic(𝒪_F)`. -/
theorem CJReductionData.thm3_1KappaOne_of_print (D : CJReductionData) (R : D.PrintRealization)
    (hP : R.P.Thm31) : D.Thm3_1KappaOne := by
  have hbij := hP.bijOn_of_kappa_eq_one R.h1 R.h2 R.h3 R.parity₀ R.kappa₀
  refine ⟨⟨fun x₁ x₂ h => ?_, fun y => ?_⟩, fun a x => ?_⟩
  · -- injective
    have hx₁ := (R.ιX_range (R.ιX x₁)).mp ⟨x₁, rfl⟩
    have hx₂ := (R.ιX_range (R.ιX x₂)).mp ⟨x₂, rfl⟩
    have : R.P.θ (R.ιX x₁) = R.P.θ (R.ιX x₂) := by rw [← R.red_eq, ← R.red_eq, h]
    exact R.ιX_injective (hbij.injOn hx₁.1 hx₂.1 this)
  · -- surjective
    obtain ⟨hyT, hyo⟩ := (R.ιY_range (R.ιY y)).mp ⟨y, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hbij.surjOn hyT
    have hox : R.orX x = R.o₀ := by rw [← R.or_θ, hxy, hyo]
    obtain ⟨x', rfl⟩ := (R.ιX_range x).mpr ⟨hx, hox⟩
    exact ⟨x', R.ιY_injective (by rw [R.red_eq, hxy])⟩
  · -- equivariant
    obtain ⟨g, rfl⟩ := R.art_surjective a
    apply R.ιY_injective
    rw [R.red_eq, R.ιX_smul, hP.equivariant R.h1 R.h2 R.h3, ← R.red_eq, R.ιY_smul]

/-- **The exact finite-sum identity of App. F (tex 9279–9286) from the print** (PROVED):
`sum_red_eq` with its hypothesis discharged by `thm3_1KappaOne_of_print`. -/
theorem CJReductionData.sum_red_eq_of_print (D : CJReductionData) (R : D.PrintRealization)
    (hP : R.P.Thm31) {A : Type*} [AddCommGroup A] (P : D.Emb → A) (χ : D.Pic → ℤ)
    (x₀ : D.CMPts) :
    ∑ a : D.Pic, χ a • P (D.red (a • x₀)) = ∑ a : D.Pic, χ a • P (a • D.red x₀) :=
  D.sum_red_eq (D.thm3_1KappaOne_of_print R hP) P χ x₀

/-! ### Non-vacuity of the realization -/

/-- A toy reduction datum: `Pic = ℤ/2` acting on two CM points and two embeddings by translation,
`red = id` (the shape of `cjToySetting`). -/
def cjToyReduction : CJReductionData where
  Pic := Multiplicative (ZMod 2)
  CMPts := ZMod 2
  actCM := cjToyAction
  Emb := ZMod 2
  actEmb := cjToyAction
  red := id

/-- **Non-vacuity (PROVED):** `cjToyReduction` is realized inside `cjToySetting` at the shape of the
manuscript's specialization (`ℓ₀ = 3`, `D = 1`, `h_* = −1`: `(1/3) = 1`, `(−1/3) = −1`). -/
def cjToyRealization : cjToyReduction.PrintRealization where
  P := cjToySetting
  ℓ₀ := ()
  p₀ := 3
  Dpar := 1
  hstar := -1
  hS := rfl
  hRamB := rfl
  hdegF := rfl
  hq := rfl
  hD := by norm_num
  hh := by norm_num
  inert_of_jacobi := fun _ => rfl
  c₀ := ()
  hval₁ := rfl
  hval₂ := rfl
  hvn := rfl
  hgal := rfl
  Or := Unit
  orX := fun _ => ()
  orY := fun _ => ()
  o₀ := ()
  or_θ := fun _ => rfl
  ιX := id
  ιY := id
  ιX_injective := Function.injective_id
  ιY_injective := Function.injective_id
  ιX_range := fun x => ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨x, rfl⟩⟩
  ιY_range := fun y => ⟨fun _ => ⟨⟨rfl, rfl⟩, rfl⟩, fun _ => ⟨y, rfl⟩⟩
  art := id
  art_surjective := Function.surjective_id
  ιX_smul := fun _ _ => rfl
  ιY_smul := fun _ _ => rfl
  red_eq := fun _ => rfl

/-- **Non-vacuity (PROVED):** the hypotheses of `thm3_1KappaOne_of_print` are jointly satisfiable:
a realization together with the print for its setting. -/
theorem cjToyRealization_hypotheses : cjToyRealization.P.Thm31 :=
  cjToySetting_thm31.2.2.2

/-- The derived conclusion at the toy instance (a sanity check of the derivation). -/
theorem cjToyReduction_thm3_1KappaOne : cjToyReduction.Thm3_1KappaOne :=
  cjToyReduction.thm3_1KappaOne_of_print cjToyRealization cjToyRealization_hypotheses

end ZInQ.Manuscript.RC.PrintsArith
