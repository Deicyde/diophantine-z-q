import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Basic

/-!
# Heegner points, cusps and CM reduction: Cai–Chen–Liu, Elkik (Manin–Drinfeld), Cornut–Jetchev

Lane RC9. The finite Heegner descent (`ex:arith-finite-heegner`, tex 2834–3393) and the odd theta
comparison (App. F, `ex:app-theta-comparison`, tex 9103–9405) cite three prints about modular
curves and CM points:

* **Cai–Chen–Liu**, *Heegner points on modular curves*, Trans. AMS 370 (2018), 3721–3743,
  **Theorem 2.15**, p. 3730 (read for this lane: the author's offprint). Use: tex 2914–2936, the
  norm relations (4.1) for `y_d = π(x_d)`.
* **Elkik**, *Le théorème de Manin–Drinfeld*, Astérisque 183 (1990), 59–67, **Théorème, p. 59**
  (read: Numdam scan). Use: tex 2937–2946, finiteness of the cuspidal subgroup `𝒞_N` of `J₀(N)`.
* **Cornut–Jetchev**, *Liftings of reduction maps for quaternion algebras*, preprint (PDF dated
  3 December 2010, author's web page), **Theorem 3.1** (§3.5, p. 9), with §§3.1–3.4 (pp. 4–8),
  Lemma 2.1 (p. 4), Corollary 3.2 (p. 9) and §§4.9–4.10 (p. 15) (read: §§2–3.5, 4.9–4.10). Use:
  tex 2522–2533 ((3.8)) and App. F tex 9195–9295.

**What is genuine.** `ManinDrinfeld` is stated over genuine definitions in its analytic form
(cusp forms, the action of `SL₂(ℤ)` on `ℍ`, path integrals): DEPARTURE of form, since `J₀(N)` and
divisor classes on `X_Γ` are absent from Mathlib; equivalent to the print by the Abel–Jacobi theorem
(GLUE). The Cornut–Jetchev hypothesis checks of App. F (`cj_kappa_eq_one`, `cj_H2`,
`cj_inert`) are PROVED.

**What is an interface.** Modular curves `X₀(N)` as curves over `ℚ`, CM points, ring class fields,
Hecke correspondences, the modular parametrization `π : X₀(N) → E` and supersingular reduction do
not exist in Mathlib. `HeegnerPointData` and `CJReductionData` carry exactly the objects and
properties the proof uses. **Vacuity:** the norm relations alone are satisfied by the zero system
(`HeegnerPointData.zero_normRelations`); in the proof the anchor is Cai–Shu–Tian's height formula
(stated by the shared top layer, `CST.CSTThm11Split`), so `CCLThm2_15Applied` is parametric in an
anchor predicate. **Sizing a genuine definition:** `X₀(N)` over `ℚ` (or its analytic uniformization
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

/-- **The norm relations (4.1)** (tex 2924–2929), the image under `φ` of Cai–Chen–Liu's
Theorem 2.15: `Tr_{H_{dℓ}/H_d} y_{dℓ} = a_ℓ y_d` at an inert `ℓ` (`(D_K/ℓ) = -1`), and
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

/-- **Cai–Chen–Liu, Trans. AMS 370 (2018), Theorem 2.15, p. 3730, applied through `φ`** (PRINT over
the interface `HeegnerPointData`, parametric in the anchor). The print: *`[H_{mℓ} : H_m] = (ℓ+1)/u_m`
if `ℓ` is inert in `K` and `(ℓ-1)/u_m` if `ℓ` is split, and
`u_m ∑_{σ ∈ Gal(H_{mℓ}/H_m)} P_{mℓ}^σ = T_ℓ P_m` (inert), `(T_ℓ - ∑_{w|ℓ} Frob_w) P_m` (split),
with `u_m = 1` for `m ≠ 1` and `u_1 = [𝒪_K^× : ℤ^×]`*, for Heegner points `P_m` of conductor `cm` on
`X_K(N)` and `ℓ, m ∈ ℕ_S`, `S ⊇ prime(6cND_K)` (§2.3), under condition (∗) (p. 3722).

Hypothesis match (tex 2917–2922): with every prime of `N` split in `K`, `N₁ = 1`, `X_K(N) = X₀(N)`
and (∗) is `(d, N) = 1`; `u_m = 1` since `𝒪_K^× = {±1}` (`K ≠ ℚ(i), ℚ(√-3)`). Applying `φ`, with
`φ T_ℓ = [a_ℓ] φ` on degree-zero divisors and `T_ℓ[∞] = (ℓ+1)[∞]` (tex 2933–2936, GLUE), gives
(4.1). The use matches.

The statement is `∃ D, D.NormRelations ∧ Anchor D`: it is the print only for the anchor that pins
`y` to the genuine Heegner points (in the proof, Cai–Shu–Tian at conductor one, stated by the shared
top layer); with `Anchor = fun _ => True` it is vacuous (`zero_normRelations`). -/
def CCLThm2_15Applied (E : WeierstrassCurve ℚ) (Anchor : HeegnerPointData E → Prop) : Prop :=
  ∃ D : HeegnerPointData E, D.NormRelations ∧ Anchor D

/-! ### Cornut–Jetchev: the reduction bijection and the hypothesis checks of App. F -/

/-- **Cornut–Jetchev, Lemma 2.1 (p. 4), the unramified case** (`K_v/F_v` unramified, residue field
of order `q`): `N(n', n'', δ)` is `1` if `δ = |n' - n''|`, `(q - 1) q^{r-1}` if
`δ = |n' - n''| + 2r` with `0 < r < min(n', n'')` (case i), `q^{min(n', n'')}` if `δ = n' + n''`
(case ii), and `0` otherwise. (Cases iii–iv, for ramified and split `K_v`, are not needed.) -/
def cjNUnram (q n₁ n₂ δ : ℕ) : ℕ :=
  if δ = n₁ + n₂ then q ^ min n₁ n₂
  else if max n₁ n₂ - min n₁ n₂ ≤ δ ∧ (δ - (max n₁ n₂ - min n₁ n₂)) % 2 = 0 ∧
      (δ - (max n₁ n₂ - min n₁ n₂)) / 2 < min n₁ n₂ then
    (if δ = max n₁ n₂ - min n₁ n₂ then 1
      else (q - 1) * q ^ ((δ - (max n₁ n₂ - min n₁ n₂)) / 2 - 1))
  else 0

/-- **`N_{ℓ₀}(0, 0, 0) = 1`** (App. F tex 9238–9242, "which also follows directly from
[Lemma 2.1(ii)]"), PROVED from the encoding of Lemma 2.1. -/
theorem cjNUnram_zero (q : ℕ) : cjNUnram q 0 0 0 = 1 := by
  simp [cjNUnram]

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

/-- **The conclusion of Cornut–Jetchev's Theorem 3.1 (§3.5, p. 9) with `κ = 1`**: *by restriction,
`θ_S` induces a surjective `κ`-to-`1` correspondence
`c_f^{-1}(c', c'') → c_{S,f}^{-1}(c'_S, c''_S) ∩ ψ_{S'}^{-1}(e_{S'}(c', c''))`*; with `κ = 1`
(`cj_kappa_eq_one`) and the orientation tuple fixed, an equivariant bijection of `Pic`-torsors
(tex 9256–9261: "Theorem 3.1 gives a bijection onto one such sign, not onto both"). PRINT over the
interface `CJReductionData` (the print is stated for the genuine adelic `θ_S`). Note: Corollary 4.1
(p. 15) counts conjugate *pairs* of optimal embeddings; the manuscript uses the sign fiber of
Theorem 3.1 instead (tex 9368–9370), which is the print's own formulation. -/
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

end ZInQ.Manuscript.RC.PrintsArith
