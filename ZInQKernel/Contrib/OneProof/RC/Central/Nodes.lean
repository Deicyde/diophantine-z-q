import ZInQKernel.Contrib.CloudB3RC53.Nodes
import ZInQKernel.Contrib.OneProof.RC.Central.BaseZero
import ZInQKernel.Contrib.OneProof.RC.Central.Correction
import ZInQKernel.Contrib.OneProof.RC.Central.Calibration

/-!
# Lane RC15 (central): the blueprint nodes `BaseZero` and `UpperBound`

The shared top layer of the proof of Theorem 5.3 (namespace `ZInQ.Contrib.CloudB3RC53`) asks, in
`FixedFieldPackage.coord`, for coefficient data `C : CoordData b` with, among others,
`UpperBound C B` (tex 5730–5733: `v₂ ũ_x(0) ≤ B` at `x ≠ 0`, from (3.9), (3.4), (4.6), (4.7)) and
`BaseZero E k C` (Lemma `ex:arith-base-zero`, tex 4319–4373: `L'(E/K,1) = 0 ⇒ ũ₀(0) = 0`). This
file produces both nodes from the results of this lane and from inputs stated as hypotheses with
their kinds.

## Cai–Shu–Tian

Following the lane's instruction, Cai–Shu–Tian, Theorem 1.1 is **not** stated here: it enters as an
abstract proposition `CSTThm11 : Prop`, to be instantiated by the project's statement
`ZInQ.Contrib.CloudB3RC53.CST.CSTThm11Split` (Cai, Shu, Tian, "Explicit Gross–Zagier and
Waldspurger formulae", Algebra & Number Theory 8 (2014) 2523–2572, Theorem 1.1, pp. 2524–2525;
the project's theorem-application audit, entry A027), together with its use at conductor one
(`hheight`, PRINT application): `L'(E/K, 1) = 0` makes the conductor-one Heegner point torsion
(tex 4336–4337, "the conductor-one height formula"). Deriving `hheight` from
`CST.CSTThm11Split` needs the factorization `L(E/K, s) = L(E, s) L(E^{(k)}, s)` of the
character-one `twistedLFunction` and `ĥ = 0 ⇔ torsion` (both GLUE); that derivation belongs with
the other applications of the print (the genus and odd-form inputs, tex 2403–2591).

* `baseZero_node` (`BaseZero E k C`): PROVED from `baseZero_core` and the inputs.
* `F8_of_calibration` (tex 10886–10891, (F.8)): the corrected central value has the calibrated
  valuation, from (4.6) for `u_prim` and the `Λ`-unit comparison (4.7). PROVED.
* `upperBound_node` (`UpperBound C B`): PROVED from (F.8) and (3.9)+(3.4).
* `upperBound_of_calibration`: the composite, with the explicit `B = C_J + C_cal`. PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Central

open ZInQ.Contrib.CloudB3RC53 Matrix

/-- **`BaseZero` from Lemma `ex:arith-base-zero`** (tex 4319–4373).

Objects: `K = ℚ(√k)` and the conductor-one Heegner point `P ∈ E(K)`; the DVR `A` (the manuscript's
`Λ_{(t)}`, residue field `ℚ₂`, residue map `ρ`) with fraction field `F`; the two-term model `D` of
the primitive complex at the base `h₀ = 1` with its cycle `z`, closed functional `w` and generic
coordinate `uprim` (`Coordinate.lean`, `BaseZero.lean`); the central Kummer comparison `κ` (the
rational Kummer map followed by the comparison `i`, into the central degree-one cochains of the
model); the corrected coordinate `ũ₀`.

Inputs (kinds):
* `hCST : CSTThm11` and `hheight` (PRINT and its application): see the module docstring;
* `hcentral` (ELLIOT, tex 4346–4348): full Selmer corank one for `E/K` (tex 2617–2647) gives central
  dimensions `(1,1)`;
* `hu` (definition): `uprim` is the class-functional coordinate of `(z, w)` on the model;
* `h45` (ELLIOT, the retained boundary (4.5), tex 3911–3915, 4338–4340): `z̄ = i(Lm P)`;
* `h47` (ELLIOT, (4.7) and the correction `η` at the base, tex 4365–4368; the algebra is
  `corrected_eq`): `ũ₀ = ε₀ u_{prim,0}` with `ε₀ ∈ A`;
* `hcoef` (GLUE, identification of the package's datum): `C.u 0 0` is the value of `ũ₀` at
  `t = 0`, i.e. the residue of any integral representative.

PROVED: `L'(E/K,1) = 0` (`ProductOrderGeTwo E k`) gives `C.u 0 0 = 0`. -/
theorem baseZero_node {E : WeierstrassCurve ℚ} {k : ℚ} {b : ℕ} (C : CoordData b)
    (K : Type*) [Field K] [DecidableEq K] [Algebra ℚ K] (P : (E.baseChange K).toAffine.Point)
    (CSTThm11 : Prop) (hCST : CSTThm11)
    (hheight : CSTThm11 → ProductOrderGeTwo E k → IsOfFinAddOrder P)
    {A F : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F]
    [Algebra A F] [IsFractionRing A F] (ρ : A →+* ℚ_[2])
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {m : ℕ}
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hcentral : (D.map ρ).rank = m)
    (z w : Fin (m + 1) → A) (hz : D *ᵥ z = 0) (uprim : F)
    (hu : IsClassFunctionalCoord (D.map (algebraMap A F)) (fun i => algebraMap A F (z i))
      (fun i => algebraMap A F (w i)) uprim)
    (κ : (E.baseChange K).toAffine.Point →+ (Fin (m + 1) → ℚ_[2])) (Lm : ℤ)
    (h45 : (fun i => ρ (z i)) = (Lm : ℚ_[2]) • κ P)
    (ε₀ : A) (utilde0 : F) (h47 : utilde0 = algebraMap A F ε₀ * uprim)
    (hcoef : ∀ a : A, algebraMap A F a = utilde0 → ρ a = C.u 0 0) :
    BaseZero E k C := by
  intro hL
  have hP := hheight hCST hL
  have hκ : κ P = 0 := kummer_eq_zero_of_isOfFinAddOrder κ hP
  have hz0 : ∀ i, ρ (z i) = 0 := by
    intro i
    have := congrFun h45 i
    rw [hκ, smul_zero] at this
    exact this
  obtain ⟨-, a, ha, hρa⟩ := baseZero_core (F := F) ρ hρ D hcentral z w hz uprim hu hz0 ε₀
  rw [← hcoef a (ha.trans h47.symm), hρa]

/-- **(F.8) from (4.6) and (4.7)** (tex 4155–4158, 10886–10891): if at `x ≠ 0` the primitive
central value `u_{prim,x}(0) ∈ ℚ₂` is nonzero with the calibrated valuation (4.6), and the
package's value `C.u x 0 = ũ_x(0)` equals `e_x · u_{prim,x}(0)` with `e_x = ε_x(0)` the value of
the `Λ`-unit of (4.7) (two-adic valuation `0`), then `C.u x 0 ≠ 0` and it has the same valuation.
PROVED. -/
theorem F8_of_calibration {b : ℕ} (C : CoordData b) (uprim0 e : (Fin b → ZMod 2) → ℚ_[2])
    (formula : (Fin b → ZMod 2) → ℤ)
    (h46 : ∀ x, x ≠ 0 → uprim0 x ≠ 0 ∧ (uprim0 x).valuation = formula x)
    (h47 : ∀ x, x ≠ 0 → C.u x 0 = e x * uprim0 x)
    (he : ∀ x, x ≠ 0 → e x ≠ 0 ∧ (e x).valuation = 0) :
    ∀ x, x ≠ 0 → C.u x 0 ≠ 0 ∧ (C.u x 0).valuation = formula x := by
  intro x hx
  obtain ⟨hu0, hv⟩ := h46 x hx
  obtain ⟨he0, hev⟩ := he x hx
  rw [h47 x hx]
  exact ⟨mul_ne_zero he0 hu0, by rw [Padic.valuation_mul he0 hu0, hev, hv, zero_add]⟩

/-- **`UpperBound` from (F.8) and (3.9) + (3.4)** (tex 5730–5733, 10869–10893). At every `x ≠ 0`:
`ũ_x(0) ≠ 0` with `v₂ ũ_x(0) = 2 j_x − 4ω_x − s_x − s'_x − T_x + ε_x` ((F.8): (4.6) transported by
(4.7)), `2 j_x ≤ 4ω_x + C_J` ((3.9) with (3.4), tex 2695–2705, 10869–10875), `|ε_x| ≤ C_cal`, and
the finite-`Ш` lengths and the companion sum are nonnegative (they "have negative sign and may be
discarded for this upper bound", tex 5731–5732). Then `UpperBound C B` for every
`B ≥ C_J + C_cal`. PROVED. -/
theorem upperBound_node {b : ℕ} (C : CoordData b) (j ω sh shk T ε : (Fin b → ZMod 2) → ℤ)
    (CJ Ccal : ℤ) (hF8 : ∀ x, x ≠ 0 → C.u x 0 ≠ 0 ∧
      (C.u x 0).valuation = 2 * j x - 4 * ω x - sh x - shk x - T x + ε x)
    (h39 : ∀ x, x ≠ 0 → 2 * j x ≤ 4 * ω x + CJ) (hε : ∀ x, x ≠ 0 → |ε x| ≤ Ccal)
    (hs : ∀ x, x ≠ 0 → 0 ≤ sh x ∧ 0 ≤ shk x ∧ 0 ≤ T x) (B : ℕ) (hB : CJ + Ccal ≤ B) :
    UpperBound C B := by
  intro x hx
  obtain ⟨hne, hv⟩ := hF8 x hx
  have h1 := h39 x hx
  have h2 := (abs_le.mp (hε x hx)).2
  obtain ⟨s1, s2, s3⟩ := hs x hx
  have hvB : (C.u x 0).valuation ≤ B := by omega
  rw [Padic.norm_eq_zpow_neg_valuation hne]
  push_cast
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

/-- **`UpperBound` from the calibration inputs, with the explicit bound** (tex 4044–4047,
5730–5733, 10886–10893): the composite of `calibration_46` (the error is `|ε_x| ≤ 2 v₂L + 2G₀ + 5`,
uniform in `x`), `F8_of_calibration` and `upperBound_node`, with `B = C_J + 2 v₂L + 2G₀ + 5`.
The per-address inputs of (4.6) are those of `calibration_46`. PROVED. -/
theorem upperBound_of_calibration {b : ℕ} (C : CoordData b) (uprim0 e : (Fin b → ZMod 2) → ℚ_[2])
    (j vm vN ω gA sA gB sB sh shk vReg vΩ vC T : (Fin b → ZMod 2) → ℤ) (vL G₀ CJ : ℤ)
    (hprimne : ∀ x, x ≠ 0 → uprim0 x ≠ 0)
    (hprim : ∀ x, x ≠ 0 → (uprim0 x).valuation = (j x + vL + vm x) + (j x + vL + vm x) +
      (diskContribution 1 (gA x) + diskContribution 2 (sA x) + diskContribution 3 (gA x)) +
      (2 * diskContribution 2 (vN x) + ω x * (2 * diskContribution 2 2)))
    (hvN : ∀ x, x ≠ 0 → vN x = vm x)
    (hMilne : ∀ x, x ≠ 0 → sA x - sB x = 2 * gA x - 2 * gB x + vReg x + vΩ x + vC x)
    (hsB : ∀ x, x ≠ 0 → sB x = sh x + shk x) (hvC : ∀ x, x ≠ 0 → vC x = T x)
    (hReg : ∀ x, x ≠ 0 → vReg x = 1 ∨ vReg x = -1) (hΩ : ∀ x, x ≠ 0 → |vΩ x| ≤ 4)
    (hgB : ∀ x, x ≠ 0 → 0 ≤ gB x ∧ gB x ≤ G₀) (hvL : 0 ≤ vL)
    (h47 : ∀ x, x ≠ 0 → C.u x 0 = e x * uprim0 x)
    (he : ∀ x, x ≠ 0 → e x ≠ 0 ∧ (e x).valuation = 0)
    (h39 : ∀ x, x ≠ 0 → 2 * j x ≤ 4 * ω x + CJ)
    (hs : ∀ x, x ≠ 0 → 0 ≤ sh x ∧ 0 ≤ shk x ∧ 0 ≤ T x)
    (B : ℕ) (hB : CJ + (2 * vL + 2 * G₀ + 5) ≤ B) : UpperBound C B := by
  have hcal : ∀ x, x ≠ 0 → (uprim0 x).valuation =
      2 * j x - 4 * ω x - sh x - shk x - T x + (2 * vL + 2 * gB x - vReg x - vΩ x) ∧
      |2 * vL + 2 * gB x - vReg x - vΩ x| ≤ 2 * vL + 2 * G₀ + 5 := fun x hx =>
    calibration_46 (hprim x hx) (hvN x hx) (hMilne x hx) (hsB x hx) (hvC x hx) (hReg x hx)
      (hΩ x hx) (hgB x hx) hvL
  have hF8 := F8_of_calibration C uprim0 e
    (fun x => 2 * j x - 4 * ω x - sh x - shk x - T x + (2 * vL + 2 * gB x - vReg x - vΩ x))
    (fun x hx => ⟨hprimne x hx, (hcal x hx).1⟩) h47 he
  exact upperBound_node C j ω sh shk T (fun x => 2 * vL + 2 * gB x - vReg x - vΩ x) CJ
    (2 * vL + 2 * G₀ + 5) hF8 h39 (fun x hx => (hcal x hx).2) hs B hB

end ZInQ.Manuscript.RC.Central
