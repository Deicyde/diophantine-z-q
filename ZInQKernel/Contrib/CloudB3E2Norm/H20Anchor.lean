import ZInQKernel.Contrib.CloudB3E2Norm.H20Dictionary
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST

/-!
# The genuine-point anchor for the Cai–Chen–Liu print

Manuscript `diophantine_zq.tex`, tex 2914–2936: "`y_d = π(x_d)`, the image under the modular
parametrization of the CM point `x_d ∈ X₀(N)(H_d)` chosen by compatible proper ideal lattices and
fixed orientations at `N`", and the norm relations (4.1), the image under `π` of Cai–Chen–Liu,
Trans. AMS 370 (2018), Theorem 2.15.

`RC/PrintsArith/Heegner.lean` states the print as `CCLThm2_15Applied E Anchor :=
∃ D : HeegnerPointData E, D.NormRelations ∧ Anchor D`; it is the print only for an anchor that pins
`D.y` to the genuine Heegner points (with `Anchor = fun _ => True` it is vacuous). This file gives
that anchor, in the vocabulary of the shared top layer's Cai–Shu–Tian print
(`CloudB3RC53/Prints/CST.lean`: the newform level `newformLevel`, the analytic
parametrization
`phiAn E f Lat κ` with `IsLatticeOf`, `IsNonCMLattice`, `IsParamScale`, Heegner forms
`IsHeegnerForm`, CM points `cmPoint`):

* **`GenuineHeegnerAnchor E K p ι D`** (definition): `D.N` is the newform level of `E`,
  `D.DK = disc K`, and for every conductor `d ≥ 1` prime to `N D_K` the point `D.y d` is defined
  over `D.H d` and its image under `ι : ℚ̄ → ℂ` is `φ(τ)` for the root `τ` of a Heegner form of
  level `N`
  and discriminant `D_K d²` — the CST quantification "any `y` with `ι(y) = φ(τ)`", at every
  conductor.
* `CCLGenuine E K p ι := CCLThm2_15Applied E (GenuineHeegnerAnchor …)` (definition): the
  print with this anchor. It is a consequence of the print: Cai–Chen–Liu's compatible family of CM
  points (`P_m = π(x_m)`, §2.3) satisfies the anchor, whose existential choice of forms is weaker
  than their compatible choice (so no compatibility is asserted beyond the print).
* `anchor_coords` (PROVED): the anchor gives the field-level input (i) of `H20Dictionary`
  (`D.y n` defined over `D.H n`) at admissible conductors.
* `anchor_y_zero` (PROVED; non-degeneracy): an anchored `D` has `D.y d = 0` only if the genuine
  parametrization `φ` vanishes at the CM point (the zero system of `zero_normRelations` is anchored
  only where the genuine Heegner points vanish).
* **`hnorm_of_genuine_print`** (PROVED): from `CCLGenuine` and the remaining field-level dictionary
  (ii)–(iv) of `H20Dictionary` for the anchored datum, the input `hnorm` of `h1_shapiro` for the
  realized genuine Heegner points.

Kinds: definitions and PROVED from the PRINT `CCLThm2_15Applied` with the anchor; the analytic
model of the parametrization and the CM points are the CST dictionaries (CONSEQUENCE GLUE).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve
open scoped WeierstrassCurve UpperHalfPlane

set_option linter.unusedSectionVars false

section Anchor

variable (E : WeierstrassCurve ℚ) (K : Type) [Field K] [NumberField K]

/-- **The modular parametrization data of the Cai–Shu–Tian print** (`CST.lean`, the hypotheses of
`CSTThm11Split`): the newform `f` of level `N_E` with the Dirichlet coefficients of `L(E, s)`, a
period lattice `Lat` of `E` without complex multiplication, and a scale `κ ≠ 0` making
`phiAn E f Lat κ` a `Γ₀(N_E)`-invariant analytic map `X₀(N_E)(ℂ) → E(ℂ)`. Kind: definition. -/
structure CSTParam where
  /-- the newform -/
  f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2
  /-- its coefficients are those of `L(E, s)` -/
  hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)
  /-- the period lattice -/
  Lat : PeriodPair
  /-- `Lat` is a lattice of `E` -/
  hLat : IsLatticeOf E Lat
  /-- `E` has no complex multiplication -/
  hCM : IsNonCMLattice Lat
  /-- the scale -/
  κ : ℂ
  /-- the parametrization is `Γ₀(N_E)`-invariant (in particular `κ ≠ 0`) -/
  hκ : IsParamScale (newformLevel E) f Lat κ

open Classical in
/-- **The genuine-point anchor** (tex 2914–2917): `D.N = N_E` (the newform level), `D.DK = disc K`,
and for every `d ≥ 1` prime to `N D_K`: `D.y d ∈ E(D.H d)` and `ι(D.y d) = φ(τ)` for the root `τ`
of a Heegner form of level `N` and discriminant `D_K d²`. Kind: definition. -/
def GenuineHeegnerAnchor (p : CSTParam E) (ι : Qbar →ₐ[ℚ] ℂ) (D : HeegnerPointData E) : Prop :=
  D.N = newformLevel E ∧ D.DK = discr K ∧
    ∀ d : ℕ, 0 < d → Nat.Coprime d (D.N * D.DK.natAbs) →
      (∃ Y' : (E.baseChange (D.H d)).toAffine.Point,
        Affine.Point.map (W' := E) (D.H d).val Y' = D.y d) ∧
      ∃ A B C : ℤ, IsHeegnerForm D.N (D.DK * (d : ℤ) ^ 2) A B C ∧
        Affine.Point.map (W' := E) ι (D.y d) =
          phiAn E p.f p.Lat p.κ (cmPoint A B (D.DK * (d : ℤ) ^ 2))

/-- **The Cai–Chen–Liu print with the genuine-point anchor** (PRINT, tex 2914–2936): some Heegner
point datum anchored to the CM points satisfies the norm relations (4.1). Kind: definition. -/
def CCLGenuine (p : CSTParam E) (ι : Qbar →ₐ[ℚ] ℂ) : Prop :=
  CCLThm2_15Applied E (GenuineHeegnerAnchor E K p ι)

variable {E K}

/-- **The anchor gives the coordinates input (i) of the dictionary** (PROVED). -/
theorem anchor_coords {p : CSTParam E} {ι : Qbar →ₐ[ℚ] ℂ}
    {D : HeegnerPointData E} (hA : GenuineHeegnerAnchor E K p ι D) {d : ℕ} (hd : 0 < d)
    (hcop : Nat.Coprime d (D.N * D.DK.natAbs)) :
    ∃ Y' : (E.baseChange (D.H d)).toAffine.Point,
      Affine.Point.map (W' := E) (D.H d).val Y' = D.y d :=
  (hA.2.2 d hd hcop).1

/-- **Non-degeneracy of the anchor** (PROVED): an anchored datum has `D.y d = 0` only if the
analytic parametrization vanishes at the CM point of some Heegner form of discriminant `D_K d²`. -/
theorem anchor_y_zero {p : CSTParam E} {ι : Qbar →ₐ[ℚ] ℂ}
    {D : HeegnerPointData E} (hA : GenuineHeegnerAnchor E K p ι D) {d : ℕ} (hd : 0 < d)
    (hcop : Nat.Coprime d (D.N * D.DK.natAbs)) (h0 : D.y d = 0) :
    ∃ A B C : ℤ, IsHeegnerForm D.N (D.DK * (d : ℤ) ^ 2) A B C ∧
      phiAn E p.f p.Lat p.κ (cmPoint A B (D.DK * (d : ℤ) ^ 2)) = 0 := by
  obtain ⟨A, B, C, hF, hφ⟩ := (hA.2.2 d hd hcop).2
  refine ⟨A, B, C, hF, ?_⟩
  rw [← hφ, h0, map_zero]

end Anchor

/-! ### The norm relation for the genuine Heegner points -/

section Norm

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) [(E.baseChange K).IsElliptic]
  {Δ : Type} [CommGroup Δ] [Finite Δ]
  (HP : Subgroup (GKS K S)) (U : Subgroup HP) [Fintype (HP ⧸ U)] (t : HP ⧸ U → HP)

/-- **`hnorm` for the genuine Heegner points from the anchored print** (PROVED from the PRINT
`CCLGenuine`): there is an anchored datum `D` (its points are the images of CM points, `D.N = N_E`,
`D.DK = disc K`) such that, whenever the remaining dictionary (ii)–(iv) of `H20Dictionary` holds for
it at an admissible `(d, q)` with `q` split, the realized points `y_R = 1 ⊗ P_{dq}`,
`y_P = 1 ⊗ P_d` satisfy the input `hnorm` of `h1_shapiro`; the coordinates input (i) is supplied by
the anchor (`anchor_coords`). -/
theorem hnorm_of_genuine_print {p : CSTParam E} {ι : Qbar →ₐ[ℚ] ℂ}
    (hprint : CCLGenuine E K p ι) :
    ∃ D : HeegnerPointData E, GenuineHeegnerAnchor E K p ι D ∧ D.NormRelations ∧
      ∀ {d q : ℕ} (_ : D.Admissible d q) (_ : jacobiSym D.DK q = 1) (σ : GKS K S)
        (κ' : Qbar →ₐ[ℚ] AlgebraicClosure K)
        (hκR : ∀ x ∈ D.H (d * q), κ' x ∈ unramifiedOutside K S₀)
        (hκP : ∀ x ∈ D.H d, κ' x ∈ unramifiedOutside K S₀)
        (e : HP ⧸ U ≃ D.relGal d q)
        (_ : ∀ τ (x) (hx : x ∈ D.H (d * q)), κ' ((e τ).1 x) =
          (galS K S₀ (inflMap K hS (t τ : GKS K S)) ⟨κ' x, hκR x hx⟩ : AlgebraicClosure K))
        (_ : ∀ x (hx : x ∈ D.H d), κ' (D.frob d q x) =
          (galS K S₀ (inflMap K hS σ) ⟨κ' x, hκP x hx⟩ : AlgebraicClosure K))
        (_ : ∀ x ∈ D.H d, (D.frob d q)⁻¹ x ∈ D.H d),
        ∃ (hyR : ∃ Y' : (E.baseChange (D.H (d * q))).toAffine.Point,
            Affine.Point.map (W' := E) (D.H (d * q)).val Y' = D.y (d * q))
          (hyP : ∃ Y' : (E.baseChange (D.H d)).toAffine.Point,
            Affine.Point.map (W' := E) (D.H d).val Y' = D.y d),
          ∑ τ : HP ⧸ U, ambRhoU hS (E.baseChange K) Δ (t τ : GKS K S)
              (yPt E hS (Δ := Δ) (realize E S₀ κ' (D.H (d * q)) hκR (D.y (d * q)) hyR)) =
            (E.LFunction q : ℤ) • yPt E hS (Δ := Δ) (realize E S₀ κ' (D.H d) hκP (D.y d) hyP) -
              ambRhoU hS (E.baseChange K) Δ σ
                (yPt E hS (Δ := Δ) (realize E S₀ κ' (D.H d) hκP (D.y d) hyP)) -
              ambRhoU hS (E.baseChange K) Δ σ⁻¹
                (yPt E hS (Δ := Δ) (realize E S₀ κ' (D.H d) hκP (D.y d) hyP)) := by
  obtain ⟨D, hD, hA⟩ := hprint
  refine ⟨D, hA, hD, fun {d q} hadm hsplit σ κ' hκR hκP e hτ hf hstab => ?_⟩
  obtain ⟨hd, hdcop, hq, hqd⟩ := hadm
  have hcopP : Nat.Coprime d (D.N * D.DK.natAbs) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 (by ring)) hdcop
  have hdq : 0 < d * q := Nat.mul_pos hd hq.pos
  have hcopR : Nat.Coprime (d * q) (D.N * D.DK.natAbs) := by
    refine Nat.Coprime.mul_left hcopP ?_
    exact (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqd (h.trans ⟨6 * d, by ring⟩)
  have hyR := anchor_coords hA hdq hcopR
  have hyP := anchor_coords hA hd hcopP
  exact ⟨hyR, hyP, hnorm_of_fields E hS HP U t D hD ⟨hd, hdcop, hq, hqd⟩ hsplit σ κ' hyR hyP
    hκR hκP e hτ hf hstab⟩

end Norm

end ZInQ.Contrib.CloudB3E2.NormCochain
