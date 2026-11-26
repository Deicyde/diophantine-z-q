import ZInQKernel.Contrib.CloudB3E2Norm.H20Dictionary
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST

/-!
# The genuine Heegner point anchor

Manuscript `diophantine_zq.tex`, tex 2914–2936: "`y_d = π(x_d)`, the image under the modular
parametrization of the CM point `x_d ∈ X₀(N)(H_d)` chosen by compatible proper ideal lattices and
fixed orientations at `N`", and the norm relations (4.1), the image under `π` of Cai–Chen–Liu,
Trans. AMS 370 (2018), Theorem 2.15.

The anchor identifies the points in `HeegnerPointData` with the CM points under the
parametrization. It uses the newform level `newformLevel`, the analytic parametrization
`phiAn E f Lat κ`, the Heegner forms `IsHeegnerForm` and the CM points `cmPoint` from
`CloudB3RC53/Prints/CST.lean`.

* **`GenuineHeegnerAnchor E K p ι D`** (definition): `D.N` is the newform level of `E`,
  `D.DK = disc K`, and for every conductor `d ≥ 1` prime to `N D_K` the point `D.y d` is defined
  over `D.H d` and its image under `ι : ℚ̄ → ℂ` is `φ(τ)` for the root `τ` of a Heegner form of
  level `N`
  and discriminant `D_K d²` — the CST quantification "any `y` with `ι(y) = φ(τ)`", at every
  conductor.
* `anchor_coords` (PROVED): the anchor gives the field-level input (i) of `H20Dictionary`
  (`D.y n` defined over `D.H n`) at admissible conductors.
* `anchor_y_zero` (PROVED; non-degeneracy): an anchored `D` has `D.y d = 0` only if the genuine
  parametrization `φ` vanishes at the CM point (the zero system of `zero_normRelations` is anchored
  only where the genuine Heegner points vanish).

Kinds: definitions and PROVED; the analytic model of the parametrization and the CM points are
the CST dictionaries (CONSEQUENCE GLUE).
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

end ZInQ.Contrib.CloudB3E2.NormCochain
