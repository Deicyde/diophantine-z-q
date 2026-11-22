import ZInQKernel.Contrib.CloudB3RC53.Prints.Kolyvagin
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_PeriodPair_discriminant_ne_zero

/-!
# From modularity to a weak Weil parametrization: reduction to one period statement

Manuscript `diophantine_zq.tex`, `lem:forward-rank`, tex L1092–1093: "Modularity follows from
[BCDT, Theorem A]. Apply [Kolyvagin, Theorem 1, pp. 4–5]." `Prints/Kolyvagin.lean` isolates the
passage from modularity (`IsModular`) to Kolyvagin's premise as the gap `ModularToWeakWeil`, with
the parametrization in its analytic form (`HasWeakWeilParametrization`: a weight-two `Γ₀(N)` cusp
form `f` with the coefficients of `L(E, s)` at `N = newformLevel E`, a period lattice `Lat` of `E`,
and a nonzero rational `c` with `c · (periods of f) ⊆ Lat`).

This file proves `ModularToWeakWeil` from ONE named input:

* `exists_form_at_newformLevel` (PROVED): a modular `E` has a cusp form with the coefficients of
  `L(E, s)` at level `newformLevel E` (the least level, `Nat.sInf_mem`). Trivial nebentypus is
  already part of `IsModular`, so no descent from `Γ₁(N)` is needed in this model.
* `exists_isLatticeOf` (PROVED): every elliptic `E/ℚ` has a period lattice with
  `g₂ = c₄/12`, `g₃ = c₆/216` (`IsLatticeOf`). The proof uses the uniformization theorem for
  elliptic curves over `ℂ` and the homogeneity of the lattice invariants from the vendored library
  `ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT`:
  `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq` and
  `P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair.g₂_scale` / `g₃_scale`, vendored from
  `anthropics/fermats-last-theorem` at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, licence
  Apache-2.0 (see `Vendor/AnthropicFLT/LICENSE`, `NOTICE.upstream`, `ATTRIBUTION.upstream.md`).
  These are library results used as infrastructure, not prints.
* `NewformPeriodsRational` — **ELLIOT-gap residue** of the text's step at tex L1092–1093: for an
  elliptic `E/ℚ`, a cusp form `f` on `Γ₀(newformLevel E)` with the coefficients of `L(E, s)` and a
  period lattice `Lat` of `E`, some nonzero rational `c` scales the periods of `2πi f dτ` into
  `Lat` (`IsParamScale`). This is the content of Shimura's construction of `E_f`, Faltings'
  isogeny theorem, and the rationality of the pull-back scalar, on which BCDT's implication
  (2) ⇒ (6) relies. Print status pending: only sources the manuscript cites can be prints.
* **`modularToWeakWeil_of_newformPeriodsRational` (PROVED)**: `NewformPeriodsRational →
  ModularToWeakWeil`.
* Non-vacuity: `isParamScale_zero` (the conclusion shape of `NewformPeriodsRational` is satisfiable,
  by the zero form with any nonzero scale) and `exists_isLatticeOf_example` (a concrete lattice for
  `y² = x³ − x`).

**Classification.** PROVED from the named input `NewformPeriodsRational` (ELLIOT-gap residue).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ModularWeil

open ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript ZInQ.Manuscript.PoleS12 CST

/-- **The form at the least level** (PROVED): a modular `E` has a cusp form on
`Γ₀(newformLevel E)` with the coefficients of `L(E, s)`. -/
theorem exists_form_at_newformLevel (E : WeierstrassCurve ℚ) (hM : IsModular E) :
    0 < newformLevel E ∧ HasCuspFormAtLevel E (newformLevel E) := by
  obtain ⟨N, hN, f, hf⟩ := hM
  have hne : {N : ℕ | 0 < N ∧ HasCuspFormAtLevel E N}.Nonempty := ⟨N, hN, f, hf⟩
  exact Nat.sInf_mem hne

/-- The Weierstrass model of a lattice has `c₆ = 216 g₃`. PROVED. -/
theorem weierstrassCurve_c₆ (L : PeriodPair) : L.weierstrassCurve.c₆ = 216 * L.g₃ := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂, PeriodPair.weierstrassCurve_a₃,
    PeriodPair.weierstrassCurve_a₄, PeriodPair.weierstrassCurve_a₆]
  ring

/-- **Every elliptic curve over `ℚ` has a period lattice** (`IsLatticeOf`, PROVED; uniformization
and homogeneity from the vendored library, see the module docstring). -/
theorem exists_isLatticeOf (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ Lat : PeriodPair, IsLatticeOf E Lat := by
  obtain ⟨L, C, hC⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq (E.baseChange ℂ)
  refine ⟨L.scale C.u, ?_, ?_⟩
  · have h4 := congrArg WeierstrassCurve.c₄ hC
    rw [WeierstrassCurve.variableChange_c₄, PeriodPair.weierstrassCurve_c₄,
      WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄] at h4
    rw [P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair.g₂_scale]
    have h4' : (E.c₄ : ℂ) = ((C.u : ℂ) ^ 4)⁻¹ * (12 * L.g₂) := by
      rw [← h4.trans (eq_ratCast (algebraMap ℚ ℂ) E.c₄)]; simp [Units.val_inv_eq_inv_val]
    rw [h4']
    ring
  · have h6 := congrArg WeierstrassCurve.c₆ hC
    rw [WeierstrassCurve.variableChange_c₆, weierstrassCurve_c₆,
      WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆] at h6
    rw [P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair.g₃_scale]
    have h6' : (E.c₆ : ℂ) = ((C.u : ℂ) ^ 6)⁻¹ * (216 * L.g₃) := by
      rw [← h6.trans (eq_ratCast (algebraMap ℚ ℂ) E.c₆)]; simp [Units.val_inv_eq_inv_val]
    rw [h6']
    ring

/-- **ELLIOT-gap residue of tex L1092–1093: the periods of the newform are rational multiples of
lattice vectors.** For an elliptic `E/ℚ`, every cusp form `f` on `Γ₀(newformLevel E)` with the
coefficients of `L(E, s)` and every period lattice `Lat` of `E` admit a nonzero rational `c` with
`c · (periods of 2πi f dτ) ⊆ Lat` (`IsParamScale`). Content: Shimura's construction of `E_f`,
Faltings' isogeny theorem, and the rationality of the pull-back scalar (what BCDT's (2) ⇒ (6)
relies on). Print status pending (only sources the manuscript cites can be prints). -/
def NewformPeriodsRational : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
    ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2),
      (∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) →
      ∀ Lat : PeriodPair, IsLatticeOf E Lat →
        ∃ c : ℚ, IsParamScale (newformLevel E) f Lat (c : ℂ)

/-- **`ModularToWeakWeil` from the single named input** `NewformPeriodsRational`. PROVED. -/
theorem modularToWeakWeil_of_newformPeriodsRational (h : NewformPeriodsRational) :
    ModularToWeakWeil := by
  intro E hE hM
  obtain ⟨-, f, hf⟩ := exists_form_at_newformLevel E hM
  obtain ⟨Lat, hLat⟩ := exists_isLatticeOf E
  obtain ⟨c, hc⟩ := h E hE f hf Lat hLat
  exact ⟨f, Lat, c, hf, hLat, hc⟩

/-! ### Non-vacuity -/

/-- The conclusion shape of `NewformPeriodsRational` is satisfiable: for the zero function every
nonzero scale works (its Eichler potential vanishes). PROVED. -/
theorem isParamScale_zero (N : ℕ) (Lat : PeriodPair) :
    IsParamScale N (0 : UpperHalfPlane → ℂ) Lat ((1 : ℚ) : ℂ) := by
  refine ⟨by norm_num, fun γ _ τ => ?_⟩
  have h0 : ∀ τ : UpperHalfPlane, eichlerPotential (0 : UpperHalfPlane → ℂ) τ = 0 := fun τ => by
    simp [eichlerPotential, TauCeti.eichlerIntegral, UpperHalfPlane.qExpansion_zero]
  rw [h0, h0, sub_self, mul_zero]
  exact Lat.lattice.zero_mem

/-- The curve `y² = x³ − x` over `ℚ`. -/
def exCurve : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

instance : exCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  simp [exCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **Non-vacuity of the lattice part**: `y² = x³ − x` has a period lattice. PROVED. -/
theorem exists_isLatticeOf_example : ∃ Lat : PeriodPair, IsLatticeOf exCurve Lat :=
  exists_isLatticeOf exCurve

end ZInQ.Contrib.CloudB3RC53.ModularWeil
