import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate5NonVacuity

/-!
# Theorem 5.3, Lane RC32: how far the common-coordinate leaf is from its target

Bridges between `CommonCoordinateInputsL` (`CommonCoordinate5.lean`) and the target
`CommonCoordinateTarget` (`RCSteps.common_coordinate`, (4.7)). All PROVED, standard axioms.

* **Not a cheap collapse of the target.** `commonCoordinateInputsL_not_of_target`: there are data
  with `CommonCoordinateTarget D` and `¬ CommonCoordinateInputsL D` (the empty family is final for
  all data; at its base no graph prime is unused, so the leaf forces `ε = 1`,
  `CommonCoordinateTrianglesL.eq_of_no_unused`, the text's empty product: the relaxed and primitive
  complexes coincide). The leaf also forces the primitive coordinates to be `t`-expansions of
  elements of `F = Frac Λ` (`CommonCoordinateTrianglesL.prim_mem_F`), which the target does not.
* **But, honestly, equivalent to the target plus these two conditions.**
  `commonCoordinateInputsL_iff`: on data whose primitive coordinates come from `F`, the leaf is
  equivalent to (4.7) together with `ε_x = 1` where no graph prime is unused. The local objects are
  the genuine ones; the arithmetic content still sitting in the existential witnesses is the
  support-triangle step itself (the models of each relaxation step are not tied to the actual
  Selmer complexes, which are not in the tree as finite free models over `Λ`).
* **`η_x` may have a pole, so the old carrier is impossible.** If `a_q = 2σ` at an unused `q`
  (`σ = x(ε(F̃r_q))`), `e_q(x)` vanishes at `t = 0` (`constantCoeff_ptFac`); then `e_q(x)⁻¹ ∈ F`
  is not in `Λ_(t)` (`eF_inv_not_regular`), no power series inverts `e_q(x)`
  (`no_powerSeries_inverse`: the old leaf's `hinv` in `ℚ₂[[t]]` cannot hold), and for a family with
  the single graph prime `q` the correction `η_x = l_q/e_q²` itself is not in `Λ_(t)`
  (`etaF_not_regular_single`). For orientation (a finite point count, not formalized here):
  `E_{11}` has `a_{13} = 2` (twelve points over `𝔽_{13}`), and at `x = 0` the sign is `σ = 1`, so
  `e_{13}(0)` vanishes at `t = 0` for every family containing `13`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53

namespace CommonCoordinateTrianglesL

variable {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b}

/-- **Where no graph prime is unused, the leaf forces `ũ_x = u_{prim,x}`** (tex 4221–4227: `η_x`
is the empty product and the relaxed complex is the primitive one). PROVED. -/
theorem eq_of_no_unused (M : CommonCoordinateTrianglesL D Fam x) (h : unusedAt Fam x = ∅) :
    D.uTilde Fam x = D.uPrim Fam x := by
  have h1 : etaF ℓ Fam x = 1 := by rw [etaF_eq, h, Finset.prod_empty]
  have h2 : IsTExpansion (M.u ∅) (D.uTilde Fam x) := by
    have := M.htilde
    rwa [h1, one_mul, h] at this
  exact h2.unique_right M.hprim

/-- The leaf forces the primitive coordinate to be the `t`-expansion of an element of `F`
(PROVED). -/
theorem prim_mem_F (M : CommonCoordinateTrianglesL D Fam x) :
    ∃ u : FracLam, IsTExpansion u (D.uPrim Fam x) :=
  ⟨M.u ∅, M.hprim⟩

end CommonCoordinateTrianglesL

/-! ## The leaf is strictly stronger than the target -/

/-- The empty family (dimension zero, no graph primes) is final for all data (PROVED). -/
theorem finalFamilyAt_witnessFamily {ℓ : ℕ} (D : RCData ℓ) (Co Ce : ℤ) :
    D.FinalFamilyAt Co Ce witnessFamily := by
  refine ⟨fun q hq => absurd hq (Finset.notMem_empty q), fun y hy => absurd ?_ hy⟩
  funext i
  exact absurd i.isLt (Nat.not_lt_zero _)

/-- Data with `u_{prim} = 1` and `ũ = −1` everywhere. -/
def negData (ℓ : ℕ) : RCData ℓ := { constData ℓ with uTilde := fun _ _ => -1 }

/-- `−1 ∈ Λ^×` (PROVED). -/
theorem lamUnit_neg_one : LamUnit (-1 : PowerSeries ℚ_[2]) := ⟨-1, by simp⟩

/-- **The leaf is not implied by the target** (PROVED): `negData` satisfies (4.7) with the
`Λ`-unit `−1`, but not the leaf, which at the base of the empty family forces `ε = 1`. -/
theorem commonCoordinateInputsL_not_of_target :
    ∃ D : RCData 1, CommonCoordinateTarget D ∧ ¬ CommonCoordinateInputsL D := by
  refine ⟨negData 1, fun _ _ _ _ _ => ⟨-1, lamUnit_neg_one, by simp [negData, constData]⟩, ?_⟩
  intro h
  obtain ⟨M⟩ := h 0 0 witnessFamily (finalFamilyAt_witnessFamily _ 0 0) 0
  have hU : unusedAt witnessFamily 0 = ∅ := by rw [unusedAt_zero]; rfl
  have := M.eq_of_no_unused hU
  simp only [negData, constData] at this
  exact neg_one_ne_one_powerSeries this

/-! ## The leaf is (4.7) plus `ε = 1` where nothing is unused -/

/-- **The leaf against the target** (PROVED): on data whose primitive coordinates are
`t`-expansions of elements of `F = Frac Λ`, `CommonCoordinateInputsL D` holds exactly when (4.7)
holds at every address of every final family with `ε_x = 1` where no graph prime is unused. The
genuine local objects (`a_q`, `z`, `e_q`, `l_q`, `η_x`) do not constrain the data further: the
support-triangle steps are realized by models over `F` (`trianglesL_of_eq`). -/
theorem commonCoordinateInputsL_iff {ℓ : ℕ} (D : RCData ℓ)
    (hfrac : ∀ F : Family, ∀ x : Addr F.b, ∃ u : FracLam, IsTExpansion u (D.uPrim F x)) :
    CommonCoordinateInputsL D ↔ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∀ x : Addr F.b, ∃ ε : PowerSeries ℚ_[2], LamUnit ε ∧ D.uTilde F x = ε * D.uPrim F x ∧
        (unusedAt F x = ∅ → D.uTilde F x = D.uPrim F x) := by
  constructor
  · intro h Co Ce F hF x
    obtain ⟨M⟩ := h Co Ce F hF x
    obtain ⟨ε, hε, h47⟩ := M.eq47 (odd_of_finalFamilyAt hF)
    exact ⟨ε, hε, h47, M.eq_of_no_unused⟩
  · intro h Co Ce F hF x
    obtain ⟨ε, ⟨e, rfl⟩, h47, hone⟩ := h Co Ce F hF x
    obtain ⟨u, hu⟩ := hfrac F x
    exact nonempty_trianglesL_of_eq D F x (odd_of_finalFamilyAt hF) u hu e h47 hone

/-! ## `e_q(x)⁻¹` and `η_x` can have a pole at `t = 0` -/

/-- **`e_q(x)(0) = a_q − 2σ`**, `σ = x(ε(F̃r_q))` (PROVED). -/
theorem constantCoeff_ptFac (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    PowerSeries.constantCoeff (ptFac ℓ Fam x q) =
      (apE ℓ q : ℤ_[2]) - 2 * ((frobSign Fam x q : ℤ) : ℤ_[2]) := by
  have h := congrArg (PowerSeries.constantCoeff (R := ℤ_[2])) (one_add_X_mul_ptFac ℓ Fam x q)
  simp only [map_mul, map_add, map_sub, map_one, PowerSeries.constantCoeff_X, add_zero, one_mul,
    map_intCast, map_pow, one_pow, mul_one] at h
  rw [h]
  ring

/-- `e_q(x)` vanishes at `t = 0` when `a_q = 2σ` (PROVED). -/
theorem lambdaEvalZero_ptFac_eq_zero {ℓ : ℕ} {Fam : Family} {x : Addr Fam.b} {q : ℕ}
    (h : apE ℓ q = 2 * (frobSign Fam x q : ℤ)) : lambdaEvalZero (ptFac ℓ Fam x q) = 0 := by
  have h0 : (apE ℓ q : ℤ_[2]) - 2 * ((frobSign Fam x q : ℤ) : ℤ_[2]) = 0 := by
    rw [h]; push_cast; ring
  rw [lambdaEvalZero, RingHom.comp_apply, constantCoeff_ptFac, h0, map_zero]

/-- **No power series inverts `e_q(x)` when `a_q = 2σ`** (PROVED): the constant coefficient of
`e_q(x)` vanishes. This is why the evaluation `χ(e_q) χ(e_q⁻¹) = 1` of the earlier leaf
(`CommonCoordinateTrianglesG.hinv`) cannot hold in `ℚ₂[[t]]` at such a prime (tex 4153–4155,
4229–4231). -/
theorem no_powerSeries_inverse {ℓ : ℕ} {Fam : Family} {x : Addr Fam.b} {q : ℕ}
    (h : apE ℓ q = 2 * (frobSign Fam x q : ℤ)) :
    ¬ ∃ E : PowerSeries ℚ_[2], lamIncl (ptFac ℓ Fam x q) * E = 1 := by
  rintro ⟨E, hE⟩
  have h1 := congrArg (PowerSeries.constantCoeff (R := ℚ_[2])) hE
  rw [map_mul, map_one] at h1
  have h0 : PowerSeries.constantCoeff (lamIncl (ptFac ℓ Fam x q)) = 0 := by
    have := lambdaEvalZero_ptFac_eq_zero h
    rw [lambdaEvalZero, RingHom.comp_apply] at this
    rw [lamIncl, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact this
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

/-- `Λ → Λ_(t) → F` is `Λ → F` (PROVED). -/
theorem algebraMap_lambdaT_algebraMap (f : Lambda) :
    algebraMap Rings.LambdaT FracLam (algebraMap Lambda Rings.LambdaT f) = lamToF f :=
  (IsScalarTower.algebraMap_apply Lambda Rings.LambdaT FracLam f).symm

/-- **`e_q(x)⁻¹` has a pole at `t = 0` when `a_q = 2σ`** (tex 4153–4155, 4229–4231): it is not
the image of an element of `Λ_(t)`. PROVED. -/
theorem eF_inv_not_regular {ℓ : ℕ} {Fam : Family} {x : Addr Fam.b} {q : ℕ}
    (h : apE ℓ q = 2 * (frobSign Fam x q : ℤ)) :
    ¬ ∃ w : Rings.LambdaT, algebraMap Rings.LambdaT FracLam w = (eF ℓ Fam x q)⁻¹ := by
  rintro ⟨w, hw⟩
  have h1 : algebraMap Rings.LambdaT FracLam (algebraMap Lambda Rings.LambdaT (ptFac ℓ Fam x q) * w)
      = algebraMap Rings.LambdaT FracLam 1 := by
    rw [map_mul, hw, algebraMap_lambdaT_algebraMap, map_one]
    exact mul_inv_cancel₀ (eF_ne_zero ℓ Fam x q)
  have h2 := IsFractionRing.injective Rings.LambdaT FracLam h1
  have h3 := congrArg Rings.rhoT h2
  rw [map_mul, map_one, Rings.rhoT_algebraMap, lambdaEvalZero_ptFac_eq_zero h, zero_mul] at h3
  exact zero_ne_one h3

/-- `l_q(x)(0) = (1 − q⁻¹)²` when `a_q = 2σ` (PROVED). -/
theorem constantCoeff_quotFac_of_eq {ℓ : ℕ} {Fam : Family} {x : Addr Fam.b} {q : ℕ}
    (hq : Odd q) (h : apE ℓ q = 2 * (frobSign Fam x q : ℤ)) :
    PowerSeries.constantCoeff (quotFac ℓ Fam x q) = (1 - qInv q) ^ 2 := by
  set σ : ℤ := (frobSign Fam x q : ℤ) with hσdef
  have hσσ : (σ : ℤ_[2]) * (σ : ℤ_[2]) = 1 := by
    rw [hσdef, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hz : PowerSeries.constantCoeff ((zAt Fam x q : Lambdaˣ) : Lambda) = (σ : ℤ_[2]) := by
    simp [zAt, hσdef, frobSign]
  have hzi : PowerSeries.constantCoeff (((zAt Fam x q)⁻¹ : Lambdaˣ) : Lambda) = (σ : ℤ_[2]) := by
    have h1 := congrArg (PowerSeries.constantCoeff (R := ℤ_[2]))
      (Units.mul_inv (zAt Fam x q))
    rw [map_mul, map_one, hz] at h1
    linear_combination (σ : ℤ_[2]) * h1 - (PowerSeries.constantCoeff
      (((zAt Fam x q)⁻¹ : Lambdaˣ) : Lambda)) * hσσ
  have hqq := natCast_mul_qInv hq
  rw [quotFac, map_quotPoly, hz, hzi, map_intCast, map_natCast, PowerSeries.constantCoeff_C, h]
  unfold quotPoly
  push_cast
  set qi := qInv q
  set A : ℤ_[2] := 1 - qi * (σ : ℤ_[2]) * (2 * (σ : ℤ_[2])) + (qi * (σ : ℤ_[2])) ^ 2 * (q : ℤ_[2])
  linear_combination ((qi ^ 2 * (q : ℤ_[2]) - 2 * qi) * (A + 1 - qi)) * hσσ +
    (qi * (A + 1 - qi)) * hqq

/-- **For a family with the single graph prime `q`, unused at `x`, the correction `η_x` has a
pole at `t = 0` when `a_q = 2σ`** (tex 4155, 4229: "The multiplier `η_x` may itself have a pole at
`t = 0`"): `η_x = l_q/e_q²` is not the image of an element of `Λ_(t)`. PROVED. -/
theorem etaF_not_regular_single {ℓ : ℕ} {Fam : Family} {x : Addr Fam.b} {q : ℕ}
    (hQ : Fam.Q = {q}) (hx : Fam.lam q x = 0) (hq : Odd q) (hq1 : q ≠ 1)
    (h : apE ℓ q = 2 * (frobSign Fam x q : ℤ)) :
    ¬ ∃ w : Rings.LambdaT, algebraMap Rings.LambdaT FracLam w = etaF ℓ Fam x := by
  rintro ⟨w, hw⟩
  have hU : unusedAt Fam x = {q} := by
    rw [unusedAt, hQ, Finset.filter_singleton, ite_eq_left hx]
  have heta : etaF ℓ Fam x = lF ℓ Fam x q / eF ℓ Fam x q ^ 2 := by
    rw [etaF_eq, hU, Finset.prod_singleton]
  have he := eF_ne_zero ℓ Fam x q
  have h1 : algebraMap Rings.LambdaT FracLam
      (w * algebraMap Lambda Rings.LambdaT (ptFac ℓ Fam x q) ^ 2) =
      algebraMap Rings.LambdaT FracLam (algebraMap Lambda Rings.LambdaT (quotFac ℓ Fam x q)) := by
    rw [map_mul, map_pow, hw, heta, algebraMap_lambdaT_algebraMap, algebraMap_lambdaT_algebraMap]
    change lF ℓ Fam x q / eF ℓ Fam x q ^ 2 * eF ℓ Fam x q ^ 2 = lF ℓ Fam x q
    field_simp
  have h2 := IsFractionRing.injective Rings.LambdaT FracLam h1
  have h3 := congrArg Rings.rhoT h2
  rw [map_mul, map_pow, Rings.rhoT_algebraMap, Rings.rhoT_algebraMap,
    lambdaEvalZero_ptFac_eq_zero h, lambdaEvalZero, RingHom.comp_apply,
    constantCoeff_quotFac_of_eq hq h] at h3
  have h4 : ((1 - qInv q) ^ 2 : ℤ_[2]) = 0 := by
    have : (PadicInt.Coe.ringHom ((1 - qInv q) ^ 2) : ℚ_[2]) = 0 := by
      rw [← h3]; ring
    exact PadicInt.coe_eq_zero.mp this
  have h5 : qInv q = 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
    linear_combination -this
  have h6 := natCast_mul_qInv hq
  rw [h5, mul_one] at h6
  exact hq1 (by exact_mod_cast h6)

end ZInQ.Manuscript.RC.Wiring
