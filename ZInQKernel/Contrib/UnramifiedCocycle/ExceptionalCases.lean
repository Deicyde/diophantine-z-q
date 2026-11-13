import ZInQKernel.Contrib.UnramifiedCocycle.FiniteQuotient

/-!
# Exceptional and adverse cases for cyclic inflation

The identity quotient, an unnormalized constant sign cocycle, and a genuinely
nontrivial cocycle on `C_2` are checked.  The latter is not a coboundary before
doubling, so the construction does not make the original cocycles trivial by
definition.  A trivial actual finite local action is also handled directly.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2 GlueDescent.B2Q

/-- The order-one quotient is covered without deleting the identity case. -/
theorem signCob_cyclicDouble_one
    (ε : CyclicGroup 1 → CyclicGroup 1 → ℂˣ) (hε : IsSignCocycle ε) :
    SignCob (pull (cyclicReduction 1) ε) := signCob_cyclicDouble 1 ε hε

/-- A valid cocycle need not have value `1` at the identity. -/
theorem constantMinusOne_isSignCocycle (n : ℕ) :
    IsSignCocycle (fun _ _ : CyclicGroup n => (-1 : ℂˣ)) := by
  refine ⟨IsLocallyConstant.const _, ?_, ?_⟩
  · intro x y; simp
  · intro x y z; rfl

/-- Restoring the normalization constant is necessary, not cosmetic. -/
theorem constantMinusOne_cochain (n : ℕ) (x : CyclicGroup (2 * n)) :
    doubledCochain n (fun _ _ : CyclicGroup n => (-1 : ℂˣ)) x = -1 := by
  simp [doubledCochain, powerCochain, normalize]

/-- The carry cocycle on `C_2`: the lift of its generator has order four. -/
def orderTwoCarry (x y : CyclicGroup 2) : ℂˣ :=
  if x.toAdd.val = 1 ∧ y.toAdd.val = 1 then -1 else 1

/-- Exhaustive two-element case coverage in actual residue coordinates. -/
theorem cyclicTwo_cases (x : CyclicGroup 2) : x = 1 ∨ x = cyclicGenerator 2 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h x.toAdd with h0 | h1
  · left
    apply Multiplicative.toAdd.injective
    change x.toAdd = 0
    exact h0
  · right
    apply Multiplicative.toAdd.injective
    change x.toAdd = 1
    exact h1

theorem orderTwoCarry_isSignCocycle : IsSignCocycle orderTwoCarry := by
  refine ⟨IsLocallyConstant.of_discrete _, ?_, ?_⟩
  · intro x y
    unfold orderTwoCarry
    split_ifs <;> simp
  · intro x y z
    have hg : cyclicGenerator 2 * cyclicGenerator 2 = 1 := by
      simpa only [pow_two] using cyclicGenerator_pow_order 2
    have hgv : (cyclicGenerator 2).toAdd.val = 1 := by
      norm_num [cyclicGenerator, ZMod.val_one_eq_one_mod]
    rcases cyclicTwo_cases x with rfl | rfl <;>
      rcases cyclicTwo_cases y with rfl | rfl <;>
      rcases cyclicTwo_cases z with rfl | rfl <;>
      simp [orderTwoCarry, hg, hgv]

/-- This original `C_2` cocycle is genuinely nontrivial with sign coefficients. -/
theorem orderTwoCarry_not_signCob : ¬ SignCob orderTwoCarry := by
  rintro ⟨b, _, hs, he⟩
  let g := cyclicGenerator 2
  have hg : g * g = 1 := by
    simpa only [g, pow_two] using cyclicGenerator_pow_order 2
  have hgv : g.toAdd.val = 1 := by norm_num [g, cyclicGenerator, ZMod.val_one_eq_one_mod]
  have hb : b 1 = 1 := by
    simpa [orderTwoCarry, dB] using (he 1 1).symm
  have h := he g g
  simp only [orderTwoCarry, hgv, and_self, ite_true, dB, hg, hb, inv_one, mul_one] at h
  have hbad : (-1 : ℂˣ) = 1 := h.trans ((pow_two (b g)).symm.trans (hs g))
  have hcomplex := congrArg (fun u : ℂˣ => (u : ℂ)) hbad
  norm_num at hcomplex

/-- Doubling actually removes this obstruction. -/
theorem orderTwoCarry_double_signCob : SignCob (pull (cyclicReduction 2) orderTwoCarry) :=
  signCob_cyclicDouble 2 orderTwoCarry orderTwoCarry_isSignCocycle

/-- The explicit witness for the adverse carry example is `(-1)^(floor(k/2))`
in the canonical residue coordinate `k` on `C_4`. -/
theorem orderTwoCarry_cochain (x : CyclicGroup 4) :
    doubledCochain 2 orderTwoCarry x = (-1 : ℂˣ) ^ (x.toAdd.val / 2) := by
  have hg : cyclicGenerator 2 * cyclicGenerator 2 = 1 := by
    simpa only [pow_two] using cyclicGenerator_pow_order 2
  have hgv : (cyclicGenerator 2).toAdd.val = 1 := by
    norm_num [cyclicGenerator, ZMod.val_one_eq_one_mod]
  have hcases : ∀ a : ZMod 4, a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 := by decide
  rcases hcases x.toAdd with hx | hx | hx | hx <;>
    simp [doubledCochain, hx, powerCochain_succ, normalize, orderTwoCarry, hg, hgv, pow_two]

/-- If the actual finite local action is trivial, the actual local cocycle is
already the coboundary of a constant sign cochain. -/
theorem signCob_of_localRestriction_eq_one
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (p : Nat.Primes) (htrivial : localRestriction L p = 1)
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hi : InflatedFrom L ε) :
    SignCob (pull (resp p) ε) := by
  have hfinite := finiteCocycle_isSignCocycle L ε hε hi
  refine ⟨fun _ => finiteCocycle L ε 1 1, IsLocallyConstant.const _,
    fun _ => hfinite.2.1 1 1, ?_⟩
  intro x y
  have hx : finiteRestriction L (resp p x) = 1 := congrArg (fun f => f x) htrivial
  have hy : finiteRestriction L (resp p y) = 1 := congrArg (fun f => f y) htrivial
  change ε (resp p x) (resp p y) =
    finiteCocycle L ε 1 1 * finiteCocycle L ε 1 1 * (finiteCocycle L ε 1 1)⁻¹
  rw [← finiteCocycle_apply L ε hi, hx, hy]
  simp

/-- The degree-one number field case is discharged over the actual absolute
Galois groups, for every finite prime, not merely on an abstract cyclic group. -/
theorem signCob_inflatedFrom_bot (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε)
    (hi : InflatedFrom (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) ε) (p : Nat.Primes) :
    SignCob (pull (resp p) ε) := by
  have he : ∀ σ τ : GQ, ε σ τ = ε 1 1 := by
    intro σ τ
    apply hi σ 1 τ 1
    · intro x hx
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hx
      rw [← hq]
      change (act σ) (algebraMap ℚ (AlgebraicClosure ℚ) q) =
        algebraMap ℚ (AlgebraicClosure ℚ) q
      exact (act σ).commutes q
    · intro x hx
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hx
      rw [← hq]
      change (act τ) (algebraMap ℚ (AlgebraicClosure ℚ) q) =
        algebraMap ℚ (AlgebraicClosure ℚ) q
      exact (act τ).commutes q
  refine ⟨fun _ => ε 1 1, IsLocallyConstant.const _, fun _ => hε.2.1 1 1, ?_⟩
  intro x y
  change ε (resp p x) (resp p y) = ε 1 1 * ε 1 1 * (ε 1 1)⁻¹
  rw [he]
  simp

end ZInQ.Contrib.UnramifiedCocycle
