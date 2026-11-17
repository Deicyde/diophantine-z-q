import ZInQKernel.Contrib.OneProof.SGA7IX35ForwardAC

/-!
# sga735-finish: SGA 7 IX 3.5 in the form "semistable ⇒ unipotent" (no echelon clause)

Task sga735-finish (docs/research/sga735-finish.md). The research field
`sga7_IX_3_5_ForwardGeom : UnipotentForward.SGA7_IX_3_5_ForwardGeom` concludes `(σ - 1)² = 0` on `T_ℓ`: the
"echelon ≤ 2" clause, which is printed in SGA 7 IX 3.5 only under one reading (reading (b) of its kinds.tsv flag).
sga735-narrow removed the other pending reading (the `k(s)` reading) by restricting to algebraically closed residue
fields (`SGA735AC.SGA7_IX_3_5_ForwardGeomAC`). This file removes the echelon clause as well:

* `SGA7_IX_3_5_ForwardUnipAC` is the restricted leaf with the conclusion `IsNilpotent (σ - 1)` on `T_ℓ`
  ("I opère unipotentement"), the direction semistable ⇒ unipotent that 3.5 prints under every reading. It is a
  specialization of the field and of sga735-narrow's leaf (`forwardUnipAC_of_forwardGeomAC`).
* `SemistableUnipotentNilCP` (the chain's `ReductSplit.SemistableUnipotent`, perfect residue field, conclusion
  nilpotent) is proved from it and the two bundle leaves of the old proof, as in sga735-narrow.
* `RaynaudCriterionNFNil` is r6 at number fields (`GapNeron.RaynaudCriterionNF`) with the conclusion
  "`σ - 1` is nilpotent on `A[ℓ^∞]` with one exponent for all levels"; it is proved from `SemistableUnipotentNilCP`
  (`raynaudCriterion_leavesNF_nil`). Every square-zero r6 gives it (`raynaudCriterionNFNil_of_sq`).
* The two algebraic cores the readers of r6 need are proved for nilpotent `σ - 1`:
  `fixed_of_nil_of_iterate` (wild `σ` with a period prime to `ℓ`), and `nilQuat_trivial` (the `ℓ = 3` quaternion
  consumer, by repeated halving of the exponent through the existing `PkgI2.quatUnipotentTrivial`).

No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction Pts torsion galAct UnipSq)
open ReductSplit ReductGlue ZInQ.HeightSplit

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SGA735Nil

/-! ## §1. Group theory: the difference operator `x ↦ f x · x⁻¹` -/

section Algebra

variable {G : Type*} [CommGroup G]

/-- The difference operator `D_f x = f x · x⁻¹` of an endomorphism `f` of a commutative group (`f - 1` written
multiplicatively), as an endomorphism. -/
def diffHom (f : G →* G) : G →* G where
  toFun x := f x * x⁻¹
  map_one' := by simp
  map_mul' x y := by rw [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _

@[simp] theorem diffHom_apply (f : G →* G) (x : G) : diffHom f x = f x * x⁻¹ := rfl

theorem diffHom_comm (f : G →* G) (x : G) : diffHom f (f x) = f (diffHom f x) := by
  simp [map_mul, map_inv]

theorem diffHom_iterate_comm (f : G →* G) (j : ℕ) (x : G) :
    (diffHom f)^[j] (f x) = f ((diffHom f)^[j] x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, diffHom_comm, ih]

theorem iterate_diffHom_comm (f : G →* G) (q j : ℕ) (x : G) :
    f^[q] ((diffHom f)^[j] x) = (diffHom f)^[j] (f^[q] x) := by
  induction q generalizing x with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, diffHom_iterate_comm]

theorem diffHom_iterate_pow (f : G →* G) (j m : ℕ) (x : G) :
    (diffHom f)^[j] (x ^ m) = ((diffHom f)^[j] x) ^ m := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_pow]

/-- The square-zero core (pkg-I2's `fixed_of_unipSq_of_iterate`, for an arbitrary endomorphism): if
`(f - 1)² x = 0`, `x^m = 1` and `f^q x = x` with `q` prime to `m`, then `f x = x`. -/
theorem fixed_of_sq_of_iterate (f : G →* G) (x : G) (m q : ℕ) (hcop : Nat.Coprime q m)
    (hx : x ^ m = 1) (hu : diffHom f (diffHom f x) = 1) (hit : f^[q] x = x) : f x = x := by
  set N := diffHom f x with hN
  have hσN : f N = N := by
    have := hu
    rw [diffHom_apply] at this
    exact mul_inv_eq_one.mp this
  have hiter : ∀ k : ℕ, f^[k] x = N ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hσN, pow_succ]
      have : f x = N * x := by rw [hN, diffHom_apply]; group
      rw [this]; group
  have h1 : N ^ q = 1 := by
    have := hiter q
    rw [hit] at this
    exact (mul_eq_right.mp this.symm)
  have h2 : N ^ m = 1 := by
    rw [hN, diffHom_apply, mul_pow, ← map_pow, hx, map_one, inv_pow, hx, inv_one, _root_.mul_one]
  have hN1 : N = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN, diffHom_apply] at hN1
  exact mul_inv_eq_one.mp hN1

/-- **The nilpotent core**: if `(f - 1)^N x = 0`, `x^m = 1` and `f^q x = x` with `q` prime to `m`, then
`f x = x`. (Downward induction on `N` with `fixed_of_sq_of_iterate` applied to `(f - 1)^{j-1} x`.) -/
theorem fixed_of_nil_of_iterate (f : G →* G) (x : G) (m q N : ℕ) (hcop : Nat.Coprime q m)
    (hx : x ^ m = 1) (hN : (diffHom f)^[N] x = 1) (hit : f^[q] x = x) : f x = x := by
  have step : ∀ j : ℕ, (diffHom f)^[j + 2] x = 1 → (diffHom f)^[j + 1] x = 1 := by
    intro j hj
    have hz := fixed_of_sq_of_iterate f ((diffHom f)^[j] x) m q hcop
      (by rw [← diffHom_iterate_pow, hx, iterate_map_one])
      (by
        rw [← Function.iterate_succ_apply' (diffHom f), ← Function.iterate_succ_apply' (diffHom f)]
        exact hj)
      (by rw [iterate_diffHom_comm, hit])
    rw [Function.iterate_succ_apply', diffHom_apply, hz, mul_inv_cancel]
  have down : ∀ k : ℕ, ∀ j : ℕ, (diffHom f)^[j + 1 + k] x = 1 → (diffHom f)^[j + 1] x = 1 := by
    intro k
    induction k with
    | zero => intro j h; simpa using h
    | succ k ih =>
      intro j h
      have h' : (diffHom f)^[(j + k) + 2] x = 1 := by
        rw [show j + k + 2 = j + 1 + (k + 1) by omega]; exact h
      have := step (j + k) h'
      exact ih j (by rw [show j + 1 + k = j + k + 1 by omega]; exact this)
  rcases N with _ | N
  · simp at hN; rw [hN, map_one]
  · have h1 := down N 0 (by rw [show 0 + 1 + N = N + 1 by omega]; exact hN)
    simp only [zero_add, Function.iterate_one, diffHom_apply] at h1
    exact mul_inv_eq_one.mp h1

theorem diffHom_iterate_add (f : G →* G) (a b : ℕ) (x : G) :
    (diffHom f)^[a + b] x = (diffHom f)^[a] ((diffHom f)^[b] x) := by
  rw [Function.iterate_add_apply]

/-- `(f - 1)^N x = 1` gives `(f - 1)^M x = 1` for `M ≥ N`. -/
theorem diffHom_iterate_of_le (f : G →* G) {N M : ℕ} (hNM : N ≤ M) (x : G)
    (h : (diffHom f)^[N] x = 1) : (diffHom f)^[M] x = 1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  rw [add_comm, diffHom_iterate_add, h, iterate_map_one]

/-- `(f - 1)^j` as an endomorphism. -/
def diffPow (f : G →* G) : ℕ → (G →* G)
  | 0 => MonoidHom.id G
  | j + 1 => (diffHom f).comp (diffPow f j)

theorem diffPow_apply (f : G →* G) (j : ℕ) (x : G) : diffPow f j x = (diffHom f)^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [diffPow, MonoidHom.comp_apply, ih, Function.iterate_succ_apply']

/-- `1 + T` for an endomorphism `T`: `x ↦ x · T x`. -/
def onePlus (T : G →* G) : G →* G where
  toFun x := x * T x
  map_one' := by simp
  map_mul' x y := by rw [map_mul]; exact mul_mul_mul_comm _ _ _ _

end Algebra


/-! ## §2. Transport of nilpotence along linear maps -/

section Lin

variable {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

theorem pow_sub_one_comm (φ : M₁ →ₗ[R] M₂) (f₁ : Module.End R M₁) (f : Module.End R M₂)
    (h : ∀ s, φ (f₁ s) = f (φ s)) (N : ℕ) (s : M₁) :
    φ (((f₁ - 1) ^ N) s) = ((f - 1) ^ N) (φ s) := by
  induction N generalizing s with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ih]
    simp [h]

/-- Nilpotence of `f₁ - 1` passes to `f - 1` along a surjective intertwiner. -/
theorem isNilpotent_sub_one_of_surj (φ : M₁ →ₗ[R] M₂) (hφ : Function.Surjective φ)
    (f₁ : Module.End R M₁) (f : Module.End R M₂) (h : ∀ s, φ (f₁ s) = f (φ s))
    (hn : IsNilpotent (f₁ - 1)) : IsNilpotent (f - 1) := by
  obtain ⟨N, hN⟩ := hn
  refine ⟨N, LinearMap.ext fun t => ?_⟩
  obtain ⟨s, rfl⟩ := hφ t
  rw [← pow_sub_one_comm φ f₁ f h, hN, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

end Lin

/-! ## §3. The leaf -/

/-- **LEAF `SGA7_IX_3_5_ForwardUnipAC`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5, the direction
"semistable ⇒ `I` acts unipotently on `T_ℓ`"; number and wording UNVERIFIED), over a strictly henselian discrete
valuation ring with algebraically closed residue field. This is sga735-narrow's `SGA735AC.SGA7_IX_3_5_ForwardGeomAC`
(the field `UnipotentForward.SGA7_IX_3_5_ForwardGeom` with `[IsAlgClosed k(s)]` added) with the conclusion
`(σ - 1)² = 0` weakened to `σ - 1` nilpotent: `O` strictly henselian with `k(s)` algebraically closed, `Ω = K^s`,
`w` over `O`, `ℓ` invertible in `O`; if `A` has semistable reduction at `O`, every `σ` in the inertia group acts
unipotently on `T_ℓ(A) = lim A(K^s)[ℓⁿ]`. No echelon clause is assumed. -/
def SGA7_IX_3_5_ForwardUnipAC : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAlgClosed (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → HasSemistableReduction A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsNilpotent (galTΩ A ℓ σ - 1)

/-- The new leaf is a specialization of sga735-narrow's restricted leaf (never stronger). -/
theorem forwardUnipAC_of_forwardGeomAC (h : SGA735AC.SGA7_IX_3_5_ForwardGeomAC) :
    SGA7_IX_3_5_ForwardUnipAC :=
  fun K _ O _ _ hO Ω _ _ _ w hw A ℓ _ hℓ hA σ hσ =>
    ⟨2, by rw [pow_two]; exact h K O hO Ω w hw A ℓ hℓ hA σ hσ⟩

/-- The new leaf is a specialization of the field `UnipotentForward.SGA7_IX_3_5_ForwardGeom` (never stronger). -/
theorem forwardUnipAC_of_forwardGeom (h : UnipotentForward.SGA7_IX_3_5_ForwardGeom) :
    SGA7_IX_3_5_ForwardUnipAC :=
  forwardUnipAC_of_forwardGeomAC (SGA735AC.forwardGeomAC_of_forwardGeom h)

/-- The new leaf follows from the `k(s)` reading of the echelon form as well. -/
theorem forwardUnipAC_of_forwardRes (h : SGA735AC.SGA7_IX_3_5_ForwardRes) : SGA7_IX_3_5_ForwardUnipAC :=
  forwardUnipAC_of_forwardGeomAC (SGA735AC.forwardGeomAC_of_forwardRes h)

/-! ## §4. `SemistableUnipotentNilCP` -/

/-- `ReductSplit.SemistableUnipotent` with `[PerfectField k(s)]` added and the conclusion `σ - 1` nilpotent on
`T_ℓ` (sga735-narrow's `SGA735AC.SemistableUnipotentCP` without the echelon clause). -/
def SemistableUnipotentNilCP : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      IsNilpotent (galTΩ A ℓ σ - 1)

/-- `SemistableUnipotentSHAC` (sga735-narrow) without the echelon clause. -/
def SemistableUnipotentNilSHAC : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAlgClosed (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      IsNilpotent (galTΩ A ℓ σ - 1)

/-- From `K^s` to an algebraic closure (sga735-narrow's `semistableUnipotentSHAC_of_forwardGeomAC`, nilpotent). -/
theorem semistableUnipotentNilSHAC_of_forwardUnipAC (hP : SGA7_IX_3_5_ForwardUnipAC)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : SemistableUnipotentNilSHAC := by
  intro K _ O _ _ hO Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isUnit O hℓ
  obtain ⟨σs, hσs, φ, hφ, hcomm⟩ := UnipotentForward.sepClosure_tate hE K Ω w A ℓ hℓK σ hσ
  have hws : (w.comap (algebraMap (separableClosure K Ω) Ω)).comap
      (algebraMap K (separableClosure K Ω)) = O := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw]
  have key := hP K O hO (separableClosure K Ω) _ hws A ℓ hℓ hA σs hσs
  exact isNilpotent_sub_one_of_surj φ hφ _ _ hcomm key

/-- **`SemistableUnipotentNilCP` from the nilpotent SH form** (sga735-narrow's `semistableUnipotentCP_of_SHAC`,
nilpotent): apply it to `A_E` over the inertia field `E` of `w`. -/
theorem semistableUnipotentNilCP_of_SHAC (hIn : StrictHenselizationInside) (hSH : SemistableUnipotentNilSHAC) :
    SemistableUnipotentNilCP := by
  intro K _ O _ _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ
  obtain ⟨E, hE, hSHPall, hfix⟩ := hIn K O Ω w hw
  haveI : PerfectField (IsLocalRing.ResidueField (w.comap (algebraMap E Ω))) :=
    SGA735AC.perfectField_of_isSHNeronExt hSHPall
  obtain ⟨hSHP, halg, hbc⟩ := hSHPall
  haveI : IsDiscreteValuationRing (w.comap (algebraMap E Ω)) := hSHP.1
  haveI : IsSepClosed (IsLocalRing.ResidueField (w.comap (algebraMap E Ω))) := hSHP.2.2
  haveI : IsAlgClosed (IsLocalRing.ResidueField (w.comap (algebraMap E Ω))) :=
    IsSepClosed.isAlgClosed_of_perfectField _
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) E⟩
  have hAE : HasSemistableReduction (A.baseChange E) (w.comap (algebraMap E Ω)) := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hE 𝒩, hbc A 𝒩 h𝒩, (isSemistable_bcDVR_iff hE halg 𝒩).mp hs⟩
  have hℓP : IsUnit (ℓ : w.comap (algebraMap E Ω)) := by
    have := hℓ.map (comapHom hE)
    rwa [map_natCast] at this
  let σ₁ := toE E σ (hfix σ hσ)
  have hσ₁ : IsInertia w σ₁ := isInertia_toE E w σ (hfix σ hσ) hσ
  let φ : TΩ (A.baseChange E) Ω ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (ZInQ.Contrib.AbVarBC.bcPt A Ω).toMonoidHom)
  let ψ : TΩ A Ω ℓ →ₗ[ℤ_[ℓ]] TΩ (A.baseChange E) Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (ZInQ.Contrib.AbVarBC.bcPt A Ω).symm.toMonoidHom)
  have hφψ : ∀ t, φ (ψ t) = t := by
    intro t
    apply Subtype.ext
    funext n
    change Additive.ofMul (ZInQ.Contrib.AbVarBC.bcPt A Ω
      ((ZInQ.Contrib.AbVarBC.bcPt A Ω).symm (Additive.toMul (t.1 n)))) = t.1 n
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcomm : ∀ s, φ (galTΩ (A.baseChange E) ℓ σ₁ s) = galTΩ A ℓ σ (φ s) := by
    intro s
    apply Subtype.ext
    funext n
    change Additive.ofMul (ZInQ.Contrib.AbVarBC.bcPt A Ω ((A.baseChange E).galAct σ₁ (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (ZInQ.Contrib.AbVarBC.bcPt A Ω (Additive.toMul (s.1 n))))
    rw [ZInQ.Contrib.AbVarBC.bcPt_galAct, toE_restrictScalars]
  have key := hSH E (w.comap (algebraMap E Ω)) hSHP Ω w rfl (A.baseChange E) hAE ℓ hℓP σ₁ hσ₁
  exact isNilpotent_sub_one_of_surj φ (fun t => ⟨ψ t, hφψ t⟩) _ _ hcomm key

/-- **`SemistableUnipotentNilCP` from the new leaf and the two bundle leaves of the old proof**
(`MulEtaleAbelianScheme`, `NeronBaseChangeStrictHenselization`). -/
theorem semistableUnipotentNilCP_of_forwardUnipAC (hP : SGA7_IX_3_5_ForwardUnipAC)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : GapSHPair.NeronBaseChangeStrictHenselization) :
    SemistableUnipotentNilCP :=
  semistableUnipotentNilCP_of_SHAC (UnipotentForward.strictHenselizationInside_of_neron hN)
    (semistableUnipotentNilSHAC_of_forwardUnipAC hP hE)

/-! ## §5. r6 at number fields, nilpotent form -/

/-- **r6 at number fields, nilpotent form** (glue statement; proved below from the leaves): `GapNeron.RaynaudCriterionNF`
with the conclusion "`(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every `n`" replaced by "`(σ - 1)^N = 0` on `A(K̄)[ℓⁿ]` for every
`n`, with one `N`". -/
def RaynaudCriterionNFNil : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ), 3 ≤ m → IsUnit (m : O) →
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
        ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
          ∃ N : ℕ, ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n),
            (fun y => galAct A σ y * y⁻¹)^[N] x = 1

/-- Square-zero r6 gives the nilpotent form (`N = 2`). -/
theorem raynaudCriterionNFNil_of_sq (h : GapNeron.RaynaudCriterionNF) : RaynaudCriterionNFNil := by
  intro K _ _ O _ w hw A _ m hm hmO hrat σ hσ ℓ hℓ hℓO
  refine ⟨2, fun n x hx => ?_⟩
  have h2 := h K O w hw A m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx
  simp only [UnipSq] at h2
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  have : IsProper A.X.hom := IsAbelianVariety.proper
  have : GeometricallyIntegral A.X.hom := IsAbelianVariety.geomIntegral
  have : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  rw [← h2, PkgI2.galAct_mul, PkgI2.galAct_inv, mul_inv, inv_inv, ← _root_.mul_assoc]

/-- The same for the kernel-universe form `HDec.PkgI2.RaynaudCriterionNF.{0}`. -/
theorem raynaudCriterionNFNil_of_sq' (h : HDec.PkgI2.RaynaudCriterionNF.{0}) : RaynaudCriterionNFNil :=
  raynaudCriterionNFNil_of_sq h

/-- `((σ - 1)^N t)_n = (σ - 1)^N (t_n)` on the Tate module. -/
theorem tate_iter {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (B : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Ω ≃ₐ[K] Ω) (t : TΩ B Ω ℓ) (n N : ℕ) :
    (((galTΩ B ℓ σ - 1) ^ N) t).1 n =
      Additive.ofMul ((fun y => B.galAct σ y * y⁻¹)^[N] (Additive.toMul (t.1 n))) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
    have ih' : (fun y => B.galAct σ y * y⁻¹)^[N] (Additive.toMul (t.1 n)) =
        Additive.toMul ((((galTΩ B ℓ σ - 1) ^ N) t).1 n) := by rw [ih]; rfl
    rw [ih']
    generalize ((galTΩ B ℓ σ - 1) ^ N) t = s
    show (galTΩ B ℓ σ s).1 n - s.1 n = _
    rw [show (galTΩ B ℓ σ s).1 n = Additive.ofMul (B.galAct σ (Additive.toMul (s.1 n))) from rfl,
      ofMul_mul, ofMul_inv, sub_eq_add_neg]
    rfl

/-- **r6 at number fields, nilpotent form, from the leaves**: neron-dvr's `GapNeron.raynaudCriterion_of_leavesNF`
(as in sga735-narrow's `raynaudCriterion_of_leavesNF_cp`) with `hU : SemistableUnipotentNilCP`. -/
theorem raynaudCriterion_of_leavesNF_nil (hR : RaynaudSemistable) (hU : SemistableUnipotentNilCP)
    (hN : GapNeron.NeronSchemeModelExistsDVRNF) (hT : PkgI2.TorsionStructure.{0})
    (hF : FixedTorsionRational) : RaynaudCriterionNFNil := by
  intro K _ _ O _ w hw A _ m hm hmO hrat σ hσ ℓ hℓ hℓO
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : PerfectField (IsLocalRing.ResidueField O) := SGA735AC.perfectField_residue_nf O
  let B := ObjBridge.ofGrp A
  have hss : SemistableNeronModels B O :=
    hR K O B m hm hmO (hF K B m (natCast_ne_zero_of_isUnit O hmO) (fun σ x hx => hrat σ x hx))
  obtain ⟨N, hN0⟩ :=
    hU K O (AlgebraicClosure K) w hw B (GapNeron.hasSemistableReduction_ofNF hN O B hss) ℓ hℓO σ hσ
  refine ⟨N, fun n x hx => ?_⟩
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  have h0 : ((galTΩ B ℓ σ - 1) ^ N) t = 0 := by rw [hN0]; rfl
  have h := tate_iter B ℓ σ t n N
  rw [h0, ht] at h
  exact (congrArg Additive.toMul h).symm

/-- **r6 at number fields, nilpotent form** (the `raynaudCriterion_leavesNF` interface). -/
theorem raynaudCriterion_leavesNF_nil (hR : RaynaudSemistable) (hU : SemistableUnipotentNilCP)
    (hN : GapNeron.NeronSchemeModelExistsDVRNF) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudCriterionNFNil :=
  raynaudCriterion_of_leavesNF_nil hR hU hN (AvSplit.torsionStructure_of_mumford hM)
    (ReductGlue.fixedTorsionRational_of_mulEtale hE)

/-- Everything at once: the nilpotent r6 from the new leaf. -/
theorem raynaudCriterionNFNil_of_forwardUnipAC (hR : RaynaudSemistable) (hP : SGA7_IX_3_5_ForwardUnipAC)
    (hNbc : GapSHPair.NeronBaseChangeStrictHenselization) (hN : GapNeron.NeronSchemeModelExistsDVRNF)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    RaynaudCriterionNFNil :=
  raynaudCriterion_leavesNF_nil hR (semistableUnipotentNilCP_of_forwardUnipAC hP hE hNbc) hN hM hE

end SGA735Nil

end
