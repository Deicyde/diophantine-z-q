
/-! ### G12's determinant identities (`G12Det`), split into R14's determinant clause, `DetTate`
and `ResQFiniteIndex` -/

section G0GaloisDetSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- `σ ↦ σ` as ring automorphisms of `ℚ̄`. -/
def toRingEquivQ : PkgI4.GQ →* (PkgI4.Qbar ≃+* PkgI4.Qbar) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The `ℓ`-adic cyclotomic character `χ_ℓ : G_ℚ → ℤ_ℓ^× ⊆ ℚ̄_ℓ^×` (Mathlib's
`cyclotomicCharacter` on `ℚ̄`, as `PkgI4.cyc` on `G_{ℚ_p}`). -/
def cycQ (ℓ : ℕ) [Fact ℓ.Prime] : PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
  (Units.map ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter PkgI4.Qbar ℓ).comp toRingEquivQ)

/-- **R14 with its published determinant clause (leaf; Shimura 1971 Thm 7.14 for `k = 2`,
Deligne 1971 for `k ≥ 2`, Deligne–Serre 1974 for `k = 1`; locators UNVERIFIED).** For a normalized
eigenform `g` of weight `k ≥ 1` with nebentypus, there is a semisimple `ρ_g` attached to `g` with
`det ρ_g = ε · χ_ℓ^{k−1}`, `ε` of finite image (the nebentypus as a Galois character). This is
`HSyn.EigenformRepExists` plus the determinant, which the published statements contain. -/
def R14Det : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k),
    0 < N → 1 ≤ k → PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g ∧
      ∃ ε : PkgI4.GQ →* (PadicAlgCl ℓ)ˣ, (Set.range ε).Finite ∧
        ∀ σ, (ρ.mat σ).det = ((ε σ * cycQ ℓ σ ^ (k - 1) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)

/-- **`det V_ℓ(A) = χ_ℓ^{dim A}` (GLUE, unproved; from T9, the Weil pairing of a polarization:
`G_K` acts on `V_ℓ(A)` through `GSp_{2g}` with multiplier `χ_ℓ`, Mumford §20, §23, STANDARD).** -/
def DetTate : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ),
    A.dim = g → ∀ σ, LinearMap.det (tate A ℓ σ) = ((cycQ ℓ (resQ K σ) : PadicAlgCl ℓ)) ^ g

/-- **`G_K` has finite index in `G_ℚ` (GLUE, unproved; Galois theory: the index is `[K:ℚ]`).** -/
def ResQFiniteIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], (resQ K).range.FiniteIndex

/-- **Chebotarev density, PkgI4 form** (copied verbatim from scratch/c9-rhof, where it is
`HSyn.FrobeniusDense` with pkg-I4's `LiesOver`, `IsArithFrob`; leaf T18). -/
def FrobeniusDenseQ : Prop :=
  ∀ (U : Subgroup PkgI4.GQ), IsOpen (U : Set PkgI4.GQ) → ∀ (σ : PkgI4.GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
      PkgI4.LiesOver v p ∧ PkgI4.IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-- The bundle's T18 is `FrobeniusDenseQ` (the two `LiesOver`, `IsArithFrob` have equal bodies). -/
theorem frobeniusDenseQ_of (h : HSyn.FrobeniusDense) : FrobeniusDenseQ := h

/-- (copied from scratch/c9-rhof, proved there from T18) Continuous functions agreeing at
arithmetic Frobenius elements outside `S` are equal. -/
theorem eq_of_eq_on_arithFrob (hD : FrobeniusDenseQ) {X : Type*} [TopologicalSpace X]
    [T2Space X] (S : Finset ℕ) (f₁ f₂ : PkgI4.GQ → X) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hfr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
      PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → f₁ τ = f₂ τ) : f₁ = f₂ := by
  funext g
  by_contra hne
  have hopen : IsOpen {x | f₁ x ≠ f₂ x} := isOpen_ne_fun h₁ h₂
  have hmem : (fun y => g * y) ⁻¹' {x | f₁ x ≠ f₂ x} ∈ nhds (1 : PkgI4.GQ) := by
    apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using hne
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ PkgI4.Qbar _).mp hmem
  have hU : IsOpen (E.fixingSubgroup : Set PkgI4.GQ) := IntermediateField.fixingSubgroup_isOpen E
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := hD E.fixingSubgroup hU g S
  have hfix : g⁻¹ * τ ∈ E.fixingSubgroup := by
    have := E.fixingSubgroup.inv_mem hU'
    simpa using this
  have := hsub hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_ofPred_eq] at this
  exact this (hfr p hp hpS v τ hv hτ)

/-- `det M = (tr(M)² − tr(M²))/2` for `2 × 2` matrices in characteristic `0`. -/
theorem det_fin_two_eq_trace {R : Type*} [Field R] [CharZero R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.det = ((M.trace) ^ 2 - (M * M).trace) / 2 := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

theorem continuous_mat {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r : GaloisRep ℓ n) :
    Continuous fun x => r.mat x :=
  Units.continuous_val.comp r.continuous_toHom

/-- **`G12Det` (proved from R14Det, DetTate, ResQFiniteIndex and T18).** `det r = det(ρ_g ⊗ ψ)`
everywhere (traces agree at Frobenius, hence everywhere by T18; then the `2 × 2` identity), and
`(det r)² = det V₅(A) = χ₅²` on `G_K` (through `e`, `LinearMap.det_conj`, `det_prodMap`). -/
theorem g12Det_of (hR : R14Det) (hDT : DetTate) (hFI : ResQFiniteIndex)
    (hD : FrobeniusDenseQ) : G12Det := by
  intro _ _ K _ _ A r e N χ g ψ ιC ιL S hdim hint hN hg hatt
  obtain ⟨ρ, -, hρatt, ε, hεfin, hdet⟩ := hR 5 ιC ιL N 2 χ g hN (by norm_num) hg
  -- traces of `r` and `ψ ⊗ ρ_g` agree
  have hN5 : N * 5 ≠ 0 := by positivity
  have htr : ∀ x, (r.mat x).trace = (ψ.toHom x : PadicAlgCl 5) * (ρ.mat x).trace := by
    have h := eq_of_eq_on_arithFrob hD (S ∪ (N * 5).primeFactors) (fun x => (r.mat x).trace)
      (fun x => (ψ.toHom x : PadicAlgCl 5) * (ρ.mat x).trace)
      (continuous_mat r).matrix_trace
      ((Units.continuous_val.comp ψ.continuous_toHom).mul (continuous_mat ρ).matrix_trace)
      (by
        intro p hp hpS v τ hv hτ
        have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
        have hpN : ¬ p ∣ N * 5 := fun h =>
          hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hN5⟩))
        obtain ⟨-, α, hα, hαt⟩ := hatt p hp hpS1
        obtain ⟨-, α', hα', hα't⟩ := hρatt p hp hpN
        have hαα : α = α' := ιC.toRingHom.injective (hα.trans hα'.symm)
        rw [hαt v τ hv hτ, hα't v τ hv hτ, hαα])
    exact fun x => congrFun h x
  have hmul : ∀ {n : ℕ} (q : GaloisRep 5 n) x, q.mat (x * x) = q.mat x * q.mat x := by
    intro n q x
    simp [PkgI4.GaloisRep.mat, map_mul]
  have hdetr : ∀ x, (r.mat x).det = (ψ.toHom x : PadicAlgCl 5) ^ 2 * (ρ.mat x).det := by
    intro x
    have h1 := htr x
    have h2 := htr (x * x)
    rw [hmul r x, hmul ρ x, map_mul, Units.val_mul] at h2
    rw [det_fin_two_eq_trace (r.mat x), det_fin_two_eq_trace (ρ.mat x), h1, h2]
    ring
  haveI := hFI K
  refine ⟨(resQ K).range, inferInstance, Matrix.GeneralLinearGroup.det.comp r.toHom, ε,
    cycQ 5, ?_, ?_, hεfin⟩
  · intro x
    apply Units.ext
    have hx := hdetr x
    rw [hdet x] at hx
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul,
      Units.val_pow_eq_pow_val]
    change (r.mat x).det = _
    rw [hx]
    norm_num
    ring
  · rintro _ ⟨σ, rfl⟩
    apply Units.ext
    have hconj : ((e : Vb A 5 →ₗ[PadicAlgCl 5] _) ∘ₗ tate A 5 σ ∘ₗ
        (e.symm : _ →ₗ[PadicAlgCl 5] Vb A 5)) =
        (Matrix.toLin' (r.mat (resQ K σ))).prodMap (Matrix.toLin' (r.mat (resQ K σ))) := by
      apply LinearMap.ext
      intro w
      have := hint σ (e.symm w)
      simp only [LinearEquiv.apply_symm_apply] at this
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
        LinearMap.prodMap_apply, Matrix.toLin'_apply]
    have h := LinearMap.det_conj (tate A 5 σ) e
    rw [hconj, LinearMap.det_prodMap, LinearMap.det_toLin', hDT K A 5 2 hdim σ] at h
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply,
      Units.val_pow_eq_pow_val]
    change (r.mat (resQ K σ)).det ^ 2 = _
    rw [← h]
    ring

end G0Galois

end

end G0GaloisDetSec

#print axioms G0Galois.g12Det_of
