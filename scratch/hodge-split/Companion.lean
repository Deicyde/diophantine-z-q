import ZInQKernel.Contrib.G9.I4Layer
import ZInQKernel.HDecomp.ModCurves.C9
import ZInQKernel.HDecomp.Textbook.C10Closed
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense

/-!
# hodge-split, companion file: `AttachedConj` proved from the kernel's T18 and T19

Task hodge-split, 2026-11-14. Separate from `HodgeSplit.lean` because importing `ZInQKernel.HDecomp`
puts a second `PkgI4` namespace (the root one) in scope, which makes the opened names of
`HodgeSplit.lean` ambiguous; scratch files cannot import each other. `IsConj` and `AttachedConj`
below are textual copies of the definitions in `HodgeSplit.lean` §10 with the names
`ZInQ.Contrib.G9.PkgI4.*` written out (the same constants `HodgeSplit.lean` resolves through
`open ZInQ.Contrib.G9`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ZInQ.Contrib.HodgeSplit

open Module

noncomputable section

/-- `r` and `ρ'` are conjugate by a fixed matrix (g12-det's `G0Galois.IsConj`, verbatim). -/
def IsConj {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r ρ' : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) : Prop :=
  ∃ P : GL (Fin n) (PadicAlgCl ℓ), ∀ σ, r.toHom σ = P * ρ'.toHom σ * P⁻¹

/-- **GLUE (Chebotarev density with Brauer–Nesbitt).** Copy of `HodgeSplit.lean`'s `AttachedConj`. -/
def AttachedConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ρ ρ' : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2) (S : Finset ℕ),
    ρ.IsSemisimple → ρ'.IsSemisimple →
    (∀ p : ℕ, p.Prime → p ∉ S → ρ.UnramifiedAt p ∧ ρ'.UnramifiedAt p ∧
      ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ),
        ZInQ.Contrib.G9.PkgI4.LiesOver v p →
        ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p → (ρ.mat σ).trace = (ρ'.mat σ).trace) →
    IsConj ρ ρ'

/-! ## §13. Glue proved: `AttachedConj` (Chebotarev with Brauer–Nesbitt)

From the kernel's proved leaves T18 (`ZInQ.Contrib.frobeniusDense`, through Tau Ceti's Chebotarev)
and T19 (`TSkolemKW.C10.brauerNesbittChar0'`), via `C9Rhof.iso_of_arithFrob`
(`ZInQKernel/HDecomp/ModCurves/C9.lean`). The bridge: pkg-I4's matrix-valued `GaloisRep` as a
Mathlib `Representation` on `ℚ̄_ℓ²`; its `IsSemisimple` (invariant complements) as
`IsSemisimpleModule` over the group algebra (Mathlib's `Representation.mapSubmodule`). -/

section AttachedConjSec


variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- pkg-I4's `GaloisRep` as a Mathlib `Representation` on `ℚ̄_ℓⁿ`. -/
def galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) :
    Representation (PadicAlgCl ℓ) ZInQ.Contrib.G9.PkgI4.GQ (Fin n → PadicAlgCl ℓ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) ≃ₐ[PadicAlgCl ℓ] _).toMonoidHom.comp
    ((Units.coeHom _).comp ρ.toHom)

theorem galRepRep_apply {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    galRepRep ρ σ = Matrix.toLin' (ρ.mat σ) := rfl

theorem toMatrix_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (galRepRep ρ σ) = ρ.mat σ := by
  rw [LinearMap.toMatrix_eq_toMatrix', galRepRep_apply, LinearMap.toMatrix'_toLin']

theorem trace_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ σ) = (ρ.mat σ).trace := by
  rw [LinearMap.trace_eq_matrix_trace (PadicAlgCl ℓ) (Pi.basisFun (PadicAlgCl ℓ) (Fin n)),
    toMatrix_galRepRep]

theorem continuous_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) :
    Continuous fun g => LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (galRepRep ρ g) := by
  simp only [toMatrix_galRepRep]
  exact Units.continuous_val.comp ρ.continuous_toHom

theorem mem_invtSubmodule_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n)
    (W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ)) :
    W ∈ (galRepRep ρ).invtSubmodule ↔ ∀ σ, W.map (Matrix.toLin' (ρ.mat σ)) ≤ W := by
  rw [Representation.mem_invtSubmodule]
  refine forall_congr' fun σ => ?_
  rw [Module.End.mem_invtSubmodule, Submodule.map_le_iff_le_comap, galRepRep_apply]

theorem isSemisimpleModule_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (h : ZInQ.Contrib.G9.PkgI4.GaloisRep.IsSemisimple ρ) :
    IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) ZInQ.Contrib.G9.PkgI4.GQ) (galRepRep ρ).asModule := by
  rw [isSemisimpleModule_iff, ← (galRepRep ρ).mapSubmodule.complementedLattice_iff]
  refine ⟨fun a => ?_⟩
  obtain ⟨W, hW⟩ := a
  obtain ⟨W', hc, hW'⟩ := h W ((mem_invtSubmodule_galRepRep ρ W).mp hW)
  refine ⟨⟨W', (mem_invtSubmodule_galRepRep ρ W').mpr hW'⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subtype.ext hc.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subtype.ext hc.sup_eq_top

/-- `C9Rhof.FrobeniusDense` from the kernel's proved T18 (same body, other namespace). -/
theorem frobeniusDense_C9 : C9Rhof.FrobeniusDense := by
  intro U hU σ S
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := ZInQ.Contrib.frobeniusDense U hU σ S
  exact ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩

/-- **`AttachedConj`, proved** (from T18, T19 in the kernel). -/
theorem attachedConj_proof : AttachedConj := by
  intro ℓ _ ρ ρ' S hss hss' hS
  have htr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (τ : ZInQ.Contrib.G9.PkgI4.GQ),
      ZInQ.Contrib.G9.PkgI4.LiesOver v p → ZInQ.Contrib.G9.PkgI4.IsArithFrob τ v p →
      LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ τ) =
        LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ' τ) := by
    intro p hp hpS v τ hv hτ
    rw [trace_galRepRep, trace_galRepRep]
    exact (hS p hp hpS).2.2 v τ hv hτ
  obtain ⟨e⟩ := C9Rhof.iso_of_arithFrob TSkolemKW.C10.brauerNesbittChar0' frobeniusDense_C9 S
    (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2))
    (galRepRep ρ) (galRepRep ρ') (continuous_galRepRep ρ) (continuous_galRepRep ρ')
    (isSemisimpleModule_galRepRep ρ hss) (isSemisimpleModule_galRepRep ρ' hss') htr
  let L : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) :=
    ((galRepRep ρ).asModuleEquiv.symm.trans (e.restrictScalars (PadicAlgCl ℓ))).trans
      (galRepRep ρ').asModuleEquiv
  have hL : ∀ σ v, L (galRepRep ρ σ v) = galRepRep ρ' σ (L v) := by
    intro σ v
    simp only [L, LinearEquiv.trans_apply, Representation.asModuleEquiv_symm_map_rho,
      LinearEquiv.restrictScalars_apply, LinearEquiv.map_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
  let M := LinearMap.toMatrix' L.toLinearMap
  let M' := LinearMap.toMatrix' L.symm.toLinearMap
  have h1 : M' * M = 1 := by
    simp only [M, M', ← LinearMap.toMatrix'_comp]
    rw [show (L.symm.toLinearMap ∘ₗ L.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => L.symm_apply_apply v, LinearMap.toMatrix'_id]
  have h2 : M * M' = 1 := by
    simp only [M, M', ← LinearMap.toMatrix'_comp]
    rw [show (L.toLinearMap ∘ₗ L.symm.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => L.apply_symm_apply v, LinearMap.toMatrix'_id]
  have hcomm : ∀ σ, M * ρ.mat σ = ρ'.mat σ * M := by
    intro σ
    have : L.toLinearMap ∘ₗ galRepRep ρ σ = galRepRep ρ' σ ∘ₗ L.toLinearMap :=
      LinearMap.ext fun v => hL σ v
    have h' := congrArg LinearMap.toMatrix' this
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, galRepRep_apply, galRepRep_apply,
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin'] at h'
    exact h'
  refine ⟨⟨M', M, h1, h2⟩, fun σ => Units.ext ?_⟩
  change ρ.mat σ = M' * ρ'.mat σ * M
  rw [mul_assoc, ← hcomm σ, ← mul_assoc, h1, one_mul]

end AttachedConjSec


/-! ## `DetFromFrobenius` (R14 glue), proved

From the kernel's T18 (density of arithmetic Frobenius elements), Mathlib's cyclotomic characters
(`cyclotomicCharacter`, `modularCyclotomicCharacter`, `cyclotomicCharacter.continuous`) and an
elementary lemma: an arithmetic Frobenius at `v ∣ p` raises roots of unity of order prime to `p`
to the `p`-th power (`arithFrob_pow_of_rootOfUnity`). -/

section DetFrob

open ZInQ.Contrib.G9.PkgI4


theorem val_eq_one_of_pow {v : ValuationSubring Qbar} {x : Qbar} {m : ℕ} (hm : m ≠ 0)
    (hx : x ^ m = 1) : v.valuation x = 1 := by
  have h := congrArg v.valuation hx
  rw [map_pow, map_one] at h
  rcases lt_trichotomy (v.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le h1 hm))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 hm))

/-- An arithmetic Frobenius at `v ∣ p` acts on roots of unity of order prime to `p` as `ζ ↦ ζ^p`. -/
theorem arithFrob_pow_of_rootOfUnity {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hv : LiesOver v p) (hσ : IsArithFrob σ v p) {ζ : Qbar} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1)
    (hpm : ¬ p ∣ m) : σ ζ = ζ ^ p := by
  set val := v.valuation
  have hζ1 : val ζ = 1 := val_eq_one_of_pow hm hζ
  have hζv : ζ ∈ v := (v.valuation_le_one_iff ζ).mp hζ1.le
  have hσζm : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  have hσζ1 : val (σ ζ) = 1 := val_eq_one_of_pow hm hσζm
  have hζp0 : ζ ^ p ≠ 0 := pow_ne_zero _ (by rintro rfl; simp [hm] at hζ)
  set ξ := σ ζ / ζ ^ p with hξ
  have hξm : ξ ^ m = 1 := by
    rw [hξ, div_pow, hσζm, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, div_one]
  have hlt : val (σ ζ - ζ ^ p) < 1 := (v.mem_nonunits_iff).mp (hσ.2 ζ hζv)
  have hξ1 : val (ξ - 1) < 1 := by
    have : ξ - 1 = (σ ζ - ζ ^ p) / ζ ^ p := by rw [hξ]; field_simp
    rw [this, map_div₀, map_pow, hζ1, one_pow, div_one]
    exact hlt
  by_contra hne
  have hξne : ξ ≠ 1 := by
    intro h; apply hne
    rw [hξ, div_eq_one_iff_eq hζp0] at h
    exact h
  -- `Σ_{j<m} ξ^j = 0`
  have hgeom : ∑ j ∈ Finset.range m, ξ ^ j = 0 := by
    have := geom_sum_mul ξ m
    rw [hξm, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hξne)
  -- each `ξ^j - 1` is in the maximal ideal
  have hj : ∀ j, val (ξ ^ j - 1) < 1 := by
    intro j
    have : ξ ^ j - 1 = (ξ - 1) * ∑ i ∈ Finset.range j, ξ ^ i := by
      rw [mul_comm, geom_sum_mul]
    rw [this, map_mul]
    have hs : val (∑ i ∈ Finset.range j, ξ ^ i) ≤ 1 := by
      apply Valuation.map_sum_le
      intro i _
      rw [map_pow]
      have : val ξ = 1 := val_eq_one_of_pow hm hξm
      rw [this, one_pow]
    calc val (ξ - 1) * val (∑ i ∈ Finset.range j, ξ ^ i) ≤ val (ξ - 1) * 1 :=
          mul_le_mul_of_nonneg_left hs zero_le
      _ < 1 := by rw [mul_one]; exact hξ1
  -- so `m ∈` the maximal ideal
  have hmval : val (m : Qbar) < 1 := by
    have : (m : Qbar) = -∑ j ∈ Finset.range m, (ξ ^ j - 1) := by
      rw [Finset.sum_sub_distrib, hgeom]; simp
    rw [this, Valuation.map_neg]
    exact Valuation.map_sum_lt' _ zero_lt_one fun j _ => hj j
  have hpval : val (p : Qbar) < 1 := (v.mem_nonunits_iff).mp hv
  -- `gcd(m, p) = 1` gives `1` in the maximal ideal
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * m + b * p = 1 := by
    have := Nat.Coprime.isCoprime hcop.symm
    obtain ⟨a, b, h⟩ := this
    exact ⟨a, b, by exact_mod_cast h⟩
  have h1 : val (1 : Qbar) < 1 := by
    have : (1 : Qbar) = (a : Qbar) * m + (b : Qbar) * p := by exact_mod_cast hab.symm
    rw [this]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (v.valuation_le_one ⟨_, intCast_mem v a⟩))
        hmval
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (v.valuation_le_one ⟨_, intCast_mem v b⟩))
        hpval
  rw [map_one] at h1
  exact lt_irrefl _ h1

namespace G0Galois

/-- `σ ↦ σ` as ring automorphisms of `ℚ̄` (copy of `HodgeSplit.lean`'s `G0Galois.toRingEquivQ`). -/
def toRingEquivQ : ZInQ.Contrib.G9.PkgI4.GQ →* (ZInQ.Contrib.G9.PkgI4.Qbar ≃+* ZInQ.Contrib.G9.PkgI4.Qbar) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The `ℓ`-adic cyclotomic character (copy of `HodgeSplit.lean`'s `G0Galois.cycQ`). -/
def cycQ (ℓ : ℕ) [Fact ℓ.Prime] : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
  (Units.map ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter ZInQ.Contrib.G9.PkgI4.Qbar ℓ).comp toRingEquivQ)

end G0Galois

/-- **GLUE (the determinant from its values at Frobenius).** Copy of `HodgeSplit.lean`'s
`DetFromFrobenius` with the names written out. -/
def DetFromFrobenius : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ)
    (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2), 0 < N →
    (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧
      ∃ β : ZInQ.Contrib.G9.PkgI4.Qbar, ιC β = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) ∧
        ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ),
          ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p → (ρ.mat σ).det = ιL β) →
    ∃ ε : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ, (Set.range ε).Finite ∧
      ∀ σ, (ρ.mat σ).det = ((ε σ * G0Galois.cycQ ℓ σ ^ (k - 1) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)

theorem pow_eq_pow_mod_of {M : Type*} [Monoid M] {t : M} {n : ℕ} (ht : t ^ n = 1) (a : ℕ) :
    t ^ a = t ^ (a % n) := by
  conv_lhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, ht, one_pow, mul_one]

/-- The cyclotomic character at an arithmetic Frobenius at `p ≠ ℓ` is `p`. -/
theorem cyc_arithFrob {ℓ : ℕ} [Fact ℓ.Prime] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpl : p ≠ ℓ) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((cyclotomicCharacter Qbar ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (p : ℤ_[ℓ]) := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  have hl : (ℓ ^ n) ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  haveI : NeZero (ℓ ^ n) := ⟨hl⟩
  refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
  have htn : (t : Qbar) ^ (ℓ ^ n) = 1 := by
    have := (mem_rootsOfUnity _ _).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hpm : ¬ p ∣ ℓ ^ n := fun h =>
    hpl ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp (hp.dvd_of_dvd_pow h))
  change σ (t : Qbar) = ((t ^ ((p : ZMod (ℓ ^ n))).val : Qbarˣ) : Qbar)
  rw [arithFrob_pow_of_rootOfUnity hp hv hσ hl htn hpm, Units.val_pow_eq_pow_val, ZMod.val_natCast,
    ← pow_eq_pow_mod_of htn]

/-- The cyclotomic character mod `N` at an arithmetic Frobenius at `p ∤ N` is `p`. -/
theorem modCyc_arithFrob {N : ℕ} [NeZero N] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((modularCyclotomicCharacter Qbar (HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar N)
      σ.toRingEquiv : (ZMod N)ˣ) : ZMod N) = (p : ZMod N) := by
  refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
  have htn : (t : Qbar) ^ N = 1 := by
    have := (mem_rootsOfUnity _ _).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  change σ (t : Qbar) = ((t ^ ((p : ZMod N)).val : Qbarˣ) : Qbar)
  rw [arithFrob_pow_of_rootOfUnity hp hv hσ (NeZero.ne N) htn hpN, Units.val_pow_eq_pow_val,
    ZMod.val_natCast, ← pow_eq_pow_mod_of htn]

end DetFrob


section EpsZero

open ZInQ.Contrib.G9.PkgI4

variable {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
  {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- `ιC` on `m`-th roots of unity is a bijection `μ_m(ℚ̄) ≃ μ_m(ℂ)`. -/
noncomputable def rootsEquiv (m : ℕ) [NeZero m] : rootsOfUnity m Qbar ≃* rootsOfUnity m ℂ :=
  MulEquiv.ofBijective (restrictRootsOfUnity ιC m) <| by
    have hinj : Function.Injective (restrictRootsOfUnity ιC m) := by
      intro x y h
      apply Subtype.ext; apply Units.ext
      have := congrArg (fun z : rootsOfUnity m ℂ => ((z : ℂˣ) : ℂ)) h
      simp only [restrictRootsOfUnity_coe_apply] at this
      exact ιC.toRingHom.injective this
    refine (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar m, Complex.card_rootsOfUnity]

theorem iotaC_rootsEquiv_symm (m : ℕ) [NeZero m] (x : rootsOfUnity m ℂ) :
    ιC (((rootsEquiv ιC m).symm x : Qbarˣ) : Qbar) = ((x : ℂˣ) : ℂ) := by
  have h := (rootsEquiv ιC m).apply_symm_apply x
  conv_rhs => rw [← h]
  rfl

/-- The order of every value of `χ` divides `m = #(ℤ/N)ˣ`. -/
noncomputable def chiRoots : (ZMod N)ˣ →* rootsOfUnity (Nat.card (ZMod N)ˣ) ℂ :=
  MonoidHom.codRestrict χ.toUnitHom _ fun u => by
    rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]

/-- The nebentypus as an `ℓ`-adic character of `(ℤ/N)ˣ`: `u ↦ ιL(ιC⁻¹(χ u))`. -/
noncomputable def chiL : (ZMod N)ˣ →* (PadicAlgCl ℓ)ˣ :=
  haveI : NeZero (Nat.card (ZMod N)ˣ) := ⟨Nat.card_pos.ne'⟩
  (Units.map ιL.toMonoidHom).comp ((rootsOfUnity (Nat.card (ZMod N)ˣ) Qbar).subtype.comp
    ((rootsEquiv ιC (Nat.card (ZMod N)ˣ)).symm.toMonoidHom.comp (chiRoots χ)))

theorem chiL_spec (u : (ZMod N)ˣ) : ∃ γ : Qbar, ιC γ = χ (u : ZMod N) ∧
    ((chiL ιC ιL χ u : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = ιL γ := by
  haveI : NeZero (Nat.card (ZMod N)ˣ) := ⟨Nat.card_pos.ne'⟩
  refine ⟨(((rootsEquiv ιC (Nat.card (ZMod N)ˣ)).symm (chiRoots χ u) : Qbarˣ) : Qbar), ?_, rfl⟩
  rw [iotaC_rootsEquiv_symm]
  rfl

/-- The cyclotomic character mod `N` on `G_ℚ`. -/
noncomputable def modCycQ : GQ →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter Qbar (HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar N)).comp
    G0Galois.toRingEquivQ

/-- `ε₀ = chiL ∘ modCycQ`: the nebentypus as a Galois character. -/
noncomputable def eps0 : GQ →* (PadicAlgCl ℓ)ˣ := (chiL ιC ιL χ).comp modCycQ

theorem eps0_finite : (Set.range (eps0 ιC ιL χ)).Finite :=
  (Set.finite_range (chiL ιC ιL χ)).subset (by rintro _ ⟨σ, rfl⟩; exact ⟨_, rfl⟩)

theorem eps0_arithFrob {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ∃ γ : Qbar, ιC γ = χ (p : ZMod N) ∧ ((eps0 ιC ιL χ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = ιL γ := by
  obtain ⟨γ, hγ, hval⟩ := chiL_spec ιC ιL χ (modCycQ σ)
  refine ⟨γ, ?_, hval⟩
  rw [hγ]
  congr 1
  exact modCyc_arithFrob hp hpN hv hσ

/-- `ε₀` is trivial on `Gal(ℚ̄/ℚ(μ_N))`, an open subgroup; hence continuous. -/
theorem eps0_continuous : Continuous (eps0 ιC ιL χ) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar N
  let K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have hK : ∀ σ ∈ K.fixingSubgroup, eps0 ιC ιL χ σ = 1 := by
    intro σ hσ
    have hfix : σ ζ = ζ := hσ ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
    have h1 : modCycQ (N := N) σ = 1 := by
      apply Units.ext
      refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
      have htn : (t : Qbar) ^ N = 1 := by
        have := (mem_rootsOfUnity _ _).mp ht
        rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one htn
      change σ (t : Qbar) = ((t ^ ((1 : (ZMod N)ˣ) : ZMod N).val : Qbarˣ) : Qbar)
      rw [← hi, map_pow, hfix, Units.val_pow_eq_pow_val, ← hi]
      by_cases hN1 : N = 1
      · subst hN1
        have : (t : Qbar) = 1 := by simpa using htn
        rw [hi, this, one_pow]
      · haveI : Fact (1 < N) := ⟨by have := NeZero.ne N; omega⟩
        rw [Units.val_one, ZMod.val_one, pow_one]
    simp [eps0, h1]
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  have hnhds : (K.fixingSubgroup : Set GQ) ∈ nhds (1 : GQ) :=
    (IntermediateField.fixingSubgroup_isOpen K).mem_nhds K.fixingSubgroup.one_mem
  exact tendsto_nhds_of_eventually_eq (Filter.mem_of_superset hnhds fun σ hσ => hK σ hσ)

end EpsZero


section DetFrobMain

open ZInQ.Contrib.G9.PkgI4

theorem toRingEquivQ_eq : G0Galois.toRingEquivQ = MulSemiringAction.toRingAut Gal(Qbar/ℚ) Qbar := by
  ext σ x; rfl

theorem continuous_units_map {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M]
    [TopologicalSpace N] {X : Type*} [TopologicalSpace X] (f : M →* N) (hf : Continuous f)
    {c : X → Mˣ} (hc : Continuous c) : Continuous fun x => Units.map f (c x) := by
  rw [Units.continuous_iff]
  exact ⟨hf.comp (Units.continuous_val.comp hc), hf.comp (Units.continuous_coe_inv.comp hc)⟩

theorem continuous_cycQ (ℓ : ℕ) [Fact ℓ.Prime] : Continuous (G0Galois.cycQ ℓ) := by
  have h := cyclotomicCharacter.continuous ℓ ℚ Qbar
  rw [← toRingEquivQ_eq] at h
  have hf : Continuous ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp PadicInt.Coe.ringHom) :=
    (continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp continuous_subtype_val
  exact continuous_units_map _ hf h

theorem cycQ_arithFrob {ℓ : ℕ} [Fact ℓ.Prime] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpl : p ≠ ℓ) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((G0Galois.cycQ ℓ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = (p : PadicAlgCl ℓ) := by
  change algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)
    (((cyclotomicCharacter Qbar ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) = _
  rw [cyc_arithFrob hp hpl hv hσ]
  simp

/-- **`DetFromFrobenius`, proved** (from the kernel's T18 and Mathlib's cyclotomic characters). -/
theorem detFromFrobenius_proof : DetFromFrobenius := by
  intro ℓ _ ιC ιL N k χ ρ hN hfrob
  haveI : NeZero N := ⟨hN.ne'⟩
  let detU : GQ →* (PadicAlgCl ℓ)ˣ := Matrix.GeneralLinearGroup.det.comp ρ.toHom
  have hdetU : ∀ σ, ((detU σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = (ρ.mat σ).det := fun σ => rfl
  have hdetc : Continuous detU := by
    rw [Units.continuous_iff]
    refine ⟨(Units.continuous_val.comp ρ.continuous_toHom).matrix_det, ?_⟩
    have : (fun σ => (((detU σ)⁻¹ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)) =
        fun σ => (((ρ.toHom σ)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) _).det := by
      funext σ; rfl
    rw [this]
    exact (Units.continuous_coe_inv.comp ρ.continuous_toHom).matrix_det
  let δ : GQ → (PadicAlgCl ℓ)ˣ := fun σ => detU σ * G0Galois.cycQ ℓ σ ^ (-(k - 1))
  have hδc : Continuous δ := hdetc.mul ((continuous_cycQ ℓ).zpow _)
  have hp0 : ∀ p : ℕ, p.Prime → (p : PadicAlgCl ℓ) ≠ 0 := fun p hp => by
    exact_mod_cast hp.ne_zero
  have hEq : δ = eps0 ιC ιL χ := by
    refine C9Rhof.eq_of_eq_on_arithFrob frobeniusDense_C9 (N * ℓ).primeFactors δ (eps0 ιC ιL χ)
      hδc (eps0_continuous ιC ιL χ) fun p hp hpS v τ hv hτ => ?_
    have hNl : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
    have hpNl : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.mpr ⟨hp, h, hNl⟩)
    have hpN : ¬ p ∣ N := fun h => hpNl (Dvd.dvd.mul_right h ℓ)
    have hpl : p ≠ ℓ := fun h => hpNl (h ▸ Dvd.intro_left N rfl)
    obtain ⟨-, β, hβ, hdet⟩ := hfrob p hp hpNl
    obtain ⟨γ, hγ, hε⟩ := eps0_arithFrob ιC ιL χ hp hpN hv hτ
    have hβγ : β = γ * (p : Qbar) ^ (k - 1) := by
      apply ιC.toRingHom.injective
      change ιC β = ιC (γ * (p : Qbar) ^ (k - 1))
      rw [hβ, map_mul, map_zpow₀, map_natCast ιC, hγ]
    apply Units.ext
    change (detU τ : PadicAlgCl ℓ) * ((G0Galois.cycQ ℓ τ ^ (-(k - 1)) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = _
    rw [hdetU, hdet v τ hv hτ, Units.val_zpow_eq_zpow_val, cycQ_arithFrob hp hpl hv hτ, hε, hβγ,
      map_mul, map_zpow₀, map_natCast ιL, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (hp0 p hp)),
      mul_one]
  refine ⟨eps0 ιC ιL χ, eps0_finite ιC ιL χ, fun σ => ?_⟩
  rw [← hEq]
  change (ρ.mat σ).det = ((detU σ * G0Galois.cycQ ℓ σ ^ (-(k - 1)) * G0Galois.cycQ ℓ σ ^ (k - 1) :
    (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)
  rw [zpow_neg, inv_mul_cancel_right, hdetU]

end DetFrobMain


section ArtinHelpers

open ZInQ.Contrib.G9.PkgI4

/-- A root of unity in `ℂ` is `ιC` of an element of `ℚ̄`. -/
theorem mem_range_of_pow_eq_one (ιC : Qbar →ₐ[ℚ] ℂ) {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
    z ∈ Set.range ιC := by
  haveI : NeZero n := ⟨hn⟩
  have hz0 : z ≠ 0 := by rintro rfl; simp [hn] at hz
  let u : rootsOfUnity n ℂ := ⟨Units.mk0 z hz0, by
    rw [mem_rootsOfUnity]; apply Units.ext; simp [hz]⟩
  refine ⟨(((rootsEquiv ιC n).symm u : Qbarˣ) : Qbar), ?_⟩
  rw [iotaC_rootsEquiv_symm]
  rfl

/-- The trace of a complex `2 × 2` matrix of finite order is `ιC` of an algebraic number. -/
theorem trace_mem_range_of_pow_eq_one (ιC : Qbar →ₐ[ℚ] ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) {n : ℕ}
    (hn : n ≠ 0) (hM : M ^ n = 1) : M.trace ∈ ιC.range := by
  rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  refine Subalgebra.multiset_sum_mem _ fun r hr => ?_
  have hroot : M.charpoly.IsRoot r := (Polynomial.mem_roots (Matrix.charpoly_monic M).ne_zero).mp hr
  have hspec : r ∈ spectrum ℂ M := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
  have hpow : r ^ n ∈ spectrum ℂ (M ^ n) := spectrum.pow_mem_pow M n hspec
  rw [hM, spectrum.one_eq, Set.mem_singleton_iff] at hpow
  obtain ⟨a, ha⟩ := mem_range_of_pow_eq_one ιC hn hpow
  exact ⟨a, ha⟩

end ArtinHelpers


section ArtinHelpers2

open ZInQ.Contrib.G9.PkgI4

/-- The subring of `ℂ` generated by `ιC(ℚ̄)` and a finite set `E`. -/
noncomputable def genRing (ιC : Qbar →ₐ[ℚ] ℂ) (E : Set ℂ) : Subring ℂ :=
  (MvPolynomial.eval₂Hom (ιC : Qbar →+* ℂ) (fun e : E => (e : ℂ))).range

theorem mem_genRing_of_mem (ιC : Qbar →ₐ[ℚ] ℂ) {E : Set ℂ} {e : ℂ} (he : e ∈ E) :
    e ∈ genRing ιC E :=
  ⟨MvPolynomial.X ⟨e, he⟩, by simp⟩

theorem iotaC_mem_genRing (ιC : Qbar →ₐ[ℚ] ℂ) (E : Set ℂ) (a : Qbar) : ιC a ∈ genRing ιC E :=
  ⟨MvPolynomial.C a, by simp⟩

/-- **Specialization (Hilbert's Nullstellensatz).** A ring map `genRing ιC E → ℚ̄` that is `ιC⁻¹`
on `ιC(ℚ̄)`. -/
theorem exists_specialization (ιC : Qbar →ₐ[ℚ] ℂ) (E : Set ℂ) [Finite E] :
    ∃ φ : genRing ιC E →+* Qbar, ∀ a : Qbar, φ ⟨ιC a, iotaC_mem_genRing ιC E a⟩ = a := by
  classical
  let F := MvPolynomial.eval₂Hom (ιC : Qbar →+* ℂ) (fun e : E => (e : ℂ))
  have hI : RingHom.ker F ≠ ⊤ := by
    intro h
    have : (1 : MvPolynomial E Qbar) ∈ RingHom.ker F := h ▸ Submodule.mem_top
    simp [RingHom.mem_ker] at this
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal Qbar hm
  let ev : MvPolynomial E Qbar →+* Qbar := MvPolynomial.eval x
  have hle : RingHom.ker F.rangeRestrict ≤ RingHom.ker ev := by
    rw [RingHom.ker_rangeRestrict]
    intro f hf
    have hfm : f ∈ m := hIm hf
    rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hfm
    rw [RingHom.mem_ker]
    exact hfm
  let e := RingHom.quotientKerEquivOfSurjective (F.rangeRestrict_surjective)
  refine ⟨(Ideal.Quotient.lift _ ev (fun a ha => RingHom.mem_ker.mp (hle ha))).comp e.symm.toRingHom, fun a => ?_⟩
  have h1 : (⟨ιC a, iotaC_mem_genRing ιC E a⟩ : genRing ιC E) = F.rangeRestrict (MvPolynomial.C a) := by
    apply Subtype.ext; simp [F]
  rw [h1]
  change Ideal.Quotient.lift _ ev (fun a ha => RingHom.mem_ker.mp (hle ha)) (e.symm (F.rangeRestrict (MvPolynomial.C a))) = a
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  simp [ev]

/-- A homomorphism to `GL_n(ℂ)` with entries in a subring `A` lifts to `GL_n(A)`. -/
def liftGLSub {G : Type*} [Group G] {n : ℕ} (A : Subring ℂ) (f : G →* GL (Fin n) ℂ)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) ℂ) i j ∈ A) : G →* GL (Fin n) A :=
  let M : G → Matrix (Fin n) (Fin n) A := fun g i j => ⟨(f g : Matrix (Fin n) (Fin n) ℂ) i j, h g i j⟩
  have hM : ∀ g, (M g).map A.subtype = (f g : Matrix (Fin n) (Fin n) ℂ) := fun g => by ext i j; rfl
  have hinj : Function.Injective (fun B : Matrix (Fin n) (Fin n) A => B.map A.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hmul : ∀ g g', M (g * g') = M g * M g' := fun g g' => hinj (by
    simp only [Matrix.map_mul, hM, map_mul, Units.val_mul])
  have hone : M 1 = 1 := hinj (by simp only [hM, map_one, Units.val_one, Matrix.map_one,
    map_zero, map_one])
  { toFun := fun g => ⟨M g, M g⁻¹, by rw [← hmul, mul_inv_cancel, hone],
      by rw [← hmul, inv_mul_cancel, hone]⟩
    map_one' := Units.ext hone
    map_mul' := fun g g' => Units.ext (hmul g g') }

theorem liftGLSub_coe {G : Type*} [Group G] {n : ℕ} (A : Subring ℂ) (f : G →* GL (Fin n) ℂ)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) ℂ) i j ∈ A) (g : G) (i j : Fin n) :
    (((liftGLSub A f h g : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j : ℂ) =
      (f g : Matrix (Fin n) (Fin n) ℂ) i j := rfl

/-- **Maschke.** A `GaloisRep` with finite image is semisimple. -/
theorem isSemisimple_of_finite_range {ℓ n : ℕ} [Fact ℓ.Prime] (ρ : GaloisRep ℓ n)
    (h : (Set.range ρ.toHom).Finite) : ρ.IsSemisimple := by
  classical
  let H := ρ.toHom.range
  haveI : Finite H := by
    have : (H : Set (GL (Fin n) (PadicAlgCl ℓ))) = Set.range ρ.toHom := MonoidHom.coe_range _
    exact Set.Finite.to_subtype (this ▸ h)
  haveI : NeZero (Nat.card H : PadicAlgCl ℓ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let ρH : Representation (PadicAlgCl ℓ) H (Fin n → PadicAlgCl ℓ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) ≃ₐ[PadicAlgCl ℓ] _).toMonoidHom.comp
      ((Units.coeHom _).comp H.subtype)
  have hρH : ∀ (x : H), ρH x = Matrix.toLin' ((x : GL (Fin n) (PadicAlgCl ℓ)) :
      Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := fun _ => rfl
  have hss : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) H) ρH.asModule := inferInstance
  rw [isSemisimpleModule_iff, ← ρH.mapSubmodule.complementedLattice_iff] at hss
  have hmem : ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
      W ∈ ρH.invtSubmodule ↔ ∀ σ, W.map (Matrix.toLin' (ρ.mat σ)) ≤ W := by
    intro W
    rw [Representation.mem_invtSubmodule]
    constructor
    · intro hW σ
      have := hW ⟨ρ.toHom σ, σ, rfl⟩
      rw [Module.End.mem_invtSubmodule, hρH] at this
      rw [Submodule.map_le_iff_le_comap]
      exact this
    · rintro hW ⟨_, σ, rfl⟩
      rw [Module.End.mem_invtSubmodule, hρH, ← Submodule.map_le_iff_le_comap]
      exact hW σ
  intro W hW
  obtain ⟨b, hb⟩ := hss.exists_isCompl ⟨W, (hmem W).mpr hW⟩
  refine ⟨b.1, ⟨?_, ?_⟩, (hmem b.1).mp b.2⟩
  · rw [disjoint_iff]
    exact congrArg Subtype.val hb.inf_eq_bot
  · rw [codisjoint_iff]
    exact congrArg Subtype.val hb.sup_eq_top

/-- Every prime `p` has an arithmetic Frobenius (from the kernel's Chebotarev files). -/
theorem exists_arithFrob (p : ℕ) (hp : p.Prime) :
    ∃ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p ∧ IsArithFrob τ v p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨P, -, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := ZInQ.Contrib.ChebFD.C10.Zbar)
    (Ideal.span {(p : ℤ)}) ⊥ (by simp)
  obtain ⟨h, hh⟩ := ZInQ.Contrib.ChebFD.C10.frobExistsAt_of_finite
    ZInQ.Contrib.ChebFD.C10.frobExistsFinite p P hPp
  obtain ⟨hv, hτ⟩ := ZInQ.Contrib.ChebFD.HSyn.liesOver_and_isArithFrob P h p hp hPp hh
  exact ⟨_, h, hv, hτ⟩

end ArtinHelpers2


section ArtinMain

open ZInQ.Contrib.G9.PkgI4

/-- The row's conclusion for one eigenform (copy of `HodgeSplit.lean`'s `R14DetConcl`). -/
def R14DetConcl (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ)
    (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} {k : ℤ} (g : ZInQ.Contrib.G9.PkgI4.CF N k) : Prop :=
  ∃ ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g ∧
    ∃ ε : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ, (Set.range ε).Finite ∧
      ∀ σ, (ρ.mat σ).det = ((ε σ * G0Galois.cycQ ℓ σ ^ (k - 1) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)

/-- R14Det in weight `1` only (copy of `HodgeSplit.lean`'s `R14DetWt1`). -/
def R14DetWt1 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ)
    (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N 1),
    0 < N → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ → R14DetConcl ℓ ιC ιL g

/-- Deligne–Serre in Diamond–Shurman's form (copy of `HodgeSplit.lean`'s `DSThm966`). -/
def DSThm966 : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N 1),
    0 < N → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : ZInQ.Contrib.G9.PkgI4.GQ →* GL (Fin 2) ℂ, Continuous ρ ∧ (Set.range ρ).Finite ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        (∀ v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar, ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : ZInQ.Contrib.G9.PkgI4.GQ) = 1) ∧
        ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ),
          ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).trace = ZInQ.Contrib.G9.PkgI4.coeff g p ∧
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).det = χ (p : ZMod N)

/-- **GLUE (Artin representation as an `ℓ`-adic one).** Copy of `HodgeSplit.lean`'s
`ArtinTransport`. -/
def ArtinTransport : Prop := DSThm966 → R14DetWt1

/-- **`ArtinTransport`, proved**: specialize the entries of Deligne–Serre's `ρ_f` to `ℚ̄`
(Nullstellensatz, identity on `ιC(ℚ̄)`), apply `ιL`; semisimple by Maschke; `ε = det`. -/
theorem artinTransport_proof : ArtinTransport := by
  intro hDS ℓ _ ιC ιL N χ g hN hg
  classical
  obtain ⟨ρc, hcont, hfin, hloc⟩ := hDS N χ g hN hg
  let E : Set ℂ := ⋃ M ∈ Set.range ρc,
    Set.range fun ij : Fin 2 × Fin 2 => (M : Matrix (Fin 2) (Fin 2) ℂ) ij.1 ij.2
  haveI : Finite E := (hfin.biUnion fun M _ => Set.finite_range _).to_subtype
  have hmem : ∀ σ i j, (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j ∈ genRing ιC E := fun σ i j =>
    mem_genRing_of_mem ιC (Set.mem_biUnion (Set.mem_range_self σ) ⟨(i, j), rfl⟩)
  obtain ⟨φ, hφ⟩ := exists_specialization ιC E
  let ρA := liftGLSub (genRing ιC E) ρc hmem
  let g' : genRing ιC E →+* PadicAlgCl ℓ := ιL.toRingHom.comp φ
  let ρh : GQ →* GL (Fin 2) (PadicAlgCl ℓ) := (Matrix.GeneralLinearGroup.map g').comp ρA
  have hentry : ∀ σ i j, (ρh σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j =
      g' ⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ := fun _ _ _ => rfl
  have hker : ∀ σ, ρc σ = 1 → ρh σ = 1 := by
    intro σ h
    apply Units.ext
    ext i j
    rw [hentry]
    have hval : (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = if i = j then 1 else 0 := by
      rw [h, Units.val_one, Matrix.one_apply]
    by_cases hij : i = j
    · have : (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ : genRing ιC E) = 1 :=
        Subtype.ext (by change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = 1; rw [hval, if_pos hij])
      rw [this, map_one, Units.val_one, Matrix.one_apply, if_pos hij]
    · have : (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ : genRing ιC E) = 0 :=
        Subtype.ext (by change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = 0; rw [hval, if_neg hij])
      rw [this, map_zero, Units.val_one, Matrix.one_apply, if_neg hij]
  have hopen : IsOpen (ρc.ker : Set GQ) := by
    have hcl : IsClosed (ρc.ker : Set GQ) := by
      have : (ρc.ker : Set GQ) = ρc ⁻¹' {1} := by ext; simp
      rw [this]; exact isClosed_singleton.preimage hcont
    haveI : Finite ρc.range := by
      have : (ρc.range : Set (GL (Fin 2) ℂ)) = Set.range ρc := MonoidHom.coe_range ρc
      exact Set.Finite.to_subtype (this ▸ hfin)
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  have hρhc : Continuous ρh := by
    refine continuous_of_continuousAt_one _ ?_
    rw [ContinuousAt, map_one]
    exact tendsto_nhds_of_eventually_eq
      (Filter.mem_of_superset (hopen.mem_nhds ρc.ker.one_mem) fun σ hσ => hker σ hσ)
  have hdep : ∀ σ σ', ρc σ = ρc σ' → ρh σ = ρh σ' := by
    intro σ σ' h
    have h1 : ρc (σ⁻¹ * σ') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hker _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hρfin : (Set.range ρh).Finite := by
    refine (hfin.image fun M => ρh (Function.invFun ρc M)).subset ?_
    rintro _ ⟨σ, rfl⟩
    refine ⟨ρc σ, ⟨σ, rfl⟩, hdep _ _ ?_⟩
    exact Function.invFun_eq ⟨σ, rfl⟩
  let ρ : GaloisRep ℓ 2 := ⟨ρh, hρhc⟩
  refine ⟨ρ, isSemisimple_of_finite_range ρ hρfin, ?_, ?_⟩
  · intro p hp hpNl
    have hpN : ¬ p ∣ N := fun h => hpNl (Dvd.dvd.mul_right h ℓ)
    obtain ⟨hun, hfr⟩ := hloc p hp hpN
    refine ⟨fun v hv σ hσ => hker _ (hun v hv σ hσ), ?_⟩
    obtain ⟨v₀, τ₀, hv₀, hτ₀⟩ := exists_arithFrob p hp
    have htr₀ := (hfr v₀ τ₀ hv₀ hτ₀).1
    -- `ρc τ₀` has finite order
    haveI : Finite ρc.range := by
      have : (ρc.range : Set (GL (Fin 2) ℂ)) = Set.range ρc := MonoidHom.coe_range ρc
      exact Set.Finite.to_subtype (this ▸ hfin)
    let x : ρc.range := ⟨ρc τ₀, τ₀, rfl⟩
    have hx : IsOfFinOrder x := isOfFinOrder_of_finite x
    have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
    have hpow : (ρc τ₀ : Matrix (Fin 2) (Fin 2) ℂ) ^ orderOf x = 1 := by
      have h1 := congrArg Subtype.val (pow_orderOf_eq_one x)
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
      rw [← Units.val_pow_eq_pow_val]
      change ((x : GL (Fin 2) ℂ) ^ orderOf x : GL (Fin 2) ℂ).val = 1
      rw [h1, Units.val_one]
    obtain ⟨α, hα'⟩ := trace_mem_range_of_pow_eq_one ιC _ hn hpow
    have hα : ιC α = (ρc τ₀ : Matrix (Fin 2) (Fin 2) ℂ).trace := hα'
    refine ⟨α, by rw [hα, htr₀], fun v σ hv hσ => ?_⟩
    have htr := (hfr v σ hv hσ).1
    have hsum : (∑ i, (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i i, hmem σ i i⟩ : genRing ιC E)) =
        ⟨ιC α, iotaC_mem_genRing ιC E α⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ).trace = ιC α
      rw [htr, ← htr₀, hα]
    change (Matrix.trace fun i j => (ρh σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j) = ιL α
    simp only [Matrix.trace, Matrix.diag, hentry, ← map_sum, hsum, g', RingHom.comp_apply, hφ]
    rfl
  · refine ⟨Matrix.GeneralLinearGroup.det.comp ρh,
      (hρfin.image Matrix.GeneralLinearGroup.det).subset
        (by rintro _ ⟨σ, rfl⟩; exact ⟨ρh σ, ⟨σ, rfl⟩, rfl⟩), fun σ => ?_⟩
    simp only [sub_self, zpow_zero, mul_one]
    rfl

end ArtinMain


/-! ## H-22 closed: `R14Det` from Diamond–Shurman's two printed theorems

Copies (names written out) of `HodgeSplit.lean` §8 (`R14Det`, `R14DetWtGe2`, `r14Det_of_wt`,
`DSThm965`, `Semisimplification2`, `r14DetWtGe2_of_ds`) and §14 (`semisimplification2_proof`), so
that the glue proved in this file closes the row. -/

namespace G0Galois

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)

/-- **R14 with its published determinant clause (leaf; Shimura 1971 Thm 7.14 for `k = 2`,
Deligne 1971 for `k ≥ 2`, Deligne–Serre 1974 for `k = 1`; locators UNVERIFIED).** For a normalized
eigenform `g` of weight `k ≥ 1` with nebentypus, there is a semisimple `ρ_g` attached to `g` with
`det ρ_g = ε · χ_ℓ^{k−1}`, `ε` of finite image (the nebentypus as a Galois character). This is
`HSyn.EigenformRepExists` plus the determinant, which the published statements contain. -/
def R14Det : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N k),
    0 < N → 1 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g ∧
      ∃ ε : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ, (Set.range ε).Finite ∧
        ∀ σ, (ρ.mat σ).det = ((ε σ * cycQ ℓ σ ^ (k - 1) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)

end G0Galois

section R14Closed

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)
open Polynomial

/-- R14Det in weights `k ≥ 2` only (Deligne's range). -/
def R14DetWtGe2 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N k),
    0 < N → 2 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ → R14DetConcl ℓ ιC ιL g

/-- **The weight split.** -/
theorem r14Det_of_wt (h1 : R14DetWt1) (h2 : R14DetWtGe2) : G0Galois.R14Det := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · subst hk1
    exact h1 ℓ ιC ιL N χ g hN hg
  · exact h2 ℓ ιC ιL N k χ g hN (by omega) hg

/-- **LEAF (Deligne's theorem, in Diamond–Shurman's form).** Diamond–Shurman, *A First Course in
Modular Forms*, GTM 228 (2005), Thm 9.6.5 (for `k ≥ 2`; from Deligne, Sém. Bourbaki 355 (1969)
[the Bourbaki talk, publ. 1971], and Shimura 1971 Thm 7.14 for `k = 2`; numbering UNVERIFIED): for a
normalized eigenform `f ∈ S_k(N, χ)`, `k ≥ 2`, and `λ ∣ ℓ` in `K_f`, there is a continuous
`ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})`, unramified at every `p ∤ ℓN`, such that for every maximal ideal `𝔭`
of `ℤ̄` over `p` the arithmetic Frobenius `Frob_𝔭` has characteristic polynomial
`x² − a_p(f) x + χ(p) p^{k−1}`. Lean form: coefficients extended along `K_{f,λ} → ℚ̄_ℓ` given by
`ιL ∘ ιC⁻¹` (the place `λ` is the one `ιL ∘ ιC⁻¹` induces), places of `ℚ̄` as valuation subrings,
arithmetic Frobenius as pkg-I4's `IsArithFrob`. The semisimplicity of the row is not part of this
form (Ribet 1977 gives irreducibility; here it is the glue `Semisimplification2`). -/
def DSThm965 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N k),
    0 < N → 2 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
      ρ.UnramifiedAt p ∧ ∃ α β : ZInQ.Contrib.G9.PkgI4.Qbar, ιC α = ZInQ.Contrib.G9.PkgI4.coeff g p ∧
        ιC β = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) ∧
        ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ), ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p →
          (ρ.mat σ).charpoly = X ^ 2 - C (ιL α) * X + C (ιL β)

/-- **GLUE (semisimplification in dimension 2; STANDARD, not proved here).** A continuous
`ρ : G_ℚ → GL₂(ℚ̄_ℓ)` has a continuous semisimple `ρ^ss` with the same characteristic polynomials,
unramified wherever `ρ` is. Needs: if `ρ` has an invariant line, conjugate it to upper triangular
form `(χ₁ ∗; 0 χ₂)` and take `diag(χ₁, χ₂)` (continuity of `χᵢ` from the entries; trivial on
inertia where `ρ` is). -/
def Semisimplification2 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ρ : GaloisRep ℓ 2), ∃ ρ' : GaloisRep ℓ 2, ρ'.IsSemisimple ∧
    (∀ σ, (ρ'.mat σ).charpoly = (ρ.mat σ).charpoly) ∧ ∀ p, ρ.UnramifiedAt p → ρ'.UnramifiedAt p

theorem trace_of_charpoly {ℓ : ℕ} [Fact ℓ.Prime] (M : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (a b : PadicAlgCl ℓ) (h : M.charpoly = X ^ 2 - C a * X + C b) : M.trace = a := by
  rw [Matrix.trace_eq_neg_charpoly_coeff, h]
  simp [coeff_X_pow, coeff_C, coeff_X]

theorem det_of_charpoly {ℓ : ℕ} [Fact ℓ.Prime] (M : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (a b : PadicAlgCl ℓ) (h : M.charpoly = X ^ 2 - C a * X + C b) : M.det = b := by
  rw [Matrix.det_eq_sign_charpoly_coeff, h]
  simp [coeff_X_pow, coeff_C, coeff_X]

/-- **R14Det in weights `≥ 2` from Deligne's theorem (Diamond–Shurman form) and two glue Props.** -/
theorem r14DetWtGe2_of_ds (hD : DSThm965) (hS : Semisimplification2) (hdet : DetFromFrobenius) :
    R14DetWtGe2 := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ0, hρ0⟩ := hD ℓ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hss, hcp, hun⟩ := hS ℓ ρ0
  have hatt : ρ.AttachedTo ιC ιL g := by
    intro p hp hpN
    obtain ⟨hu, α, β, hα, -, hfrob⟩ := hρ0 p hp hpN
    refine ⟨hun p hu, α, hα, fun v σ hv hσ => ?_⟩
    exact trace_of_charpoly _ _ _ ((hcp σ).trans (hfrob v σ hv hσ))
  obtain ⟨ε, hεfin, hε⟩ := hdet ℓ ιC ιL N k χ ρ hN fun p hp hpN => by
    obtain ⟨hu, α, β, -, hβ, hfrob⟩ := hρ0 p hp hpN
    exact ⟨hun p hu, β, hβ, fun v σ hv hσ =>
      det_of_charpoly _ _ _ ((hcp σ).trans (hfrob v σ hv hσ))⟩
  exact ⟨ρ, hss, hatt, ε, hεfin, hε⟩


section SS

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem charpoly_fin_two' (M : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det := by
  rw [Matrix.charpoly, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _
    (show (0 : Fin 2) ≠ 1 by decide), Matrix.diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide),
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  simp only [map_sub, map_add, map_mul]
  ring

/-- `σ ↦ diag(a σ, d σ)`. -/
def diagHom (a d : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ) : ZInQ.Contrib.G9.PkgI4.GQ →* GL (Fin 2) (PadicAlgCl ℓ) where
  toFun σ := ⟨!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)],
    !![(((a σ)⁻¹ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ), 0; 0, (((d σ)⁻¹ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)],
    by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  map_one' := Units.ext (by simp [Matrix.one_fin_two])
  map_mul' σ τ := Units.ext (by simp [Matrix.mul_fin_two])

theorem diagHom_val (a d : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    ((diagHom a d σ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
      !![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)] := rfl

/-- A diagonal representation is semisimple. -/
theorem isSemisimple_diag (a d : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ)
    (W : Submodule (PadicAlgCl ℓ) (Fin 2 → PadicAlgCl ℓ))
    (hW : ∀ σ, W.map (Matrix.toLin' (!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)])) ≤ W) :
    ∃ W', IsCompl W W' ∧ ∀ σ,
      W'.map (Matrix.toLin' (!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)])) ≤ W' := by
  classical
  -- the coordinate lines
  let e0 : Fin 2 → PadicAlgCl ℓ := ![1, 0]
  let e1 : Fin 2 → PadicAlgCl ℓ := ![0, 1]
  have hdiag : ∀ σ (x : Fin 2 → PadicAlgCl ℓ),
      Matrix.toLin' (!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)]) x =
        ![(a σ : PadicAlgCl ℓ) * x 0, (d σ : PadicAlgCl ℓ) * x 1] := by
    intro σ x; ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hline0 : ∀ σ, (PadicAlgCl ℓ ∙ e0).map (Matrix.toLin'
      (!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)])) ≤ (PadicAlgCl ℓ ∙ e0) := by
    intro σ
    rw [Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem, Submodule.mem_comap,
      hdiag, Submodule.mem_span_singleton]
    exact ⟨(a σ : PadicAlgCl ℓ), by ext i; fin_cases i <;> simp [e0]⟩
  have hline1 : ∀ σ, (PadicAlgCl ℓ ∙ e1).map (Matrix.toLin'
      (!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)])) ≤ (PadicAlgCl ℓ ∙ e1) := by
    intro σ
    rw [Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem, Submodule.mem_comap,
      hdiag, Submodule.mem_span_singleton]
    exact ⟨(d σ : PadicAlgCl ℓ), by ext i; fin_cases i <;> simp [e1]⟩
  have hc01 : IsCompl (PadicAlgCl ℓ ∙ e0) (PadicAlgCl ℓ ∙ e1) := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      obtain ⟨⟨c, rfl⟩, ⟨c', hc'⟩⟩ := (Submodule.mem_inf.mp hx).imp Submodule.mem_span_singleton.mp
        Submodule.mem_span_singleton.mp
      have h0 := congrFun hc' 0
      have h1 := congrFun hc' 1
      simp [e0, e1] at h0 h1
      rw [Submodule.mem_bot]
      ext i; fin_cases i <;> simp [e0, ← h0]
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have : x = x 0 • e0 + x 1 • e1 := by ext i; fin_cases i <;> simp [e0, e1]
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self _)))
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  by_cases hsc : ∀ σ, (a σ : PadicAlgCl ℓ) = d σ
  · -- scalar: every subspace is invariant
    obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
    refine ⟨W', hW', fun σ => ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hdiag, ← hsc σ]
    have : ![(a σ : PadicAlgCl ℓ) * x 0, (a σ : PadicAlgCl ℓ) * x 1] = (a σ : PadicAlgCl ℓ) • x := by
      ext i; fin_cases i <;> simp
    rw [this]
    exact W'.smul_mem _ hx
  push_neg at hsc
  obtain ⟨σ₀, hσ₀⟩ := hsc
  by_cases htop : W = ⊤
  · exact ⟨⊥, by rw [htop]; exact isCompl_top_bot, fun σ => by simp⟩
  by_cases hbot : W = ⊥
  · exact ⟨⊤, by rw [hbot]; exact isCompl_bot_top, fun σ => le_top⟩
  -- every vector of `W` lies on a coordinate line
  have key : ∀ z ∈ W, z 0 = 0 ∨ z 1 = 0 := by
    intro z hz
    by_contra h
    push_neg at h
    apply htop
    have hz' : ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1] ∈ W := by
      rw [← hdiag]; exact hW σ₀ ⟨z, hz, rfl⟩
    have hsub : (a σ₀ : PadicAlgCl ℓ) ≠ d σ₀ := hσ₀
    have he0 : e0 ∈ W := by
      have hm : (d σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1] ∈ W :=
        W.sub_mem (W.smul_mem _ hz) hz'
      have hne : ((d σ₀ : PadicAlgCl ℓ) - a σ₀) * z 0 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr (Ne.symm hsub)) h.1
      have hv : (d σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1] =
          (((d σ₀ : PadicAlgCl ℓ) - a σ₀) * z 0) • e0 := by
        ext i; fin_cases i
        · simp [e0, Matrix.vecHead]; ring
        · simp [e0, Matrix.vecHead, Matrix.vecTail]
      have : e0 = (((d σ₀ : PadicAlgCl ℓ) - a σ₀) * z 0)⁻¹ •
          ((d σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1]) := by
        rw [hv, inv_smul_smul₀ hne]
      rw [this]; exact W.smul_mem _ hm
    have he1 : e1 ∈ W := by
      have hm : (a σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1] ∈ W :=
        W.sub_mem (W.smul_mem _ hz) hz'
      have hne : ((a σ₀ : PadicAlgCl ℓ) - d σ₀) * z 1 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr hsub) h.2
      have hv : (a σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1] =
          (((a σ₀ : PadicAlgCl ℓ) - d σ₀) * z 1) • e1 := by
        ext i; fin_cases i
        · simp [e1, Matrix.vecHead]
        · simp [e1, Matrix.vecHead, Matrix.vecTail]; ring
      have : e1 = (((a σ₀ : PadicAlgCl ℓ) - d σ₀) * z 1)⁻¹ •
          ((a σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1]) := by
        rw [hv, inv_smul_smul₀ hne]
      rw [this]; exact W.smul_mem _ hm
    rw [eq_top_iff]
    intro x _
    have : x = x 0 • e0 + x 1 • e1 := by ext i; fin_cases i <;> simp [e0, e1]
    rw [this]
    exact W.add_mem (W.smul_mem _ he0) (W.smul_mem _ he1)
  by_cases h0 : ∀ x ∈ W, x 1 = 0
  · have hle : W ≤ PadicAlgCl ℓ ∙ e0 := by
      intro x hx
      rw [Submodule.mem_span_singleton]
      exact ⟨x 0, by ext i; fin_cases i <;> simp [e0, h0 x hx]⟩
    have hge : PadicAlgCl ℓ ∙ e0 ≤ W := by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      have hx00 : x 0 ≠ 0 := by
        intro h; apply hx0; ext i; fin_cases i <;> simp [h, h0 x hx]
      rw [Submodule.span_singleton_le_iff_mem]
      have : e0 = (x 0)⁻¹ • x := by ext i; fin_cases i <;> simp [e0, h0 x hx, hx00]
      rw [this]; exact W.smul_mem _ hx
    have hWe : W = PadicAlgCl ℓ ∙ e0 := le_antisymm hle hge
    exact ⟨PadicAlgCl ℓ ∙ e1, hWe ▸ hc01, hline1⟩
  push_neg at h0
  obtain ⟨x, hx, hx1⟩ := h0
  have hx0 : x 0 = 0 := (key x hx).resolve_right hx1
  by_cases h1 : ∀ y ∈ W, y 0 = 0
  · have hle : W ≤ PadicAlgCl ℓ ∙ e1 := by
      intro y hy
      rw [Submodule.mem_span_singleton]
      exact ⟨y 1, by ext i; fin_cases i <;> simp [e1, h1 y hy]⟩
    have hge : PadicAlgCl ℓ ∙ e1 ≤ W := by
      rw [Submodule.span_singleton_le_iff_mem]
      have : e1 = (x 1)⁻¹ • x := by ext i; fin_cases i <;> simp [e1, hx0, hx1]
      rw [this]; exact W.smul_mem _ hx
    have hWe : W = PadicAlgCl ℓ ∙ e1 := le_antisymm hle hge
    exact ⟨PadicAlgCl ℓ ∙ e0, hWe ▸ hc01.symm, hline0⟩
  push_neg at h1
  obtain ⟨y, hy, hy0⟩ := h1
  have hy1 : y 1 = 0 := (key y hy).resolve_left hy0
  rcases key (x + y) (W.add_mem hx hy) with h | h
  · exact absurd (by simpa [hx0] using h) hy0
  · exact absurd (by simpa [hy1] using h) hx1

theorem mulVec_e0 (M : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) (i : Fin 2) :
    (M.mulVec ![1, 0]) i = M i 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **`Semisimplification2`, proved.** If `ρ` is not semisimple it has an invariant line; in a
basis through it `ρ` is upper triangular `(a ∗; 0 d)`, and `diag(a, d)` is the semisimplification. -/
theorem semisimplification2_proof : Semisimplification2 := by
  intro ℓ _ ρ
  classical
  by_cases hss : ρ.IsSemisimple
  · exact ⟨ρ, hss, fun _ => rfl, fun _ h => h⟩
  -- an invariant subspace without invariant complement
  have hss' := hss
  simp only [GaloisRep.IsSemisimple, not_forall, not_exists, not_and] at hss'
  obtain ⟨W, hW, hno⟩ := hss'
  have hWbot : W ≠ ⊥ := by
    rintro rfl
    obtain ⟨σ, hσ⟩ := hno ⊤ isCompl_bot_top
    exact hσ le_top
  have hWtop : W ≠ ⊤ := by
    rintro rfl
    obtain ⟨σ, hσ⟩ := hno ⊥ isCompl_top_bot
    exact hσ (by simp)
  obtain ⟨w, hwW, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
  have hfin : Module.finrank (PadicAlgCl ℓ) W = 1 := by
    have h2 : Module.finrank (PadicAlgCl ℓ) W ≤ 2 := by
      have := Submodule.finrank_le W
      simpa using this
    have h0 : Module.finrank (PadicAlgCl ℓ) W ≠ 0 := by
      intro h; exact hWbot (Submodule.finrank_eq_zero.mp h)
    have h2' : Module.finrank (PadicAlgCl ℓ) W ≠ 2 := by
      intro h; apply hWtop
      apply Submodule.eq_top_of_finrank_eq
      simp [h]
    omega
  have hmul : ∀ v ∈ W, ∃ c : PadicAlgCl ℓ, c • w = v := by
    intro v hv
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwW⟩ : W)
      (fun h => hw (congrArg Subtype.val h))).mp hfin ⟨v, hv⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have heig : ∀ σ, ∃ c : PadicAlgCl ℓ, (ρ.mat σ).mulVec w = c • w := by
    intro σ
    obtain ⟨c, hc⟩ := hmul _ (hW σ ⟨w, hwW, rfl⟩)
    exact ⟨c, by rw [hc, Matrix.toLin'_apply]⟩
  -- a basis through `w`
  let u : Fin 2 → PadicAlgCl ℓ := if w 0 ≠ 0 then ![0, 1] else ![1, 0]
  let P : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) := !![w 0, u 0; w 1, u 1]
  have hdet : P.det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    by_cases h0 : w 0 ≠ 0
    · simp [u, h0]
    · have hw0 : w 0 = 0 := not_not.mp h0
      have h1 : w 1 ≠ 0 := by
        intro h1; apply hw; ext i; fin_cases i <;> simp [hw0, h1]
      simp [u, hw0, h1]
  let Pu : GL (Fin 2) (PadicAlgCl ℓ) := Matrix.nonsingInvUnit P (Ne.isUnit hdet)
  let Q : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) := ((Pu⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix _ _ _)
  have hQP : Q * P = 1 := by
    change (Pu⁻¹).val * Pu.val = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPQ : P * Q = 1 := by
    change Pu.val * (Pu⁻¹).val = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let T : ZInQ.Contrib.G9.PkgI4.GQ → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) := fun σ => Q * ρ.mat σ * P
  have hPe0 : P.mulVec ![1, 0] = w := by
    ext i; rw [mulVec_e0]; fin_cases i <;> simp [P]
  have hT10 : ∀ σ, T σ 1 0 = 0 := by
    intro σ
    obtain ⟨c, hc⟩ := heig σ
    have h1 : (T σ).mulVec ![1, 0] = c • ![1, 0] := by
      simp only [T, ← Matrix.mulVec_mulVec, hPe0, hc, Matrix.mulVec_smul]
      rw [← hPe0, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
    have := congrFun h1 1
    rw [mulVec_e0] at this
    simpa using this
  have hmatmul : ∀ σ τ, ρ.mat (σ * τ) = ρ.mat σ * ρ.mat τ := by
    intro σ τ; simp [GaloisRep.mat]
  have hTmul : ∀ σ τ, T (σ * τ) = T σ * T τ := by
    intro σ τ
    simp only [T, hmatmul]
    rw [show Q * ρ.mat σ * P * (Q * ρ.mat τ * P) = Q * ρ.mat σ * (P * Q) * ρ.mat τ * P by
      simp only [mul_assoc], hPQ, mul_one]
    simp only [mul_assoc]
  have hT1 : T 1 = 1 := by simp [T, GaloisRep.mat, hQP]
  have hdetT : ∀ σ, (T σ).det = T σ 0 0 * T σ 1 1 := by
    intro σ; rw [Matrix.det_fin_two, hT10]; ring
  have hdetT' : ∀ σ, (T σ).det ≠ 0 := by
    intro σ
    simp only [T, Matrix.det_mul]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hdet
    · intro h
      have := congrArg Matrix.det hQP
      rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    · exact (Matrix.isUnit_iff_isUnit_det _).mp (ρ.toHom σ).isUnit |>.ne_zero
  have ha0 : ∀ σ, T σ 0 0 ≠ 0 := fun σ h => hdetT' σ (by rw [hdetT, h, zero_mul])
  have hd0 : ∀ σ, T σ 1 1 ≠ 0 := fun σ h => hdetT' σ (by rw [hdetT, h, mul_zero])
  let a : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
    { toFun := fun σ => Units.mk0 (T σ 0 0) (ha0 σ)
      map_one' := Units.ext (by simp [hT1])
      map_mul' := fun σ τ => Units.ext (by
        simp only [Units.val_mk0, Units.val_mul, hTmul, Matrix.mul_apply, Fin.sum_univ_two, hT10]
        ring) }
  let d : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
    { toFun := fun σ => Units.mk0 (T σ 1 1) (hd0 σ)
      map_one' := Units.ext (by simp [hT1])
      map_mul' := fun σ τ => Units.ext (by
        simp only [Units.val_mk0, Units.val_mul, hTmul, Matrix.mul_apply, Fin.sum_univ_two, hT10]
        ring) }
  have hTc : Continuous T :=
    (continuous_const.matrix_mul (Units.continuous_val.comp ρ.continuous_toHom)).matrix_mul
      continuous_const
  have hac : Continuous fun σ => (a σ : PadicAlgCl ℓ) := hTc.matrix_elem 0 0
  have hdc : Continuous fun σ => (d σ : PadicAlgCl ℓ) := hTc.matrix_elem 1 1
  have hdiagc : ∀ (f g : ZInQ.Contrib.G9.PkgI4.GQ → PadicAlgCl ℓ), Continuous f → Continuous g →
      Continuous fun σ => !![f σ, 0; 0, g σ] := by
    intro f g hf hg
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j
    · simpa using hf
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using hg
  have hcont : Continuous (diagHom a d) := by
    rw [Units.continuous_iff]
    refine ⟨hdiagc _ _ hac hdc, ?_⟩
    have : (fun σ => (((diagHom a d σ)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)))
        = fun σ => !![(a σ⁻¹ : PadicAlgCl ℓ), 0; 0, (d σ⁻¹ : PadicAlgCl ℓ)] := by
      funext σ; rw [← map_inv]; rfl
    rw [this]
    exact hdiagc _ _ (hac.comp continuous_inv) (hdc.comp continuous_inv)
  let ρ' : GaloisRep ℓ 2 := ⟨diagHom a d, hcont⟩
  have hρ'mat : ∀ σ, ρ'.mat σ = !![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)] := fun σ => rfl
  have hρT : ∀ σ, ρ.mat σ = P * T σ * Q := by
    intro σ
    simp only [T]
    rw [show P * (Q * ρ.mat σ * P) * Q = (P * Q) * ρ.mat σ * (P * Q) by simp only [mul_assoc],
      hPQ, one_mul, mul_one]
  refine ⟨ρ', fun W' hW' => ?_, fun σ => ?_, fun p hu => ?_⟩
  · simp only [hρ'mat] at hW' ⊢
    exact isSemisimple_diag a d W' hW'
  · rw [charpoly_fin_two', charpoly_fin_two', hρ'mat, hρT]
    have htr : (P * T σ * Q).trace = (T σ).trace := by
      rw [Matrix.trace_mul_comm, ← mul_assoc, hQP, one_mul]
    have hdt : (P * T σ * Q).det = (T σ).det := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, hPQ,
        Matrix.det_one, mul_one]
    rw [htr, hdt, hdetT]
    simp [Matrix.trace_fin_two, Matrix.det_fin_two, a, d]
  · intro v hv σ hσ
    have h1 := hu v hv σ hσ
    apply Units.ext
    change !![(a _ : PadicAlgCl ℓ), 0; 0, (d _ : PadicAlgCl ℓ)] = 1
    have hTσ : T ((σ : v.decompositionSubgroup ℚ) : ZInQ.Contrib.G9.PkgI4.GQ) = 1 := by
      simp only [T, GaloisRep.mat, h1, Units.val_one, mul_one, hQP]
    rw [Matrix.one_fin_two]
    simp [a, d, hTσ]


end SS

/-- **H-22 closed.** `R14Det` from the two printed theorems `DSThm965` (Deligne, via Diamond–Shurman
Thm 9.6.5) and `DSThm966` (Deligne–Serre, via Diamond–Shurman Thm 9.6.6) only. -/
theorem r14Det_of_printed (hD : DSThm965) (hDS : DSThm966) : G0Galois.R14Det :=
  r14Det_of_wt (artinTransport_proof hDS)
    (r14DetWtGe2_of_ds hD semisimplification2_proof detFromFrobenius_proof)

end R14Closed

end

end ZInQ.Contrib.HodgeSplit

#print axioms ZInQ.Contrib.HodgeSplit.attachedConj_proof
#print axioms ZInQ.Contrib.HodgeSplit.detFromFrobenius_proof
#print axioms ZInQ.Contrib.HodgeSplit.artinTransport_proof
#print axioms ZInQ.Contrib.HodgeSplit.r14Det_of_printed
