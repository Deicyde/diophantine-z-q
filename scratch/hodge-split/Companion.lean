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

end

end ZInQ.Contrib.HodgeSplit

#print axioms ZInQ.Contrib.HodgeSplit.attachedConj_proof
#print axioms ZInQ.Contrib.HodgeSplit.detFromFrobenius_proof
