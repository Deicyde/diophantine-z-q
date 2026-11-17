import ZInQKernel.Contrib.OneProof.BergerBst
import ZInQKernel.Contrib.OneProof.DSThm966EV
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# `r11r12` from Pan 2022 Thm 1.0.4 and Berger 2002 Thm 0.7 with printed hypotheses and conclusion (task pb-fix3)

bst-construct's `PanPrintedB` was pb-fix2's `PanPrintedU` with potential semistability over Berger's `B_st`. Its
Hodge–Tate hypothesis was finrank-based (`htMultU = dim_{ℚ_p} / [E : ℚ_p]`, a natural-number division), its
irreducibility hypothesis was the kernel's Burnside form, and its conclusion used the kernel's coefficient-form
predicate `IsNormalizedEigenform`. This file restates Pan's theorem with every hypothesis and the conclusion as
printed (`PanPrintedP`) and proves in Lean the dictionaries the consumer needs:

* **Hodge–Tate weights** (`htMultE`, `LocalDistinctHTP`): the multiplicity of `w` is
  `dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` on a model `V = E^n` (cyclotomic weight `−1`). `htMultE_eq_htMultU` and
  `localDistinctHTP_iff` prove it equal to the finrank form (`dim_{ℚ_p} W = [E : ℚ_p] · dim_E W`).
* **Irreducible** (`IsIrreducibleP`): no stable subspace of `ℚ̄_p²` but `0` and the whole space;
  `isIrreducibleP_of`: the Burnside form implies it.
* **"Comes from a cuspidal eigenform up to twist"**: a cuspidal eigenform `g` (Tau Ceti's
  `EigenformAwayFromLevel`), the representation `ρ_g` attached to it through `ι_p` (`IsAttachedVia`: geometric
  Frobenius traces `ι_p⁻¹(λ_q(g))` at almost all `q`), and `ρ ≅ ρ_g ⊗ ψ` (`IsTwistOf`).
  `exists_normalized_of_eigenform` passes to the newform of the eigensystem (Tau Ceti, Diamond–Shurman
  Prop. 5.8.4), a normalized full eigenform, hence `IsNormalizedEigenform` with `a_q = λ_q(g)` for `q ∤ N`
  (`DSCoeffExt.isNormalizedEigenform_of_DS`); `exists_eigenform_of_normalized` is the converse; `one_le_weight`
  gives `k ≥ 1`; `trace_of_twist` gives the trace form.

`panPrintedB_of_printedP` proves bst-construct's `PanPrintedB` from `PanPrintedP`. Berger's leaf is restated for
one continuous `ρ_E : G_{ℚ_p} → GL_n(E)` (`BergerPrintedV`: a `p`-adic representation `V = E^n`), and
`bergerPrintedB_of_V` proves bst-construct's `BergerPrintedB` from it (`continuous_model`).
`panBerger_of_printedPV` discharges `r11r12 : PanBerger` from the two printed leaves and the current bundle's
fields `dsThm965Printed`, `eigenformCoeffFieldFinite` and `dsThm966Printed`.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace PanDict

open Module
open scoped TensorProduct Matrix
open PanBergerSplit BergerBst

/-! ## §1. Hodge–Tate weights as printed: `dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` -/

section HT

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

theorem tensorMap_smul (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (f : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p])
    (c : E) (x : (Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) :
    TensorProduct.map (vAct p ρ σ) f (c • x) = c • TensorProduct.map (vAct p ρ σ) f x := by
  induction x using TensorProduct.inductionOn with
  | tmul v z =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', vAct_apply, vAct_apply, Matrix.mulVec_smul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **`(V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}`** for the `E`-linear representation `V = E^n` (action `ρ`), as an
`E`-subspace (`E` acting on `V`). -/
def htSpaceE (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    Submodule E ((Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) where
  carrier := {x | ∀ σ : GQp p, TensorProduct.map (vAct p ρ σ) (htLin p w σ) x = x}
  zero_mem' σ := map_zero _
  add_mem' {x y} hx hy σ := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, hx σ, hy σ]
  smul_mem' c x hx σ := by
    simp only [Set.mem_ofPred_eq] at *
    rw [tensorMap_smul, hx σ]

/-- **Multiplicity of the Hodge–Tate weight `w`** of the `E`-linear `V`, as printed:
`dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` (the cyclotomic character has weight `−1`, Pan's convention). -/
def htMultE (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : ℕ := finrank E (htSpaceE p ρ w)

/-- **`ρ|_{G_{ℚ_p}}` is Hodge–Tate with distinct Hodge–Tate weights** (dimension 2), as printed: in a
model over a finite `E ⊆ ℚ̄_p`, the Hodge–Tate weights with their multiplicities
`dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` are two distinct integers `a ≠ b`. -/
def LocalDistinctHTP (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)) : Prop :=
  ∃ a b : ℤ, a ≠ b ∧ ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin 2) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    ∀ w : ℤ, htMultE p ρE w = Multiset.count w {a, b}

/-- `ℂ_p ⊗ V ≅ V ⊗ ℂ_p` carries pb-fix2's `htU` onto `htSpaceE`. -/
theorem map_comm_htU (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    (htU p ρ w).map (TensorProduct.comm ℚ_[p] ℂ_[p] (Fin n → E)).toLinearMap =
      (htSpaceE p ρ w).restrictScalars ℚ_[p] := by
  ext x
  simp only [Submodule.mem_map, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩ σ
    have h := hy σ (Subgroup.mem_top σ)
    change TensorProduct.map (vAct p ρ σ) (htLin p w σ) (TensorProduct.comm ℚ_[p] _ _ y) =
      TensorProduct.comm ℚ_[p] _ _ y
    rw [TensorProduct.map_comm, h]
  · intro hx
    refine ⟨(TensorProduct.comm ℚ_[p] ℂ_[p] (Fin n → E)).symm x, fun σ _ => ?_, by simp⟩
    apply (TensorProduct.comm ℚ_[p] ℂ_[p] (Fin n → E)).injective
    rw [← TensorProduct.map_comm, LinearEquiv.apply_symm_apply]
    exact hx σ

/-- **The printed multiplicity is pb-fix2's finrank form**: `dim_E W = dim_{ℚ_p} W / [E : ℚ_p]`. -/
theorem htMultE_eq_htMultU [FiniteDimensional ℚ_[p] E] (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    htMultE p ρ w = htMultU p ρ w := by
  have h1 : finrank ℚ_[p] (htU p ρ w) = finrank ℚ_[p] ((htSpaceE p ρ w).restrictScalars ℚ_[p]) := by
    rw [← map_comm_htU, LinearEquiv.finrank_map_eq]
  have h2 : finrank ℚ_[p] ((htSpaceE p ρ w).restrictScalars ℚ_[p]) =
      finrank ℚ_[p] E * finrank E (htSpaceE p ρ w) := by
    have : Module.Free ℚ_[p] E := Module.Free.of_divisionRing _ _
    have : Module.Free E (htSpaceE p ρ w) := @Module.Free.of_divisionRing E (htSpaceE p ρ w) _ _ _
    rw [(((htSpaceE p ρ w).restrictScalarsEquiv ℚ_[p]).restrictScalars ℚ_[p]).finrank_eq,
      Module.finrank_mul_finrank]
  have hE : 0 < finrank ℚ_[p] E := Module.finrank_pos
  rw [htMultU, h1, h2, Nat.mul_div_cancel_left _ hE, htMultE]

/-- **Dictionary**: the printed "Hodge–Tate with distinct weights" is pb-fix2's finrank form. -/
theorem localDistinctHTP_iff (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)) :
    LocalDistinctHTP p ρ ↔ LocalDistinctHTU p ρ := by
  constructor
  · rintro ⟨a, b, hab, E, hE, ρE, hmod, hw⟩
    exact ⟨a, b, hab, E, hE, ρE, hmod, fun w => (htMultE_eq_htMultU p ρE w).symm.trans (hw w)⟩
  · rintro ⟨a, b, hab, E, hE, ρE, hmod, hw⟩
    exact ⟨a, b, hab, E, hE, ρE, hmod, fun w => (htMultE_eq_htMultU p ρE w).trans (hw w)⟩

end HT

/-! ## §2. Irreducibility as printed -/

section Irred

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- **`ρ` is irreducible** (as printed): no `ℚ̄_ℓ`-subspace of `ℚ̄_ℓ^n` other than `0` and the whole space
is stable under every `ρ(σ)`. -/
def IsIrreducibleP (ρ : GaloisRep ℓ n) : Prop :=
  ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
    (∀ σ, ∀ v ∈ W, (ρ.mat σ) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

/-- The kernel's Burnside form (the image spans `M_n(ℚ̄_ℓ)`) implies irreducibility as printed. -/
theorem isIrreducibleP_of (ρ : GaloisRep ℓ n) (h : ρ.IsIrreducible) : IsIrreducibleP ρ := by
  intro W hW
  let S : Subalgebra (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) :=
    { carrier := {M | ∀ v ∈ W, M *ᵥ v ∈ W}
      mul_mem' := fun {M M'} hM hM' v hv => by
        show (M * M') *ᵥ v ∈ W
        rw [← Matrix.mulVec_mulVec]
        exact hM _ (hM' v hv)
      add_mem' := fun {M M'} hM hM' v hv => by
        show (M + M') *ᵥ v ∈ W
        rw [Matrix.add_mulVec]
        exact W.add_mem (hM v hv) (hM' v hv)
      algebraMap_mem' := fun r v hv => by
        show (algebraMap (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) r) *ᵥ v ∈ W
        rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact W.smul_mem r hv }
  have hle : Algebra.adjoin (PadicAlgCl ℓ) (Set.range ρ.mat) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨σ, rfl⟩
    exact hW σ
  rw [h] at hle
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv0 (funext hc)
    rw [eq_top_iff]
    intro u _
    have hM : Matrix.vecMulVec u (Pi.single j (v j)⁻¹) ∈ S := hle Algebra.mem_top
    have h1 := hM v hv
    rwa [Matrix.vecMulVec_mulVec, single_dotProduct, inv_mul_cancel₀ hj, MulOpposite.op_one,
      one_smul] at h1

end Irred

/-! ## §3. The modular side as printed: a cuspidal eigenform, its representation through `ι_p`, a twist -/

section Modular

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup

/-- A nonzero cusp form on `Γ₁(N)` has weight `≥ 1` (cusp forms of negative weight vanish, Mathlib's
`ModularForm.isZero_of_neg_weight`; in weight `0` they are constant, `ModularForm.eq_const_of_weight_zero`,
and vanish at `i∞`). -/
theorem one_le_weight {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ≠ 0) : 1 ≤ k := by
  by_contra hk
  push Not at hk
  rcases lt_or_eq_of_le (show k ≤ 0 by omega) with hneg | rfl
  · apply hf
    apply CuspForm.toModularFormₗ_injective
    rw [map_zero]
    exact ModularForm.isZero_of_neg_weight hneg _
  · obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero (CuspForm.toModularFormₗ f)
    have hc' : (f : ℍ → ℂ) = Function.const ℍ c := hc
    have hz : IsZeroAtImInfty (f : ℍ → ℂ) :=
      OnePoint.isZeroAt_infty_iff.mp (CuspFormClass.zero_at_cusps f Fact.out)
    rw [hc'] at hz
    have h0 : c = 0 := tendsto_const_nhds_iff.mp hz
    apply hf
    ext τ
    rw [hc', h0]
    rfl

variable (p : ℕ) [Fact p.Prime]

/-- **`ρ_g` is the `p`-adic representation attached to the cuspidal eigenform `g` through `ι_p`**, in Pan's
normalization (geometric Frobenius): outside a finite set of primes `q ∤ N`, `ρ_g` is unramified at `q` and
`tr ρ_g(Frob_q) = ι_p⁻¹(λ_q(g))`, with `Frob_q = σ⁻¹` for any arithmetic Frobenius `σ` at any place
`v ∣ q`, and `λ_q(g)` the `T_q`-eigenvalue of `g`. -/
def IsAttachedVia (ιp : PadicAlgCl p ≃+* ℂ) {N : ℕ} [NeZero N] {k : ℤ}
    (g : EigenformAwayFromLevel N k) (ρg : GaloisRep p 2) : Prop :=
  ∃ S : Finset ℕ, ∀ (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N), q ∉ S →
    ρg.UnramifiedAt q ∧
    ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
      (ρg.mat σ⁻¹).trace =
        ιp.symm (g.eigenvalue (q.toPNat hq.pos) (DSThm966EV.coprime_of_not_dvd hq hqN))

/-- **`ρ ≅ ρ_g ⊗ ψ`**: `ρ` is the twist of `ρ_g` by the character `ψ`, up to isomorphism (a change of basis
`P ∈ GL₂(ℚ̄_p)`). -/
def IsTwistOf (ρ ρg : GaloisRep p 2) (ψ : GaloisChar p) : Prop :=
  ∃ P : GL (Fin 2) (PadicAlgCl p), ∀ σ : GQ,
    ρ.mat σ = (ψ.toHom σ : PadicAlgCl p) •
      ((P : Matrix (Fin 2) (Fin 2) (PadicAlgCl p)) * ρg.mat σ * ((P⁻¹ : GL (Fin 2) (PadicAlgCl p)) :
        Matrix (Fin 2) (Fin 2) (PadicAlgCl p)))

theorem trace_of_twist {ρ ρg : GaloisRep p 2} {ψ : GaloisChar p} (h : IsTwistOf p ρ ρg ψ) (σ : GQ) :
    (ρ.mat σ).trace = (ψ.toHom σ : PadicAlgCl p) * (ρg.mat σ).trace := by
  obtain ⟨P, hP⟩ := h
  rw [hP σ, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-- **Dictionary (eigenform → normalized eigenform)**: a cuspidal eigenform away from the level has the
eigenvalues of a normalized eigenform in the kernel's coefficient form (`IsNormalizedEigenform`), at some
level `M ∣ N`: the newform of the eigensystem (Tau Ceti's `exists_newform_eigenvalue_eq`, Diamond–Shurman
Prop. 5.8.4), which is a full eigenform (`Newform.toEigenform`) with `a₁ = 1`, then
`DSCoeffExt.isNormalizedEigenform_of_DS`. -/
theorem exists_normalized_of_eigenform {N : ℕ} [NeZero N] {k : ℤ} (g : EigenformAwayFromLevel N k) :
    ∃ (M : ℕ) (χ : DirichletCharacter ℂ M) (g' : CF M k), 0 < M ∧ 1 ≤ k ∧
      IsNormalizedEigenform g' χ ∧
      ∀ (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N),
        coeff g' q = g.eigenvalue (q.toPNat hq.pos) (DSThm966EV.coprime_of_not_dvd hq hqN) := by
  obtain ⟨M, hM0, hMN, h, hev⟩ := g.exists_newform_eigenvalue_eq
  refine ⟨M, MulChar.ofUnitHom h.χ, h.toCuspForm, Nat.pos_of_ne_zero (NeZero.ne M),
    one_le_weight g.toCuspForm g.ne_zero, ?_, fun q hq hqN => ?_⟩
  · apply DSCoeffExt.isNormalizedEigenform_of_DS
    refine ⟨h.toEigenform, Newform.toEigenform_toCuspForm h, ?_, h.isNorm⟩
    rw [Newform.toEigenform_χ]
    exact (MulChar.equivToUnitHom.apply_symm_apply h.χ).symm
  · have hc := (DSThm966EV.coprime_of_not_dvd hq hqN).coprime_dvd_right hMN
    have h1 := hev q hq (DSThm966EV.coprime_of_not_dvd hq hqN)
    have h2 := Newform.toEigenform_eigenvalue_eq_qExpansion_coeff h (q.toPNat hq.pos)
    have h3 : h.toEigenform.eigenvalue (q.toPNat hq.pos) = h.eigenvalue (q.toPNat hq.pos) hc := by
      have := congrArg (fun F : EigenformAwayFromLevel M k => F.eigenvalue (q.toPNat hq.pos) hc)
        (Newform.toEigenform_toEigenformAwayFromLevel h)
      exact this
    change (qExpansion 1 h.toCuspForm).coeff q = _
    change _ = (qExpansion 1 h.toCuspForm).coeff q at h2
    rw [← h2, h3]
    exact h1

/-- **Dictionary, converse**: a normalized eigenform in the kernel's coefficient form is a cuspidal eigenform
away from the level with eigenvalues `a_q`. With `exists_normalized_of_eigenform`, the two ways of stating
"some eigenform with eigenvalues `a_q` (`q ∤ N`)" are equivalent. -/
theorem exists_eigenform_of_normalized {M : ℕ} [NeZero M] {k : ℤ} {χ : DirichletCharacter ℂ M}
    {g' : CF M k} (hg : IsNormalizedEigenform g' χ) :
    ∃ g : EigenformAwayFromLevel M k, g.toCuspForm = g' ∧
      ∀ (q : ℕ) (hq : q.Prime) (hqM : ¬ q ∣ M),
        g.eigenvalue (q.toPNat hq.pos) (DSThm966EV.coprime_of_not_dvd hq hqM) = coeff g' q := by
  obtain ⟨F, hF, -, h1⟩ := DSCoeffExt.isNormalizedEigenformDS_of hg
  refine ⟨F.toEigenformAwayFromLevel, hF, fun q hq hqM => ?_⟩
  rw [Eigenform.toEigenformAwayFromLevel_eigenvalue]
  have h2 := F.qExpansion_coeff_eq_eigenvalue_mul_coeff_one ⟨q, hq.pos⟩
  have h1' : (qExpansion 1 F.toCuspForm).coeff 1 = 1 := by rw [hF]; exact h1
  rw [h1', mul_one] at h2
  rw [← hF]
  exact h2.symm

end Modular

/-! ## §4. The printed leaves -/

/-- **Pan, Theorem 1.0.4, printed form** (L. Pan, *The Fontaine–Mazur conjecture in the residually reducible
case*, J. Amer. Math. Soc. 35 (2022), 1031-1169; = arXiv:1901.07166v2, Theorem 1.0.4 with Conjecture 1.0.1,
pp. 5 and 2 (statement read from the TeX by h-a011 §1.1 and rv-h-a011 §2, FM.tex L167-177, L226-233; conventions
L253, L268, L270); JAMS numbering and page UNVERIFIED), for `p ≥ 5` and Pan's fixed `ι_p : ℚ̄_p ≅ ℂ` (for each
`ι_p`). Hypotheses on one continuous `ρ : G_ℚ → GL₂(ℚ̄_p)`, each as printed:

* irreducible (`IsIrreducibleP`: no stable subspace other than `0` and `ℚ̄_p²`);
* ramified at finitely many primes (`FinitelyRamified`);
* `ρ|_{G_{ℚ_p}}` potentially semistable in the sense of Fontaine (`LocalIsPstB`: `B_st`-admissible over some
  finite `K/ℚ_p`, Berger's `B_st = B_max[log [p̃]] ⊆ B_dR`, bst-construct);
* odd (`IsOdd`: `det ρ(c) = −1` for every complex conjugation `c`);
* `ρ|_{G_{ℚ_p}}` has distinct Hodge–Tate weights (`LocalDistinctHTP`: the weights, with multiplicity
  `dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` on a model `V = E^n`, are two distinct integers; the cyclotomic character
  has weight `−1`, Pan's convention).

Conclusion, "`ρ` comes from a cuspidal eigenform up to twist", as printed: a cuspidal eigenform `g` (Tau Ceti's
`EigenformAwayFromLevel N k`: a nonzero cusp form on `Γ₁(N)` with a nebentypus, an eigenvector of the Hecke
operators `T_n`, `n` prime to `N`), the representation `ρ_g` attached to `g` through `ι_p` in Pan's
normalization (`IsAttachedVia`: `tr ρ_g(Frob_q) = ι_p⁻¹(λ_q(g))` with `Frob_q` the geometric Frobenius, for almost
all `q`), and a continuous character `ψ` with `ρ ≅ ρ_g ⊗ ψ` (`IsTwistOf`).

Readings (flags): "cuspidal eigenform" is read in its weakest sense (eigen for the `T_n`, `n` prime to the
level; a full eigenform or a newform is in particular one); `ρ_g` is pinned only by its Frobenius traces at
almost all primes and unramifiedness there (the weakest form of "attached"), with Pan's geometric-Frobenius
normalization (L253/L270, read by h-a011; the formula `tr ρ_g(Frob_q) = ι_p⁻¹ λ_q` itself is UNVERIFIED here). -/
def PanPrintedP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    IsIrreducibleP ρ → ρ.FinitelyRamified → LocalIsPstB p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTP p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (_ : NeZero N) (k : ℤ) (g : HeckeRing.GL2.EigenformAwayFromLevel N k)
      (ρg : GaloisRep p 2) (ψ : GaloisChar p),
      IsAttachedVia p ιp g ρg ∧ IsTwistOf p ρ ρg ψ

/-- **bst-construct's `PanPrintedB` from the printed leaf.** Irreducibility (Burnside ⇒ printed), the
Hodge–Tate condition (finrank form ⇔ printed, `localDistinctHTP_iff`), the eigenform
(`exists_normalized_of_eigenform`) and the trace form (`trace_of_twist`) are glue proved here. -/
theorem panPrintedB_of_printedP (hP : PanPrintedP) : PanPrintedB := by
  intro p _ hp ιp ρ hirr hfr hpst hodd hht
  obtain ⟨N, _, k, g, ρg, ψ, ⟨S, hatt⟩, htw⟩ := hP p hp ιp ρ (isIrreducibleP_of ρ hirr) hfr hpst hodd
    ((localDistinctHTP_iff p _).mpr hht)
  obtain ⟨M, χ, g', hM, hk, hg', hcoef⟩ := exists_normalized_of_eigenform g
  refine ⟨M, k, χ, g', hM, hk, hg', ψ, S ∪ Finset.range (N + 1), fun q hq hqS v σ hv hσ => ?_⟩
  simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hqS
  obtain ⟨hqS, hqN1⟩ := hqS
  have hqN : ¬ q ∣ N := fun hd => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hd
    omega
  rw [trace_of_twist p htw, (hatt q hq hqN hqS).2 v σ hv hσ, hcoef q hq hqN]

/-- **Berger, Théorème 0.7, printed form, for one `p`-adic representation** (L. Berger, *Représentations
p-adiques et équations différentielles*, Invent. Math. 148 (2002), 219-284; Théorème 0.7 = Corollaire 5.22 of the
published version (locator audit row R11) = Théorème 0.6 = Théorème 5.19 of arXiv:math/0102179v3), at
`K = ℚ_p`: a de Rham `p`-adic representation `V` of `G_{ℚ_p}` is potentially semistable. Here `V = E^n` for a
finite `E/ℚ_p` inside `ℚ̄_p`, with a continuous action `ρ : G_{ℚ_p} → GL_n(E)` (`ℚ_p`-linear on `V`; the
topology of `E` is its unique `ℚ_p`-vector-space topology):

* de Rham: `dim_{ℚ_p} (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}} = dim_{ℚ_p} V` (`IsDeRhamU`);
* potentially semistable: `dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V` for some finite `K/ℚ_p`
  (`IsPstB`, Berger's `B_st = B_max[log [p̃]] ⊆ B_dR`, bst-construct). -/
def BergerPrintedV : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] E] (ρE : GQp p →* GL (Fin n) E),
    Continuous ρE → IsDeRhamU p ρE → IsPstB p ρE

/-- A model `ρ_E` of a continuous `ρ` is continuous (`E ⊆ ℚ̄_p` with the subspace topology). -/
theorem continuous_model {p : ℕ} [Fact p.Prime] {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {ρ : GQp p →* GL (Fin n) (PadicAlgCl p)} {ρE : GQp p →* GL (Fin n) E}
    (hmod : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ)
    (hρ : Continuous ρ) : Continuous ρE := by
  have hemb : Topology.IsEmbedding (fun M : Matrix (Fin n) (Fin n) E =>
      M.map (algebraMap E (PadicAlgCl p))) :=
    Topology.IsEmbedding.subtypeVal.matrix_map
  have hval : ∀ σ, ((ρE σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (PadicAlgCl p)) =
      ((ρ σ : GL (Fin n) (PadicAlgCl p)) : Matrix (Fin n) (Fin n) (PadicAlgCl p)) := fun σ => by
    rw [← hmod σ]
    rfl
  have h1 : Continuous (fun σ => ((ρE σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) := by
    rw [hemb.continuous_iff]
    simp only [Function.comp_def, hval]
    exact Units.continuous_val.comp hρ
  rw [Units.continuous_iff]
  refine ⟨h1, ?_⟩
  have hinv : ∀ σ, ((ρE σ)⁻¹ : GL (Fin n) E) = ρE σ⁻¹ := fun σ => (map_inv ρE σ).symm
  simp only [hinv]
  exact h1.comp continuous_inv

/-- bst-construct's `BergerPrintedB` (for `ℚ̄_p`-valued `ρ` with a model) from the printed leaf: Berger applied
to the model `V = E^n`, continuous by `continuous_model`. -/
theorem bergerPrintedB_of_V (h : BergerPrintedV) : BergerPrintedB := by
  intro p _ n ρ hρ hdr
  obtain ⟨E, hE, ρE, hmod, hdrE⟩ := hdr
  exact ⟨E, hE, ρE, hmod, h p n E ρE (continuous_model hmod hρ) hdrE⟩

/-- **`r11r12 : PanBerger` from the two printed leaves** and the current bundle's Diamond–Shurman 9.6.5
(`dsThm965Printed`, with `eigenformCoeffFieldFinite`) and Deligne–Serre (`dsThm966Printed`) fields. -/
theorem panBerger_of_printedPV (hP : PanPrintedP) (hB : BergerPrintedV)
    (h965 : DSCoeffExt.DSThm965Printed) (hK : DSCoeffExt.EigenformCoeffFieldFinite)
    (h966 : DSThm966EV.DSThm966Printed) : PanBerger :=
  panBerger_of_printedB_weak (panPrintedB_of_printedP hP) (bergerPrintedB_of_V hB)
    (DSCoeffExt.dsThm965Weak_of_printed h965 hK) (DSThm966EV.dsThm966_of_printed h966)

end PanDict
end PkgI4
end HDec
