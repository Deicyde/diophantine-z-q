import ZInQKernel.Contrib.OneProof.PstModel

/-!
Copyright: this file is part of the fork Deicyde/diophantine-z-q (task htmult-model, 2026-11-17). Report
`docs/research/htmult-model.md`; scratch copy `scratch/htmult-model/HTModel.lean`.

# htmult-model: the Hodge–Tate multiplicities do not depend on the finite coefficient model

The `ℂ_p`-side counterpart of `PstModel.lean` §2–§5 (pb-dimform).

* **§1. Invariants of a twisted `V` under a change of coefficient field.** For `E ⊆ L` with an `E`-basis
  `b` of `L` (`d = [L : E]`) and `ρ_L = ρ_E ⊗_E L`, pb-dimform's `ℚ_p[G]`-isomorphism `L^n ≅ (E^n)^d`
  (`PstModel.phiE`, `phiE_symm_equivariant`) and its tensor form `PstModel.psi` give
  `(A ⊗_{ℚ_p} L^n)^H ≅ ((A ⊗_{ℚ_p} E^n)^H)^d` over `ℚ_p`, for any `ℚ_p`-module `A` with a `ℚ_p`-linear action
  of `G_{ℚ_p}` and any subgroup `H` (`tensorInvEquiv`), so `dim_{ℚ_p}` is multiplied by `d`
  (`finrank_tensorInv`, with pb-dimform's `finrank_fin_pi_sub`).
* **§2. The multiplicities.** With `A = ℂ_p(w)`, `H = G_{ℚ_p}`: `dim_{ℚ_p} (ℂ_p(w) ⊗ L^n)^G = d · dim_{ℚ_p} (ℂ_p(w) ⊗
  E^n)^G`, and `[L : ℚ_p] = [E : ℚ_p] · d`, so the multiplicity over the model's own field,
  `htMultU = dim_{ℚ_p} / [· : ℚ_p]`, is the same (`htMultU_eq_of_basis`); by pb-fix3's dictionary
  `htMultE_eq_htMultU` (`htMultE = dim_E (V ⊗ ℂ_p(w))^G`) so is `htMultE` (`htMultE_eq_of_basis`).
* **§3. Models inside `ℚ̄_p`.** `htMultE_eq_of_le` (`E ≤ L`), `htMultE_model_eq` (two models, through `E ⊔ E'`),
  `localDistinctHTP_iff_of_model` and `localDistinctHTP_iff_forall`: Pan's hypothesis `LocalDistinctHTP`
  ("Hodge–Tate with distinct weights, read on some finite model") holds iff it holds on any given model, iff it
  holds on every model with the same pair of weights.

On-the-spot (provenance (c)): neither the manuscript nor a source it cites states this step; it is standard
(the Hodge–Tate weights of a `ℚ̄_p`-representation are defined through any finite model).
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace HTModel

open Module BergerBst PanBergerSplit PanDict PstModel
open scoped TensorProduct

/-! ## §1. `(A ⊗ L^n)^H ≅ ((A ⊗ E^n)^H)^d` over `ℚ_p` -/

section TensorInv

variable (p : ℕ) [Fact p.Prime]
variable {E L : Type*} [Field E] [Field L] [Algebra ℚ_[p] E] [Algebra ℚ_[p] L] [Algebra E L]
  [IsScalarTower ℚ_[p] E L] {d n : ℕ} (b : Basis (Fin d) E L)
variable {ρE : GQp p →* GL (Fin n) E} {ρL : GQp p →* GL (Fin n) L}
variable {A : Type*} [AddCommGroup A] [Module ℚ_[p] A] (act : GQp p → A →ₗ[ℚ_[p]] A)

/-- `psi` intertwines the actions `act ⊗ ρ_L` and `(act ⊗ ρ_E)^d` (pb-dimform's `psi_act`, for any `A`). -/
theorem psi_map (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ) (σ : GQp p)
    (y : A ⊗[ℚ_[p]] (Fin n → L)) (j : Fin d) :
    psi p b ℚ_[p] A (TensorProduct.map (act σ) (vAct p ρL σ) y) j =
      TensorProduct.map (act σ) (vAct p ρE σ) (psi p b ℚ_[p] A y j) := by
  induction y using TensorProduct.inductionOn with
  | tmul a v => simp [psi_tmul, phiE_symm_equivariant hρ]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem mem_tensorInv_iff (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ)
    (H : Subgroup (GQp p)) (x : A ⊗[ℚ_[p]] (Fin n → L)) :
    x ∈ tensorInv p act H ρL ↔ ∀ j, psi p b ℚ_[p] A x j ∈ tensorInv p act H ρE := by
  change (∀ σ ∈ H, TensorProduct.map (act σ) (vAct p ρL σ) x = x) ↔
    ∀ j, ∀ σ ∈ H, TensorProduct.map (act σ) (vAct p ρE σ) (psi p b ℚ_[p] A x j) = psi p b ℚ_[p] A x j
  constructor
  · intro hx j σ hσ
    rw [← psi_map p b act hρ, hx σ hσ]
  · intro hx σ hσ
    apply (psi p b ℚ_[p] A).injective
    funext j
    rw [psi_map p b act hρ]
    exact hx j σ hσ

/-- **`(A ⊗_{ℚ_p} L^n)^H ≅ ((A ⊗_{ℚ_p} E^n)^H)^d` as `ℚ_p`-spaces** (`d = [L : E]`). -/
def tensorInvEquiv (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ)
    (H : Subgroup (GQp p)) :
    tensorInv p act H ρL ≃ₗ[ℚ_[p]] (Fin d → tensorInv p act H ρE) where
  toFun x j := ⟨psi p b ℚ_[p] A x j, (mem_tensorInv_iff p b act hρ H x).1 x.2 j⟩
  map_add' x y := by
    funext j
    apply Subtype.ext
    simp
  map_smul' c x := by
    funext j
    apply Subtype.ext
    exact congrFun (map_smul (psi p b ℚ_[p] A) c (x : A ⊗[ℚ_[p]] (Fin n → L))) j
  invFun f := ⟨(psi p b ℚ_[p] A).symm (fun j => (f j : A ⊗[ℚ_[p]] (Fin n → E))),
    (mem_tensorInv_iff p b act hρ H _).2 (fun j => by
      rw [LinearEquiv.apply_symm_apply]
      exact (f j).2)⟩
  left_inv x := Subtype.ext ((psi p b ℚ_[p] A).symm_apply_apply (x : A ⊗[ℚ_[p]] (Fin n → L)))
  right_inv f := by
    funext j
    apply Subtype.ext
    exact congrFun ((psi p b ℚ_[p] A).apply_symm_apply
      (fun j => (f j : A ⊗[ℚ_[p]] (Fin n → E)))) j

include b in
theorem finrank_tensorInv (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ)
    (H : Subgroup (GQp p)) :
    finrank ℚ_[p] (tensorInv p act H ρL) = d * finrank ℚ_[p] (tensorInv p act H ρE) := by
  rw [(tensorInvEquiv p b act hρ H).finrank_eq, finrank_fin_pi_sub]

end TensorInv

/-! ## §2. The Hodge–Tate multiplicities of the two models agree -/

section Mult

variable (p : ℕ) [Fact p.Prime]
variable {E L : Type*} [Field E] [Field L] [Algebra ℚ_[p] E] [Algebra ℚ_[p] L] [Algebra E L]
  [IsScalarTower ℚ_[p] E L] [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] L]
  {d n : ℕ} (b : Basis (Fin d) E L)
variable {ρE : GQp p →* GL (Fin n) E} {ρL : GQp p →* GL (Fin n) L}

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] L] in
include b in
/-- pb-fix2's finrank form `htMultU = dim_{ℚ_p} (ℂ_p(w) ⊗ V)^G / [· : ℚ_p]` is the same on `E` and on `L`:
numerator and denominator are both multiplied by `d = [L : E]`. -/
theorem htMultU_eq_of_basis (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ)
    (w : ℤ) : htMultU p ρL w = htMultU p ρE w := by
  have : Module.Free ℚ_[p] E := Module.Free.of_divisionRing _ _
  have : Module.Free E L := Module.Free.of_divisionRing _ _
  have hd : 0 < d := Fin.pos_iff_nonempty.2 b.index_nonempty
  have hL : finrank ℚ_[p] L = finrank ℚ_[p] E * d := by
    rw [← Module.finrank_mul_finrank ℚ_[p] E L, Module.finrank_eq_card_basis b, Fintype.card_fin]
  unfold htMultU htU
  rw [finrank_tensorInv p b (htLin p w) hρ ⊤, hL, mul_comm (finrank ℚ_[p] E) d,
    Nat.mul_div_mul_left _ _ hd]

include b in
/-- **The printed Hodge–Tate multiplicity does not see the coefficient field**: for `E ⊆ L` and the model
`ρ_L = ρ_E ⊗_E L`, `dim_L (L^n ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}} = dim_E (E^n ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` for every `w`
(on-the-spot: neither the manuscript nor a cited source states this; standard). -/
theorem htMultE_eq_of_basis (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ)
    (w : ℤ) : htMultE p ρL w = htMultE p ρE w := by
  rw [htMultE_eq_htMultU, htMultE_eq_htMultU, htMultU_eq_of_basis p b hρ]

end Mult

/-! ## §3. Models inside `ℚ̄_p`; the model clause of `LocalDistinctHTP` -/

section Models

variable (p : ℕ) [Fact p.Prime] {n : ℕ}

/-- The multiplicities are unchanged when the coefficient field of the model is enlarged inside `ℚ̄_p`. -/
theorem htMultE_eq_of_le {E L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hEL : E ≤ L)
    [FiniteDimensional ℚ_[p] L] (ρE : GQp p →* GL (Fin n) E) (ρL : GQp p →* GL (Fin n) L)
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) =
      Matrix.GeneralLinearGroup.map (algebraMap L (PadicAlgCl p)) (ρL σ)) (w : ℤ) :
    htMultE p ρE w = htMultE p ρL w := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[p] E L := IsScalarTower.of_algebraMap_eq (fun c => rfl)
  have : FiniteDimensional ℚ_[p] E := FiniteDimensional.left ℚ_[p] E L
  have : FiniteDimensional E L := FiniteDimensional.right ℚ_[p] E L
  have : Module.Free E L := Module.Free.of_divisionRing E L
  have hρ' : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ := by
    intro σ
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have h1 := congrArg (fun g : GL (Fin n) (PadicAlgCl p) => g.val i j) (hρ σ)
    simp only [Matrix.GeneralLinearGroup.map_apply] at h1
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact Subtype.ext h1
  exact (htMultE_eq_of_basis p (Module.finBasis E L) hρ' w).symm

/-- **Two finite models of the same `ℚ̄_p`-valued `ρ` have the same Hodge–Tate multiplicities** (compare both with
the model over the compositum `E ⊔ E'`, `htMultE_eq_of_le`). On-the-spot (standard). -/
theorem htMultE_model_eq {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E'] {ρ : GQp p →* GL (Fin n) (PadicAlgCl p)}
    (ρE : GQp p →* GL (Fin n) E) (ρE' : GQp p →* GL (Fin n) E')
    (hE : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ)
    (hE' : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E' (PadicAlgCl p)) (ρE' σ) = ρ σ) (w : ℤ) :
    htMultE p ρE w = htMultE p ρE' w := by
  let ρL : GQp p →* GL (Fin n) ↥(E ⊔ E') :=
    (Matrix.GeneralLinearGroup.map (IntermediateField.inclusion (le_sup_left : E ≤ E ⊔ E')).toRingHom).comp ρE
  have hL : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap ↥(E ⊔ E') (PadicAlgCl p)) (ρL σ) = ρ σ := by
    intro σ
    rw [← hE σ]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  rw [htMultE_eq_of_le p le_sup_left ρE ρL (fun σ => (hE σ).trans (hL σ).symm),
    htMultE_eq_of_le p le_sup_right ρE' ρL (fun σ => (hE' σ).trans (hL σ).symm)]

/-- **The model clause of `LocalDistinctHTP` is harmless**: for any one finite model `ρ_E` of `ρ`,
`LocalDistinctHTP ρ` (distinct Hodge–Tate weights read on some model) holds iff the multiplicities of `ρ_E` are
those of two distinct integers. -/
theorem localDistinctHTP_iff_of_model {ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)}
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] (ρE : GQp p →* GL (Fin 2) E)
    (hE : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) :
    LocalDistinctHTP p ρ ↔ ∃ a b : ℤ, a ≠ b ∧ ∀ w : ℤ, htMultE p ρE w = Multiset.count w {a, b} := by
  constructor
  · rintro ⟨a, b, hab, E', hE'f, ρE', hE', hw⟩
    exact ⟨a, b, hab, fun w => (htMultE_model_eq p ρE ρE' hE hE' w).trans (hw w)⟩
  · rintro ⟨a, b, hab, hw⟩
    exact ⟨a, b, hab, E, inferInstance, ρE, hE, hw⟩

/-- **Distinct Hodge–Tate weights on one finite model iff on every finite model** (with the same pair of
weights, and some model exists): the analogue of pb-dimform's `localIsPstF_iff_forall`. -/
theorem localDistinctHTP_iff_forall (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)) :
    LocalDistinctHTP p ρ ↔
      (∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
          (ρE : GQp p →* GL (Fin 2) E),
          ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
        ∃ a b : ℤ, a ≠ b ∧
          ∀ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
            (ρE : GQp p →* GL (Fin 2) E),
            (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) →
            ∀ w : ℤ, htMultE p ρE w = Multiset.count w {a, b} := by
  constructor
  · rintro ⟨a, b, hab, E, hEf, ρE, hE, hw⟩
    exact ⟨⟨E, hEf, ρE, hE⟩, a, b, hab, fun E' _ ρE' hE' w =>
      (htMultE_model_eq p ρE' ρE hE' hE w).trans (hw w)⟩
  · rintro ⟨⟨E, hEf, ρE, hE⟩, a, b, hab, hall⟩
    exact ⟨a, b, hab, E, hEf, ρE, hE, hall E hEf ρE hE⟩

/-- The same for pb-fix2's finrank form `LocalDistinctHTU` (through `localDistinctHTP_iff`). -/
theorem localDistinctHTU_iff_of_model {ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)}
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] (ρE : GQp p →* GL (Fin 2) E)
    (hE : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) :
    LocalDistinctHTU p ρ ↔ ∃ a b : ℤ, a ≠ b ∧ ∀ w : ℤ, htMultU p ρE w = Multiset.count w {a, b} := by
  rw [← localDistinctHTP_iff, localDistinctHTP_iff_of_model p E ρE hE]
  simp only [htMultE_eq_htMultU]

end Models

end HTModel
end PkgI4
end HDec

open HDec.PkgI4.HTModel in
#print axioms psi_map
open HDec.PkgI4.HTModel in
#print axioms mem_tensorInv_iff
open HDec.PkgI4.HTModel in
#print axioms tensorInvEquiv
open HDec.PkgI4.HTModel in
#print axioms finrank_tensorInv
open HDec.PkgI4.HTModel in
#print axioms htMultU_eq_of_basis
open HDec.PkgI4.HTModel in
#print axioms htMultE_eq_of_basis
open HDec.PkgI4.HTModel in
#print axioms htMultE_eq_of_le
open HDec.PkgI4.HTModel in
#print axioms htMultE_model_eq
open HDec.PkgI4.HTModel in
#print axioms localDistinctHTP_iff_of_model
open HDec.PkgI4.HTModel in
#print axioms localDistinctHTP_iff_forall
open HDec.PkgI4.HTModel in
#print axioms localDistinctHTU_iff_of_model
