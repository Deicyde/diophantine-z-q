import ZInQKernel.Contrib.OneProof.EigenformHTPrinted

/-! # htnew-assembly: `modularHTPrinted` from the printed form over a finite coefficient field

Task htnew-assembly, 2026-11-17 (report `docs/research/htnew-assembly.md`, log `scratch/htnew-assembly/log.md`).

The bundle field `modularHTPrinted : EigenformHTPrinted.ModularHTPrinted` (htnew-print) asks for a
`ρ : G_ℚ → GL₂(ℚ̄_ℓ)` and states its Hodge–Tate weights in the kernel's form `HasHTWeightsAtSelf`, a dimension count
of `ℚ_ℓ`-linear `G_{ℚ_ℓ}`-equivariant maps `V → ℂ_ℓ(i)` (the *dual side*: `(ℂ_ℓ(i) ⊗ V^∨)^{G}`). The strict review
rated it a consequence (GLUE): the passage from a print's wording to that form was not written in Lean (R1, R4).

This file states the theorem as printed (`ModularHTCoeff`, §4):

* **coefficients**: `ρ` takes values in `GL₂(E)` for a finite extension `E/ℚ_ℓ` inside `ℚ̄_ℓ` (the print's
  `K_{f,λ}`, or Kato's `F_λ`, with its embedding into `ℚ̄_ℓ`; the leaf only asks that there be one such `E`);
* **Hodge–Tate weights on the print's side**: `w` has multiplicity `dim_E (V ⊗_{ℚ_ℓ} ℂ_ℓ(w))^{G_{ℚ_ℓ}}`
  (`PrintHTSpace`, §1: the invariants of `ρ(σ) ⊗ χ(σ)^w σ` on the `ℚ_ℓ`-tensor product, Mathlib's
  `TensorProduct`), in either sign convention (`PrintHasHTWeights`: cyclotomic weight `−1`;
  `PrintHasHTWeightsPos`: cyclotomic weight `+1`);
* **Frobenius**: arithmetic or geometric normalization; the four combinations of normalization and sign
  convention that a print can use reduce to the two disjuncts of the leaf (§5, `readings`).

and proves the field from it in Lean (`modularHTPrinted_of_coeff`, §5):

* §2 **the assembly lemma** (`printHTMult_eq`): `dim_E (V ⊗_{ℚ_ℓ} ℂ_ℓ(w))^{G} = htMult(ρ^∨, −w)`, through
  the `ℚ_ℓ`-linear isomorphism `V ⊗_{ℚ_ℓ} ℂ_ℓ ≅ Hom_{ℚ_ℓ}(E^n, ℂ_ℓ)`, `v ⊗ c ↦ (u ↦ Tr_{E/ℚ_ℓ}(u·v) c)`
  (trace form + `dualTensorHomEquiv`), which carries the invariants onto the kernel's `htSpace` of the
  contragredient `ρ^∨(σ) = ρ(σ⁻¹)ᵀ`;
* §3 **from the print's side to the kernel's**: the print's weights `S` give kernel weights `−S` for `ρ^∨`, and
  `HTDual` (htnew-print, from Tate's theorems proved on main) gives kernel weights `S` for `ρ^∨^∨ = ρ`;
* §5 **coefficient extension** `E ⊆ ℚ̄_ℓ` (`DSCoeffExt.mapRep`), traces, unramifiedness.

No `sorry`, no `axiom`, no code that runs at build time.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option synthInstance.maxHeartbeats 400000

namespace HTNewAssembly

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

/-! ## §1. Hodge–Tate weights on the print's side: `(V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` -/

section PrintSide

variable (p : ℕ) [Fact p.Prime] {n : ℕ} (E : IntermediateField ℚ_[p] (PadicAlgCl p))

local instance smulCommClassE : SMulCommClass ℚ_[p] E (Fin n → E) := inferInstance

/-- `E` acts on `V ⊗_{ℚ_p} ℂ_p` through `V = Eⁿ`. -/
local instance moduleE : Module E ((Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) := TensorProduct.leftModule

local instance isScalarTowerE : IsScalarTower ℚ_[p] E ((Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) :=
  TensorProduct.isScalarTower_left

theorem cpAct_smul' (σ : GQp p) (c : ℚ_[p]) (x : ℂ_[p]) : cpAct p σ (c • x) = c • cpAct p σ x := by
  rw [Algebra.smul_def, map_mul, cpAct_algebraMap, ← Algebra.smul_def]

theorem cpAct_mul' (σ τ : GQp p) (x : ℂ_[p]) : cpAct p (σ * τ) x = cpAct p σ (cpAct p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_cpAct p _) ((continuous_cpAct p σ).comp (continuous_cpAct p τ))
  | ih a => rw [cpAct_coe, cpAct_coe, cpAct_coe]; rfl

theorem cpAct_one' (x : ℂ_[p]) : cpAct p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_cpAct p _) continuous_id
  | ih a => rw [cpAct_coe]; rfl

theorem cycPow_mul' (σ τ : GQp p) (i : ℤ) : cycPow p (σ * τ) i = cycPow p σ i * cycPow p τ i := by
  have h : cyc p (σ * τ) = cyc p σ * cyc p τ := by
    simp only [cyc]
    rw [← map_mul]
    rfl
  simp only [cycPow, h, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem cycPow_one' (i : ℤ) : cycPow p 1 i = 1 := by
  have h : cyc p 1 = 1 := by
    simp only [cyc]
    rw [← map_one (cyclotomicCharacter (PadicAlgCl p) p)]
    rfl
  simp [cycPow, h]

/-- `x ↦ χ(σ)^w σ(x)` on `ℂ_p`, `ℚ_p`-linear: the action of `σ` on `ℂ_p(w)`. -/
def cTw (w : ℤ) (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] where
  toFun x := cycPow p σ w • cpAct p σ x
  map_add' x y := by rw [map_add, smul_add]
  map_smul' c x := by
    rw [cpAct_smul', RingHom.id_apply, smul_comm]

theorem cTw_apply (w : ℤ) (σ : GQp p) (x : ℂ_[p]) : cTw p w σ x = cycPow p σ w • cpAct p σ x := rfl

/-- **The action of `σ ∈ G_{ℚ_p}` on `V ⊗_{ℚ_p} ℂ_p(w)`**, `V = Eⁿ` with `ρ`: `ρ(σ) ⊗ χ(σ)^w σ`. -/
def twistAct (ρ : GQp p →* GL (Fin n) E) (w : ℤ) (σ : GQp p) :
    ((Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) →ₗ[ℚ_[p]] ((Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) :=
  TensorProduct.map ((Matrix.toLin' (ρ σ : Matrix (Fin n) (Fin n) E)).restrictScalars ℚ_[p]) (cTw p w σ)

theorem twistAct_tmul (ρ : GQp p →* GL (Fin n) E) (w : ℤ) (σ : GQp p) (v : Fin n → E) (c : ℂ_[p]) :
    twistAct p E ρ w σ (v ⊗ₜ c) = ((ρ σ : Matrix (Fin n) (Fin n) E).mulVec v) ⊗ₜ cTw p w σ c := rfl

theorem twistAct_smul (ρ : GQp p →* GL (Fin n) E) (w : ℤ) (σ : GQp p) (e : E)
    (t : (Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) : twistAct p E ρ w σ (e • t) = e • twistAct p E ρ w σ t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul v c =>
    rw [TensorProduct.smul_tmul', twistAct_tmul, twistAct_tmul, TensorProduct.smul_tmul',
      Matrix.mulVec_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **`(V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}`** for an `E`-linear representation `ρ` of `G_{ℚ_p}` on `V = Eⁿ`: the tensors
fixed by every `ρ(σ) ⊗ χ(σ)^w σ`. An `E`-subspace (`E` acting on `V`). This is the space whose dimension the
printed definition of Hodge–Tate weights counts (Tate 1967 §4; Faltings 1987/1989; the surveys' definition of
Hodge–Tate weights; for an `E`-linear `V`, the multiplicity of `w` is its `E`-dimension). -/
def PrintHTSpace (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : Submodule E ((Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) where
  carrier := {t | ∀ σ : GQp p, twistAct p E ρ w σ t = t}
  zero_mem' σ := map_zero _
  add_mem' {x y} hx hy σ := by rw [map_add, hx σ, hy σ]
  smul_mem' e t ht σ := by rw [twistAct_smul, ht σ]

/-- The multiplicity of the weight `w` on the print's side: `dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}`. -/
def PrintHTMult (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : ℕ := finrank E (PrintHTSpace p E ρ w)

/-- **Hodge–Tate weights `S`, convention "the cyclotomic character has weight `−1`"**: `w` occurs with
multiplicity `dim_E (V ⊗ ℂ_p(w))^{G}` (for `V = ℚ_p(1)` the only weight is `−1`; this is the kernel's sign
convention). -/
def PrintHasHTWeights (ρ : GQp p →* GL (Fin n) E) (S : Multiset ℤ) : Prop :=
  ∀ w : ℤ, PrintHTMult p E ρ w = S.count w

/-- **Hodge–Tate weights `S`, convention "the cyclotomic character has weight `+1`"**: `w` occurs with
multiplicity `dim_E (V ⊗ ℂ_p(−w))^{G}`. -/
def PrintHasHTWeightsPos (ρ : GQp p →* GL (Fin n) E) (S : Multiset ℤ) : Prop :=
  ∀ w : ℤ, PrintHTMult p E ρ (-w) = S.count w

theorem count_neg_map (S : Multiset ℤ) (w : ℤ) : (S.map Neg.neg).count w = S.count (-w) := by
  have := Multiset.count_map_eq_count' (fun w : ℤ => -w) S neg_injective (-w)
  simp only [neg_neg] at this
  exact this

/-- The two sign conventions differ by `S ↦ −S`. -/
theorem printHasHTWeightsPos_iff (ρ : GQp p →* GL (Fin n) E) (S : Multiset ℤ) :
    PrintHasHTWeightsPos p E ρ S ↔ PrintHasHTWeights p E ρ (S.map Neg.neg) := by
  constructor
  · intro h w
    rw [count_neg_map, ← h (-w), neg_neg]
  · intro h w
    rw [h (-w), count_neg_map, neg_neg]

end PrintSide

/-! ## §2. The assembly lemma: `dim_E (V ⊗ ℂ_p(w))^G = htMult(ρ^∨, −w)` -/

section Assembly

variable (p : ℕ) [Fact p.Prime] {n : ℕ} (E : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] E]

/-- The contragredient `σ ↦ ρ(σ⁻¹)ᵀ` of a matrix representation. -/
def dualE {G : Type*} [Group G] {R : Type*} [CommRing R] (ρ : G →* GL (Fin n) R) : G →* GL (Fin n) R where
  toFun σ := ⟨(ρ σ⁻¹ : Matrix (Fin n) (Fin n) R).transpose, (ρ σ : Matrix (Fin n) (Fin n) R).transpose,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' σ τ := Units.ext (by simp [Matrix.transpose_mul])

theorem dualE_val {G : Type*} [Group G] {R : Type*} [CommRing R] (ρ : G →* GL (Fin n) R) (σ : G) :
    ((dualE ρ σ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = (ρ σ⁻¹ : Matrix (Fin n) (Fin n) R).transpose :=
  rfl

/-- The trace pairing `v ↦ (u ↦ Tr_{E/ℚ_p}(u · v))`, `Eⁿ → Hom_{ℚ_p}(Eⁿ, ℚ_p)`. -/
def trPair : (Fin n → E) →ₗ[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E) :=
  LinearMap.mk₂ ℚ_[p] (fun v u => Algebra.trace ℚ_[p] E (u ⬝ᵥ v))
    (fun v v' u => by rw [dotProduct_add, map_add])
    (fun c v u => by rw [dotProduct_smul, LinearMap.map_smul_of_tower, smul_eq_mul])
    (fun v u u' => by rw [add_dotProduct, map_add])
    (fun c v u => by rw [smul_dotProduct, LinearMap.map_smul_of_tower, smul_eq_mul])

theorem trPair_apply (v u : Fin n → E) : trPair p E v u = Algebra.trace ℚ_[p] E (u ⬝ᵥ v) := rfl

theorem trPair_injective : Function.Injective (trPair p E (n := n)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  funext k
  by_contra hk
  rw [Pi.zero_apply] at hk
  have h := LinearMap.congr_fun hv (Pi.single k (v k)⁻¹)
  rw [trPair_apply, single_dotProduct, inv_mul_cancel₀ hk, LinearMap.zero_apply] at h
  have h1 : Algebra.trace ℚ_[p] E 1 = (finrank ℚ_[p] E : ℚ_[p]) := by
    rw [← map_one (algebraMap ℚ_[p] E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  rw [h1, Nat.cast_eq_zero] at h
  exact (Module.finrank_pos (R := ℚ_[p]) (M := E)).ne' h

/-- The trace pairing as an isomorphism `Eⁿ ≅ Hom_{ℚ_p}(Eⁿ, ℚ_p)`. -/
def trEquiv : (Fin n → E) ≃ₗ[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E) :=
  (trPair p E).linearEquivOfInjective (trPair_injective p E) (Subspace.dual_finrank_eq).symm

theorem trEquiv_apply (v u : Fin n → E) : trEquiv p E v u = Algebra.trace ℚ_[p] E (u ⬝ᵥ v) := rfl

/-- **The isomorphism `V ⊗_{ℚ_p} ℂ_p ≅ Hom_{ℚ_p}(Eⁿ, ℂ_p)`**, `v ⊗ c ↦ (u ↦ Tr_{E/ℚ_p}(u · v) c)`. -/
def psi : ((Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) ≃ₗ[ℚ_[p]] ((Fin n → E) →ₗ[ℚ_[p]] ℂ_[p]) :=
  (TensorProduct.congr (trEquiv p E) (LinearEquiv.refl ℚ_[p] ℂ_[p])).trans
    (dualTensorHomEquiv ℚ_[p] (Fin n → E) ℂ_[p])

theorem psi_tmul (v : Fin n → E) (c : ℂ_[p]) (u : Fin n → E) :
    psi p E (v ⊗ₜ c) u = Algebra.trace ℚ_[p] E (u ⬝ᵥ v) • c := by
  simp [psi, trEquiv_apply]

/-- **Equivariance of `psi`**: `psi(ρ(σ) ⊗ χ^w σ · t)(u) = χ(σ)^w σ(psi(t)(ρ(σ)ᵀ u))`. -/
theorem psi_twistAct (ρ : GQp p →* GL (Fin n) E) (w : ℤ) (σ : GQp p)
    (t : (Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) (u : Fin n → E) :
    psi p E (twistAct p E ρ w σ t) u =
      cycPow p σ w • cpAct p σ (psi p E t ((ρ σ : Matrix (Fin n) (Fin n) E).transpose.mulVec u)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    rw [twistAct_tmul, psi_tmul, psi_tmul, cTw_apply, cpAct_smul', smul_comm,
      Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]

/-- `psi` carries `(V ⊗ ℂ_p(w))^{G}` onto the kernel's `htSpace` of the contragredient at `w`. -/
theorem psi_mem_iff (ρ : GQp p →* GL (Fin n) E) (w : ℤ) (t : (Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) :
    psi p E t ∈ htSpace p (dualE ρ) w ↔ t ∈ PrintHTSpace p E ρ w := by
  constructor
  · intro h σ
    apply (psi p E).injective
    refine LinearMap.ext fun u => ?_
    have h1 := h σ⁻¹ u
    rw [dualE_val, inv_inv] at h1
    rw [psi_twistAct, h1, cpAct_smul', smul_smul, ← cpAct_mul', mul_inv_cancel, cpAct_one', ← cycPow_mul',
      mul_inv_cancel, cycPow_one', one_smul]
  · intro h σ u
    have h1 := LinearMap.congr_fun (congrArg (psi p E) (h σ))
      ((ρ σ⁻¹ : Matrix (Fin n) (Fin n) E).transpose.mulVec u)
    rw [psi_twistAct, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec] at h1
    change psi p E t ((dualE ρ σ : Matrix (Fin n) (Fin n) E).mulVec u) = _
    rw [dualE_val, ← h1]

/-- **The assembly lemma** (R1): the print-side multiplicity of `w` is the kernel's multiplicity of `−w` for the
contragredient: `dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G} = htMult(ρ^∨, −w)`. -/
theorem printHTMult_eq (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    PrintHTMult p E ρ w = htMult p (dualE ρ) (-w) := by
  have hmap : ((PrintHTSpace p E ρ w).restrictScalars ℚ_[p]).map (psi p E (n := n)).toLinearMap =
      htSpace p (dualE ρ) w := by
    ext φ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (psi_mem_iff p E ρ w t).2 ht
    · intro hφ
      refine ⟨(psi p E).symm φ, ?_, by simp⟩
      show (psi p E).symm φ ∈ PrintHTSpace p E ρ w
      rw [← psi_mem_iff, LinearEquiv.apply_symm_apply]
      exact hφ
  have h1 : finrank ℚ_[p] ((PrintHTSpace p E ρ w).restrictScalars ℚ_[p]) =
      finrank ℚ_[p] (htSpace p (dualE ρ) w) := by
    rw [← hmap, LinearEquiv.finrank_map_eq]
  have h2 : finrank ℚ_[p] E * finrank E (PrintHTSpace p E ρ w) =
      finrank ℚ_[p] ((PrintHTSpace p E ρ w).restrictScalars ℚ_[p]) := by
    have : Module.Free E (PrintHTSpace p E ρ w) := Module.Free.of_divisionRing E (PrintHTSpace p E ρ w)
    exact Module.finrank_mul_finrank ℚ_[p] E (PrintHTSpace p E ρ w)
  rw [htMult, neg_neg, ← h1, ← h2, PrintHTMult, Nat.mul_div_cancel_left _ Module.finrank_pos]

end Assembly

/-! ## §3. From the print's side to the kernel's `HasHTWeightsAtSelf` -/

section Kernel

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- A continuous `ρ : G_ℚ → GL_n(E)`, `E ⊆ ℚ̄_ℓ`, with coefficients extended to `ℚ̄_ℓ`. -/
def toGR (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (ρ : GQ →* GL (Fin n) E) (hρ : Continuous ρ) :
    GaloisRep ℓ n where
  toHom := (Units.map ((algebraMap E (PadicAlgCl ℓ)).mapMatrix :
    Matrix (Fin n) (Fin n) E →+* Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).toMonoidHom).comp ρ
  continuous_toHom := (Units.continuous_map (continuous_id.matrix_map continuous_subtype_val)).comp hρ

theorem toGR_mat (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (ρ : GQ →* GL (Fin n) E) (hρ : Continuous ρ)
    (σ : GQ) : (toGR E ρ hρ).mat σ = (ρ σ : Matrix (Fin n) (Fin n) E).map (algebraMap E (PadicAlgCl ℓ)) :=
  rfl

theorem dualGR_dualGR_restrictLocal (r : GaloisRep ℓ n) :
    (EigenformHTPrinted.dualGR (EigenformHTPrinted.dualGR r)).restrictLocal ℓ = r.restrictLocal ℓ :=
  MonoidHom.ext fun σ => Units.ext (by
    change (EigenformHTPrinted.dualGR (EigenformHTPrinted.dualGR r)).mat (decomp ℓ σ) = r.mat (decomp ℓ σ)
    rw [EigenformHTPrinted.dualGR_mat, EigenformHTPrinted.dualGR_mat, inv_inv, Matrix.transpose_transpose])

/-- **Print side ⇒ kernel form** (R1 assembled): if `ρ|_{G_{ℚ_ℓ}}` (`ρ` with coefficients in a finite
`E ⊆ ℚ̄_ℓ`) has Hodge–Tate weights `S` on the print's side (`dim_E (V ⊗ ℂ_ℓ(w))^{G}`, cyclotomic weight `−1`),
then `ρ` has Hodge–Tate weights `S` in the kernel's form `HasHTWeightsAtSelf`. Proof: §2 gives kernel weights
`−S` for `ρ^∨` (over the same `E`), and `HTDual` gives `S` for `ρ^∨^∨ = ρ`. -/
theorem kernel_of_print (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] E]
    (ρ : GQ →* GL (Fin n) E) (hρ : Continuous ρ) (S : Multiset ℤ) (hS : S.card = n)
    (h : PrintHasHTWeights ℓ E (ρ.comp (decomp ℓ)) S) : (toGR E ρ hρ).HasHTWeightsAtSelf ℓ S := by
  have hd : (EigenformHTPrinted.dualGR (toGR E ρ hρ)).HasHTWeightsAtSelf ℓ (S.map Neg.neg) := by
    refine ⟨E, inferInstance, dualE (ρ.comp (decomp ℓ)), fun σ => ?_, fun w => ?_⟩
    · apply Units.ext
      ext i j
      change (algebraMap E (PadicAlgCl ℓ)) ((ρ (decomp ℓ σ⁻¹) : Matrix (Fin n) (Fin n) E) j i) =
        ((toGR E ρ hρ).mat (decomp ℓ σ)⁻¹) j i
      rw [toGR_mat, Matrix.map_apply, map_inv (decomp ℓ) σ]
    · have := printHTMult_eq ℓ E (ρ.comp (decomp ℓ)) (-w)
      rw [neg_neg] at this
      rw [← this, h, count_neg_map]
  have h2 := EigenformHTPrinted.htDual ℓ n _ (S.map Neg.neg) (by rw [Multiset.card_map, hS]) hd
  have hSS : (S.map Neg.neg).map Neg.neg = S := by
    rw [Multiset.map_map]
    simp
  rw [hSS] at h2
  unfold GaloisRep.HasHTWeightsAtSelf at h2 ⊢
  rwa [dualGR_dualGR_restrictLocal] at h2

end Kernel

/-! ## §4. The new leaf: the printed existence form over a finite coefficient field -/

/-- **New leaf (R13, printed existence form, coefficients in a finite extension of `ℚ_ℓ`, Hodge–Tate weights on
the print's side).** Galois representations attached to newforms are Hodge–Tate at `ℓ` with weights `0, k − 1`,
every level (`ℓ ∣ N` included): for a prime `ℓ`, embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`, and a newform
`f ∈ S_k(Γ₁(N))` of weight `k ≥ 2` (Tau Ceti's `HeckeRing.GL2.Newform N k`), **there are** a finite extension
`E/ℚ_ℓ` inside `ℚ̄_ℓ` and a continuous `ρ : G_ℚ → GL₂(E)`, unramified at every `p ∤ Nℓ`, with Frobenius traces
`a_p(f)` (read through `ιC`, `ιL`) and with `ρ|_{G_{ℚ_ℓ}}` Hodge–Tate of weights `0, k − 1`, where:

* *coefficients*: `E` is the print's `K_{f,λ}` (Deligne, Diamond–Shurman 9.6.5, Taylor) or Kato's `F_λ`, embedded
  in `ℚ̄_ℓ` by the continuous extension of `ιL ∘ ιC⁻¹ : K_f → ℚ̄_ℓ` (`λ` the place it cuts out); the leaf asks only
  that some such `E` exist;
* *Hodge–Tate weights*, as printed: the multiplicity of `w` is `dim_E (V ⊗_{ℚ_ℓ} ℂ_ℓ(±w))^{G_{ℚ_ℓ}}`
  (`PrintHTSpace`, Mathlib's tensor product over `ℚ_ℓ`, `σ` acting by `ρ(σ) ⊗ χ(σ)^{±w} σ`);
* *normalizations*: either **arithmetic** Frobenius has trace `a_p` and the weights are `{0, k − 1}` in the
  convention where the cyclotomic character has weight `+1` (`PrintHasHTWeightsPos`), **or** **geometric**
  Frobenius `σ⁻¹` has trace `a_p` and the weights are `{0, k − 1}` in the convention where the cyclotomic
  character has weight `−1` (`PrintHasHTWeights`). The other two combinations of normalization and sign
  convention, written with the weights `{0, 1 − k}`, are the same two statements (`reading_arith`,
  `reading_geom`), so a print in any of the four conventions is one disjunct;
* *Frobenius*: only the trace, as "if `ιC α = a_p` then `tr ρ(Frob) = ιL α`"; a "characteristic polynomial
  `x² − a_p x + χ(p)p^{k−1}`" wording gives it (`EigenformHTPrinted.trace_of_charpoly`). No semisimplicity,
  no determinant.

Sources (no network on this host: numbers and wordings UNVERIFIED unless said otherwise). Content: Deligne,
Sém. Bourbaki 355 (1969/1971) (existence over `K_{f,λ}`, `ℓ ∤ N` trace formula); Faltings, Math. Ann. 278 (1987)
and Hodge–Tate decomposition (`ℓ ∤ N`); Saito, Invent. Math. 129 (1997) (every level); Kato, Astérisque 295 (2004)
§§9.2-9.4, (9.2.2), pp. 187-188 (`V_{F_λ}(f)` over `F_λ`, de Rham at every level: read by the locator audit,
row R13) and §11.3 (Hodge filtration jumps `0, k − 1`; UNVERIFIED). Existence form printed in the surveys Taylor,
*Galois representations*, Ann. Fac. Sci. Toulouse Math. (6) 13 (2004), and Gee, *Modularity lifting theorems*,
Essent. Number Theory 1 (2022) §2 (both UNVERIFIED). For Kato's statement the leaf is its consequence with witness
`E = F_λ`, `ρ = V_{F_λ}(f)` in a basis (∃-introduction). Replaces htnew-print's `ModularHTPrinted`, which is
proved from it (`modularHTPrinted_of_coeff`). -/
def ModularHTCoeff : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (f : HeckeRing.GL2.Newform N k), 2 ≤ k →
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρ : GQ →* GL (Fin 2) E), Continuous ρ ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ v : ValuationSubring Qbar, LiesOver v p →
        ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
      (((∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) p →
            ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
              (((ρ σ : Matrix (Fin 2) (Fin 2) E).trace : E) : PadicAlgCl ℓ) = ιL α) ∧
          PrintHasHTWeightsPos ℓ E (ρ.comp (decomp ℓ)) {0, k - 1}) ∨
        ((∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) p →
            ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
              (((ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) E).trace : E) : PadicAlgCl ℓ) = ιL α) ∧
          PrintHasHTWeights ℓ E (ρ.comp (decomp ℓ)) {0, k - 1}))

/-! ## §5. Readings and the discharge -/

section Discharge

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem neg_pair (k : ℤ) : (({0, k - 1} : Multiset ℤ).map Neg.neg) = {0, 1 - k} := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, neg_zero, neg_sub]

theorem neg_pair' (k : ℤ) : (({0, 1 - k} : Multiset ℤ).map Neg.neg) = {0, k - 1} := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, neg_zero, neg_sub]

/-- **Reading (arithmetic normalization)**: "weights `{0, 1 − k}`, cyclotomic weight `−1`" is the leaf's
"weights `{0, k − 1}`, cyclotomic weight `+1`". -/
theorem reading_arith (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) {n : ℕ} (ρ : GQp ℓ →* GL (Fin n) E) (k : ℤ) :
    PrintHasHTWeights ℓ E ρ {0, 1 - k} ↔ PrintHasHTWeightsPos ℓ E ρ {0, k - 1} := by
  rw [printHasHTWeightsPos_iff, neg_pair]

/-- **Reading (geometric normalization)**: "weights `{0, 1 − k}`, cyclotomic weight `+1`" is the leaf's
"weights `{0, k − 1}`, cyclotomic weight `−1`". -/
theorem reading_geom (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) {n : ℕ} (ρ : GQp ℓ →* GL (Fin n) E) (k : ℤ) :
    PrintHasHTWeightsPos ℓ E ρ {0, 1 - k} ↔ PrintHasHTWeights ℓ E ρ {0, k - 1} := by
  rw [printHasHTWeightsPos_iff, neg_pair']

theorem trace_toGR (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (ρ : GQ →* GL (Fin 2) E) (hρ : Continuous ρ)
    (σ : GQ) : ((toGR E ρ hρ).mat σ).trace = (((ρ σ : Matrix (Fin 2) (Fin 2) E).trace : E) : PadicAlgCl ℓ) := by
  rw [toGR_mat, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp

/-- **The field `modularHTPrinted` from the printed form over a finite coefficient field** (GLUE, all proved:
coefficient extension `E ⊆ ℚ̄_ℓ`, the assembly lemma `printHTMult_eq`, `HTDual`). -/
theorem modularHTPrinted_of_coeff (h : ModularHTCoeff) : EigenformHTPrinted.ModularHTPrinted := by
  intro ℓ _ ιC ιL N _ k f hk
  obtain ⟨E, hE, ρ, hc, hun, hfr⟩ := h ℓ ιC ιL N k f hk
  refine ⟨toGR E ρ hc, ?_⟩
  have hU : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → (toGR E ρ hc).UnramifiedAt p :=
    fun p hp hpN v hv σ hσ => by
      change Units.map _ (ρ _) = 1
      rw [hun p hp hpN v hv σ hσ, map_one]
  rcases hfr with ⟨hA, hHT⟩ | ⟨hG, hHT⟩
  · left
    refine ⟨fun p hp hpN => ⟨hU p hp hpN, fun α hα v σ hv hσ => ?_⟩, ?_⟩
    · rw [trace_toGR, hA p hp hpN α hα v σ hv hσ]
    · exact kernel_of_print E ρ hc _ (by simp) ((reading_arith E _ k).2 hHT)
  · right
    refine ⟨fun p hp hpN => ⟨hU p hp hpN, fun α hα v σ hv hσ => ?_⟩, ?_⟩
    · rw [trace_toGR, hG p hp hpN α hα v σ hv hσ]
    · exact kernel_of_print E ρ hc _ (by simp) hHT

/-- **The field `eigenformHTNew`'s consumer chain**: `eigenformHTNew` from the new leaf, through htnew-print's
discharge (with the LEAF/derived input `EigenformCoeffFieldFinite`). -/
theorem eigenformHTNew_of_coeff (h : ModularHTCoeff) (hK : DSCoeffExt.EigenformCoeffFieldFinite) :
    EigenformHTNew :=
  EigenformHTPrinted.eigenformHTNew_of_printed (modularHTPrinted_of_coeff h) hK

end Discharge

end

end HTNewAssembly
