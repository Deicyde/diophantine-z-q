import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import ZInQKernel.HDecomp.ModCurves.Glue
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.I3Linalg.RhoCont
import ZInQKernel.HDecomp.I3Linalg.TateBC
import ZInQKernel.HDecomp.Conductor.Level
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.Main
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.HDecomp.Textbook.Different
import ZInQKernel.HDecomp.Descent.Constants
import ZInQKernel.Multiplication.Certificate.Constants
import ZInQKernel.HDecomp.Descent.ProjRep
import ZInQKernel.HDecomp.Descent.B2Glue
import ZInQKernel.HDecomp.Descent.Chi

/-! Copied from scratch/c9-rhof/C9.lean (compiled there), lines 4-632. -/
section C9Copy

/-!
# c9-rhof: glue C9 for R16's representation `ρ_{f,ι}` (`LeafModCurves.rhoF`)

Check with `lake env lean scratch/c9-rhof/C9.lean`.

* §1. `rhoF` is an equivariant quotient of `V_ℓ(A) ⊗_{ℚ_ℓ} ℚ̄_ℓ` (`quotMap`, proved).
* §2. Semisimplicity of `rhoF` from Faltings' Satz 3 (`PkgI3.FaltingsSemisimple`), the leaf
  I3.M0 (`PkgI3.TateModuleFree`) and the kernel's proved base change of semisimplicity.
* §3. Continuity of `rhoF` (matrix coefficients in any basis) from I3.M0 and the kernel's
  continuity of `ρ_ℓ` (glue-rho-cont).
* §4. Density of arithmetic Frobenius elements (`FrobeniusDense`, leaf T18, copied verbatim from
  `scratch/h-decomposition/Leaves.lean`) ⇒ continuous functions agreeing on Frobenius agree.
* §5. Brauer–Nesbitt (`GlueC10.BrauerNesbittChar0`, leaf T19): `rhoF ≅ r` for every continuous
  semisimple `r` with the `AttachedTo` traces of `f` (outside a finite set).
* §6. Against R14 (`EigenformRepExists`'s `GaloisRep`), and against C8's `r₅` after the twist
  (EigenformTwist, NewformOfEigenform): C9 and the hypothesis `h₅` of `GlueC10.c10`.

Leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`.
-/

noncomputable section

namespace C9Rhof

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ## §1. `rhoF` as a quotient of `V_ℓ(A) ⊗ ℚ̄_ℓ` -/

section Quot

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

/-- Evaluation `v ↦ (φ ↦ φ v)`, `V_ℓ(A) → (ι-eigenfunctionals)^∨`, `ℚ_ℓ`-linear. -/
def ev : A.V ℓ →ₗ[ℚ_[ℓ]] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) where
  toFun v :=
    { toFun := fun φ => (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' v w := by
    ext φ
    simp
  map_smul' c v := by
    ext φ
    simp [Algebra.smul_def]

@[simp] theorem ev_apply (v : A.V ℓ) (φ : eigenFun ℓ A θ emb) :
    ev ℓ A θ emb v φ = (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v := rfl

/-- The `ℚ̄_ℓ`-linear extension `V_ℓ(A) ⊗_{ℚ_ℓ} ℚ̄_ℓ → (ι-eigenfunctionals)^∨` of `ev`. -/
def quotMap : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) →ₗ[PadicAlgCl ℓ]
    Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
  (ev ℓ A θ emb).liftBaseChange (PadicAlgCl ℓ)

theorem rhoF_ev (σ : GQ) (v : A.V ℓ) :
    rhoF ℓ A θ emb σ (ev ℓ A θ emb v) = ev ℓ A θ emb (A.galRep ℓ σ v) := by
  ext φ
  rfl

/-- `quotMap` is `G_ℚ`-equivariant from the base change of `ρ_ℓ` to `rhoF`. -/
theorem quotMap_equivariant (σ : GQ) (x : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)) :
    quotMap ℓ A θ emb (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σ x) =
      rhoF ℓ A θ emb σ (quotMap ℓ A θ emb x) := by
  induction x using TensorProduct.inductionOn with
  | tmul e v =>
    change quotMap ℓ A θ emb ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) (e ⊗ₜ v)) = _
    rw [LinearMap.baseChange_tmul]
    simp only [quotMap, LinearMap.liftBaseChange_tmul, map_smul, rhoF_ev]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `quotMap` is onto when the eigenfunctionals are finite-dimensional. -/
theorem quotMap_surjective [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    Function.Surjective (quotMap ℓ A θ emb) := by
  rw [← LinearMap.range_eq_top, quotMap, LinearMap.range_liftBaseChange]
  apply Submodule.span_eq_top_of_ne_zero
  intro z hz
  have : (z : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) ≠ 0 := by
    intro h; exact hz (Subtype.ext h)
  obtain ⟨v, hv⟩ : ∃ v, (z : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v ≠ 0 := by
    by_contra h
    push Not at h
    exact this (LinearMap.ext h)
  exact ⟨ev ℓ A θ emb v, ⟨v, rfl⟩, hv⟩

end Quot

/-! ## §2. Semisimplicity -/

section SS

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

instance : CharZero (PadicAlgCl ℓ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective

/-- `V_ℓ(A)` is finite-dimensional over `ℚ_ℓ` (from the leaf I3.M0). -/
theorem finiteDimensional_V (hT : TateModuleFree) : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨h1, h2, -⟩ := hT ℚ A ℓ hℓ
  infer_instance

/-- **Semisimplicity of `ρ_{f,ι}` (GLUE, proved from Faltings' Satz 3 and I3.M0).** -/
theorem rhoF_semisimple (hS : FaltingsSemisimple) (hT : TateModuleFree)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    (rhoF ℓ A θ emb).IsSemisimpleRepresentation := by
  have := finiteDimensional_V ℓ A hT
  have h1 : (A.galRep ℓ).IsSemisimpleRepresentation := hS ℚ A ℓ
  have h2 := GlueI3.isSemisimpleRepresentation_baseChange (PadicAlgCl ℓ) (A.galRep ℓ) h1
  exact GlueI3.isSemisimple_of_surjective _ _ h2 (quotMap ℓ A θ emb)
    (quotMap_surjective ℓ A θ emb) (fun σ x => quotMap_equivariant ℓ A θ emb σ x)

/-- The same, in the form `GlueC10` consumes. -/
theorem rhoF_isSemisimpleModule (hS : FaltingsSemisimple) (hT : TateModuleFree)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) (rhoF ℓ A θ emb).asModule :=
  (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp
    (rhoF_semisimple ℓ A θ emb hS hT)

end SS

/-! ## §3. Continuity -/

section Cont

variable (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)

/-- For every `x ∈ V_ℓ(A) ⊗ ℚ̄_ℓ` and every linear form `c` on `(ι-eigenfunctionals)^∨`,
`σ ↦ c(ρ_{f,ι}(σ) (quotMap x))` is continuous. -/
theorem continuous_coord (hT : TateModuleFree)
    (c : Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) →ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ)
    (x : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)) :
    Continuous fun σ : GQ => c (rhoF ℓ A θ emb σ (quotMap ℓ A θ emb x)) := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hρ : ∀ v : A.V ℓ, Continuous fun σ : GQ => A.galRep ℓ σ v := by
    intro v
    have h1 : Continuous fun σ : GQ => (σ, v) := continuous_id.prodMk continuous_const
    exact ((continuous_galRep_of_tateModuleFree hT A ℓ hℓ).1.comp h1).congr fun σ => rfl
  induction x using TensorProduct.inductionOn with
  | tmul e v =>
    have hL : Continuous ((c.restrictScalars ℚ_[ℓ]) ∘ₗ ev ℓ A θ emb) :=
      IsModuleTopology.continuous_of_linearMap _
    have : (fun σ : GQ => c (rhoF ℓ A θ emb σ (quotMap ℓ A θ emb (e ⊗ₜ v)))) =
        fun σ => e * ((c.restrictScalars ℚ_[ℓ]) ∘ₗ ev ℓ A θ emb) (A.galRep ℓ σ v) := by
      funext σ
      simp only [quotMap, LinearMap.liftBaseChange_tmul, map_smul, rhoF_ev, smul_eq_mul,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    rw [this]
    exact continuous_const.mul (hL.comp (hρ v))
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

/-- **Continuity of `ρ_{f,ι}` (GLUE, proved from I3.M0).** In any finite basis `b` of the
representation space, `σ ↦ [ρ_{f,ι}(σ)]_b` is continuous (Krull topology on `G_ℚ`, the
spectral-norm topology on `ℚ̄_ℓ`). -/
theorem rhoF_continuous (hT : TateModuleFree)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))) :
    Continuous fun σ : GQ => LinearMap.toMatrix b b (rhoF ℓ A θ emb σ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  obtain ⟨x, hx⟩ := quotMap_surjective ℓ A θ emb (b j)
  refine (continuous_coord ℓ A θ emb hT (b.coord i) x).congr fun σ => ?_
  simp only [LinearMap.toMatrix_apply, Module.Basis.coord_apply, hx]

end Cont

/-! ## §4. Density of arithmetic Frobenius elements (leaf T18) -/

/-- **L18 = T18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. Copied verbatim from
`HSyn.FrobeniusDense` of `scratch/h-decomposition/Leaves.lean`. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-- Two continuous functions on `G_ℚ` with Hausdorff values that agree at every arithmetic
Frobenius (`PkgI4.IsArithFrob`) above every prime outside `S` are equal (GLUE, proved from T18). -/
theorem eq_of_eq_on_arithFrob (hD : FrobeniusDense) {X : Type*} [TopologicalSpace X] [T2Space X]
    (S : Finset ℕ) (f₁ f₂ : GQ → X) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hfr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p →
      IsArithFrob τ v p → f₁ τ = f₂ τ) : f₁ = f₂ := by
  funext g
  by_contra hne
  have hopen : IsOpen {x | f₁ x ≠ f₂ x} := isOpen_ne_fun h₁ h₂
  have hmem : (fun y => g * y) ⁻¹' {x | f₁ x ≠ f₂ x} ∈ nhds (1 : GQ) := by
    apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using hne
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar _).mp hmem
  have hU : IsOpen (E.fixingSubgroup : Set GQ) := IntermediateField.fixingSubgroup_isOpen E
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := hD E.fixingSubgroup hU g S
  have hfix : g⁻¹ * τ ∈ E.fixingSubgroup := by
    have := E.fixingSubgroup.inv_mem hU'
    simpa using this
  have := hsub hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_ofPred_eq] at this
  exact this (hfr p hp hpS v τ hv hτ)

/-! ## §5. Brauer–Nesbitt (leaf T19) with arithmetic Frobenius traces -/

section BN

variable {k V W ι κ : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Continuous representations with equal traces at arithmetic Frobenius outside `S` have equal
traces everywhere (GLUE, proved from T18). -/
theorem trace_eq_of_arithFrob (hD : FrobeniusDense) (S : Finset ℕ)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (ρ : Representation k GQ V) (σ : Representation k GQ W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (htr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p →
      IsArithFrob τ v p → LinearMap.trace k V (ρ τ) = LinearMap.trace k W (σ τ)) :
    ∀ g, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g) :=
  congrFun (eq_of_eq_on_arithFrob hD S _ _ (GlueC10.continuous_trace bV ρ hρc)
    (GlueC10.continuous_trace bW σ hσc) htr)

/-- **C10-type comparison with `IsArithFrob` (GLUE, proved from T18 and T19).** -/
theorem iso_of_arithFrob [CharZero k] [FiniteDimensional k V] [FiniteDimensional k W]
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense) (S : Finset ℕ)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (ρ : Representation k GQ V) (σ : Representation k GQ W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra k GQ) σ.asModule)
    (htr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p →
      IsArithFrob τ v p → LinearMap.trace k V (ρ τ) = LinearMap.trace k W (σ τ)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k GQ] σ.asModule) :=
  hBN k GQ V W ρ σ hρ hσ (trace_eq_of_arithFrob hD S bV bW ρ σ hρc hσc htr)

end BN

/-! ## §6. C9 -/

section C9

/-- The core of C9 for a fixed `A`, `θ`, `ι` (GLUE, proved). -/
theorem c9_core (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    (N : ℕ) (hN : 0 < N) {F : Type} [Field F] (a : ℕ → F)
    (A : AbVar ℚ) (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)
    (h2 : Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2)
    (hfr : ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
      LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb (a p))
    (S : Finset ℕ) {W κ : Type} [AddCommGroup W] [Module (PadicAlgCl ℓ) W]
    [FiniteDimensional (PadicAlgCl ℓ) W] [Fintype κ] [DecidableEq κ]
    (bW : Module.Basis κ (PadicAlgCl ℓ) W) (r : Representation (PadicAlgCl ℓ) GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bW bW (r g))
    (hr : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) r.asModule)
    (hatt : ∀ p, p.Prime → p ∉ S → ¬ p ∣ N * ℓ → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p → LinearMap.trace (PadicAlgCl ℓ) W (r τ) = emb (a p)) :
    (rhoF ℓ A θ emb).IsSemisimpleRepresentation ∧
      (∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
          (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))),
        Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ emb g)) ∧
      Nonempty (r.asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ] (rhoF ℓ A θ emb).asModule) ∧
      (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) W (r g) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g)) ∧
      (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g) = emb (a p)) := by
  have hfd : FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
    Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hFrob : ∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
      LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g) = emb (a p) := by
    intro g p hp hpN hg
    rw [trace_rhoF ℓ A θ emb h2]
    exact hfr p hp hpN g hg
  have hNℓ : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  have htr : ∀ p, p.Prime → p ∉ S ∪ (N * ℓ).primeFactors → ∀ (v : ValuationSubring Qbar)
      (τ : GQ), LiesOver v p → IsArithFrob τ v p → LinearMap.trace (PadicAlgCl ℓ) W (r τ) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb τ) := by
    intro p hp hpS v τ hv hτ
    have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
    have hpN : ¬ p ∣ N * ℓ := fun h =>
      hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hNℓ⟩))
    rw [hatt p hp hpS1 hpN v τ hv hτ, hFrob τ p hp hpN (isFrobAt_of_isArithFrob τ v p hp hv hτ)]
  have hcont : ∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
      (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))),
      Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ emb g) :=
    fun b => rhoF_continuous ℓ A θ emb hT b
  let bV := Module.finBasis (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb))
  refine ⟨rhoF_semisimple ℓ A θ emb hS hT, hcont, ?_, ?_, hFrob⟩
  · exact iso_of_arithFrob hBN hD _ bW bV r _ hrc (hcont bV) hr
      (rhoF_isSemisimpleModule ℓ A θ emb hS hT) htr
  · exact trace_eq_of_arithFrob hD _ bW bV r _ hrc (hcont bV) htr

/-- **C9 (GLUE, proved from R16, Faltings' Satz 3, I3.M0, T18 and T19).** Let `f` be a newform of
weight 2, level `N` and nebentypus `χ`, `J` a `J₁(N)`, `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`. Let `r` be a
continuous semisimple finite-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` whose arithmetic
Frobenius traces outside a finite set `S` are those of `f` (through `ιC`, `ιL`). Then for R16's
`A_f` and `ρ_{f,ι} = rhoF` with `ι = ιL ∘ ιC⁻¹` (`embOf`):
(i) `ρ_{f,ι}` is 2-dimensional, semisimple and continuous;
(ii) `r ≅ ρ_{f,ι}` (Brauer–Nesbitt);
(iii) `tr r(g) = tr ρ_{f,ι}(g)` for every `g ∈ G_ℚ` (needs T18 and continuity only), which is the
hypothesis `h₅` of `GlueC10.c10`;
(iv) `tr ρ_{f,ι}(g) = ι(a_p(f))` at every `GlueC10.IsFrobAt g p`, `p ∤ Nℓ`: the hypothesis `hρ₅`. -/
theorem c9 (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ)
    (J : AbVar ℚ) (hJ : IsJ1 N J) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (S : Finset ℕ) {W κ : Type} [AddCommGroup W] [Module (PadicAlgCl ℓ) W]
    [FiniteDimensional (PadicAlgCl ℓ) W] [Fintype κ] [DecidableEq κ]
    (bW : Module.Basis κ (PadicAlgCl ℓ) W) (r : Representation (PadicAlgCl ℓ) GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bW bW (r g))
    (hr : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) r.asModule)
    (hatt : ∀ p, p.Prime → p ∉ S → ¬ p ∣ N * ℓ → ∃ α : Qbar, ιC α = coeff f p ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        LinearMap.trace (PadicAlgCl ℓ) W (r τ) = ιL α) :
    ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
      (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
      Module.finrank (PadicAlgCl ℓ)
        (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f)))) = 2 ∧
      (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).IsSemisimpleRepresentation ∧
      (∀ {ι' : Type} [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι' (PadicAlgCl ℓ)
          (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ (embOf ℓ ιC ιL (coeffField f))))),
        Continuous fun g => LinearMap.toMatrix b b (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
      Nonempty (r.asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
        (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
      (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) W (r g) =
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
      (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
        LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) =
          embOf ℓ ιC ιL (coeffField f) ⟨coeff f p, coeff_mem_coeffField f p⟩) := by
  obtain ⟨hfin, A, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  obtain ⟨h2, hfr⟩ := hrest ℓ (embOf ℓ ιC ιL (coeffField f))
  refine ⟨hfin, A, π, θ, hπ, finrank_rhoF ℓ A θ _ h2,
    c9_core ℓ hS hT hBN hD N hN (fun p => ⟨coeff f p, coeff_mem_coeffField f p⟩) A θ _ h2
      (fun p hp hpN σ hσ => (hfr p hp hpN σ hσ).1 _ rfl) S bW r hrc hr ?_⟩
  intro p hp hpS hpN v τ hv hτ
  obtain ⟨α, hα, hrα⟩ := hatt p hp hpS hpN
  rw [hrα v τ hv hτ]
  exact (embOf_spec ℓ ιC ιL (coeffField f) _ α hα).symm

end C9

end C9Rhof

/-! ## §7. Leaves R14, T24, T25 and Pan's trace form, copied verbatim from
`scratch/h-decomposition/Leaves.lean` (namespace `PkgI4`, §2-§3 there) -/

namespace PkgI4

open scoped MatrixGroups ModularForm

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **I4-L1. Galois representations of eigenforms** (Eichler–Shimura and Shimura 1971 Thm 7.14
for `k = 2`; Deligne 1971 for `k ≥ 2`; Deligne–Serre 1974 Thm 6.1 for `k = 1`; theorem numbers
UNVERIFIED). Consequence form (the published statements also give the determinant
`ε_g χ^{k−1}`). Same as hdec-faithful L27(a). -/
def EigenformRepExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g

/-- **I4-L4. Twisting an eigenform** (Shimura 1971 Prop. 3.64; Atkin–Li, Invent. Math. 48 (1978)
Prop. 3.1; locators UNVERIFIED). Consequence form. Same as hdec-faithful L28(a). -/
def EigenformTwist : Prop :=
  ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
    0 < N → 0 < m → IsNormalizedEigenform g χ →
    ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
      IsNormalizedEigenform g' χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p

/-- **I4-L5. Newform attached to an eigensystem** (Li, Math. Ann. 212 (1975), Thm 5 (strong
multiplicity one) with the decomposition `S_k = S_k^new ⊕ S_k^old`; Miyake Thm 4.6.19; locators
UNVERIFIED). Every normalized eigenform of level `M` has the Hecke eigenvalues away from `M` of a
newform of level dividing `M`. Consequence form. -/
def NewformOfEigenform : Prop :=
  ∀ (M : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ M) (g : CF M k),
    0 < M → IsNormalizedEigenform g χ →
    ∃ (N : ℕ) (χ' : DirichletCharacter ℂ N) (f : CF N k), 0 < N ∧ N ∣ M ∧ IsNewform f χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → coeff f p = coeff g p

/-- `ρ` is attached to `g` **up to the twist** `ψ`, outside a finite set `S`: Pan's conclusion
"comes from a cuspidal eigenform up to twist", in trace form (see `PanFor`). -/
def GaloisRep.AttachedUpToTwist (ρ : GaloisRep ℓ 2) (ψ : GaloisChar ℓ) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} (g : CF N k) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧
      ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
        (ρ.mat σ).trace = (ψ.toHom σ : PadicAlgCl ℓ) * ιL α

end PkgI4

namespace C9Rhof

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves

/-! ## §8. `GaloisRep` (matrix form) as a `Representation` -/

section Bridge

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- A `GaloisRep` as a `Representation` on `ℚ̄_ℓ^n`. -/
def toRep (ρ : GaloisRep ℓ n) : Representation (PadicAlgCl ℓ) GQ (Fin n → PadicAlgCl ℓ) where
  toFun σ := Matrix.toLin' (ρ.mat σ)
  map_one' := by
    simp only [GaloisRep.mat, map_one, Units.val_one, Matrix.toLin'_one]; rfl
  map_mul' σ τ := by
    simp only [GaloisRep.mat, map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl

theorem toRep_apply (ρ : GaloisRep ℓ n) (σ : GQ) : toRep ρ σ = Matrix.toLin' (ρ.mat σ) := rfl

theorem toMatrix_toRep (ρ : GaloisRep ℓ n) (σ : GQ) :
    LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (toRep ρ σ) = ρ.mat σ := by
  rw [toRep_apply, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem toRep_continuous (ρ : GaloisRep ℓ n) :
    Continuous fun σ => LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (toRep ρ σ) := by
  simp_rw [toMatrix_toRep]
  exact Units.continuous_val.comp ρ.continuous_toHom

theorem trace_toRep (ρ : GaloisRep ℓ n) (σ : GQ) :
    LinearMap.trace (PadicAlgCl ℓ) _ (toRep ρ σ) = (ρ.mat σ).trace := by
  rw [LinearMap.trace_eq_matrix_trace (PadicAlgCl ℓ) (Pi.basisFun (PadicAlgCl ℓ) (Fin n)),
    toMatrix_toRep]

/-- Invariant complements give a semisimple representation. -/
theorem semisimple_of_complements {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V)
    (h : ∀ W : Submodule k V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      ∃ W' : Submodule k V, IsCompl W W' ∧ ∀ g, ∀ v ∈ W', ρ g v ∈ W') :
    ρ.IsSemisimpleRepresentation := by
  refine ⟨fun a => ?_⟩
  obtain ⟨W', hc, hW'⟩ := h a.toSubmodule (fun g v hv => a.apply_mem_toSubmodule g hv)
  refine ⟨⟨W', fun g v hv => hW' g v hv⟩, ⟨?_, ?_⟩⟩
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact hc.inf_eq_bot
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact hc.sup_eq_top

/-- `GaloisRep.IsSemisimple` gives a semisimple `MonoidAlgebra`-module. -/
theorem toRep_semisimple (ρ : GaloisRep ℓ n) (h : ρ.IsSemisimple) :
    IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) GQ) (toRep ρ).asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  apply semisimple_of_complements
  intro W hW
  obtain ⟨W', hc, hW'⟩ := h W (fun σ => Submodule.map_le_iff_le_comap.mpr
    (fun v hv => hW σ v hv))
  exact ⟨W', hc, fun σ v hv => hW' σ (Submodule.mem_map_of_mem hv)⟩

/-- **Irreducible (Burnside form) implies semisimple (GLUE, proved).** If the image of `ρ` spans
`M_n(ℚ̄_ℓ)` as an algebra, the only invariant subspaces are `⊥` and `⊤`. -/
theorem isSemisimple_of_isIrreducible (ρ : GaloisRep ℓ n) (h : ρ.IsIrreducible) :
    ρ.IsSemisimple := by
  intro W hW
  let S : Subalgebra (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) :=
    { carrier := {M | ∀ v ∈ W, M.mulVec v ∈ W}
      mul_mem' := fun {M N} hM hN v hv => by
        rw [← Matrix.mulVec_mulVec]; exact hM _ (hN v hv)
      add_mem' := fun {M N} hM hN v hv => by
        rw [Matrix.add_mulVec]; exact W.add_mem (hM v hv) (hN v hv)
      algebraMap_mem' := fun c v hv => by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact W.smul_mem c hv }
  have hrange : Set.range ρ.mat ⊆ S := by
    rintro _ ⟨σ, rfl⟩ v hv
    exact hW σ ⟨v, hv, rfl⟩
  have hall : ∀ M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ), ∀ v ∈ W, M.mulVec v ∈ W := by
    intro M
    have : M ∈ S := by
      have h1 := Algebra.adjoin_le hrange
      rw [h] at h1
      exact h1 Algebra.mem_top
    exact this
  by_cases hbot : W = ⊥
  · refine ⟨⊤, hbot ▸ isCompl_bot_top, fun σ => le_top⟩
  · obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hw0 (funext hc)
    have htop : W = ⊤ := by
      rw [eq_top_iff]
      intro u _
      let M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) :=
        Matrix.of fun a b => if b = i then u a * (w i)⁻¹ else 0
      have hM : M.mulVec w = u := by
        funext a
        simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        field_simp
      rw [← hM]
      exact hall M w hwW
    refine ⟨⊥, htop ▸ isCompl_top_bot, fun σ => ?_⟩
    rw [Submodule.map_bot]

end Bridge

/-! ## §9. C9 against R14 and against C8's `r₅` -/

section Apps

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **C9 against R14 (GLUE, proved from R14, R16, Faltings' Satz 3, I3.M0, T18, T19).** For a
newform `f` of weight 2 and level `N`, a `J₁(N)` `J` and embeddings `ιC`, `ιL`: R14's semisimple
`ρ` attached to `f` is isomorphic to R16's `ρ_{f,ι}` (`ι = ιL ∘ ιC⁻¹`), and they have the same
trace at every `g ∈ G_ℚ`. -/
theorem c9_R14 (hR14 : PkgI4.EigenformRepExists) (hR16 : R16_EichlerShimuraJ1')
    (hS : FaltingsSemisimple) (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (f : CF N 2)
    (hf : IsNewform f χ) (J : AbVar ℚ) (hJ : IsJ1 N J) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
        (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
        Nonempty ((toRep ρ).asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
          (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
        ∀ g : GQ, (ρ.mat g).trace =
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) := by
  obtain ⟨ρ, hss, hatt⟩ := hR14 ℓ ιC ιL N 2 χ f hN (by norm_num) hf.1
  have hNℓ : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfin, A, π, θ, hπ, -, -, -, hiso, htr, -⟩ := c9 ℓ hR16 hS hT hBN hD N hN χ f hf J hJ
    ιC ιL (N * ℓ).primeFactors (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (toRep ρ)
    (toRep_continuous ρ) (toRep_semisimple ρ hss) (by
      intro p hp hpS _
      have hpN : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.mpr ⟨hp, h, hNℓ⟩)
      obtain ⟨-, α, hα, h⟩ := hatt p hp hpN
      exact ⟨α, hα, fun v τ hv hτ => by rw [trace_toRep]; exact h v τ hv hτ⟩)
  exact ⟨ρ, hss, hatt, hfin, A, π, θ, hπ, hiso, fun g => by rw [← trace_toRep]; exact htr g⟩

/-- **C9 for C8's `r₅` (GLUE, proved from T24 EigenformTwist, T25 NewformOfEigenform, R16,
Faltings' Satz 3, I3.M0, T18, T19).** C8's output: a semisimple `r : G_ℚ → GL₂(ℚ̄_ℓ)` attached up
to the twist `ψ` to a normalized eigenform `g` of weight 2 and level `M` (Pan's trace form,
`PkgI4.GaloisRep.AttachedUpToTwist`), where `ψ` is (at arithmetic Frobenius outside `S`) the
Dirichlet character `ψD` mod `m` through `ιC`, `ιL` (C8 steps 1-4: determinant argument and
Kronecker–Weber). Then there is a newform `f` of weight 2 and level `N ∣ M m²` such that for every
`J₁(N)`: `r ≅ ρ_{f,ι}` (`ι = ιL ∘ ιC⁻¹`), their traces agree on all of `G_ℚ` (`h₅` of
`GlueC10.c10`), and `tr ρ_{f,ι}(g) = ι(a_p(f))` at every `IsFrobAt g p`, `p ∤ Nℓ` (`hρ₅`).
The hypothesis `hr` follows from Pan's hypothesis `r.IsIrreducible` by
`isSemisimple_of_isIrreducible`. -/
theorem c9_r5 (hTw : PkgI4.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hT : TateModuleFree)
    (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (M : ℕ) (hM : 0 < M) (χg : DirichletCharacter ℂ M) (g : CF M 2)
    (hg : IsNormalizedEigenform g χg) (m : ℕ) (hm : 0 < m) (ψD : DirichletCharacter ℂ m)
    (ψ : GaloisChar ℓ) (S : Finset ℕ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (hrg : r.AttachedUpToTwist ψ ιC ιL g S)
    (hψ : ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        (ψ.toHom τ : PadicAlgCl ℓ) = ιL β) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N ∧ N ∣ M * m ^ 2 ∧
      IsNewform f χ ∧ ∀ J : AbVar ℚ, IsJ1 N J →
      ∃ (_ : FiniteDimensional ℚ (coeffField f)) (A : AbVar ℚ) (π : Hom J A)
        (θ : coeffField f →+* A.End0), AlgebraicGeometry.Surjective π.hom.left ∧
        Nonempty ((toRep r).asModule ≃ₗ[MonoidAlgebra (PadicAlgCl ℓ) GQ]
          (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f))).asModule) ∧
        (∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) _ (toRep r g) =
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g)) ∧
        (∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
          LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ (embOf ℓ ιC ιL (coeffField f)) g) =
            embOf ℓ ιC ιL (coeffField f) ⟨coeff f p, coeff_mem_coeffField f p⟩) := by
  obtain ⟨χ', g', hg', hcoef⟩ := hTw M m 2 χg ψD g hM hm hg
  obtain ⟨N, χ, f, hN, hNd, hf, hcf⟩ := hNew (M * m ^ 2) 2 χ' g' (by positivity) hg'
  refine ⟨N, χ, f, hN, hNd, hf, fun J hJ => ?_⟩
  have hMm : M * m ≠ 0 := Nat.mul_ne_zero hM.ne' hm.ne'
  obtain ⟨hfin, A, π, θ, hπ, -, -, -, hiso, htr, hFrob⟩ := c9 ℓ hR16 hS hT hBN hD N hN χ f hf J
    hJ ιC ιL (S ∪ (M * m).primeFactors) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (toRep r)
    (toRep_continuous r) (toRep_semisimple r hr) (by
      intro p hp hpS _
      have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
      have hpMm : ¬ p ∣ M * m := fun h =>
        hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hMm⟩))
      have hpMm2 : ¬ p ∣ M * m ^ 2 := by
        intro h
        rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
        · exact hpMm (dvd_mul_of_dvd_left h1 _)
        · exact hpMm (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h1) _)
      obtain ⟨-, α, hα, htrα⟩ := hrg p hp hpS1
      obtain ⟨β, hβ, hψp⟩ := hψ p hp hpS1
      refine ⟨β * α, ?_, fun v τ hv hτ => ?_⟩
      · rw [map_mul, hβ, hα, hcf p hp hpMm2, hcoef p hp hpMm]
      · rw [trace_toRep, htrα v τ hv hτ, hψp v τ hv hτ, map_mul])
  exact ⟨hfin, A, π, θ, hπ, hiso, htr, hFrob⟩

/-- **C9's outputs fit `GlueC10.c10` (GLUE, proved).** With `ρ₅ := ρ_{f,ι}` (`rhoF`), C9's
trace identity `tr r₅ = tr ρ_{f,ι}` (from `c9`, `c9_r5`) is `h₅`, and its Frobenius clause is
`hρ₅` for every `S` containing the primes of `Nℓ`; the remaining inputs of `c10` (the
abelian-variety traces `hr₅`, `hr₃` and the data at 3) are passed through. -/
theorem c10_via_c9 (hC : GlueC10.ChebotarevExists) (hBN : GlueC10.BrauerNesbittChar0)
    (N : ℕ) {C : Type} [Field C] (c a : ℕ → C) (A : AbVar ℚ) (θ : C →+* A.End0)
    (emb : C →+* PadicAlgCl ℓ) (S : Finset ℕ) (hSN : ∀ p, p.Prime → p ∣ N * ℓ → p ∈ S)
    {V₅ : Type} [AddCommGroup V₅] [Module (PadicAlgCl ℓ) V₅]
    (r₅ : Representation (PadicAlgCl ℓ) GQ V₅)
    (h₅ : ∀ g : GQ, LinearMap.trace (PadicAlgCl ℓ) V₅ (r₅ g) =
      LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g))
    (hFrob : ∀ (g : GQ) (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → IsFrobAt g p →
      LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb g) = emb (a p))
    (hr₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace (PadicAlgCl ℓ) V₅ (r₅ g) = emb (c p))
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k)
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (r₃ : Representation k GQ V) (ρ₃ : Representation k GQ W)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV (r₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k GQ) r₃.asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k GQ) ρ₃.asModule)
    (hr₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k V (r₃ g) = ι₃ (c p))
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k W (ρ₃ g) = ι₃ (a p)) :
    Nonempty (r₃.asModule ≃ₗ[MonoidAlgebra k GQ] ρ₃.asModule) :=
  GlueC10.c10 hC hBN S C c a (PadicAlgCl ℓ) V₅ _ emb r₅ (rhoF ℓ A θ emb)
    (fun g _ _ _ _ => h₅ g) hr₅
    (fun g p hp hpS hg => hFrob g p hp (fun h => hpS (hSN p hp h)) hg)
    k V W ι κ ι₃ bV bW r₃ ρ₃ hrc hρc hr hρ hr₃ hρ₃

end Apps

end C9Rhof
end
end C9Copy

/-! Copied from scratch/e1-sub/E1Sub.lean (compiled there), lines 4-870. -/
section E1Copy

/-! # e1-sub, part 1: `VSurjOfSurjective` (proved) and `ρ_{f,ι}` as a subrepresentation of
`V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` over `G_ℚ`.

* §1 `vSurjOfSurjective`: the glue target `LeafModCurves.VSurjOfSurjective` holds, from the I3
  leaves `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree` (Faltings 1983 Satz 3, Satz 4 /
  Kor. 1; Mumford §4) and Mathlib's `ext_of_isDominant_of_isSeparated`. (No Poincaré
  reducibility is needed.)
* §2 `exists_subrep_equiv_of_surjective`: a surjective equivariant map out of a semisimple
  representation has an equivariant section onto a subrepresentation.
* §3 `rhoF_subrep_J`: R16's `ρ_{f,ι}` (`LeafModCurves.rhoF`) is isomorphic to a
  subrepresentation of `V_ℓ(J) ⊗ ℚ̄_ℓ`, for every `J₁(N)` `J`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar
open scoped TensorProduct

namespace E1Sub

/-! ## §1. A surjective homomorphism is surjective on `V_ℓ` -/

section VSurj

variable {K : Type} [Field K]

/-- Precomposition with `π : J → A`, `Hom(A, B) → Hom(J, B)`. -/
def precomp {J A B : AbVar K} (π : Hom J A) : Hom A B →ₗ[ℤ] Hom J B :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => Hom.mk' (π.hom ≫ f.hom)
      map_zero' := Hom.ext' (by simp)
      map_add' := fun f g => Hom.ext' (by simp [MonObj.comp_mul]) }

@[simp] lemma precomp_hom {J A B : AbVar K} (π : Hom J A) (f : Hom A B) :
    (precomp π f).hom = π.hom ≫ f.hom := rfl

lemma isReduced_left (A : AbVar K) : IsReduced A.X.left :=
  GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.X.hom

/-- Precomposition with a surjective homomorphism is injective (`A` is reduced, `B` separated). -/
lemma precomp_injective {J A B : AbVar K} (π : Hom J A) (hπ : Surjective π.hom.left) :
    Function.Injective (precomp (B := B) π) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have h1 : π.hom ≫ f.hom = π.hom ≫ (1 : A.X ⟶ B.X) := by
    have := congrArg Hom.hom hf
    simp only [precomp_hom, Hom.hom_zero] at this
    rw [this, MonObj.comp_one]
  have := isReduced_left A
  apply Hom.ext'
  rw [Hom.hom_zero]
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated B.X.hom (by simp) π.hom.left
    (by rw [← Over.comp_left, ← Over.comp_left, h1])

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `V_ℓ(π)` over any field. -/
def homVK {J A : AbVar K} (π : Hom J A) : J.V ℓ →ₗ[ℚ_[ℓ]] A.V ℓ :=
  (homT (ℓ := ℓ) π).baseChange ℚ_[ℓ]

lemma homT_comp {J A B : AbVar K} (π : Hom J A) (f : Hom A B) (x : J.T ℓ) :
    homT (ℓ := ℓ) (precomp π f) x = homT f (homT π x) := by
  apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ π.hom ≫ f.hom) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ π.hom) ≫ f.hom)
  rw [Category.assoc]

lemma tateHomZl_precomp {J A B : AbVar K} (π : Hom J A) (z : ℤ_[ℓ] ⊗[ℤ] Hom A B) (x : J.T ℓ) :
    tateHomZl ℓ J B ((precomp π).lTensor ℤ_[ℓ] z) x = tateHomZl ℓ A B z (homT π x) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    simp only [LinearMap.lTensor_tmul]
    change (a • tateHom ℓ J B (precomp π f)) x = (a • tateHom ℓ A B f) (homT π x)
    simp only [LinearMap.smul_apply]
    exact congrArg (a • ·) (homT_comp ℓ π f x)
  | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]

lemma homVK_galRep {J A : AbVar K} (π : Hom J A) (σ : Field.absoluteGaloisGroup K) :
    homVK ℓ π ∘ₗ J.galRep ℓ σ = A.galRep ℓ σ ∘ₗ homVK ℓ π := by
  have h1 : homT (ℓ := ℓ) π ∘ₗ J.galT σ = A.galT σ ∘ₗ homT π :=
    LinearMap.ext fun t => homT_galT π σ t
  change (homT π).baseChange ℚ_[ℓ] ∘ₗ (J.galT σ).baseChange ℚ_[ℓ] =
    (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ (homT π).baseChange ℚ_[ℓ]
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h1]

/-- Complement of a subrepresentation, as `IsCompl` of submodules. -/
lemma isCompl_toSubmodule {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} {W W' : Subrepresentation ρ} (h : IsCompl W W') :
    IsCompl W.toSubmodule W'.toSubmodule := by
  constructor
  · rw [disjoint_iff]
    have := congrArg Subrepresentation.toSubmodule h.inf_eq_bot
    simp only [Subrepresentation.toSubmodule_inf] at this
    exact this
  · rw [codisjoint_iff]
    have := congrArg Subrepresentation.toSubmodule h.sup_eq_top
    simp only [Subrepresentation.toSubmodule_sup] at this
    exact this

/-- **`VSurjOfSurjective` over a number field (GLUE, proved from Faltings' Satz 3 and Satz 4 and
`TateModuleFree`).** If `π : J → A` is a homomorphism of abelian varieties over a number field
whose underlying morphism of schemes is surjective, then `V_ℓ(π) : V_ℓ(J) → V_ℓ(A)` is surjective.

Proof: the image `R` is `G_K`-stable; by semisimplicity it has an invariant complement `R'`. The
projection `p` onto `R'` is equivariant and kills `R`. Clearing denominators, `s • p` comes from an
equivariant `h : T_ℓ A → T_ℓ A`, which by Faltings is `tateHomZl z`, `z ∈ ℤ_ℓ ⊗ End(A)`. Since
`h ∘ T_ℓ(π) = 0`, injectivity of `tateHomZl` on `Hom(J, A)` and flatness of `ℤ_ℓ` over `ℤ` give
`z = 0` (precomposition with `π` is injective because `A` is reduced and `π` is dominant).
So `p = 0` and `R' = 0`. -/
theorem homVK_surjective (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
    [NumberField K] (J A : AbVar K) (π : Hom J A) (hπ : Surjective π.hom.left) :
    Function.Surjective (homVK ℓ π) := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfreeA, hfinA, -⟩ := hT K A ℓ hℓK
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  -- the image as a subrepresentation
  let R : Subrepresentation (A.galRep ℓ) :=
    { toSubmodule := LinearMap.range (homVK ℓ π)
      apply_mem_toSubmodule := by
        rintro σ _ ⟨w, rfl⟩
        exact ⟨J.galRep ℓ σ w, LinearMap.congr_fun (homVK_galRep ℓ π σ) w⟩ }
  obtain ⟨R', hR'⟩ := (hS K A ℓ).exists_isCompl R
  have hc := isCompl_toSubmodule hR'.symm
  -- if `R' = 0` we are done
  suffices hR'0 : R'.toSubmodule = ⊥ by
    have htop : R.toSubmodule = ⊤ := by
      have := hc.symm.sup_eq_top
      rwa [hR'0, sup_bot_eq] at this
    intro v
    have : v ∈ R.toSubmodule := htop ▸ Submodule.mem_top
    exact this
  by_contra hne
  -- the projection onto `R'` along `R`
  set p : A.V ℓ →ₗ[ℚ_[ℓ]] A.V ℓ := R'.toSubmodule.projection R.toSubmodule hc with hpdef
  have hpeq : ∀ σ, p ∘ₗ A.galRep ℓ σ = A.galRep ℓ σ ∘ₗ p :=
    GlueI3.projection_comm R' R hc
  have hpR : ∀ w, p (homVK ℓ π w) = 0 := fun w =>
    Submodule.projection_apply_of_mem_right hc ⟨w, rfl⟩
  obtain ⟨r, hrR', hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hpr : p r = r := Submodule.projection_apply_of_mem_left hc hrR'
  -- lattice clearing (as in `PkgI3.exists_hom_ne_zero_of_equivariant`)
  let ιA : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  let ιJ : J.T ℓ →ₗ[ℤ_[ℓ]] J.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (J.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) ιA := inferInstance
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (nonZeroDivisors ℤ_[ℓ]) ιA ((p.restrictScalars ℤ_[ℓ]) ∘ₗ ιA)
  have hs0 : (s : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hιA : Function.Injective ιA := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) ιA).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  have hιAσ : ∀ σ x, ιA (A.galT σ x) = A.galRep ℓ σ (ιA x) := fun σ x => by
    simp [ιA, galRep, LinearMap.baseChange_tmul]
  have hsp : ∀ x, ιA (h x) = (s : ℤ_[ℓ]) • p (ιA x) := fun x => by
    have := congrArg (fun g => g x) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
    exact this
  have hheq : IsGalEquivariant h := by
    intro σ x
    apply hιA
    rw [hsp, hιAσ, hιAσ, hsp]
    have := congrArg (fun g => g (ιA x)) (hpeq σ)
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, LinearMap.map_smul_of_tower]
  -- `h ∘ T_ℓ(π) = 0`
  have hhπ : ∀ x, h (homT π x) = 0 := fun x => by
    apply hιA
    rw [hsp, map_zero]
    have : ιA (homT π x) = homVK ℓ π (ιJ x) := by
      simp [ιA, ιJ, homVK, LinearMap.baseChange_tmul]
    rw [this, hpR, smul_zero]
  -- Faltings: `h = tateHomZl z`
  obtain ⟨z, hz⟩ : h ∈ Set.range (tateHomZl ℓ A A) := by
    rw [(hF K A A ℓ).2]; exact hheq
  have hz0 : (precomp π).lTensor ℤ_[ℓ] z = 0 := by
    apply (hF K J A ℓ).1
    rw [map_zero]
    apply LinearMap.ext; intro x
    rw [tateHomZl_precomp, hz, hhπ, LinearMap.zero_apply]
  have hinj : Function.Injective ((precomp (B := A) π).lTensor ℤ_[ℓ]) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (precomp_injective π hπ)
  have hz' : z = 0 := hinj (by rw [hz0, map_zero])
  have hh0 : h = 0 := by rw [← hz, hz', map_zero]
  -- hence `p = 0`, contradicting `p r = r ≠ 0`
  have hpι : ∀ x, p (ιA x) = 0 := fun x => by
    have h1 : (s : ℤ_[ℓ]) • p (ιA x) = 0 := by rw [← hsp, hh0]; simp
    rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ])] at h1
    exact (smul_eq_zero.mp h1).resolve_left (by
      simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne hs0)
  have hp0 : ∀ v, p v = 0 := fun v => by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q x =>
      have : (q ⊗ₜ[ℤ_[ℓ]] x : A.V ℓ) = q • ιA x := by simp [ιA, TensorProduct.smul_tmul']
      rw [this, map_smul, hpι, smul_zero]
    | add v w hv hw => rw [map_add, hv, hw, add_zero]
  exact hr0 (by rw [← hpr, hp0])

end VSurj

/-- **`LeafModCurves.VSurjOfSurjective` (the glue target of leaf-modcurves), proved.** -/
theorem vSurjOfSurjective (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree) :
    LeafModCurves.VSurjOfSurjective := by
  intro J A π ℓ _ hπ
  exact homVK_surjective ℓ hS hF hT J A π hπ

/-! ## §2. Equivariant sections out of a semisimple representation -/

section Section

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- A surjective equivariant map `q : V → W` out of a semisimple representation restricts to an
equivariant isomorphism from a subrepresentation of `V` onto `W` (an invariant complement of
`ker q`). -/
theorem exists_subrep_equiv_of_surjective (ρ : Representation k G V) (σ : Representation k G W)
    (hss : ρ.IsSemisimpleRepresentation) (q : V →ₗ[k] W) (hq : Function.Surjective q)
    (hqeq : ∀ g v, q (ρ g v) = σ g (q v)) :
    ∃ (U : Subrepresentation ρ) (e : U.toSubmodule ≃ₗ[k] W),
      ∀ g (u : U.toSubmodule), e ⟨ρ g u, U.apply_mem_toSubmodule g u.2⟩ = σ g (e u) := by
  let Kr : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker q
      apply_mem_toSubmodule := fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢; rw [hqeq, hv, map_zero] }
  obtain ⟨U, hU⟩ := hss.exists_isCompl Kr
  have hc : IsCompl Kr.toSubmodule U.toSubmodule := isCompl_toSubmodule hU
  have hbij : Function.Bijective (q ∘ₗ U.toSubmodule.subtype) := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      have hK : (u : V) ∈ Kr.toSubmodule := hu
      exact Subtype.ext ((Submodule.disjoint_def.mp hc.disjoint) u hK u.2)
    · intro w
      obtain ⟨v, rfl⟩ := hq w
      have hv : v ∈ Kr.toSubmodule ⊔ U.toSubmodule := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      have ha' : q a = 0 := ha
      exact ⟨⟨b, hb⟩, by simp [ha']⟩
  refine ⟨U, LinearEquiv.ofBijective _ hbij, fun g u => ?_⟩
  simp [LinearEquiv.ofBijective_apply, hqeq]

end Section

/-- Base change of a surjective linear map is surjective. -/
lemma baseChange_surjective {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (E : Type*) [CommRing E] [Algebra R E] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : Function.Surjective (f.baseChange E) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul e n =>
    obtain ⟨m, rfl⟩ := hf n
    exact ⟨e ⊗ₜ m, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, map_add _ _ _⟩

/-! ## §3. `ρ_{f,ι}` is a subrepresentation of `V_ℓ(J) ⊗ ℚ̄_ℓ` (over `G_ℚ`) -/

section RhoSub

open LeafModCurves
open PkgI4 (GQ)

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Evaluation of the `ι`-eigenfunctionals: `V_ℓ(A) → (eigenFun)^∨`, `v ↦ (φ ↦ φ v)`. -/
def evalEig (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ) :
    A.V ℓ →ₗ[ℚ_[ℓ]] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) where
  toFun v :=
    { toFun := fun φ => (φ : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v
      map_add' := fun φ ψ => rfl
      map_smul' := fun c φ => rfl }
  map_add' v w := by ext φ; simp
  map_smul' c v := by ext φ; simp

/-- Its `ℚ̄_ℓ`-linear extension `V_ℓ(A) ⊗ ℚ̄_ℓ → (eigenFun)^∨`. -/
def evalEigE (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ) :
    TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ) →ₗ[PadicAlgCl ℓ]
      Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
  (evalEig ℓ A θ emb).liftBaseChange (PadicAlgCl ℓ)

theorem evalEigE_equivariant (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) (σ : GQ) (x : TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)) :
    evalEigE ℓ A θ emb (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σ x) =
      rhoF ℓ A θ emb σ (evalEigE ℓ A θ emb x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e v =>
    change evalEigE ℓ A θ emb ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) (e ⊗ₜ v)) = _
    rw [LinearMap.baseChange_tmul]
    simp only [evalEigE, LinearMap.liftBaseChange_tmul, map_smul]
    congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

theorem evalEigE_surjective (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    Function.Surjective (evalEigE ℓ A θ emb) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
    inferInstance
  set w := (Module.evalEquiv (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)).symm f
  have hfw : ∀ g, f g = g w := fun g => by
    have : f = Module.evalEquiv (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) w := by simp [w]
    rw [this]; rfl
  have hv : ∀ v, (w : A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) v = 0 := fun v => by
    have hx : evalEigE ℓ A θ emb (1 ⊗ₜ v) ∈ LinearMap.range (evalEigE ℓ A θ emb) := ⟨_, rfl⟩
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [hf, Submodule.mem_bot, hfw] at this
    simp only [evalEigE, LinearMap.liftBaseChange_tmul, one_smul] at this
    exact this
  have hw0 : w = 0 := Subtype.ext (LinearMap.ext hv)
  apply hf0
  ext g
  rw [hfw, hw0, map_zero]; rfl

/-- **`ρ_{f,ι}` as a subrepresentation (GLUE, proved).** If `V_ℓ(π) : V_ℓ(J) → V_ℓ(A)` is
surjective, the representation `rhoF ℓ A θ ι` of `G_ℚ` on `(eigenFun)^∨` is equivariantly
isomorphic to a subrepresentation of `V_ℓ(J) ⊗ ℚ̄_ℓ` (Faltings' semisimplicity of `V_ℓ(J)`,
kept under extension of scalars by `GlueI3.semisimpleBaseChange`). -/
theorem rhoF_subrep_of_surj (hS : FaltingsSemisimple) (hT : TateModuleFree) (J A : AbVar ℚ)
    (π : Hom J A) (hπ : Function.Surjective (homV ℓ π)) {F : Type} [Field F]
    (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    ∃ (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ)))
      (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)),
      ∀ g (u : U.toSubmodule),
        e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ =
          rhoF ℓ A θ emb g (e u) := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfin, -⟩ := hT ℚ J ℓ hℓ
  have : FiniteDimensional ℚ_[ℓ] (J.V ℓ) := inferInstance
  have hss := GlueI3.semisimpleBaseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ (J.galRep ℓ) (hS ℚ J ℓ)
  refine exists_subrep_equiv_of_surjective _ (rhoF ℓ A θ emb) hss
    (evalEigE ℓ A θ emb ∘ₗ (homV ℓ π).baseChange (PadicAlgCl ℓ))
    ((evalEigE_surjective ℓ A θ emb).comp (baseChange_surjective _ _ hπ)) ?_
  intro g v
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [← evalEigE_equivariant]
  congr 1
  change ((homV ℓ π).baseChange _ ∘ₗ (J.galRep ℓ g).baseChange _) v =
    ((A.galRep ℓ g).baseChange _ ∘ₗ (homV ℓ π).baseChange _) v
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, homV_galRep]

/-- **`ρ_{f,ι}` is semisimple (GLUE, proved)**: it is an equivariant quotient of the semisimple
`V_ℓ(J) ⊗ ℚ̄_ℓ` (a C9 input). -/
theorem rhoF_semisimple_of_surj (hS : FaltingsSemisimple) (hT : TateModuleFree) (J A : AbVar ℚ)
    (π : Hom J A) (hπ : Function.Surjective (homV ℓ π)) {F : Type} [Field F]
    (θ : F →+* A.End0) (emb : F →+* PadicAlgCl ℓ)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)] :
    (rhoF ℓ A θ emb).IsSemisimpleRepresentation := by
  have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfin, -⟩ := hT ℚ J ℓ hℓ
  have : FiniteDimensional ℚ_[ℓ] (J.V ℓ) := inferInstance
  have hss := GlueI3.semisimpleBaseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ (J.galRep ℓ) (hS ℚ J ℓ)
  refine GlueI3.isSemisimple_of_surjective _ (rhoF ℓ A θ emb) hss
    (evalEigE ℓ A θ emb ∘ₗ (homV ℓ π).baseChange (PadicAlgCl ℓ))
    ((evalEigE_surjective ℓ A θ emb).comp (baseChange_surjective _ _ hπ)) ?_
  intro g v
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [← evalEigE_equivariant]
  congr 1
  change ((homV ℓ π).baseChange _ ∘ₗ (J.galRep ℓ g).baseChange _) v =
    ((A.galRep ℓ g).baseChange _ ∘ₗ (homV ℓ π).baseChange _) v
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, homV_galRep]

/-- **G13 as a subrepresentation (GLUE, proved from R16 and the I3 leaves).** For a newform `f`
of level `N` and any `J₁(N)` `J`: Shimura's `A_f`, `π : J ↠ A_f`, `θ : K_f → End⁰(A_f)` such that
for every prime `ℓ` and embedding `ι : K_f → ℚ̄_ℓ`, R16's `ρ_{f,ι} = rhoF ℓ A_f θ ι` is
2-dimensional, has Frobenius traces `ι(a_p(f))` at `p ∤ Nℓ`, and is equivariantly isomorphic to a
subrepresentation `U` of `V_ℓ(J) ⊗ ℚ̄_ℓ` (as `G_ℚ`-representations). This replaces the quotient
of `LeafModCurves.g13_constituent` by a sub, and discharges its hypothesis `VSurjOfSurjective`. -/
theorem rhoF_subrep_J (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2) (hf : PkgI4.IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) :
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) = 2 ∧
        (rhoF ℓ A θ emb).IsSemisimpleRepresentation ∧
        (∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∀ a : coeffField f, (a : ℂ) = PkgI4.coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb σ) = emb a) ∧
        ∃ (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ)))
          (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)),
          ∀ g (u : U.toSubmodule),
            e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) g u,
                U.apply_mem_toSubmodule g u.2⟩ = rhoF ℓ A θ emb g (e u) := by
  obtain ⟨-, A, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  refine ⟨A, π, θ, hπ, fun ℓ _ emb => ?_⟩
  obtain ⟨h2, hfr⟩ := hrest ℓ emb
  have : FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) :=
    Module.finite_of_finrank_pos (by omega)
  have hVs := vSurjOfSurjective hS hF hT J A π ℓ hπ
  refine ⟨finrank_rhoF ℓ A θ emb h2, rhoF_semisimple_of_surj ℓ hS hT J A π hVs θ emb,
    fun p hp hpN σ hσ a ha => ?_,
    rhoF_subrep_of_surj ℓ hS hT J A π (vSurjOfSurjective hS hF hT J A π ℓ hπ) θ emb⟩
  rw [trace_rhoF ℓ A θ emb h2]
  exact (hfr p hp hpN σ hσ).1 a ha

/-- `LeafModCurves.g13_constituent` with its glue hypothesis `VSurjOfSurjective` discharged. -/
theorem g13_constituent' (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2) (hf : PkgI4.IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∀ emb : coeffField f →+* PadicAlgCl ℓ, ∃ W : Submodule (PadicAlgCl ℓ)
        (J.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ), Module.finrank (PadicAlgCl ℓ) W = 2 ∧
      ∃ hW : ∀ σ : GQ, ∀ φ ∈ W, dualAct ℓ J σ φ ∈ W,
      ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        (∀ a : coeffField f, (a : ℂ) = PkgI4.coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) W ((dualAct ℓ J σ).restrict (hW σ)) = emb a) ∧
        (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
            LinearMap.det ((dualAct ℓ J σ).restrict (hW σ)) = emb c * p) :=
  g13_constituent hR16 (vSurjOfSurjective hS hF hT) N hN χ f hf J hJ ℓ

end RhoSub

end E1Sub

/-! ## §4. `V_ℓ` under base change -/

section BCsec
open scoped CategoryTheory.Obj

namespace E1Sub

section BaseChange

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- `Spec M₂ → Spec M₁` over `K`, for a `K`-algebra map `M₁ → M₂`. -/
def specHom {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra K M₁] [Algebra K M₂]
    (i : M₁ →ₐ[K] M₂) : ptObj (K := K) M₂ ⟶ ptObj (K := K) M₁ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (i : M₁ →+* M₂))) (by
    simp only [ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

/-- `Spec M → Spec M ×_{Spec K} Spec L` over `L` (graph of the structure maps). -/
def ptUnit (M : Type) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    ptObj (K := L) M ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj (ptObj (K := K) M) :=
  Over.homMk (pullback.lift (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap L M))) (by
    simp only [ptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])) (pullback.lift_snd _ _ _)

variable (L) in
/-- Points of `A` with values in an `L`-algebra `M` become points of `A_L`. -/
def bcPt (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    J.Pt M →* (J.baseChange L).Pt M where
  toFun Q := ptUnit M ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map Q
  map_one' := by
    change ptUnit M ≫ (Over.pullback _).map (1 : ptObj (K := K) M ⟶ J.X) = 1
    rw [Functor.map_one, MonObj.comp_one]
    rfl
  map_mul' Q Q' := by
    change ptUnit M ≫ (Over.pullback _).map (Q * Q') =
      (ptUnit M ≫ (Over.pullback _).map Q) * (ptUnit M ≫ (Over.pullback _).map Q')
    rw [Functor.map_mul, MonObj.comp_mul]
    rfl

lemma bcPt_fst (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] (Q : J.Pt M) :
    (bcPt L J M Q).left ≫ pullback.fst _ _ = Q.left := by
  change ((ptUnit (K := K) (L := L) M).left ≫
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map Q).left) ≫
      pullback.fst _ _ = Q.left
  simp only [ptUnit, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  exact (pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)

lemma bcPt_injective (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] : Function.Injective (bcPt L J M) := by
  intro Q Q' h
  apply Over.OverMorphism.ext
  rw [← bcPt_fst (L := L) J M Q, ← bcPt_fst (L := L) J M Q', h]

/-- Precomposition with `Spec ι`, `A(M₁) → A(M₂)`. -/
def precompPt (J : AbVar K) {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra K M₁] [Algebra K M₂]
    (i : M₁ →ₐ[K] M₂) : J.Pt M₁ →* J.Pt M₂ where
  toFun P := specHom i ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

lemma precompPt_injective (J : AbVar K) {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra K M₁]
    [Algebra K M₂] (i : M₁ →ₐ[K] M₂) : Function.Injective (precompPt J i) := by
  intro P P' h
  have hd : IsDominant (specHom (K := K) i).left := by
    constructor
    have : Subsingleton (ptObj (K := K) M₁).left :=
      inferInstanceAs (Subsingleton (PrimeSpectrum M₁))
    have hne : Nonempty (ptObj (K := K) M₂).left :=
      inferInstanceAs (Nonempty (PrimeSpectrum M₂))
    obtain ⟨x⟩ := hne
    intro y
    rw [Subsingleton.elim y ((specHom (K := K) i).left x)]
    exact subset_closure (Set.mem_range_self x)
  have : IsReduced (ptObj (K := K) M₁).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of M₁)))
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated J.X.hom (by simp) (specHom (K := K) i).left
    (by rw [← Over.comp_left, ← Over.comp_left]; exact congrArg CommaMorphism.left h)

end BaseChange

section BC2

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- The point map `A(K̄) → A_L(L̄)` along a `K`-embedding `i : K̄ → L̄`. -/
def bcPhi (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    J.Pt (AlgebraicClosure K) →* (J.baseChange L).Pt (AlgebraicClosure L) :=
  (bcPt L J (AlgebraicClosure L)).comp (precompPt J i)

lemma bcPhi_injective (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective (bcPhi J i) := by
  intro a b h
  exact precompPt_injective J i (bcPt_injective (L := L) J (AlgebraicClosure L) h)

variable (K) in
/-- `τ ∈ Gal(L̄/L)` acting on `Spec L̄` over `K`. -/
def galHomK (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    ptObj (K := K) (AlgebraicClosure L) ⟶ ptObj (K := K) (AlgebraicClosure L) :=
  specHom ((τ.restrictScalars K).toAlgHom)

lemma specHom_galHom (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) :
    specHom i ≫ galHom σ = galHomK K τ ≫ specHom i := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (i : AlgebraicClosure K →+* AlgebraicClosure L)) ≫
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) =
    Spec.map (CommRingCat.ofHom ((τ.restrictScalars K).toAlgHom :
        AlgebraicClosure L →+* AlgebraicClosure L)) ≫
      Spec.map (CommRingCat.ofHom (i : AlgebraicClosure K →+* AlgebraicClosure L))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact h x

lemma galHom_ptUnit (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    galHom τ ≫ ptUnit (K := K) (L := L) (AlgebraicClosure L) =
      ptUnit (AlgebraicClosure L) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map (galHomK K τ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.pullback_map_left]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    erw [pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd]
    erw [pullback.lift_snd]
    change Spec.map (CommRingCat.ofHom (τ : AlgebraicClosure L →+* AlgebraicClosure L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))) =
        Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact τ.commutes x

/-- **Equivariance of the point map.** For `τ ∈ G_L` and `σ ∈ G_K` with `i ∘ σ = τ ∘ i`. -/
lemma bcPhi_galAct (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) (P : J.Pt (AlgebraicClosure K)) :
    bcPhi J i (J.galAct σ P) = (J.baseChange L).galAct τ (bcPhi J i P) := by
  change ptUnit (AlgebraicClosure L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map
        (specHom i ≫ galHom σ ≫ P) =
    galHom τ ≫ ptUnit (AlgebraicClosure L) ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map (specHom i ≫ P)
  rw [← Category.assoc (galHom τ), galHom_ptUnit, Category.assoc, ← Functor.map_comp,
    ← Category.assoc (specHom i), specHom_galHom i τ σ h, Category.assoc]

/-- Every `τ ∈ G_L` restricts along `i` to some `σ ∈ G_K`. -/
lemma exists_res (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x, i (σ x) = τ (i x) := by
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := i.toRingHom.toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun x => (i.commutes x).symm)
  refine ⟨(τ.restrictScalars K).restrictNormal (AlgebraicClosure K), fun x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) (AlgebraicClosure K) x

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) → T_ℓ(A_L)` along `i`. -/
def bcT (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    J.T ℓ →ₗ[ℤ_[ℓ]] (J.baseChange L).T ℓ :=
  Tate.map (MonoidHom.toAdditive (bcPhi J i))

lemma bcT_injective (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective (bcT ℓ J i) :=
  Tate.map_injective _ (bcPhi_injective J i)

lemma bcT_galT (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) (x : J.T ℓ) :
    bcT ℓ J i (J.galT σ x) = (J.baseChange L).galT τ (bcT ℓ J i x) := by
  apply Subtype.ext; funext n
  change Additive.ofMul (bcPhi J i (J.galAct σ (Additive.toMul (x.1 n)))) =
    Additive.ofMul ((J.baseChange L).galAct τ (bcPhi J i (Additive.toMul (x.1 n))))
  rw [bcPhi_galAct J i τ σ h]

/-- `V_ℓ(A) → V_ℓ(A_L)` along `i`. -/
def bcV (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    J.V ℓ →ₗ[ℚ_[ℓ]] (J.baseChange L).V ℓ :=
  (bcT ℓ J i).baseChange ℚ_[ℓ]

lemma bcV_injective (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective (bcV ℓ J i) := by
  haveI : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (bcT_injective ℓ J i)

lemma bcV_galRep (J : AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) :
    bcV ℓ J i ∘ₗ J.galRep ℓ σ = (J.baseChange L).galRep ℓ τ ∘ₗ bcV ℓ J i := by
  have h1 : bcT ℓ J i ∘ₗ J.galT σ = (J.baseChange L).galT τ ∘ₗ bcT ℓ J i :=
    LinearMap.ext fun x => bcT_galT ℓ J i τ σ h x
  change (bcT ℓ J i).baseChange ℚ_[ℓ] ∘ₗ (J.galT σ).baseChange ℚ_[ℓ] =
    ((J.baseChange L).galT τ).baseChange ℚ_[ℓ] ∘ₗ (bcT ℓ J i).baseChange ℚ_[ℓ]
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h1]

/-- **`V_ℓ` under base change (GLUE, proved).** For an abelian variety `J` over `K`, a field
extension `L/K` and a `K`-embedding `i : K̄ → L̄`, `V_ℓ(i) : V_ℓ(J) → V_ℓ(J_L)` is injective and
intertwines `σ ∈ G_K` with `τ ∈ G_L` whenever `i ∘ σ = τ ∘ i`; after extension of scalars to any
field `E ⊇ ℚ_ℓ` it stays injective and equivariant. (With `TateModuleFree` over `K` and `L` and
`dim J_L = dim J` it is bijective, `PkgI3.Tate.map_bijective`; injectivity suffices for E1.) -/
theorem bcVE_injective (E : Type) [Field E] [Algebra ℚ_[ℓ] E] (J : AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Function.Injective ((bcV ℓ J i).baseChange E) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ (bcV_injective ℓ J i)

theorem bcVE_equivariant (E : Type) [Field E] [Algebra ℚ_[ℓ] E] (J : AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x, i (σ x) = τ (i x)) (v : TensorProduct ℚ_[ℓ] E (J.V ℓ)) :
    (bcV ℓ J i).baseChange E (GlueI3.repBaseChange E (J.galRep ℓ) σ v) =
      GlueI3.repBaseChange E ((J.baseChange L).galRep ℓ) τ ((bcV ℓ J i).baseChange E v) := by
  change ((bcV ℓ J i).baseChange E ∘ₗ (J.galRep ℓ σ).baseChange E) v =
    (((J.baseChange L).galRep ℓ τ).baseChange E ∘ₗ (bcV ℓ J i).baseChange E) v
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, bcV_galRep ℓ J i τ σ h]

end BC2

/-! ### The restriction `G_L → G_K` along `i` and bijectivity under `TateModuleFree` -/

section Res

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- The restriction `res_i : G_L → G_K`, `i ∘ res_i(τ) = τ ∘ i` (unique since `i` is injective). -/
def res (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) →* (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    where
  toFun τ := Classical.choose (exists_res i τ)
  map_one' := by
    apply AlgEquiv.ext; intro x
    apply i.toRingHom.injective
    exact (Classical.choose_spec (exists_res i 1) x).trans rfl
  map_mul' τ₁ τ₂ := by
    apply AlgEquiv.ext; intro x
    apply i.toRingHom.injective
    change i _ = i _
    rw [Classical.choose_spec (exists_res i (τ₁ * τ₂)) x]
    change τ₁ (τ₂ (i x)) = i (Classical.choose (exists_res i τ₁)
      (Classical.choose (exists_res i τ₂) x))
    rw [Classical.choose_spec (exists_res i τ₁), Classical.choose_spec (exists_res i τ₂)]

lemma res_spec (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (x : AlgebraicClosure K) :
    i (res i τ x) = τ (i x) :=
  Classical.choose_spec (exists_res i τ) x

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`T_ℓ` under base change is bijective (GLUE, proved from `TateModuleFree` and the
dimension being unchanged by base change).** `dim A_L = dim A` is a standard fact (dimension of
a scheme locally of finite type over a field is invariant under field extension; Stacks, Tag
00P4 for algebras, UNVERIFIED tag) taken here as a hypothesis; it is not needed for E1. -/
theorem bcT_bijective (hT : TateModuleFree) (J : AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (hℓ : (ℓ : K) ≠ 0)
    (hdim : (J.baseChange L).dim = J.dim) : Function.Bijective (bcT ℓ J i) := by
  have hℓL : (ℓ : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).2 hℓ
  obtain ⟨hfr, hfi, hr⟩ := hT K J ℓ hℓ
  obtain ⟨-, hfiL, hrL⟩ := hT L (J.baseChange L) ℓ hℓL
  refine Tate.map_bijective _ (bcPhi_injective J i) ?_
  have : ((Module.finrank ℤ_[ℓ] (J.T ℓ) : ℕ∞) : WithBot ℕ∞) =
      ((Module.finrank ℤ_[ℓ] ((J.baseChange L).T ℓ) : ℕ∞) : WithBot ℕ∞) := by
    rw [hr, hrL, hdim]
  exact_mod_cast this

end Res

end E1Sub

end BCsec

/-! ## §5. E1 for R16: `ρ_{f,ι}` is a subrepresentation of `V_ℓ(J₁(N)_L) ⊗ ℚ̄_ℓ` -/

namespace E1Sub

section Final

open LeafModCurves
open PkgI4 (GQ)

/-- **E1 for R16 (GLUE, proved from R16 and the I3 leaves `FaltingsSemisimple`, `FaltingsTate`,
`TateModuleFree`).** Let `f` be a weight-2 newform of level `N`, `J` a `J₁(N)` over `ℚ`, `L` any
field of characteristic `0` (in the application, the number field `L'` of N5 L861-867) and
`i : ℚ̄ → L̄` an embedding. Then there are Shimura's `A_f`, `π : J ↠ A_f` and `θ : K_f → End⁰(A_f)`
such that for every prime `ℓ` and embedding `ι : K_f → ℚ̄_ℓ`, R16's `ρ_{f,ι} = rhoF ℓ A_f θ ι` (on
a 2-dimensional `ℚ̄_ℓ`-space, with Frobenius traces `ι(a_p(f))` at `p ∤ Nℓ`) is equivariantly
isomorphic to a subrepresentation `U` of `V_ℓ(J_L) ⊗ ℚ̄_ℓ`, where `τ ∈ G_L` acts on `ρ_{f,ι}`
through any `σ ∈ G_ℚ` with `i ∘ σ = τ ∘ i` (such `σ` exists, `exists_res`, and is unique
because `i` is injective; `rhoFL_subrep_JL` restates this with `res i`). This is the `U'` that `PkgI3.E1_exists_hom_ne_zero`
consumes on the `J` side (with `K = L'`, `E = ℚ̄_ℓ`). -/
theorem rhoF_subrep_JL (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2) (hf : PkgI4.IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) (L : Type) [Field L] [Algebra ℚ L]
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) = 2 ∧
        (rhoF ℓ A θ emb).IsSemisimpleRepresentation ∧
        (∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∀ a : coeffField f, (a : ℂ) = PkgI4.coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb σ) = emb a) ∧
        ∃ (U : Subrepresentation
            (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)))
          (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)),
          ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : GQ),
            (∀ x, i (σ x) = τ (i x)) → ∀ u : U.toSubmodule,
              e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ u,
                  U.apply_mem_toSubmodule τ u.2⟩ = rhoF ℓ A θ emb σ (e u) := by
  obtain ⟨A, π, θ, hπ, hrest⟩ := rhoF_subrep_J hR16 hS hF hT N hN χ f hf J hJ
  refine ⟨A, π, θ, hπ, fun ℓ _ emb => ?_⟩
  obtain ⟨h2, hss, htr, U0, e0, he0⟩ := hrest ℓ emb
  refine ⟨h2, hss, htr, ?_⟩
  let Ψ := (bcV ℓ J i).baseChange (PadicAlgCl ℓ)
  have hΨ : Function.Injective Ψ := bcVE_injective ℓ (PadicAlgCl ℓ) J i
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)) :=
    { toSubmodule := U0.toSubmodule.map Ψ
      apply_mem_toSubmodule := by
        rintro τ _ ⟨u, hu, rfl⟩
        obtain ⟨σ, hσ⟩ := exists_res i τ
        refine ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u,
          U0.apply_mem_toSubmodule σ hu, ?_⟩
        exact bcVE_equivariant ℓ (PadicAlgCl ℓ) J i τ σ hσ u }
  let eM := Submodule.equivMapOfInjective Ψ hΨ U0.toSubmodule
  refine ⟨U, eM.symm.trans e0, fun τ σ hσ u => ?_⟩
  obtain ⟨u0, rfl⟩ := eM.surjective u
  have hmap : (⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (eM u0),
      U.apply_mem_toSubmodule τ (eM u0).2⟩ : U.toSubmodule) =
      eM ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u0,
        U0.apply_mem_toSubmodule σ u0.2⟩ := by
    apply Subtype.ext
    change GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (Ψ u0) =
      Ψ (GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u0)
    exact (bcVE_equivariant ℓ (PadicAlgCl ℓ) J i τ σ hσ u0).symm
  simp only [LinearEquiv.trans_apply]
  rw [hmap, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact he0 σ u0

/-- `ρ_{f,ι}|_{G_L}`: R16's representation restricted along `res_i : G_L → G_ℚ`. -/
def rhoFL (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) {L : Type} [Field L] [Algebra ℚ L]
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    Representation (PadicAlgCl ℓ) (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
      (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) :=
  (rhoF ℓ A θ emb).comp (res i)

/-- **E1 for R16, as `G_L`-representations.** `ρ_{f,ι}|_{G_L}` (`rhoFL`) is isomorphic to a
subrepresentation of `V_ℓ(J_L) ⊗ ℚ̄_ℓ`. -/
theorem rhoFL_subrep_JL (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2) (hf : PkgI4.IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) (L : Type) [Field L] [Algebra ℚ L]
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) = 2 ∧
        ∃ (U : Subrepresentation
            (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)))
          (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)),
          ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (u : U.toSubmodule),
            e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ u,
                U.apply_mem_toSubmodule τ u.2⟩ = rhoFL ℓ A θ emb i τ (e u) := by
  obtain ⟨A, π, θ, hπ, hrest⟩ := rhoF_subrep_JL hR16 hS hF hT N hN χ f hf J hJ L i
  refine ⟨A, π, θ, hπ, fun ℓ _ emb => ?_⟩
  obtain ⟨h2, -, -, U, e, he⟩ := hrest ℓ emb
  exact ⟨h2, U, e, fun τ u => he τ (res i τ) (res_spec i τ) u⟩

/-- **E1 for R16, assembled (GLUE, proved).** In the situation of `rhoF_subrep_JL`, with `L` a
number field: for every abelian variety `A'` over `L` (the QM surface of N5) and every nonzero
subrepresentation `U` of `V_ℓ(A') ⊗ ℚ̄_ℓ` that is `G_L`-equivariantly isomorphic to
`ρ_{f,ι}|_{G_L}` (the output C9 must supply: `r_ℓ ≅ ρ_{f,ι}` on a constituent of `V_ℓ(A')`; the
dimension, semisimplicity and trace clauses for these `A_f, θ` are exported for that purpose), there
is a nonzero homomorphism `A' → J_L` over `L`; if moreover `End⁰(A')` is a division algebra,
Poincaré reducibility (leaf T8) gives an abelian variety `Z` and `g : Z → J_L` with
`(φ, g) : A' × Z → J_L` an isogeny (N5 L861-867). -/
theorem E1_R16 (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (hP : PoincareReducibility) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : PkgI4.CF N 2) (hf : PkgI4.IsNewform f χ) (J : AbVar ℚ)
    (hJ : IsJ1 N J) (L : Type) [Field L] [NumberField L]
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb)) = 2 ∧
        (rhoF ℓ A θ emb).IsSemisimpleRepresentation ∧
        (∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∀ a : coeffField f, (a : ℂ) = PkgI4.coeff f p →
            LinearMap.trace (PadicAlgCl ℓ) _ (rhoF ℓ A θ emb σ) = emb a) ∧
        ∀ (A' : AbVar L)
        (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A'.galRep ℓ))),
        U ≠ ⊥ →
        ∀ eA : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ A θ emb),
          (∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : GQ),
            (∀ x, i (σ x) = τ (i x)) → ∀ u : U.toSubmodule,
              eA ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A'.galRep ℓ) τ u,
                  U.apply_mem_toSubmodule τ u.2⟩ = rhoF ℓ A θ emb σ (eA u)) →
          ∃ φ : Hom A' (J.baseChange L), φ ≠ 0 ∧
            (EndDivision A' → ∃ (Z : AbVar L) (g : Hom Z (J.baseChange L)),
              IsIsogenyMor (fst A'.X Z.X ≫ φ.hom * snd A'.X Z.X ≫ g.hom)) := by
  obtain ⟨A, π, θ, hπ, hrest⟩ := rhoF_subrep_JL hR16 hS hF hT N hN χ f hf J hJ L i
  refine ⟨A, π, θ, hπ, fun ℓ _ emb => ?_⟩
  obtain ⟨h2, hss, htr, U', eJ, heJ⟩ := hrest ℓ emb
  refine ⟨h2, hss, htr, fun A' U hU eA heA => ?_⟩
  let e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] U'.toSubmodule := eA.trans eJ.symm
  have he : ∀ (τ : Field.absoluteGaloisGroup L) (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A'.galRep ℓ) τ u, U.apply_mem_toSubmodule τ u.2⟩ :
        TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) ((J.baseChange L).V ℓ)) =
        GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (e u) := by
    intro τ u
    obtain ⟨σ, hσ⟩ := exists_res i τ
    have h1 : eJ ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (e u),
        U'.apply_mem_toSubmodule τ (e u).2⟩ =
        eJ (e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A'.galRep ℓ) τ u,
          U.apply_mem_toSubmodule τ u.2⟩) := by
      rw [heJ τ σ hσ (e u)]
      simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [heA τ σ hσ u]
    exact congrArg Subtype.val (eJ.injective h1).symm
  obtain ⟨φ, hφ⟩ := E1_exists_hom_ne_zero' hS hF hT A' (J.baseChange L) ℓ (PadicAlgCl ℓ) U U' hU
    e he
  exact ⟨φ, hφ, fun hdiv => hP L A' (J.baseChange L) hdiv φ hφ⟩

end Final

end E1Sub
end
end E1Copy

/-!
# g0-mod-newform: glue G13-G16 of `docs/research/h-decomposition.md` §3

The last range of `ModularConstituent` (`scratch/g0-split/part_split.lean`, piece 10): from the
outputs of G8-G12 (the constituent `r_ℓ` of `V_ℓ(A)` as a `G_ℚ`-representation, and Pan-Berger's
eigenform up to a finite twist, `G12Out`) to the outputs of G16 (a newform `f` of weight 2 and
level `1 ≤ N ≤ Q_R M²`, and for every `J₁(N)` a common constituent of `V₅(A)` and
`V₅(J₁(N)_{L'})`, E1's hypothesis).

* G13 (`g13`, proved from T24, T25, R16, Faltings' Satz 3 and 4, I3.M0, T18, T19):
  `r₅` is attached to a newform `f` outside a finite set, and `r₅|G_{L'} ≅ ρ_{f,5}|G_{L'}` is a
  common constituent of `V₅(A)` and `V₅(J₁(N)_{L'})`.
* G14 (`g14`, proved from R14, T18, T19 and the named AV-side Prop `G14TraceCompat`):
  `r₃` is attached to the same `f` outside a finite set, and `r₃`, `r₅` are isomorphic to R14's
  semisimple representations attached to `f` (in `AttachedTo` form, unramified outside `Nℓ`).
* G15 (`g15`, proved from R17 (`CarayolR17'`), the glue `SwanIndependent` and the named Prop
  `G15LocalBounds`): the exponents of `N` (`r₅` at `p ≠ 5`, `r₃` at `p = 5`).
* G16 (`g16`, proved: `GlueConductor.level_le`): `N ≤ Q_R M²`.

Leaves and glue targets are hypotheses (`def … : Prop`); no `sorry`, no `axiom`.
-/

noncomputable section

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves C9Rhof
open CategoryTheory AlgebraicGeometry

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-! ## §1. Representation lemmas (proved) -/

section RepLemmas

variable {k G V W : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- An isomorphism of `k[G]`-modules `ρ.asModule ≅ σ.asModule` is a `G`-equivariant
`k`-linear equivalence `V ≃ W`. -/
theorem equivariant_of_asModule (ρ : Representation k G V) (σ : Representation k G W)
    (φ : ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  refine ⟨{ toFun := fun v => σ.asModuleEquiv (φ (ρ.asModuleEquiv.symm v))
            invFun := fun w => ρ.asModuleEquiv (φ.symm (σ.asModuleEquiv.symm w))
            map_add' := fun v w => by simp
            map_smul' := fun c v => by
              rw [ρ.asModuleEquiv_symm_map_smul, φ.map_smul,
                Representation.asModuleEquiv_map_smul]
              simp
            left_inv := fun v => by simp
            right_inv := fun w => by simp }, fun g v => ?_⟩
  simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ρ.asModuleEquiv_symm_map_rho, φ.map_smul, Representation.asModuleEquiv_map_smul]
  simp

end RepLemmas

/-! ## §2. The conductor exponent at a level is invariant under isomorphism (proved) -/

section CondIso

open LadicCond
open PkgI4 (GQp)

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] {n : ℕ}

/-- If `e` intertwines `ρ` and `ρ'`, then `e` maps `V^{ρ(S)}` onto `V^{ρ'(S)}`. -/
theorem invariants_eq_map (ρ ρ' : GQp p →* GL (Fin n) k) (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (S : Set (GQp p)) :
    invariants ρ' S = (invariants ρ S).map (e : (Fin n → k) →ₗ[k] (Fin n → k)) := by
  ext w
  constructor
  · intro hw
    refine ⟨e.symm w, ?_, by simp⟩
    intro σ hσ
    apply e.injective
    rw [← he, e.apply_symm_apply]
    exact hw σ hσ
  · rintro ⟨v, hv, rfl⟩ σ hσ
    change (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) = e v
    rw [he]
    exact congrArg e (hv σ hσ)

theorem codimInv_eq (ρ ρ' : GQp p →* GL (Fin n) k) (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (S : Set (GQp p)) :
    codimInv ρ' S = codimInv ρ S := by
  unfold codimInv
  rw [invariants_eq_map ρ ρ' e he S, LinearEquiv.finrank_map_eq]

theorem eq_one_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (σ : GQp p) (h : ρ σ = 1) : ρ' σ = 1 := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [Matrix.toLin'_apply, he, h]
  simp

theorem isAdapted_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (L : Fld p) (hL : IsAdapted L ρ) :
    IsAdapted L ρ' :=
  ⟨hL.1, fun σ hσ => eq_one_of_intertwine ρ ρ' e he σ (hL.2 σ hσ)⟩

theorem condAt_eq_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (L : Fld p) :
    condAt L ρ' = condAt L ρ := by
  unfold condAt swanAt
  rw [codimInv_eq ρ ρ' e he]
  congr 1
  exact finsum_congr fun i => by rw [codimInv_eq ρ ρ' e he]

/-- An equivariant equivalence of `GaloisRep`s intertwines their restrictions to `G_{ℚ_p}`. -/
theorem restrictLocal_intertwine {ℓ : ℕ} [Fact ℓ.Prime] (r ρ : GaloisRep ℓ n)
    (e : (Fin n → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin n → PadicAlgCl ℓ))
    (he : ∀ g v, e (toRep r g v) = toRep ρ g (e v)) :
    ∀ σ v, ((ρ.restrictLocal p) σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).mulVec (e v) =
      e (((r.restrictLocal p) σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).mulVec v) := by
  intro σ v
  have h := he (PkgI4.decomp p σ) v
  rw [toRep_apply, toRep_apply, Matrix.toLin'_apply, Matrix.toLin'_apply] at h
  exact h.symm

end CondIso

/-! ## §3. The interface: data and outputs of G8-G12 -/

/-- **Pan-Berger's output on `r` (C7-C8 = G12's output, `docs/research/h-decomposition.md` §3).**
`r` is attached, up to the twist `ψ` and outside a finite set `S`, to a normalized eigenform `g`
of **weight 2** and level `M` (Pan's trace form, `PkgI4.GaloisRep.AttachedUpToTwist`), and `ψ` is,
at arithmetic Frobenius outside `S`, the Dirichlet character `ψD` mod `m` (N5 L758-768: the twist
is finite, then class field theory over `ℚ`; the weight comparison forces `k = 2`). -/
def PanOutput {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (r : GaloisRep ℓ 2) : Prop :=
  ∃ (M : ℕ) (χg : DirichletCharacter ℂ M) (g : CF M 2) (m : ℕ) (ψD : DirichletCharacter ℂ m)
    (ψ : GaloisChar ℓ) (S : Finset ℕ),
    0 < M ∧ IsNormalizedEigenform g χg ∧ 0 < m ∧ r.AttachedUpToTwist ψ ιC ιL g S ∧
    ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-- **`r|_{G_L}` is a constituent of `V_ℓ(A) ⊗ ℚ̄_ℓ`** (G8's `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` on `G_{L'}`): a
nonzero subrepresentation `U` of `V_ℓ(A) ⊗ ℚ̄_ℓ` (`A` over `L`) with a linear isomorphism
`U ≃ ℚ̄_ℓ²` carrying `τ ∈ G_L` to `r(σ)` for every `σ ∈ G_ℚ` with `i ∘ σ = τ ∘ i`
(`i : ℚ̄ → L̄`; such `σ` exist and are unique, `E1Sub.exists_res`). -/
def IsConstituentOf (ℓ : ℕ) [Fact ℓ.Prime] {L : Type} [Field L] [Algebra ℚ L] (A : AbVar L)
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) (r : GaloisRep ℓ 2) : Prop :=
  ∃ (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ)), U ≠ ⊥ ∧
    ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : GQ), (∀ x, i (σ x) = τ (i x)) →
      ∀ u : U.toSubmodule,
        e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) τ u, U.apply_mem_toSubmodule τ u.2⟩ =
          toRep r σ (e u)

/-- The data that G8-G12 produce for the model `A/L'`: an embedding `i : ℚ̄ → L̄'`, embeddings
`ιC : ℚ̄ → ℂ`, `ι₅ : ℚ̄ → ℚ̄₅`, `ι₃ : ℚ̄ → ℚ̄₃`, and the two `G_ℚ`-representations `r₅`, `r₃`
(N5 L719-734: `r_ℓ`, made a `G_ℚ`-representation by the Tate action and the descent of G7). -/
structure ModData (L : Type) [Field L] [NumberField L] (A : AbVar L) where
  i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L
  ιC : Qbar →ₐ[ℚ] ℂ
  ι5 : Qbar →ₐ[ℚ] PadicAlgCl 5
  ι3 : Qbar →ₐ[ℚ] PadicAlgCl 3
  r5 : GaloisRep 5 2
  r3 : GaloisRep 3 2

/-- **G12Out: the output of G8-G12** (the range of task g0-mod-galois) on the data `D`:
`r₅`, `r₃` irreducible (C2, Burnside form), constituents of `V₅(A)`, `V₃(A)` on `G_{L'}` (C1),
and Pan-Berger's weight-2 eigenform up to a finite twist for `r₅` (C3-C8). -/
def G12Spec {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) : Prop :=
  D.r5.IsIrreducible ∧ D.r3.IsIrreducible ∧ IsConstituentOf 5 A D.i D.r5 ∧
    IsConstituentOf 3 A D.i D.r3 ∧ PanOutput D.ιC D.ι5 D.r5

/-- `G12Out A`: some data `D` for `A` satisfy `G12Spec`. -/
def G12Out {L : Type} [Field L] [NumberField L] (A : AbVar L) : Prop :=
  ∃ D : ModData L A, G12Spec D

/-- **Open part of G14 (glue, AV side; N5 L776-795).** At every arithmetic Frobenius `τ` above
`p ∉ S`, the traces of `r₅` and `r₃` are the images of one algebraic number: if
`tr r₅(τ) = ι₅(c)` then `tr r₃(τ) = ι₃(c)`. Glazer's proof: for `p ∉ T ∪ {3, 5}` a lift `σ` of
Frobenius, the relative Frobenius of the reduction of `A` composed with `μ̄_σ` is an endomorphism
of `Ā_v` whose characteristic polynomial on `V_ℓ` is independent of `ℓ` (T7, with T3, T4); half
its trace times `β(σ)⁻¹a_σ` is the common value. It is a statement about the `r_ℓ` built in G8
from the descent data of G7 (not about arbitrary constituents: a constituent determines `r_ℓ`
only on `G_{L'}`), so it is to be proved together with that construction. -/
def G14TraceCompat {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p → ∀ c : Qbar,
      (D.r5.mat τ).trace = D.ι5 c → (D.r3.mat τ).trace = D.ι3 c

/-- Glazer's local bound for `r` at `p` (N5 L798-852), at a level `L_p` adapted to `r|G_{ℚ_p}`:
the conductor exponent is `≤ E₀` if `p ≤ R` (`R = D`), `≤ 2` if `p > R`, and `0` if
`p ∉ T = S ∪ supp M_S(u)`. -/
def LocalBound (u : ℚ) (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) :
    Prop :=
  ∃ Lp : LadicCond.Fld p, LadicCond.IsAdapted Lp (r.restrictLocal p) ∧
    ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      LadicCond.condAt Lp (r.restrictLocal p) ≤ (ZInQ.heightE0 : ℚ)) ∧
    ((ZInQ.heightD : ℝ) < p → LadicCond.condAt Lp (r.restrictLocal p) ≤ 2) ∧
    (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u →
      LadicCond.condAt Lp (r.restrictLocal p) = 0)

/-- **Open part of G15 (glue, D1-D4 on the actual `A`; N5 L796-852).** `r₅` satisfies Glazer's
local bound at every prime `p ≠ 5` and `r₃` at `p = 5`. The cores are proved over the kernel's
finite-level objects (D1 `GlueConductor.D1_genuine`, D2 `PkgI2.D2_fixed_of_raynaud`, D3
`GlueConductor.fourth_pow_mem`, D4 `PkgI6.artinConductor_le_of_upper`,
`LadicCond.condAt_le_of_upper`); what is open is their instantiation on the `r_ℓ` built in G8
(Raynaud's semistability over `L'_v(A[3])`, wild inertia on `V_ℓ(A)`, the wild part of `β`). -/
def G15LocalBounds {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (u : ℚ) : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalBound u p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalBound u p ⟨hp⟩ 3 _ D.r3)

/-! ## §4. G13: the newform and the common constituent -/

/-- `r` is attached to `f` outside `S`: at every arithmetic Frobenius above `p ∉ S`, the trace is
`ι_L(α)` with `ι_C(α) = a_p(f)` (`AttachedUpToTwist` with trivial twist, without the
unramifiedness clause). -/
def AttachedOutside {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} (f : CF N k) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S → ∃ α : Qbar, ιC α = coeff f p ∧
    ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
      (r.mat τ).trace = ιL α

/-- E1's hypothesis (copied from `scratch/g0-split/part_split.lean`): for some prime `ℓ` and
field `E ⊇ ℚ_ℓ`, `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a common nonzero constituent, as
`G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-- **G13Out** on the data `D`: a newform `f` of weight 2, level `N ≥ 1` and nebentypus `χ`;
`r₅` is attached to `f` outside a finite set; and for every `J₁(N)` `J` over `ℚ`, `V₅(A)` and
`V₅(J_{L'})` have a common constituent (`r₅|G_{L'} ≅ ρ_{f,5}|G_{L'}`). -/
def G13Spec {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) : Prop :=
  0 < N ∧ IsNewform f χ ∧ D.r5.IsSemisimple ∧ D.r3.IsSemisimple ∧
    (∃ S, AttachedOutside D.r5 D.ιC D.ι5 f S) ∧
    ∀ J : AbVar ℚ, IsJ1 N J → CommonConstituent A (J.baseChange L)

/-- The `J`-side of E1 for a given Shimura quotient `π : J ↠ A_f` (the proof of
`E1Sub.rhoF_subrep_JL`, for given `A_f`, `π`, `θ`). -/
theorem jSide (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
    (J Af : AbVar ℚ) (π : Hom J Af) (hπ : Surjective π.hom.left) {F : Type} [Field F]
    (θ : F →+* Af.End0) (ℓ : ℕ) [Fact ℓ.Prime] (emb : F →+* PadicAlgCl ℓ)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ Af θ emb)]
    (L : Type) [Field L] [Algebra ℚ L] (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    ∃ (U : Subrepresentation
        (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)))
      (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ Af θ emb)),
      ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : GQ),
        (∀ x, i (σ x) = τ (i x)) → ∀ u : U.toSubmodule,
          e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ u,
              U.apply_mem_toSubmodule τ u.2⟩ = rhoF ℓ Af θ emb σ (e u) := by
  obtain ⟨U0, e0, he0⟩ := E1Sub.rhoF_subrep_of_surj ℓ hS hT J Af π
    (E1Sub.vSurjOfSurjective hS hF hT J Af π ℓ hπ) θ emb
  let Ψ := (E1Sub.bcV ℓ J i).baseChange (PadicAlgCl ℓ)
  have hΨ : Function.Injective Ψ := E1Sub.bcVE_injective ℓ (PadicAlgCl ℓ) J i
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)) :=
    { toSubmodule := U0.toSubmodule.map Ψ
      apply_mem_toSubmodule := by
        rintro τ _ ⟨u, hu, rfl⟩
        obtain ⟨σ, hσ⟩ := E1Sub.exists_res i τ
        refine ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u,
          U0.apply_mem_toSubmodule σ hu, ?_⟩
        exact E1Sub.bcVE_equivariant ℓ (PadicAlgCl ℓ) J i τ σ hσ u }
  let eM := Submodule.equivMapOfInjective Ψ hΨ U0.toSubmodule
  refine ⟨U, eM.symm.trans e0, fun τ σ hσ u => ?_⟩
  obtain ⟨u0, rfl⟩ := eM.surjective u
  have hmap : (⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (eM u0),
      U.apply_mem_toSubmodule τ (eM u0).2⟩ : U.toSubmodule) =
      eM ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u0,
        U0.apply_mem_toSubmodule σ u0.2⟩ := by
    apply Subtype.ext
    change GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (Ψ u0) =
      Ψ (GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u0)
    exact (E1Sub.bcVE_equivariant ℓ (PadicAlgCl ℓ) J i τ σ hσ u0).symm
  simp only [LinearEquiv.trans_apply]
  rw [hmap, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact he0 σ u0

/-- **Twist bookkeeping (proved, from T24 and T25; the computation of `C9Rhof.c9_r5`).** From
Pan-Berger's output, a newform `f` of weight 2 and level `N ∣ M m²` to which `r` is attached
outside a finite set. -/
theorem newform_of_pan (hTw : PkgI4.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (r : GaloisRep ℓ 2) (h : PanOutput ιC ιL r) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N ∧ IsNewform f χ ∧
      ∃ S, AttachedOutside r ιC ιL f S := by
  obtain ⟨M, χg, g, m, ψD, ψ, S, hM, hg, hm, hrg, hψ⟩ := h
  obtain ⟨χ', g', hg', hcoef⟩ := hTw M m 2 χg ψD g hM hm hg
  obtain ⟨N, χ, f, hN, hNd, hf, hcf⟩ := hNew (M * m ^ 2) 2 χ' g' (by positivity) hg'
  refine ⟨N, χ, f, hN, hf, S ∪ (M * m).primeFactors, fun p hp hpS => ?_⟩
  have hMm : M * m ≠ 0 := Nat.mul_ne_zero hM.ne' hm.ne'
  have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
  have hpMm : ¬ p ∣ M * m := fun h =>
    hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hMm⟩))
  have hpMm2 : ¬ p ∣ M * m ^ 2 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact hpMm (dvd_mul_of_dvd_left h1 _)
    · exact hpMm (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h1) _)
  obtain ⟨-, α, hα, htrα⟩ := hrg p hp hpS1
  obtain ⟨β, hβ, hψp⟩ := hψ p hp hpS1
  refine ⟨β * α, ?_, fun v τ hv hτ => ?_⟩
  · rw [map_mul, hβ, hα, hcf p hp hpMm2, hcoef p hp hpMm]
  · rw [htrα v τ hv hτ, hψp v τ hv hτ, map_mul]

/-- **E1 on `A` for a representation attached to `f` (proved from R16, Faltings' Satz 3 and 4,
I3.M0, T18, T19).** If `r` is semisimple, attached to the newform `f` outside a finite set, and
`r|_{G_L}` is a constituent of `V_ℓ(A)`, then for every `J₁(N)` `J`, `V_ℓ(A)` and `V_ℓ(J_L)` have
a common constituent: `r|G_L ≅ ρ_{f,ι}|G_L` (C9, Brauer–Nesbitt), which is a sub of
`V_ℓ(J_L) ⊗ ℚ̄_ℓ` (E1Sub). -/
theorem commonConstituent_of_attached (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) {L : Type} [Field L] [NumberField L] (A : AbVar L)
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) (ℓ : ℕ) [Fact ℓ.Prime]
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (hA : IsConstituentOf ℓ A i r) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (f : CF N 2) (hf : IsNewform f χ) (S : Finset ℕ) (hatt : AttachedOutside r ιC ιL f S)
    (J : AbVar ℚ) (hJ : IsJ1 N J) : CommonConstituent A (J.baseChange L) := by
  obtain ⟨hfin, Af, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  set emb := embOf ℓ ιC ιL (coeffField f) with hemb
  obtain ⟨h2, hfr⟩ := hrest ℓ emb
  haveI : FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ Af θ emb) :=
    Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  obtain ⟨-, -, ⟨φ⟩, -, -⟩ := c9_core ℓ hS hT hBN hD N hN
    (fun p => (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f)) Af θ emb h2
    (fun p hp hpN σ hσ => (hfr p hp hpN σ hσ).1 _ rfl) S (Pi.basisFun (PadicAlgCl ℓ) (Fin 2))
    (toRep r) (toRep_continuous r) (toRep_semisimple r hr) (by
      intro p hp hpS _ v τ hv hτ
      obtain ⟨α, hα, hrα⟩ := hatt p hp hpS
      rw [trace_toRep, hrα v τ hv hτ]
      exact (embOf_spec ℓ ιC ιL (coeffField f) _ α hα).symm)
  obtain ⟨eφ, heφ⟩ := equivariant_of_asModule _ _ φ
  obtain ⟨U, eR, hU, heR⟩ := hA
  obtain ⟨U', eJ, heJ⟩ := jSide hS hF hT J Af π hπ θ ℓ emb L i
  let e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] U'.toSubmodule := (eR.trans eφ).trans eJ.symm
  refine ⟨ℓ, inferInstance, PadicAlgCl ℓ, inferInstance, inferInstance, U, U', e, hU,
    fun τ u => ?_⟩
  obtain ⟨σ, hσ⟩ := E1Sub.exists_res i τ
  have h1 : eJ ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (e u),
      U'.apply_mem_toSubmodule τ (e u).2⟩ =
      eJ (e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) τ u,
        U.apply_mem_toSubmodule τ u.2⟩) := by
    rw [heJ τ σ hσ (e u)]
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [heR τ σ hσ u, heφ]
  exact congrArg Subtype.val (eJ.injective h1).symm

/-- **G13 (GLUE, proved from T24, T25, R16, Faltings' Satz 3 and 4, I3.M0, T18, T19).** -/
theorem g13 (hTw : PkgI4.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hF : FaltingsTate)
    (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (h12 : G12Spec D) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), G13Spec D N χ f := by
  obtain ⟨hirr5, hirr3, hA5, -, hpan⟩ := h12
  obtain ⟨N, χ, f, hN, hf, S, hatt⟩ := newform_of_pan hTw hNew D.ιC D.ι5 D.r5 hpan
  have hss5 := isSemisimple_of_isIrreducible D.r5 hirr5
  refine ⟨N, χ, f, hN, hf, hss5, isSemisimple_of_isIrreducible D.r3 hirr3, ⟨S, hatt⟩,
    fun J hJ => ?_⟩
  exact commonConstituent_of_attached hR16 hS hF hT hBN hD A D.i 5 D.ιC D.ι5 D.r5 hss5 hA5 N hN
    χ f hf S hatt J hJ

/-! ## §5. G14: `r₃` and `r₅` against R14's representations of `f` -/

/-- **Brauer–Nesbitt against R14 (proved from R14, T18, T19).** A semisimple `r` attached to the
newform `f` outside a finite set is equivariantly isomorphic to R14's semisimple `ρ` attached to
`f` (in `AttachedTo` form: unramified outside `Nℓ`, traces `a_p` at every `p ∤ Nℓ`). -/
theorem iso_R14 (hR14 : PkgI4.EigenformRepExists) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (f : CF N 2) (hf : IsNewform f χ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (S : Finset ℕ) (hatt : AttachedOutside r ιC ιL f S) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∃ e : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ),
        ∀ g v, e (toRep r g v) = toRep ρ g (e v) := by
  obtain ⟨ρ, hss, hρ⟩ := hR14 ℓ ιC ιL N 2 χ f hN (by norm_num) hf.1
  have hNℓ : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨φ⟩ := iso_of_arithFrob hBN hD (S ∪ (N * ℓ).primeFactors)
    (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (toRep r)
    (toRep ρ) (toRep_continuous r) (toRep_continuous ρ) (toRep_semisimple r hr)
    (toRep_semisimple ρ hss) (by
      intro p hp hpS v τ hv hτ
      have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
      have hpN : ¬ p ∣ N * ℓ := fun h =>
        hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hNℓ⟩))
      obtain ⟨α, hα, hrα⟩ := hatt p hp hpS1
      obtain ⟨-, α', hα', hρα⟩ := hρ p hp hpN
      have : α = α' := ιC.toRingHom.injective (hα.trans hα'.symm)
      rw [trace_toRep, trace_toRep, hrα v τ hv hτ, hρα v τ hv hτ, this])
  obtain ⟨e, he⟩ := equivariant_of_asModule _ _ φ
  exact ⟨ρ, hss, hρ, e, he⟩

/-- **G14Out** on the data `D` and the newform `f`: both `r₅` and `r₃` are equivariantly
isomorphic to semisimple representations attached to `f` in R14's `AttachedTo` form. -/
def G14Spec {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (N : ℕ)
    (f : CF N 2) : Prop :=
  (∃ ρ : GaloisRep 5 2, ρ.IsSemisimple ∧ ρ.AttachedTo D.ιC D.ι5 f ∧
      ∃ e : (Fin 2 → PadicAlgCl 5) ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5),
        ∀ g v, e (toRep D.r5 g v) = toRep ρ g (e v)) ∧
    (∃ ρ : GaloisRep 3 2, ρ.IsSemisimple ∧ ρ.AttachedTo D.ιC D.ι3 f ∧
      ∃ e : (Fin 2 → PadicAlgCl 3) ≃ₗ[PadicAlgCl 3] (Fin 2 → PadicAlgCl 3),
        ∀ g v, e (toRep D.r3 g v) = toRep ρ g (e v))

/-- **G14 (GLUE, proved from R14, T18, T19 and the AV-side Prop `G14TraceCompat`).** -/
theorem g14 (hR14 : PkgI4.EigenformRepExists) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (h13 : G13Spec D N χ f)
    (hc : G14TraceCompat D) : G14Spec D N f := by
  obtain ⟨hN, hf, hss5, hss3, ⟨S, hatt⟩, -⟩ := h13
  obtain ⟨Sc, hSc⟩ := hc
  have hatt3 : AttachedOutside D.r3 D.ιC D.ι3 f (S ∪ Sc) := by
    intro p hp hpS
    have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
    have hpS2 : p ∉ Sc := fun h => hpS (Finset.mem_union_right _ h)
    obtain ⟨α, hα, hrα⟩ := hatt p hp hpS1
    exact ⟨α, hα, fun v τ hv hτ => hSc p hp hpS2 v τ hv hτ α (hrα v τ hv hτ)⟩
  exact ⟨iso_R14 hR14 hBN hD D.ιC D.ι5 N hN χ f hf D.r5 hss5 S hatt,
    iso_R14 hR14 hBN hD D.ιC D.ι3 N hN χ f hf D.r3 hss3 (S ∪ Sc) hatt3⟩

/-! ## §6. G15: the exponents of `N` -/

/-- **G15Out**: the exponents of the level, N5 L846-852 (`a_p = v_p(N)` by Carayol). -/
def G15Out (N : ℕ) (u : ℚ) : Prop :=
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ (ZInQ.heightD : ℝ) → N.factorization p ≤ ZInQ.heightE0) ∧
    (∀ p : ℕ, p.Prime → (ZInQ.heightD : ℝ) < p → N.factorization p ≤ 2) ∧
    (∀ p : ℕ, p.Prime → p ∣ N → p ∈ ZInQ.Mult.S_mul ∨ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u)

/-- Carayol at one prime, transported along an equivariant equivalence (proved from R17's
adapted-level form). -/
theorem factorization_eq_condAt (hCar : LadicCond.CarayolR17) {ℓ : ℕ} [Fact ℓ.Prime]
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ) (r : GaloisRep ℓ 2)
    (ρ : GaloisRep ℓ 2) (hss : ρ.IsSemisimple) (hρ : ρ.AttachedTo ιC ιL f)
    (e : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ))
    (he : ∀ g v, e (toRep r g v) = toRep ρ g (e v)) (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (Lp : LadicCond.Fld p) (hL : LadicCond.IsAdapted Lp (r.restrictLocal p)) :
    (N.factorization p : ℚ) = LadicCond.condAt Lp (r.restrictLocal p) := by
  have hint := restrictLocal_intertwine (p := p) r ρ e he
  rw [← hCar ℓ ιC ιL N χ f ρ p hN hf hss hρ hpℓ Lp
    (isAdapted_of_intertwine _ _ e hint Lp hL)]
  exact condAt_eq_of_intertwine _ _ e hint Lp

/-- **G15 (GLUE, proved from R17 (`CarayolR17'`), the glue `SwanIndependent` and the open Prop
`G15LocalBounds`).** -/
theorem g15 (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (h13 : G13Spec D N χ f) (h14 : G14Spec D N f)
    (u : ℚ) (hloc : G15LocalBounds D u) : G15Out N u := by
  have hC := LadicCond.carayolR17_of_R17' hSw hCar
  obtain ⟨hN, hf, -⟩ := h13
  obtain ⟨⟨ρ5, hss5, hρ5, e5, he5⟩, ⟨ρ3, hss3, hρ3, e3, he3⟩⟩ := h14
  -- the exponent at `p` is a conductor exponent of `r₅` (`p ≠ 5`) or `r₃` (`p = 5`)
  have key : ∀ p : ℕ, ∀ hp : p.Prime, ∃ (Lp : @LadicCond.Fld p ⟨hp⟩) (c : ℚ),
      (N.factorization p : ℚ) = c ∧ ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → c ≤ (ZInQ.heightE0 : ℚ)) ∧
      ((ZInQ.heightD : ℝ) < p → c ≤ 2) ∧
      (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → c = 0) := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases h5 : p = 5
    · obtain ⟨Lp, had, h1, h2, h3⟩ := (hloc p hp).2 h5
      exact ⟨Lp, _, factorization_eq_condAt hC D.ιC D.ι3 N hN χ f hf D.r3 ρ3 hss3 hρ3 e3 he3 p
        (by omega) Lp had, h1, h2, h3⟩
    · obtain ⟨Lp, had, h1, h2, h3⟩ := (hloc p hp).1 h5
      exact ⟨Lp, _, factorization_eq_condAt hC D.ιC D.ι5 N hN χ f hf D.r5 ρ5 hss5 hρ5 e5 he5 p
        h5 Lp had, h1, h2, h3⟩
  refine ⟨fun p hp hpR => ?_, fun p hp hpR => ?_, fun p hp hpN => ?_⟩
  · obtain ⟨Lp, c, hc, h1, -, -⟩ := key p hp
    have := h1 hpR
    rw [← hc] at this
    exact_mod_cast this
  · obtain ⟨Lp, c, hc, -, h2, -⟩ := key p hp
    have := h2 hpR
    rw [← hc] at this
    exact_mod_cast this
  · by_contra hcon
    push_neg at hcon
    obtain ⟨Lp, c, hc, -, -, h3⟩ := key p hp
    have h0 := h3 hcon.1 hcon.2
    rw [h0] at hc
    have hfac : N.factorization p = 0 := by exact_mod_cast hc
    have hpos : 0 < N.factorization p := hp.factorization_pos_of_dvd hN.ne' hpN
    omega

/-! ## §7. G16: `N ≤ Q_R M²` -/

/-- **G16 (GLUE, proved: `GlueConductor.level_le` with `R = D`, `S = S_mul`).** -/
theorem g16 (N : ℕ) (hN : 0 < N) (u : ℚ) (h15 : G15Out N u) :
    (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD *
      (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 := by
  obtain ⟨hsmall, hlarge, hout⟩ := h15
  exact GlueConductor.level_le ZInQ.Mult.S_mul u ZInQ.heightD GlueAssembly.one_le_heightD_real
    (fun p hp => by exact_mod_cast ZInQ.Mult.le_heightD_of_mem_S_mul hp) N hN.ne'
    hsmall hlarge hout

/-! ## §7b. G15's local bounds from ramification statements (proved from L8 and
`AdaptedExists`) -/

section LocalRamSec

open LadicCond
open PkgI4 (GQp)

/-- Glazer's uniform bound for the last upper break, `U₀ = 4(DG₀)²` (N5 L826-830). -/
def U0 : ℝ := 4 * ((ZInQ.heightD * ZInQ.heightG0 : ℕ) : ℝ) ^ 2

/-- **The ramification of `r` at `p` that D1-D4 establish (N5 L819-852).** (i) for `p ≤ R`
(`R = D`): every absolute upper ramification group `G_{ℚ_p}^t`, `t > U₀`, acts trivially;
(ii) for `p > R`: wild inertia acts trivially (tame case); (iii) for `p ∉ T = S ∪ supp M_S(u)`:
inertia acts trivially (G11, in local form). -/
def LocalRam (u : ℚ) (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) :
    Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, U0 < t → ∀ σ ∈ upperAbs p t, r.restrictLocal p σ = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ wildSet, r.restrictLocal p σ = 1) ∧
    (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u →
      ∀ σ ∈ inertiaSet, r.restrictLocal p σ = 1)

/-- **Open part of G15, reduced (glue, D1-D4 on the actual `A`).** `LocalRam` for `r₅` at every
`p ≠ 5` and for `r₃` at `p = 5`. Proved cores over the kernel's finite-level objects: D1
(`GlueConductor.D1_genuine`, the break bound `≤ 4a²` from the different), D2
(`PkgI2.D2_fixed_of_raynaud`: wild inertia trivial on `V_ℓ(A)` after Raynaud), D3
(`GlueConductor.fourth_pow_mem`: the wild part of `β` at 2). Open: their instantiation on the
`r_ℓ` built in G8, and the transport from the finite-level filtrations to `upperAbs`. -/
def G15Ram {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ) :
    Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalRam u p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalRam u p ⟨hp⟩ 3 _ D.r3)

variable {p : ℕ} [Fact p.Prime]

/-- `ρ|_{G_{ℚ_p}}` is continuous (`Field.absoluteGaloisGroup.map` is a continuous hom). -/
theorem restrictLocal_continuous {ℓ n : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ n) :
    Continuous (r.restrictLocal p) :=
  r.continuous_toHom.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous

/-- Trivial wild inertia ⇒ `Sw_L(ρ) = 0`. -/
theorem swanAt_eq_zero_of_wild {k : Type*} [Field k] {n : ℕ} {ρ : GQp p →* GL (Fin n) k}
    (h : ∀ σ ∈ wildSet, ρ σ = 1) (L : Fld p) : swanAt L ρ = 0 := by
  rw [swanAt]
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  rw [codimInv_eq_zero (fun σ hσ => h σ hσ.2)]
  simp

/-- `2(1 + U₀) ≤ E₀`. -/
theorem two_one_add_U0_le : 2 * (1 + U0) ≤ (ZInQ.heightE0 : ℝ) := by
  have hD : 0 < ZInQ.heightD := by
    rw [ZInQ.Compiler.Precision.heightD_eq]
    exact Nat.mul_pos (Nat.factorial_pos 324) (by positivity)
  have h1 : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
    Nat.mul_pos hD (by unfold ZInQ.heightG0; norm_num)
  rw [ZInQ.Compiler.Precision.heightE0_eq, U0]
  generalize ZInQ.heightD * ZInQ.heightG0 = x at h1 ⊢
  have hx : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h1
  have hx2 : (1 : ℝ) ≤ (x : ℝ) ^ 2 := one_le_pow₀ hx
  have hc : (((10 * x ^ 2 : ℕ)) : ℝ) = 10 * (x : ℝ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_pow]; rfl
  rw [hc]
  linarith

/-- **G15's local bound from the ramification (GLUE, proved from L8 `SwanIntegral` and
`AdaptedExists`):** `a ≤ 2(1 + U₀) ≤ E₀` for `p ≤ R` (`LadicCond.condAt_le_of_upper`), `a ≤ 2`
for tame `p`, `a = 0` if unramified. -/
theorem localBound_of_ram (hL8 : SwanIntegral) (hAd : AdaptedExists (p := p)) (u : ℚ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ) (r : GaloisRep ℓ 2) (h : LocalRam u p r) :
    LocalBound u p r := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨Lp, hL⟩ := hAd ℓ (Ne.symm hpℓ) 2 (r.restrictLocal p) (restrictLocal_continuous r)
  refine ⟨Lp, hL, fun hpR => ?_, fun hpR => ?_, fun hS hM => ?_⟩
  · have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
    have hb := condAt_le_of_upper hL8 ℓ hpℓ (r.restrictLocal p) (restrictLocal_continuous r) Lp
      hL U0 hU0 (h1 hpR)
    have : ((condAt Lp (r.restrictLocal p) : ℚ) : ℝ) ≤ ((ZInQ.heightE0 : ℚ) : ℝ) := by
      push_cast at hb ⊢
      linarith [two_one_add_U0_le]
    exact_mod_cast this
  · rw [condAt, swanAt_eq_zero_of_wild (h2 hpR), add_zero]
    exact_mod_cast codimInv_le (r.restrictLocal p) inertiaSet
  · exact condAt_eq_zero_of_unramified (h3 hS hM) Lp

/-- **G15's local bounds from `G15Ram` (GLUE, proved).** -/
theorem g15LocalBounds_of_ram (hL8 : SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h : G15Ram D u) : G15LocalBounds D u := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h5 => ?_, fun h5 => ?_⟩
  · exact localBound_of_ram hL8 (hAd p) u h5 D.r5 ((h p hp).1 h5)
  · exact localBound_of_ram hL8 (hAd p) u (by omega) D.r3 ((h p hp).2 h5)

end LocalRamSec

/-! ## §8. The range G13-G16 assembled -/

/-- **G16Out**: what G13-G16 deliver to `ModularConstituent`: a level `1 ≤ N ≤ Q_R M²` (with
`R = D`, `M = M_{S_mul}(u)`) such that `V₅(A)` and `V₅(J_{L'})` have a common constituent for
every `J₁(N)` `J` over `ℚ`. -/
def G16Out {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ) : Prop :=
  ∃ N : ℕ, 0 < N ∧
    (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
    ∀ J : AbVar ℚ, IsJ1 N J → CommonConstituent A (J.baseChange L)

/-- The literature leaves this range uses (all already in `Leaves.lean` / the kernel). -/
structure NewformLeaves : Prop where
  t24 : PkgI4.EigenformTwist
  t25 : PkgI4.NewformOfEigenform
  r14 : PkgI4.EigenformRepExists
  r16 : R16_EichlerShimuraJ1'
  r17 : LadicCond.CarayolR17'
  r9a : FaltingsSemisimple
  r9b : FaltingsTate
  m0 : TateModuleFree
  t18 : FrobeniusDense
  t19 : GlueC10.BrauerNesbittChar0

/-- **G13-G16 (GLUE, proved).** From G8-G12's output on data `D`, the two open AV-side Props
`G14TraceCompat D` and `G15LocalBounds D u` on the same data, the leaves, and the glue Prop
`SwanIndependent`: the level and the common constituent of `ModularConstituent`. -/
theorem g13_g16 (lv : NewformLeaves)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (D : ModData L A)
    (h12 : G12Spec D) (hc : G14TraceCompat D) (hloc : G15LocalBounds D u) : G16Out A u := by
  obtain ⟨N, χ, f, h13⟩ := g13 lv.t24 lv.t25 lv.r16 lv.r9a lv.r9b lv.m0 lv.t19 lv.t18 D h12
  have h14 := g14 lv.r14 lv.t19 lv.t18 D N χ f h13 hc
  have h15 := g15 lv.r17 hSw D N χ f h13 h14 u hloc
  exact ⟨N, h13.1, g16 N h13.1 u h15, h13.2.2.2.2.2⟩

/-- **G13-G16, reduced form (GLUE, proved).** As `g13_g16`, with G15's open part in the
ramification form `G15Ram` and the conductor arithmetic proved from the glue Props L8
(`SwanIntegral`) and `AdaptedExists` (both stated in the kernel's `LadicCond`). -/
theorem g13_g16_ram (lv : NewformLeaves)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (D : ModData L A)
    (h12 : G12Spec D) (hc : G14TraceCompat D) (hram : G15Ram D u) : G16Out A u :=
  g13_g16 lv hSw u D h12 hc (g15LocalBounds_of_ram hL8 hAd D u hram)

/-- With a `J₁(N)` from T33 (`JacobianExists`) and the glue target `X1ModelExists`: the `N`
of `G16Out` has a `J₁(N)`, as `ModularConstituent` asks. -/
theorem g16Out_with_J1 (hJac : JacobianExists ℚ) (hX : X1ModelExists)
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (h : G16Out A u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨N, hN, hle, hcc⟩ := h
  obtain ⟨J, hJ⟩ := exists_J1 hJac hX N hN
  exact ⟨N, J, hN, hJ, hle, hcc J hJ⟩

/-- **The G13-G16 conclusion in the shape of `ModularConstituent`'s last conjuncts** (kernel
objects): for a model `A/L'` with G8-G12's data `D` and the two open Props on `D`, there are a level
`N` with `0 < N ≤ Q_R M²`, a `J₁(N)` `J` over `ℚ` and a common constituent of `V_ℓ(A)` and
`V_ℓ(J_{L'})`. -/
theorem modularConstituent_tail (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15Ram D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, hram⟩ := h
  exact g16Out_with_J1 hJac hX u (g13_g16_ram lv hSw hL8 hAd u D h12 hc hram)

/-! ## §9. Bridge from g0-mod-galois's interface (draft at origin/wip/g0-mod-galois ad7f14c2)

The definitions `resQ`, `Vb`, `tate`, `Intertwines`, `G8Out` (here `GalG8Out`), `G12Out` (here
`GalG12Out`) are copied verbatim from
`scratch/g0-mod-galois/part_galois.lean` (namespace `G0Galois` there), over the kernel's objects. -/

section Bridge

/-- (copied from g0-mod-galois) The restriction map `G_K → G_ℚ`. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- (copied from g0-mod-galois) `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- (copied from g0-mod-galois) The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- (copied from g0-mod-galois) `e` intertwines `f g` with `r(g) ⊕ r(g)`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-- (copied from g0-mod-galois) **Output of G8.** -/
def GalG8Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ)) (r : GaloisRep ℓ 2) : Prop :=
  (∀ σ, ρ (resQ K σ) = tate A ℓ σ) ∧
  ∃ e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ),
    Intertwines ρ r.mat e ∧
    Algebra.adjoin (PadicAlgCl ℓ) (Set.range fun σ => r.mat (resQ K σ)) = ⊤

/-- (copied from g0-mod-galois) **Output of G12** at `ℓ = 5`: `ψ` of finite image. -/
def GalG12Out (r : GaloisRep 5 2) : Prop :=
  ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (S : Finset ℕ),
    0 < N ∧ PkgI4.IsNormalizedEigenform g χ ∧ (Set.range ψ.toHom).Finite ∧
    r.AttachedUpToTwist ψ ιC ιL g S

/-- **Kronecker–Weber at Frobenius (GLUE, unproved; from T17 `KroneckerWeber`).** A continuous
character `ψ : G_ℚ → ℚ̄_ℓ^×` of finite image is, at arithmetic Frobenius outside a finite set,
a Dirichlet character `ψD mod m` through `ιC`, `ιL`: `ψ` factors through
`Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/m)^×` (T17), arithmetic Frobenius at `p ∤ m` maps to `p`, and the values
(roots of unity) lie in `ιL(ℚ̄)`. -/
def DirichletOfFinite : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ψ : GaloisChar ℓ), (Set.range ψ.toHom).Finite →
    ∀ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
    ∃ (m : ℕ) (ψD : DirichletCharacter ℂ m) (S : Finset ℕ), 0 < m ∧
      ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
        ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
          (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-- **G12Out ⇒ PanOutput (GLUE, proved from `DirichletOfFinite`).** -/
theorem panOutput_of_G12Out (hDF : DirichletOfFinite) (r : GaloisRep 5 2) (h : GalG12Out r) :
    ∃ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl 5), PanOutput ιC ιL r := by
  obtain ⟨M, χ, g, ψ, ιC, ιL, S, hM, hg, hfin, hatt⟩ := h
  obtain ⟨m, ψD, S', hm, hψ⟩ := hDF 5 ψ hfin ιC ιL
  refine ⟨ιC, ιL, M, χ, g, m, ψD, ψ, S ∪ S', hM, hg, hm, fun p hp hpS => ?_,
    fun p hp hpS => hψ p hp (fun h => hpS (Finset.mem_union_right _ h))⟩
  exact hatt p hp (fun h => hpS (Finset.mem_union_left _ h))

/-- The embedding `ℚ̄ → K̄` underlying Mathlib's `Field.absoluteGaloisGroup.map`: it intertwines
`resQ K τ` with `τ`. -/
theorem resQ_spec (K : Type) [Field K] [NumberField K] :
    ∃ i : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x,
      i (resQ K τ x) = τ (i x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  refine ⟨g.toRingHom, fun τ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) τ)
    (AlgebraicClosure ℚ) x

/-- **G8Out ⇒ IsConstituentOf (GLUE, proved).** `U = ker(pr₂ ∘ e)` is the constituent. -/
theorem isConstituentOf_of_GalG8Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (r : GaloisRep ℓ 2) (h : GalG8Out A ℓ ρ r)
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K)
    (hi : ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x, i (resQ K τ x) = τ (i x)) :
    IsConstituentOf ℓ A i r := by
  obtain ⟨hres, e, he, -⟩ := h
  let W : Submodule (PadicAlgCl ℓ) (Vb A ℓ) :=
    LinearMap.ker ((LinearMap.snd (PadicAlgCl ℓ) _ _) ∘ₗ e.toLinearMap)
  have hW : ∀ v, v ∈ W ↔ (e v).2 = 0 := fun v => Iff.rfl
  have hstab : ∀ (σ : Field.absoluteGaloisGroup K) (w : Vb A ℓ), w ∈ W →
      GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σ w ∈ W := by
    intro σ w hw
    rw [hW] at hw ⊢
    have h1 := he (resQ K σ) w
    rw [hres σ] at h1
    change (e (tate A ℓ σ w)).2 = 0
    rw [h1, hw, Matrix.mulVec_zero]
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)) :=
    { toSubmodule := W
      apply_mem_toSubmodule := fun σ w hw => hstab σ w hw }
  let f : U.toSubmodule →ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) :=
    (LinearMap.fst (PadicAlgCl ℓ) _ _) ∘ₗ e.toLinearMap ∘ₗ W.subtype
  have hmemW : ∀ w : Fin 2 → PadicAlgCl ℓ, e.symm (w, 0) ∈ W := fun w => by
    rw [hW, LinearEquiv.apply_symm_apply]
  let eU : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) :=
    { f with
      invFun := fun w => ⟨e.symm (w, 0), hmemW w⟩
      left_inv := fun u => by
        apply Subtype.ext
        change e.symm ((e u).1, 0) = u
        have hu : (e u).2 = 0 := (hW u).mp u.2
        rw [← hu, Prod.mk.eta, LinearEquiv.symm_apply_apply]
      right_inv := fun w => by
        change (e (e.symm (w, 0))).1 = w
        rw [LinearEquiv.apply_symm_apply] }
  have hσ : ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (σ : GQ), (∀ x, i (σ x) = τ (i x)) →
      σ = resQ K τ := by
    intro τ σ hστ
    ext x
    apply i.toRingHom.injective
    change i (σ x) = i (resQ K τ x)
    rw [hστ, hi]
  refine ⟨U, eU, ?_, fun τ σ hστ u => ?_⟩
  · intro hbot
    have hmem : e.symm ((Pi.single 0 1 : Fin 2 → PadicAlgCl ℓ), 0) ∈ U.toSubmodule := hmemW _
    rw [hbot] at hmem
    have h0 : e.symm ((Pi.single 0 1 : Fin 2 → PadicAlgCl ℓ), 0) = 0 := hmem
    have h1 := congrArg (fun v => (e v).1 0) h0
    simp at h1
  · rw [hσ τ σ hστ]
    change (e (tate A ℓ τ u)).1 = toRep r (resQ K τ) ((e u).1)
    have h1 := he (resQ K τ) u
    rw [hres τ] at h1
    rw [h1, toRep_apply, Matrix.toLin'_apply]

/-- **G12Spec from g0-mod-galois's outputs (GLUE, proved from `DirichletOfFinite`).** Their
`G8Out` at `ℓ = 5` and `ℓ = 3` and `G12Out r₅` give `i`, `ιC`, `ι₅` such that the data
`⟨i, ιC, ι₅, ι₃, r₅, r₃⟩` satisfy `G12Spec` for **every** `ι₃` (`G12Spec` does not involve `ι₃`).
So `ι₃` can be chosen afterwards, compatibly with `ι₅`, as `G14TraceCompat` requires. -/
theorem g12Spec_of_galois (hDF : DirichletOfFinite) {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (ρ5 : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (ρ3 : PkgI4.GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2)
    (r3 : GaloisRep 3 2) (h5 : GalG8Out A 5 ρ5 r5) (h3 : GalG8Out A 3 ρ3 r3)
    (h12 : GalG12Out r5) :
    ∃ (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K) (ιC : Qbar →ₐ[ℚ] ℂ)
      (ι5 : Qbar →ₐ[ℚ] PadicAlgCl 5),
      ∀ ι3 : Qbar →ₐ[ℚ] PadicAlgCl 3, G12Spec (⟨i, ιC, ι5, ι3, r5, r3⟩ : ModData K A) := by
  obtain ⟨i0, hi0⟩ := resQ_spec K
  let i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := i0.toRatAlgHom
  have hi : ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x, i (resQ K τ x) = τ (i x) := hi0
  obtain ⟨ιC, ιL, hpan⟩ := panOutput_of_G12Out hDF r5 h12
  have hirr : ∀ {ℓ : ℕ} [Fact ℓ.Prime] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
      (r : GaloisRep ℓ 2), GalG8Out A ℓ ρ r → r.IsIrreducible := by
    intro ℓ _ ρ r h
    obtain ⟨-, -, -, hadj⟩ := h
    rw [PkgI4.GaloisRep.IsIrreducible, eq_top_iff, ← hadj]
    exact Algebra.adjoin_mono (Set.range_subset_iff.mpr fun σ => ⟨resQ K σ, rfl⟩)
  exact ⟨i, ιC, ιL, fun ι3 => ⟨hirr ρ5 r5 h5, hirr ρ3 r3 h3,
    isConstituentOf_of_GalG8Out A 5 ρ5 r5 h5 i hi, isConstituentOf_of_GalG8Out A 3 ρ3 r3 h3 i hi,
    hpan⟩⟩

end Bridge

/-! ## §10. Local unramifiedness from G11's global form (proved) -/

section LocalGlobal

open PkgI4 (GQp)
open scoped Pointwise

variable (p : ℕ) [Fact p.Prime]

/-- The embedding `ℚ̄ → ℚ̄_p` underlying `PkgI4.decomp p` (Mathlib's
`Field.absoluteGaloisGroup.map`): it intertwines `decomp p σ` with `σ`. -/
theorem decomp_spec : ∃ j : Qbar →+* PadicAlgCl p,
    ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x, j (PkgI4.decomp p σ x) = σ (j x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p] := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) := g.toAlgebra
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ)
    (AlgebraicClosure ℚ) x

/-- The valuation subring `{x ∈ ℚ̄ : ‖j x‖ ≤ 1}` of the place of `ℚ̄` above `p` given by `j`. -/
def vj (j : Qbar →+* PadicAlgCl p) : ValuationSubring Qbar :=
  (PadicAlgCl.valued p).v.valuationSubring.comap j

theorem mem_vj (j : Qbar →+* PadicAlgCl p) (x : Qbar) : x ∈ vj p j ↔ ‖j x‖ ≤ 1 := by
  rw [vj, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
  change ‖j x‖₊ ≤ 1 ↔ _
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

/-- `G_{ℚ_p}` acts isometrically on `ℚ̄_p` (spectral norm). -/
theorem norm_aut (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : PadicAlgCl p) :
    ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ y).symm

theorem mem_nonunits_vj (j : Qbar →+* PadicAlgCl p) (b : Qbar) (hb : ‖j b‖ < 1) :
    b ∈ (vj p j).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases h0 : b = 0
  · exact Or.inl h0
  · refine Or.inr fun hinv => ?_
    rw [mem_vj, map_inv₀, norm_inv] at hinv
    have hpos : 0 < ‖j b‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr h0)
    rw [inv_le_one₀ hpos] at hinv
    linarith

theorem liesOver_vj (j : Qbar →+* PadicAlgCl p) : LiesOver (vj p j) p := by
  apply mem_nonunits_vj
  rw [map_natCast, LadicCond.norm_p_kbar]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- **Global unramified ⇒ local inertia acts trivially (GLUE, proved).** If `r` is unramified at
`p` in PkgI4's global sense (every inertia group of `G_ℚ` at a place above `p` acts trivially),
then `r|G_{ℚ_p}` is trivial on the local inertia set `LadicCond.inertiaSet`. -/
theorem localUnram_of_unramifiedAt {ℓ n : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ n)
    (hr : r.UnramifiedAt p) : ∀ σ ∈ LadicCond.inertiaSet, r.restrictLocal p σ = 1 := by
  obtain ⟨j, hj⟩ := decomp_spec p
  intro σ hσ
  set τ := PkgI4.decomp p σ with hτ
  have hdec : τ ∈ (vj p j).decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_vj, mem_vj, AlgEquiv.smul_def,
      hτ, ← map_inv, hj, norm_aut]
  have hin : (⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) ∈
      (vj p j).inertiaSubgroup ℚ := by
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    ext y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    change (⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) • IsLocalRing.residue _ a =
      IsLocalRing.residue _ a
    rw [← IsLocalRing.ResidueField.residue_smul]
    apply Ideal.Quotient.eq.mpr
    have hb : ((⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) • a - a : vj p j) =
        ⟨τ a - a, by
          have := ((⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) • a - a).2
          exact this⟩ := rfl
    have hnorm : ‖j (τ (a : Qbar) - a)‖ < 1 := by
      rw [map_sub, hτ, hj]
      exact hσ (j a) ((mem_vj p j a).mp a.2)
    obtain ⟨hmem, hmax⟩ :=
      (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp
        (mem_nonunits_vj p j _ hnorm)
    rw [hb]
    exact hmax
  exact hr (vj p j) (liesOver_vj p j) ⟨τ, hdec⟩ hin

end LocalGlobal

/-- `LocalRam` with clause (iii) in G11's global form (`G0Galois.G11Out`: `r.UnramifiedAt p`). -/
def LocalRamG (u : ℚ) (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) :
    Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, r.restrictLocal p σ = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ LadicCond.wildSet, r.restrictLocal p σ = 1) ∧
    (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → r.UnramifiedAt p)

/-- **Open part of G15, final form.** Clauses (i)-(ii) of `LocalRam` (D1-D4 on G8's `r_ℓ`) and
clause (iii) as G11's output (proved by g0-mod-galois as `g11`, `G0Galois.G11Out`). -/
def G15RamG {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ) :
    Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalRamG u p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalRamG u p ⟨hp⟩ 3 _ D.r3)

theorem g15Ram_of_G {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h : G15RamG D u) : G15Ram D u := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h5 => ?_, fun h5 => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (h p hp).1 h5
    exact ⟨h1, h2, fun hS hM => localUnram_of_unramifiedAt p D.r5 (h3 hS hM)⟩
  · obtain ⟨h1, h2, h3⟩ := (h p hp).2 h5
    exact ⟨h1, h2, fun hS hM => localUnram_of_unramifiedAt p D.r3 (h3 hS hM)⟩

/-- **G13-G16, final form (GLUE, proved).** As `modularConstituent_tail`, with G15's open part
`G15RamG` (D1-D4's ramification statements on G8's `r_ℓ`, and G11's output). -/
theorem modularConstituent_tail_G (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, hram⟩ := h
  exact modularConstituent_tail lv hJac hX hSw hL8 hAd A u ⟨D, h12, hc, g15Ram_of_G D u hram⟩

end G0ModNewform

end

#print axioms G0ModNewform.equivariant_of_asModule
#print axioms G0ModNewform.condAt_eq_of_intertwine
#print axioms G0ModNewform.newform_of_pan
#print axioms G0ModNewform.commonConstituent_of_attached
#print axioms G0ModNewform.g13
#print axioms G0ModNewform.iso_R14
#print axioms G0ModNewform.g14
#print axioms G0ModNewform.g15
#print axioms G0ModNewform.g16
#print axioms G0ModNewform.g13_g16
#print axioms G0ModNewform.g16Out_with_J1
#print axioms G0ModNewform.localBound_of_ram
#print axioms G0ModNewform.g13_g16_ram
#print axioms G0ModNewform.modularConstituent_tail
#print axioms G0ModNewform.isConstituentOf_of_GalG8Out
#print axioms G0ModNewform.g12Spec_of_galois
#print axioms G0ModNewform.localUnram_of_unramifiedAt
#print axioms G0ModNewform.g15Ram_of_G
#print axioms G0ModNewform.modularConstituent_tail_G

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- **Output of G11:** `r` is unramified at every prime outside `T ∪ {ℓ}`. -/
def G11Out {ℓ : ℕ} [Fact ℓ.Prime] (T : Finset ℕ) (r : GaloisRep ℓ 2) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → p ≠ ℓ → r.UnramifiedAt p

end G0Galois

/-! ## §1. The smaller named Props -/

namespace G15Ram

open PkgI4 (GQp GaloisRep)
open LadicCond G0ModNewform

section Local

variable (p : ℕ) [Fact p.Prime]

/-- **Glue: T20 + T21 transported to `ℚ̄_p`** (Hilbert's formula for the different, Serre,
*Corps locaux* IV §1 Prop. 4, and Serre's bound `v_F(𝔇) ≤ e − 1 + v_F(e)`, III §6 remark after
Prop. 13; UNVERIFIED numbering). For a finite Galois `F ⊆ ℚ̄_p` with lower ramification groups
`G_i = ramSet F i` (pulled back to `G_{ℚ_p}`) and `g_i = ramCard F i`, some `G_n` is trivial and
`∑_{i<n}(g_i − 1) ≤ e − 1 + e·v_p(e)` with `e = g_0`. Both parts are proved by t-different over
complete DVRs (`PkgI6.hilbertDifferentFormula`, `PkgI6.differentBound`). This Prop is derived
below from them and the transport `LadicDVRModel` (`hilbertSerre_of_model`). The existence of
`n` alone is already proved (`LadicCond.eventuallyTrivial`). -/
def HilbertSerreLadic : Prop :=
  ∀ F : Fld p, IsFinGal F → ∃ n : ℕ, ramSet F n ⊆ fixSet F ∧
    ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0)

/-- **Glue (D1 at the level of `upperAbs`; N5 L796-812, L824-827).** For a finite Galois
`F ⊆ ℚ̄_p` with ramification index `e(F/ℚ_p) ≤ a!`, every absolute upper ramification group
`G_{ℚ_p}^t` with `t > 4a²` fixes `F`. Proved below from `HilbertSerreLadic`
(`upperBreakFix_of_hilbertSerre`). -/
def UpperBreakFix : Prop :=
  ∀ F : Fld p, IsFinGal F → ∀ a : ℕ, 1 ≤ a → ramCard F 0 ≤ a.factorial →
    ∀ t : ℝ, 4 * (a : ℝ) ^ 2 < t → upperAbs p t ⊆ fixSet F

/-- **Glue (Serre, *Corps locaux* IV §3: `G^t ⊆ G^0`'s wild part for `t > 0`; UNVERIFIED
numbering).** For `t > 0` every element of `G_{ℚ_p}^t` lies in wild inertia: `|σx − x| < |x|`
for all `x ≠ 0`. (Proof: take `F` = the Galois closure of `ℚ_p(x)`; `σ|_F ∈ G^t(F) = G_{ψ(t)}(F)`
with `ψ(t) > 0`, so `σ|_F ∈ G_1(F)`, and `σx/x ≡ 1 mod 𝔪_F` because `|F^×| = |ϖ|^ℤ`.)
Proved below (`upperWild`). -/
def UpperWild : Prop :=
  ∀ t : ℝ, 0 < t → upperAbs p t ⊆ wildSet

/-- **Glue (tame extensions; Serre, *Corps locaux* IV §2, Cor. 1-4 of Prop. 7: `G_1` is the
`p`-Sylow subgroup of `G_0`; UNVERIFIED numbering).** If `F ⊆ ℚ̄_p` is finite Galois and `p` does
not divide `e(F/ℚ_p)`, wild inertia fixes `F`. Proved below (`wildFixTame`). -/
def WildFixTame : Prop :=
  ∀ F : Fld p, IsFinGal F → ¬ p ∣ ramCard F 0 → wildSet ⊆ fixSet F

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Glue on G8's construction (G8 + G3 + R6 + D2; N5 L719-727, L819-823).** On `G_F ∩ P_p`
the representation `r` is the scalar `β(σ)` (`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ` with `a_σ μ_σ = 1`
on `G_L ⊇ G_F`, and the Tate action of `A` trivial on `P_p ∩ G_F`: by Raynaud's criterion (R6)
`A` is semistable over `F ⊇ L_v(A[3])` (`A[5]` if `p = 3`), and then wild inertia acts trivially
(D2, `PkgI2.D2_fixed_of_raynaud`); at `p > D` by good reduction (G3) and
Néron–Ogg–Shafarevich). Here `β` is the local twist (the inverse of Glazer's `β`). -/
def TwistShape (r : GaloisRep ℓ 2) (F : Fld p) (β : GQp p → PadicAlgCl ℓ) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet,
    ((r.restrictLocal p σ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
      Matrix.scalar (Fin 2) (β σ)

/-- **Glue on G7's `β` (D3 + T16; N5 L823-844).** The local twist is trivial on
`G_{ℚ_p}^t ∩ G_F` for `t > U`: at odd `p`, `β|_{G_F}` is trivial on wild inertia (its square is
the tame `χ`, and a pro-`p` group has no quotient of order two;
`GlueConductor.char_trivial_of_odd_pgroup`);
at `p = 2`, local reciprocity with the upper numbering theorem (T16) and `(U_F^{e+1})⁴ = U_F^{3e+1}`
(D3, `GlueConductor.fourth_pow_mem`) bound the relative upper break of `β` by `3e`, and
`ψ_{F/ℚ_2}(u) ≥ u` moves it to the absolute numbering; `max(4D², 3e) ≤ U₀`
(`GlueConductor.max_le_U0`). -/
def TwistUpper (F : Fld p) (β : GQp p → PadicAlgCl ℓ) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, β σ = 1

/-- **Glue on G7's `β` at tame primes (N5 L848-851).** `β` is trivial on `P_p ∩ G_F` (for odd
`p`: `β²` is tame, `GlueConductor.char_trivial_of_odd_pgroup`). -/
def TwistTame (F : Fld p) (β : GQp p → PadicAlgCl ℓ) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β σ = 1

/-- **G8-G7 local data at `p ≤ D`** (N5 L819-844): `F` the Galois closure of `L_v(A[3])`
(`A[5]` if `p = 3`), of degree `≤ (DG₀)!`, so `e(F/ℚ_p) ≤ (DG₀)!`; the local twist `β`. -/
def SmallPrimeData (r : GaloisRep ℓ 2) : Prop :=
  ∃ (F : Fld p) (β : GQp p → PadicAlgCl ℓ), IsFinGal F ∧
    ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
    TwistShape p r F β ∧ TwistUpper p F β U0

/-- **G8-G7 local data at `p > D`** (N5 L848-851): `F` the Galois closure of `L_v`, tame since
`[L_v:ℚ_p] ≤ D < p` (the Galois closure of a tame extension is tame); the local twist `β`. -/
def LargePrimeData (r : GaloisRep ℓ 2) : Prop :=
  ∃ (F : Fld p) (β : GQp p → PadicAlgCl ℓ), IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
    TwistShape p r F β ∧ TwistTame p F β

/-- The local data at `p` for `r`, by the size of `p`. -/
def LocalData (r : GaloisRep ℓ 2) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → SmallPrimeData p r) ∧
    ((ZInQ.heightD : ℝ) < p → LargePrimeData p r)

end Local

/-! ## §2. Local field: the break bound at the level of `upperAbs` (proved) -/

section Break

variable {p : ℕ} [Fact p.Prime] {F : Fld p}

theorem ramSet_anti {i j : ℕ} (h : i ≤ j) : ramSet F j ⊆ ramSet F i := by
  rintro σ ⟨ϖ, hϖ, hσ⟩
  refine ⟨ϖ, hϖ, fun x hx hx1 => (hσ x hx hx1).trans ?_⟩
  exact pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega)

theorem card_image_mono (hF : IsFinGal F) {S T : Set (GQp p)} (h : S ⊆ T) :
    Nat.card (restr F '' S) ≤ Nat.card (restr F '' T) :=
  Nat.card_mono (finite_restr hF T) (Set.image_mono h)

theorem ramCard_anti (hF : IsFinGal F) : Antitone (ramCard F) := fun _ _ h =>
  card_image_mono hF (ramSet_anti h)

theorem one_le_ramCard (hF : IsFinGal F) (i : ℕ) : 1 ≤ ramCard F i := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  exact Nat.one_le_iff_ne_zero.mpr (ramCard_ne_zero hF hϖ i)

/-- If `g_i ≤ 1`, then `G_i` (pulled back) fixes `F`. -/
theorem fix_of_ramCard_le_one (hF : IsFinGal F) {i : ℕ} (h : ramCard F i ≤ 1) :
    ramSet F i ⊆ fixSet F := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  have hfin : Finite (restr F '' ramSet F i) := (finite_restr hF (ramSet F i)).to_subtype
  have hsub : Subsingleton (restr F '' ramSet F i) := Finite.card_le_one_iff_subsingleton.mp h
  have h1 : (1 : GQp p) ∈ ramSet F i := fixSet_subset_ramSet hϖ i (fun x _ => rfl)
  intro σ hσ x hx
  have he : (⟨restr F σ, σ, hσ, rfl⟩ : restr F '' ramSet F i) = ⟨restr F 1, 1, h1, rfl⟩ :=
    Subsingleton.elim _ _
  have := congrFun (congrArg Subtype.val he) ⟨x, hx⟩
  exact this

theorem ramCardR_of_gt {t : ℝ} (ht : -1 < t) : ramCardR F t = ramCard F ⌈t⌉.toNat := by
  unfold ramCardR ramSetR
  rw [if_neg (not_le.mpr ht)]
  rfl

theorem ramCardR_anti (hF : IsFinGal F) : Antitone (ramCardR F) := by
  intro s t hst
  unfold ramCardR ramSetR
  by_cases ht : t ≤ -1
  · have hs : s ≤ -1 := hst.trans ht
    rw [if_pos ht, if_pos hs]
  · rw [if_neg ht]
    by_cases hs : s ≤ -1
    · rw [if_pos hs]
      exact card_image_mono hF (Set.subset_univ _)
    · rw [if_neg hs]
      exact card_image_mono hF (ramSet_anti (Int.toNat_le_toNat (Int.ceil_mono hst)))

/-- The integrand of Herbrand's `φ` (`phiAt`). -/
def gInt (F : Fld p) (t : ℝ) : ℝ := (ramCardR F t : ℝ) / (ramCard F 0 : ℝ)

theorem phiAt_eq (u : ℝ) : phiAt F u = ∫ t in (0 : ℝ)..u, gInt F t := rfl

theorem gInt_anti (hF : IsFinGal F) : Antitone (gInt F) := fun _ _ h =>
  div_le_div_of_nonneg_right (by exact_mod_cast ramCardR_anti hF h) (Nat.cast_nonneg _)

theorem gInt_int (hF : IsFinGal F) (a b : ℝ) :
    IntervalIntegrable (gInt F) MeasureTheory.volume a b :=
  (gInt_anti hF).intervalIntegrable

theorem g0_pos (hF : IsFinGal F) : (0 : ℝ) < ramCard F 0 := by
  exact_mod_cast one_le_ramCard hF 0

theorem gInt_le_one (hF : IsFinGal F) {t : ℝ} (ht : -1 < t) : gInt F t ≤ 1 := by
  rw [gInt, div_le_one (g0_pos hF), ramCardR_of_gt ht]
  exact_mod_cast ramCard_anti hF (Nat.zero_le _)

theorem gInt_ge (hF : IsFinGal F) (t : ℝ) : 1 / (ramCard F 0 : ℝ) ≤ gInt F t := by
  have h1 : 1 ≤ ramCardR F t := by
    have h0 : -1 < max t 0 := lt_of_lt_of_le (by norm_num) (le_max_right t 0)
    have := ramCardR_anti hF (le_max_left t 0)
    rw [ramCardR_of_gt h0] at this
    exact (one_le_ramCard hF _).trans this
  exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (Nat.cast_nonneg _)

theorem gInt_nonneg (hF : IsFinGal F) (t : ℝ) : 0 ≤ gInt F t :=
  le_trans (by have := g0_pos hF; positivity) (gInt_ge hF t)

theorem phi_mono (hF : IsFinGal F) {u w : ℝ} (h : u ≤ w) : phiAt F u ≤ phiAt F w := by
  have h1 := intervalIntegral.integral_interval_sub_left (gInt_int hF 0 w) (gInt_int hF 0 u)
  have h2 : 0 ≤ ∫ t in u..w, gInt F t :=
    intervalIntegral.integral_nonneg h (fun x _ => gInt_nonneg hF x)
  rw [phiAt_eq, phiAt_eq]
  linarith

theorem phi_sub_le (hF : IsFinGal F) {w u : ℝ} (hw : 0 ≤ w) (hwu : w ≤ u) :
    phiAt F u - phiAt F w ≤ u - w := by
  rw [phiAt_eq, phiAt_eq,
    intervalIntegral.integral_interval_sub_left (gInt_int hF _ _) (gInt_int hF _ _)]
  calc ∫ t in w..u, gInt F t ≤ ∫ _ in w..u, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hwu (gInt_int hF _ _) intervalIntegrable_const
          (fun x hx => gInt_le_one hF (by linarith [hx.1]))
    _ = u - w := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]

theorem phi_ge (hF : IsFinGal F) {u : ℝ} (hu : 0 ≤ u) :
    u * (1 / (ramCard F 0 : ℝ)) ≤ phiAt F u := by
  rw [phiAt_eq]
  calc u * (1 / (ramCard F 0 : ℝ)) = ∫ _ in (0 : ℝ)..u, (1 / (ramCard F 0 : ℝ)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    _ ≤ ∫ t in (0 : ℝ)..u, gInt F t :=
        intervalIntegral.integral_mono_on hu intervalIntegrable_const (gInt_int hF _ _)
          (fun x _ => gInt_ge hF x)

theorem phi_nat (hF : IsFinGal F) (m : ℕ) :
    phiAt F m = ∑ k ∈ Finset.range m, (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
  rw [phiAt_eq]
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := gInt F) (a := fun k : ℕ => (k : ℝ)) (n := m) (fun k _ => gInt_int hF _ _)
  simp only [Nat.cast_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have : ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), gInt F x =
      ∫ _ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le hk] at hx
    have hx1 := hx.1
    have hx2 := hx.2
    push_cast at hx2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hxm : -1 < x := by linarith
    have hc : ⌈x⌉ = ((k + 1 : ℕ) : ℤ) := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor <;> linarith
    simp only [gInt]
    rw [ramCardR_of_gt hxm, hc, Int.toNat_natCast]
  rw [this, intervalIntegral.integral_const, smul_eq_mul]
  push_cast
  ring

theorem phi_eq_sum (g : ℕ → ℕ) (m : ℕ) :
    GlueConductor.phi g m = ∑ k ∈ Finset.range m, (g (k + 1) : ℚ) / g 0 := by
  induction m with
  | zero => rw [GlueConductor.phi_zero, Finset.sum_range_zero]
  | succ m ih => rw [GlueConductor.phi_succ, ih, Finset.sum_range_succ]

/-- **D1 at the level of `upperAbs` (GLUE, proved from `HilbertSerreLadic`).** -/
theorem upperBreakFix_of_hilbertSerre (h : HilbertSerreLadic p) : UpperBreakFix p := by
  classical
  intro F hF a ha hea t ht σ hσ
  have hex : ∃ n, ramSet F n ⊆ fixSet F ∧ ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0) := h F hF
  have hex' : ∃ n, ramSet F n ⊆ fixSet F := let ⟨n, hn, _⟩ := hex; ⟨n, hn⟩
  set n := Nat.find hex' with hn_def
  have hnfix : ramSet F n ⊆ fixSet F := Nat.find_spec hex'
  obtain ⟨N, hN, hsum⟩ := hex
  have hnN : n ≤ N := Nat.find_min' hex' hN
  have hsum' : ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0) :=
    (Finset.sum_le_sum_of_subset (Finset.range_mono hnN)).trans hsum
  set w : ℕ := n - 1 with hw
  have ha2 : (0 : ℝ) ≤ 4 * (a : ℝ) ^ 2 := by positivity
  have hφw : phiAt F w < t := by
    have h4 : phiAt F w ≤ 4 * (a : ℝ) ^ 2 := by
      by_cases hn1 : n ≤ 1
      · have hw0 : w = 0 := by omega
        rw [hw0, Nat.cast_zero, phiAt_eq, intervalIntegral.integral_same]
        exact ha2
      · have hb : ¬ ramSet F w ⊆ fixSet F := Nat.find_min hex' (by omega)
        have hgb : 2 ≤ ramCard F w := by
          by_contra hlt
          exact hb (fix_of_ramCard_le_one hF (by omega))
        have hub := GlueConductor.upper_break_le p a (Fact.out) ha (ramCard F)
          (ramCard_anti hF) (one_le_ramCard hF) w n hgb (by omega) hea hsum'
        rw [phi_nat hF]
        have hcast : ((GlueConductor.phi (ramCard F) w : ℚ) : ℝ) =
            ∑ k ∈ Finset.range w, (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
          rw [phi_eq_sum]
          push_cast
          rfl
        rw [← hcast]
        exact_mod_cast hub
    linarith
  set S := {u : ℝ | -1 ≤ u ∧ t ≤ phiAt F u} with hS
  have ht0 : 0 < t := by linarith
  have hg0 := g0_pos hF
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hne : S.Nonempty := by
    refine ⟨w + t * ramCard F 0, by nlinarith, ?_⟩
    have h1 := phi_ge hF (u := w + t * ramCard F 0) (by positivity)
    have h2 : t ≤ (w + t * ramCard F 0) * (1 / (ramCard F 0 : ℝ)) := by
      rw [add_mul, mul_one_div, mul_one_div, mul_div_assoc, div_self hg0.ne', mul_one]
      have : (0 : ℝ) ≤ w / ramCard F 0 := div_nonneg hw0 hg0.le
      linarith
    exact h2.trans h1
  have hlb : ∀ u ∈ S, (w : ℝ) + (t - phiAt F w) ≤ u := by
    rintro u ⟨-, hu⟩
    by_cases huw : u ≤ w
    · exact absurd (hu.trans (phi_mono hF huw)) (not_le.mpr hφw)
    · have := phi_sub_le hF hw0 (le_of_not_ge huw)
      linarith
  have hψ : (w : ℝ) < sInf S := lt_of_lt_of_le (by linarith) (le_csInf hne hlb)
  have hσF : σ ∈ ramSetR F (sInf S) := hσ F hF
  unfold ramSetR at hσF
  rw [if_neg (by linarith)] at hσF
  apply hnfix
  refine ramSet_anti ?_ hσF
  have hz : ((w : ℕ) : ℤ) < ⌈sInf S⌉ := Int.lt_ceil.mpr (by exact_mod_cast hψ)
  omega

end Break

/-! ## §2b. Positive upper groups are wild (proved) -/

section Wild

variable {p : ℕ} [Fact p.Prime]

/-- `G_{ℚ_p}` acts isometrically on `ℚ̄_p` (copied from g0-mod-newform's `norm_aut`). -/
theorem norm_aut' (σ : GQp p) (y : Kbar p) : ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ y).symm

/-- For `t > 0`, `G^t(F) ⊆ G_1(F)` (pulled back): `ψ_F(t) > 0`. -/
theorem ramSet_one_of_upperSet {F : Fld p} (hF : IsFinGal F) {t : ℝ} (ht : 0 < t) {σ : GQp p}
    (hσ : σ ∈ upperSet F t) : σ ∈ ramSet F 1 := by
  set S := {u : ℝ | -1 ≤ u ∧ t ≤ phiAt F u} with hS
  have hg0 := g0_pos hF
  have hφ0 : phiAt F 0 = 0 := by rw [phiAt_eq, intervalIntegral.integral_same]
  have hne : S.Nonempty := by
    refine ⟨t * ramCard F 0, by nlinarith, ?_⟩
    have h1 := phi_ge hF (u := t * ramCard F 0) (by positivity)
    have h2 : t * ramCard F 0 * (1 / (ramCard F 0 : ℝ)) = t := by field_simp
    linarith
  have hlb : ∀ u ∈ S, t ≤ u := by
    rintro u ⟨-, hu⟩
    by_cases hu0 : u ≤ 0
    · have := phi_mono hF hu0
      linarith
    · have := phi_sub_le hF le_rfl (le_of_not_ge hu0)
      linarith
  have hψ : t ≤ sInf S := le_csInf hne hlb
  have hσF : σ ∈ ramSetR F (sInf S) := hσ
  unfold ramSetR at hσF
  rw [if_neg (by linarith)] at hσF
  refine ramSet_anti ?_ hσF
  have hz : (0 : ℤ) < ⌈sInf S⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
  omega

/-- The predicate "`σ x / x ≡ 1`": `‖σ x − x‖ < ‖x‖`. -/
def WildAt (σ : GQp p) (y : Kbar p) : Prop := ‖σ y - y‖ < ‖y‖

theorem wildAt_mul {σ : GQp p} {y z : Kbar p} (hy : WildAt σ y) (hz : WildAt σ z) :
    WildAt σ (y * z) := by
  unfold WildAt at *
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt (norm_nonneg _) hy
  have hz0 : 0 < ‖z‖ := lt_of_le_of_lt (norm_nonneg _) hz
  have he : σ (y * z) - y * z = σ y * (σ z - z) + (σ y - y) * z := by rw [map_mul]; ring
  rw [he, norm_mul y z]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_aut']
    exact mul_lt_mul_of_pos_left hz hy0
  · rw [norm_mul]
    exact mul_lt_mul_of_pos_right hy hz0

theorem wildAt_inv {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) : WildAt σ y⁻¹ := by
  unfold WildAt at *
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt (norm_nonneg _) hy
  have hy0' : y ≠ 0 := norm_pos_iff.mp hy0
  have hσy : σ y ≠ 0 := (map_ne_zero σ).mpr hy0'
  have he : σ y⁻¹ - y⁻¹ = (y - σ y) / (σ y * y) := by
    rw [map_inv₀]; field_simp
  rw [he, norm_div, norm_mul, norm_aut', norm_sub_rev, norm_inv,
    div_lt_iff₀ (by positivity)]
  calc ‖σ y - y‖ < ‖y‖ := hy
    _ = ‖y‖⁻¹ * (‖y‖ * ‖y‖) := by field_simp

theorem wildAt_one (σ : GQp p) : WildAt σ 1 := by
  unfold WildAt; simp

theorem wildAt_pow {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) (n : ℕ) : WildAt σ (y ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact wildAt_one σ
  | succ n ih => rw [pow_succ]; exact wildAt_mul ih hy

theorem wildAt_zpow {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) (k : ℤ) : WildAt σ (y ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact wildAt_pow hy n
  · rw [zpow_neg, zpow_natCast]; exact wildAt_inv (wildAt_pow hy n)

theorem natCast_mem (F : Fld p) : (p : Kbar p) ∈ F := by
  rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
  exact IntermediateField.algebraMap_mem _ _

/-- An element of `G_1(F)` (pulled back) satisfies `σx/x ≡ 1` for every `x ∈ F^×`. -/
theorem wild_of_ramSet_one {F : Fld p} {σ : GQp p} (hσ : σ ∈ ramSet F 1) {x : Kbar p}
    (hx : x ∈ F) (hx0 : x ≠ 0) : ‖σ x - x‖ < ‖x‖ := by
  obtain ⟨ϖ, hϖ, h1⟩ := hσ
  have hϖ1 : ‖ϖ‖ < 1 := hϖ.2.1
  have hϖpos : 0 < ‖ϖ‖ := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hpn : ‖(p : Kbar p)‖ < 1 := by rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
    have hp := hϖ.2.2 _ (natCast_mem F) hpn
    exact lt_of_lt_of_le (by rw [norm_p_kbar]; positivity) hp
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.mp hϖpos
  -- `ϖ` and the units of `F` satisfy `WildAt`
  have hwϖ : WildAt σ ϖ := by
    unfold WildAt
    have := h1 ϖ hϖ.1 hϖ1.le
    calc ‖σ ϖ - ϖ‖ ≤ ‖ϖ‖ ^ (1 + 1) := this
      _ < ‖ϖ‖ := by rw [pow_two]; exact mul_lt_of_lt_one_right hϖpos hϖ1
  have hwu : ∀ z ∈ F, ‖z‖ = 1 → WildAt σ z := by
    intro z hz hz1
    unfold WildAt
    rw [hz1]
    calc ‖σ z - z‖ ≤ ‖ϖ‖ ^ (1 + 1) := h1 z hz hz1.le
      _ < 1 := pow_lt_one₀ (norm_nonneg _) hϖ1 (by norm_num)
  -- discreteness: `x = ϖ^k z` with `‖z‖ = 1`
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hxpos ((one_lt_inv₀ hϖpos).mpr hϖ1)
  set k : ℤ := -(n + 1) with hk
  set z := x * (ϖ ^ k)⁻¹ with hz
  have hzF : z ∈ F := mul_mem hx (inv_mem (zpow_mem hϖ.1 k))
  have hnk : ‖ϖ ^ k‖ = ‖ϖ‖⁻¹ ^ (n + 1) := by
    rw [norm_zpow, hk, zpow_neg, inv_zpow]
  have hnk' : ‖ϖ‖⁻¹ ^ n = ‖ϖ ^ k‖ * ‖ϖ‖ := by
    rw [hnk, zpow_add₀ (inv_ne_zero hϖpos.ne'), zpow_one, mul_assoc,
      inv_mul_cancel₀ hϖpos.ne', mul_one]
  have hpk : 0 < ‖ϖ ^ k‖ := by rw [hnk]; positivity
  have hz_le : ‖z‖ ≤ 1 := by
    rw [hz, norm_mul, norm_inv, ← div_eq_mul_inv, div_le_one hpk, hnk]
    exact hn2
  have hz_gt : ‖ϖ‖ < ‖z‖ := by
    rw [hz, norm_mul, norm_inv, ← div_eq_mul_inv, lt_div_iff₀ hpk]
    rw [hnk'] at hn1
    linarith [mul_comm ‖ϖ ^ k‖ ‖ϖ‖]
  have hz1 : ‖z‖ = 1 := by
    by_contra hne
    exact absurd (hϖ.2.2 z hzF (lt_of_le_of_ne hz_le hne)) (not_le.mpr hz_gt)
  have hxz : x = ϖ ^ k * z := by
    rw [hz, mul_comm x, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero k hϖ0), one_mul]
  have := wildAt_mul (wildAt_zpow hwϖ k) (hwu z hzF hz1)
  rw [← hxz] at this
  exact this

instance isGalois_Kbar : IsGalois ℚ_[p] (Kbar p) := ⟨⟩

/-- **`UpperWild` (GLUE, proved).** For `t > 0`, `G_{ℚ_p}^t ⊆ P_p`. -/
theorem upperWild : UpperWild p := by
  intro t ht σ hσ x hx0
  let F := FiniteGaloisIntermediateField.adjoin ℚ_[p] ({x} : Set (Kbar p))
  have hF : IsFinGal F.toIntermediateField := ⟨inferInstance, inferInstance⟩
  have hxF : x ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin ℚ_[p] {x} rfl
  exact wild_of_ramSet_one (ramSet_one_of_upperSet hF ht (hσ _ hF)) hxF hx0

end Wild

/-! ## §2d. Wild inertia fixes tame extensions (proved) -/

section Tame

variable {p : ℕ} [Fact p.Prime]

theorem wildSet_mul {σ τ : GQp p} (hσ : σ ∈ wildSet) (hτ : τ ∈ wildSet) : σ * τ ∈ wildSet := by
  intro x hx
  have hτx : τ x ≠ 0 := (map_ne_zero τ).mpr hx
  have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [he]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx))
  have := hσ (τ x) hτx
  rwa [norm_aut'] at this

theorem wildSet_pow {σ : GQp p} (hσ : σ ∈ wildSet) (k : ℕ) : σ ^ k ∈ wildSet := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_wildSet
  | succ k ih => rw [pow_succ]; exact wildSet_mul ih hσ

theorem norm_natCast_kbar {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : Kbar p)‖ = 1 := by
  have h := PadicAlgCl.norm_extends p (m : ℚ_[p])
  have e : ((m : ℚ_[p]) : PadicAlgCl p) = (m : Kbar p) := map_natCast (algebraMap ℚ_[p] _) m
  rw [e] at h
  rw [h, Padic.norm_natCast_eq_one_iff]
  exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)

/-- In an ultrametric normed group, a finite sum of terms of norm `< c` has norm `< c`. -/
theorem norm_sum_range_lt {f : ℕ → Kbar p} {c : ℝ} (hc : 0 < c) (m : ℕ)
    (hf : ∀ k < m, ‖f k‖ < c) : ‖∑ k ∈ Finset.range m, f k‖ < c := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    rw [Finset.sum_range_succ]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (ih fun k hk => hf k (by omega)) (hf m (by omega)))

/-- **The averaging argument.** A wild `σ` with `σ^m x = x`, `p ∤ m`, fixes `x`. -/
theorem fix_of_wild_pow {σ : GQp p} (hσ : σ ∈ wildSet) {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m)
    {x : Kbar p} (hx : (σ ^ m) x = x) : σ x = x := by
  set S := ∑ k ∈ Finset.range m, (σ ^ k) x with hS
  have hσS : σ S = S := by
    have h1 : σ S = ∑ k ∈ Finset.range m, (σ ^ (k + 1)) x := by
      rw [hS, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    have h2 := Finset.sum_range_succ' (fun k => (σ ^ k) x) m
    have h3 := Finset.sum_range_succ (fun k => (σ ^ k) x) m
    simp only [pow_zero, AlgEquiv.one_apply] at h2
    rw [hx] at h3
    rw [h1]
    rw [← hS] at h3
    linear_combination -(h3.symm.trans h2)
  have hkS : ∀ k : ℕ, (σ ^ k) S = S := by
    intro k
    induction k with
    | zero => rw [pow_zero, AlgEquiv.one_apply]
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσS]
  have hm : (m : Kbar p) ≠ 0 := by
    intro h
    have := norm_natCast_kbar (p := p) hpm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set y := (m : Kbar p)⁻¹ * S with hy
  have hky : ∀ k : ℕ, (σ ^ k) y = y := by
    intro k
    rw [hy, map_mul, map_inv₀, map_natCast, hkS]
  set z := x - y with hz
  have hz0 : z = 0 := by
    by_contra hne
    have hsum : ∑ k ∈ Finset.range m, (z - (σ ^ k) z) = (m : Kbar p) * z := by
      have hterm : ∀ k ∈ Finset.range m, z - (σ ^ k) z = x - (σ ^ k) x := by
        intro k _
        rw [hz, map_sub, hky]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← hS, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, hz, hy, mul_sub, ← mul_assoc, mul_inv_cancel₀ hm,
        one_mul]
    have hlt : ‖∑ k ∈ Finset.range m, (z - (σ ^ k) z)‖ < ‖z‖ := by
      apply norm_sum_range_lt (norm_pos_iff.mpr hne)
      intro k _
      rw [norm_sub_rev]
      exact wildSet_pow hσ k z hne
    rw [hsum, norm_mul, norm_natCast_kbar hpm, one_mul] at hlt
    exact lt_irrefl _ hlt
  have hxy : x = y := sub_eq_zero.mp hz0
  rw [hxy]
  have := hky 1
  rwa [pow_one] at this

/-- The inertia subgroup at level `F`, pulled back: `{σ | ‖σx − x‖ < 1 for x ∈ 𝓞_F}`. -/
def inertiaSub (F : Fld p) (hF : IsFinGal F) : Subgroup (GQp p) where
  carrier := {σ | ∀ x ∈ F, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}
  one_mem' := by
    intro x _ _
    simp
  mul_mem' := by
    intro σ τ hσ hτ x hx hx1
    have hτx : τ x ∈ F := apply_mem hF τ hx
    have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [he]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx hx1))
    exact hσ (τ x) hτx (by rw [norm_aut']; exact hx1)
  inv_mem' := by
    intro σ hσ x hx hx1
    have hσx : σ⁻¹ x ∈ F := apply_mem hF σ⁻¹ hx
    have h1 : ‖σ⁻¹ x‖ ≤ 1 := by rw [norm_aut']; exact hx1
    have h2 := hσ (σ⁻¹ x) hσx h1
    have he : σ (σ⁻¹ x) = x := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [he, norm_sub_rev] at h2
    exact h2

theorem ramSet_zero_eq (F : Fld p) (hF : IsFinGal F) :
    ramSet F 0 = (inertiaSub F hF : Set (GQp p)) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  ext σ
  constructor
  · rintro ⟨ϖ', hϖ', h⟩ x hx hx1
    have := h x hx hx1
    rw [zero_add, pow_one] at this
    exact lt_of_le_of_lt this hϖ'.2.1
  · intro h
    refine ⟨ϖ, hϖ, fun x hx hx1 => ?_⟩
    rw [zero_add, pow_one]
    exact hϖ.2.2 _ (F.sub_mem (apply_mem hF σ hx) hx) (h x hx hx1)

/-- `e(F/ℚ_p) = |G_0|` as the order of a subgroup of `Gal(F/ℚ_p)`. -/
theorem ramCard_zero_eq (F : Fld p) (hF : IsFinGal F) :
    haveI : Normal ℚ_[p] F := hF.2.to_normal
    ramCard F 0 =
      Nat.card ((inertiaSub F hF).map (AlgEquiv.restrictNormalHom F)) := by
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  set φ : (F ≃ₐ[ℚ_[p]] F) → (F → Kbar p) := fun s x => ((s x : F) : Kbar p) with hφ
  have hφinj : Function.Injective φ := by
    intro s t h
    ext x
    have := congrFun h x
    exact this
  have himg : restr F '' ramSet F 0 =
      φ '' ((inertiaSub F hF).map (AlgEquiv.restrictNormalHom F) : Set _) := by
    rw [ramSet_zero_eq F hF, Subgroup.coe_map, Set.image_image]
    refine Set.image_congr fun σ _ => ?_
    funext x
    simp only [hφ, restr]
    exact (AlgEquiv.restrictNormalHom_apply F σ x).symm
  unfold ramCard
  rw [himg, Nat.card_image_of_injective hφinj]
  rfl

/-- **`WildFixTame` (GLUE, proved).** If `F/ℚ_p` is finite Galois with `p ∤ e(F/ℚ_p)`, wild
inertia fixes `F`. The restriction `s` of a wild `σ` lies in the inertia subgroup, of order `e`,
so its order `m` is prime to `p`; the averaging `y = m⁻¹ ∑_{k<m} σ^k x` then gives `σx = x`. -/
theorem wildFixTame : WildFixTame p := by
  intro F hF hpe σ hσ x hx
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  set s := AlgEquiv.restrictNormalHom F σ with hs
  have hσI : σ ∈ inertiaSub F hF := by
    intro y _ hy1
    by_cases hy0 : y = 0
    · simp [hy0]
    · exact lt_of_lt_of_le (hσ y hy0) hy1
  have hsK : s ∈ (inertiaSub F hF).map (AlgEquiv.restrictNormalHom F) := ⟨σ, hσI, rfl⟩
  have hdvd : orderOf s ∣ ramCard F 0 := by
    rw [ramCard_zero_eq F hF]
    have := orderOf_dvd_natCard (⟨s, hsK⟩ : (inertiaSub F hF).map (AlgEquiv.restrictNormalHom F))
    rwa [Subgroup.orderOf_mk] at this
  have he0 : ramCard F 0 ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_ramCard hF 0)
  have hm0 : 0 < orderOf s :=
    Nat.pos_of_ne_zero fun h => he0 (by rw [h] at hdvd; exact zero_dvd_iff.mp hdvd)
  have hpm : ¬ p ∣ orderOf s := fun h => hpe (h.trans hdvd)
  have hsm : AlgEquiv.restrictNormalHom F (σ ^ orderOf s) = 1 := by
    rw [map_pow, ← hs, pow_orderOf_eq_one]
  have hfix : (σ ^ orderOf s) x = x := by
    have := (AlgEquiv.restrictNormal_eq_one_iff F (σ ^ orderOf s)).mp hsm x hx
    exact this
  exact fix_of_wild_pow hσ hm0 hpm hfix

end Tame

/-! ## §2c. `HilbertSerreLadic` from T20 + T21 (proved by t-different) and a DVR model -/

section Bridge

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Glue: the DVR model of a finite Galois `F ⊆ ℚ̄_p`** (the transport between `LadicCond`'s
norm-defined filtrations and the ring-theoretic setting of T20-T22, `PkgI6`; Serre, *Corps
locaux*, II §2 and IV §1). There are a complete DVR `A` with perfect residue field and a DVR `B`
finite, torsion-free, separable and Galois over `A` (namely `A = ℤ_p` and `B = 𝓞_F`, the elements
of norm `≤ 1`), whose lower ramification groups `PkgI6.lowerRam A B i` have the orders
`ramCard F i` and are trivial only when `ramSet F i` fixes `F`, whose ramification index is
`e = ramCard F 0`, with `(p) = 𝔪_B^e` and every integer prime to `p` a unit of `B`. -/
def LadicDVRModel (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ F : Fld p, IsFinGal F →
    ∃ (A B : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : PerfectField (ResidueField A))
      (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B)
      (_ : Module.Finite A B) (_ : Module.IsTorsionFree A B)
      (_ : Algebra.IsSeparable (FractionRing A) (FractionRing B))
      (_ : IsGalois (FractionRing A) (FractionRing B)),
      (∀ i, Nat.card (PkgI6.lowerRam A B i) = ramCard F i) ∧
      (∀ i, PkgI6.lowerRam A B i = ⊥ → ramSet F i ⊆ fixSet F) ∧
      Ideal.ramificationIdx (maximalIdeal B) A = ramCard F 0 ∧
      Ideal.span {(p : B)} = maximalIdeal B ^ ramCard F 0 ∧
      (∀ n : ℕ, ¬ p ∣ n → IsUnit (n : B))

/-- In `B` with `(p) = 𝔪^e` and integers prime to `p` units: `(e) = 𝔪^{e·v_p(e)}`. -/
theorem span_natCast_eq {B : Type} [CommRing B] [IsLocalRing B] {p : ℕ} (hp : p.Prime)
    {e : ℕ} (he : e ≠ 0) (hpB : Ideal.span {(p : B)} = maximalIdeal B ^ e)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : B)) :
    Ideal.span {(e : B)} = maximalIdeal B ^ (e * padicValNat p e) := by
  have hdec := Nat.ordProj_mul_ordCompl_eq_self e p
  have hnd := Nat.not_dvd_ordCompl hp he
  rw [Nat.factorization_def e hp] at hdec hnd
  set v := padicValNat p e
  set u := e / p ^ v
  have hcast : (e : B) = (p : B) ^ v * (u : B) := by
    conv_lhs => rw [← hdec]
    push_cast
    rfl
  rw [hcast, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hpB,
    Ideal.span_singleton_eq_top.mpr (hunit u hnd), Ideal.mul_top, ← pow_mul]

variable {p : ℕ} [Fact p.Prime]

/-- **`HilbertSerreLadic` from T20 + T21 and the DVR model (GLUE, proved).** T20 and T21 are
the kernel's theorems `PkgI6.hilbertDifferentFormula`, `PkgI6.differentBound` (t-different). -/
theorem hilbertSerre_of_model (hM : LadicDVRModel p) : HilbertSerreLadic p := by
  intro F hF
  obtain ⟨A, B, _, _, _, _, _, _, _, _, _, _, _, _, _, hcard, hbot, he, hpB, hunit⟩ := hM F hF
  obtain ⟨N, hN, hD⟩ := PkgI6.hilbertDifferentFormula A B
  have hB := PkgI6.differentBound A B
  refine ⟨N, hbot N hN, ?_⟩
  have hsum : ∑ i ∈ Finset.range N, (Nat.card (PkgI6.lowerRam A B i) - 1) =
      ∑ i ∈ Finset.range N, (ramCard F i - 1) :=
    Finset.sum_congr rfl fun i _ => by rw [hcard i]
  rw [hsum] at hD
  have he0 : ramCard F 0 ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_ramCard hF 0)
  rw [he, hD, span_natCast_eq (Fact.out) he0 hpB hunit, ← pow_add] at hB
  have hm0 : maximalIdeal B ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hmu : ¬ IsUnit (maximalIdeal B) := by
    rw [Ideal.isUnit_iff]
    exact (maximalIdeal.isMaximal B).ne_top
  exact (pow_dvd_pow_iff hm0 hmu).mp hB

end Bridge

/-! ## §2e. The DVR model over `ℤ_p`: the arithmetic conjuncts are automatic -/

section BridgeZp

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

instance perfectField_residueField_Zp (p : ℕ) [Fact p.Prime] :
    PerfectField (ResidueField ℤ_[p]) :=
  PerfectField.of_ringEquiv (K := ZMod p) PadicInt.residueField.symm

/-- **Glue: the DVR model of a finite Galois `F ⊆ ℚ̄_p` over `ℤ_p`** (transport; Serre, *Corps
locaux* II §2, IV §1). There is a DVR `B` (namely `𝓞_F`, the elements of norm `≤ 1`), finite,
torsion-free, separable and Galois over `ℤ_p`, whose lower ramification groups
`PkgI6.lowerRam ℤ_p B i` have the orders `ramCard F i` and are trivial only when `ramSet F i`
fixes `F`. This is `LadicDVRModel` with `A = ℤ_p`; its other conjuncts are proved
(`ladicDVRModel_of_Zp`). -/
def LadicDVRModelZp (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ F : Fld p, IsFinGal F →
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (_ : Algebra ℤ_[p] B) (_ : Module.Finite ℤ_[p] B) (_ : Module.IsTorsionFree ℤ_[p] B)
      (_ : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing B))
      (_ : IsGalois (FractionRing ℤ_[p]) (FractionRing B)),
      (∀ i, Nat.card (PkgI6.lowerRam ℤ_[p] B i) = ramCard F i) ∧
      (∀ i, PkgI6.lowerRam ℤ_[p] B i = ⊥ → ramSet F i ⊆ fixSet F)

variable {p : ℕ} [Fact p.Prime]

/-- **`LadicDVRModel` from its `ℤ_p` form (GLUE, proved).** `e(B/ℤ_p) = |G_0|`
(t-different's `TDifferent.card_lowerRam_zero`), `(p) = 𝔪_{ℤ_p}` maps to `𝔪_B^e`
(`TDifferent.map_maximalIdeal_eq_pow`), and integers prime to `p` are units of `ℤ_p`. -/
theorem ladicDVRModel_of_Zp (h : LadicDVRModelZp p) : LadicDVRModel p := by
  intro F hF
  obtain ⟨B, _, _, _, _, _, _, _, _, hcard, hbot⟩ := h F hF
  have : IsGaloisGroup (B ≃ₐ[ℤ_[p]] B) ℤ_[p] B := TDifferent.isGaloisGroup_algEquiv ℤ_[p] B
  have : Finite (B ≃ₐ[ℤ_[p]] B) := TDifferent.finite_algEquiv ℤ_[p] B
  have : PerfectField (maximalIdeal ℤ_[p]).ResidueField :=
    PerfectField.of_ringEquiv (K := ResidueField ℤ_[p])
      (RingEquiv.ofBijective
        (algebraMap (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (maximalIdeal ℤ_[p]).ResidueField :
          ResidueField ℤ_[p] →+* _)
        (maximalIdeal ℤ_[p]).bijective_algebraMap_quotient_residueField)
  have : Algebra.HasSeparableResidueFieldsAt ℤ_[p] B (maximalIdeal ℤ_[p]) := inferInstance
  have he : Ideal.ramificationIdx (maximalIdeal B) ℤ_[p] = ramCard F 0 := by
    rw [← TDifferent.card_lowerRam_zero ℤ_[p] B, hcard 0]
  refine ⟨ℤ_[p], B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcard, hbot, he, ?_, ?_⟩
  · have hmap := TDifferent.map_maximalIdeal_eq_pow ℤ_[p] B
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast,
      he] at hmap
    exact hmap
  · intro n hn
    have hu : IsUnit (n : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn
    have := hu.map (algebraMap ℤ_[p] B)
    rwa [map_natCast] at this

end BridgeZp

/-! ## §2f. The `ℤ_p`-model `𝓞_F = integralClosure ℤ_p F` (proved): `LadicDVRModelZp` -/

section DVRModelSec

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

section Model

variable (F : Fld p)

/-- `ℤ_p → ℚ_p → F`. -/
@[reducible] def algZpF : Algebra ℤ_[p] F :=
  ((algebraMap ℚ_[p] F).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

attribute [local instance] algZpF

instance towerZpF : IsScalarTower ℤ_[p] ℚ_[p] F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The ring of integers `𝓞_F = integralClosure ℤ_p F`. -/
abbrev OF := integralClosure ℤ_[p] F

theorem norm_eq_spectral (x : F) : ‖(x : Kbar p)‖ = spectralNorm ℚ_[p] F x := by
  rw [spectralNorm.eq_of_tower (L := Kbar p) x, PadicAlgCl.spectralNorm_eq]
  rfl

variable [FiniteDimensional ℚ_[p] F]

/-- `y ∈ F` is integral over `ℤ_p` iff `‖y‖ ≤ 1` (copied from glue-sqrt-local's
`isIntegral_iff_spectralNorm_le_one`, with the norm of `ℚ̄_p`). -/
theorem isIntegral_iff_norm_le_one (y : F) :
    IsIntegral ℤ_[p] y ↔ ‖(y : Kbar p)‖ ≤ 1 := by
  rw [norm_eq_spectral]
  have hyQ : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

theorem mem_OF (y : F) : y ∈ OF F ↔ ‖(y : Kbar p)‖ ≤ 1 := isIntegral_iff_norm_le_one F y

theorem norm_le_one (b : OF F) : ‖((b : F) : Kbar p)‖ ≤ 1 := (mem_OF F b).mp b.2

theorem isUnit_iff_norm (b : OF F) : IsUnit b ↔ ‖((b : F) : Kbar p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖(((u : OF F) : F) : Kbar p)‖ * ‖((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p)‖ = 1 := by
      rw [← norm_mul]
      have : ((u : OF F) : F) * (((u⁻¹ : (OF F)ˣ) : OF F) : F) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
      have h2 : (((u : OF F) : F) : Kbar p) * ((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p) = 1 := by
        rw [← IntermediateField.coe_mul, this, IntermediateField.coe_one]
      rw [h2, norm_one]
    have a1 := norm_le_one F u
    have a2 := norm_le_one F (u⁻¹ : (OF F)ˣ)
    have b1 := norm_nonneg ((((u : OF F) : F) : Kbar p))
    have b2 := norm_nonneg (((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p))
    nlinarith
  · intro h
    have hx0 : (b : F) ≠ 0 := by
      intro h0
      rw [h0, IntermediateField.coe_zero, norm_zero] at h
      exact zero_ne_one h
    have hinv : ‖(((b : F)⁻¹ : F) : Kbar p)‖ = 1 := by
      rw [IntermediateField.coe_inv, norm_inv, h, inv_one]
    have hint : ((b : F)⁻¹) ∈ OF F := (mem_OF F _).mpr hinv.le
    refine IsUnit.of_mul_eq_one (⟨_, hint⟩ : OF F) ?_
    apply Subtype.ext
    simp [hx0]

theorem isLocalRing_OF : IsLocalRing (OF F) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff_norm] at ha hb ⊢
  have ha' : ‖((a : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F a) ha
  have hb' : ‖((b : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F b) hb
  have := IsUltrametricDist.norm_add_le_max ((a : F) : Kbar p) ((b : F) : Kbar p)
  intro hab
  rw [Subalgebra.coe_add, IntermediateField.coe_add] at hab
  rw [hab] at this
  exact absurd this (not_le.mpr (max_lt ha' hb'))

end Model

section Model2

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] algZpF

theorem finite_OF : Module.Finite ℤ_[p] (OF F) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] F (OF F)

theorem noeth_OF : IsNoetherianRing (OF F) :=
  IsIntegralClosure.isNoetherianRing ℤ_[p] ℚ_[p] F (OF F)

theorem dedekind_OF : IsDedekindDomain (OF F) :=
  IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] F (OF F)

omit [FiniteDimensional ℚ_[p] F] in
theorem coe_natCast_F (n : ℕ) : ((n : F) : Kbar p) = n := map_natCast (algebraMap F (Kbar p)) n

theorem p_mem : ((p : ℕ) : F) ∈ OF F := by
  rw [mem_OF, coe_natCast_F, norm_p_kbar]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)

theorem not_isField_OF : ¬ IsField (OF F) := by
  intro h
  have hp0 : (⟨((p : ℕ) : F), p_mem F⟩ : OF F) ≠ 0 := by
    intro h0
    have := congrArg (fun x : OF F => ((x : F) : Kbar p)) h0
    simp only [ZeroMemClass.coe_zero] at this
    rw [coe_natCast_F] at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  obtain ⟨b, hb⟩ := h.mul_inv_cancel hp0
  have hu : IsUnit (⟨((p : ℕ) : F), p_mem F⟩ : OF F) := IsUnit.of_mul_eq_one _ hb
  rw [isUnit_iff_norm] at hu
  change ‖(((p : ℕ) : F) : Kbar p)‖ = 1 at hu
  rw [coe_natCast_F, norm_p_kbar, inv_eq_one] at hu
  have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

theorem dvr_OF : IsDiscreteValuationRing (OF F) := by
  haveI := isLocalRing_OF F
  haveI := noeth_OF F
  haveI := dedekind_OF F
  have h := (IsDiscreteValuationRing.TFAE (OF F) (not_isField_OF F)).out 1 3
  exact h.mpr (dedekind_OF F)

theorem torsionFree_OF : Module.IsTorsionFree ℤ_[p] (OF F) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap ℤ_[p] F) :=
    (algebraMap ℚ_[p] F).injective.comp (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p])
  intro a b h
  apply hinj
  have := congrArg (fun x : OF F => (x : F)) h
  exact this

variable {F}

/-- The uniformizer `ϖ` as an element of `𝓞_F`. -/
def unifB {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : OF F :=
  ⟨⟨ϖ, hϖ.1⟩, (mem_OF F _).mpr hϖ.2.1.le⟩

theorem coe_unifB {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : (((unifB hϖ : OF F) : F) : Kbar p) = ϖ := rfl

theorem norm_unif_pos {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : 0 < ‖ϖ‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpF : (p : Kbar p) ∈ F := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hpn : ‖(p : Kbar p)‖ < 1 := by rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
  have hp := hϖ.2.2 _ hpF hpn
  exact lt_of_lt_of_le (by rw [norm_p_kbar]; positivity) hp

theorem mem_span_pow_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (k : ℕ) (b : OF F) :
    b ∈ Ideal.span {unifB hϖ ^ k} ↔ ‖((b : F) : Kbar p)‖ ≤ ‖ϖ‖ ^ k := by
  have hϖ0 := norm_unif_pos hϖ
  have hϖne : ϖ ≠ 0 := norm_pos_iff.mp hϖ0
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    have : (((c * unifB hϖ ^ k : OF F) : F) : Kbar p) = ((c : F) : Kbar p) * ϖ ^ k := by
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, IntermediateField.coe_mul,
        IntermediateField.coe_pow, coe_unifB]
    rw [this, norm_mul, norm_pow]
    calc ‖((c : F) : Kbar p)‖ * ‖ϖ‖ ^ k ≤ 1 * ‖ϖ‖ ^ k :=
          mul_le_mul_of_nonneg_right (norm_le_one F c) (by positivity)
      _ = ‖ϖ‖ ^ k := one_mul _
  · intro h
    set ϖF : F := ⟨ϖ, hϖ.1⟩
    have hϖF : ϖF ≠ 0 := by
      intro h0
      exact hϖne (congrArg (fun x : F => (x : Kbar p)) h0)
    set c : F := (b : F) * (ϖF ^ k)⁻¹ with hc
    have hcn : ‖(c : Kbar p)‖ ≤ 1 := by
      rw [hc, IntermediateField.coe_mul, IntermediateField.coe_inv, IntermediateField.coe_pow,
        norm_mul, norm_inv, norm_pow]
      have : ‖((ϖF : F) : Kbar p)‖ = ‖ϖ‖ := rfl
      rw [this]
      rw [mul_inv_le_iff₀ (by positivity), one_mul]
      exact h
    refine ⟨⟨c, (mem_OF F c).mpr hcn⟩, ?_⟩
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow]
    change c * ϖF ^ k = (b : F)
    rw [hc, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hϖF), mul_one]

theorem maximalIdeal_eq {ϖ : Kbar p} (hϖ : IsUnif F ϖ) :
    haveI := isLocalRing_OF F
    maximalIdeal (OF F) = Ideal.span {unifB hϖ} := by
  haveI := isLocalRing_OF F
  ext b
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm, ← pow_one (unifB hϖ),
    mem_span_pow_iff, pow_one]
  constructor
  · intro h
    exact hϖ.2.2 _ (b : F).2 (lt_of_le_of_ne (norm_le_one F b) h)
  · intro h h1
    rw [h1] at h
    exact absurd hϖ.2.1 (not_lt.mpr h)

theorem mem_maximalIdeal_pow_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (k : ℕ) (b : OF F) :
    haveI := isLocalRing_OF F
    b ∈ maximalIdeal (OF F) ^ k ↔ ‖((b : F) : Kbar p)‖ ≤ ‖ϖ‖ ^ k := by
  haveI := isLocalRing_OF F
  rw [maximalIdeal_eq hϖ, Ideal.span_singleton_pow, mem_span_pow_iff]

end Model2

section Galois

attribute [local instance] algZpF FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] torsionFree_OF

instance faithful_OF : FaithfulSMul ℤ_[p] (OF F) := by
  rw [faithfulSMul_iff_algebraMap_injective, ← Module.isTorsionFree_iff_algebraMap_injective]
  exact torsionFree_OF F

instance faithful_frac_OF : FaithfulSMul ℤ_[p] (FractionRing (OF F)) := inferInstance


instance isFractionRing_OF : IsFractionRing (OF F) F :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] F

theorem hcomp :
    (algebraMap (FractionRing ℤ_[p]) (FractionRing (OF F))).comp
        ((FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.toRingEquiv : ℚ_[p] →+* FractionRing ℤ_[p]) =
      ((FractionRing.algEquiv (OF F) F).symm.toRingEquiv : F →+* FractionRing (OF F)).comp
        (algebraMap ℚ_[p] F) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
  ext z
  simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv]
  have h1 : (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm (algebraMap ℤ_[p] ℚ_[p] z) =
      algebraMap ℤ_[p] (FractionRing ℤ_[p]) z :=
    (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.commutes z
  have h2 : algebraMap ℚ_[p] F (algebraMap ℤ_[p] ℚ_[p] z) =
      algebraMap (OF F) F (algebraMap ℤ_[p] (OF F) z) := rfl
  have h3 : (FractionRing.algEquiv (OF F) F).symm (algebraMap (OF F) F (algebraMap ℤ_[p] (OF F) z))
      = algebraMap (OF F) (FractionRing (OF F)) (algebraMap ℤ_[p] (OF F) z) :=
    (FractionRing.algEquiv (OF F) F).symm.commutes _
  rw [h1, h2, h3, ← IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p])
    (FractionRing (OF F)), IsScalarTower.algebraMap_apply ℤ_[p] (OF F) (FractionRing (OF F))]

theorem isGalois_frac [IsGalois ℚ_[p] F] :
    IsGalois (FractionRing ℤ_[p]) (FractionRing (OF F)) :=
  IsGalois.of_equiv_equiv (hcomp F)

theorem isSeparable_frac :
    Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (OF F)) :=
  Algebra.IsSeparable.of_equiv_equiv _ _ (hcomp F)

end Galois

section Filtration

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem coe_galRestrict (s : F ≃ₐ[ℚ_[p]] F) (b : OF F) :
    ((galRestrict ℤ_[p] ℚ_[p] F (OF F) s b : OF F) : F) = s (b : F) :=
  algebraMap_galRestrict_apply ℤ_[p] s b

theorem mem_lowerRam_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (i : ℕ) (s : F ≃ₐ[ℚ_[p]] F) :
    haveI := isLocalRing_OF F
    galRestrict ℤ_[p] ℚ_[p] F (OF F) s ∈ PkgI6.lowerRam ℤ_[p] (OF F) i ↔
      ∀ x : F, ‖(x : Kbar p)‖ ≤ 1 → ‖((s x : F) : Kbar p) - x‖ ≤ ‖ϖ‖ ^ (i + 1) := by
  haveI := isLocalRing_OF F
  rw [PkgI6.mem_lowerRam]
  constructor
  · intro h x hx
    have := (mem_maximalIdeal_pow_iff hϖ (i + 1) _).mp (h ⟨x, (mem_OF F x).mpr hx⟩)
    rw [Subalgebra.coe_sub, coe_galRestrict, AddSubgroupClass.coe_sub] at this
    exact this
  · intro h b
    rw [mem_maximalIdeal_pow_iff hϖ, Subalgebra.coe_sub, coe_galRestrict,
      AddSubgroupClass.coe_sub]
    exact h b (norm_le_one F b)

end Filtration

section Card

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem mem_ramSet_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (i : ℕ) (σ : GQp p) :
    haveI := isLocalRing_OF F
    σ ∈ ramSet F i ↔ galRestrict ℤ_[p] ℚ_[p] F (OF F) (AlgEquiv.restrictNormalHom F σ) ∈
      PkgI6.lowerRam ℤ_[p] (OF F) i := by
  haveI := isLocalRing_OF F
  rw [mem_lowerRam_iff hϖ]
  constructor
  · rintro ⟨ϖ', hϖ', h⟩ x hx
    rw [AlgEquiv.restrictNormalHom_apply, ← IsUnif.norm_eq hϖ hϖ']
    exact h x x.2 hx
  · intro h
    refine ⟨ϖ, hϖ, fun x hx hx1 => ?_⟩
    have := h ⟨x, hx⟩ hx1
    rwa [AlgEquiv.restrictNormalHom_apply] at this

theorem card_lowerRam (i : ℕ) :
    haveI := isLocalRing_OF F
    Nat.card (PkgI6.lowerRam ℤ_[p] (OF F) i) = ramCard F i := by
  haveI := isLocalRing_OF F
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (inferInstance : FiniteDimensional ℚ_[p] F)
  set G := galRestrict ℤ_[p] ℚ_[p] F (OF F) with hG
  set K : Set (F ≃ₐ[ℚ_[p]] F) := {s | G s ∈ PkgI6.lowerRam ℤ_[p] (OF F) i} with hKdef
  have h1 : Nat.card (PkgI6.lowerRam ℤ_[p] (OF F) i) = Nat.card K :=
    (Nat.card_congr (G.toEquiv.subtypeEquiv (fun s => Iff.rfl))).symm
  have hK : K = AlgEquiv.restrictNormalHom F '' ramSet F i := by
    ext s
    constructor
    · intro hs
      obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (Kbar p) s
      exact ⟨σ, (mem_ramSet_iff hϖ i σ).mpr hs, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact (mem_ramSet_iff hϖ i σ).mp hσ
  set φ : (F ≃ₐ[ℚ_[p]] F) → (F → Kbar p) := fun s x => ((s x : F) : Kbar p) with hφ
  have hφinj : Function.Injective φ := by
    intro s t h
    ext x
    exact congrFun h x
  have himg : restr F '' ramSet F i = φ '' (AlgEquiv.restrictNormalHom F '' ramSet F i) := by
    rw [Set.image_image]
    refine Set.image_congr fun σ _ => ?_
    funext x
    exact (AlgEquiv.restrictNormalHom_apply F σ x).symm
  unfold ramCard
  rw [himg, Nat.card_image_of_injective hφinj, ← hK, h1]

theorem fix_of_lowerRam_bot (i : ℕ) :
    haveI := isLocalRing_OF F
    PkgI6.lowerRam ℤ_[p] (OF F) i = ⊥ → ramSet F i ⊆ fixSet F := by
  haveI := isLocalRing_OF F
  intro hbot σ hσ
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (inferInstance : FiniteDimensional ℚ_[p] F)
  have h := (mem_ramSet_iff hϖ i σ).mp hσ
  rw [hbot, Subgroup.mem_bot, ← map_one (galRestrict ℤ_[p] ℚ_[p] F (OF F))] at h
  have h1 := (galRestrict ℤ_[p] ℚ_[p] F (OF F)).injective h
  intro x hx
  exact (AlgEquiv.restrictNormal_eq_one_iff F σ).mp h1 x hx

end Card

section FinalZp

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {p : ℕ} [Fact p.Prime]

/-- **`LadicDVRModelZp` (GLUE, proved).** `B = 𝓞_F = integralClosure ℤ_p F`: a DVR (local by the
ultrametric norm, Dedekind as an integral closure, `IsDiscreteValuationRing.TFAE`), finite and
torsion-free over `ℤ_p`, with `Frac(B) ≅ F` Galois over `Frac(ℤ_p) ≅ ℚ_p`
(`IsGalois.of_equiv_equiv`); `𝔪_B^k = {‖b‖ ≤ ‖ϖ‖^k}`, and `galRestrict` identifies
`PkgI6.lowerRam ℤ_p B i` with the restrictions of `ramSet F i`. -/
theorem ladicDVRModelZp : LadicDVRModelZp p := by
  intro F hF
  haveI : FiniteDimensional ℚ_[p] F := hF.1
  haveI : IsGalois ℚ_[p] F := hF.2
  letI := algZpF F
  haveI := torsionFree_OF F
  haveI := faithful_OF F
  haveI := dvr_OF F
  exact ⟨OF F, inferInstance, inferInstance, dvr_OF F, inferInstance, finite_OF F,
    torsionFree_OF F, isSeparable_frac F, isGalois_frac F, card_lowerRam, fix_of_lowerRam_bot⟩

end FinalZp

end DVRModelSec

/-! ## §3. The reduction (proved) -/

section Reduction

theorem gl_eq_one_of_scalar {ℓ : ℕ} [Fact ℓ.Prime] {g : GL (Fin 2) (PadicAlgCl ℓ)}
    {c : PadicAlgCl ℓ} (h : (g : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = Matrix.scalar (Fin 2) c)
    (hc : c = 1) : g = 1 := by
  apply Units.ext
  rw [h, hc, map_one, Units.val_one]

/-- **`LocalRamG` from the local pieces (GLUE, proved).** -/
theorem localRamG_of {ℓ : ℕ} [Fact ℓ.Prime] (u : ℚ) (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (r : GaloisRep ℓ 2) (hUB : UpperBreakFix p) (hUW : UpperWild p) (hWT : WildFixTame p)
    (hd : LocalData p r) (h11 : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) r) :
    LocalRamG u p r := by
  refine ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_, fun hS hM => ?_⟩
  · obtain ⟨F, β, hF, he, hsh, hup⟩ := hd.1 hpD
    have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
      Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
    have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
    have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold U0 at ht; exact ht) hσ
    have hwild : σ ∈ wildSet := hUW t (by linarith) hσ
    exact gl_eq_one_of_scalar (hsh σ ⟨hfix, hwild⟩) (hup t ht σ ⟨hσ, hfix⟩)
  · obtain ⟨F, β, hF, he, hsh, htame⟩ := hd.2 hpD
    have hfix := hWT F hF he hσ
    exact gl_eq_one_of_scalar (hsh σ ⟨hfix, hσ⟩) (htame σ ⟨hfix, hσ⟩)
  · refine h11 p (Fact.out) ?_ hpℓ
    intro hT
    rcases Finset.mem_union.mp hT with h | h
    · exact hS h
    · exact hM (Nat.mem_primeFactors.mp h).2.1

/-- **`G15RamG` from smaller named Props (GLUE, proved).** Closed local-field Props
(`UpperBreakFix`, `UpperWild`, `WildFixTame`), the local data of G8/G7 on `D` (`LocalData`), and
G11's output on `D` for `T = S_mul ∪ supp M_{S_mul}(u)` (`GlueDescent.ramSet`). -/
theorem g15RamG_of_pieces
    (hUB : ∀ (p : ℕ) [Fact p.Prime], UpperBreakFix p)
    (hUW : ∀ (p : ℕ) [Fact p.Prime], UpperWild p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h5' => localRamG_of u p h5' D.r5 (hUB p) (hUW p) (hWT p) (h5 p hp h5') h11₅,
    fun h5' => ?_⟩
  subst h5'
  exact localRamG_of u 5 (by norm_num) D.r3 (hUB 5) (hUW 5) (hWT 5) h3 h11₃

/-- **`G15RamG`, with D1 discharged (GLUE, proved).** As `g15RamG_of_pieces`, with
`UpperBreakFix` replaced by the transport `HilbertSerreLadic` of T20 + T21. -/
theorem g15RamG_of_hilbertSerre
    (hHS : ∀ (p : ℕ) [Fact p.Prime], HilbertSerreLadic p)
    (hUW : ∀ (p : ℕ) [Fact p.Prime], UpperWild p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_pieces (fun p _ => upperBreakFix_of_hilbertSerre (hHS p)) hUW hWT D u h5 h3
    h11₅ h11₃

/-- **`G15RamG` from the DVR model, T20-T21 (proved in the kernel), `WildFixTame` and the data
of G7-G8-G11 on `D` (GLUE, proved).** `UpperWild` is proved (`upperWild`). -/
theorem g15RamG_of_model
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModel p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_hilbertSerre (fun p _ => hilbertSerre_of_model (hM p)) (fun p _ => upperWild) hWT
    D u h5 h3 h11₅ h11₃

/-- **`G15RamG` with all closed local-field glue proved except the DVR model (GLUE, proved).**
Hypotheses: the transport `LadicDVRModel`, the data of G7-G8 on `D` (`LocalData`), and G11's
output on `D`. -/
theorem g15RamG_of_dvrModel
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModel p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_model hM (fun p _ => wildFixTame) D u h5 h3 h11₅ h11₃

/-- **`G15RamG` from the `ℤ_p`-model of finite Galois `F ⊆ ℚ̄_p` (GLUE, proved).** -/
theorem g15RamG_of_zpModel
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModelZp p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_dvrModel (fun p _ => ladicDVRModel_of_Zp (hM p)) D u h5 h3 h11₅ h11₃

/-- The trivial two-dimensional representation (for the non-vacuity check below). -/
def trivRep (ℓ : ℕ) [Fact ℓ.Prime] : GaloisRep ℓ 2 := ⟨1, continuous_const⟩

/-- **Non-vacuity check (proved).** `LocalData p r` holds for the trivial representation (with
`F = ℚ_p`, `β = 1`), so the hypotheses on `D` are not contradictory. -/
theorem localData_trivRep (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] :
    LocalData p (trivRep ℓ) := by
  have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
  have hshape : TwistShape p (trivRep ℓ) ⊥ (fun _ => 1) := by
    intro σ _
    simp [trivRep, PkgI4.GaloisRep.restrictLocal]
  have he : ramCard (⊥ : Fld p) 0 = 1 := by
    have h1 := one_le_ramCard hF 0
    have h2 : ramCard (⊥ : Fld p) 0 ≤ 1 := by
      unfold ramCard
      have hfin := (finite_restr hF (ramSet (⊥ : Fld p) 0)).to_subtype
      refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => ?_⟩
      apply Subtype.ext
      obtain ⟨σ, -, hσ⟩ := a.2
      obtain ⟨τ, -, hτ⟩ := b.2
      rw [← hσ, ← hτ]
      funext x
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
      simp only [restr, ← hq, AlgEquiv.commutes]
    omega
  refine ⟨fun _ => ⟨⊥, fun _ => 1, hF, ?_, hshape, fun _ _ _ _ => rfl⟩,
    fun _ => ⟨⊥, fun _ => 1, hF, ?_, hshape, fun _ _ => rfl⟩⟩
  · rw [he]; exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [he]; exact (Nat.Prime.one_lt Fact.out).ne' ∘ Nat.dvd_one.mp

/-- **`G15RamG` from the data of G7-G8 on `D` and G11's output alone (GLUE, proved).** Every
closed local-field input is proved: `UpperBreakFix` (from T20, T21 and `ladicDVRModelZp`),
`UpperWild`, `WildFixTame`. -/
theorem g15RamG_of_localData
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_zpModel (fun _ _ => ladicDVRModelZp) D u h5 h3 h11₅ h11₃

end Reduction

end G15Ram

end

/-! ## §3' (local-data). Verbatim copies from scratch/g0-mod-galois/part_galois.lean -/

section G0GaloisSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ### Objects -/

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- `e` intertwines the operators `f g` on `V` with `r(g) ⊕ r(g)` on `ℚ̄_ℓ² × ℚ̄_ℓ²`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-- **Output of G7 (scalar descent, N5 L632-716) at the coefficient prime `ℓ`**, together with
the outputs of G4-G6 that G8 uses. `A` is the model over `K = L'` (an abelian surface with
`End_K(A)` of rank 4, the maximal order case of `End⁰ = B`: A9's output). The data are:
operators `Tm σ = μ_σ ∘ σ` on `ℚ̄_ℓ ⊗ V_ℓ(A)` (without `a_σ`: `GlueDescent.rho` multiplies by
`β_σ⁻¹ a_σ`, giving N5's `ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ`) with the cocycle `c` (`Tm g Tm h = c(g,h) Tm(gh)`),
the scalars `a` and the cochain `β` with `a_g a_h c(g,h) = ε(g,h) a_{gh}` and
`β_g β_h = ε(g,h) β_{gh}` (`∂β = ε`, B2-B3), all trivial on `G_{L'}` where `Tm` is the Tate
action (`L'` contains the kernel field of `β|G_L`; it is taken finite Galois over `ℚ`, as
g0-mod-field's `G7Data` supplies, which `G10Glue` needs); a system of `2 × 2` matrix units (the image of
`B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`) commuting with every `Tm σ` (`μ_σ` is `B`-linear); and continuity of
`σ ↦ β_σ⁻¹ a_σ Tm σ` (glue-rho-cont proved continuity on `G_K`; finite index gives the rest). -/
def G7Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) : Prop :=
  A.dim = 2 ∧ Module.finrank ℤ (PkgI3.AbVar.End A) = 4 ∧
  (∀ g h, Tm g * Tm h = c g h • Tm (g * h)) ∧
  (∀ g h, a g * a h * c g h = ε g h * a (g * h)) ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧
  (∀ σ, Tm (resQ K σ) = tate A ℓ σ ∧ a (resQ K σ) = 1 ∧ β (resQ K σ) = 1) ∧
  (∀ g i j, Commute (Tm g) (u.e i j)) ∧
  (∀ (f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ)) (v : Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho Tm a β g v))

/-- **Output of G8.** `r : G_ℚ → GL₂(ℚ̄_ℓ)` (continuous) and `e : ℚ̄_ℓ ⊗ V_ℓ(A) ≅ ℚ̄_ℓ² × ℚ̄_ℓ²`
with: (i) `e` intertwines the descended representation `ρ` (an operator family on
`ℚ̄_ℓ ⊗ V_ℓ(A)`, in the theorem `GlueDescent.rho Tm a β`) with `r ⊕ r` on all of `G_ℚ`;
(ii) `ρ` is the Tate action on `G_{L'}`; (iii) `r|G_{L'}` is absolutely irreducible, in
Burnside's form (the matrices `r(σ)`, `σ ∈ G_{L'}`, generate `M₂(ℚ̄_ℓ)`). -/
def G8Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ)) (r : GaloisRep ℓ 2) : Prop :=
  (∀ σ, ρ (resQ K σ) = tate A ℓ σ) ∧
  ∃ e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ),
    Intertwines ρ r.mat e ∧
    Algebra.adjoin (PadicAlgCl ℓ) (Set.range fun σ => r.mat (resQ K σ)) = ⊤

end G0Galois

end

end G0GaloisSec
noncomputable section

/-! ## §4 (local-data). `LocalData p r` on G8's `r`, from G7's data

The copied `LocalData p r` (§1) is a predicate on a bare `r : GaloisRep ℓ 2`. Here:

* `largePrimeData_iff`, `localData_large_iff` (proved): for `p > D`, `LocalData p r ↔ r` is
  trivial on wild inertia. So `LocalData` fails for any `r` wildly ramified at some `p > D`
  (e.g. `ψ ⊕ 1`, `ψ` a Dirichlet character of conductor `p²`), and cannot be proved for
  arbitrary `r`: it is a claim about the `r` that G8 builds.
* **Main result** `localData_of_g7` (proved): for `r` as in G8's output (`G0Galois.G8Out`) on
  `ρ = GlueDescent.rho Tm a β`, `LocalData p r` follows, at every prime `p`, from
  `G7Clauses β ε L` (clauses of G4/G7) and `LocalGlue p Tm a β L` (the Tate-module glue
  `TorsionFieldWild` at `p ≤ D`, `TateWildTrivialL` at `p > D`, and `BetaUpper` at `p = 2`).
  `g15RamG_of_g7` composes it with g15-ram's `g15RamG_of_localData`.
* On the way (all proved): `twistShape_of_g8` (`r` is scalar where `ρ` is), `betaTame_of_odd`,
  `betaOpen_of_isLocallyConstant`, `wild_fix_root` (wild inertia fixes `μ_n`, `p² ∤ n`),
  `galChar_decomp_wild`, `betaSqWild_of_chi`, `betaCharOn_of_cocycle`, `wild_fix_small_degree`
  (wild inertia fixes every `E` with `[E:ℚ_p] < p`), `exists_finGal_ramCard_le` (Galois closure
  with `e ≤ [E:ℚ_p]!`), `exists_local_field_le` (`[L_v:ℚ_p] ≤ [L:ℚ]`).
-/

namespace G15Ram

open PkgI4 (GQp GaloisRep GQ decomp)
open LadicCond G0ModNewform

section LocalDataSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### The characterization at `p > D` -/

/-- At `p > D` the local data say exactly that `r` is trivial on wild inertia: `F` is tame, so
`P_p ⊆ G_F` (`wildFixTame`), and `r = β = 1` on `G_F ∩ P_p`. Conversely take `F = ℚ_p`. -/
theorem largePrimeData_iff (r : GaloisRep ℓ 2) :
    LargePrimeData p r ↔ ∀ σ ∈ wildSet, r.restrictLocal p σ = 1 := by
  constructor
  · rintro ⟨F, β, hF, hpe, hsh, htm⟩ σ hσ
    have hfix : σ ∈ fixSet F := wildFixTame F hF hpe hσ
    have h1 := hsh σ ⟨hfix, hσ⟩
    rw [htm σ ⟨hfix, hσ⟩, Matrix.scalar_apply, Matrix.diagonal_one] at h1
    exact Units.ext h1
  · intro h
    have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
    have hcard : ramCard (⊥ : Fld p) 0 = 1 := by
      have h1 := one_le_ramCard hF 0
      have h2 : ramCard (⊥ : Fld p) 0 ≤ 1 := by
        unfold ramCard
        have hfin := (finite_restr hF (ramSet (⊥ : Fld p) 0)).to_subtype
        refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => ?_⟩
        apply Subtype.ext
        obtain ⟨σ, -, hσ⟩ := a.2
        obtain ⟨τ, -, hτ⟩ := b.2
        rw [← hσ, ← hτ]
        funext x
        obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
        simp only [restr, ← hq, AlgEquiv.commutes]
      omega
    refine ⟨⊥, fun _ => 1, hF, ?_, ?_, fun _ _ => rfl⟩
    · rw [hcard]; exact (Fact.out : p.Prime).not_dvd_one
    · intro σ hσ
      rw [h σ hσ.2, Matrix.scalar_apply, Matrix.diagonal_one]
      rfl

/-- **`LocalData` at `p > D`, characterized (proved).** -/
theorem localData_large_iff (r : GaloisRep ℓ 2) (hp : (ZInQ.heightD : ℝ) < p) :
    LocalData p r ↔ ∀ σ ∈ wildSet, r.restrictLocal p σ = 1 := by
  rw [← largePrimeData_iff]
  constructor
  · exact fun h => h.2 hp
  · exact fun h => ⟨fun hle => absurd hp (not_lt.mpr hle), fun _ => h⟩

/-! ### From `ρ` to `r` (linear algebra) -/

/-- If `e` intertwines `ρ` with `m ⊕ m` and `ρ(g)` is the scalar `c`, then `m(g)` is the scalar
`c`. -/
theorem mat_eq_scalar_of_intertwines {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {f : G → Module.End (PadicAlgCl ℓ) V} {m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)}
    {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines f m e) {g : G} {c : PadicAlgCl ℓ} (hg : f g = c • 1) :
    m g = Matrix.scalar (Fin 2) c := by
  have hv : ∀ x : Fin 2 → PadicAlgCl ℓ, (m g).mulVec x = c • x := by
    intro x
    have := h g (e.symm (x, x))
    rw [hg, LinearMap.smul_apply, Module.End.one_apply, map_smul,
      LinearEquiv.apply_symm_apply] at this
    exact (congrArg Prod.fst this).symm
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hv x, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

/-! ### The smaller Props on G7's data at `p` -/

/-- **Glue on G4/G7 + R6 + D2 (N5 L719-727, L819-823; at `p > D` G3 + Néron–Ogg–Shafarevich,
N5 L848-851).** On `G_F ∩ P_p` (pushed to `G_ℚ` by `decomp`) the twisted Tate action
`a_σ μ_σ ∘ σ` (`a σ • Tm σ`) is the identity. Glazer: for `σ ∈ G_L` (`F ⊇ L_v`) the descent
datum has `a_σ μ_σ = 1`, so `a_σ Tm σ` is the Tate action of `A/L`; `A` is semistable over
`F ⊇ L_v(A[3])` (`A[5]` if `p = 3`) by Raynaud's criterion (R6, `PkgI2.RaynaudCriterion`), and
then wild inertia acts trivially on `V_ℓ` (D2, `PkgI2.D2_fixed_of_raynaud`); at `p > D`, `A` has
good reduction (G3) and inertia acts trivially (`PkgI2.inertiaTrivial_of_goodReduction`).
Only claimed for `p ≠ ℓ` (D2 and Néron–Ogg–Shafarevich are about `V_ℓ`, `ℓ ≠ p`; at `p = ℓ` it is
false in general); `g15RamG_of_g8` uses it only at `p ≠ ℓ`. -/
def TateWildTrivial {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, a (decomp p σ) • Tm (decomp p σ) = 1

/-- **Glue on G7's `β` (D3 + T16; N5 L823-844).** `β` is trivial on `G_{ℚ_p}^t ∩ G_F` for
`t > U`. At odd `p` it follows from `BetaTame` (`betaUpper_of_betaTame`); at `p = 2` from local
reciprocity with the upper numbering theorem (T16, `PkgI6.LocalReciprocityUpper`) and
`(U_F^{e+1})⁴ = U_F^{3e+1}` (D3, `GlueConductor.fourth_pow_mem`) applied to the character
`β|_{G_F}`, `ψ ≥ id`, and `max(4D², 3e) ≤ U₀` (`GlueConductor.max_le_U0`). -/
def BetaUpper (β : GQ → PadicAlgCl ℓ) (F : Fld p) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, β (decomp p σ) = 1

/-- **Glue on G7's `β` at odd `p` (N5 L835-838, L848-851).** `β` is trivial on `G_F ∩ P_p`.
Proved for odd `p` from `BetaCharOn`, `BetaSqWild`, `BetaOpen` (`betaTame_of_odd`). -/
def BetaTame (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β (decomp p σ) = 1

/-- **Glue on G7 (`∂β = ε` with `ε` inflated from `Gal(L/ℚ)` and normalized; N5 L664-700).**
On `G_F` (`F ⊇ L_v`, so `decomp(G_F) ⊆ G_L`) the cochain `β` is a character. -/
def BetaCharOn (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, β (decomp p (σ * τ)) = β (decomp p σ) * β (decomp p τ)

/-- **Glue on G7 (`β² = χ`, `χ` a Dirichlet character of level `N = ∏ lev q`, `lev p = p` for
odd `p`, so `χ` is tame at odd `p`; N5 L677-683; g0-mod-field `G7Data`).** `β² = 1` on
`G_F ∩ P_p`. -/
def BetaSqWild (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β (decomp p σ) ^ 2 = 1

/-- **Glue (local constancy of `β`, g0-mod-field `G7Data`: `IsLocallyConstant β`, and the
continuity of `decomp`).** `β ∘ decomp` is trivial on `G_{F'}` for some finite Galois `F'`. -/
def BetaOpen (β : GQ → PadicAlgCl ℓ) : Prop :=
  ∃ F' : Fld p, IsFinGal F' ∧ ∀ σ ∈ fixSet F', β (decomp p σ) = 1

/-! ### The reduction -/

/-- **`TwistShape` from G8's output (proved).** With `ρ = β⁻¹ a Tm` and `a Tm = 1` on
`G_F ∩ P_p`, `ρ = β⁻¹` there, and `r` is the same scalar (`e` intertwines `ρ` with `r ⊕ r`). -/
theorem twistShape_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r) {F : Fld p}
    (hT : TateWildTrivial Tm a F) :
    TwistShape p r F (fun σ => (β (decomp p σ))⁻¹) := by
  obtain ⟨-, e, he, -⟩ := hG8
  intro σ hσ
  have hρ : GlueDescent.rho Tm a β (decomp p σ) = (β (decomp p σ))⁻¹ • 1 := by
    unfold GlueDescent.rho
    rw [mul_smul, hT σ hσ]
  exact mat_eq_scalar_of_intertwines he hρ

theorem twistUpper_of_betaUpper {β : GQ → PadicAlgCl ℓ} {F : Fld p} {U : ℝ}
    (h : BetaUpper β F U) : TwistUpper p F (fun σ => (β (decomp p σ))⁻¹) U := by
  intro t ht σ hσ
  simp only [h t ht σ hσ, inv_one]

theorem twistTame_of_betaTame {β : GQ → PadicAlgCl ℓ} {F : Fld p}
    (h : BetaTame β F) : TwistTame p F (fun σ => (β (decomp p σ))⁻¹) := by
  intro σ hσ
  simp only [h σ hσ, inv_one]

/-- **`BetaUpper` from `BetaTame` (proved):** `G_{ℚ_p}^t ⊆ P_p` for `t > 0` (`upperWild`). -/
theorem betaUpper_of_betaTame {β : GQ → PadicAlgCl ℓ} {F : Fld p} {U : ℝ} (hU : 0 ≤ U)
    (h : BetaTame β F) : BetaUpper β F U := by
  intro t ht σ hσ
  exact h σ ⟨hσ.2, upperWild t (lt_of_le_of_lt hU ht) hσ.1⟩

/-- **Corrected form of `LocalData p r`: the local data of G7 at `p` (GLUE on G4/G7 + R6 + D2 +
D3 + T16; N5 L813-851).** A Prop on G7's data `(Tm, a, β)` instead of on the bare `r`: at
`p ≤ D` a finite Galois `F ⊆ ℚ̄_p` with `e(F/ℚ_p) ≤ (DG₀)!` (Glazer: the Galois closure of
`L_v(A[3])`, `A[5]` if `p = 3`, of degree `≤ (DG₀)!`) on which `TateWildTrivial` and
`BetaUpper` (bound `U₀`) hold; at `p > D` a tame finite Galois `F` (the Galois closure of `L_v`,
`[L_v:ℚ_p] ≤ D < p`) with `TateWildTrivial` and `BetaTame`. -/
def G7LocalData {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      TateWildTrivial Tm a F ∧ BetaUpper β F U0) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      TateWildTrivial Tm a F ∧ BetaTame β F)

/-- **`LocalData p r` for G8's `r` (proved).** For `r` as in G8's output on
`ρ = GlueDescent.rho Tm a β`, `G7LocalData p Tm a β` gives `LocalData p r`, with the local
twist `σ ↦ β(σ)⁻¹`. -/
theorem localData_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (h : G7LocalData (p := p) Tm a β) : LocalData p r := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨F, hF, he, hT, hB⟩ := h.1 hp
    exact ⟨F, _, hF, he, twistShape_of_g8 hG8 hT, twistUpper_of_betaUpper hB⟩
  · obtain ⟨F, hF, he, hT, hB⟩ := h.2 hp
    exact ⟨F, _, hF, he, twistShape_of_g8 hG8 hT, twistTame_of_betaTame hB⟩

/-- **`G15RamG D u` from G8's outputs for `D.r5`, `D.r3` and G7's local data (proved).**
Composes `localData_of_g8` with g15-ram's `g15RamG_of_localData`. The G7/G8 data for `r₅` and
`r₃` may live on different models (`K₅`, `A₅`) and (`K₃`, `A₃`). -/
theorem g15RamG_of_g8 {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : ModData L A) (u : ℚ)
    {K₅ : Type} [Field K₅] [NumberField K₅] {A₅ : PkgI3.AbVar K₅}
    {Tm₅ : GQ → Module.End (PadicAlgCl 5) (G0Galois.Vb A₅ 5)} {a₅ β₅ : GQ → PadicAlgCl 5}
    (hG8₅ : G0Galois.G8Out A₅ 5 (GlueDescent.rho Tm₅ a₅ β₅) D.r5)
    {K₃ : Type} [Field K₃] [NumberField K₃] {A₃ : PkgI3.AbVar K₃}
    {Tm₃ : GQ → Module.End (PadicAlgCl 3) (G0Galois.Vb A₃ 3)} {a₃ β₃ : GQ → PadicAlgCl 3}
    (hG8₃ : G0Galois.G8Out A₃ 3 (GlueDescent.rho Tm₃ a₃ β₃) D.r3)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G7LocalData p ⟨hp⟩ 5 _ _ _ _ Tm₅ a₅ β₅)
    (h3 : G7LocalData (p := 5) Tm₃ a₃ β₃)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_localData D u (fun p hp hp5 => @localData_of_g8 p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ hG8₅
    (h5 p hp hp5)) (localData_of_g8 hG8₃ h3) h11₅ h11₃

/-! ### `BetaTame` at odd `p` (proved) -/

/-- A wild `σ` has `σ^{p^a}` fixing a given finite Galois `F'` for some `a`: the restriction
`s ∈ Gal(F'/ℚ_p)` has order `p^a m` with `p ∤ m`, and the wild `σ^{p^a}` has restriction of
order `m` prime to `p`, so it fixes `F'` (`fix_of_wild_pow`). -/
theorem exists_pow_fix_of_wild {σ : GQp p} (hσ : σ ∈ wildSet) {F' : Fld p} (hF' : IsFinGal F') :
    ∃ a : ℕ, σ ^ (p ^ a) ∈ fixSet F' := by
  haveI : FiniteDimensional ℚ_[p] F' := hF'.1
  haveI : Normal ℚ_[p] F' := hF'.2.to_normal
  set s := AlgEquiv.restrictNormalHom F' σ with hs
  have hm0 : 0 < orderOf s := orderOf_pos s
  obtain ⟨a, m, hpm, hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p
    (Fact.out : p.Prime).ne_one
  refine ⟨a, ?_⟩
  have hm0' : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hdec; omega
  intro x hx
  have hsm : AlgEquiv.restrictNormalHom F' ((σ ^ (p ^ a)) ^ m) = 1 := by
    rw [map_pow, map_pow, ← hs, ← pow_mul, ← hdec, pow_orderOf_eq_one]
  have hfix : ((σ ^ (p ^ a)) ^ m) x = x :=
    (AlgEquiv.restrictNormal_eq_one_iff F' _).mp hsm x hx
  exact fix_of_wild_pow (wildSet_pow hσ _) hm0' hpm hfix

theorem fixSet_pow {F : Fld p} {σ : GQp p} (hσ : σ ∈ fixSet F) (k : ℕ) : σ ^ k ∈ fixSet F := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx
    rw [pow_succ, AlgEquiv.mul_apply, hσ x hx, ih x hx]

/-- **`BetaTame` at odd `p` (proved).** If `β` is a character on `G_F`, `β² = 1` on
`G_F ∩ P_p`, and `β ∘ decomp` dies on an open `G_{F'}`, then `β = 1` on `G_F ∩ P_p` for odd `p`:
`β(σ)^{p^a} = β(σ^{p^a}) = 1` with `σ^{p^a} ∈ G_{F'}`, and `β(σ)² = 1`, `gcd(p^a, 2) = 1`. -/
theorem betaTame_of_odd (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {F : Fld p}
    (hmul : BetaCharOn β F) (hsq : BetaSqWild β F) (hopen : BetaOpen (p := p) β) :
    BetaTame β F := by
  obtain ⟨F', hF', h1⟩ := hopen
  intro σ hσ
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ.2 hF'
  have hpow : ∀ k : ℕ, β (decomp p (σ ^ (k + 1))) = β (decomp p σ) ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ σ (k + 1), hmul _ (fixSet_pow hσ.1 _) _ hσ.1, ih, ← pow_succ]
  have hpa : β (decomp p σ) ^ (p ^ a) = 1 := by
    have hpos : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
    obtain ⟨k, hk⟩ : ∃ k, p ^ a = k + 1 := ⟨p ^ a - 1, by omega⟩
    rw [hk, ← hpow k, ← hk]
    exact h1 _ ha
  have hcop : Nat.Coprime (p ^ a) 2 := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2
  have := pow_gcd_eq_one.mpr ⟨hpa, hsq σ hσ⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this

/-- `β(1) = 1` for a nonzero `β` that is a character on `G_F`. -/
theorem beta_one_of_charOn {β : GQ → PadicAlgCl ℓ} {F : Fld p} (hm : BetaCharOn β F)
    (h0 : β 1 ≠ 0) : β 1 = 1 := by
  have h := hm 1 (fun _ _ => rfl) 1 (fun _ _ => rfl)
  rw [mul_one, map_one] at h
  have h' : β 1 * β 1 = β 1 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ h0 h'

/-- **`BetaOpen` from local constancy (proved).** If `β : G_ℚ → ℚ̄_ℓ` is locally constant
(g0-mod-field's `G7Data` has `IsLocallyConstant β` for the `ℂ^×`-valued `β`; any transport of
the values preserves it) and `β(1) = 1`, then `β ∘ decomp` is trivial on `G_{F'}` for a finite
Galois `F'`: `decomp` is continuous (Mathlib's `Field.absoluteGaloisGroup.map`), the fibre over
`1` is an open neighbourhood of `1`, so it contains the fixer of a finite `E`
(`krullTopology_mem_nhds_one_iff`), and of its normal closure `F'`. -/
theorem betaOpen_of_isLocallyConstant {β : GQ → PadicAlgCl ℓ} (hβ : IsLocallyConstant β)
    (h1 : β 1 = 1) : BetaOpen (p := p) β := by
  set S : Set (GQp p) := {σ | β (decomp p σ) = 1} with hSdef
  have hcont : Continuous (decomp p) :=
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous
  have hS : S ∈ nhds (1 : GQp p) := by
    have hopen : IsOpen S := (hβ.comp_continuous hcont).isOpen_fiber 1
    refine hopen.mem_nhds ?_
    show β (decomp p 1) = 1
    rw [map_one, h1]
  obtain ⟨E, hEfin, hE⟩ := (krullTopology_mem_nhds_one_iff ℚ_[p] (Kbar p) S).mp hS
  set F' := IntermediateField.normalClosure ℚ_[p] E (Kbar p) with hF'
  haveI : FiniteDimensional ℚ_[p] F' := normalClosure.is_finiteDimensional ℚ_[p] E (Kbar p)
  haveI : Normal ℚ_[p] F' := normalClosure.normal ℚ_[p] E (Kbar p)
  refine ⟨F', ⟨inferInstance, IsGalois.mk⟩, fun σ hσ => ?_⟩
  have hσE : σ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hσ x (E.le_normalClosure hx)
  exact hE hσE

/-- **Corrected form at odd `p` (GLUE).** `G7LocalData` with the `β`-side replaced by
`BetaCharOn` and `BetaSqWild` on the same `F` (local constancy and `β(1) ≠ 0` are separate
hypotheses of `g7LocalData_of_odd`). -/
def G7LocalDataOdd {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      TateWildTrivial Tm a F ∧ BetaCharOn β F ∧ BetaSqWild β F) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      TateWildTrivial Tm a F ∧ BetaCharOn β F ∧ BetaSqWild β F)

/-- **`G7LocalData` at odd `p` (proved)** from `G7LocalDataOdd`, local constancy of `β` and
`β(1) ≠ 0` (`G0Galois.G7Out` has `∀ g, β g ≠ 0`). -/
theorem g7LocalData_of_odd (hp2 : p ≠ 2) {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a β : GQ → PadicAlgCl ℓ}
    (hβ : IsLocallyConstant β) (h0 : β 1 ≠ 0) (h : G7LocalDataOdd (p := p) Tm a β) :
    G7LocalData (p := p) Tm a β := by
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨F, hF, he, hT, hm, hs⟩ := h.1 hp
    have hopen := betaOpen_of_isLocallyConstant (p := p) hβ (beta_one_of_charOn hm h0)
    exact ⟨F, hF, he, hT, betaUpper_of_betaTame hU0 (betaTame_of_odd hp2 hm hs hopen)⟩
  · obtain ⟨F, hF, he, hT, hm, hs⟩ := h.2 hp
    have hopen := betaOpen_of_isLocallyConstant (p := p) hβ (beta_one_of_charOn hm h0)
    exact ⟨F, hF, he, hT, betaTame_of_odd hp2 hm hs hopen⟩

/-! ### `BetaSqWild` at odd `p` from `β² = χ` (proved)

Wild inertia fixes every root of unity of order `n` with `p² ∤ n` (`wild_fix_root`, norms only);
so the cyclotomic character mod `N`, and every Dirichlet character mod `N`, is trivial on
`decomp(P_p)` when `p² ∤ N` (`galChar_decomp_wild`); and `p² ∤ chiLevel T₋` for odd `p`
(`not_sq_dvd_chiLevel`). -/

theorem norm_eq_one_of_pow_eq_one {η : Kbar p} {n : ℕ} (hn : 0 < n) (h : η ^ n = 1) :
    ‖η‖ = 1 := by
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp this

theorem norm_sum_range_le_one {f : ℕ → Kbar p} (m : ℕ) (hf : ∀ k < m, ‖f k‖ ≤ 1) :
    ‖∑ k ∈ Finset.range m, f k‖ ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le (ih fun k hk => hf k (by omega)) (hf m (by omega)))

theorem norm_pow_sub_one_le {η : Kbar p} (h1 : ‖η‖ = 1) (i : ℕ) : ‖η ^ i - 1‖ ≤ ‖η - 1‖ := by
  have he : η ^ i - 1 = (∑ k ∈ Finset.range i, η ^ k) * (η - 1) := (geom_sum_mul η i).symm
  rw [he, norm_mul]
  have hs : ‖∑ k ∈ Finset.range i, η ^ k‖ ≤ 1 :=
    norm_sum_range_le_one i fun k _ => by rw [norm_pow, h1, one_pow]
  calc ‖∑ k ∈ Finset.range i, η ^ k‖ * ‖η - 1‖ ≤ 1 * ‖η - 1‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = ‖η - 1‖ := one_mul _

/-- A root of unity of order prime to `p` congruent to `1` is `1`. -/
theorem eq_one_of_pow_eq_one_of_norm_lt {η : Kbar p} {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m)
    (hη : η ^ m = 1) (hlt : ‖η - 1‖ < 1) : η = 1 := by
  by_contra hne
  have h1 : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one hm0 hη
  have hsub : η - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hgeom : ∑ k ∈ Finset.range m, η ^ k = 0 := by
    have := geom_sum_mul η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right hsub
  have hm : (m : Kbar p) = ∑ k ∈ Finset.range m, (1 - η ^ k) := by
    rw [Finset.sum_sub_distrib, hgeom, sub_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hlt' : ‖∑ k ∈ Finset.range m, (1 - η ^ k)‖ < 1 :=
    norm_sum_range_lt one_pos m fun k _ => by
      rw [norm_sub_rev]; exact lt_of_le_of_lt (norm_pow_sub_one_le h1 k) hlt
  rw [← hm, norm_natCast_kbar hpm] at hlt'
  exact lt_irrefl _ hlt'

/-- Wild inertia fixes roots of unity of order prime to `p`. -/
theorem wild_fix_prime_to_p {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} {m : ℕ} (hm0 : 0 < m)
    (hpm : ¬ p ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0.ne'] at hζ; exact zero_ne_one hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηm : η ^ m = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : ‖η - 1‖ < 1 := by
    have he : η - 1 = (σ ζ - ζ) * ζ⁻¹ := by rw [hη, sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, norm_mul, norm_inv]
    have hw := hσ ζ hζ0
    have hpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
    rw [mul_inv_lt_iff₀ hpos, one_mul]
    exact hw
  have := eq_one_of_pow_eq_one_of_norm_lt hm0 hpm hηm hlt
  rw [hη, mul_inv_eq_one₀ hζ0] at this
  exact this

/-- Wild inertia fixes the `p`-th roots of unity. -/
theorem wild_fix_p_root {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} (hζ : ζ ^ p = 1) :
    σ ζ = ζ := by
  have hp := (Fact.out : p.Prime)
  by_contra hne
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hp.ne_zero] at hζ; exact zero_ne_one hζ
  have hζ1 : ζ ≠ 1 := by rintro rfl; exact hne (map_one σ)
  have h1ζ : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hp.pos hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηp : η ^ p = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hη1 : η ≠ 1 := by
    intro h; rw [hη, mul_inv_eq_one₀ hζ0] at h; exact hne h
  have h1η : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one hp.pos hηp
  have hord : orderOf η = p := orderOf_eq_prime hηp hη1
  have hprim : IsPrimitiveRoot η p := by
    have := IsPrimitiveRoot.orderOf η
    rwa [hord] at this
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hζ
  have hx0 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  have hw := hσ (ζ - 1) hx0
  have he : σ (ζ - 1) - (ζ - 1) = ζ * (η - 1) := by
    rw [map_sub, map_one, hη]; field_simp; ring
  rw [he, norm_mul, h1ζ, one_mul, ← hi] at hw
  exact lt_irrefl _ (lt_of_lt_of_le hw (norm_pow_sub_one_le h1η i))

/-- **Wild inertia fixes `μ_n` for `p² ∤ n` (proved).** -/
theorem wild_fix_root {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} {n : ℕ} (hn0 : 0 < n)
    (hp2 : ¬ p ^ 2 ∣ n) (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hp := (Fact.out : p.Prime)
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hpm : ¬ p ∣ m := by
      rintro ⟨k, rfl⟩; exact hp2 ⟨k, by ring⟩
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at hn0
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [zero_pow hn0.ne'] at hζ; exact zero_ne_one hζ
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
    have hy : σ (ζ ^ p) = ζ ^ p :=
      wild_fix_prime_to_p hσ hm0 hpm (by rw [← pow_mul, hζ])
    have hz : σ (ζ ^ m) = ζ ^ m :=
      wild_fix_p_root hσ (by rw [← pow_mul, mul_comm, hζ])
    have hb : ((p.gcd m : ℕ) : ℤ) = p * p.gcdA m + m * p.gcdB m := Nat.gcd_eq_gcd_ab p m
    rw [hcop.gcd_eq_one, Nat.cast_one] at hb
    have hdec : ζ = (ζ ^ p) ^ (p.gcdA m) * (ζ ^ m) ^ (p.gcdB m) := by
      rw [← zpow_natCast, ← zpow_natCast (ζ) m, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← hb,
        zpow_one]
    rw [hdec, map_mul, map_zpow₀, map_zpow₀, hy, hz]
  · exact wild_fix_prime_to_p hσ hn0 hpn hζ

/-- The embedding `ℚ̄ → ℚ̄_p` that `decomp` uses. -/
def embP : PkgI4.Qbar →+* Kbar p :=
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom

/-- `embP ∘ decomp σ = σ ∘ embP` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
theorem decomp_spec (σ : GQp p) (x : PkgI4.Qbar) : embP (decomp p σ x) = σ (embP x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem decomp_fix_root {σ : GQp p} (hσ : σ ∈ wildSet) {x : PkgI4.Qbar} {n : ℕ} (hn0 : 0 < n)
    (hp2 : ¬ p ^ 2 ∣ n) (hx : x ^ n = 1) : decomp p σ x = x := by
  apply (embP (p := p)).injective
  rw [decomp_spec]
  exact wild_fix_root hσ hn0 hp2 (by rw [← map_pow, hx, map_one])

/-- **The cyclotomic character mod `N` is trivial on `decomp(P_p)` when `p² ∤ N` (proved).** -/
theorem cyc_decomp_wild {N : ℕ} [NeZero N] (hp2 : ¬ p ^ 2 ∣ N) {σ : GQp p}
    (hσ : σ ∈ wildSet) : GlueDescent.B2Q.cyc N (decomp p σ) = 1 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases hN1 : N = 1
  · subst hN1; exact Subsingleton.elim _ _
  haveI : Fact (1 < N) := ⟨by omega⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  apply Units.ext
  have hu := modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (GlueDescent.B2Q.toRingAut (decomp p σ)) (c := 1) (fun t ht => by
      rw [ZMod.val_one, pow_one]
      have htN : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ N = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N t).mp ht, Units.val_one]
      exact decomp_fix_root hσ hN0 hp2 htN)
  have hc : GlueDescent.B2Q.cyc N (decomp p σ) = modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
      (GlueDescent.B2Q.toRingAut (decomp p σ)) := rfl
  rw [hc, Units.val_one]
  exact hu.symm

/-- **Every Dirichlet character mod `N`, as a Galois character, is trivial on `decomp(P_p)`
when `p² ∤ N` (proved).** -/
theorem galChar_decomp_wild {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hp2 : ¬ p ^ 2 ∣ N) {σ : GQp p} (hσ : σ ∈ wildSet) :
    GlueDescent.B2Q.galChar χ (decomp p σ) = 1 := by
  change χ.toUnitHom (GlueDescent.B2Q.cyc N (decomp p σ)) = 1
  rw [cyc_decomp_wild hp2 hσ, map_one]

/-- **`p² ∤ chiLevel T₋` for odd `p` (proved)**, `T₋` a finite set of primes (`lev q = q` for odd
`q`, `lev 2 = 4`). -/
theorem not_sq_dvd_chiLevel (hp2 : p ≠ 2) {Tm : Finset ℕ} (hTm : ∀ q ∈ Tm, q.Prime) :
    ¬ p ^ 2 ∣ GlueDescent.chiLevel Tm := by
  have hp := (Fact.out : p.Prime)
  intro h
  have hpp : p ∣ GlueDescent.chiLevel Tm := (dvd_pow_self p two_ne_zero).trans h
  have hmem : p ∈ Tm := by
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpp
    have hqp := hTm q hq
    unfold GlueDescent.lev at hpq
    split_ifs at hpq with h2
    · subst h2
      have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hpq)
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this) hp2
    · rwa [(Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq]
  unfold GlueDescent.chiLevel at h
  rw [← Finset.mul_prod_erase Tm _ hmem] at h
  have hlev : GlueDescent.lev p = p := by unfold GlueDescent.lev; rw [if_neg hp2]
  rw [hlev, pow_two] at h
  have hdvd := Nat.dvd_of_mul_dvd_mul_left hp.pos h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  have hqp := hTm q (Finset.mem_of_mem_erase hq)
  have hqne := Finset.ne_of_mem_erase hq
  unfold GlueDescent.lev at hpq
  split_ifs at hpq with h2
  · subst h2
    have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hpq)
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this) hp2
  · exact hqne ((Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq).symm

/-- **`BetaSqWild` at odd `p` (proved)** from `β² = ι ∘ χ` on `G_F` (`χ` a Dirichlet character
mod `N = chiLevel T₋` for a set `T₋` of primes, as in g0-mod-field's `G7Data`; `ι` the transport
of values `ℂ^× → ℚ̄_ℓ^×`). -/
theorem betaSqWild_of_chi (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {F : Fld p} {Tm : Finset ℕ}
    (hTm : ∀ q ∈ Tm, q.Prime) [NeZero (GlueDescent.chiLevel Tm)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tm)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ σ ∈ fixSet F, β (decomp p σ) ^ 2 = (ι (GlueDescent.B2Q.galChar χ (decomp p σ)) :
      PadicAlgCl ℓ)) :
    BetaSqWild β F := by
  intro σ hσ
  rw [hsq σ hσ.1, galChar_decomp_wild χ (not_sq_dvd_chiLevel hp2 hTm) hσ.2, map_one,
    Units.val_one]

/-! ### `BetaCharOn` from `∂β = ε` (proved) -/

/-- `decomp(G_F) ⊆ G_L` when `F ⊇ embP(L)` (`L ⊆ ℚ̄`; `F ⊇ L_v` for the place `v` of `embP`). -/
theorem decomp_fix_of_le {L : IntermediateField ℚ PkgI4.Qbar} {F : Fld p}
    (hLF : ∀ x ∈ L, embP x ∈ F) {σ : GQp p} (hσ : σ ∈ fixSet F) :
    ∀ x ∈ L, decomp p σ x = x := by
  intro x hx
  apply (embP (p := p)).injective
  rw [decomp_spec]
  exact hσ _ (hLF x hx)

/-- **`BetaCharOn` from G7's `∂β = ε` (proved).** If `β g β h = ε(g,h) β(gh)` (a clause of
`G0Galois.G7Out`), `ε = 1` on `G_L × G_L` (`ε` is inflated from `Gal(L/ℚ)` and normalized,
g0-mod-field `DescentDatum`), and `F ⊇ embP(L)`, then `β` is a character on `G_F`. -/
theorem betaCharOn_of_cocycle {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) {L : IntermediateField ℚ PkgI4.Qbar}
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    {F : Fld p} (hLF : ∀ x ∈ L, embP x ∈ F) : BetaCharOn β F := by
  intro σ hσ τ hτ
  rw [hβ, hε _ _ (decomp_fix_of_le hLF hσ) (decomp_fix_of_le hLF hτ), one_mul, map_mul]

/-! ### Wild inertia fixes fields of degree `< p` (proved) -/

/-- **Wild inertia fixes every finite `E ⊆ ℚ̄_p` with `[E:ℚ_p] < p` (proved).** For `x ∈ E`
and wild `σ`, `σ^{p^a}` fixes the Galois closure of `ℚ_p(x)` (`exists_pow_fix_of_wild`), so the
`σ`-orbit of `x` has `p`-power size; its elements are distinct roots of the minimal polynomial
of `x`, of degree `≤ [E:ℚ_p] < p`; so the orbit is `{x}`. (This replaces "the Galois closure of
`L_v` is tame" at `p > D`.) -/
theorem wild_fix_small_degree {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E < p) : wildSet ⊆ fixSet E := by
  classical
  intro σ hσ x hx
  let F := FiniteGaloisIntermediateField.adjoin ℚ_[p] ({x} : Set (Kbar p))
  have hF : IsFinGal F.toIntermediateField := ⟨inferInstance, inferInstance⟩
  have hxF : x ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin ℚ_[p] {x} rfl
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ hF
  have hper : Function.IsPeriodicPt σ (p ^ a) x := by
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [← AlgEquiv.coe_pow]
    exact ha x hxF
  set k := Function.minimalPeriod σ x with hk
  have hkdvd : k ∣ p ^ a := hper.minimalPeriod_dvd
  have hkpos : 0 < k := hper.minimalPeriod_pos (pow_pos (Fact.out : p.Prime).pos a)
  -- the orbit lies in the roots of the minimal polynomial
  have hint : IsIntegral ℚ_[p] x := IsIntegral.of_finite ℚ_[p] (⟨x, hx⟩ : E) |>.map E.val
  set P := minpoly ℚ_[p] x with hP
  have hroot : ∀ i : ℕ, (σ^[i] x) ∈ P.aroots (Kbar p) := by
    intro i
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [← AlgEquiv.coe_pow, Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval,
      map_zero]
  have hcard : k ≤ P.natDegree := by
    have hinj : Set.InjOn (fun i => σ^[i] x) (Finset.range k : Set ℕ) := by
      intro i hi j hj hij
      have := Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := x)
      exact this (by simpa using hi) (by simpa using hj) hij
    have hsub : (Finset.range k).image (fun i => σ^[i] x) ⊆ (P.aroots (Kbar p)).toFinset := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact Multiset.mem_toFinset.mpr (hroot i)
    calc k = ((Finset.range k).image (fun i => σ^[i] x)).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ (P.aroots (Kbar p)).toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (P.aroots (Kbar p)) := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := by
          rw [Polynomial.aroots_def]
          exact (Polynomial.card_roots' _).trans Polynomial.natDegree_map_le
  have hdeg : P.natDegree ≤ Module.finrank ℚ_[p] E := by
    have h1 : (minpoly ℚ_[p] (⟨x, hx⟩ : E)).natDegree ≤ Module.finrank ℚ_[p] E :=
      minpoly.natDegree_le _
    rwa [IntermediateField.minpoly_eq] at h1
  have hkp : k < p := lt_of_le_of_lt (hcard.trans hdeg) hE
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hkdvd
  have hb0 : b = 0 := by
    by_contra hb0
    have : p ≤ p ^ b := Nat.le_self_pow hb0 p
    omega
  rw [hb0, pow_zero] at hb
  have h1 : Function.IsPeriodicPt σ 1 x := by
    rw [← hb]; exact Function.isPeriodicPt_minimalPeriod σ x
  exact h1

/-- **`LocalData` at `p > D` from a field of degree `< p` (proved).** If `E ⊆ ℚ̄_p` has
`[E:ℚ_p] < p` (Glazer: `E = L_v`, `[L_v:ℚ_p] ≤ D < p`) and `a·Tm` and `β` are trivial on
`G_E ∩ P_p`, then `LocalData p r` holds at `p > D` for G8's `r`. -/
theorem localData_large_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hp : (ZInQ.heightD : ℝ) < p) {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E < p) (hT : TateWildTrivial Tm a E) (hB : BetaTame β E) :
    LocalData p r := by
  rw [localData_large_iff r hp]
  intro σ hσ
  have hfix := wild_fix_small_degree hE hσ
  have h1 : ((r.restrictLocal p σ : GL (Fin 2) (PadicAlgCl ℓ)) :
      Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = Matrix.scalar (Fin 2) ((β (decomp p σ))⁻¹) :=
    twistShape_of_g8 hG8 hT σ ⟨hfix, hσ⟩
  rw [hB σ ⟨hfix, hσ⟩, inv_one, Matrix.scalar_apply, Matrix.diagonal_one] at h1
  exact Units.ext h1

/-! ### The Galois closure and `e ≤ [E:ℚ_p]!` (proved) -/

/-- `e(F/ℚ_p) ≤ [F:ℚ_p]` for finite Galois `F`. -/
theorem ramCard_zero_le_finrank {F : Fld p} (hF : IsFinGal F) :
    ramCard F 0 ≤ Module.finrank ℚ_[p] F := by
  haveI : FiniteDimensional ℚ_[p] F := hF.1
  haveI : IsGalois ℚ_[p] F := hF.2
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  rw [ramCard_zero_eq F hF, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_le_card_group _

/-- **A finite `E ⊆ ℚ̄_p` lies in a finite Galois `F` with `e(F/ℚ_p) ≤ n!` when
`[E:ℚ_p] ≤ n` (proved).** `F` = the splitting field in `ℚ̄_p` of the minimal polynomial `f` of a
primitive element of `E`; `Gal(F/ℚ_p)` acts faithfully on the `≤ deg f ≤ n` roots
(as in `GlueRepo.Numerics.splitting_degree_le`). -/
theorem exists_finGal_ramCard_le {E : Fld p} [FiniteDimensional ℚ_[p] E] {n : ℕ}
    (hE : Module.finrank ℚ_[p] E ≤ n) :
    ∃ F : Fld p, IsFinGal F ∧ E ≤ F ∧ ramCard F 0 ≤ n.factorial := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[p] E
  set a : Kbar p := (α : Kbar p) with ha
  have hint : IsIntegral ℚ_[p] a := (IsIntegral.of_finite ℚ_[p] α).map E.val
  set f := minpoly ℚ_[p] a with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero hint
  have hsplit : (f.map (algebraMap ℚ_[p] (Kbar p))).Splits := IsAlgClosed.splits _
  set F : Fld p := IntermediateField.adjoin ℚ_[p] (f.rootSet (Kbar p)) with hFdef
  haveI : Polynomial.IsSplittingField ℚ_[p] F f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  haveI : FiniteDimensional ℚ_[p] F := Polynomial.IsSplittingField.finiteDimensional F f
  have hsep : f.Separable := minpoly.irreducible hint |>.separable
  haveI : IsGalois ℚ_[p] F := IsGalois.of_separable_splitting_field hsep
  have hdeg : f.natDegree ≤ n := by
    have h1 : (minpoly ℚ_[p] α).natDegree ≤ Module.finrank ℚ_[p] E := minpoly.natDegree_le _
    rw [IntermediateField.minpoly_eq] at h1
    exact h1.trans hE
  have hfin : Module.finrank ℚ_[p] F ≤ n.factorial := by
    rw [(Polynomial.IsSplittingField.algEquiv F f).toLinearEquiv.finrank_eq,
      ← Polynomial.Gal.card_of_separable hsep]
    have : Fact ((f.map (algebraMap ℚ_[p] f.SplittingField)).Splits) :=
      ⟨Polynomial.SplittingField.splits f⟩
    calc Nat.card f.Gal ≤ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
          Nat.card_le_card_of_injective _ (Polynomial.Gal.galActionHom_injective f _)
      _ = (Nat.card (f.rootSet f.SplittingField)).factorial := Nat.card_perm
      _ ≤ n.factorial := by
          apply Nat.factorial_le
          rw [Nat.card_coe_set_eq]
          exact (Polynomial.ncard_rootSet_le f _).trans hdeg
  have hEF : E ≤ F := by
    intro y hy
    have h1 : (⟨y, hy⟩ : E) ∈ IntermediateField.adjoin ℚ_[p] {α} := by rw [hα]; trivial
    have h2 : y ∈ (IntermediateField.adjoin ℚ_[p] {α}).map E.val :=
      ⟨⟨y, hy⟩, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    have hroot : a ∈ f.rootSet (Kbar p) := by
      rw [Polynomial.mem_rootSet]
      exact ⟨hf0, minpoly.aeval ℚ_[p] a⟩
    have hle : IntermediateField.adjoin ℚ_[p] {E.val α} ≤ F :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.subset_adjoin _ _ hroot)
    exact hle h2
  have hFG : IsFinGal F := ⟨inferInstance, inferInstance⟩
  exact ⟨F, hFG, hEF, (ramCard_zero_le_finrank hFG).trans hfin⟩

theorem tateWildTrivial_mono {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ} {E F : Fld p} (hEF : E ≤ F)
    (h : TateWildTrivial Tm a E) : TateWildTrivial Tm a F :=
  fun σ hσ => h σ ⟨fun x hx => hσ.1 x (hEF hx), hσ.2⟩

theorem betaUpper_mono {β : GQ → PadicAlgCl ℓ} {E F : Fld p} {U : ℝ} (hEF : E ≤ F)
    (h : BetaUpper β E U) : BetaUpper β F U :=
  fun t ht σ hσ => h t ht σ ⟨hσ.1, fun x hx => hσ.2 x (hEF hx)⟩

/-- **`LocalData` at `p ≤ D` from a field of degree `≤ DG₀` (proved).** If `E ⊆ ℚ̄_p` has
`[E:ℚ_p] ≤ DG₀` (Glazer: `E = L_v(A[3])`, `A[5]` if `p = 3`) and `TateWildTrivial`, `BetaUpper`
hold on `E`, then `LocalData p r` holds at `p ≤ D` for G8's `r` (`F` = the Galois closure,
`exists_finGal_ramCard_le`). -/
theorem localData_small_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0)
    (hT : TateWildTrivial Tm a E) (hB : BetaUpper β E U0) : SmallPrimeData p r := by
  obtain ⟨F, hF, hEF, he⟩ := exists_finGal_ramCard_le hE
  exact ⟨F, _, hF, he, twistShape_of_g8 hG8 (tateWildTrivial_mono hEF hT),
    twistUpper_of_betaUpper (betaUpper_mono hEF hB)⟩

/-! ### Assembly at odd `p` (proved) -/

/-- **`LocalData p r` at odd `p` for G8's `r`, from G7's clauses and one named glue Prop
(proved).** Hypotheses:
* G8's output for `ρ = GlueDescent.rho Tm a β` (`G0Galois.G8Out`, proved by g0-mod-galois `g8`);
* clauses of G7 (`G0Galois.G7Out`: `∂β = ε`, `β ≠ 0`; g0-mod-field `G7Data`/`DescentDatum`,
  with the values moved to `ℚ̄_ℓ` by `ι`: `β` locally constant, `β² = ι ∘ χ` for a Dirichlet
  character `χ` mod `chiLevel T₋`, `T₋` a set of primes, and `ε = 1` on `G_L × G_L`, as `ε` is
  inflated from `Gal(L/ℚ)` with `ε(1,1) = 1`);
* at `p ≤ D`: a finite `E ⊆ ℚ̄_p` containing `embP(L)` with `[E:ℚ_p] ≤ DG₀` (Glazer:
  `E = L_v(A[3])`, `A[5]` if `p = 3`) and `TateWildTrivial` on `E`;
* at `p > D`: a finite `E ⊇ embP(L)` with `[E:ℚ_p] < p` (Glazer: `E = L_v`, degree `≤ D`) and
  `TateWildTrivial` on `E`.
The `β`-side (`BetaUpper`, `BetaTame`) is fully proved from these clauses. -/
theorem localData_of_g7_odd (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hβε : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (hβlc : IsLocallyConstant β)
    {Tmin : Finset ℕ} (hTm : ∀ q ∈ Tmin, q.Prime) [NeZero (GlueDescent.chiLevel Tmin)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ))
    {L : IntermediateField ℚ PkgI4.Qbar}
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    (hsmall : (p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0 ∧
      TateWildTrivial Tm a E)
    (hlarge : (ZInQ.heightD : ℝ) < p → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E < p ∧ TateWildTrivial Tm a E) :
    LocalData p r := by
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  have htame : ∀ E : Fld p, (∀ x ∈ L, embP x ∈ E) → BetaTame β E := by
    intro E hLE
    have hm := betaCharOn_of_cocycle (p := p) hβε hε hLE
    have hs := betaSqWild_of_chi hp2 (F := E) hTm χ ι (fun σ _ => hsq _)
    have ho := betaOpen_of_isLocallyConstant (p := p) hβlc (beta_one_of_charOn hm (hβ0 1))
    exact betaTame_of_odd hp2 hm hs ho
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨E, hEfd, hLE, hdeg, hT⟩ := hsmall hp
    exact localData_small_of_g8 hG8 hdeg hT (betaUpper_of_betaTame hU0 (htame E hLE))
  · obtain ⟨E, hEfd, hLE, hdeg, hT⟩ := hlarge hp
    exact (localData_large_of_g8 hG8 hp hdeg hT (htame E hLE)).2 hp

/-! ### `p > D` from `[L:ℚ] ≤ D` (proved) -/

/-- **`[ℚ_p · embP(L) : ℚ_p] ≤ [L:ℚ]` (proved).** For a number field `L ⊆ ℚ̄`, the field
`E = ℚ_p(embP α)` (`α` a primitive element of `L`) contains `embP(L)` and has degree
`≤ deg minpoly_ℚ α = [L:ℚ]` (the minimal polynomial over `ℚ_p` divides the image of the one
over `ℚ`). This is `[L_v:ℚ_p] ≤ [L:ℚ]`. -/
theorem exists_local_field_le (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ (∀ x ∈ L, embP x ∈ E) ∧
      Module.finrank ℚ_[p] E ≤ Module.finrank ℚ L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  set αQ : PkgI4.Qbar := (α : PkgI4.Qbar) with hαQ
  have hintQ : IsIntegral ℚ αQ := (IsIntegral.of_finite ℚ α).map L.val
  set g := minpoly ℚ αQ with hg
  set a : Kbar p := embP αQ with ha
  have hroot : Polynomial.aeval a (g.map (algebraMap ℚ ℚ_[p])) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, ha]
    have : Polynomial.aeval (embP (p := p) αQ) g = embP (Polynomial.aeval αQ g) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext_rat _ _
    rw [this, minpoly.aeval, map_zero]
  have hg0 : g.map (algebraMap ℚ ℚ_[p]) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℚ_[p]).injective).mpr (minpoly.ne_zero hintQ)
  have hint : IsIntegral ℚ_[p] a :=
    ⟨_, (minpoly.monic hintQ).map _, by
      rw [← Polynomial.aeval_def]; exact hroot⟩
  set E : Fld p := IntermediateField.adjoin ℚ_[p] {a} with hE
  haveI : FiniteDimensional ℚ_[p] E := IntermediateField.adjoin.finiteDimensional hint
  refine ⟨E, inferInstance, ?_, ?_⟩
  · intro x hx
    have h1 : (⟨x, hx⟩ : L) ∈ IntermediateField.adjoin ℚ {α} := by rw [hα]; trivial
    have h2 : x ∈ (IntermediateField.adjoin ℚ {α}).map L.val := ⟨⟨x, hx⟩, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    have h3 : embP (p := p) x ∈
        (IntermediateField.adjoin ℚ {L.val α}).map (embP (p := p)).toRatAlgHom :=
      ⟨x, h2, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h3
    have hle : IntermediateField.adjoin ℚ {(embP (p := p)).toRatAlgHom (L.val α)} ≤
        E.restrictScalars ℚ := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.mem_adjoin_simple_self ℚ_[p] a
    exact hle h3
  · rw [IntermediateField.adjoin.finrank hint]
    have hdvd : minpoly ℚ_[p] a ∣ g.map (algebraMap ℚ ℚ_[p]) := minpoly.dvd ℚ_[p] a hroot
    have h1 := Polynomial.natDegree_le_of_dvd hdvd hg0
    rw [Polynomial.natDegree_map] at h1
    have h2 : g.natDegree = Module.finrank ℚ L := by
      have h3 : (minpoly ℚ α).natDegree ≤ Module.finrank ℚ L := minpoly.natDegree_le _
      have h4 : Module.finrank ℚ L ≤ (minpoly ℚ α).natDegree := by
        have := IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ α)
        rw [hα, IntermediateField.finrank_top'] at this
        omega
      rw [hg, ← IntermediateField.minpoly_eq]
      omega
    omega

/-- **Glue on G3 + Néron–Ogg–Shafarevich + the descent datum on `G_L` (N5 L848-851).** At
`p > D`: on wild inertia elements whose image in `G_ℚ` lies in `G_L`, `a_σ μ_σ ∘ σ` is the
identity (it is the Tate action of `A/L`, which has good reduction at `v ∤ 3`, so inertia acts
trivially, `PkgI2.inertiaTrivial_of_goodReduction`). Only claimed for `p ≠ ℓ`. -/
def TateWildTrivialL {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ σ ∈ wildSet, (∀ x ∈ L, decomp p σ x = x) → a (decomp p σ) • Tm (decomp p σ) = 1

theorem tateWildTrivial_of_L {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (h : TateWildTrivialL (p := p) Tm a L) {E : Fld p}
    (hLE : ∀ x ∈ L, embP x ∈ E) : TateWildTrivial Tm a E :=
  fun σ hσ => h σ hσ.2 (decomp_fix_of_le hLE hσ.1)

/-- **`LocalData p r` at `p > D` for G8's `r` (proved)** from G7's clauses (as in
`localData_of_g7_odd`), `[L:ℚ] ≤ D` (G4's output `G4Out`), and `TateWildTrivialL`. -/
theorem localData_of_g7_large {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hβε : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (hβlc : IsLocallyConstant β)
    {Tmin : Finset ℕ} (hTm : ∀ q ∈ Tmin, q.Prime) [NeZero (GlueDescent.chiLevel Tmin)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ))
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L]
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (hp : (ZInQ.heightD : ℝ) < p)
    (hT : TateWildTrivialL (p := p) Tm a L) :
    LocalData p r := by
  have hpD : ZInQ.heightD < p := by exact_mod_cast hp
  have hp2 : p ≠ 2 := by
    have := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
    omega
  obtain ⟨E, hEfd, hLE, hdeg⟩ := exists_local_field_le (p := p) L
  refine localData_of_g7_odd hp2 hG8 hβε hβ0 hβlc hTm χ ι hsq hε
    (fun hle => absurd hp (not_lt.mpr hle)) (fun _ => ⟨E, hEfd, hLE, ?_, ?_⟩)
  · omega
  · exact tateWildTrivial_of_L hT hLE

/-! ### Final form: the glue on `L_v = ℚ_p · embP(L)` and the assembly for every `p` -/

/-- `L_v = ℚ_p · embP(L) ⊆ ℚ̄_p`, the completion of `L ⊆ ℚ̄` at the place of `embP`. -/
def Lv (L : IntermediateField ℚ PkgI4.Qbar) : Fld p :=
  IntermediateField.adjoin ℚ_[p] (embP '' (L : Set PkgI4.Qbar))

theorem embP_mem_Lv {L : IntermediateField ℚ PkgI4.Qbar} {x : PkgI4.Qbar} (hx : x ∈ L) :
    embP x ∈ Lv (p := p) L :=
  IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩

theorem Lv_le {L : IntermediateField ℚ PkgI4.Qbar} {E : Fld p} (h : ∀ x ∈ L, embP x ∈ E) :
    Lv (p := p) L ≤ E :=
  IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

/-- `[L_v:ℚ_p] ≤ [L:ℚ]` (proved, from `exists_local_field_le`). -/
theorem Lv_fin (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ_[p] (Lv (p := p) L) ∧
      Module.finrank ℚ_[p] (Lv (p := p) L) ≤ Module.finrank ℚ L := by
  obtain ⟨E, hEfd, hLE, hdeg⟩ := exists_local_field_le (p := p) L
  have hle := Lv_le (p := p) hLE
  have hfd : FiniteDimensional ℚ_[p] (Lv (p := p) L) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  exact ⟨hfd, (IntermediateField.finrank_le_of_le_right hle).trans hdeg⟩

/-- **The clauses of G4/G7 used here (GLUE: transport between g0-mod-field's `ℂ^×`-valued data
and g0-mod-galois's `ℚ̄_ℓ`-valued `G7Out`).** `L ⊆ ℚ̄` (G4's Hom field) is finite with
`[L:ℚ] ≤ D` (`G4Out`); `∂β = ε` and `β ≠ 0` (`G0Galois.G7Out`); `β` locally constant and
`β² = ι ∘ χ` for a Dirichlet character `χ` mod `chiLevel T₋`, `T₋` a set of primes (`G7Data`, with
`ι : ℂ^× → ℚ̄_ℓ^×` the transport of values); `ε = 1` on `G_L × G_L` (`DescentDatum`: `ε` inflated
from `Gal(L/ℚ)` with `ε(1,1) = 1`). Note: g0-mod-field's interface `G7Data` (and so `AfterG7`)
does not carry `[L:ℚ] ≤ D`; `G4Out` does. -/
def G7Clauses (β : GQ → PadicAlgCl ℓ) (ε : GQ → GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  FiniteDimensional ℚ L ∧ Module.finrank ℚ L ≤ ZInQ.heightD ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧ IsLocallyConstant β ∧
  (∃ (Tmin : Finset ℕ) (_ : ∀ q ∈ Tmin, q.Prime) (_ : NeZero (GlueDescent.chiLevel Tmin))
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ),
    ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ)) ∧
  (∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)

/-- **Glue on G4/G7 + R6 + D2 + the torsion field (N5 L813-818).** There is a finite
`E ⊇ L_v` with `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` on which `a·Tm` is trivial on wild inertia. Glazer:
`E = L_v(A[3])` (`A[5]` if `p = 3`), `[E:L_v] ≤ |GL₄(𝔽₅)| = G₀ = 116064000000`
(`A[m] ≅ (ℤ/m)⁴`, `PkgI2.TorsionStructure`); `A` is semistable over `E` (R6,
`PkgI2.RaynaudCriterion`), so wild inertia acts trivially on `V_ℓ(A)` (D2,
`PkgI2.D2_fixed_of_raynaud`), and `a_σ μ_σ = 1` on `G_L` (`DescentDatum`). Only for `p ≠ ℓ`. -/
def TorsionFieldWild {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    TateWildTrivial Tm a E

/-- **The local glue at `p`.** `TorsionFieldWild` at `p ≤ D`, `TateWildTrivialL` at `p > D`, and
at `p = 2` the bound for `β` on `L_v` (`BetaUpper`, glue on T16 + D3 + Herbrand's `ψ ≥ id`,
N5 L826-844; `β|_{G_{L_v}}` is a character with `β⁴ = 1` on units since the 2-part of `χ` has
conductor `4`). -/
def LocalGlue {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → TorsionFieldWild (p := p) Tm a L) ∧
  ((ZInQ.heightD : ℝ) < p → TateWildTrivialL (p := p) Tm a L) ∧
  (p = 2 → BetaUpper β (Lv (p := p) L) U0)

/-- **`LocalData p r` for G8's `r`, every prime `p` (proved)** from G8's output, the G4/G7
clauses (`G7Clauses`) and the local glue (`LocalGlue`). -/
theorem localData_of_g7 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2} {L : IntermediateField ℚ PkgI4.Qbar}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r) (hC : G7Clauses β ε L)
    (hG : LocalGlue (p := p) Tm a β L) : LocalData p r := by
  obtain ⟨hLfd, hLD, hβε, hβ0, hβlc, ⟨Tmin, hTm, hNZ, χ, ι, hsq⟩, hε⟩ := hC
  obtain ⟨hLvfd, hLvdeg⟩ := Lv_fin (p := p) L
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  -- the field of `TorsionFieldWild` has degree `≤ D G₀`
  have hsmall : (p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0 ∧
      TateWildTrivial Tm a E := by
    intro hp
    obtain ⟨E, hEfd, hLvE, hdeg, hT⟩ := hG.1 hp
    refine ⟨E, hEfd, fun x hx => hLvE (embP_mem_Lv hx), ?_, hT⟩
    calc Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) := hdeg
      _ ≤ ZInQ.heightG0 * ZInQ.heightD := Nat.mul_le_mul_left _ (hLvdeg.trans hLD)
      _ = ZInQ.heightD * ZInQ.heightG0 := Nat.mul_comm _ _
  by_cases hp2 : p = 2
  · subst hp2
    have hle : ((2 : ℕ) : ℝ) ≤ (ZInQ.heightD : ℝ) := by exact_mod_cast (by omega : 2 ≤ ZInQ.heightD)
    refine ⟨fun hp => ?_, fun hp => absurd hp (not_lt.mpr hle)⟩
    obtain ⟨E, hEfd, hLvE, hdeg, hT⟩ := hG.1 hp
    obtain ⟨E', hE'fd, hLE', hdeg', hT'⟩ := hsmall hp
    exact localData_small_of_g8 hG8 hdeg' hT' (betaUpper_mono (Lv_le hLE') (hG.2.2 rfl))
  · refine localData_of_g7_odd hp2 hG8 hβε hβ0 hβlc hTm χ ι hsq hε hsmall (fun hp => ?_)
    have hpD : ZInQ.heightD < p := by exact_mod_cast hp
    exact ⟨Lv (p := p) L, hLvfd, fun x hx => embP_mem_Lv hx, by omega,
      tateWildTrivial_of_L (hG.2.1 hp) (fun x hx => embP_mem_Lv hx)⟩

/-- **`G15RamG D u` from G8's outputs, the G4/G7 clauses and the local glue (proved).**
The G7/G8 data for `r₅` and `r₃` (models `A₅/K₅`, `A₃/K₃`, Hom fields `L₅`, `L₃`). -/
theorem g15RamG_of_g7 {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : ModData L A) (u : ℚ)
    {K₅ : Type} [Field K₅] [NumberField K₅] {A₅ : PkgI3.AbVar K₅}
    {Tm₅ : GQ → Module.End (PadicAlgCl 5) (G0Galois.Vb A₅ 5)} {a₅ β₅ : GQ → PadicAlgCl 5}
    {ε₅ : GQ → GQ → PadicAlgCl 5} {L₅ : IntermediateField ℚ PkgI4.Qbar}
    (hG8₅ : G0Galois.G8Out A₅ 5 (GlueDescent.rho Tm₅ a₅ β₅) D.r5) (hC₅ : G7Clauses β₅ ε₅ L₅)
    (hG₅ : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm₅ a₅ β₅ L₅)
    {K₃ : Type} [Field K₃] [NumberField K₃] {A₃ : PkgI3.AbVar K₃}
    {Tm₃ : GQ → Module.End (PadicAlgCl 3) (G0Galois.Vb A₃ 3)} {a₃ β₃ : GQ → PadicAlgCl 3}
    {ε₃ : GQ → GQ → PadicAlgCl 3} {L₃ : IntermediateField ℚ PkgI4.Qbar}
    (hG8₃ : G0Galois.G8Out A₃ 3 (GlueDescent.rho Tm₃ a₃ β₃) D.r3) (hC₃ : G7Clauses β₃ ε₃ L₃)
    (hG₃ : LocalGlue (p := 5) Tm₃ a₃ β₃ L₃)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_localData D u
    (fun p hp hp5 => @localData_of_g7 p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ _ _ hG8₅ hC₅ (hG₅ p hp hp5))
    (localData_of_g7 hG8₃ hC₃ hG₃) h11₅ h11₃

/-! ### Non-vacuity (proved) -/

/-- **`G7LocalData` is satisfiable (proved):** it holds for trivial data (`Tm = 1`, `a = 1`,
`β = 1`, `F = ℚ_p`), so it is not contradictory. -/
theorem g7LocalData_triv {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V] :
    G7LocalData (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V)) (fun _ => 1)
      (fun _ => 1) := by
  have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
  have he : ramCard (⊥ : Fld p) 0 = 1 := by
    have h1 := one_le_ramCard hF 0
    have h2 := ramCard_zero_le_finrank hF
    rw [IntermediateField.finrank_bot] at h2
    omega
  have hT : TateWildTrivial (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V))
      (fun _ => (1 : PadicAlgCl ℓ)) ⊥ := fun _ _ => one_smul _ _
  refine ⟨fun _ => ⟨⊥, hF, ?_, hT, fun _ _ _ _ => rfl⟩,
    fun _ => ⟨⊥, hF, ?_, hT, fun _ _ => rfl⟩⟩
  · rw [he]; exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [he]; exact (Nat.Prime.one_lt Fact.out).ne' ∘ Nat.dvd_one.mp

/-- **`G7Clauses` and `LocalGlue` are satisfiable (proved):** both hold for trivial data
(`β = 1`, `ε = 1`, `L = ℚ`, `Tm = 1`, `a = 1`, `χ = 1`, `ι = 1`). -/
theorem g7Clauses_triv : G7Clauses (ℓ := ℓ) (fun _ => 1) (fun _ _ => 1) ⊥ := by
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  refine ⟨inferInstance, ?_, fun _ _ => by simp, fun _ => one_ne_zero,
    IsLocallyConstant.const _, ⟨∅, fun q hq => absurd hq (Finset.notMem_empty q),
      ⟨by simp [GlueDescent.chiLevel]⟩, 1, 1, fun _ => by simp⟩, fun _ _ _ _ => rfl⟩
  rw [IntermediateField.finrank_bot]
  omega

theorem localGlue_triv {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    LocalGlue (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V)) (fun _ => 1) (fun _ => 1) L := by
  obtain ⟨hfd, -⟩ := Lv_fin (p := p) L
  have hG0 : 1 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
  refine ⟨fun _ => ⟨Lv (p := p) L, hfd, le_rfl, ?_, fun _ _ => one_smul _ _⟩,
    fun _ _ _ _ => one_smul _ _, fun _ _ _ _ _ => rfl⟩
  exact Nat.le_mul_of_pos_left _ hG0

end LocalDataSec

end G15Ram

end

/-! ## §5 (local-data). The tail of `ModularConstituent` with G15 fed by G7/G8 (proved) -/

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves C9Rhof
open CategoryTheory AlgebraicGeometry

/-- **G8's data for a representation `r` at coefficient prime `ℓ`, with the G4/G7 clauses and
the local glue at the primes `p ∈ P`** (`G15Ram.G7Clauses`, `G15Ram.LocalGlue`). -/
def G8LocalPack (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (a β : GQ → PadicAlgCl ℓ)
    (ε : GQ → GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ Qbar),
    G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧ G15Ram.G7Clauses β ε L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p → @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β L

/-- **G13-G16 with G15 fed by G7/G8 (GLUE, proved).** As `modularConstituent_tail_G`, with
`G15RamG D u` replaced by: `D.r5` and `D.r3` come from G8 on G7's data (`G8LocalPack`, with the
local glue at `p ≠ 5`, resp. `p = 5`) and G11's output. -/
theorem modularConstituent_tail_L (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧
      G8LocalPack 5 D.r5 (fun p => p ≠ 5) ∧ G8LocalPack 3 D.r3 (fun p => p = 5) ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5 ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩,
    ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩, h11a, h11b⟩ := h
  exact modularConstituent_tail_G lv hJac hX hSw hL8 hAd A u
    ⟨D, h12, hc, G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃
      (hG₃ 5 (by norm_num) rfl) h11a h11b⟩

end G0ModNewform

#print axioms G0ModNewform.modularConstituent_tail_L


/-! ## §5' (local-glue). Verbatim copy from scratch/g0-mod-galois/part_galois.lean lines 40-58 -/

noncomputable section

namespace G0Galois


/-- The embedding `ℚ̄ → K̄` that `Field.absoluteGaloisGroup.map` chooses (`IsAlgClosed.lift`). -/
def qEmbRing (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →+* AlgebraicClosure K :=
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom

/-- `qEmbRing` as a `ℚ`-algebra map (the `i` of g0-mod-newform's `ModData`). -/
def qEmb (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K :=
  (qEmbRing K).toRatAlgHom

/-- `qEmb K ∘ resQ K τ = τ ∘ qEmb K` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
lemma resQ_spec (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure ℚ) :
    qEmbRing K (resQ K τ x) = τ (qEmbRing K x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

end G0Galois

end

/-! ## §6 (local-glue). `LocalGlue p Tm a β L` on G7's data

`LocalGlue p Tm a β L` (§4 above, copied verbatim from scratch/local-data) is a predicate on
arbitrary operators `Tm`, scalars `a`, `β` and a field `L`. Here:

* `not_localGlue_zero` (proved): it fails for `Tm = 0` at every `p > D`, so it is not a closed
  theorem; it is a claim about the data that G7 builds.
* **Main result** `localGlue_of_g7` (proved): for G7's data (`G0Galois.G7Out`, with the clauses
  `G7Clauses`), `LocalGlue p Tm a β L` follows from three named Props about the abelian surface
  `A/K` and the kernel field, with no `Tm` or `a` left:
  - `KerWild K β L`: wild inertia elements of `G_L` killed by `β` lie in `G_K` (G7Data's kernel
    field clause `G_{L'} = G_L ∩ ker β`, transported);
  - `TateWildK p A ℓ` (`p ≥ 7`): wild inertia at `p` in `G_K` acts trivially on `V_ℓ(A)`;
  - `TateWildKE p A ℓ β L` (`p ≤ 5`): the same on `G_E` for a field `E ⊇ L_v` of degree
    `≤ G₀[L_v:ℚ_p]`, on which also `β` kills wild inertia;
  and `BetaUpper` at `p = 2` (unchanged).
* `tate_eq_one_of_torsFix` (proved): `σ` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` if it fixes every
  `ℓⁿ`-torsion point; so `TateWildK`, `TateWildKE` reduce to statements on torsion points
  (`TorsFixWild`, `TorsFixWildE`), the form in which Raynaud's criterion (R6) and D2 are stated.
-/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GaloisRep GQ decomp)
open LadicCond G0ModNewform
open CategoryTheory MonObj

section LocalGlueSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### `LocalGlue` is not a closed statement -/

/-- **`LocalGlue` fails for `Tm = 0` at every `p > D` (proved).** `σ = 1` is wild and fixes
`L`, and `1 • 0 ≠ 1` on the nonzero space `ℚ̄_ℓ`. -/
theorem not_localGlue_zero (hp : (ZInQ.heightD : ℝ) < p) (L : IntermediateField ℚ PkgI4.Qbar) :
    ¬ LocalGlue (p := p) (fun _ => (0 : Module.End (PadicAlgCl ℓ) (PadicAlgCl ℓ))) (fun _ => 1)
      (fun _ => 1) L := by
  intro h
  have h1 := h.2.1 hp 1 one_mem_wildSet (fun x _ => by rw [map_one]; rfl)
  have h2 := LinearMap.congr_fun h1 1
  simp at h2

/-! ### Fixing `L` and fixing `L_v` -/

/-- If `decomp σ` fixes `L`, then `σ` fixes `L_v = ℚ_p · embP(L)` (proved). -/
theorem fixSet_Lv_of_fix {L : IntermediateField ℚ PkgI4.Qbar} {σ : GQp p}
    (h : ∀ x ∈ L, decomp p σ x = x) : σ ∈ fixSet (Lv (p := p) L) := by
  have hle : Lv (p := p) L ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    apply Lv_le
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hσ : σ ∈ MulAction.stabilizer (GQp p) (embP (p := p) x) := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, ← decomp_spec, h x hx]
    have := (Subgroup.zpowers_le.mpr hσ) hf
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  intro y hy
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hy) σ (Subgroup.mem_zpowers σ)

/-- `σ` fixes `L_v` iff `decomp σ` fixes `L` (proved). -/
theorem fixSet_Lv_iff {L : IntermediateField ℚ PkgI4.Qbar} {σ : GQp p} :
    σ ∈ fixSet (Lv (p := p) L) ↔ ∀ x ∈ L, decomp p σ x = x :=
  ⟨fun h => decomp_fix_of_le (fun _ hx => embP_mem_Lv hx) h, fixSet_Lv_of_fix⟩

/-! ### `β` on wild inertia of `G_L` at odd `p` -/

/-- **`β` kills wild inertia of `G_L` at odd `p` (proved)** from G7's clauses: on `G_{L_v}`,
`β` is a character (`∂β = ε`, `ε = 1` on `G_L²`) with `β² = χ` tame (`χ` mod `chiLevel T₋`) and
open kernel (local constancy), so `betaTame_of_odd` applies with `F = L_v`. -/
theorem beta_wild_of_clauses (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L) {σ : GQp p} (hσ : σ ∈ wildSet)
    (hfix : ∀ x ∈ L, decomp p σ x = x) : β (decomp p σ) = 1 := by
  obtain ⟨-, -, hβε, hβ0, hβlc, ⟨Tmin, hTm, hNZ, χ, ιc, hsq⟩, hε⟩ := hC
  have hm : BetaCharOn β (Lv (p := p) L) :=
    betaCharOn_of_cocycle hβε hε (fun _ hx => embP_mem_Lv hx)
  have hs : BetaSqWild β (Lv (p := p) L) :=
    betaSqWild_of_chi hp2 hTm χ ιc (fun _ _ => hsq _)
  have hopen := betaOpen_of_isLocallyConstant (p := p) hβlc (beta_one_of_charOn hm (hβ0 1))
  exact betaTame_of_odd hp2 hm hs hopen σ ⟨fixSet_Lv_of_fix hfix, hσ⟩

/-! ### The smaller named Props -/

/-- **Glue: G7Data's kernel field clause, transported (N5 L702-716; g0-mod-field `G7Data`,
clause `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`).** Every `g ∈ G_L` with `β(g) = 1` lies in `G_K`
(the image of `resQ K`), for the model field `K = L'` of `G0Galois.G7Out`. Notes: (i) `resQ K`
is taken along the embedding `K ↪ ℚ̄` that Mathlib's `Field.absoluteGaloisGroup.map` chooses;
`L'` is Galois over `ℚ`, so `G_{L'}` is normal and does not depend on that embedding; (ii) the
`ℚ̄_ℓ`-valued `β` here is `ι ∘ β_ℂ` (F5 of local-data), so `β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1` needs `ι`
injective on the roots of unity, which a transport `ℂ^× → ℚ̄_ℓ^×` can be chosen to be. -/
def KerWild (K : Type) [Field K] [NumberField K] (β : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ g : GQ, (∀ x ∈ L, g x = x) → β g = 1 → g ∈ (G0Galois.resQ K).range

/-- **Glue on R6 (`PkgI2.RaynaudCriterion`), D2 (`PkgI2.D2_fixed_of_raynaud`) and I2-Tors
(`PkgI2.TorsionStructure`) at `p ≥ 7`, `p ≠ ℓ` (N5 L813-818).** Wild inertia at `p` (at the place
of `embP`) inside `G_K` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)`. Proof plan: `m = 3` (`m = 4` if
`p = 13`); `|GL₄(ℤ/m)|` is prime to `p`, so a wild `σ' ∈ G_K` (whose action on the finite group
`A[m] ≅ (ℤ/m)⁴` has `p`-power order) fixes `A[m]`; over `K(A[m])` Raynaud gives `(σ'-1)² = 0` on
`A[ℓⁿ]`, and D2 gives `σ'` fixes `A[ℓⁿ]`; `tate_eq_one_of_torsFix`. Only true for `p ≠ ℓ`.
(Equivalently: for `p > 2g + 1` inertia acts tamely on `V_ℓ`, Grothendieck, SGA 7 I, Exp. IX;
locator UNVERIFIED.) -/
def TateWildK {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K,
    G0Galois.resQ K σ' = decomp p σ → G0Galois.tate A ℓ σ' = 1

/-- **Glue at `p ∈ {2, 3, 5}`, `p ≠ ℓ` (N5 L813-818, L826-833), on R6, D2, I2-Tors and the
descent of `A` to `L`.** There is a finite `E ⊇ L_v` with `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` such that
every wild `σ` fixing `E` has `β(σ) = 1` and acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` through `G_K`.
Glazer: `A = (A_L)_{L'}` with `A_L` over `L`; `E = L_v'(A_L[3])` (`A_L[5]` if `p = 3`), where at
`p = 2` `L_v'/L_v` (degree `≤ 4`) kills `β` on wild inertia (`β|G_{L_v}` has order `≤ 4` on
inertia since the `2`-part of `χ` has conductor `4`; an unramified twist removes the rest; at odd
`p`, `L_v' = L_v` by `beta_wild_of_clauses`); `[E:L_v] ≤ 4·|GL₄(𝔽₃)| ≤ G₀`, resp.
`|GL₄(𝔽₅)| = G₀`. Raynaud and D2 on `A_L/E`. Not provable from `A/K` alone at these primes:
`|GL₄(ℤ/m)|` is divisible by `2`, `3` and `5` for every `m ≥ 3`. -/
def TateWildKE {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, β (decomp p σ) = 1 ∧
      ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
        G0Galois.tate A ℓ σ' = 1

/-! ### The reduction -/

/-- On a wild `σ` with `decomp σ ∈ G_L`, `β(decomp σ) = 1`, `a·Tm` is the Tate action through
`G_K` (proved, from `G7Out` and `KerWild`). -/
theorem aTm_eq_one_of_kerWild {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hK : KerWild K β L) {g : GQ} (hfix : ∀ x ∈ L, g x = x) (hβ : β g = 1)
    (htate : ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = g →
      G0Galois.tate A ℓ σ' = 1) :
    a g • Tm g = 1 := by
  obtain ⟨σ', rfl⟩ := hK g hfix hβ
  obtain ⟨hT, ha, -⟩ := h7.2.2.2.2.2.2.1 σ'
  rw [hT, ha, one_smul, htate σ' rfl]

/-- **`LocalGlue` on G7's data (proved).** For `Tm, a, β` as in `G0Galois.G7Out` with the
clauses `G7Clauses`, `LocalGlue p Tm a β L` follows from `KerWild` (all `p`), `TateWildK` at
`p ≥ 7`, `TateWildKE` at `p ≤ 5`, and `BetaUpper` at `p = 2`. At `p ≥ 7`, `p ≤ D`, the field of
`TorsionFieldWild` is `L_v` itself. -/
theorem localGlue_of_g7 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaUpper β (Lv (p := p) L) U0) :
    LocalGlue (p := p) Tm a β L := by
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  have hpp : p.Prime := Fact.out
  have h7le : ¬ p ≤ 5 → 7 ≤ p := by
    intro h
    by_contra h'
    have : p = 6 := by omega
    exact absurd (this ▸ hpp) (by norm_num)
  -- at `p ≥ 7`: wild `σ` with `decomp σ ∈ G_L` has `a·Tm = 1`
  have hbig : 7 ≤ p → ∀ σ ∈ wildSet (p := p), (∀ x ∈ L, decomp p σ x = x) →
      a (decomp p σ) • Tm (decomp p σ) = 1 := by
    intro h7p σ hσ hfix
    have hp2 : p ≠ 2 := by omega
    exact aTm_eq_one_of_kerWild h7 hK hfix (beta_wild_of_clauses hp2 hC hσ hfix)
      (hW h7p σ hσ)
  refine ⟨fun hpD => ?_, fun hpD => ?_, hB⟩
  · by_cases h5 : p ≤ 5
    · obtain ⟨E, hEfd, hLvE, hdeg, hEw⟩ := hE h5
      refine ⟨E, hEfd, hLvE, hdeg, fun σ hσ => ?_⟩
      have hfix := decomp_fix_of_le (fun _ hx => hLvE (embP_mem_Lv hx)) hσ.1
      exact aTm_eq_one_of_kerWild h7 hK hfix (hEw σ hσ).1 (hEw σ hσ).2
    · have : FiniteDimensional ℚ L := hC.1
      obtain ⟨hfd, -⟩ := Lv_fin (p := p) L
      have hG0 : 1 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
      refine ⟨Lv (p := p) L, hfd, le_rfl, Nat.le_mul_of_pos_left _ hG0, fun σ hσ => ?_⟩
      exact hbig (h7le h5) σ hσ.2 (fixSet_Lv_iff.mp hσ.1)
  · have hpD' : ZInQ.heightD < p := by exact_mod_cast hpD
    exact fun σ hσ hfix => hbig (by omega) σ hσ hfix

/-! ### From torsion points to `V_ℓ` -/

/-- **`σ` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` if it fixes every `ℓⁿ`-torsion point (proved).**
`T_ℓ(A)` is the group of compatible sequences `(xₙ)` with `xₙ ∈ A(K̄)[ℓⁿ]`
(`PkgI3.Tate.pow_smul_eq_zero`), and `σ` acts termwise. -/
theorem tate_eq_one_of_torsFix {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K)
    (h : ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ P = P) :
    G0Galois.tate A ℓ σ = 1 := by
  have hT : A.galT (ℓ := ℓ) σ = LinearMap.id := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    have hx : (ℓ ^ n) • x.1 n = 0 := PkgI3.Tate.pow_smul_eq_zero x.2 n
    have hP : (Additive.toMul (x.1 n)) ^ (ℓ ^ n) = 1 := by
      rw [← toMul_nsmul, hx]; rfl
    change Additive.ofMul (A.galAct σ (Additive.toMul (x.1 n))) = x.1 n
    rw [h n _ hP]; rfl
  have hR : A.galRep ℓ σ = LinearMap.id := by
    change (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ] = LinearMap.id
    rw [hT, LinearMap.baseChange_id]
  change (A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) = LinearMap.id
  rw [hR, LinearMap.baseChange_id]

/-- **Glue on R6 + D2 + I2-Tors, on torsion points (`p ≥ 7`, `p ≠ ℓ`; N5 L813-818).** Wild
inertia at `p` inside `G_K` fixes every `ℓⁿ`-torsion point of `A(K̄)`. This is the form of
`PkgI2.D2_fixed_of_raynaud`; what remains is the bridge from the number field `K` with the place
of `embP` (`resQ`, `decomp`, `wildSet`) to the valuation-ring setting of PkgI2 (a DVR `O ⊆ K(A[m])`
and a valuation ring `w` of `K̄` over it), the base change of `A` to `K(A[m])`, and the
`p`-power order of a wild `σ'` on the finite set `A[m]` (see `TateWildK`). -/
def TorsFixWild {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K,
    G0Galois.resQ K σ' = decomp p σ →
      ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

theorem tateWildK_of_torsFixWild {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (h : TorsFixWild (p := p) A ℓ) : TateWildK (p := p) A ℓ :=
  fun σ hσ σ' hσ' => tate_eq_one_of_torsFix A ℓ σ' (h σ hσ σ' hσ')

/-- **Glue at `p ∈ {2, 3, 5}` on torsion points** (as `TateWildKE`, with "acts trivially on
`V_ℓ`" replaced by "fixes every `ℓⁿ`-torsion point"). -/
def TorsFixWildE {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, β (decomp p σ) = 1 ∧
      ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
        ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

theorem tateWildKE_of_torsFixWildE {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {β : GQ → PadicAlgCl ℓ} {L : IntermediateField ℚ PkgI4.Qbar}
    (h : TorsFixWildE (p := p) A ℓ β L) : TateWildKE (p := p) A ℓ β L := by
  obtain ⟨E, hEfd, hLvE, hdeg, hw⟩ := h
  exact ⟨E, hEfd, hLvE, hdeg, fun σ hσ =>
    ⟨(hw σ hσ).1, fun σ' hσ' => tate_eq_one_of_torsFix A ℓ σ' ((hw σ hσ).2 σ' hσ')⟩⟩

/-- **Glue at `p ∈ {3, 5}`, `p ≠ ℓ` (as `TorsFixWildE` without the `β` clause, which is
automatic at odd `p`: `torsFixWildE_of_odd`).** Some finite `E ⊇ L_v` with
`[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` has every wild `σ ∈ G_E` fixing `A(K̄)[ℓⁿ]` through `G_K`. Glazer:
`E = L_v(A_L[5])` (`p = 3`), `L_v(A_L[3])` (`p = 5`), for the model `A_L` over `L`; R6 and D2. -/
def TorsFixWildOdd {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, ∀ σ' : Field.absoluteGaloisGroup K,
      G0Galois.resQ K σ' = decomp p σ →
        ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

/-- At odd `p`, `TorsFixWildOdd` and G7's clauses give `TorsFixWildE` (proved). -/
theorem torsFixWildE_of_odd (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L)
    (h : TorsFixWildOdd (p := p) A ℓ L) : TorsFixWildE (p := p) A ℓ β L := by
  obtain ⟨E, hEfd, hLvE, hdeg, hw⟩ := h
  exact ⟨E, hEfd, hLvE, hdeg, fun σ hσ => ⟨beta_wild_of_clauses hp2 hC hσ.2
    (decomp_fix_of_le (fun _ hx => hLvE (embP_mem_Lv hx)) hσ.1), hw σ hσ⟩⟩

/-! ### `BetaUpper` at `p = 2` without T16 (proved from a degree-`4` twist field) -/

/-- **Glue at `p = 2` (N5 L826-844; replaces T16 + D3 + Herbrand).** Some finite `M ⊇ L_v` with
`[M:L_v] ≤ 4` has `β = 1` on wild inertia of `G_M`. Proof plan: on `G_{L_v}`, `β` is a character
(`betaCharOn_of_cocycle`) and `β⁴ = χ²` is unramified at `2` (the `2`-part of `χ` is the
character mod `4`, of order `2`; the odd parts are unramified at `2`); an unramified `η` with
`η⁴ = β⁴` exists (`G_{L_v}/I` is procyclic and `β⁴` has finite order), and `M` is the kernel
field of `β η⁻¹`, of order dividing `4`. On wild inertia `η = 1`. -/
def BetaTwist2 (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ M : Fld p, FiniteDimensional ℚ_[p] M ∧ Lv (p := p) L ≤ M ∧
    Module.finrank ℚ_[p] M ≤ 4 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet M ∩ wildSet, β (decomp p σ) = 1

/-- **`BetaUpper` from `BetaTwist2` and G7's clauses (proved), with no class field theory.**
`[M:ℚ_p] ≤ 4D ≤ DG₀`; its Galois closure `F` has `e(F) ≤ (DG₀)!` (`exists_finGal_ramCard_le`), so
`G_{ℚ_p}^t ⊆ G_F ⊆ G_M` for `t > U₀ = 4(DG₀)²` (`UpperBreakFix`, proved from T20 + T21 and
`ladicDVRModelZp`), and `G_{ℚ_p}^t` is wild (`upperWild`). -/
theorem betaUpper_of_twist {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L)
    (h : BetaTwist2 (p := p) β L) : BetaUpper β (Lv (p := p) L) U0 := by
  haveI : FiniteDimensional ℚ L := hC.1
  obtain ⟨M, hMfd, hLvM, hdeg, hM⟩ := h
  obtain ⟨-, hLv⟩ := Lv_fin (p := p) L
  have hG0 : 4 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
  have hMn : Module.finrank ℚ_[p] M ≤ ZInQ.heightD * ZInQ.heightG0 := by
    calc Module.finrank ℚ_[p] M ≤ 4 * Module.finrank ℚ_[p] (Lv (p := p) L) := hdeg
      _ ≤ ZInQ.heightG0 * ZInQ.heightD := Nat.mul_le_mul hG0 (hLv.trans hC.2.1)
      _ = ZInQ.heightD * ZInQ.heightG0 := Nat.mul_comm _ _
  obtain ⟨F, hF, hMF, he⟩ := exists_finGal_ramCard_le hMn
  have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
    Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
  have hUB : UpperBreakFix p :=
    upperBreakFix_of_hilbertSerre (hilbertSerre_of_model (ladicDVRModel_of_Zp ladicDVRModelZp))
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  intro t ht σ hσ
  have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold U0 at ht; exact ht) hσ.1
  have hwild : σ ∈ wildSet := upperWild (p := p) t (by linarith) hσ.1
  exact hM σ ⟨fun x hx => hfix x (hMF hx), hwild⟩

/-- **`LocalGlue` on G7's data with `BetaTwist2` at `p = 2` (proved)**: as `localGlue_of_g7`,
with `BetaUpper` replaced by the smaller `BetaTwist2` (`betaUpper_of_twist`). -/
theorem localGlue_of_g7_twist {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_g7 h7 hC hK hW hE (fun h => betaUpper_of_twist hC (hB h))

end LocalGlueSec

end G15Ram


/-! ## §7 (local-glue). `TorsFixWild` at `p ≥ 7` from Raynaud's criterion and I2-Tors

`torsFixWild_of_raynaud` (proved): `TorsFixWild` at `p ≥ 7`, `p ≠ ℓ`, follows from
* `WildIter`: a wild `σ'` has `p`-power period on each point of `A(K̄)` (proved in §7b, `wildIter`);
* `TorsGL A m` for `m = 3, 7`: `A(K̄)[m] ≅ (ℤ/m)⁴` as groups (the instance of the leaf I2-Tors,
  `torsGL_of_leaf`);
* `RaynaudPlace A m` for `m = 3` (`p ≠ 13`), `m = 7` (`p = 13`): a wild `σ'` fixing `A(K̄)[m]`
  satisfies `(σ' - 1)² = 0` on
  `A(K̄)[ℓⁿ]` (the instance of the leaf R6 at the place of `embP`; bridge glue).
The algebra in between is proved: `|GL₄(𝔽₃)| = 2⁹·3⁶·5·13` and `13 ∤ |GL₄(𝔽₇)|`, so the action of
a wild `σ'` on `A[m]` has order prime to `p` and `p`-power, hence is trivial
(`iterate_card_GL_fix`); then `(σ'-1)² = 0` and a `p`-power period force `σ' = 1` on
`A[ℓⁿ]` (`fixed_of_unipSq_of_iterate'`, the core of D2). -/

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj

section TorsSec

/-- **An additive structure of `S ≅ (ℤ/q)ⁿ` bounds the period (proved).** If `φ : G →* G` is
injective, maps the multiplicatively closed `S` into itself, and `S ≅ (ℤ/q)ⁿ` as groups, then
`φ^[N] = id` on `S`, `N = |GLₙ(𝔽_q)|`. -/
theorem iterate_card_GL_fix {G : Type*} [Group G] (φ : G →* G) (hinj : Function.Injective φ)
    (S : Set G) (hS : ∀ x ∈ S, φ x ∈ S) (hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (q : ℕ) [Fact q.Prime] (n : ℕ) (e : S ≃ (Fin n → ZMod q))
    (he : ∀ (x y : S) (h : x.1 * y.1 ∈ S), e ⟨x.1 * y.1, h⟩ = e x + e y) :
    ∀ x ∈ S, φ^[Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod q))] x = x := by
  set φS : S → S := fun x => ⟨φ x, hS x x.2⟩ with hφS
  set f : (Fin n → ZMod q) → (Fin n → ZMod q) := fun v => e (φS (e.symm v)) with hf
  have hadd : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    set x := e.symm a
    set y := e.symm b
    have hxy : e.symm (a + b) = ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he x y, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hφxy : φS ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ =
        ⟨(φS x).1 * (φS y).1, hSmul _ (φS x).2 _ (φS y).2⟩ := by
      apply Subtype.ext
      simp [hφS, map_mul]
    simp only [hf]
    rw [hxy, hφxy, he]
  have hfinj : Function.Injective f := by
    intro a b h
    have h1 := e.injective h
    have h2 : φ (e.symm a).1 = φ (e.symm b).1 := congrArg Subtype.val h1
    exact e.symm.injective (Subtype.ext (hinj h2))
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  let fA : (Fin n → ZMod q) →+ (Fin n → ZMod q) := AddMonoidHom.mk' f hadd
  let fL := fA.toZModLinearMap q
  let fLE := LinearEquiv.ofBijective fL hfbij
  let u : LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q) :=
    ⟨fLE.toLinearMap, fLE.symm.toLinearMap, by ext v; simp, by ext v; simp⟩
  set N := Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod q)) with hN
  have hcard : Nat.card (LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q)) = N :=
    (Nat.card_congr (Matrix.GeneralLinearGroup.toLin).toEquiv).symm
  have huN : u ^ N = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have hfN : ∀ v, f^[N] v = v := by
    intro v
    have h1 : ((u ^ N : LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q)) :
        Module.End (ZMod q) (Fin n → ZMod q)) v = v := by rw [huN]; rfl
    rw [Units.val_pow_eq_pow_val, Module.End.pow_apply] at h1
    exact h1
  have hsemi : Function.Semiconj e φS f := by
    intro x
    simp [hf]
  have hval : Function.Semiconj (Subtype.val : S → G) φS φ := fun x => rfl
  intro x hx
  have h1 : e (φS^[N] ⟨x, hx⟩) = e ⟨x, hx⟩ := by
    rw [(hsemi.iterate_right N) ⟨x, hx⟩]
    exact hfN _
  have h2 := congrArg Subtype.val (e.injective h1)
  rw [(hval.iterate_right N) ⟨x, hx⟩] at h2
  exact h2

/-- `|GL₄(𝔽₃)| = 80·78·72·54 = 24261120 = 2⁹·3⁶·5·13` (proved). -/
theorem card_GL4_three : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 3)) = 24261120 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

/-- `|GL₄(𝔽₇)| = 2400·2394·2352·2058` (proved). -/
theorem card_GL4_seven :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 7)) = 2400 * 2394 * 2352 * 2058 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

theorem coprime_card_GL4_three {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (h13 : p ≠ 13) :
    Nat.Coprime p 24261120 := by
  rw [hp.coprime_iff_not_dvd]
  intro h
  have hfac : (24261120 : ℕ) = 2 ^ 9 * 3 ^ 6 * 5 * 13 := by norm_num
  rw [hfac] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h; omega

theorem coprime_card_GL4_seven : Nat.Coprime 13 (2400 * 2394 * 2352 * 2058) := by norm_num

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]

/-- **D2's algebraic core on PkgI3 points (proved; as `PkgI2.fixed_of_unipSq_of_iterate`).** If
`(σ - 1)² x = 0`, `x ∈ A(K̄)[ℓⁿ]`, and `σ^{qᵃ} x = x` with `qᵃ` prime to `ℓⁿ`, then `σ x = x`. -/
theorem fixed_of_unipSq_of_iterate' (A : PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (x : A.Pt (AlgebraicClosure K)) (ℓ n q a : ℕ) (hcop : Nat.Coprime (q ^ a) (ℓ ^ n))
    (hx : x ^ (ℓ ^ n) = 1)
    (hu : A.galAct σ (A.galAct σ x) * (A.galAct σ x)⁻¹ * (A.galAct σ x)⁻¹ * x = 1)
    (hit : (A.galAct σ)^[q ^ a] x = x) : A.galAct σ x = x := by
  set N := A.galAct σ x * x⁻¹ with hN
  have hσN : A.galAct σ N = N := by
    rw [hN, map_mul, map_inv]
    have h2 : A.galAct σ (A.galAct σ x) * (A.galAct σ x)⁻¹ =
        ((A.galAct σ x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hiter : ∀ k : ℕ, (A.galAct σ)^[k] x = N ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hσN, pow_succ, hN]
      group
  have h1 : N ^ (q ^ a) = 1 := by
    have := hiter (q ^ a)
    rw [hit] at this
    exact (mul_eq_right.mp this.symm)
  have h2 : N ^ (ℓ ^ n) = 1 := by
    rw [hN, mul_pow, ← map_pow, hx, map_one, inv_pow, hx]; simp
  have hN1 : N = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN] at hN1
  exact mul_inv_eq_one.mp hN1

/-- **Glue (bridge): wild elements have `p`-power period on points.** For wild `σ` and
`σ' ∈ G_K` over `decomp σ`, every `P ∈ A(K̄)` has `σ'^{pᵃ} P = P` for some `a`. Proof plan: `P` is
defined over a finite `F ⊆ K̄` (a `K̄`-point of a scheme of finite type over `K`); `qEmb K` is an
isomorphism `ℚ̄ ≅ K̄` (both are algebraic closures of `ℚ`), and `embP` sends `qEmb⁻¹(F)` into a
finite extension of `ℚ_p`, whose Galois closure is fixed by some `σ^{pᵃ}`
(`exists_pow_fix_of_wild`, local-data). -/
def WildIter (A : PkgI3.AbVar K) : Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
    ∀ P : A.Pt (AlgebraicClosure K), ∃ a : ℕ, (A.galAct σ')^[p ^ a] P = P

/-- **The instance of the leaf I2-Tors on `A` (`A(K̄)[m] ≅ (ℤ/m)⁴` as groups).** Proved from
`ObjBridge.TorsionStructure` for `dim A = 2` in `torsGL_of_leaf`. -/
def TorsGL (A : PkgI3.AbVar K) (m : ℕ) : Prop :=
  ∃ e : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} ≃ (Fin 4 → ZMod m),
    ∀ (x y : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1})
      (h : x.1 * y.1 ∈ {P : A.Pt (AlgebraicClosure K) | P ^ m = 1}),
      e ⟨x.1 * y.1, h⟩ = e x + e y

/-- **Glue on the leaf R6 (`PkgI2.RaynaudCriterion`) at the place of `embP` (N5 L813-818).**
A wild `σ' ∈ G_K` (over `decomp σ`, `σ ∈ wildSet`) that fixes `A(K̄)[m]` satisfies
`(σ' - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ ≠ p`. Proof plan: R6 on `K' = K(A[m])`
(over which `A[m]` is rational, `m ≥ 3` prime to `p`) with the valuation ring of `K'` at the
place of `embP` (a DVR) and a valuation ring `w` of `K̄` over it; `σ'` fixes `K'`, and a wild
element is in the inertia group of `w`. What is missing is that bridge (PkgI2's setting is a
field with a DVR and `AlgebraicClosure`; here `G_K`, `resQ`, `decomp`) and the base change of
`A` to `K'`. Claimed only for `m ≥ 3` prime to `p` (used with `m = 3` for `p ≠ 13` and `m = 7`
for `p = 13`; for `m = p` Raynaud's criterion does not apply and the statement can fail). -/
def RaynaudPlace (A : PkgI3.AbVar K) (m : ℕ) : Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
    (∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ (n : ℕ) (x : A.Pt (AlgebraicClosure K)), x ^ (ℓ ^ n) = 1 →
      A.galAct σ' (A.galAct σ' x) * (A.galAct σ' x)⁻¹ * (A.galAct σ' x)⁻¹ * x = 1

/-- **`TorsGL` from the leaf I2-Tors (proved)**, for `dim A = 2` (a clause of `G7Out`). -/
theorem torsGL_of_leaf (hT : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2)
    (m : ℕ) (hm : 0 < m) : TorsGL A m := by
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  obtain ⟨e, he⟩ := hT K (ObjBridge.toGrp A) 2 m (by exact_mod_cast hdim) hm hmK
  exact ⟨e, he⟩

/-- `σ⁻¹ (σ P) = P` on points (proved). -/
theorem galAct_inv_galAct (A : PkgI3.AbVar K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (P : A.Pt (AlgebraicClosure K)) :
    A.galAct σ⁻¹ (A.galAct σ P) = P := by
  change PkgI3.AbVar.galHom σ⁻¹ ≫ PkgI3.AbVar.galHom σ ≫ P = P
  rw [← Category.assoc, ← PkgI3.AbVar.galHom_mul, inv_mul_cancel, PkgI3.AbVar.galHom_one,
    Category.id_comp]

theorem galAct_injective (A : PkgI3.AbVar K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    Function.Injective (A.galAct (L := AlgebraicClosure K) σ) := by
  intro x y h
  have h1 := congrArg (A.galAct σ⁻¹) h
  rwa [galAct_inv_galAct, galAct_inv_galAct] at h1

/-- A wild `σ'` fixes `A(K̄)[m]` when `p ∤ |GL₄(ℤ/m)|` (proved from `WildIter` and `TorsGL`). -/
theorem fix_torsion_of_coprime {A : PkgI3.AbVar K} (hI : WildIter (p := p) A) (m : ℕ)
    [Fact m.Prime] (hT : TorsGL A m)
    (hcop : Nat.Coprime p (Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod m))))
    {σ : GQp p} (hσ : σ ∈ wildSet) {σ' : Field.absoluteGaloisGroup K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) :
    ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P := by
  obtain ⟨e, he⟩ := hT
  intro P hP
  have hfix := iterate_card_GL_fix (A.galAct σ') (galAct_injective A σ')
    {P : A.Pt (AlgebraicClosure K) | P ^ m = 1}
    (fun x hx => by
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [← map_pow, hx, map_one])
    (fun x hx y hy => by
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      rw [mul_pow, hx, hy, _root_.one_mul]) m 4 e he P hP
  obtain ⟨a, ha⟩ := hI σ hσ σ' hσ' P
  have h1 : Function.IsPeriodicPt (A.galAct σ') (p ^ a) P := ha
  have h2 : Function.IsPeriodicPt (A.galAct σ')
      (Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod m))) P := hfix
  have h3 := h1.gcd h2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left a hcop)] at h3
  exact h3

/-! ### `WildIter` from `PtFinite` (proved) -/

/-- `σ (τ P) = (στ) P` on points (proved). -/
theorem galAct_galAct (A : PkgI3.AbVar K) (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (P : A.Pt (AlgebraicClosure K)) : A.galAct σ (A.galAct τ P) = A.galAct (σ * τ) P := by
  change PkgI3.AbVar.galHom σ ≫ PkgI3.AbVar.galHom τ ≫ P = PkgI3.AbVar.galHom (σ * τ) ≫ P
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

theorem galAct_iterate (A : PkgI3.AbVar K) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (P : A.Pt (AlgebraicClosure K)) (k : ℕ) : (A.galAct σ)^[k] P = A.galAct (σ ^ k) P := by
  induction k with
  | zero =>
    change P = PkgI3.AbVar.galHom 1 ≫ P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  | succ k ih => rw [Function.iterate_succ_apply', ih, galAct_galAct, ← pow_succ']

/-- `qEmb K : ℚ̄ → K̄` is onto (proved): `K̄` is integral over `ℚ` (`K` is a number field), hence
over the algebraically closed `ℚ̄`. -/
theorem qEmbRing_surjective (K : Type) [Field K] [NumberField K] :
    Function.Surjective (G0Galois.qEmbRing K) := by
  have hint : Algebra.IsIntegral ℚ (AlgebraicClosure K) := Algebra.IsIntegral.trans K
  have h : ((G0Galois.qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ))).IsIntegral := by
    rw [Subsingleton.elim ((G0Galois.qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ)))
      (algebraMap ℚ (AlgebraicClosure K))]
    exact hint.isIntegral
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral _ (RingHom.IsIntegral.tower_top _ _ h)).2

theorem pow_fix_mono {G X : Type*} [Group G] [MulAction G X] {g : G} {x : X} {q b a : ℕ}
    (h : g ^ (q ^ b) • x = x) (hba : b ≤ a) : g ^ (q ^ a) • x = x := by
  have hmem : g ^ (q ^ b) ∈ MulAction.stabilizer G x := h
  have : g ^ (q ^ a) = (g ^ (q ^ b)) ^ (q ^ (a - b)) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hba]
  rw [this]
  exact (MulAction.stabilizer G x).pow_mem hmem _

/-- **A wild `σ'` has `p`-power period on each element of `K̄` (proved).** `x = qEmb y`;
`σ^{pᵃ}` fixes the normal closure of `ℚ_p(embP y)` (`exists_pow_fix_of_wild`), so
`decomp(σ^{pᵃ})` fixes `y` (`decomp_spec`), and `σ'^{pᵃ} x = qEmb(decomp(σ^{pᵃ}) y) = x`
(`resQ_spec`). -/
theorem wild_pow_fix_elem {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (x : AlgebraicClosure K) :
    ∃ a : ℕ, (σ' ^ (p ^ a)) x = x := by
  obtain ⟨y, rfl⟩ := qEmbRing_surjective K x
  set E : Fld p := IntermediateField.adjoin ℚ_[p] {embP (p := p) y}
  haveI : FiniteDimensional ℚ_[p] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  set F' := IntermediateField.normalClosure ℚ_[p] E (Kbar p)
  haveI : FiniteDimensional ℚ_[p] F' := normalClosure.is_finiteDimensional ℚ_[p] E (Kbar p)
  haveI : Normal ℚ_[p] F' := normalClosure.normal ℚ_[p] E (Kbar p)
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ (F' := F') ⟨inferInstance, IsGalois.mk⟩
  refine ⟨a, ?_⟩
  have hyE : embP (p := p) y ∈ F' :=
    E.le_normalClosure (IntermediateField.mem_adjoin_simple_self ℚ_[p] _)
  have hdec : decomp p (σ ^ (p ^ a)) y = y := by
    apply (embP (p := p)).injective
    rw [decomp_spec]
    exact ha _ hyE
  have h1 : G0Galois.qEmbRing K (G0Galois.resQ K (σ' ^ (p ^ a)) y) =
      (σ' ^ (p ^ a)) (G0Galois.qEmbRing K y) := G0Galois.resQ_spec K _ y
  have hpow : G0Galois.resQ K (σ' ^ (p ^ a)) = (G0Galois.resQ K σ') ^ (p ^ a) := map_pow _ _ _
  rw [hpow, hσ', ← map_pow, hdec] at h1
  exact h1.symm

/-- **A wild `σ'` has `p`-power period on each finite `F ⊆ K̄` over `K` (proved)**, from
`wild_pow_fix_elem` on a basis. -/
theorem wild_pow_fix_field {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (F : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K F] : ∃ a : ℕ, ∀ x ∈ F, (σ' ^ (p ^ a)) x = x := by
  set b := Module.finBasis K F
  choose c hc using fun i => wild_pow_fix_elem hσ hσ' ((b i : F) : AlgebraicClosure K)
  refine ⟨∑ i, c i, fun x hx => ?_⟩
  have hb : ∀ i, (σ' ^ (p ^ (∑ i, c i))) ((b i : F) : AlgebraicClosure K) = b i := fun i =>
    pow_fix_mono (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hc i)
      (Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) (Finset.mem_univ i))
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • ((b i : F) : AlgebraicClosure K) := by
    have h := congrArg (fun z : F => (z : AlgebraicClosure K)) (b.sum_repr ⟨x, hx⟩).symm
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    exact h
  rw [hx', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, hb i, ← Algebra.smul_def]

/-- **Glue (Mathlib-level): `K̄`-points are defined over finite extensions.** Every
`P ∈ A(K̄)` is fixed by `G_F` for a finite `F ⊆ K̄` over `K` (a `K̄`-point of a scheme of finite
type over `K` factors through `Spec F`, `F` generated by the images of finitely many coordinates;
standard, e.g. EGA I/IV, locator UNVERIFIED). -/
def PtFinite (A : PkgI3.AbVar K) : Prop :=
  ∀ P : A.Pt (AlgebraicClosure K), ∃ F : IntermediateField K (AlgebraicClosure K),
    FiniteDimensional K F ∧ ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (∀ x ∈ F, τ x = x) → A.galAct τ P = P

/-- **`WildIter` from `PtFinite` (proved).** -/
theorem wildIter_of_ptFinite {A : PkgI3.AbVar K} (h : PtFinite A) : WildIter (p := p) A := by
  intro σ hσ σ' hσ' P
  obtain ⟨F, hF, hP⟩ := h P
  obtain ⟨a, ha⟩ := wild_pow_fix_field (σ' := σ') hσ hσ' F
  have hit := galAct_iterate A σ' P (p ^ a)
  exact ⟨a, hit.trans (hP _ ha)⟩

/-- **`TorsFixWild` at `p ≥ 7`, `p ≠ ℓ`, from `WildIter`, I2-Tors and Raynaud at the place
(proved).** `m = 3` (`m = 7` if `p = 13`): the wild `σ'` fixes `A[m]`
(`fix_torsion_of_coprime`), so `(σ'-1)² = 0` on `A[ℓⁿ]` (`RaynaudPlace`), and with a `p`-power
period it fixes `A[ℓⁿ]` (`fixed_of_unipSq_of_iterate'`). -/
theorem torsFixWild_of_raynaud {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hI : WildIter (p := p) A) (hT3 : TorsGL A 3) (hT7 : TorsGL A 7)
    (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3) (hR7 : p = 13 → RaynaudPlace (p := p) A 7) :
    TorsFixWild (p := p) A ℓ := by
  intro σ hσ σ' hσ' n x hx
  have hpp : p.Prime := Fact.out
  have hfixm : ∃ m, (∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P) ∧
      RaynaudPlace (p := p) A m := by
    by_cases h13 : p = 13
    · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      refine ⟨7, fix_torsion_of_coprime hI 7 hT7 ?_ hσ hσ', hR7 h13⟩
      rw [card_GL4_seven, h13]; exact coprime_card_GL4_seven
    · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      refine ⟨3, fix_torsion_of_coprime hI 3 hT3 ?_ hσ hσ', hR3 h13⟩
      rw [card_GL4_three]; exact coprime_card_GL4_three hpp h7 h13
  obtain ⟨m, hm, hR⟩ := hfixm
  obtain ⟨a, ha⟩ := hI σ hσ σ' hσ' x
  have hcop : Nat.Coprime (p ^ a) (ℓ ^ n) :=
    Nat.Coprime.pow a n ((Nat.coprime_primes hpp Fact.out).mpr (Ne.symm hℓp))
  exact fixed_of_unipSq_of_iterate' A σ' x ℓ n p a hcop hx
    (hR σ hσ σ' hσ' hm ℓ Fact.out hℓp n x hx) ha

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaves I2-Tors and (through `RaynaudPlace`) R6,
and the bridge `WildIter` (proved).** `dim A = 2` is a clause of `G7Out`. -/
theorem tateWildK_of_leaves {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2)
    (hI : WildIter (p := p) A) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_torsFixWild (torsFixWild_of_raynaud hℓp h7 hI (torsGL_of_leaf hTors A hdim 3
    (by norm_num)) (torsGL_of_leaf hTors A hdim 7 (by norm_num)) hR3 hR7)

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaf I2-Tors, `PtFinite` and `RaynaudPlace`
(proved).** -/
theorem tateWildK_of_leaves' {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2)
    (hPt : PtFinite A) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_leaves hℓp h7 hTors hdim (wildIter_of_ptFinite hPt) hR3 hR7

end TorsSec

end G15Ram

end


/-! ## §7b (local-glue). `PtFinite` proved: `K̄`-points come from finite extensions

`K̄ = colim F` over the finite subextensions `F` of `K̄/K` (as in scratch/morph-descend's
`ringCoconeIsColimit`, there for `ℚ̄`), so `Spec K̄ = lim Spec F`; since `A → Spec K` is smooth,
hence locally of finite presentation, Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(Stacks 01ZC) factors every `K`-morphism `Spec K̄ → A` through some `Spec F`. -/

noncomputable section

namespace G15Ram

open CategoryTheory Limits AlgebraicGeometry

section PtFiniteSec

variable {K : Type} [Field K]

/-- The finite subextensions of `K̄/K`, ordered by inclusion. -/
abbrev FIdx (K : Type) [Field K] : Type :=
  {F : IntermediateField K (AlgebraicClosure K) // FiniteDimensional K F}

instance : IsDirectedOrder (FIdx K) where
  directed F₁ F₂ := by
    obtain ⟨F₁, h₁⟩ := F₁
    obtain ⟨F₂, h₂⟩ := F₂
    exact ⟨⟨F₁ ⊔ F₂, IntermediateField.finiteDimensional_sup F₁ F₂⟩,
      show F₁ ≤ F₁ ⊔ F₂ from le_sup_left, show F₂ ≤ F₁ ⊔ F₂ from le_sup_right⟩

instance : Nonempty (FIdx K) := ⟨⟨⊥, inferInstance⟩⟩

/-- The diagram `F ↦ F` of rings. -/
def fRingDiag (K : Type) [Field K] : FIdx K ⥤ CommRingCat where
  obj F := CommRingCat.of F.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `K̄` as a cocone. -/
def fRingCocone (K : Type) [Field K] : Cocone (fRingDiag K) where
  pt := CommRingCat.of (AlgebraicClosure K)
  ι := { app F := CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure K))
         naturality _ _ _ := rfl }

/-- `K̄ = colim F` over the finite subextensions (as morph-descend's `ringCoconeIsColimit`). -/
def fRingCoconeIsColimit (K : Type) [Field K] : IsColimit (fRingCocone K) := by
  haveI : ReflectsColimit (fRingDiag K) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : AlgebraicClosure K)
    have hx : _root_.IsIntegral K x := Algebra.IsIntegral.isIntegral _
    have : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
      IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin K {x}, this⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro i x y h
    exact ⟨i, 𝟙 i, by rw [Subtype.ext h]⟩

/-- The diagram `F ↦ Spec F` of schemes. -/
def fSpecDiag (K : Type) [Field K] : (FIdx K)ᵒᵖ ⥤ Scheme where
  obj F := Spec (CommRingCat.of F.unop.1)
  map f := Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)
  map_id F := by
    rw [show CommRingCat.ofHom (IntermediateField.inclusion (leOfHom (𝟙 F).unop)).toRingHom =
      𝟙 _ from rfl, Spec.map_id]
  map_comp f g := by
    rw [← Spec.map_comp]
    rfl

/-- `Spec K̄` as a cone over `fSpecDiag`. -/
def fSpecCone (K : Type) [Field K] : Cone (fSpecDiag K) where
  pt := Spec (CommRingCat.of (AlgebraicClosure K))
  π := { app F := Spec.map (CommRingCat.ofHom (algebraMap F.unop.1 (AlgebraicClosure K)))
         naturality F F' f := by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
          change _ = _ ≫ Spec.map _
          rw [← Spec.map_comp]
          rfl }

/-- `Spec K̄ = lim Spec F` (proved; `Spec` turns the colimit `fRingCoconeIsColimit` into a limit). -/
def fSpecConeIsLimit (K : Type) [Field K] : IsLimit (fSpecCone K) := by
  have h := isLimitOfPreserves Scheme.Spec (fRingCoconeIsColimit K).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro F F' f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro F
    simp only [Iso.refl_hom, Category.id_comp]

/-- **`PtFinite` holds for every abelian variety (proved).** -/
theorem ptFinite (A : PkgI3.AbVar K) : PtFinite A := by
  intro P
  have h3 : ∀ {i j : (FIdx K)ᵒᵖ} (f : i ⟶ j), IsAffineHom ((fSpecDiag K).map f) := fun f => by
    change IsAffineHom (Spec.map _); infer_instance
  have h1 : ∀ i, CompactSpace ((fSpecDiag K).obj i) := fun i => by
    change CompactSpace (Spec _); infer_instance
  have h2 : ∀ i, QuasiSeparatedSpace ((fSpecDiag K).obj i) := fun i => by
    change QuasiSeparatedSpace (Spec _); infer_instance
  let t : fSpecDiag K ⟶ (Functor.const _).obj (Spec (CommRingCat.of K)) :=
    { app F := Spec.map (CommRingCat.ofHom (algebraMap K F.unop.1))
      naturality F F' f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map]
        change Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp]
        rfl }
  have ha : (fSpecCone K).π ≫ t = (Functor.const _).map (P.left ≫ A.X.hom) := by
    ext F
    simp only [NatTrans.comp_app, Functor.const_map_app]
    change Spec.map _ ≫ Spec.map _ = P.left ≫ A.X.hom
    rw [← Spec.map_comp, Over.w P]
    rfl
  obtain ⟨F, g, hg, -⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (fSpecDiag K) t A.X.hom
      (fSpecCone K) (fSpecConeIsLimit K) P.left ha
  refine ⟨F.unop.1, F.unop.2, fun τ hτ => ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (τ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ P.left =
    P.left
  rw [← hg]
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) ?_)
  refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
  ext x
  exact hτ x.1 x.2

/-- **`WildIter` holds for every abelian variety (proved)**: `wildIter_of_ptFinite` and
`ptFinite`. -/
theorem wildIter {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) : WildIter (p := p) A :=
  wildIter_of_ptFinite (ptFinite A)

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaf I2-Tors and the instances `RaynaudPlace`
of the leaf R6 alone (proved).** -/
theorem tateWildK_of_raynaud {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p)
    (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_leaves hℓp h7 hTors hdim (wildIter A) hR3 hR7

end PtFiniteSec

end G15Ram

end


/-! ## §7c' (local-glue). Verbatim slices of scratch/neron-lg/NeronLG.lean (origin/wip/neron-lg)
l.207-215, l.225-236, l.1406-1472 -/

noncomputable section

namespace ZInQ.NeronLG

open NumberField
open CategoryTheory MonObj

/-- The discrete valuation ring `𝓞_{L,v}` of a nonzero prime `v` of `𝓞_L`, as a valuation subring
of `L` (the ring of the `v`-adic valuation). -/
noncomputable def dvrAt {L : Type} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ValuationSubring L :=
  (v.valuation L).valuationSubring

instance {L : Type} [Field L] [NumberField L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    IsDiscreteValuationRing (dvrAt v) := by
  unfold dvrAt; infer_instance

section Classify

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K]

/-- Every valuation subring of a number field contains `𝓞_K` (it is integrally closed). -/
theorem ringOfIntegers_mem (O : ValuationSubring K) (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem O)

theorem toO_coe (O : ValuationSubring K) (x : 𝓞 K) : ((toO O x : O) : K) = algebraMap (𝓞 K) K x :=
  rfl

end Classify

section Restrict

variable {K : Type} [Field K] [NumberField K]

/-- The center of a valuation subring `O ≠ ⊤` of a number field on `𝓞_K`: a nonzero prime. -/
def center' (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := (IsLocalRing.maximalIdeal O).comap (toO O)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy⟩ : ∃ y : K, y ∉ O := by
      by_contra h
      push_neg at h
      exact hO (eq_top_iff.2 fun y _ => h y)
    have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hyi : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    let x : O := ⟨y⁻¹, hyi⟩
    have hx : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu'⟩ := hu
      apply hy
      have : ((u⁻¹ : Oˣ) : O) * x = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Oˣ) : O) : K)) * y⁻¹ = 1 := congrArg Subtype.val this
      have h3 : y = (((u⁻¹ : Oˣ) : O) : K) := by
        field_simp at h2
        exact h2.symm
      rw [h3]; exact (((u⁻¹ : Oˣ) : O)).2
    have hx0 : x ≠ 0 := fun h => inv_ne_zero hy0 (congrArg Subtype.val h)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have ha : toO O a = x * toO O b := by
      apply Subtype.ext
      rw [toO_coe, Subring.coe_mul, toO_coe, ← hab, div_mul_cancel₀ _ hb0]
    intro hbot
    have hmem : a ∈ (IsLocalRing.maximalIdeal O).comap (toO O) := by
      rw [Ideal.mem_comap, ha]; exact Ideal.mul_mem_right _ _ hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    apply Subtype.ext
    rw [← hab, hmem, map_zero, zero_div]; rfl

/-- **Every valuation subring `O ≠ ⊤` of a number field is `𝓞_{K,v}` (proved).** -/
theorem dvrAt_center' (O : ValuationSubring K) (hO : O ≠ ⊤) : dvrAt (center' O hO) = O := by
  apply ValuationSubring.eq_of_le_of_ne_top _ _ hO
  intro x hx
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (center' O hO) x hx
  have hd : IsUnit (toO O d) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hvd : O.valuation (algebraMap (𝓞 K) K d) = 1 := (O.valuation_eq_one_iff _).1 hd
  apply O.mem_of_valuation_le_one
  have h2 := congrArg O.valuation hnd
  rw [map_mul, hvd, _root_.mul_one] at h2
  rw [h2]
  exact O.valuation_le_one (toO O n)

/-- Every valuation subring `O ≠ ⊤` of a number field is a DVR. -/
theorem isDiscreteValuationRing_of_ne_top (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by
  rw [← dvrAt_center' O hO]
  infer_instance

end Restrict

end ZInQ.NeronLG

end


/-! ## §7c'' (local-glue). Verbatim copy of scratch/unram-tate/BCPoints.lean
(origin/wip/unram-tate) l.14-142 -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace UnramTate

/-- `Spec L → Spec K`. -/
noncomputable abbrev sK (K L : Type) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

theorem specMap_comp_sK :
    Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ sK K L =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K L Ω]

/-- `Over.map (Spec L → Spec K) (Spec Ω / L) ≅ Spec Ω / K`. -/
noncomputable def ptMapIso :
    (Over.map (sK K L)).obj (PkgI3.AbVar.ptObj (K := L) Ω) ≅ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, PkgI3.AbVar.ptObj, Over.mk_hom]
    erw [Category.id_comp]
    exact (specMap_comp_sK (K := K) (L := L) Ω).symm)

/-- The adjunction bijection is multiplicative. -/
theorem homEquiv_mul (X : Over (Spec (CommRingCat.of L)))
    (p q : (Over.map (sK K L)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (sK K L)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (sK K L)).homEquiv X A.X p *
        (Over.mapPullbackAdj (sK K L)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- **Points of a base change**: `A_L(Ω) ≃* A(Ω)`. -/
noncomputable def bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω where
  toFun p := (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  invFun x := (Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)
  left_inv p := Equiv.apply_symm_apply ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X) p
  right_inv x := by
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)) = x
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  map_mul' p q := by
    obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective p
    obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective q
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
        ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X p' *
          (Over.mapPullbackAdj (sK K L)).homEquiv _ A.X q') = _
    rw [← homEquiv_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      MonObj.comp_mul]

/-- `bcPt` is natural for `L`-automorphisms of `Ω`. -/
theorem bcPt_galAct (σ : Ω ≃ₐ[L] Ω) (p : (A.baseChange L).Pt Ω) :
    bcPt A Ω ((A.baseChange L).galAct σ p) = A.galAct (σ.restrictScalars K) (bcPt A Ω p) := by
  show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      (PkgI3.AbVar.galHom σ ≫ p) =
    PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv ≫
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  have hnat := Adjunction.homEquiv_naturality_left_symm (Over.mapPullbackAdj (sK K L))
    (PkgI3.AbVar.galHom σ) (p : PkgI3.AbVar.ptObj Ω ⟶ (Over.pullback (sK K L)).obj A.X)
  have hsq : (ptMapIso Ω).inv ≫ (Over.map (sK K L)).map (PkgI3.AbVar.galHom σ) =
      PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv := by
    apply Over.OverMorphism.ext
    simp [ptMapIso, PkgI3.AbVar.galHom]
    rfl
  erw [hnat]
  rw [← Category.assoc, hsq, Category.assoc]

end BC

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-isomorphism `φ : Ω ≃ Ω₂`. -/
noncomputable def trHom (φ : Ω ≃ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem trHom_left (φ : Ω ≃ₐ[K] Ω₂) :
    (trHom φ).left = Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) := rfl

theorem trHom_symm_comp (φ : Ω ≃ₐ[K] Ω₂) : trHom φ.symm ≫ trHom φ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (φ.symm : Ω₂ →+* Ω)) ≫
    Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) = 𝟙 (Spec (CommRingCat.of Ω))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (φ.symm : Ω₂ →+* Ω).comp (φ : Ω →+* Ω₂) = RingHom.id Ω by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

theorem trHom_comp_symm (φ : Ω ≃ₐ[K] Ω₂) : trHom φ ≫ trHom φ.symm = 𝟙 _ := by
  simpa using trHom_symm_comp φ.symm

/-- **Transport of points** along `φ : Ω ≃ₐ[K] Ω₂`. -/
noncomputable def trPt (φ : Ω ≃ₐ[K] Ω₂) : A.Pt Ω ≃* A.Pt Ω₂ where
  toFun p := trHom φ ≫ p
  invFun x := trHom φ.symm ≫ x
  left_inv p := by simp [← Category.assoc, trHom_symm_comp]
  right_inv x := by simp [← Category.assoc, trHom_comp_symm]
  map_mul' p q := MonObj.comp_mul _ _ _

/-- `trPt φ` carries the action of `σ` to that of `φσφ⁻¹`. -/
theorem trPt_galAct (φ : Ω ≃ₐ[K] Ω₂) (σ : Ω ≃ₐ[K] Ω) (σ₂ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, σ₂ (φ x) = φ (σ x)) (p : A.Pt Ω) :
    trPt A φ (A.galAct σ p) = A.galAct σ₂ (trPt A φ p) := by
  show trHom φ ≫ PkgI3.AbVar.galHom σ ≫ p = PkgI3.AbVar.galHom σ₂ ≫ trHom φ ≫ p
  have hsq : trHom φ ≫ PkgI3.AbVar.galHom σ = PkgI3.AbVar.galHom σ₂ ≫ trHom φ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ₂ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, ← Category.assoc, hsq]

end Tr

end UnramTate

end


/-! ## §7c (local-glue). Raynaud's criterion (R6) at the place of `embP`: the rational case

`raynaudPlace_rational` (proved): if `A[m]` is `K`-rational (`m ≥ 3`, `p ∤ m`), the leaf R6
(`ObjBridge.RaynaudCriterion`) gives `RaynaudPlace A m`. The valuation-theoretic bridge is proved:
* `wK`, `OK`: the valuation subrings of `K̄` and `K` at the place of `embP` (norm `≤ 1` after
  `K̄ ≅ ℚ̄ → ℚ̄_p`); `OK` is a DVR (`OK_ne_top` and neron-lg's `isDiscreteValuationRing_of_ne_top`);
* `m`, `ℓ` prime to `p` are units of `OK`;
* a wild `σ'` (over `decomp σ`) lies in the inertia group of `wK` (`isInertia_of_wild`).
The general case of `RaynaudPlace` needs R6 over `K(A[m])` and the base change of `A`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj
open scoped Pointwise

section RaynaudSec

/-- The valuation subring `{x : ‖f x‖ ≤ 1}` for a ring map `f` to an ultrametric normed field. -/
def normVS {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] (f : F →+* E) :
    ValuationSubring F where
  carrier := {x | ‖f x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
  mem_or_inv_mem' x := by
    by_cases h : ‖f x‖ ≤ 1
    · exact Or.inl h
    · right
      show ‖f x⁻¹‖ ≤ 1
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h))

theorem mem_normVS {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] (f : F →+* E)
    (x : F) : x ∈ normVS f ↔ ‖f x‖ ≤ 1 := Iff.rfl

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]

/-- `ℚ̄ ≅ K̄` (`qEmbRing` is bijective). -/
def eK (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective (G0Galois.qEmbRing K)
    ⟨(G0Galois.qEmbRing K).injective, qEmbRing_surjective K⟩

/-- `K̄ ≅ ℚ̄ → ℚ̄_p`, the place of `embP` on `K̄`. -/
def ιbar (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    AlgebraicClosure K →+* Kbar p :=
  (embP (p := p)).comp (eK K).symm.toRingHom

/-- The valuation ring of `K̄` at the place of `embP`. -/
def wK (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    ValuationSubring (AlgebraicClosure K) :=
  normVS (ιbar p K)

/-- The valuation ring of `K` at the place of `embP`. -/
def OK (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] : ValuationSubring K :=
  normVS ((ιbar p K).comp (algebraMap K (AlgebraicClosure K)))

theorem wK_comap : (wK p K).comap (algebraMap K (AlgebraicClosure K)) = OK p K := by
  ext x; exact Iff.rfl

theorem OK_ne_top : OK p K ≠ ⊤ := by
  intro h
  have hmem : ((p : K))⁻¹ ∈ OK p K := by rw [h]; exact ValuationSubring.mem_top _
  rw [OK, mem_normVS] at hmem
  simp only [map_inv₀, map_natCast, norm_inv] at hmem
  rw [norm_p_kbar, inv_inv] at hmem
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

instance OK_dvr : IsDiscreteValuationRing (OK p K) :=
  ZInQ.NeronLG.isDiscreteValuationRing_of_ne_top _ OK_ne_top

/-- A natural number prime to `p` is a unit of `OK`. -/
theorem isUnit_natCast_OK {n : ℕ} (hn : ¬ p ∣ n) : IsUnit ((n : OK p K)) := by
  have hnorm : ‖(n : Kbar p)‖ = 1 := norm_natCast_kbar hn
  have hn0 : (n : K) ≠ 0 := by
    intro h0
    have : (n : Kbar p) = 0 := by
      have := congrArg ((ιbar p K).comp (algebraMap K (AlgebraicClosure K))) h0
      simpa using this
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinv : ((n : K))⁻¹ ∈ OK p K := by
    rw [OK, mem_normVS]
    simp only [map_inv₀, map_natCast, norm_inv, hnorm, inv_one, le_refl]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change ((n : OK p K) : K) * ((n : K))⁻¹ = 1
  rw [show ((n : OK p K) : K) = (n : K) from by simp]
  exact mul_inv_cancel₀ hn0

/-- `ιbar ∘ σ' = σ ∘ ιbar` for `σ'` over `decomp σ` (proved, from `resQ_spec`, `decomp_spec`). -/
theorem ιbar_apply {σ : GQp p} {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (y : AlgebraicClosure K) :
    ιbar p K (σ' y) = σ (ιbar p K y) := by
  obtain ⟨z, rfl⟩ := (eK K).surjective y
  have h1 : σ' (eK K z) = eK K (decomp p σ z) := by
    have := G0Galois.resQ_spec K σ' z
    rw [hσ'] at this
    exact this.symm
  simp only [ιbar, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [h1, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, decomp_spec]

theorem norm_wild_eq {σ : GQp p} (hσ : σ ∈ wildSet) (u : Kbar p) : ‖σ u‖ = ‖u‖ := by
  by_cases hu : u = 0
  · rw [hu, map_zero]
  have h := hσ u hu
  have : σ u = u + (σ u - u) := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h),
    max_eq_left (le_of_lt h)]

/-- **A wild `σ'` lies in the inertia group of `wK` (proved).** -/
theorem isInertia_of_wild {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) : PkgI2.IsInertia (wK p K) σ' := by
  have hnorm : ∀ y, ‖ιbar p K (σ' y)‖ = ‖ιbar p K y‖ := fun y => by
    rw [ιbar_apply hσ', norm_wild_eq hσ]
  have hnorm' : ∀ y, ‖ιbar p K (σ'⁻¹ y)‖ = ‖ιbar p K y‖ := fun y => by
    have := hnorm (σ'⁻¹ y)
    rw [show σ' (σ'⁻¹ y) = y from by
      change (σ' * σ'⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    exact this.symm
  have hdec : σ' ∈ (wK p K).decompositionSubgroup K := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change ‖ιbar p K (σ'⁻¹ x)‖ ≤ 1 ↔ ‖ιbar p K x‖ ≤ 1
    rw [hnorm']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ', hdec⟩ : (wK p K).decompositionSubgroup K) • IsLocalRing.residue (wK p K) a =
    IsLocalRing.residue (wK p K) a
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  set b : wK p K := (⟨σ', hdec⟩ : (wK p K).decompositionSubgroup K) • a - a with hb
  have hbval : (b : AlgebraicClosure K) = σ' a - a := rfl
  have hlt : ‖ιbar p K (b : AlgebraicClosure K)‖ < 1 := by
    rw [hbval, map_sub, ιbar_apply hσ']
    by_cases ha0 : ιbar p K (a : AlgebraicClosure K) = 0
    · rw [ha0, map_zero, sub_zero, norm_zero]; exact zero_lt_one
    · exact lt_of_lt_of_le (hσ _ ha0) a.2
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
  have hc' : ιbar p K (b : AlgebraicClosure K) * ιbar p K (c : AlgebraicClosure K) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hc
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    rw [show ((b * c : wK p K) : AlgebraicClosure K) = (b : AlgebraicClosure K) * c from rfl] at this
    rw [this, map_one]
  have hcn : ‖ιbar p K (c : AlgebraicClosure K)‖ ≤ 1 := c.2
  have := congrArg norm hc'
  rw [norm_mul, norm_one] at this
  have h0 : 0 ≤ ‖ιbar p K (b : AlgebraicClosure K)‖ := norm_nonneg _
  nlinarith

/-- **`RaynaudPlace` when `A[m]` is `K`-rational, from the leaf R6 (proved).** -/
theorem raynaudPlace_rational (hR6 : ObjBridge.RaynaudCriterion) (A : PkgI3.AbVar K) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m)
    (hrat : ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct τ P = P) :
    RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' _ ℓ hℓ hℓp n x hx
  have hℓp' : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  exact hR6 K (OK p K) (wK p K) wK_comap (ObjBridge.toGrp A) m hm3 (isUnit_natCast_OK hpm)
    hrat σ' (isInertia_of_wild hσ hσ') ℓ hℓ (isUnit_natCast_OK hℓp') n x hx

end RaynaudSec


/-! ### The general case: R6 over the field of `A[m]`, via the base change of `A` -/

section RaynaudGen

variable {p : ℕ} [Fact p.Prime]

/-- `normVS f ≠ ⊤` for a map of a field to `ℚ̄_p` (`1/p ∉`). -/
theorem normVS_ne_top {F : Type} [Field F] [CharZero F] (f : F →+* Kbar p) : normVS f ≠ ⊤ := by
  intro h
  have hmem : ((p : F))⁻¹ ∈ normVS f := by rw [h]; exact ValuationSubring.mem_top _
  rw [mem_normVS] at hmem
  simp only [map_inv₀, map_natCast, norm_inv] at hmem
  rw [norm_p_kbar, inv_inv] at hmem
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

/-- A natural number prime to `p` is a unit of `normVS f`. -/
theorem isUnit_natCast_normVS {F : Type} [Field F] (f : F →+* Kbar p) {n : ℕ} (hn : ¬ p ∣ n) :
    IsUnit ((n : normVS f)) := by
  have hnorm : ‖(n : Kbar p)‖ = 1 := norm_natCast_kbar hn
  have hn0 : (n : F) ≠ 0 := by
    intro h0
    have : (n : Kbar p) = 0 := by simpa using congrArg f h0
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinv : ((n : F))⁻¹ ∈ normVS f := by
    rw [mem_normVS]
    simp only [map_inv₀, map_natCast, norm_inv, hnorm, inv_one, le_refl]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change ((n : normVS f) : F) * ((n : F))⁻¹ = 1
  rw [show ((n : normVS f) : F) = (n : F) from by simp]
  exact mul_inv_cancel₀ hn0

/-- **Wild elements are inertial (general form, proved).** If `f ∘ τ = σ ∘ f` with `σ` wild, then
`τ` lies in the inertia group of `normVS f`. -/
theorem isInertia_of_wild_gen {K₀ Ω : Type} [Field K₀] [Field Ω] [Algebra K₀ Ω]
    (f : Ω →+* Kbar p) {σ : GQp p} (hσ : σ ∈ wildSet) (τ : Ω ≃ₐ[K₀] Ω)
    (hf : ∀ y, f (τ y) = σ (f y)) : PkgI2.IsInertia (normVS f) τ := by
  have hnorm : ∀ y, ‖f (τ y)‖ = ‖f y‖ := fun y => by rw [hf, norm_wild_eq hσ]
  have hnorm' : ∀ y, ‖f (τ⁻¹ y)‖ = ‖f y‖ := fun y => by
    have := hnorm (τ⁻¹ y)
    rw [show τ (τ⁻¹ y) = y from by
      change (τ * τ⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    exact this.symm
  have hdec : τ ∈ (normVS f).decompositionSubgroup K₀ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change ‖f (τ⁻¹ x)‖ ≤ 1 ↔ ‖f x‖ ≤ 1
    rw [hnorm']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨τ, hdec⟩ : (normVS f).decompositionSubgroup K₀) • IsLocalRing.residue (normVS f) a =
    IsLocalRing.residue (normVS f) a
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  set b : normVS f := (⟨τ, hdec⟩ : (normVS f).decompositionSubgroup K₀) • a - a with hb
  have hbval : (b : Ω) = τ a - a := rfl
  have hlt : ‖f (b : Ω)‖ < 1 := by
    rw [hbval, map_sub, hf]
    by_cases ha0 : f (a : Ω) = 0
    · rw [ha0, map_zero, sub_zero, norm_zero]; exact zero_lt_one
    · exact lt_of_lt_of_le (hσ _ ha0) a.2
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
  have hc' : f (b : Ω) * f (c : Ω) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hc
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    rw [show ((b * c : normVS f) : Ω) = (b : Ω) * c from rfl] at this
    rw [this, map_one]
  have hcn : ‖f (c : Ω)‖ ≤ 1 := c.2
  have := congrArg norm hc'
  rw [norm_mul, norm_one] at this
  have h0 : 0 ≤ ‖f (b : Ω)‖ := norm_nonneg _
  nlinarith

variable {K : Type} [Field K] [NumberField K]

/-- The stabilizer of `A(K̄)[m]` in `G_K`. -/
def torsStab (A : PkgI3.AbVar K) (m : ℕ) :
    Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  carrier := {τ | ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct τ P = P}
  mul_mem' {a b} ha hb P hP := by
    rw [← galAct_galAct, hb P hP, ha P hP]
  one_mem' P _ := by
    change PkgI3.AbVar.galHom 1 ≫ P = P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  inv_mem' {a} ha P hP := by
    calc A.galAct a⁻¹ P = A.galAct a⁻¹ (A.galAct a P) := by rw [ha P hP]
      _ = P := galAct_inv_galAct A a P

/-- The stabilizer of `A[m]` contains `G_{F'}` for a finite `F'/K` (from `ptFinite`, `A[m]`
finite by I2-Tors). -/
theorem exists_fin_le_torsStab (A : PkgI3.AbVar K) (m : ℕ) [NeZero m] (hT : TorsGL A m) :
    ∃ F' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K F' ∧
      F'.fixingSubgroup ≤ torsStab A m := by
  obtain ⟨e, -⟩ := hT
  haveI : Finite {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} := Finite.of_equiv _ e.symm
  choose F hF hP using fun P : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} => ptFinite A P.1
  haveI : ∀ i, FiniteDimensional K (F i) := hF
  refine ⟨⨆ i, F i, inferInstance, fun τ hτ P hPm => ?_⟩
  refine hP ⟨P, hPm⟩ τ (fun x hx => ?_)
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
  exact hτ x ((le_iSup F ⟨P, hPm⟩) hx)

/-- **`RaynaudPlace` from the leaves R6 and I2-Tors (proved), for `dim A = 2`, `3 ≤ m`,
`p ∤ m`.** R6 is applied over `F = K(A[m])` (the fixed field of the stabilizer of `A[m]`, finite
by `ptFinite`) to the base change `A_F`, with the valuation rings at the place of `embP`
transported along `K̄ ≅ F̄`; points of `A_F` are those of `A` (`bcPt`, `trPt`, copied from
scratch/unram-tate). -/
theorem raynaudPlace_of_R6 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m) : RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' hfix ℓ hℓ hℓp n x hx
  set σg : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ' with hσg
  haveI : NeZero m := ⟨by omega⟩
  set H := torsStab A m with hHdef
  obtain ⟨F', hF'fd, hF'H⟩ := exists_fin_le_torsStab A m (torsGL_of_leaf hTors A hdim m (by omega))
  have hHopen : IsOpen (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isOpen_mono hF'H (IntermediateField.fixingSubgroup_isOpen F')
  have hHclosed : IsClosed (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isClosed_of_isOpen H hHopen
  set F : IntermediateField K (AlgebraicClosure K) := IntermediateField.fixedField H with hFdef
  have hFH : F.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hFF' : F ≤ F' := by
    intro y hy
    rw [← InfiniteGalois.fixedField_fixingSubgroup F']
    rw [IntermediateField.mem_fixedField_iff] at hy ⊢
    exact fun τ hτ => hy τ (hF'H hτ)
  haveI : FiniteDimensional K F :=
    Module.Finite.of_injective (IntermediateField.inclusion hFF').toLinearMap
      (IntermediateField.inclusion hFF').injective
  haveI : FiniteDimensional ℚ F := Module.Finite.trans K F
  haveI : NumberField F := ⟨⟩
  -- `σ'` fixes `F`
  have hσ'F : ∀ y ∈ F, σg y = y := fun y hy =>
    ((IntermediateField.mem_fixedField_iff _ _).mp hy) σg hfix
  have hℓp' : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  -- `K̄` is an algebraic closure of `F`
  haveI : IsAlgClosure F (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) (L := F) (A := AlgebraicClosure K)⟩
  let Ω := AlgebraicClosure F
  let ψ : Ω ≃ₐ[F] AlgebraicClosure K := IsAlgClosure.equiv F Ω (AlgebraicClosure K)
  let σF : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K :=
    { σg.toRingEquiv with commutes' := fun c => hσ'F c c.2 }
  let σ₁ : Ω ≃ₐ[F] Ω := (ψ.trans σF).trans ψ.symm
  have hσ₁ : ∀ y, ψ (σ₁ y) = σg (ψ y) := fun y => by
    simp only [σ₁, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    rfl
  let f₁ : Ω →+* Kbar p := (ιbar p K).comp (ψ : Ω →+* AlgebraicClosure K)
  have hf₁ : ∀ y, f₁ (σ₁ y) = σ (f₁ y) := fun y => by
    change ιbar p K (ψ (σ₁ y)) = σ (ιbar p K (ψ y))
    rw [hσ₁ y]
    exact ιbar_apply (σ' := σg) hσ' (ψ y)
  let w₁ : ValuationSubring Ω := normVS f₁
  let O₁ : ValuationSubring F := normVS (f₁.comp (algebraMap F Ω))
  have hw₁ : w₁.comap (algebraMap F Ω) = O₁ := by ext; exact Iff.rfl
  haveI : IsDiscreteValuationRing O₁ :=
    ZInQ.NeronLG.isDiscreteValuationRing_of_ne_top _ (normVS_ne_top _)
  -- points of `A_F` over `Ω` are points of `A` over `K̄`
  let A₁ : PkgI3.AbVar F := A.baseChange F
  let ψK : Ω ≃ₐ[K] AlgebraicClosure K := ψ.restrictScalars K
  let Φ : A₁.Pt Ω ≃* A.Pt (AlgebraicClosure K) :=
    (UnramTate.bcPt A Ω).trans (UnramTate.trPt A ψK)
  have hΦ : ∀ (τ₁ : Ω ≃ₐ[F] Ω) (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      (∀ y, τ (ψ y) = ψ (τ₁ y)) → ∀ z, Φ (A₁.galAct τ₁ z) = A.galAct τ (Φ z) := by
    intro τ₁ τ h z
    change UnramTate.trPt A ψK (UnramTate.bcPt A Ω (A₁.galAct τ₁ z)) =
      A.galAct τ (UnramTate.trPt A ψK (UnramTate.bcPt A Ω z))
    rw [UnramTate.bcPt_galAct, UnramTate.trPt_galAct A ψK (τ₁.restrictScalars K) τ h]
  have hrat : ∀ τ₁ : Ω ≃ₐ[F] Ω, ∀ z ∈ PkgI2.torsion (ObjBridge.toGrp A₁) Ω m,
      PkgI2.galAct (ObjBridge.toGrp A₁) τ₁ z = z := by
    intro τ₁ z₀ hz
    let z : A₁.Pt Ω := z₀
    change A₁.galAct τ₁ z = z
    let τF : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K := (ψ.symm.trans τ₁).trans ψ
    let τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τF.restrictScalars K
    have hτ : ∀ y, τ (ψ y) = ψ (τ₁ y) := fun y => by
      change ψ (τ₁ (ψ.symm (ψ y))) = ψ (τ₁ y)
      rw [AlgEquiv.symm_apply_apply]
    have hτH : τ ∈ H := by
      rw [← hFH, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact τF.commutes ⟨y, hy⟩
    have hz' : z ^ m = 1 := hz
    have hzm : (Φ z) ^ m = 1 := by rw [← map_pow, hz', map_one]
    have h1 := hΦ τ₁ τ hτ z
    rw [hτH (Φ z) hzm] at h1
    exact Φ.injective h1
  have hxm : (Φ.symm x) ^ (ℓ ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hU := hR6 F O₁ w₁ hw₁ (ObjBridge.toGrp A₁) m hm3 (isUnit_natCast_normVS _ hpm) hrat σ₁
    (isInertia_of_wild_gen f₁ hσ σ₁ hf₁) ℓ hℓ (isUnit_natCast_normVS _ hℓp') n (Φ.symm x) hxm
  have hU' : A₁.galAct σ₁ (A₁.galAct σ₁ (Φ.symm x)) * (A₁.galAct σ₁ (Φ.symm x))⁻¹ *
      (A₁.galAct σ₁ (Φ.symm x))⁻¹ * Φ.symm x = 1 := hU
  have hcomm : ∀ z, Φ (A₁.galAct σ₁ z) = A.galAct σg (Φ z) :=
    hΦ σ₁ σg (fun y => (hσ₁ y).symm)
  have h2 := congrArg Φ hU'
  simp only [map_one, map_mul, map_inv, hcomm, MulEquiv.apply_symm_apply] at h2
  exact h2

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaves R6 and I2-Tors alone (proved).**
`m = 3` for `p ≠ 13`, `m = 7` for `p = 13` (`raynaudPlace_of_R6`, `tateWildK_of_raynaud`). -/
theorem tateWildK_of_R6 (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    {A : PkgI3.AbVar K} (hdim : A.dim = 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p) :
    TateWildK (p := p) A ℓ := by
  have hp : p.Prime := Fact.out
  refine tateWildK_of_raynaud hℓp h7 hTors hdim (fun _ => raynaudPlace_of_R6 hR6 hTors A hdim
    (by norm_num) ?_) (fun h13 => raynaudPlace_of_R6 hR6 hTors A hdim (by norm_num) ?_)
  · intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · intro h
    rw [h13] at h
    norm_num at h

end RaynaudGen

end G15Ram

end


noncomputable section

/-! ## §8 (local-glue). The packs: G8's data with the local glue replaced by Props on `A/K`

`G8LocalPack` is copied verbatim from scratch/local-data/tail_part.lean (the hypothesis of
local-data's tail `modularConstituent_tail_L`). `G7LocalPackK` asks instead for G7's data
(`G7Out`), G8's output, the clauses, `KerWild`, and the torsion-point Props `TorsFixWild`
(`p ≥ 7`), `TorsFixWildE` (`p ≤ 5`) and `BetaUpper` (`p = 2`) at the primes in `P`. -/

namespace G0ModNewform

open PkgI4 (Qbar GQ GaloisRep)
open PkgI3


/-- **G7's data for `r` at coefficient prime `ℓ`, with the local glue at `p ∈ P` as Props on the
abelian surface `A/K` (GLUE).** -/
def G7LocalPackK (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (7 ≤ p → @G15Ram.TorsFixWild p ⟨hp⟩ K _ _ A ℓ _) ∧
      (p ≤ 5 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L) ∧
      (p = 2 → @G15Ram.BetaUpper p ⟨hp⟩ ℓ _ β (@G15Ram.Lv p ⟨hp⟩ L) U0)

/-- **`G8LocalPack` from `G7LocalPackK` (proved)**, by `G15Ram.localGlue_of_g7`. -/
theorem g8LocalPack_of_K {ℓ : ℕ} [Fact ℓ.Prime] {r : GaloisRep ℓ 2} {P : ℕ → Prop}
    (h : G7LocalPackK ℓ r P) : G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hW, hE, hB⟩ := hloc p hp hP
  exact G15Ram.localGlue_of_g7 h7 hC hK (fun h => G15Ram.tateWildK_of_torsFixWild (hW h))
    (fun h => G15Ram.tateWildKE_of_torsFixWildE (hE h)) hB

/-- **G15's open Prop `G15RamG` from the packs (proved)**: g15-ram's `G15RamG D u` follows from
G7's data for `D.r5` (local glue at `p ≠ 5`) and for `D.r3` (at `p = 5`), and G11's outputs. -/
theorem g15RamG_of_packK {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (u : ℚ) (h5 : G7LocalPackK 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackK 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ := g8LocalPack_of_K h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ := g8LocalPack_of_K h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` in leaf form (GLUE).**
At `p ≥ 7` nothing: the local glue there follows from the leaves R6 and I2-Tors
(`G15Ram.raynaudPlace_of_R6`, `G15Ram.ptFinite`); at
`p ∈ {3, 5}`: `TorsFixWildOdd`; at `p = 2`: `TorsFixWildE` and `BetaTwist2` (which replaces
`BetaUpper`, `G15Ram.betaUpper_of_twist`). With the leaves R6 and
I2-Tors and `p ≠ ℓ` on `P`, it gives `G7LocalPackK` (`g7LocalPackK_of_R`). -/
def G7LocalPackR (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (3 ≤ p → p ≤ 5 → @G15Ram.TorsFixWildOdd p ⟨hp⟩ K _ _ A ℓ _ L) ∧
      (p = 2 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L ∧ @G15Ram.BetaTwist2 p ⟨hp⟩ ℓ _ β L)

/-- **`G7LocalPackK` from `G7LocalPackR`, the leaf I2-Tors and `p ≠ ℓ` on `P` (proved).** -/
theorem g7LocalPackK_of_R (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackR ℓ r P) :
    G7LocalPackK ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hO, h2⟩ := hloc p hp hP
  refine ⟨fun h7p => ?_, fun h5 => ?_, fun h2' => G15Ram.betaUpper_of_twist hC (h2 h2').2⟩
  · exact G15Ram.torsFixWild_of_raynaud (Ne.symm (hPℓ p hP)) h7p
      (G15Ram.wildIter A) (G15Ram.torsGL_of_leaf hTors A h7.1 3 (by norm_num))
      (G15Ram.torsGL_of_leaf hTors A h7.1 7 (by norm_num))
      (fun _ => G15Ram.raynaudPlace_of_R6 hR6 hTors A h7.1 (by norm_num)
        (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
      (fun h13 => G15Ram.raynaudPlace_of_R6 hR6 hTors A h7.1 (by norm_num)
        (by rw [h13]; norm_num))
  · by_cases hp2 : p = 2
    · exact (h2 hp2).1
    · have h3 : 3 ≤ p := by have := hp.two_le; omega
      exact G15Ram.torsFixWildE_of_odd hp2 hC (hO h3 h5)

/-- **`G15RamG` from the leaf-and-bridge packs and I2-Tors (proved).** -/
theorem g15RamG_of_packR (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackR 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackR 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u :=
  g15RamG_of_packK D u (g7LocalPackK_of_R hR6 hTors (fun _ h => h) h5)
    (g7LocalPackK_of_R hR6 hTors (fun p h => by rw [h]; norm_num) h3) h11₅ h11₃

end G0ModNewform

end


/-! ## §9 (local-glue). The tail of `ModularConstituent` with the local glue on `A/K` (proved) -/

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves C9Rhof
open CategoryTheory AlgebraicGeometry

/-- **G13-G16 with G15 fed by G7's data and the local glue as Props on `A/K` (GLUE, proved).**
As local-data's `modularConstituent_tail_L`, with `G8LocalPack` replaced by `G7LocalPackK`
(`g8LocalPack_of_K`). -/
theorem modularConstituent_tail_K (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧
      G7LocalPackK 5 D.r5 (fun p => p ≠ 5) ∧ G7LocalPackK 3 D.r3 (fun p => p = 5) ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5 ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, h5, h3, h11a, h11b⟩ := h
  exact modularConstituent_tail_L lv hJac hX hSw hL8 hAd A u
    ⟨D, h12, hc, g8LocalPack_of_K h5, g8LocalPack_of_K h3, h11a, h11b⟩

/-- **G13-G16 with the local glue in leaf-and-bridge form (GLUE, proved).** As
`modularConstituent_tail_K`, with `G7LocalPackR` and the leaves R6, I2-Tors (`g7LocalPackK_of_R`). -/
theorem modularConstituent_tail_R (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧
      G7LocalPackR 5 D.r5 (fun p => p ≠ 5) ∧ G7LocalPackR 3 D.r3 (fun p => p = 5) ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5 ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, h5, h3, h11a, h11b⟩ := h
  exact modularConstituent_tail_K lv hJac hX hSw hL8 hAd A u
    ⟨D, h12, hc, g7LocalPackK_of_R hR6 hTors (fun _ h => h) h5,
      g7LocalPackK_of_R hR6 hTors (fun p h => by rw [h]; norm_num) h3, h11a, h11b⟩

end G0ModNewform

#print axioms G0ModNewform.modularConstituent_tail_K
#print axioms G0ModNewform.modularConstituent_tail_R
