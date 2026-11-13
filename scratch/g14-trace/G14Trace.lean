import ZInQKernel.HDecomp.ModCurves.Glue
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.I3Linalg.RhoCont
import ZInQKernel.HDecomp.I3Linalg.TateBC
import ZInQKernel.HDecomp.Conductor.Level
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.HDecomp.C10.Link
import ZInQKernel.Main

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

/-! Copied verbatim from scratch/g0-mod-newform/part_new.lean. -/
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

/-!
# g14-trace: `G14TraceCompat` (r₃ and r₅ in one compatible system), reduced

`G0ModNewform.G14TraceCompat D` (copied verbatim above, from `scratch/g0-mod-newform/`) is a
statement about the data `D : ModData L A`. It is proved here for the data that G8 constructs
(g0-mod-galois' `G8Out`, copied above as `GalG8Out`) from the descended operators
`ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` (`GlueDescent.rho`), from:

* the leaf T7 (`PkgI3.CharPolyIndepOfEll`, Mumford §19 Thm 4);
* the AV-side glue Prop `FrobTraceLink A Tm₅ Tm₃` (N5 L781-786: at a Frobenius `τ` above
  `p ∉ S`, `N·Tm_ℓ(τ)` is conjugate to `V_ℓ(α')` for one endomorphism `α'` of an abelian variety
  over a field of characteristic `p`, at `ℓ = 3` and `ℓ = 5`; the kernel's
  `GlueC10Link.FrobCompare`), or its square form `FrobSquaresLink` (the kernel's
  `GlueC10Link.FrobSquares`: Galois transport, Serre–Tate reduction, Néron mapping);
* the scalar link: `a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β` for one pair `a, β : G_ℚ → ℚ̄` (N5 L719-722:
  the scalars lie in the coefficient field `C` and are mapped to `ℚ̄_ℓ` by embeddings).

§1 proves that the scalar link is needed: G8's inputs at one `ℓ` (`G7Out`) are preserved by
twisting `a` by a character of `G_ℚ` trivial on `G_{L'}`, which multiplies the traces of `ρ_ℓ`
by the character. So `G14TraceCompat` does not follow from `G7Out` at `3` and at `5` separately
(the form in which g0-mod-field's `TateBridge` delivers them).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace G14Trace

open PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisRep)
open PkgI3 G0ModNewform GlueC10Link

/-! ## §1. G7Out at one `ℓ` does not fix the traces: twisting `a` (proved) -/

section Twist

variable {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]

/-- (copied from g0-mod-galois, `part_galois.lean`, as in g0-mod-field's `GaloisCopy`)
G7's output at the coefficient prime `ℓ`. -/
def G7Out (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
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

/-- **Twisting G7's output (proved).** If `χ : G_ℚ → ℚ̄_ℓ^×` is a continuous character trivial on
`G_K` (a character of `Gal(K/ℚ)`), then `(Tm, c, ε, χ·a, β, u)` satisfies `G7Out` whenever
`(Tm, c, ε, a, β, u)` does. -/
theorem g7Out_twist (Tm : GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : GQ → GQ → PadicAlgCl ℓ) (a β : GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) (h : G7Out A ℓ Tm c ε a β u)
    (χ : GQ →* (PadicAlgCl ℓ)ˣ) (hχc : Continuous χ) (hχ : ∀ σ, χ (resQ K σ) = 1) :
    G7Out A ℓ Tm c ε (fun g => (χ g : PadicAlgCl ℓ) * a g) β u := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, fun g k => ?_, h5, h6, fun σ => ?_, h8, fun f v => ?_⟩
  · rw [map_mul, Units.val_mul]
    linear_combination (χ g : PadicAlgCl ℓ) * (χ k) * h4 g k
  · obtain ⟨t1, t2, t3⟩ := h7 σ
    exact ⟨t1, by rw [t2, hχ σ]; simp, t3⟩
  · have hc : Continuous fun g => (χ g : PadicAlgCl ℓ) :=
      Units.continuous_val.comp hχc
    have : (fun g => f (GlueDescent.rho Tm (fun g => (χ g : PadicAlgCl ℓ) * a g) β g v)) =
        fun g => (χ g : PadicAlgCl ℓ) * f (GlueDescent.rho Tm a β g v) := by
      funext g
      simp only [GlueDescent.rho, LinearMap.smul_apply, map_smul, smul_eq_mul]
      ring
    rw [this]
    exact hc.mul (h9 f v)

/-- The twist multiplies the traces of `ρ = β⁻¹ a Tm` by `χ`. -/
theorem trace_rho_twist (Tm : GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (a β : GQ → PadicAlgCl ℓ) (χ : GQ → PadicAlgCl ℓ) (g : GQ) :
    LinearMap.trace _ _ (GlueDescent.rho Tm (fun g => χ g * a g) β g) =
      χ g * LinearMap.trace _ _ (GlueDescent.rho Tm a β g) := by
  rw [trace_rho, trace_rho]
  ring

end Twist

/-! ## §2. Traces through G8's intertwining (proved) -/

/-- If `e : V ≃ ℚ̄_ℓ² × ℚ̄_ℓ²` intertwines `f g` with `m g ⊕ m g`, then `tr f(g) = 2 tr m(g)`. -/
theorem trace_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (f : G → Module.End (PadicAlgCl ℓ) V)
    (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : Intertwines f m e) (g : G) :
    LinearMap.trace (PadicAlgCl ℓ) V (f g) = 2 * (m g).trace := by
  haveI : Module.Finite (PadicAlgCl ℓ) V := Module.Finite.equiv e.symm
  have hconj : e.conj (f g) = LinearMap.prodMap (Matrix.toLin' (m g)) (Matrix.toLin' (m g)) := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h g, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply, Matrix.toLin'_apply]
  rw [← LinearMap.trace_conj' (f g) e, hconj, LinearMap.trace_prodMap', Matrix.trace_toLin'_eq]
  ring

/-- One coefficient prime: if `N·tr T = t` and `tr(β⁻¹ a T) = 2 tr m` (images of
`a, β ∈ ℚ̄` under `j`), then `tr m = j(½ β⁻¹ a t/N)`. -/
theorem trace_eq_image {ℓ : ℕ} [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] (T : Module.End (PadicAlgCl ℓ) V) (a β : Qbar)
    (N : ℕ) (hN : N ≠ 0) (t : ℤ) (hNT : (N : PadicAlgCl ℓ) * LinearMap.trace _ V T = t)
    (m : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (h2 : LinearMap.trace _ V (((j β)⁻¹ * j a) • T) = 2 * m.trace) :
    m.trace = j ((β)⁻¹ * a * ((t : Qbar) / N) / 2) := by
  have hNE : (N : PadicAlgCl ℓ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hT : LinearMap.trace _ V T = (t : PadicAlgCl ℓ) / N := by
    rw [eq_div_iff hNE, mul_comm, hNT]
  rw [map_smul, smul_eq_mul, hT] at h2
  rw [map_div₀, map_mul, map_mul, map_inv₀, map_div₀, map_intCast, map_natCast, map_ofNat]
  linear_combination (-1 / 2 : PadicAlgCl ℓ) * h2

/-! ## §3. The AV-side glue Props -/

/-- **The Frobenius trace link (GLUE, AV side; N5 L781-786).** There is a finite set `S` of
primes such that at every arithmetic Frobenius `τ` above `p ∉ S` there are an abelian variety
`Ā` over a field `k` of characteristic `p`, an endomorphism `α'` of `Ā` and `N ≠ 0` with
`FrobCompare` (kernel, `GlueC10Link`) at `ℓ = 3` and at `ℓ = 5`: some isomorphism
`ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ ⊗ V_ℓ(Ā)` carries `N·Tm_ℓ(τ)` to `V_ℓ(α')`. In N5, `S = T ∪ {3, 5}`
(`T` = bad primes of `A/L'`), `Ā` is the reduction of `A` at the place `v ∩ L'`, `α' = N·(μ̄_τ ∘ F)`
(relative `p`-Frobenius `F`, reduction `μ̄_τ` of the isogeny `μ_τ : {}^τA → A`), and the
isomorphism is the Serre–Tate reduction isomorphism. It concerns the operators `Tm_ℓ` that
g0-mod-field's `TateBridge` builds from the points-level `m_σ = μ_σ ∘ σ` (one `m_σ` for all `ℓ`). -/
def FrobTraceLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p →
    ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab)
      (N : ℕ), N ≠ 0 ∧ FrobCompare 3 (Tm3 τ) α N ∧ FrobCompare 5 (Tm5 τ) α N

/-- **The Frobenius link in square form (GLUE, AV side; N5 L781-786).** As `FrobTraceLink`, with
`FrobCompare` replaced by its three inputs (kernel, `GlueC10Link.FrobSquares`): abelian
varieties `A₀, Aσ` over a field `L` (`A₀ = A`, `Aσ = {}^τA`), an isogeny `μ' : Aσ → A₀`
(`N μ_τ`), abelian varieties `Ā, Ā'` over `k` of characteristic `p` (`Ā = Ā_v`,
`Ā' = Ā^{(p)}`), the relative Frobenius `F : Ā → Ā'` and the reduction `μ̄' : Ā' → Ā` of `μ'`,
with the three squares (descent instantiation `N·Tm_ℓ(τ) = μ' ∘ τ_*`; Serre–Tate
`red' ∘ τ_* = V_ℓ(F) ∘ red`; Néron mapping `red ∘ V_ℓ(μ') = V_ℓ(μ̄') ∘ red'`) at `ℓ = 3, 5`. -/
def FrobSquaresLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p →
    ∃ (L : Type) (_ : Field L) (k : Type) (_ : Field k), CharP k p ∧
      ∃ (A₀ Aσ : PkgI3.AbVar L) (mu : PkgI3.AbVar.Hom Aσ A₀) (Ab Ab' : PkgI3.AbVar k)
        (F : PkgI3.AbVar.Hom Ab Ab') (mub : PkgI3.AbVar.Hom Ab' Ab) (N : ℕ), N ≠ 0 ∧
        FrobSquares 3 mu F mub (Tm3 τ) N ∧ FrobSquares 5 mu F mub (Tm5 τ) N

/-- `FrobSquaresLink ⇒ FrobTraceLink` (proved, kernel's `frobCompare_of_frobSquares`). -/
theorem frobTraceLink_of_squares {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (h : FrobSquaresLink A Tm5 Tm3) :
    FrobTraceLink A Tm5 Tm3 := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun p hp hpS v τ hv hτ => ?_⟩
  obtain ⟨L, _, k, _, hk, A₀, Aσ, mu, Ab, Ab', F, mub, N, hN, h3, h5⟩ := hS p hp hpS v τ hv hτ
  exact ⟨k, inferInstance, hk, Ab, homComp F mub, N, hN,
    frobCompare_of_frobSquares 3 mu F mub (Tm3 τ) N h3,
    frobCompare_of_frobSquares 5 mu F mub (Tm5 τ) N h5⟩

/-! ## §4. One algebraic number for both traces (proved from T7) -/

/-- **The common trace (GLUE, proved from T7, `FrobTraceLink` and the scalar link).** With
`ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ`, `a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β`, and G8's intertwining of `ρ_ℓ` with
`r_ℓ ⊕ r_ℓ` at `ℓ = 3, 5`: outside a finite set, at every arithmetic Frobenius `τ`, the traces of
`r₅(τ)` and `r₃(τ)` are `j₅(x)` and `j₃(x)` for one `x = ½ β(τ)⁻¹ a(τ) tr(α')/N ∈ ℚ̄`. -/
theorem common_trace (hM : CharPolyIndepOfEll) {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2)
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3)
    (hF : FrobTraceLink A Tm5 Tm3) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (r5.mat τ).trace = j5 x ∧ (r3.mat τ).trace = j3 x := by
  obtain ⟨S, hS⟩ := hF
  obtain ⟨-, e5, he5, -⟩ := h5
  obtain ⟨-, e3, he3, -⟩ := h3
  haveI : Module.Finite (PadicAlgCl 5) (Vb A 5) := Module.Finite.equiv e5.symm
  haveI : Module.Finite (PadicAlgCl 3) (Vb A 3) := Module.Finite.equiv e3.symm
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
  have hp3 : p ≠ 3 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  have hp5 : p ≠ 5 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  obtain ⟨k, _, hk, Ab, α, N, hN, hc3, hc5⟩ := hS p hp hpS1 v τ hv hτ
  obtain ⟨t, ht⟩ := trace_T_of_frobCompare hM Ab α
  have hk3 : ((3 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp Nat.prime_three hp3
  have hk5 : ((5 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp (by norm_num) hp5
  have t5 := ht 5 hk5 (Tm5 τ) N hc5
  have t3 := ht 3 hk3 (Tm3 τ) N hc3
  refine ⟨(β τ)⁻¹ * a τ * ((t : Qbar) / N) / 2, ?_, ?_⟩
  · refine trace_eq_image j5 (Tm5 τ) (a τ) (β τ) N hN t t5 (r5.mat τ) ?_
    exact trace_of_intertwines _ r5.mat e5 he5 τ
  · refine trace_eq_image j3 (Tm3 τ) (a τ) (β τ) N hN t t3 (r3.mat τ) ?_
    exact trace_of_intertwines _ r3.mat e3 he3 τ

/-! ## §5. Choosing `ι₃` compatibly with Pan's `ι₅` (proved) -/

/-- Any two `ℚ`-embeddings of `ℚ̄` into a field differ by an endomorphism of `ℚ̄`:
`ι = j ∘ γ` (`ι(x)` is a root of the minimal polynomial of `x`, which splits in `j(ℚ̄)`). -/
theorem exists_comp_eq {F : Type*} [Field F] [Algebra ℚ F] (ι j : Qbar →ₐ[ℚ] F) :
    ∃ γ : Qbar →ₐ[ℚ] Qbar, ι = j.comp γ := by
  have hmem : ∀ x : Qbar, ∃ y : Qbar, j y = ι x := by
    intro x
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    set P := minpoly ℚ x with hP
    have hP0 : P.map (algebraMap ℚ Qbar) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have hroot : ((P.map (algebraMap ℚ Qbar)).map (j : Qbar →+* F)).IsRoot (ι x) := by
      rw [Polynomial.map_map, j.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    obtain ⟨y, hy⟩ := (IsAlgClosed.splits (P.map (algebraMap ℚ Qbar))).mem_range_of_isRoot hP0 hroot
    exact ⟨y, hy⟩
  choose γf hγf using hmem
  have hj : Function.Injective j := j.toRingHom.injective
  refine ⟨{ toFun := γf
            map_one' := hj (by rw [hγf, map_one, map_one])
            map_mul' := fun x y => hj (by rw [hγf, map_mul, map_mul, hγf, hγf])
            map_zero' := hj (by rw [hγf, map_zero, map_zero])
            map_add' := fun x y => hj (by rw [hγf, map_add, map_add, hγf, hγf])
            commutes' := fun q => hj (by rw [hγf, AlgHom.commutes, AlgHom.commutes]) }, ?_⟩
  ext x
  exact (hγf x).symm

/-- **`G14TraceCompat` from the common trace (GLUE, proved).** If the traces of `r₅`, `r₃` at
Frobenius are `j₅(x)`, `j₃(x)`, and `ι₅ = j₅ ∘ γ`, `ι₃ = j₃ ∘ γ`, then `G14TraceCompat` holds for
any data with these `ι₅, ι₃, r₅, r₃`. -/
theorem g14TraceCompat_of_common {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (γ : Qbar →ₐ[ℚ] Qbar) (h5 : D.ι5 = j5.comp γ) (h3 : D.ι3 = j3.comp γ)
    (h : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (D.r5.mat τ).trace = j5 x ∧ (D.r3.mat τ).trace = j3 x) :
    G14TraceCompat D := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun p hp hpS v τ hv hτ c hc => ?_⟩
  obtain ⟨x, hx5, hx3⟩ := hS p hp hpS v τ hv hτ
  have hxc : x = γ c := by
    apply j5.toRingHom.injective
    change j5 x = j5 (γ c)
    rw [← hx5, hc, h5, AlgHom.comp_apply]
  rw [hx3, hxc, h3, AlgHom.comp_apply]

/-- **G14TraceCompat on G8's construction (GLUE, proved from T7, `FrobTraceLink` and the scalar
link).** For data `D` whose `r₅`, `r₃` are G8's outputs on `ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` with
`a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β`, and whose embeddings are `ι₅ = j₅ ∘ γ`, `ι₃ = j₃ ∘ γ`. -/
theorem g14TraceCompat_of_link (hM : CharPolyIndepOfEll) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3) (γ : Qbar →ₐ[ℚ] Qbar) (hι5 : D.ι5 = j5.comp γ)
    (hι3 : D.ι3 = j3.comp γ) (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3))
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) D.r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) D.r3)
    (hF : FrobTraceLink A Tm5 Tm3) : G14TraceCompat D :=
  g14TraceCompat_of_common D j5 j3 γ hι5 hι3
    (common_trace hM A j5 j3 a β Tm5 Tm3 D.r5 D.r3 h5 h3 hF)

/-! ## §6. With G12: data satisfying both `G12Spec` and `G14TraceCompat` (proved) -/

/-- **`G12Spec D ∧ G14TraceCompat D` from G8 at `3` and `5`, G12 at `5`, T7, `FrobTraceLink` and
the scalar link (GLUE, proved; with g0-mod-newform's `DirichletOfFinite`).** The embedding
`ι₅` is the one from Pan's output (`g12Spec_of_galois`); `ι₃ := j₃ ∘ γ` where `ι₅ = j₅ ∘ γ`
(`exists_comp_eq`). The data keep G8's `r₅`, `r₃`. -/
theorem g12Spec_g14_of_galois (hDF : DirichletOfFinite) (hM : CharPolyIndepOfEll) {K : Type}
    [Field K] [NumberField K] (A : PkgI3.AbVar K) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3) (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2)
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3)
    (h12 : GalG12Out r5) (hF : FrobTraceLink A Tm5 Tm3) :
    ∃ D : ModData K A, D.r5 = r5 ∧ D.r3 = r3 ∧ G12Spec D ∧ G14TraceCompat D := by
  obtain ⟨i, ιC, ι5, hspec⟩ := g12Spec_of_galois hDF A _ _ r5 r3 h5 h3 h12
  obtain ⟨γ, hγ⟩ := exists_comp_eq ι5 j5
  refine ⟨⟨i, ιC, ι5, j3.comp γ, r5, r3⟩, rfl, rfl, hspec _, ?_⟩
  exact g14TraceCompat_of_link hM _ j5 j3 γ hγ rfl a β Tm5 Tm3 h5 h3 hF

end G14Trace

end

#print axioms G14Trace.g7Out_twist
#print axioms G14Trace.trace_rho_twist
#print axioms G14Trace.trace_of_intertwines
#print axioms G14Trace.trace_eq_image
#print axioms G14Trace.frobTraceLink_of_squares
#print axioms G14Trace.common_trace
#print axioms G14Trace.exists_comp_eq
#print axioms G14Trace.g14TraceCompat_of_common
#print axioms G14Trace.g14TraceCompat_of_link
#print axioms G14Trace.g12Spec_g14_of_galois
