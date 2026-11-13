import ZInQKernel.HDecomp.ModCurves.Glue
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.I3Linalg.RhoCont

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
  induction x using TensorProduct.induction_on with
  | zero => simp
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
  induction x using TensorProduct.induction_on with
  | zero => simpa using continuous_const
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
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_setOf_eq] at this
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
    (hatt : ∀ p, p.Prime → p ∉ S → ∃ α : Qbar, ιC α = coeff f p ∧
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
  obtain ⟨α, hα, hrα⟩ := hatt p hp hpS
  rw [hrα v τ hv hτ]
  exact (embOf_spec ℓ ιC ιL (coeffField f) _ α hα).symm

end C9

end C9Rhof
