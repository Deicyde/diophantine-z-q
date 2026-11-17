import ZInQKernel.OneProof.H.TailE
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.Contrib.AVB1.AlgClosed

/-!
# homfree-proof: Mumford §19 Thm 3 for abelian varieties over fields that embed into `ℂ`

From the bundle fields `uniformizationLeafAll` (AN3, `A(ℂ) ≅ ℂ^g/Λ`) and `mumfordTorsionAlgClosed`
(Mumford §4 App. 2 (iv)) only.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.OneProof.HomFreeC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ZInQ.LeafPush2 (CPts IsUniformization)

variable {K : Type} [Field K]

/-! ## 1. A homomorphism killing all complex points is zero -/

/-- **A homomorphism of abelian varieties over `K` that is trivial on `A(ℂ)_σ` is zero (proved).**
Base change to `ℂ` along `σ` (`bcHom` is injective), then Mathlib's `ext_of_apply_eq` over `ℂ`
(hom-unify's `hom_ext_of_cpts`). -/
theorem hom_eq_zero_of_cpts (σ : K →+* ℂ) {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B)
    (h : ∀ p : CPts A σ, p ≫ f.hom = 1) : f = 0 := by
  letI : Algebra K ℂ := σ.toAlgebra
  have hC : ZInQ.Contrib.AVB1.bcHom ℂ A B f = 0 := by
    apply PkgI3.AbVar.Hom.ext'
    apply ZInQ.HomUnify.hom_ext_of_cpts
    intro q
    rw [PkgI3.AbVar.Hom.hom_zero, MonObj.comp_one]
    have h1 := ZInQ.Contrib.AVB1.bcPt_ptMap (A := A) (B := B) ℂ f q
    have h2 : PkgI3.AbVar.ptMap f (ZInQ.Contrib.AbVarBC.bcPt A ℂ q) = 1 :=
      h (ZInQ.Contrib.AbVarBC.bcPt A ℂ q)
    rw [h2] at h1
    have h3 : PkgI3.AbVar.ptMap (ZInQ.Contrib.AVB1.bcHom ℂ A B f) q = 1 :=
      (MulEquiv.map_eq_one_iff _).1 h1
    exact h3
  apply ZInQ.Contrib.AVB1.bcHom_injective (L := ℂ) A B
  rw [hC, map_zero]

/-! ## 2. Linear lifts are unique, additive, and determine the homomorphism -/

section Lift

variable {σ : K →+* ℂ} {A B : PkgI3.AbVar K} {g h : ℕ}
  {ΛA : Submodule ℤ (Fin g → ℂ)} {ΛB : Submodule ℤ (Fin h → ℂ)}
  {ΦA : (Fin g → ℂ) → CPts A σ} {ΦB : (Fin h → ℂ) → CPts B σ}

/-- Two linear lifts of the same map agree (`Λ_B` is discrete). -/
theorem lift_unique [DiscreteTopology ΛB] [IsZLattice ℝ ΛB] (hB : IsUniformization σ ΛB ΦB)
    (ψ : (Fin g → ℂ) → CPts B σ) (M M' : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))
    (hM : ∀ z, ΦB (M z) = ψ z) (hM' : ∀ z, ΦB (M' z) = ψ z) : M = M' := by
  have key : ∀ w, M w - M' w ∈ ΛB := by
    intro w
    rw [← hB.2.1]
    have e : ΦB (M w) = ΦB (M w - M' w) * ΦB (M' w) := by
      rw [← hB.1, sub_add_cancel]
    rw [hM, hM'] at e
    have := congrArg (fun x => x * (ψ w)⁻¹) e
    simpa using this.symm
  apply LinearMap.ext
  intro z
  apply sub_eq_zero.1
  apply HDec.G0Galois.eq_zero_of_real_smul_mem ΛB
  intro t
  have := key ((t : ℂ) • z)
  rwa [map_smul, map_smul, ← smul_sub, Complex.coe_smul] at this

/-- The lift of `f + f'` is the sum of the lifts. -/
theorem lift_add [DiscreteTopology ΛB] [IsZLattice ℝ ΛB] (hB : IsUniformization σ ΛB ΦB)
    (f f' : PkgI3.AbVar.Hom A B) (M M' N : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))
    (hM : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (hM' : ∀ z, ΦB (M' z) = ΦA z ≫ f'.hom)
    (hN : ∀ z, ΦB (N z) = ΦA z ≫ (f + f').hom) : N = M + M' := by
  refine lift_unique hB (fun z => ΦA z ≫ (f + f').hom) N (M + M') hN fun z => ?_
  rw [LinearMap.add_apply, hB.1, hM, hM', PkgI3.AbVar.Hom.hom_add, MonObj.comp_mul]

/-- A linear lift vanishing on `Λ_A` comes from the zero homomorphism. -/
theorem eq_zero_of_lift_lattice [DiscreteTopology ΛA] [IsZLattice ℝ ΛA] (hA : IsUniformization σ ΛA ΦA)
    (hB : IsUniformization σ ΛB ΦB) (f : PkgI3.AbVar.Hom A B) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))
    (hM : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (h0 : ∀ lam ∈ ΛA, M lam = 0) : f = 0 := by
  have hMR : M.restrictScalars ℝ = 0 := by
    apply LinearMap.ext_on_range (v := fun lam : ΛA => (lam : Fin g → ℂ))
    · rw [Subtype.range_coe_subtype]
      exact IsZLattice.span_top
    · intro lam
      exact h0 lam lam.2
  apply hom_eq_zero_of_cpts σ f
  intro p
  obtain ⟨z, rfl⟩ := hA.2.2.1 p
  rw [← hM]
  have : M z = 0 := by
    have := LinearMap.congr_fun hMR z
    simpa using this
  rw [this]
  exact (hB.2.1 0).2 (zero_mem _)

end Lift

/-! ## 3. The main theorem over a field whose algebraic closure embeds into `ℂ` -/

/-- The conclusion of Mumford §19 Thm 3 for `A, B` (the body of `PkgI3.HomFreeFinite`, without
the hypothesis `ℓ ≠ char K`, which is automatic in characteristic `0`). -/
def HomFreeConcl (A B : PkgI3.AbVar K) : Prop :=
  Module.Free ℤ (PkgI3.AbVar.Hom A B) ∧ Module.Finite ℤ (PkgI3.AbVar.Hom A B) ∧
    ((Module.finrank ℤ (PkgI3.AbVar.Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], Function.Injective (PkgI3.AbVar.tateHomZl ℓ A B)

theorem finrank_lattice {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : Module.finrank ℤ Λ = 2 * g := by
  rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/-- **Mumford §19 Thm 3 when `K̄` embeds into `ℂ` (proved from AN3 and Mumford §4 App. 2).**
`f ↦ ρ(f)|_{Λ_A}` embeds `Hom(A, B)` into `Hom_ℤ(Λ_A, Λ_B) ≅ ℤ^{4gh}`; the comparison
`α_B : ℤ_ℓ ⊗ Λ_B ↪ T_ℓ(B)` (conj-twist's `TateLatticeInj`) and flatness of `ℤ_ℓ` give the
injectivity of `ℤ_ℓ ⊗ Hom(A, B) → Hom(T_ℓ A, T_ℓ B)`. -/
theorem homFreeConcl_of_emb (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) (emb : AlgebraicClosure K →+* ℂ)
    (A B : PkgI3.AbVar K) : HomFreeConcl A B := by
  classical
  set σ : K →+* ℂ := emb.comp (algebraMap K (AlgebraicClosure K)) with hσ
  have h35 := AvSplit.Final.h38 HL HT
  have hN2 := ZInQ.HomLattice.homLinearLift_of_analyticHomLift
    (AvSplit.HomLatticeAN3.analyticHomLift_of_C (ZInQ.HomLattice.analyticHomLiftC_of_leaf HL))
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨h, hh⟩ := PkgI3.AbVar.dim_finite B
  obtain ⟨ΛA, ΦA, hdA, hlatA, hA⟩ := h35 K A σ g hg
  obtain ⟨ΛB, ΦB, hdB, hlatB, hB⟩ := h35 K B σ h hh
  choose M hM using fun f => hN2 K A B σ g h ΛA ΛB ΦA ΦB hg hh hA hB f
  have hMlat : ∀ (f : PkgI3.AbVar.Hom A B) (lam : ΛA), M f lam ∈ ΛB := fun f lam =>
    HDec.G0Galois.lift_mem_lattice hA hB f (M f) (hM f) lam
  let u : PkgI3.AbVar.Hom A B → (ΛA →ₗ[ℤ] ΛB) := fun f =>
    { toFun := fun lam => ⟨M f lam, hMlat f lam⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun n x => Subtype.ext (by
        simp only [RingHom.id_apply, Submodule.coe_smul]; exact map_zsmul (M f) n _) }
  let U : PkgI3.AbVar.Hom A B →ₗ[ℤ] (ΛA →ₗ[ℤ] ΛB) :=
    (AddMonoidHom.mk' u (fun f f' => by
      apply LinearMap.ext; intro lam; apply Subtype.ext
      change M (f + f') lam = M f lam + M f' lam
      rw [lift_add hB f f' (M f) (M f') (M (f + f')) (hM f) (hM f') (hM (f + f'))]
      rfl)).toIntLinearMap
  have hUapp : ∀ f lam, ((U f lam : ΛB) : Fin h → ℂ) = M f lam := fun f lam => rfl
  have hU : Function.Injective U := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    refine eq_zero_of_lift_lattice hA hB f (M f) (hM f) fun lam hlam => ?_
    have := congrArg Subtype.val (LinearMap.congr_fun hf ⟨lam, hlam⟩)
    rw [hUapp] at this
    exact this
  haveI := ZLattice.module_finite ℝ ΛA
  haveI := ZLattice.module_free ℝ ΛA
  haveI := ZLattice.module_finite ℝ ΛB
  haveI := ZLattice.module_free ℝ ΛB
  haveI : Module.Finite ℤ (ΛA →ₗ[ℤ] ΛB) := Module.Finite.linearMap ℤ ℤ ΛA ΛB
  haveI : Module.Free ℤ (ΛA →ₗ[ℤ] ΛB) := Module.Free.linearMap ℤ ℤ ΛA ΛB
  haveI : Module.Finite ℤ (PkgI3.AbVar.Hom A B) := Module.Finite.of_injective U hU
  haveI : Module.IsTorsionFree ℤ (PkgI3.AbVar.Hom A B) :=
    Function.Injective.moduleIsTorsionFree U hU (fun r m => map_zsmul U r m)
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · -- the rank bound
    have h1 := LinearMap.finrank_le_finrank_of_injective hU
    rw [Module.finrank_linearMap, finrank_lattice ΛA, finrank_lattice ΛB] at h1
    have h2 : Module.finrank ℤ (PkgI3.AbVar.Hom A B) ≤ 4 * g * h := by nlinarith
    rw [hg, hh]
    have h3 : (((Module.finrank ℤ (PkgI3.AbVar.Hom A B) : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
        (((4 * g * h : ℕ) : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h2
    refine h3.trans (le_of_eq ?_)
    push_cast
    rfl
  · -- injectivity of `ℤ_ℓ ⊗ Hom(A, B) → Hom(T_ℓ A, T_ℓ B)`
    intro ℓ _
    have hTL := HDec.G0Galois.tateLatticeInj_of_T5 (AvSplit.Final.h25 HT)
    obtain ⟨αA, -, hαA⟩ := hTL K A emb g ΛA ΦA hg hlatA hA ℓ
    obtain ⟨αB, hαBinj, hαB⟩ := hTL K B emb h ΛB ΦB hh hlatB hB ℓ
    let χ : ΛA → (PkgI3.AbVar.Hom A B →ₗ[ℤ] ΛB) := fun lam => LinearMap.applyₗ lam ∘ₗ U
    have hnat : ∀ (x : ℤ_[ℓ] ⊗[ℤ] PkgI3.AbVar.Hom A B) (lam : ΛA),
        αB (LinearMap.lTensor ℤ_[ℓ] (χ lam) x) = PkgI3.AbVar.tateHomZl ℓ A B x (αA (1 ⊗ₜ lam)) := by
      intro x lam
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a f =>
        rw [LinearMap.lTensor_tmul]
        have e1 : PkgI3.AbVar.tateHomZl ℓ A B (a ⊗ₜ f) = a • PkgI3.AbVar.tateHom ℓ A B f := rfl
        rw [e1, LinearMap.smul_apply]
        change _ = a • PkgI3.AbVar.homT f (αA (1 ⊗ₜ lam))
        rw [HDec.G0Galois.homT_tateLattice emb ℓ αA hαA αB hαB f (M f) (hM f) lam (hMlat f lam)]
        have e2 : a ⊗ₜ[ℤ] (χ lam f) = a • ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] (χ lam f)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [e2, map_smul]
        rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_apply]
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hz : ∀ lam, LinearMap.lTensor ℤ_[ℓ] (χ lam) x = 0 := fun lam =>
      hαBinj (by rw [hnat, hx, LinearMap.zero_apply, map_zero])
    let bA := Module.Free.chooseBasis ℤ ΛA
    let E : (ΛA →ₗ[ℤ] ΛB) →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ ΛA → ΛB) :=
      LinearMap.pi (fun i => LinearMap.applyₗ (bA i))
    have hE : Function.Injective E := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      apply bA.ext
      intro i
      exact congrFun hv i
    haveI := ZInQ.Contrib.AVB1.flat_int_padicInt ℓ
    have hW : Function.Injective (LinearMap.lTensor ℤ_[ℓ] (E ∘ₗ U)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (hE.comp hU)
    apply hW
    rw [map_zero]
    apply (TensorProduct.piRight ℤ ℤ_[ℓ] ℤ_[ℓ]
      (fun _ : Module.Free.ChooseBasisIndex ℤ ΛA => ΛB)).injective
    rw [map_zero]
    funext i
    have key : ∀ y : ℤ_[ℓ] ⊗[ℤ] PkgI3.AbVar.Hom A B,
        TensorProduct.piRight ℤ ℤ_[ℓ] ℤ_[ℓ] (fun _ : Module.Free.ChooseBasisIndex ℤ ΛA => ΛB)
          (LinearMap.lTensor ℤ_[ℓ] (E ∘ₗ U) y) i = LinearMap.lTensor ℤ_[ℓ] (χ (bA i)) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a f =>
        rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.piRight_apply,
          TensorProduct.piRightHom_tmul]
        rfl
      | add y y' hy hy' => rw [map_add, map_add, Pi.add_apply, hy, hy', map_add]
    rw [key, hz]
    rfl

/-! ## 4. Corollaries: the narrowed statements -/

/-- **Mumford §19 Thm 3 (T6, `PkgI3.HomFreeFinite`) over every field that embeds into `ℂ`.** The
body of `PkgI3.HomFreeFinite`, quantified over fields `k` with a ring homomorphism `σ : k → ℂ`. -/
def HomFreeFiniteC : Prop :=
  ∀ (k : Type) [Field k] (_ : k →+* ℂ) (A B : PkgI3.AbVar k),
    Module.Free ℤ (PkgI3.AbVar.Hom A B) ∧ Module.Finite ℤ (PkgI3.AbVar.Hom A B) ∧
      ((Module.finrank ℤ (PkgI3.AbVar.Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
        Function.Injective (PkgI3.AbVar.tateHomZl ℓ A B)

/-- **`HomFreeFiniteAlgClosed` over algebraically closed fields that embed into `ℂ`.** The field's
statement with the extra hypothesis `σ : k → ℂ`. -/
def HomFreeFiniteAlgClosedC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (_ : k →+* ℂ) (A B : PkgI3.AbVar k),
    Module.Free ℤ (PkgI3.AbVar.Hom A B) ∧ Module.Finite ℤ (PkgI3.AbVar.Hom A B) ∧
      ((Module.finrank ℤ (PkgI3.AbVar.Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
        Function.Injective (PkgI3.AbVar.tateHomZl ℓ A B)

/-- `σ : k → ℂ` extends to `k̄ → ℂ`. -/
theorem exists_emb (σ : K →+* ℂ) : Nonempty (AlgebraicClosure K →+* ℂ) := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact ⟨(IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] ℂ).toRingHom⟩

/-- **`HomFreeFiniteC` (proved) from `uniformizationLeafAll` and `mumfordTorsionAlgClosed`.** -/
theorem homFreeFiniteC (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) : HomFreeFiniteC := by
  intro k _ σ A B
  obtain ⟨emb⟩ := exists_emb σ
  obtain ⟨h1, h2, h3, h4⟩ := homFreeConcl_of_emb HL HT emb A B
  exact ⟨h1, h2, h3, fun ℓ _ _ => h4 ℓ⟩

/-- **`HomFreeFiniteAlgClosedC` (proved).** -/
theorem homFreeFiniteAlgClosedC (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) : HomFreeFiniteAlgClosedC :=
  fun k _ _ σ A B => homFreeFiniteC HL HT k σ A B

/-- **The remainder of Mumford §19 Thm 3: algebraically closed fields with no embedding into
`ℂ`** (characteristic `p > 0`, or characteristic `0` and transcendence degree over `ℚ` larger than
the continuum). The field's statement restricted to them. -/
def HomFreeFiniteAlgClosedNoEmb : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k], IsEmpty (k →+* ℂ) → ∀ (A B : PkgI3.AbVar k),
    Module.Free ℤ (PkgI3.AbVar.Hom A B) ∧ Module.Finite ℤ (PkgI3.AbVar.Hom A B) ∧
      ((Module.finrank ℤ (PkgI3.AbVar.Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
        Function.Injective (PkgI3.AbVar.tateHomZl ℓ A B)

/-- **The field from the two bundle fields and the remainder (proved).** -/
theorem homFreeFiniteAlgClosed_of_noEmb (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) (HR : HomFreeFiniteAlgClosedNoEmb) :
    ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed := by
  intro k _ _ A B
  rcases isEmpty_or_nonempty (k →+* ℂ) with he | hne
  · exact HR k he A B
  · obtain ⟨σ⟩ := hne
    exact homFreeFiniteC HL HT k σ A B

/-! ## 5. Forms for rerouting the consumers of T6 -/

/-- **T6 over fields algebraic over `ℚ`** (number fields, `ℚ̄`, `K̄` for a number field `K`). The
body of `PkgI3.HomFreeFinite`. -/
def HomFreeFiniteAlgQ : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Algebra.IsAlgebraic ℚ k] (A B : PkgI3.AbVar k),
    Module.Free ℤ (PkgI3.AbVar.Hom A B) ∧ Module.Finite ℤ (PkgI3.AbVar.Hom A B) ∧
      ((Module.finrank ℤ (PkgI3.AbVar.Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
        Function.Injective (PkgI3.AbVar.tateHomZl ℓ A B)

/-- **T6 over number fields.** -/
def HomFreeFiniteNF : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (A B : PkgI3.AbVar k),
    Module.Free ℤ (PkgI3.AbVar.Hom A B) ∧ Module.Finite ℤ (PkgI3.AbVar.Hom A B) ∧
      ((Module.finrank ℤ (PkgI3.AbVar.Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
        Function.Injective (PkgI3.AbVar.tateHomZl ℓ A B)

/-- **`HomFreeFiniteAlgQ` (proved).** A field algebraic over `ℚ` embeds into `ℂ`. -/
theorem homFreeFiniteAlgQ (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) : HomFreeFiniteAlgQ := by
  intro k _ _ _ A B
  exact homFreeFiniteC HL HT k (IsAlgClosed.lift : k →ₐ[ℚ] ℂ).toRingHom A B

/-- **`HomFreeFiniteNF` (proved).** -/
theorem homFreeFiniteNF (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) : HomFreeFiniteNF := by
  intro k _ _ A B
  exact homFreeFiniteAlgQ HL HT k A B

end ZInQ.Contrib.OneProof.HomFreeC

#print axioms ZInQ.Contrib.OneProof.HomFreeC.homFreeConcl_of_emb
#print axioms ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteC
#print axioms ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteAlgClosed_of_noEmb
#print axioms ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteAlgQ
#print axioms ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteNF
