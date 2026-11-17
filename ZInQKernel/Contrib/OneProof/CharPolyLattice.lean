import ZInQKernel.OneProof.H.TailE
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.Contrib.AVB1.AlgClosed
import ZInQKernel.OneProof.H.LF4T5

/-!
# degpoly-proof: Mumford §19 Thm 4 (integral `ℓ`-independent characteristic polynomial) over fields that embed into `ℂ`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task degpoly-proof, 2026-11-16);
report `docs/research/degpoly-proof.md`, scratch `scratch/degpoly-proof/`.

Over a field `K` with `emb : K̄ → ℂ`, the bundle field `charPolyIndepOfEllAlgClosed`
(`ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed`) and T7 (`PkgI3.CharPolyIndepOfEll`) need no degree
theory. With `Φ : ℂ^g → A(ℂ)` the uniformization (T35, proved from the open fields
`uniformizationLeafAll` and `mumfordTorsionAlgClosed`), `Λ = ker Φ` and `M_φ` the `ℂ`-linear lift of
`φ ∈ End(A)` (which preserves `Λ`), conj-twist's injective comparison `α : ℤ_ℓ ⊗ Λ ↪ T_ℓ(A)` is natural
(`T_ℓ(φ) ∘ α = α ∘ (M_φ|_Λ ⊗ 1)`), and `rank T_ℓ = 2g = rank Λ`. So `α ⊗ ℚ_ℓ` is an isomorphism
conjugating `V_ℓ(φ)` to `M_φ|_Λ ⊗ ℚ_ℓ`, and
`charpoly V_ℓ(φ) = charpoly_ℤ(M_φ|_Λ)`: monic, integral, independent of `ℓ` (`charpoly_V_eq`).

* `charPolyIndep_of_emb`: the body of T7 for `K`, `A`, `φ`, from `uniformizationLeafAll` and
  `mumfordTorsionAlgClosed`.
* `charPolyIndepOfEllC` (T7 over every field with a ring homomorphism to `ℂ`),
  `charPolyIndepOfEllAlgClosedC` (the field with `σ : k → ℂ` added), `charPolyIndepOfEllAlgQ`.
* `charPolyIndepOfEllAlgClosed_of_noEmb`: the field from the two open fields and the new leaf
  `CharPolyIndepOfEllAlgClosedNoEmb` (the field restricted to algebraically closed fields with no ring
  homomorphism to `ℂ`: characteristic `p`, or characteristic `0` beyond the continuum).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.OneProof.CharPolyLattice

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Polynomial
open scoped TensorProduct
open ZInQ.LeafPush2 (CPts IsUniformization)

variable {K : Type} [Field K]

/-! ## 1. Lattice facts -/

/-- `rank_ℤ Λ = 2g` for a lattice `Λ ⊂ ℂ^g`. -/
theorem finrank_lattice {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : Module.finrank ℤ Λ = 2 * g := by
  rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/-- The restriction to `Λ` of a `ℂ`-linear map preserving `Λ`. -/
def latEnd {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ lam : Λ, M lam ∈ Λ) : Λ →ₗ[ℤ] Λ :=
  (M.restrictScalars ℤ).restrict (fun x hx => hM ⟨x, hx⟩)

theorem latEnd_apply {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ lam : Λ, M lam ∈ Λ) (lam : Λ) : ((latEnd Λ M hM lam : Λ) : Fin g → ℂ) = M lam := rfl

/-- `#A(K̄)[ℓⁿ] = ℓ^{2gn}` from `mumfordTorsionAlgClosed` (as t5-torsion's `tateModuleFree_at`). -/
theorem card_tb_of_mumford (hM : AvSplit.MumfordTorsionAlgClosed) (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (n : ℕ) :
    Nat.card (T5Torsion.TateFree.tb ℓ (Additive (A.Pt (AlgebraicClosure K))) n) =
      ℓ ^ (n * (2 * g)) := by
  have hT := AvSplit.torsionStructure_of_mumford hM K
  obtain ⟨e', -⟩ := hT (ObjBridge.toGrp A) g (ℓ ^ n) hg
    (pow_pos (Fact.out : ℓ.Prime).pos n) (by push_cast; exact pow_ne_zero _ hℓ)
  rw [← Nat.card_congr (T5Torsion.TateFree.torsionEquivTb A ℓ n), Nat.card_congr e', Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]

/-! ## 2. `charpoly V_ℓ(φ) = charpoly_ℤ(φ on Λ)` -/

/-- **`charpoly V_ℓ(φ) = charpoly_ℤ(M_φ|_Λ)`** (in any basis of `V_ℓ`). -/
theorem charpoly_V_eq (HT : AvSplit.MumfordTorsionAlgClosed) (emb : AlgebraicClosure K →+* ℂ)
    (A : PkgI3.AbVar K) (φ : PkgI3.AbVar.End A) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞))
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (hlat : IsZLattice ℝ Λ)
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))
    (hA : IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ)
    (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hM : ∀ z, Φ (M z) = Φ z ≫ φ.hom)
    (hMlat : ∀ lam : Λ, M lam ∈ Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) (I : Type) [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) :
    haveI := ZLattice.module_finite ℝ Λ
    haveI := ZLattice.module_free ℝ Λ
    (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
      (latEnd Λ M hMlat).charpoly.map (Int.castRingHom ℚ_[ℓ]) := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  set X := latEnd Λ M hMlat with hX
  obtain ⟨α, hαinj, hα⟩ := HDec.G0Galois.tateLatticeInj_of_T5 (AvSplit.Final.h25 HT) K A emb g Λ Φ
    hg hlat hA ℓ
  -- intertwining over `ℤ_ℓ`
  have hint : ∀ x, α (X.baseChange ℤ_[ℓ] x) = PkgI3.AbVar.homT (ℓ := ℓ) φ (α x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a lam =>
      rw [LinearMap.baseChange_tmul]
      have e1 : ∀ y : Λ, a ⊗ₜ[ℤ] y = a • ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] y) := fun y => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e1, e1, map_smul, map_smul, map_smul,
        HDec.G0Galois.homT_tateLattice emb ℓ α hα α hα φ M hM lam (hMlat lam)]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  -- `T_ℓ` is free of rank `2g`
  have hcard := card_tb_of_mumford HT A ℓ hℓ g hg
  obtain ⟨E⟩ := T5Torsion.TateFree.tate_linearEquiv (2 * g) hcard
  haveI : Module.Free ℤ_[ℓ] (A.T ℓ) := Module.Free.of_equiv E.symm
  haveI : Module.Finite ℤ_[ℓ] (A.T ℓ) := Module.Finite.equiv E.symm
  -- base change to `ℚ_ℓ`
  haveI : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  set β := α.baseChange ℚ_[ℓ] with hβ
  have hβinj : Function.Injective β := by
    rw [hβ, LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hαinj
  have hdim : Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] Λ)) =
      Module.finrank ℚ_[ℓ] (A.V ℓ) := by
    change _ = Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] A.T ℓ)
    rw [Module.finrank_baseChange, Module.finrank_baseChange, Module.finrank_baseChange,
      E.finrank_eq, Module.finrank_fin_fun, finrank_lattice Λ]
  haveI : Module.Finite ℚ_[ℓ] (A.V ℓ) := Module.Finite.of_basis b
  set e := LinearMap.linearEquivOfInjective β hβinj hdim with he
  set Y := (X.baseChange ℤ_[ℓ]).baseChange ℚ_[ℓ] with hY
  have hcomm : (PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ] ∘ₗ β = β ∘ₗ Y := by
    rw [hβ, hY, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    exact LinearMap.ext fun x => (hint x).symm
  have hconj : e.conj Y = (PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ] := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact (LinearMap.congr_fun hcomm w).symm
  rw [LinearMap.charpoly_toMatrix, ← hconj, LinearEquiv.charpoly_conj, hY,
    LinearMap.charpoly_baseChange, LinearMap.charpoly_baseChange, Polynomial.map_map,
    RingHom.ext_int ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).comp (algebraMap ℤ ℤ_[ℓ])) (Int.castRingHom ℚ_[ℓ])]

/-- **Mumford §19 Thm 4 (second assertion) when `K̄` embeds into `ℂ` (proved from AN3 and Mumford
§4 App. 2).** The characteristic polynomial of `V_ℓ(φ)` is `charpoly_ℤ(M_φ|_Λ)` for every `ℓ`. -/
theorem charPolyIndep_of_emb (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) (emb : AlgebraicClosure K →+* ℂ)
    (A : PkgI3.AbVar K) (φ : PkgI3.AbVar.End A) :
    ∃ P : ℤ[X], P.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ]) := by
  classical
  set σ : K →+* ℂ := emb.comp (algebraMap K (AlgebraicClosure K)) with hσ
  have h35 := AvSplit.Final.h38 HL HT
  have hN2 := ZInQ.HomLattice.homLinearLift_of_analyticHomLift
    (AvSplit.HomLatticeAN3.analyticHomLift_of_C (ZInQ.HomLattice.analyticHomLiftC_of_leaf HL))
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨Λ, Φ, hd, hlat, hA⟩ := h35 K A σ g hg
  obtain ⟨M, hM⟩ := hN2 K A A σ g g Λ Λ Φ Φ hg hg hA hA φ
  have hMlat : ∀ lam : Λ, M lam ∈ Λ := fun lam =>
    HDec.G0Galois.lift_mem_lattice hA hA φ M hM lam
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  refine ⟨(latEnd Λ M hMlat).charpoly, LinearMap.charpoly_monic _, fun ℓ _ hℓ I _ _ b => ?_⟩
  exact charpoly_V_eq HT emb A φ g hg Λ hlat Φ hA M hM hMlat ℓ hℓ I b

/-! ## 3. The narrowed statements and the discharge of the field -/

/-- `σ : k → ℂ` extends to `k̄ → ℂ`. -/
theorem exists_emb (σ : K →+* ℂ) : Nonempty (AlgebraicClosure K →+* ℂ) := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact ⟨(IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] ℂ).toRingHom⟩

/-- **T7 (`PkgI3.CharPolyIndepOfEll`) over every field that embeds into `ℂ`.** The body of
`PkgI3.CharPolyIndepOfEll`, quantified over fields `k` with a ring homomorphism `k → ℂ`. -/
def CharPolyIndepOfEllC : Prop :=
  ∀ (k : Type) [Field k] (_ : k →+* ℂ) (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A),
    ∃ P : ℤ[X], P.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

/-- **The field `charPolyIndepOfEllAlgClosed` over algebraically closed fields that embed into `ℂ`.** -/
def CharPolyIndepOfEllAlgClosedC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (_ : k →+* ℂ) (A : PkgI3.AbVar k)
    (φ : PkgI3.AbVar.End A), ∃ P : ℤ[X], P.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

/-- **T7 over fields algebraic over `ℚ`** (number fields, `ℚ̄`, `K̄` for a number field `K`). -/
def CharPolyIndepOfEllAlgQ : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Algebra.IsAlgebraic ℚ k] (A : PkgI3.AbVar k)
    (φ : PkgI3.AbVar.End A), ∃ P : ℤ[X], P.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

/-- **`CharPolyIndepOfEllC` (proved) from `uniformizationLeafAll` and `mumfordTorsionAlgClosed`.** -/
theorem charPolyIndepOfEllC (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) : CharPolyIndepOfEllC := by
  intro k _ σ A φ
  obtain ⟨emb⟩ := exists_emb σ
  exact charPolyIndep_of_emb HL HT emb A φ

/-- **`CharPolyIndepOfEllAlgClosedC` (proved).** -/
theorem charPolyIndepOfEllAlgClosedC (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) : CharPolyIndepOfEllAlgClosedC :=
  fun k _ _ σ A φ => charPolyIndepOfEllC HL HT k σ A φ

/-- **`CharPolyIndepOfEllAlgQ` (proved).** A field algebraic over `ℚ` embeds into `ℂ`. -/
theorem charPolyIndepOfEllAlgQ (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) : CharPolyIndepOfEllAlgQ := by
  intro k _ _ _ A φ
  exact charPolyIndepOfEllC HL HT k (IsAlgClosed.lift : k →ₐ[ℚ] ℂ).toRingHom A φ

/-- **LEAF (published; a ∀-specialization of the printed theorem): Mumford §19 Thm 4 over
algebraically closed fields with no ring homomorphism to `ℂ`.** D. Mumford, *Abelian varieties*
(1970), §19, Theorem 4 (UNVERIFIED locator; the field `charPolyIndepOfEllAlgClosed` cites the same
theorem): for `φ ∈ End(X)`, `X` an abelian variety over an algebraically closed field `k`, the
characteristic polynomial of `T_ℓ(φ)` (`ℓ ≠ char k`) has integer coefficients independent of `ℓ`.
Restricted here to the `k` with `IsEmpty (k →+* ℂ)` (by Steinitz: characteristic `p > 0`, or
characteristic `0` and transcendence degree over `ℚ` above the continuum). Same objects as the field. -/
def CharPolyIndepOfEllAlgClosedNoEmb : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k], IsEmpty (k →+* ℂ) → ∀ (A : PkgI3.AbVar k)
    (φ : PkgI3.AbVar.End A), ∃ P : ℤ[X], P.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

/-- **The field from the two bundle fields and the remainder (proved).** -/
theorem charPolyIndepOfEllAlgClosed_of_noEmb (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) (HR : CharPolyIndepOfEllAlgClosedNoEmb) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed := by
  intro k _ _ A φ
  rcases isEmpty_or_nonempty (k →+* ℂ) with he | hne
  · exact HR k he A φ
  · obtain ⟨σ⟩ := hne
    exact charPolyIndepOfEllC HL HT k σ A φ

end ZInQ.Contrib.OneProof.CharPolyLattice
