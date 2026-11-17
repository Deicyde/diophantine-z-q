import ZInQKernel.Contrib.OneProof.PanBergerFix

/-!
# `PanBerger` from Pan's and Berger's theorems in printed form (task pb-fix2)

The open research field `r11r12 : HDec.PkgI4.PanBerger` (Pan's Theorem 1.0.4 with "de Rham at
`p`" for "potentially semistable at `p`") is discharged by `panBerger_of_printedU` from two leaves
stated in printed form, each about one representation and over genuine definitions:

* `BergerPrintedU` (Berger 2002, Théorème 0.7): de Rham ⇒ potentially semistable, for the
  `ℚ_p`-representation `V` underlying `ρ`, with Fontaine's definitions in tensor form
  `(B ⊗_{ℚ_p} V)^{G_K}` and Fontaine's `K_0 = W(k_K)[1/p]` (`K0W`, Witt vectors of the residue
  field of `K`, Mathlib's `WittVector`);
* `PanPrintedU` (Pan 2022, Theorem 1.0.4): every hypothesis on the one `ρ` (pst and Hodge–Tate
  with distinct weights computed on `V`), conclusion with Pan's `ι_p` and geometric Frobenius.

The glue applies both to the contragredient `ρ^∨` (`dualRep`, `σ ↦ ρ(σ⁻¹)ᵀ`):

* pkg-I4's `LocalIsDeRham ρ` and `DistinctHTWeights ρ` are computed on `Hom_G(V, B)`; the trace
  pairing `E^n ≅ (E^n)^*` turns them into the printed de Rham and Hodge–Tate conditions for `ρ^∨`
  (`finrank_tensorInv_dualHom`; weights `{a, b}` become `{−a, −b}`), with no input from Sen theory;
* irreducibility, finite ramification and oddness pass to `ρ^∨` (`dualRep_isIrreducible`, …);
* Pan's identity for `ρ^∨` at `σ⁻¹` is `tr ρ(σ) = ψ(σ)⁻¹ ι_p⁻¹(a_q(g))` (`trace_dualRep_inv`);
* the algebraicity of `a_q(g)` that `PanBerger`'s conclusion asks for comes from Diamond–Shurman
  9.6.5/9.6.6 (`DSThm965`, `DSThm966`, leaves of the same bundle) through pb-fix's
  `coeff_mem_range`, and `ι_p` from Steinitz (`exists_complex_equiv`).

Also proved (sanity of `K_0`): `[W(k)[1/p] : ℚ_p] = [k : 𝔽_p]` for every finite field `k` of
characteristic `p` (`finrank_wittLoc`: Teichmüller lifts of an `𝔽_p`-basis are a `ℤ_p`-basis of
`W(k)`), the residue field `k_K` of a finite `K/ℚ_p` is finite (`resField_finite`), so
`|k_K| = p^{[K_0 : ℚ_p]}` (`card_resField`: `[K_0 : ℚ_p]` is the residue degree), and
`1 ≤ [K_0 : ℚ_p] ≤ [K : ℚ_p]`, `[K_0(ℚ_p) : ℚ_p] = 1`.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace PanBergerSplit

open Module
open scoped TensorProduct Matrix

/-! ## §1. The contragredient of a matrix representation -/

section DualHom

variable {G : Type*} [Group G] {R : Type*} [CommRing R] {n : ℕ}

/-- The contragredient `σ ↦ ρ(σ⁻¹)ᵀ` of a matrix representation (the action on the dual basis). -/
def dualHom (ρ : G →* GL (Fin n) R) : G →* GL (Fin n) R where
  toFun σ := ⟨(ρ σ⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ, (ρ σ : Matrix (Fin n) (Fin n) R)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' σ τ := Units.ext (by simp [Matrix.transpose_mul])

theorem dualHom_val (ρ : G →* GL (Fin n) R) (σ : G) :
    ((dualHom ρ σ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      (ρ σ⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ := rfl

theorem dualHom_map {S : Type*} [CommRing S] (f : R →+* S) (ρ : G →* GL (Fin n) R) (σ : G) :
    Matrix.GeneralLinearGroup.map f (dualHom ρ σ) =
      dualHom ((Matrix.GeneralLinearGroup.map f).comp ρ) σ := by
  apply Units.ext
  ext i j
  rfl

theorem dualHom_model {S : Type*} [CommRing S] (f : R →+* S) (ρ : G →* GL (Fin n) R)
    (ρ' : G →* GL (Fin n) S) (h : ∀ σ, Matrix.GeneralLinearGroup.map f (ρ σ) = ρ' σ) (σ : G) :
    Matrix.GeneralLinearGroup.map f (dualHom ρ σ) = dualHom ρ' σ := by
  rw [dualHom_map, show (Matrix.GeneralLinearGroup.map f).comp ρ = ρ' from MonoidHom.ext h]

end DualHom

/-! ## §2. The contragredient of a Galois representation, and what it preserves -/

section DualRep

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- The contragredient `ρ^∨ : σ ↦ ρ(σ⁻¹)ᵀ` of a continuous `ρ : G_ℚ → GL_n(ℚ̄_ℓ)`. -/
def dualRep (ρ : GaloisRep ℓ n) : GaloisRep ℓ n where
  toHom := dualHom ρ.toHom
  continuous_toHom := by
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_val.comp (ρ.continuous_toHom.comp continuous_inv)).matrix_transpose
    · exact (Units.continuous_val.comp ρ.continuous_toHom).matrix_transpose

theorem dualRep_mat (ρ : GaloisRep ℓ n) (σ : GQ) : (dualRep ρ).mat σ = (ρ.mat σ⁻¹)ᵀ := rfl

theorem dualRep_mat_inv (ρ : GaloisRep ℓ n) (σ : GQ) : (dualRep ρ).mat σ⁻¹ = (ρ.mat σ)ᵀ := by
  rw [dualRep_mat, inv_inv]

theorem trace_dualRep_inv (ρ : GaloisRep ℓ n) (σ : GQ) :
    ((dualRep ρ).mat σ⁻¹).trace = (ρ.mat σ).trace := by
  rw [dualRep_mat_inv, Matrix.trace_transpose]

theorem dualRep_restrictLocal (p : ℕ) [Fact p.Prime] (ρ : GaloisRep ℓ n) :
    (dualRep ρ).restrictLocal p = dualHom (ρ.restrictLocal p) := by
  ext σ i j
  change (ρ.toHom (decomp p σ)⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))ᵀ i j =
    (ρ.toHom (decomp p σ⁻¹) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))ᵀ i j
  rw [map_inv (decomp p), map_inv ρ.toHom]

/-- `ρ` irreducible (Burnside form) implies `ρ^∨` irreducible. -/
theorem dualRep_isIrreducible (ρ : GaloisRep ℓ n) (h : ρ.IsIrreducible) :
    (dualRep ρ).IsIrreducible := by
  unfold GaloisRep.IsIrreducible at *
  set A := Algebra.adjoin (PadicAlgCl ℓ) (Set.range (dualRep ρ).mat) with hA
  let S : Subalgebra (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) :=
    { carrier := {X | Xᵀ ∈ A}
      mul_mem' := fun {X Y} hX hY => by
        simp only [Set.mem_ofPred_eq, Matrix.transpose_mul] at *
        exact A.mul_mem hY hX
      add_mem' := fun {X Y} hX hY => by
        simp only [Set.mem_ofPred_eq, Matrix.transpose_add] at *
        exact A.add_mem hX hY
      algebraMap_mem' := fun r => by
        simp only [Set.mem_ofPred_eq, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_transpose]
        rw [← Matrix.algebraMap_eq_diagonal]
        exact A.algebraMap_mem r }
  have hle : Algebra.adjoin (PadicAlgCl ℓ) (Set.range ρ.mat) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨σ, rfl⟩
    show (ρ.mat σ)ᵀ ∈ A
    rw [← dualRep_mat_inv]
    exact Algebra.subset_adjoin ⟨_, rfl⟩
  rw [h] at hle
  refine eq_top_iff.mpr fun X _ => ?_
  have hX : Xᵀ ∈ S := hle Algebra.mem_top
  simpa [S] using hX

theorem dualRep_unramifiedAt (ρ : GaloisRep ℓ n) (q : ℕ) (h : ρ.UnramifiedAt q) :
    (dualRep ρ).UnramifiedAt q := by
  intro v hv σ hσ
  have h1 := h v hv σ hσ
  apply Units.ext
  change (ρ.toHom _⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))ᵀ = 1
  rw [map_inv, h1, inv_one, Units.val_one, Matrix.transpose_one]

theorem dualRep_finitelyRamified (ρ : GaloisRep ℓ n) (h : ρ.FinitelyRamified) :
    (dualRep ρ).FinitelyRamified := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun q hq hqS => dualRep_unramifiedAt ρ q (hS q hq hqS)⟩

theorem dualRep_isOdd (ρ : GaloisRep ℓ 2) (h : ρ.IsOdd) : (dualRep ρ).IsOdd := by
  intro c hc
  have h1 := h c hc
  rw [dualRep_mat, Matrix.det_transpose]
  have h2 : (ρ.mat c).det * (ρ.mat c⁻¹).det = 1 := by
    rw [← Matrix.det_mul]
    simp only [GaloisRep.mat, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.det_one]
  rw [h1] at h2
  linear_combination -h2

end DualRep

/-! ## §3. Fontaine's functors in the printed tensor form, and the trace pairing -/

section Tensor

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- **`(B ⊗_{ℚ_p} V)^H`**, Fontaine's `D_B` in the printed tensor form, for a `ℚ_p`-linear action
`act` of `G_{ℚ_p}` on a period ring (or module) `B`, a subgroup `H` (`G_K`), and `V = E^n` with
the action `ρ` (`ℚ_p`-linearly). -/
def tensorInv {B : Type*} [AddCommGroup B] [Module ℚ_[p] B] (act : GQp p → B →ₗ[ℚ_[p]] B)
    (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule ℚ_[p] (B ⊗[ℚ_[p]] (Fin n → E)) where
  carrier := {x | ∀ σ ∈ H, TensorProduct.map (act σ) (vAct p ρ σ) x = x}
  zero_mem' σ _ := map_zero _
  add_mem' ha hb σ hσ := by rw [map_add, ha σ hσ, hb σ hσ]
  smul_mem' c x hx σ hσ := by rw [map_smul, hx σ hσ]

/-- `Hom_H(V, B)`: `H`-equivariant `ℚ_p`-linear maps `V → B` (the form of pkg-I4's `ddrSpace`,
`htSpace` and pb-bypass's `dstSpace`). -/
def homInv {B : Type*} [AddCommGroup B] [Module ℚ_[p] B] (act : GQp p → B →ₗ[ℚ_[p]] B)
    (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule ℚ_[p] ((Fin n → E) →ₗ[ℚ_[p]] B) where
  carrier := {φ | ∀ σ ∈ H, ∀ v, φ (Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v) = act σ (φ v)}
  zero_mem' := by intro σ _ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ hσ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ hσ v, hψ σ hσ v, map_add]
  smul_mem' := by
    intro c φ hφ σ hσ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ hσ v, map_smul]

/-- The trace pairing `E^n × E^n → ℚ_p`, `(w, v) ↦ Tr_{E/ℚ_p}(Σ v_i w_i)`. -/
def trPair : (Fin n → E) →ₗ[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E) :=
  LinearMap.mk₂ ℚ_[p] (fun w v => Algebra.trace ℚ_[p] E (v ⬝ᵥ w))
    (fun w w' v => by rw [dotProduct_add, map_add])
    (fun c w v => by rw [dotProduct_smul, map_smul])
    (fun w v v' => by rw [add_dotProduct, map_add])
    (fun c w v => by rw [smul_dotProduct, map_smul])

omit [FiniteDimensional ℚ_[p] E] in
theorem trPair_apply (w v : Fin n → E) : trPair p w v = Algebra.trace ℚ_[p] E (v ⬝ᵥ w) := rfl

theorem trPair_injective : Function.Injective (trPair p (E := E) (n := n)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext i
  have : PerfectField ℚ_[p] := PerfectField.ofCharZero
  have : Algebra.IsAlgebraic ℚ_[p] E := Algebra.IsAlgebraic.of_finite ℚ_[p] E
  have : Algebra.IsSeparable ℚ_[p] E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  refine (traceForm_nondegenerate ℚ_[p] E).1 (w i) fun c => ?_
  have := LinearMap.congr_fun hw (Pi.single i c)
  rw [trPair_apply, single_dotProduct, LinearMap.zero_apply] at this
  rw [Algebra.traceForm_apply, mul_comm]
  exact this

/-- The trace pairing as an isomorphism `E^n ≅ (E^n)^* = Hom_{ℚ_p}(E^n, ℚ_p)`. -/
def trEquiv : (Fin n → E) ≃ₗ[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E) :=
  LinearEquiv.ofBijective (trPair p) ⟨trPair_injective p,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).mp (trPair_injective p)⟩

theorem trEquiv_apply (w v : Fin n → E) : trEquiv p w v = Algebra.trace ℚ_[p] E (v ⬝ᵥ w) := rfl

omit [FiniteDimensional ℚ_[p] E] in
/-- The trace pairing intertwines the contragredient matrix action with the dual action:
`⟨ρ(σ⁻¹)ᵀ w, v⟩ = ⟨w, ρ(σ⁻¹) v⟩`. -/
theorem trPair_dual (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (w v : Fin n → E) :
    trPair p (vAct p (dualHom ρ) σ w) v = trPair p w (vAct p ρ σ⁻¹ v) := by
  rw [trPair_apply, trPair_apply, vAct_apply, vAct_apply, dualHom_val, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

variable {B : Type*} [AddCommGroup B] [Module ℚ_[p] B]

/-- `B ⊗ E^n ≅ Hom_{ℚ_p}(E^n, B)`, `b ⊗ w ↦ (v ↦ ⟨w, v⟩ b)`, through the trace pairing. -/
def tensorHomEquiv : (B ⊗[ℚ_[p]] (Fin n → E)) ≃ₗ[ℚ_[p]] ((Fin n → E) →ₗ[ℚ_[p]] B) :=
  haveI : Module.Free ℚ_[p] (Fin n → E) := Module.Free.of_divisionRing _ _
  haveI : Module.Finite ℚ_[p] (Fin n → E) := Module.Finite.pi
  (TensorProduct.congr (LinearEquiv.refl ℚ_[p] B) (trEquiv p)).trans
    ((TensorProduct.comm ℚ_[p] B (Module.Dual ℚ_[p] (Fin n → E))).trans
      (dualTensorHomEquiv ℚ_[p] (Fin n → E) B))

theorem tensorHomEquiv_tmul (b : B) (w v : Fin n → E) :
    tensorHomEquiv p (b ⊗ₜ w) v = trPair p w v • b := rfl

theorem tensorHomEquiv_map (act : GQp p → B →ₗ[ℚ_[p]] B) (ρ : GQp p →* GL (Fin n) E)
    (σ : GQp p) (x : B ⊗[ℚ_[p]] (Fin n → E)) (v : Fin n → E) :
    tensorHomEquiv p (TensorProduct.map (act σ) (vAct p (dualHom ρ) σ) x) v =
      act σ (tensorHomEquiv p x (vAct p ρ σ⁻¹ v)) := by
  induction x using TensorProduct.inductionOn with
  | tmul b w =>
    rw [TensorProduct.map_tmul, tensorHomEquiv_tmul, tensorHomEquiv_tmul, map_smul, trPair_dual]
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply, map_add]

/-- **`(B ⊗ V^∨)^H ≅ Hom_H(V, B)`**, with `V^∨` realized as `E^n` with the contragredient matrix
action (`dualHom`) through the trace pairing. -/
theorem map_tensorInv_dualHom (act : GQp p → B →ₗ[ℚ_[p]] B) (H : Subgroup (GQp p))
    (ρ : GQp p →* GL (Fin n) E) :
    Submodule.map (tensorHomEquiv p).toLinearMap (tensorInv p act H (dualHom ρ)) =
      homInv p act H ρ := by
  ext φ
  constructor
  · rintro ⟨x, hx, rfl⟩ σ hσ w
    have h := congrArg (fun y => tensorHomEquiv p y (vAct p ρ σ w)) (hx σ hσ)
    rw [tensorHomEquiv_map, vAct_inv_mul] at h
    exact h.symm
  · intro hφ
    refine ⟨(tensorHomEquiv p).symm φ, fun σ hσ => ?_, by simp⟩
    apply (tensorHomEquiv p).injective
    refine LinearMap.ext fun v => ?_
    rw [tensorHomEquiv_map, LinearEquiv.apply_symm_apply]
    have := hφ σ hσ (vAct p ρ σ⁻¹ v)
    rw [← vAct_apply, vAct_mul_inv] at this
    exact this.symm

theorem finrank_tensorInv_dualHom (act : GQp p → B →ₗ[ℚ_[p]] B) (H : Subgroup (GQp p))
    (ρ : GQp p →* GL (Fin n) E) :
    finrank ℚ_[p] (tensorInv p act H (dualHom ρ)) = finrank ℚ_[p] (homInv p act H ρ) := by
  rw [← map_tensorInv_dualHom, LinearEquiv.finrank_map_eq]

end Tensor

/-! ## §4. The actions on `B_dR` and `ℂ_p(i)`, and pkg-I4's spaces as `Hom` forms -/

section Actions

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- `σ` on `B_dR`, as a `ℚ_p`-linear map. -/
def bdrLin (σ : GQp p) : BdR p →ₗ[ℚ_[p]] BdR p where
  toFun := bdrAct p σ
  map_add' := map_add _
  map_smul' := bdrAct_smul p σ

/-- `σ` on `ℂ_p`, as a `ℚ_p`-linear map. -/
def cpLin (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] where
  toFun := cpAct p σ
  map_add' := map_add _
  map_smul' c x := by
    rw [RingHom.id_apply, Algebra.smul_def, map_mul, cpAct_algebraMap, ← Algebra.smul_def]

/-- `σ` on the Tate twist `ℂ_p(i)`: `x ↦ χ(σ)^i σ(x)`. -/
def htLin (i : ℤ) (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] := cycPow p σ i • cpLin p σ

omit [FiniteDimensional ℚ_[p] E] in
/-- pkg-I4's `ddrSpace` is `Hom_{G_{ℚ_p}}(V, B_dR)`. -/
theorem homInv_bdr (ρ : GQp p →* GL (Fin n) E) : homInv p (bdrLin p) ⊤ ρ = ddrSpace p ρ := by
  ext φ
  exact ⟨fun h σ v => h σ (Subgroup.mem_top σ) v, fun h σ _ v => h σ v⟩

omit [FiniteDimensional ℚ_[p] E] in
/-- pkg-I4's `htSpace ρ i` is `Hom_{G_{ℚ_p}}(V, ℂ_p(i))`. -/
theorem homInv_ht (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    homInv p (htLin p i) ⊤ ρ = htSpace p ρ i := by
  ext φ
  exact ⟨fun h σ v => h σ (Subgroup.mem_top σ) v, fun h σ _ v => h σ v⟩

end Actions

/-! ## §5a. `W(k)[1/p]` for a field `k` of characteristic `p`, as a `ℚ_p`-algebra -/

section WittLoc

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]

/-- `ℤ_p = W(𝔽_p) → W(k)` (Mathlib's `WittVector.equiv` and functoriality). -/
def zpToWitt : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom

/-- **`W(k)[1/p]`** (Mathlib's `Localization.Away`), as a type with its instances. -/
def WittLoc : Type _ := Localization.Away (p : WittVector p k)

instance : CommRing (WittLoc p k) :=
  inferInstanceAs (CommRing (Localization.Away (p : WittVector p k)))

instance : Algebra (WittVector p k) (WittLoc p k) :=
  inferInstanceAs (Algebra (WittVector p k) (Localization.Away (p : WittVector p k)))

instance : IsLocalization (Submonoid.powers (p : WittVector p k)) (WittLoc p k) :=
  inferInstanceAs (IsLocalization (Submonoid.powers (p : WittVector p k))
    (Localization.Away (p : WittVector p k)))

/-- `ℚ_p = ℤ_p[1/p] → W(k)[1/p]`. -/
def qpToWittLoc : ℚ_[p] →+* WittLoc p k :=
  IsLocalization.lift (M := Submonoid.powers (p : ℤ_[p]))
    (g := (algebraMap _ _).comp (zpToWitt p k)) (by
      rintro ⟨_, j, rfl⟩
      have := (IsLocalization.Away.algebraMap_isUnit (S := WittLoc p k)
        (p : WittVector p k)).pow j
      rw [map_natCast] at this
      simpa only [RingHom.comp_apply, map_pow, map_natCast] using this)

instance : Algebra ℚ_[p] (WittLoc p k) := (qpToWittLoc p k).toAlgebra

end WittLoc


/-! ## §5b. `[W(k)[1/p] : ℚ_p] = [k : 𝔽_p]` for a finite field `k`

The Teichmüller lifts of an `𝔽_p`-basis of `k` form a `ℤ_p`-basis of `W(k)` (independence by
reduction mod `p` and `p`-torsion-freeness; spanning by successive approximation, using that
`ℤ_p` is `p`-adically complete and `W(k)` is `p`-adically separated, both in Mathlib), hence a
`ℚ_p`-basis of `W(k)[1/p]`. -/

section WittBasis

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]

theorem constantCoeff_zpToWitt (a : ℤ_[p]) :
    WittVector.constantCoeff (zpToWitt p k a) = (((PadicInt.toZMod a).val : ℕ) : k) := by
  have h := PadicInt.toZMod_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  have ha : a = (((PadicInt.toZMod a).val : ℕ) : ℤ_[p]) + b * p := by
    rw [hb, ZMod.cast_eq_val]
    ring
  conv_lhs => rw [ha]
  rw [map_add, map_mul, map_natCast, map_natCast, map_add, map_mul, map_natCast, map_natCast,
    CharP.cast_eq_zero k p, mul_zero, add_zero]

theorem mem_pow_smul_top {R : Type*} [CommRing R] (I : Ideal R) (m : ℕ) (x : R) :
    x ∈ (I ^ m • ⊤ : Submodule R R) ↔ x ∈ I ^ m := by
  rw [smul_eq_mul, Ideal.mul_top]

variable [Algebra (ZMod p) k] [Finite k]

omit [CharP k p] [Finite k] in
theorem algebraMap_zmod (c : ZMod p) : algebraMap (ZMod p) k c = ((c.val : ℕ) : k) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [map_natCast]

/-- A relation `Σ g_i [b_i] = 0` over `ℤ_p` among Teichmüller lifts of an `𝔽_p`-basis is
trivial. -/
theorem teich_relation_trivial {ι : Type*} [Fintype ι] (b : Basis ι (ZMod p) k) :
    ∀ g : ι → ℤ_[p], ∑ i, zpToWitt p k (g i) * WittVector.teichmuller p (b i) = 0 →
      ∀ i, g i = 0 := by
  have hb := b.linearIndependent
  rw [Fintype.linearIndependent_iff] at hb
  have key : ∀ m : ℕ, ∀ g : ι → ℤ_[p],
      ∑ i, zpToWitt p k (g i) * WittVector.teichmuller p (b i) = 0 →
        ∀ i, g i ∈ Ideal.span {(p : ℤ_[p]) ^ m} := by
    intro m
    induction m with
    | zero => intro g _ i; simp
    | succ m ih =>
      intro g hg i
      have hc : ∑ i, (PadicInt.toZMod (g i)) • b i = 0 := by
        have := congrArg WittVector.constantCoeff hg
        simp only [map_sum, map_mul, constantCoeff_zpToWitt, map_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def, algebraMap_zmod]
        rfl
      have hdiv : ∀ j, ∃ h : ℤ_[p], g j = h * p := by
        intro j
        have h0 : g j ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := hb _ hc j
        rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h0
        obtain ⟨h, hh⟩ := h0
        exact ⟨h, hh.symm⟩
      choose h hh using hdiv
      have hrel : ∑ i, zpToWitt p k (h i) * WittVector.teichmuller p (b i) = 0 := by
        apply WittVector.eq_zero_of_p_mul_eq_zero
        rw [← hg, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hh j, map_mul, map_natCast]
        ring
      have := ih h hrel i
      rw [Ideal.mem_span_singleton'] at this ⊢
      obtain ⟨c, hc⟩ := this
      exact ⟨c, by rw [hh i, ← hc, pow_succ]; ring⟩
  intro g hg i
  by_contra hne
  have h1 := key ((g i).valuation + 1) g hg i
  rw [PadicInt.mem_span_pow_iff_le_valuation _ hne] at h1
  omega

/-- Every `x ∈ W(k)` is `Σ g_i [b_i]` with `g_i ∈ ℤ_p`. -/
theorem teich_span {ι : Type*} [Fintype ι] (b : Basis ι (ZMod p) k) (x : WittVector p k) :
    ∃ g : ι → ℤ_[p], x = ∑ i, zpToWitt p k (g i) * WittVector.teichmuller p (b i) := by
  -- one approximation step
  have step : ∀ y : WittVector p k, ∃ d : ι → ℤ_[p], ∃ z : WittVector p k,
      y = ∑ i, zpToWitt p k (d i) * WittVector.teichmuller p (b i) + p * z := by
    intro y
    refine ⟨fun i => (((b.repr (WittVector.constantCoeff y) i).val : ℕ) : ℤ_[p]), ?_⟩
    have hmem : y - ∑ i, zpToWitt p k (((b.repr (WittVector.constantCoeff y) i).val : ℕ) : ℤ_[p]) *
        WittVector.teichmuller p (b i) ∈ Ideal.span {(p : WittVector p k)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
      rw [show ∀ z : WittVector p k, z.coeff 0 = WittVector.constantCoeff z from fun _ => rfl]
      rw [map_sub, map_sum, sub_eq_zero]
      conv_lhs => rw [← b.sum_repr (WittVector.constantCoeff y)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_natCast, map_natCast, Algebra.smul_def, algebraMap_zmod]
      rfl
    rw [Ideal.mem_span_singleton'] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, by rw [mul_comm, hz]; ring⟩
  choose dstep zstep hstep using step
  let Y : ℕ → WittVector p k := fun n => zstep^[n] x
  let D : ℕ → ι → ℤ_[p] := fun n i => ∑ j ∈ Finset.range n, (p : ℤ_[p]) ^ j * dstep (Y j) i
  have hinv : ∀ n, x = ∑ i, zpToWitt p k (D n i) * WittVector.teichmuller p (b i) +
      (p : WittVector p k) ^ n * Y n := by
    intro n
    induction n with
    | zero => simp [D, Y]
    | succ n ih =>
      have hY : Y (n + 1) = zstep (Y n) := Function.iterate_succ_apply' _ _ _
      have hD : ∀ i, D (n + 1) i = D n i + (p : ℤ_[p]) ^ n * dstep (Y n) i := fun i =>
        Finset.sum_range_succ _ _
      rw [hY]
      simp only [hD, map_add, map_mul, map_pow, map_natCast, add_mul, Finset.sum_add_distrib]
      conv_lhs => rw [ih, hstep (Y n)]
      rw [mul_add, Finset.mul_sum, pow_succ]
      simp only [mul_assoc]
      ring
  -- the coefficients converge in `ℤ_p`
  have hcau : ∀ i, ∀ {m n : ℕ}, m ≤ n → D m i ≡ D n i
      [SMOD ((IsLocalRing.maximalIdeal ℤ_[p]) ^ m • ⊤ : Submodule ℤ_[p] ℤ_[p])] := by
    intro i m n hmn
    rw [SModEq.sub_mem, mem_pow_smul_top, PadicInt.maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have hD : D (n + 1) i = D n i + (p : ℤ_[p]) ^ n * dstep (Y n) i := Finset.sum_range_succ _ _
      rw [hD, sub_add_eq_sub_sub]
      refine Ideal.sub_mem _ ih ?_
      rw [Ideal.mem_span_singleton']
      exact ⟨(p : ℤ_[p]) ^ (n - m) * dstep (Y n) i, by
        rw [show n = (n - m) + m from (Nat.sub_add_cancel hmn).symm, pow_add]
        simp only [Nat.add_sub_cancel]
        ring⟩
  have hlim : ∀ i, ∃ L : ℤ_[p], ∀ n, D n i ≡ L
      [SMOD ((IsLocalRing.maximalIdeal ℤ_[p]) ^ n • ⊤ : Submodule ℤ_[p] ℤ_[p])] :=
    fun i => IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal ℤ_[p]) (fun n => D n i) (hcau i)
  choose L hL using hlim
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(p : WittVector p k)}) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton']
  have he : ∀ i, ∃ e : ℤ_[p], D n i - L i = (p : ℤ_[p]) ^ n * e := by
    intro i
    have := hL i n
    rw [SModEq.sub_mem, mem_pow_smul_top, PadicInt.maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at this
    obtain ⟨e, he⟩ := this
    exact ⟨e, by rw [← he, mul_comm]⟩
  choose e he using he
  refine ⟨∑ i, zpToWitt p k (e i) * WittVector.teichmuller p (b i) + Y n, ?_⟩
  conv_rhs => rw [hinv n]
  have hL' : ∀ i, L i = D n i - (p : ℤ_[p]) ^ n * e i := fun i => by rw [← he i]; ring
  simp only [hL', map_sub, map_mul, map_pow, map_natCast, sub_mul, Finset.sum_sub_distrib]
  rw [add_mul, Finset.sum_mul]
  simp only [mul_assoc]
  ring_nf
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **`[W(k)[1/p] : ℚ_p] = [k : 𝔽_p]`** for a finite field `k` of characteristic `p`. -/
theorem finrank_wittLoc : finrank ℚ_[p] (WittLoc p k) = finrank (ZMod p) k := by
  let b := Module.finBasis (ZMod p) k
  let : Algebra ℤ_[p] (WittVector p k) := (zpToWitt p k).toAlgebra
  have hsmul : ∀ (a : ℤ_[p]) (w : WittVector p k), a • w = zpToWitt p k a * w := fun _ _ => rfl
  have hli : LinearIndependent ℤ_[p] (fun i => WittVector.teichmuller p (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    exact teich_relation_trivial p k b g (by simpa only [hsmul] using hg)
  have hsp : ⊤ ≤ Submodule.span ℤ_[p] (Set.range fun i => WittVector.teichmuller p (b i)) := by
    intro x _
    obtain ⟨g, hg⟩ := teich_span p k b x
    rw [hg]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B := Basis.mk hli hsp
  let : Algebra ℤ_[p] (WittLoc p k) :=
    ((algebraMap (WittVector p k) (WittLoc p k)).comp (zpToWitt p k)).toAlgebra
  have : IsScalarTower ℤ_[p] ℚ_[p] (WittLoc p k) := IsScalarTower.of_algebraMap_eq fun z => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    exact (IsLocalization.lift_eq (M := Submonoid.powers (p : ℤ_[p])) _ z).symm
  have : IsScalarTower ℤ_[p] (WittVector p k) (WittLoc p k) :=
    IsScalarTower.of_algebraMap_eq fun z => rfl
  have hsub : Algebra.algebraMapSubmonoid (WittVector p k) (Submonoid.powers (p : ℤ_[p])) =
      Submonoid.powers (p : WittVector p k) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, map_natCast]
  have : IsLocalization (Algebra.algebraMapSubmonoid (WittVector p k)
      (Submonoid.powers (p : ℤ_[p]))) (WittLoc p k) := by
    rw [hsub]
    infer_instance
  let B' := B.localizationLocalization ℚ_[p] (Submonoid.powers (p : ℤ_[p])) (WittLoc p k)
  rw [Module.finrank_eq_card_basis B', Module.finrank_eq_card_basis b]
  simp only [Fintype.card_fin]

/-- **`|k| = p^{[W(k)[1/p] : ℚ_p]}`**: the residue degree is `[K_0 : ℚ_p]`. -/
theorem card_eq_pow_finrank_wittLoc : Nat.card k = p ^ finrank ℚ_[p] (WittLoc p k) := by
  have := Fintype.ofFinite k
  rw [finrank_wittLoc, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p),
    ZMod.card]

end WittBasis

/-! ## §5. `K_0 = W(k)[1/p]` -/

section K0

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- **`𝓞_K`**, the valuation ring of `K ⊆ ℚ̄_p`: the elements of `K` of norm `≤ 1` (the norm of
`ℚ̄_p` is the unique extension of `|·|_p`). -/
def intRing : Subring (PadicAlgCl p) where
  carrier := {x | x ∈ K ∧ ‖x‖ ≤ 1}
  mul_mem' := fun ha hb => ⟨K.mul_mem ha.1 hb.1, by
    rw [norm_mul]; exact (mul_le_mul ha.2 hb.2 (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)⟩
  one_mem' := ⟨K.one_mem, by rw [norm_one]⟩
  add_mem' := fun ha hb => ⟨K.add_mem ha.1 hb.1,
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨K.zero_mem, by rw [norm_zero]; exact zero_le_one⟩
  neg_mem' := fun ha => ⟨K.neg_mem ha.1, by rw [norm_neg]; exact ha.2⟩

/-- **`𝔪_K`**, the maximal ideal of `𝓞_K`: the elements of norm `< 1`. -/
def maxIdeal : Ideal (intRing p K) where
  carrier := {x | ‖(x : PadicAlgCl p)‖ < 1}
  add_mem' := fun {a b} ha hb => by
    show ‖(a : PadicAlgCl p) + b‖ < 1
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by
    show ‖((0 : intRing p K) : PadicAlgCl p)‖ < 1
    rw [ZeroMemClass.coe_zero, norm_zero]; exact zero_lt_one
  smul_mem' := fun c x hx => by
    show ‖(c : PadicAlgCl p) * x‖ < 1
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) c.2.2) hx

instance maxIdeal_isMaximal : (maxIdeal p K).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => ?_, fun J x hle hx hxJ => ?_⟩
  · change ‖((1 : intRing p K) : PadicAlgCl p)‖ < 1 at h
    rw [OneMemClass.coe_one, norm_one] at h
    exact lt_irrefl _ h
  · have hx1 : ‖(x : PadicAlgCl p)‖ = 1 := le_antisymm x.2.2 (not_lt.mp hx)
    have hx0 : (x : PadicAlgCl p) ≠ 0 := by
      intro h; rw [h, norm_zero] at hx1; exact zero_ne_one hx1
    let y : intRing p K := ⟨(x : PadicAlgCl p)⁻¹, K.inv_mem x.2.1, by rw [norm_inv, hx1, inv_one]⟩
    have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    rw [← hxy]
    exact J.mul_mem_right y hxJ

/-- **`k_K = 𝓞_K / 𝔪_K`**, the residue field of `K`. -/
abbrev resField : Type := intRing p K ⧸ maxIdeal p K

instance : Field (resField p K) := Ideal.Quotient.field _

theorem natCast_p_mem_maxIdeal : (p : intRing p K) ∈ maxIdeal p K := by
  show ‖((p : intRing p K) : PadicAlgCl p)‖ < 1
  rw [show ((p : intRing p K) : PadicAlgCl p) = (p : PadicAlgCl p) by simp]
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, norm_algebraMap', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

instance resField_charP : CharP (resField p K) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk (maxIdeal p K)) p, Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_p_mem_maxIdeal p K)


/-- `ℤ_p → 𝓞_K`. -/
def zpToInt : ℤ_[p] →+* intRing p K where
  toFun z := ⟨algebraMap ℚ_[p] (PadicAlgCl p) z, K.algebraMap_mem _, by
    rw [norm_algebraMap']; exact z.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem mk_zpToInt (a : ℤ_[p]) :
    Ideal.Quotient.mk (maxIdeal p K) (zpToInt p K a) = (((PadicInt.toZMod a).val : ℕ) : resField p K) := by
  have h := PadicInt.toZMod_spec a
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  have ha : a = (((PadicInt.toZMod a).val : ℕ) : ℤ_[p]) + b * p := by
    rw [hb, ZMod.cast_eq_val]
    ring
  conv_lhs => rw [ha]
  rw [map_add, map_mul, map_natCast, map_natCast, map_add, map_mul, map_natCast, map_natCast,
    CharP.cast_eq_zero (resField p K) p, mul_zero, add_zero]

/-- Lifts to `𝓞_K` of `𝔽_p`-independent elements of `k_K` are `ℚ_p`-independent in `K`. -/
theorem lift_linearIndependent [Algebra (ZMod p) (resField p K)] {ι : Type*} [Fintype ι]
    (x : ι → intRing p K)
    (hx : LinearIndependent (ZMod p) (fun i => Ideal.Quotient.mk (maxIdeal p K) (x i))) :
    LinearIndependent ℚ_[p] (fun i => (⟨(x i : PadicAlgCl p), (x i).2.1⟩ : K)) := by
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro g hg i
  by_contra hne
  have : Nonempty ι := ⟨i⟩
  obtain ⟨j, hj⟩ := Finite.exists_max (fun i => ‖g i‖)
  have hgj : g j ≠ 0 := by
    intro h
    apply hne
    have := hj i
    rw [h, norm_zero] at this
    exact norm_le_zero_iff.mp this
  let h' : ι → ℤ_[p] := fun i => ⟨g i / g j, (PadicInt.mem_subring_iff p).mpr (by
    rw [norm_div]; exact div_le_one_of_le₀ (hj i) (norm_nonneg _))⟩
  have hrel : ∑ i, zpToInt p K (h' i) * x i = 0 := by
    apply Subtype.ext
    have hg' := congrArg (fun y : K => (y : PadicAlgCl p)) hg
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, IntermediateField.coe_zero]
      at hg'
    rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
    have hc : ∀ l, (((zpToInt p K (h' l) * x l : intRing p K)) : PadicAlgCl p) =
        (g j)⁻¹ • (g l • (x l : PadicAlgCl p)) := fun l => by
      rw [Subring.coe_mul, smul_smul, Algebra.smul_def]
      congr 1
      change algebraMap ℚ_[p] (PadicAlgCl p) (g l / g j) = _
      rw [div_eq_inv_mul]
    simp only [hc, ← Finset.smul_sum, hg', smul_zero]
  have h1 := hx (fun i => PadicInt.toZMod (h' i)) (by
    have := congrArg (Ideal.Quotient.mk (maxIdeal p K)) hrel
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, mk_zpToInt, Algebra.smul_def, algebraMap_zmod]) j
  have hj1 : h' j = 1 := Subtype.ext (div_self hgj)
  rw [hj1, map_one] at h1
  exact one_ne_zero h1


/-- `[k_K : 𝔽_p] ≤ [K : ℚ_p]`: an `𝔽_p`-independent family in `k_K` has at most `[K : ℚ_p]`
members. -/
theorem card_le_finrank_of_resField [Algebra (ZMod p) (resField p K)] [FiniteDimensional ℚ_[p] K]
    {ι : Type*} [Fintype ι] (v : ι → resField p K) (hv : LinearIndependent (ZMod p) v) :
    Fintype.card ι ≤ finrank ℚ_[p] K := by
  have hsurj := Ideal.Quotient.mk_surjective (I := maxIdeal p K)
  choose lift hlift using hsurj
  have hli := lift_linearIndependent p K (fun i => lift (v i)) (by
    simp only [hlift]
    exact hv)
  exact hli.fintype_card_le_finrank

/-- **The residue field of a finite `K/ℚ_p` is finite.** -/
instance resField_finite [FiniteDimensional ℚ_[p] K] : Finite (resField p K) := by
  let := ZMod.algebra (resField p K) p
  have hrk : Module.rank (ZMod p) (resField p K) ≤ finrank ℚ_[p] K :=
    rank_le fun s hs => by
      have := card_le_finrank_of_resField p K (fun i : s => (i : resField p K)) hs
      rwa [Fintype.card_coe] at this
  have : Module.Finite (ZMod p) (resField p K) :=
    Module.rank_lt_aleph0_iff.mp (hrk.trans_lt Cardinal.natCast_lt_aleph0)
  exact Module.finite_of_finite (ZMod p)

/-- **`K_0 = W(k_K)[1/p]`**, Fontaine's `K_0` for `K` (Berger 2002, §0: `K_0 = W(k)[1/p]`;
Fontaine, Astérisque 223 (1994), Exp. III; numbers UNVERIFIED): the Witt vectors of the residue
field of `K` with `p` inverted (Mathlib's `WittVector`, `Localization.Away`; `WittLoc` below). -/
abbrev K0W : Type := WittLoc p (resField p K)

/-- **`[K_0 : ℚ_p]` is the residue degree `f(K/ℚ_p)`**: `|k_K| = p^{[K_0 : ℚ_p]}`. -/
theorem card_resField [FiniteDimensional ℚ_[p] K] :
    Nat.card (resField p K) = p ^ finrank ℚ_[p] (K0W p K) := by
  let := ZMod.algebra (resField p K) p
  exact card_eq_pow_finrank_wittLoc p (resField p K)

/-- `[K_0 : ℚ_p] ≤ [K : ℚ_p]`. -/
theorem finrank_K0W_le [FiniteDimensional ℚ_[p] K] : finrank ℚ_[p] (K0W p K) ≤ finrank ℚ_[p] K := by
  let := ZMod.algebra (resField p K) p
  change finrank ℚ_[p] (WittLoc p (resField p K)) ≤ _
  rw [finrank_wittLoc]
  have : Module.Free (ZMod p) (resField p K) := Module.Free.of_divisionRing _ _
  have : Module.Finite (ZMod p) (resField p K) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod p) (resField p K)
  rw [Module.finrank_eq_card_basis b]
  exact card_le_finrank_of_resField p K b b.linearIndependent

/-- `[K_0 : ℚ_p] ≥ 1`. -/
theorem finrank_K0W_pos [FiniteDimensional ℚ_[p] K] : 0 < finrank ℚ_[p] (K0W p K) := by
  let := ZMod.algebra (resField p K) p
  change 0 < finrank ℚ_[p] (WittLoc p (resField p K))
  rw [finrank_wittLoc]
  have : Module.Free (ZMod p) (resField p K) := Module.Free.of_divisionRing _ _
  have : Module.Finite (ZMod p) (resField p K) := Module.Finite.of_finite
  exact Module.finrank_pos

/-- `K_0(ℚ_p) = ℚ_p`: `[K_0 : ℚ_p] = 1` for `K = ℚ_p`. -/
theorem finrank_K0W_bot : finrank ℚ_[p] (K0W p ⊥) = 1 :=
  le_antisymm ((finrank_K0W_le p ⊥).trans_eq (IntermediateField.finrank_bot))
    (finrank_K0W_pos p ⊥)

end K0

/-! ## §6. Fontaine's de Rham, Hodge–Tate and semistable conditions on the underlying space -/

section Predicates

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- **`D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}}`** for `V = E^n` with the action `ρ`. -/
def ddrU (ρ : GQp p →* GL (Fin n) E) : Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] (Fin n → E)) :=
  tensorInv p (bdrLin p) ⊤ ρ

/-- **`V` is de Rham** (Fontaine): `dim_{ℚ_p} D_dR(V) = dim_{ℚ_p} V` (`K = K_0 = ℚ_p`). -/
def IsDeRhamU (ρ : GQp p →* GL (Fin n) E) : Prop :=
  finrank ℚ_[p] (ddrU p ρ) = finrank ℚ_[p] (Fin n → E)

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is de Rham: it takes values in `GL_n(E)` for a
finite `E/ℚ_p` inside `ℚ̄_p`, and the `ℚ_p`-representation `E^n` is de Rham. -/
def LocalIsDeRhamU (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsDeRhamU p ρE

/-- **`(ℂ_p(w) ⊗_{ℚ_p} V)^{G_{ℚ_p}}`**. -/
def htU (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : Submodule ℚ_[p] (ℂ_[p] ⊗[ℚ_[p]] (Fin n → E)) :=
  tensorInv p (htLin p w) ⊤ ρ

/-- **Multiplicity of the Hodge–Tate weight `w`** of the `E`-linear `V = E^n`:
`dim_E (ℂ_p(w) ⊗_{ℚ_p} V)^{G_{ℚ_p}}` (cyclotomic character of weight `−1`, Pan's convention). -/
def htMultU (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : ℕ :=
  finrank ℚ_[p] (htU p ρ w) / finrank ℚ_[p] E

/-- **`ρ|_{G_{ℚ_p}}` is Hodge–Tate with distinct Hodge–Tate weights** (2-dimensional case): in a
model over a finite `E ⊆ ℚ̄_p`, the weights (with multiplicity, over `E`) are two distinct
integers `a ≠ b`. -/
def LocalDistinctHTU (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)) : Prop :=
  ∃ a b : ℤ, a ≠ b ∧ ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin 2) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    ∀ w : ℤ, htMultU p ρE w = Multiset.count w {a, b}

/-- **`D_st,K(V) = (B_st ⊗_{ℚ_p} V)^{G_K}`**. -/
def dstU (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule ℚ_[p] (Bst p ⊗[ℚ_[p]] (Fin n → E)) :=
  tensorInv p (stLin p) K.fixingSubgroup ρ

/-- **`V` is semistable over `K`** (Fontaine): `dim_{K_0} D_st,K(V) = dim_{ℚ_p} V`, written in
`ℚ_p`-dimensions with `K_0 = W(k_K)[1/p]` (`K0W`):
`dim_{ℚ_p} D_st,K(V) = [K_0 : ℚ_p] · dim_{ℚ_p} V`. -/
def IsSemistableOverU (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Prop :=
  finrank ℚ_[p] (dstU p K ρ) = finrank ℚ_[p] (K0W p K) * finrank ℚ_[p] (Fin n → E)

/-- **`V` is potentially semistable** (Fontaine): semistable over some finite `K/ℚ_p`. -/
def IsPstU (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsSemistableOverU p K ρ

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is potentially semistable: it takes values in
`GL_n(E)` for a finite `E/ℚ_p` inside `ℚ̄_p`, and the `ℚ_p`-representation `E^n` is potentially
semistable. -/
def LocalIsPstU (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPstU p ρE

theorem finrank_fun :
    finrank ℚ_[p] (Fin n → E) = n * finrank ℚ_[p] E := by
  have : Module.Free ℚ_[p] E := Module.Free.of_divisionRing _ _
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- pkg-I4's `LocalIsDeRham ρ` (computed on `Hom_G(V, B_dR)`) is the printed de Rham condition for
the contragredient. -/
theorem localIsDeRhamU_dualHom (ρ : GQp p →* GL (Fin n) (PadicAlgCl p))
    (h : LocalIsDeRham p n ρ) : LocalIsDeRhamU p n (dualHom ρ) := by
  obtain ⟨E, hE, ρE, hmod, hdr⟩ := h
  refine ⟨E, hE, dualHom ρE, dualHom_model _ ρE ρ hmod, ?_⟩
  rw [IsDeRhamU, ddrU, finrank_tensorInv_dualHom, homInv_bdr, finrank_fun]
  exact hdr

theorem count_neg_pair (a b w : ℤ) :
    Multiset.count w ({-a, -b} : Multiset ℤ) = Multiset.count (-w) ({a, b} : Multiset ℤ) := by
  have h : ({-a, -b} : Multiset ℤ) = Multiset.map Neg.neg {a, b} := by simp
  rw [h, ← Multiset.count_map_eq_count' Neg.neg _ neg_injective (-w), neg_neg]

/-- pkg-I4's `DistinctHTWeights ρ` (computed on `Hom_G(V, ℂ_p(i))`) gives the printed condition
"Hodge–Tate with distinct weights" for the contragredient (weights `−a ≠ −b`). -/
theorem localDistinctHTU_dualHom (ρ : GaloisRep p 2)
    (h : GaloisRep.DistinctHTWeights (ρ := ρ) p) :
    LocalDistinctHTU p (dualHom (ρ.restrictLocal p)) := by
  obtain ⟨a, b, hab, E, hE, ρE, hmod, hw⟩ := h
  refine ⟨-a, -b, fun h => hab (neg_inj.mp h), E, hE, dualHom ρE,
    dualHom_model _ ρE _ hmod, fun w => ?_⟩
  have h1 := hw (-w)
  rw [htMult, neg_neg] at h1
  rw [htMultU, htU, finrank_tensorInv_dualHom, homInv_ht, h1, count_neg_pair]

/-! ### Sanity: the printed predicates against pb-bypass's Hom forms -/

omit [FiniteDimensional ℚ_[p] E] in
/-- pb-bypass's `dstSpace` is `Hom_{G_K}(V, B_st)`. -/
theorem homInv_st (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    homInv p (stLin p) K.fixingSubgroup ρ = dstSpace p K ρ := by
  ext φ
  exact Iff.rfl

/-- The printed semistability of the contragredient is pb-bypass's Hom form of `V^∨`, now with
Fontaine's `[K_0 : ℚ_p]` (`K_0 = W(k_K)[1/p]`) in place of `dim B_st^{G_K}`. -/
theorem isSemistableOverU_dualHom_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ρ : GQp p →* GL (Fin n) E) :
    IsSemistableOverU p K (dualHom ρ) ↔
      finrank ℚ_[p] (dstSpace p K ρ) = finrank ℚ_[p] (K0W p K) * (n * finrank ℚ_[p] E) := by
  rw [IsSemistableOverU, dstU, finrank_tensorInv_dualHom, homInv_st, finrank_fun]

theorem dualHom_one {G : Type*} [Group G] {R : Type*} [CommRing R] {m : ℕ} :
    dualHom (1 : G →* GL (Fin m) R) = 1 := by
  ext σ i j
  simp only [dualHom_val, MonoidHom.one_apply, Units.val_one, Matrix.transpose_one]

/-- **Normalization of the printed semistability on the trivial representation**: the trivial
one-dimensional representation is semistable over `K` exactly when
`dim_{ℚ_p} B_st^{G_K} = [K_0 : ℚ_p]`, i.e. exactly when Fontaine's `B_st^{G_K} = K_0` holds in
dimension form (not proved in Lean; pb-sanity proves `≥ [ℚ_p(μ) : ℚ_p]` for roots of unity
`μ ∈ K` of order prime to `p`). -/
theorem isSemistableOverU_trivial_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IsSemistableOverU p K (1 : GQp p →* GL (Fin 1) ℚ_[p]) ↔
      finrank ℚ_[p] (bstInv p K) = finrank ℚ_[p] (K0W p K) := by
  have h := isSemistableOver_trivial p K
  rw [IsSemistableOver] at h
  rw [← dualHom_one, isSemistableOverU_dualHom_iff, h, finrank_self]
  simp

/-- Given Fontaine's `B_st^{G_{ℚ_p}} = ℚ_p` in dimension form, the trivial representation is
potentially semistable in the printed sense (take `K = ℚ_p`, `[K_0 : ℚ_p] = 1`). -/
theorem isPstU_trivial (hF : finrank ℚ_[p] (bstInv p ⊥) = 1) :
    IsPstU p (1 : GQp p →* GL (Fin 1) ℚ_[p]) :=
  ⟨⊥, inferInstance, (isSemistableOverU_trivial_iff p ⊥).mpr (hF.trans (finrank_K0W_bot p).symm)⟩

end Predicates

/-! ## §7. The two printed leaves -/

/-- **Berger, Théorème 0.7** (L. Berger, *Représentations p-adiques et équations
différentielles*, Invent. Math. 148 (2002), 219-284; Théorème 0.7 = Corollaire 5.22 of the
published version (author copy pp. 6 and 52, read by the locator audit row R11; Springer
pagination unread) = Théorème 0.6 = Théorème 5.19 of arXiv:math/0102179v3), at `K = ℚ_p`: every
de Rham `p`-adic representation of `G_{ℚ_p}` is potentially semistable. Printed form, applied to
the `ℚ_p`-representation `V = E^n` underlying a continuous `ρ` with values in `GL_n(E)`, `E/ℚ_p`
finite inside `ℚ̄_p` (both predicates are computed on `V` itself, in Fontaine's tensor form):

* de Rham: `dim_{ℚ_p} (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}} = dim_{ℚ_p} V` (`IsDeRhamU`);
* potentially semistable: for some finite `K/ℚ_p` inside `ℚ̄_p`,
  `dim_{ℚ_p} (B_st ⊗_{ℚ_p} V)^{G_K} = [K_0 : ℚ_p] · dim_{ℚ_p} V` with `K_0 = W(k_K)[1/p]`, `k_K`
  the residue field of `K` (`IsSemistableOverU`, `K0W`), i.e. `dim_{K_0} D_st,K(V) = dim V`.

Readings (flags): `B_st` is Fontaine's abstract `B_cris[X]` with `σ(X) = X + c(σ)t` (pb-bypass's
`Bst`), not the subring `B_cris[log [p♭]]` of `B_dR`; the semistability condition is written in
`ℚ_p`-dimensions with the explicit factor `[K_0 : ℚ_p]` (`D_st,K` is a `K_0`-space because
`K_0 ⊆ B_st^{G_K}`; that module structure is not built in Lean). -/
def BergerPrintedU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    Continuous ρ → LocalIsDeRhamU p n ρ → LocalIsPstU p n ρ

/-- **Pan, Theorem 1.0.4** (L. Pan, *The Fontaine–Mazur conjecture in the residually reducible
case*, J. Amer. Math. Soc. 35 (2022), 1031-1169; = arXiv:1901.07166v2, Theorem 1.0.4 with
Conjecture 1.0.1, pp. 5 and 2, read by h-a011 §1.1 and the locator audit row R12; JAMS numbering
and page UNVERIFIED), for `p ≥ 5`, with Pan's fixed isomorphism `ι_p : ℚ̄_p ≅ ℂ` (for each `ι_p`).
Every hypothesis is on the one representation `ρ`, in printed form:

* `ρ : G_ℚ → GL₂(ℚ̄_p)` continuous (`GaloisRep`), irreducible (`IsIrreducible`, Burnside's form:
  the image spans `M₂(ℚ̄_p)`; this implies irreducible), unramified outside finitely many primes
  (`FinitelyRamified`), odd (`IsOdd`: `det ρ(c) = −1`);
* `ρ|_{G_{ℚ_p}}` potentially semistable (`LocalIsPstU`, Fontaine's definition on the underlying
  space, as in `BergerPrintedU`);
* `ρ|_{G_{ℚ_p}}` Hodge–Tate with distinct Hodge–Tate weights (`LocalDistinctHTU`: the
  multiplicities `dim_E (ℂ_p(w) ⊗_{ℚ_p} V)^{G_{ℚ_p}}` are those of two distinct integers).

Conclusion, "`ρ` comes from a cuspidal eigenform up to twist", in Pan's normalization (geometric
Frobenius): a normalized cuspidal eigenform `g` of level `N ≥ 1` and weight `k ≥ 1`, a continuous
character `ψ` and a finite set `S` of primes with `tr ρ(Frob_q) = ψ(Frob_q) · ι_p⁻¹(a_q(g))` for
`q ∉ S`, `Frob_q = σ⁻¹` the geometric Frobenius at any place `v | q` (`σ` arithmetic).

Reading (flag): "comes from `g` up to twist" is read as `ρ ≅ ρ_{g,ι_p} ⊗ ψ'`, `ρ_{g,ι_p}` the
`p`-adic representation attached to `g` through `ι_p`; the trace identity follows from it in
every Frobenius and duality normalization of `ρ_{g,ι_p}` (in dimension 2 the dual, and the
representation of the conjugate eigenform, differ from `ρ_{g,ι_p}` by a character), with a
suitably changed `ψ`. -/
def PanPrintedU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsPstU p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTU p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (S : Finset ℕ), ∀ q : ℕ, q.Prime → q ∉ S →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
          (ρ.mat σ⁻¹).trace = (ψ.toHom σ⁻¹ : PadicAlgCl p) * ιp.symm (coeff g q)

/-! ## §8. Glue: `PanBerger` -/

/-- The inverse of a continuous character. -/
def charInv {ℓ : ℕ} [Fact ℓ.Prime] (ψ : GaloisChar ℓ) : GaloisChar ℓ where
  toHom := ψ.toHom⁻¹
  continuous_toHom := ψ.continuous_toHom.inv

theorem charInv_apply {ℓ : ℕ} [Fact ℓ.Prime] (ψ : GaloisChar ℓ) (σ : GQ) :
    (charInv ψ).toHom σ = ψ.toHom σ⁻¹ := by
  rw [map_inv]
  rfl

/-- **`PanBerger` (the research field `r11r12`) from Pan's and Berger's printed theorems**, both
applied to the contragredient `ρ^∨`, with Diamond–Shurman's Thms 9.6.5 and 9.6.6 (existing leaves
`dsThm965`, `dsThm966`) for the algebraicity of the Hecke eigenvalues. -/
theorem panBerger_of_printedU (hP : PanPrintedU) (hB : BergerPrintedU)
    (hD : ZInQ.Contrib.HodgeSplit.DSThm965) (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) :
    PanBerger := by
  intro p _ hp ρ hirr hfr hdr hodd hdist
  have hdr' : LocalIsDeRhamU p 2 ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localIsDeRhamU_dualHom p _ hdr
  have hpst' := hB p 2 _ ((dualRep ρ).continuous_toHom.comp
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous) hdr'
  have hht' : LocalDistinctHTU p ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localDistinctHTU_dualHom p ρ hdist
  obtain ⟨Φ⟩ := exists_complex_equiv p
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, S, htr⟩ := hP p hp Φ.symm (dualRep ρ)
    (dualRep_isIrreducible ρ hirr) (dualRep_finitelyRamified ρ hfr) hpst'
    (dualRep_isOdd ρ hodd) hht'
  obtain ⟨Sr, hSr⟩ := hfr
  let ιC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ιL : Qbar →ₐ[ℚ] PadicAlgCl p := (Φ : ℂ →+* PadicAlgCl p).toRatAlgHom.comp ιC
  refine ⟨N, k, χ, g, hN, hk, hg, charInv ψ, ιC, ιL, S ∪ Sr ∪ Finset.range (N * p + 1), ?_⟩
  intro q hq hqS
  simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hqS
  obtain ⟨⟨hqS, hqSr⟩, hqNp⟩ := hqS
  have hNp : 0 < N * p := Nat.mul_pos hN (Fact.out : p.Prime).pos
  have hqdvd : ¬ q ∣ N * p := fun h => by
    have := Nat.le_of_dvd hNp h
    omega
  refine ⟨hSr q hq hqSr, ?_⟩
  obtain ⟨α, hα⟩ := coeff_mem_range hD hDS p ιC ιL hN hk hg hq hqdvd
  refine ⟨α, hα, fun v σ hv hσ => ?_⟩
  have h1 := htr q hq hqS v σ hv hσ
  rw [trace_dualRep_inv] at h1
  rw [h1, charInv_apply]
  congr 1
  change Φ.symm.symm (coeff g q) = Φ (ιC α)
  rw [hα]
  rfl

end PanBergerSplit
end PkgI4
end HDec
