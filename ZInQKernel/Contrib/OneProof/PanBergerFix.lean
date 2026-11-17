import ZInQKernel.Contrib.OneProof.PanBerger
import ZInQKernel.OneProof.H.TailT

/-!
# `PanBerger` from Pan's and Berger's theorems in their printed forms, repaired (task pb-fix)

pb-bypass (`ZInQKernel/Contrib/OneProof/PanBerger.lean`) split the research field
`r11r12 : HDec.PkgI4.PanBerger` into `PanPrinted` and `BergerPrinted`. A review rated both
*consequence* rather than *printed form*, for two reasons, which this file repairs:

1. **Normalization of "semistable".** pb-bypass's `IsSemistableOver K ρ` compares
   `dim_{ℚ_p} D_st,K` with `dim_{ℚ_p} B_st^{G_K} · dim V`; Fontaine's definition compares it with
   `[K_0 : ℚ_p] · dim V`, `K_0` the maximal absolutely unramified subextension of `K/ℚ_p`. The two
   agree only through Fontaine's theorem `B_st^{G_K} = K_0`. Here `IsSemistableOverT` is stated in
   the printed tensor form `D_st,K(W) = (B_st ⊗_{ℚ_p} W)^{G_K}` with the explicit `[K_0 : ℚ_p]`
   (`K0`), as `IsDeRhamTensorOver` (TailS §15) does for `D_dR`, so that `BergerPrintedT` is
   Berger's Théorème 0.7 with Fontaine's definition and no step about `B_st^{G_K}`.
   `isSemistableOverT_iff` proves it equal to pb-bypass's Hom form with the explicit `[K_0 : ℚ_p]`,
   and `localIsPst_iff_T` proves the new predicate equal to pb-bypass's `LocalIsPst` given
   Fontaine's `dim B_st^{G_K} = [K_0 : ℚ_p]` (`BstInvariantsDim`, a hypothesis there, not a leaf of
   the fold).
2. **`ι_p`-transport.** pb-bypass's `PanPrinted` is pkg-I4's template `PanFor`, whose conclusion
   asks for embeddings `ι_C : ℚ̄ → ℂ`, `ι_L : ℚ̄ → ℚ̄_p` and `α ∈ ℚ̄` with `ι_C(α) = a_q(g)`, i.e. it
   contains the algebraicity of the Hecke eigenvalues, which Pan does not state. `PanPrintedT` is
   Pan's Theorem 1.0.4 with his fixed isomorphism `ι_p : ℚ̄_p ≅ ℂ`, for every `ι_p`:
   `tr ρ(σ) = ψ(σ) · ι_p⁻¹(a_q(g))` at arithmetic Frobenius elements `σ` above almost all `q`.
   `panFor_of_printedT` derives `PanFor` from it with the algebraicity supplied by Diamond–Shurman's
   Thms 9.6.5/9.6.6 (`DSThm965`, `DSThm966`, existing leaves of the same bundle; through
   `r14Det_of_printed`) and an isomorphism `ℂ ≃+* ℚ̄_p` (Steinitz, proved: `exists_complex_equiv`).

Main theorem: `panBerger_of_printedT : PanPrintedT → BergerPrintedT → DSThm965 → DSThm966 →
PanBerger`.

That `B_cris`, `B_st` are nonzero and `t` is not nilpotent (so that `LocalIsPstT` is not trivially
true) is proved by pb-sanity in `ZInQKernel/Contrib/OneProof/PanBergerSanity.lean`
(`nontrivial_bcris`, `logOf_not_isNilpotent`), over the same definitions.

Citations corrected from pb-bypass's docstrings: the admissibility formalism is Brinon–Conrad,
*CMI summer school notes on p-adic Hodge theory* (2009), §5 (Thm 5.2.1), not §6.1; "`V` is
potentially semistable iff `V^∨` is" is Fontaine, *Représentations p-adiques semi-stables*,
Astérisque 223 (1994), Exp. III, 1.5, not Exp. VIII (numbers as given by the review; UNVERIFIED
here, no network).
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace PanBergerSplit

open Module
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

/-! ### `K_0` -/

/-- **`K_0`, the maximal absolutely unramified subextension of `K/ℚ_p`**, as
`ℚ_p(μ_{prime to p}(K))`: the field generated over `ℚ_p` by the roots of unity in `K` of order
prime to `p`. For `K/ℚ_p` finite with residue field `𝔽_q` these are `μ_{q−1}`, and
`ℚ_p(μ_{q−1})` is the maximal unramified subextension (Serre, *Local Fields*, Ch. IV §4;
Neukirch, *Algebraic Number Theory*, II.7.12; STANDARD, numbers UNVERIFIED). This is the field
`K_0` of Fontaine's definition of semistable representations. -/
def K0 (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p]
    {x : PadicAlgCl p | x ∈ K ∧ ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ x ^ m = 1}

theorem K0_le (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : K0 p K ≤ K :=
  IntermediateField.adjoin_le_iff.mpr fun _ hx => hx.1

theorem finrank_K0_pos (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    0 < finrank ℚ_[p] (K0 p K) := by
  have : FiniteDimensional ℚ_[p] (K0 p K) :=
    Module.Finite.of_injective (IntermediateField.inclusion (K0_le p K)).toLinearMap
      (IntermediateField.inclusion (K0_le p K)).injective
  exact finrank_pos

/-- `ℚ_p` is its own `K_0`. -/
theorem finrank_K0_bot : finrank ℚ_[p] (K0 p ⊥) = 1 := by
  have h : K0 p ⊥ = ⊥ := le_bot_iff.mp (K0_le p ⊥)
  rw [h, IntermediateField.finrank_bot]

/-! ### `D_st` in the printed tensor form -/

/-- `σ` on `B_st` as a `ℚ_p`-linear map. -/
def stLin (σ : GQp p) : Bst p →ₗ[ℚ_[p]] Bst p where
  toFun := stAct p σ
  map_add' := map_add _
  map_smul' := stAct_smul p σ

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- `ρ(σ)` on `V = E^n`, as a `ℚ_p`-linear map. -/
def vAct (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E) :=
  (Matrix.mulVecLin (ρ σ : Matrix (Fin n) (Fin n) E)).restrictScalars ℚ_[p]

omit [FiniteDimensional ℚ_[p] E] in
theorem vAct_apply (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (v : Fin n → E) :
    vAct p ρ σ v = Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v := rfl

omit [FiniteDimensional ℚ_[p] E] in
theorem vAct_mul_inv (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (v : Fin n → E) :
    vAct p ρ σ (vAct p ρ σ⁻¹ v) = v := by
  rw [vAct_apply, vAct_apply, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
    map_one, Units.val_one, Matrix.one_mulVec]

omit [FiniteDimensional ℚ_[p] E] in
theorem vAct_inv_mul (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (v : Fin n → E) :
    vAct p ρ σ⁻¹ (vAct p ρ σ v) = v := by
  rw [vAct_apply, vAct_apply, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel,
    map_one, Units.val_one, Matrix.one_mulVec]

/-- The contragredient action on `V^* = Hom_{ℚ_p}(V, ℚ_p)`: `σ · f = f ∘ ρ(σ)⁻¹`. -/
def dualAct (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) :
    Module.Dual ℚ_[p] (Fin n → E) →ₗ[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E) :=
  Module.Dual.transpose (vAct p ρ σ⁻¹)

/-- **`D_st,K(V^*) = (B_st ⊗_{ℚ_p} V^*)^{G_K}`** (Fontaine, Astérisque 223 (1994), Exp. III;
Brinon–Conrad, CMI notes, §9.2; numbers UNVERIFIED), for the contragredient `V^*` of `V = E^n`
with the action `ρ`, and `G_K` the subgroup of `G_{ℚ_p}` fixing `K ⊆ ℚ̄_p`. -/
def dstT (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule ℚ_[p] (Bst p ⊗[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E)) where
  carrier := {x | ∀ σ ∈ K.fixingSubgroup, TensorProduct.map (stLin p σ) (dualAct p ρ σ) x = x}
  zero_mem' σ _ := map_zero _
  add_mem' ha hb σ hσ := by rw [map_add, ha σ hσ, hb σ hσ]
  smul_mem' c x hx σ hσ := by rw [map_smul, hx σ hσ]

/-- **`V^*` is semistable over `K`, in Fontaine's printed form**: `D_st,K(V^*)` has dimension
`dim_{ℚ_p} V^*` over `K_0`, i.e. `dim_{ℚ_p} D_st,K(V^*) = [K_0 : ℚ_p] · dim_{ℚ_p} V^*`
(Fontaine, Astérisque 223, Exp. III, §1 (`B`-admissible representations) with `B = B_st`, whose
`G_K`-invariants are `K_0`; Brinon–Conrad §5, Thm 5.2.1, and §9.2; numbers UNVERIFIED). The
normalization is the explicit `[K_0 : ℚ_p]` (`K0`), so the predicate does not depend on
computing `B_st^{G_K}`. (`D_st,K` is a `K_0`-vector space since `K_0 ⊆ B_st^{G_K}`; pb-sanity
proved this inclusion in dimension form.) -/
def IsSemistableOverT (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Prop :=
  finrank ℚ_[p] (dstT p K ρ) = finrank ℚ_[p] (K0 p K) * finrank ℚ_[p] (Module.Dual ℚ_[p] (Fin n → E))

/-- **`V^*` is potentially semistable** (Fontaine): semistable over some finite `K/ℚ_p`. -/
def IsPstT (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsSemistableOverT p K ρ

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is potentially semistable: it takes values in
`GL_n(E)` for a finite `E/ℚ_p` inside `ℚ̄_p`, and the `E`-representation is potentially
semistable (the same convention as pkg-I4's `LocalIsDeRham`: the space computed on is the
contragredient `V^*` of the underlying `ℚ_p`-representation `V = E^n`). -/
def LocalIsPstT (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPstT p ρE

/-! ### The tensor form equals the Hom form (with the explicit `[K_0 : ℚ_p]`) -/

/-- pb-bypass's Hom form `D_st,K(V^*) = Hom_{G_K}(V, B_st)`, with the explicit `[K_0 : ℚ_p]`. -/
def IsSemistableOverH (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Prop :=
  finrank ℚ_[p] (dstSpace p K ρ) = finrank ℚ_[p] (K0 p K) * (n * finrank ℚ_[p] E)

/-- `B_st ⊗ V^* ≅ Hom(V, B_st)`, `b ⊗ f ↦ (v ↦ f(v) b)`. -/
def stTensorDualEquiv :
    (Bst p ⊗[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E)) ≃ₗ[ℚ_[p]] ((Fin n → E) →ₗ[ℚ_[p]] Bst p) :=
  haveI : Module.Free ℚ_[p] (Fin n → E) := Module.Free.of_divisionRing _ _
  haveI : Module.Finite ℚ_[p] (Fin n → E) := Module.Finite.pi
  (TensorProduct.comm ℚ_[p] (Bst p) (Module.Dual ℚ_[p] (Fin n → E))).trans
    (dualTensorHomEquiv ℚ_[p] (Fin n → E) (Bst p))

theorem stTensorDualEquiv_tmul (b : Bst p) (f : Module.Dual ℚ_[p] (Fin n → E)) (v : Fin n → E) :
    stTensorDualEquiv p (b ⊗ₜ f) v = f v • b := rfl

theorem stTensorDualEquiv_map (ρ : GQp p →* GL (Fin n) E) (σ : GQp p)
    (x : Bst p ⊗[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E)) (v : Fin n → E) :
    stTensorDualEquiv p (TensorProduct.map (stLin p σ) (dualAct p ρ σ) x) v =
      stAct p σ (stTensorDualEquiv p x (vAct p ρ σ⁻¹ v)) := by
  induction x using TensorProduct.inductionOn with
  | tmul b f =>
    rw [TensorProduct.map_tmul, stTensorDualEquiv_tmul, stTensorDualEquiv_tmul, stAct_smul]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply, map_add]

/-- **The tensor form and the Hom form agree** (both with the explicit `[K_0 : ℚ_p]`). -/
theorem isSemistableOverT_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ρ : GQp p →* GL (Fin n) E) : IsSemistableOverT p K ρ ↔ IsSemistableOverH p K ρ := by
  have hmap : Submodule.map (stTensorDualEquiv p).toLinearMap (dstT p K ρ) = dstSpace p K ρ := by
    ext φ
    constructor
    · rintro ⟨x, hx, rfl⟩ σ hσ w
      have h := congrArg (fun y => stTensorDualEquiv p y (vAct p ρ σ w)) (hx σ hσ)
      rw [stTensorDualEquiv_map, vAct_inv_mul] at h
      exact h.symm
    · intro hφ
      refine ⟨(stTensorDualEquiv p).symm φ, fun σ hσ => ?_, by simp⟩
      apply (stTensorDualEquiv p).injective
      refine LinearMap.ext fun v => ?_
      rw [stTensorDualEquiv_map, LinearEquiv.apply_symm_apply]
      have := hφ σ hσ (vAct p ρ σ⁻¹ v)
      rw [← vAct_apply, vAct_mul_inv] at this
      exact this.symm
  have : Module.Free ℚ_[p] E := Module.Free.of_divisionRing _ _
  rw [IsSemistableOverT, IsSemistableOverH, ← hmap, LinearEquiv.finrank_map_eq,
    Subspace.dual_finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Fontaine's `dim_{ℚ_p} B_st^{G_K} = [K_0 : ℚ_p]`** (from `B_st^{G_K} = K_0`: Fontaine,
Astérisque 223 (1994), Exp. II §3 and Exp. III; Brinon–Conrad, CMI notes, §9.2; numbers
UNVERIFIED) for every finite
`K ⊆ ℚ̄_p`, over pb-bypass's `B_st`. Not a leaf of this file's fold: it only relates the new
predicate to pb-bypass's (`localIsPst_iff_T`). -/
def BstInvariantsDim : Prop :=
  ∀ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K →
    finrank ℚ_[p] (bstInv p K) = finrank ℚ_[p] (K0 p K)

/-- Given Fontaine's `dim B_st^{G_K} = [K_0 : ℚ_p]`, pb-bypass's `IsPst` is the printed one. -/
theorem isPst_iff_T (hF : BstInvariantsDim p) (ρ : GQp p →* GL (Fin n) E) :
    IsPst p ρ ↔ IsPstT p ρ := by
  unfold IsPst IsPstT
  refine exists_congr fun K => and_congr_right fun hK => ?_
  rw [isSemistableOverT_iff, IsSemistableOver, IsSemistableOverH, hF K hK]

/-- Given Fontaine's `dim B_st^{G_K} = [K_0 : ℚ_p]`, pb-bypass's `LocalIsPst` is `LocalIsPstT`. -/
theorem localIsPst_iff_T (hF : BstInvariantsDim p) (n : ℕ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : LocalIsPst p n ρ ↔ LocalIsPstT p n ρ := by
  unfold LocalIsPst LocalIsPstT
  refine exists_congr fun E => exists_congr fun hE => exists_congr fun ρE =>
    and_congr_right fun _ => ?_
  exact isPst_iff_T p hF ρE

/-- **Normalization of `IsSemistableOverT` on the trivial representation.** The trivial
one-dimensional representation is semistable over `K` in the printed sense exactly when
`dim_{ℚ_p} B_st^{G_K} = [K_0 : ℚ_p]` (Fontaine's theorem, not in Lean): with the explicit
normalization, even this example rests on `B_st^{G_K} = K_0`. -/
theorem isSemistableOverT_trivial_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IsSemistableOverT p K (1 : GQp p →* GL (Fin 1) ℚ_[p]) ↔
      finrank ℚ_[p] (bstInv p K) = finrank ℚ_[p] (K0 p K) := by
  have h := isSemistableOver_trivial p K
  rw [IsSemistableOver] at h
  rw [isSemistableOverT_iff, IsSemistableOverH, h, finrank_self]
  simp

/-- Given Fontaine's `dim B_st^{G_K} = [K_0 : ℚ_p]`, the trivial representation is potentially
semistable in the printed sense (pb-bypass's `isPst_trivial` transported). -/
theorem isPstT_trivial (hF : BstInvariantsDim p) : IsPstT p (1 : GQp p →* GL (Fin 1) ℚ_[p]) :=
  (isPst_iff_T p hF _).mp (isPst_trivial p)

/-! ### `ℂ ≃+* ℚ̄_p` (Steinitz), copied from `scratch/g8-tate/part_tools.lean` -/

section Steinitz

open Cardinal

/-- The cardinality of `ℚ_p` is at most `𝔠`. -/
theorem padic_card_le : Cardinal.mk ℚ_[p] ≤ 𝔠 := by
  have hex : ∀ x : ℚ_[p], ∀ n : ℕ, ∃ r : ℚ, ‖x - r‖ < 1 / ((n : ℝ) + 1) :=
    fun x n => Padic.rat_dense p x (by positivity)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hpos)
    have h1 := hf x n
    have h2 := hf y n
    rw [hxy] at h1
    have h3 : ‖x - y‖ ≤ ‖x - (f y n : ℚ_[p])‖ + ‖y - (f y n : ℚ_[p])‖ := by
      calc ‖x - y‖ = ‖(x - (f y n : ℚ_[p])) - (y - (f y n : ℚ_[p]))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  calc Cardinal.mk ℚ_[p] ≤ Cardinal.mk (ℕ → ℚ) := mk_le_of_injective hinj
    _ = 𝔠 := by
      rw [← power_def, Cardinal.mkRat, mk_nat, aleph0_power_aleph0]

/-- The cardinality of `ℚ̄_p` is `𝔠`. -/
theorem padicAlgCl_card : Cardinal.mk (PadicAlgCl p) = 𝔠 := by
  have : FaithfulSMul ℚ_[p] (PadicAlgCl p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  have : Module.IsTorsionFree ℚ_[p] (PadicAlgCl p) :=
    Module.IsTorsionFree.trans_faithfulSMul ℚ_[p] (PadicAlgCl p) (PadicAlgCl p)
  apply le_antisymm
  · calc Cardinal.mk (PadicAlgCl p) ≤ max (Cardinal.mk ℚ_[p]) ℵ₀ :=
          Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)
      _ ≤ 𝔠 := max_le (padic_card_le p) aleph0_le_continuum
  · calc 𝔠 ≤ Cardinal.mk ℚ_[p] := continuum_le_cardinal_of_nontriviallyNormedField _
      _ ≤ Cardinal.mk (PadicAlgCl p) := mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective

/-- **`ℂ ≃+* ℚ̄_p`** (Steinitz; Mathlib's `IsAlgClosed.ringEquiv_of_equiv_of_charZero`). -/
theorem exists_complex_equiv : Nonempty (ℂ ≃+* PadicAlgCl p) := by
  have : CharZero (PadicAlgCl p) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  exact IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [mk_complex]; exact aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [mk_complex, padicAlgCl_card]))

end Steinitz

/-! ### The two printed leaves -/

/-- **Pan, Theorem 1.0.4, with his `ι_p`** (L. Pan, *The Fontaine–Mazur conjecture in the
residually reducible case*, J. Amer. Math. Soc. 35 (2022), 1031-1169; = arXiv:1901.07166v2,
Theorem 1.0.4 with Conjecture 1.0.1, p. 5 and p. 2, statement read by h-a011 §1.1 and the locator
audit row R12; JAMS numbering and page UNVERIFIED), for `p ≥ 5` (at `p = 3` Pan excludes a
residual case). Pan fixes an isomorphism `ι_p : ℚ̄_p ≅ ℂ`; the theorem holds for each, hence the
`∀ ιp`. A continuous irreducible `ρ : G_ℚ → GL₂(ℚ̄_p)` ramified at finitely many primes,
potentially semistable at `p`, odd, with distinct Hodge–Tate weights at `p`, "comes from a cuspidal
eigenform up to twist": there are a normalized cuspidal eigenform `g`, a continuous character `ψ`
and a finite set `S` of primes such that `tr ρ(σ) = ψ(σ) · ι_p⁻¹(a_q(g))` for every arithmetic
Frobenius `σ` above every prime `q ∉ S`. No algebraicity of `a_q(g)` is asserted.

Conventions. `LocalIsPstT` and `DistinctHTWeights` are computed on the contragredient `V^*` of
`V = ℚ̄_p^2` (as `LocalIsDeRham`), so the statement is Pan's theorem for `ρ^∨`, read with Pan's
geometric Frobenius: `ρ^∨ ≅ ρ_{g,ι_p} ⊗ ψ'` with `tr ρ_{g,ι_p}(Frob_q) = ι_p⁻¹(a_q(g))` for
`q ∤ Np`, `Frob_q = σ⁻¹` geometric, gives `tr ρ(σ) = tr ρ^∨(σ⁻¹) = ψ'(σ)⁻¹ ι_p⁻¹(a_q(g))`, i.e. the
displayed identity with `ψ = ψ'⁻¹` (the eigenform reading of "comes from a cuspidal eigenform up to
twist": the representation attached to `g` through `ι_p` in the cohomological normalization). -/
def PanPrintedT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsPstT p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    GaloisRep.DistinctHTWeights (ρ := ρ) p →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (S : Finset ℕ), ∀ q : ℕ, q.Prime → q ∉ S →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
          (ρ.mat σ).trace = (ψ.toHom σ : PadicAlgCl p) * ιp.symm (coeff g q)

/-- **Berger, Théorème 0.7** (L. Berger, *Représentations p-adiques et équations
différentielles*, Invent. Math. 148 (2002); Théorème 0.7 = Corollaire 5.22 of the published
version (author copy p. 6 and p. 52, read by the locator audit row R11; Springer pagination
unread) = Théorème 0.6 = Théorème 5.19 of arXiv:math/0102179v3 (read by rv-h-a011)): every de Rham
representation of `G_{ℚ_p}` is potentially semistable, with Fontaine's definition of potentially
semistable (`IsSemistableOverT`: `(B_st ⊗ W)^{G_K}` of dimension `dim W` over `K_0`). pkg-I4's
template `BergerDR` at `LocalIsPstT`. A continuous `ρ` with values in `GL_n(E)`, `E/ℚ_p` finite,
gives the `ℚ_p`-representation `V = E^n`; both predicates are computed on its contragredient `V^*`
(`LocalIsDeRham` as `Hom_{G}(V, B_dR) = (B_dR ⊗ V^*)^{G}`), so this is Berger's theorem applied to
`V^*`. -/
def BergerPrintedT : Prop :=
  BergerDR fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
    LocalIsPstT p n ρ

/-! ### Glue: algebraicity of the coefficients, and `PanFor` -/

/-- **Algebraicity of Hecke eigenvalues (proved from `DSThm965`, `DSThm966`).** For a normalized
eigenform `g` of weight `k ≥ 1` and level `N`, any `ι_C : ℚ̄ → ℂ` and any prime `q ∤ N`,
`a_q(g) ∈ ι_C(ℚ̄)`. Through `r14Det_of_printed` (TailT §18) at an auxiliary prime `ℓ ≠ q`. -/
theorem coeff_mem_range (hD : ZInQ.Contrib.HodgeSplit.DSThm965)
    (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} {χ : DirichletCharacter ℂ N} {g : CF N k}
    (hN : 0 < N) (hk : 1 ≤ k) (hg : IsNormalizedEigenform g χ) {q : ℕ} (hq : q.Prime)
    (hqN : ¬ q ∣ N * ℓ) : ∃ α : Qbar, ιC α = coeff g q := by
  obtain ⟨ρg, -, hatt, -⟩ := ZInQ.Contrib.HodgeSplit.r14Det_of_printed hD hDS ℓ ιC ιL N k χ g hN hk hg
  obtain ⟨-, α, hα, -⟩ := hatt q hq hqN
  exact ⟨α, hα⟩

/-- **`PanFor LocalIsPstT` from `PanPrintedT`** and Diamond–Shurman's Thms 9.6.5/9.6.6 (for the
algebraicity of `a_q(g)`): choose `ι_p : ℚ̄_p ≅ ℂ` (Steinitz), any `ι_C : ℚ̄ → ℂ`, and
`ι_L = ι_p⁻¹ ∘ ι_C`; the exceptional set grows by the ramified primes of `ρ` and the primes
`≤ N p`. -/
theorem panFor_of_printedT (hP : PanPrintedT) (hD : ZInQ.Contrib.HodgeSplit.DSThm965)
    (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) :
    PanFor fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
      LocalIsPstT p n ρ := by
  intro p _ hp ρ hirr hfr hpst hodd hdist
  obtain ⟨Φ⟩ := exists_complex_equiv p
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, S, htr⟩ := hP p hp Φ.symm ρ hirr hfr hpst hodd hdist
  obtain ⟨Sr, hSr⟩ := hfr
  let ιC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ιL : Qbar →ₐ[ℚ] PadicAlgCl p := (Φ : ℂ →+* PadicAlgCl p).toRatAlgHom.comp ιC
  refine ⟨N, k, χ, g, hN, hk, hg, ψ, ιC, ιL, S ∪ Sr ∪ Finset.range (N * p + 1), ?_⟩
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
  rw [htr q hq hqS v σ hv hσ]
  congr 1
  change Φ.symm.symm (coeff g q) = Φ (ιC α)
  rw [hα]
  rfl

/-- **`PanBerger` (the research field `r11r12`) from Pan's and Berger's printed theorems**, with
Diamond–Shurman's Thms 9.6.5 and 9.6.6 (existing leaves `dsThm965`, `dsThm966` of the same bundle)
for the algebraicity of the Hecke eigenvalues. -/
theorem panBerger_of_printedT (hP : PanPrintedT) (hB : BergerPrintedT)
    (hD : ZInQ.Contrib.HodgeSplit.DSThm965) (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) :
    PanBerger := by
  intro p _ hp ρ hirr hfr hdr hodd hdist
  exact panFor_of_printedT hP hD hDS p hp ρ hirr hfr (hB p 2 (ρ.restrictLocal p)
    (ρ.continuous_toHom.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous)
    hdr) hodd hdist

end PanBergerSplit
end PkgI4
end HDec
