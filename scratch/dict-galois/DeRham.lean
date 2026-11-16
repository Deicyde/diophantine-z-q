import ZInQKernel.OneProof.H.TailS
import ZInQKernel.Contrib.G9.KerTheta

/-!
# dict-galois (1): `deRhamH1AbVarT` from "`V_p(A)` is de Rham" and `B_dR^{G_F} = F`

The chain's field `deRhamH1AbVarT : ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (`TailS.lean`) states that
`Hom(V_p A, ℚ_p)` (contragredient action) is de Rham; that module is `H¹_ét(A_{F̄}, ℚ_p)` only through Milne 1986,
Thm 15.1(a). The new leaf `DeRhamVpAbVarT` states that `V_p(A)` itself is de Rham, with the printed
`D_dR(V) = (B_dR ⊗ V)^{G_F}`, as Fontaine's statement is recorded (Berger 2004, I.3). The dual is de Rham by a Lean
proof (glue) from `B_dR` being a field (kernel, bdr-kertheta) and the leaf `BdRInvariantsOver`
(`B_dR^{G_F} = F`, Fontaine), via the standard argument: `D_dR(V)` contains a `B_dR`-basis of `B_dR ⊗ V`
whose coordinates are `G_F`-invariant, and the `B_dR`-linear functionals with invariant values on that basis are
the equivariant maps `V → B_dR`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace DeRhamDict

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- `B_dR^{G_F}`, the `G_F`-invariants of `B_dR` (`G_F` acting through `gfToGqp`), a `ℚ_p`-subspace. -/
def bdrFix (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] : Submodule ℚ_[p] (BdR p) where
  carrier := {x | ∀ σ : Field.absoluteGaloisGroup F, bdrAct p (gfToGqp p F σ) x = x}
  zero_mem' σ := map_zero _
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  smul_mem' c x hx σ := by rw [bdrAct_smul, hx σ]

/-- **LEAF (Fontaine: `B_dR^{G_K} = K`; locator UNVERIFIED).** Fontaine, *Le corps des périodes p-adiques*,
Astérisque 223 (1994), Exp. II, §1.5 and §3; Brinon–Conrad, *CMI summer school notes on p-adic Hodge theory*
(2009), §4.4 (`(B_dR)^{G_K} = K`). Specialization: `K = F` finite over `ℚ_p`, `G_F` acting on Mathlib's
`B_dR(𝓞_ℂ_p)` through pkg-I4's `gfToGqp` (an embedding `ℚ̄_p ≅ F̄`, which identifies `ℂ_F` with `ℂ_p`). Lean form:
the `ℚ_p`-dimension of `B_dR^{G_F}` is `[F : ℚ_p]` (the dimension of `K`; no embedding `F → B_dR` is needed to
state it). A consequence of the printed statement. -/
def BdRInvariantsOver : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F],
    finrank ℚ_[p] (bdrFix p F) = finrank ℚ_[p] F

/-- **LEAF (`V_p(A)` is de Rham; Fontaine's statement as recorded by Berger 2004, I.3; locator UNVERIFIED).**
Berger, *An introduction to the theory of p-adic representations*, in: Geometric aspects of Dwork theory (de
Gruyter 2004), §I.3: for an abelian variety `A` over a finite extension `F` of `ℚ_p`, `V_p(A)` is a de Rham
representation of `G_F` (Fontaine 1982 for abelian varieties; Faltings 1989; Tsuji 1999; Scholze 2013 for
`H^i_ét` of proper smooth varieties). Lean form: `dim_{ℚ_p} (B_dR ⊗ V_p(A))^{G_F} = [F:ℚ_p] · dim V_p(A)`, i.e.
`dim_F D_dR(V_p A) = dim V_p A`, with pkg-I4's `V_p(A) = ℚ_p ⊗ T_p A` and `G_F` acting through `gfToGqp`. -/
def DeRhamVpAbVarT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), IsDeRhamTensorOver p (A.galRep p)

/-! ## `B_dR` as a field, the semilinear action on `B_dR ⊗ V` -/

theorem isField_BdR : IsField (BdR p) := ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p

/-- `B_dR` as a field (the ring structure is Mathlib's). -/
def bdrField : Field (BdR p) := (isField_BdR p).toField

attribute [local instance] bdrField

variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- `σ ⊗ ρ(σ)` on `B_dR ⊗ V`. -/
abbrev Phi (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (σ : Field.absoluteGaloisGroup F) :
    BdR p ⊗[ℚ_[p]] V →ₗ[ℚ_[p]] BdR p ⊗[ℚ_[p]] V :=
  TensorProduct.map (drAct p (gfToGqp p F σ)) (ρ σ)

/-- `σ ⊗ ρ(σ)` is `σ`-semilinear for the `B_dR`-module structure. -/
theorem Phi_smul (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (σ : Field.absoluteGaloisGroup F)
    (b : BdR p) (m : BdR p ⊗[ℚ_[p]] V) :
    Phi p ρ σ (b • m) = bdrAct p (gfToGqp p F σ) b • Phi p ρ σ m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul',
      drAct_apply, drAct_apply, smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem mem_ddrTensorOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (m : BdR p ⊗[ℚ_[p]] V) :
    m ∈ ddrTensorOver p ρ ↔ ∀ σ, Phi p ρ σ m = m := Iff.rfl

theorem mem_bdrFix (b : BdR p) : b ∈ bdrFix p F ↔ ∀ σ : Field.absoluteGaloisGroup F, bdrAct p (gfToGqp p F σ) b = b :=
  Iff.rfl

/-! ## Step 1: `D_dR(V) ≅ (B_dR^{G_F})^r` for a `B_dR`-basis of its span -/

/-- `Φ_σ (Σ cᵢ xᵢ) = Σ σ(cᵢ) xᵢ` for `xᵢ ∈ D_dR(V)`. -/
theorem Phi_sum {ι : Type*} [Fintype ι] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (x : ι → BdR p ⊗[ℚ_[p]] V) (hx : ∀ i, x i ∈ ddrTensorOver p ρ) (c : ι → BdR p)
    (σ : Field.absoluteGaloisGroup F) :
    Phi p ρ σ (∑ i, c i • x i) = ∑ i, bdrAct p (gfToGqp p F σ) (c i) • x i := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Phi_smul, (mem_ddrTensorOver p ρ _).mp (hx i) σ]

/-- The coordinates of an invariant vector in a `B_dR`-independent family of invariant vectors are
invariant. -/
theorem coeff_mem_bdrFix {ι : Type*} [Fintype ι] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (x : ι → BdR p ⊗[ℚ_[p]] V) (hx : ∀ i, x i ∈ ddrTensorOver p ρ) (hli : LinearIndependent (BdR p) x)
    (c : ι → BdR p) (hc : ∑ i, c i • x i ∈ ddrTensorOver p ρ) (i : ι) : c i ∈ bdrFix p F := by
  intro σ
  have h := (mem_ddrTensorOver p ρ _).mp hc σ
  rw [Phi_sum p ρ x hx c σ] at h
  have h2 : ∑ j, (bdrAct p (gfToGqp p F σ) (c j) - c j) • x j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h2 i)

/-- `e ↦ Σ eᵢ xᵢ`, from `(B_dR^{G_F})^ι` to `B_dR ⊗ V`. -/
def combo {ι : Type*} [Fintype ι] (x : ι → BdR p ⊗[ℚ_[p]] V) :
    (ι → bdrFix p F) →ₗ[ℚ_[p]] BdR p ⊗[ℚ_[p]] V where
  toFun e := ∑ i, ((e i : BdR p)) • x i
  map_add' e e' := by simp only [Pi.add_apply, Submodule.coe_add, add_smul, Finset.sum_add_distrib]
  map_smul' c e := by
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_assoc]

theorem combo_injective {ι : Type*} [Fintype ι] (x : ι → BdR p ⊗[ℚ_[p]] V)
    (hli : LinearIndependent (BdR p) x) : Function.Injective (combo p (F := F) x) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro e he
  funext i
  exact Subtype.ext (Fintype.linearIndependent_iff.mp hli (fun j => (e j : BdR p)) he i)

theorem range_combo {ι : Type*} [Fintype ι] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (x : ι → BdR p ⊗[ℚ_[p]] V) (hx : ∀ i, x i ∈ ddrTensorOver p ρ) (hli : LinearIndependent (BdR p) x)
    (hspan : ∀ y ∈ ddrTensorOver p ρ, y ∈ Submodule.span (BdR p) (Set.range x)) :
    LinearMap.range (combo p (F := F) x) = ddrTensorOver p ρ := by
  ext y
  constructor
  · rintro ⟨e, rfl⟩ σ
    change Phi p ρ σ (∑ i, ((e i : BdR p)) • x i) = ∑ i, ((e i : BdR p)) • x i
    rw [Phi_sum p ρ x hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(e i).2 σ]
  · intro hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (BdR p)).mp (hspan y hy)
    refine ⟨fun i => ⟨c i, coeff_mem_bdrFix p ρ x hx hli c (hc ▸ hy) i⟩, ?_⟩
    exact hc

/-! ## Step 2: the equivariant maps `V → B_dR` -/

/-- The `B_dR`-linear extension `B_dR ⊗ V → B_dR`, `c ⊗ v ↦ c φ(v)`, of an equivariant `φ` is equivariant. -/
theorem lift_Phi (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (φ : ddrSpaceOver p ρ)
    (σ : Field.absoluteGaloisGroup F) (m : BdR p ⊗[ℚ_[p]] V) :
    (φ : V →ₗ[ℚ_[p]] BdR p).liftBaseChange (BdR p) (Phi p ρ σ m) =
      bdrAct p (gfToGqp p F σ) ((φ : V →ₗ[ℚ_[p]] BdR p).liftBaseChange (BdR p) m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [TensorProduct.map_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, drAct_apply,
      φ.2 σ v, smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **The dual of a de Rham representation is de Rham** (Fontaine; proved from `B_dR` a field and
`B_dR^{G_F} = F`). In pkg-I4's Hom form: `dim_{ℚ_p} Hom_{G_F}(V, B_dR) = [F:ℚ_p] dim V`. -/
theorem isDeRhamOver_of_tensor [FiniteDimensional ℚ_[p] V]
    (hB : finrank ℚ_[p] (bdrFix p F) = finrank ℚ_[p] F)
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (h : IsDeRhamTensorOver p ρ) :
    IsDeRhamOver p ρ := by
  classical
  set D := ddrTensorOver p ρ
  set n := finrank ℚ_[p] V
  set d := finrank ℚ_[p] F
  have hd : 0 < d := Module.finrank_pos
  haveI hEfin : FiniteDimensional ℚ_[p] (bdrFix p F) :=
    Module.finite_of_finrank_pos (by rw [hB]; exact hd)
  -- a `B_dR`-basis of the span of `D` inside `D`
  obtain ⟨b, hbD, hspan, hli⟩ := exists_linearIndependent (BdR p) (D : Set (BdR p ⊗[ℚ_[p]] V))
  haveI : Finite b := hli.finite
  letI : Fintype b := Fintype.ofFinite b
  have hx : ∀ i : b, (i : BdR p ⊗[ℚ_[p]] V) ∈ D := fun i => hbD i.2
  have hsp : ∀ y ∈ D, y ∈ Submodule.span (BdR p) (Set.range ((↑) : b → BdR p ⊗[ℚ_[p]] V)) := by
    intro y hy
    rw [Subtype.range_coe, hspan]
    exact Submodule.subset_span hy
  have hrange := range_combo p ρ _ hx hli hsp
  have hfD : finrank ℚ_[p] D = Fintype.card b * d := by
    rw [← hrange, LinearMap.finrank_range_of_inj (combo_injective p _ hli), Module.finrank_pi_fintype,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, hB]
  have hcard : Fintype.card b = n := by
    have h1 : finrank ℚ_[p] D = d * n := h
    rw [hfD] at h1
    have : Fintype.card b * d = n * d := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hd this
  have hcardM : Fintype.card b = finrank (BdR p) (BdR p ⊗[ℚ_[p]] V) := by
    rw [Module.finrank_baseChange, hcard]
  let β : Basis b (BdR p) (BdR p ⊗[ℚ_[p]] V) := basisOfLinearIndependentOfCardEqFinrank hli hcardM
  have hβ : ∀ i, β i = (i : BdR p ⊗[ℚ_[p]] V) := fun i => by
    simp [β, basisOfLinearIndependentOfCardEqFinrank]
  have hβD : ∀ i, β i ∈ D := fun i => by rw [hβ]; exact hx i
  have hβli : LinearIndependent (BdR p) β := β.linearIndependent
  -- `Ψ : Hom_{G_F}(V, B_dR) → (B_dR^{G_F})^b`
  let Ψ : ddrSpaceOver p ρ →ₗ[ℚ_[p]] (b → bdrFix p F) :=
    { toFun := fun φ i => ⟨(φ : V →ₗ[ℚ_[p]] BdR p).liftBaseChange (BdR p) (β i), fun σ => by
        rw [← lift_Phi, (mem_ddrTensorOver p ρ _).mp (hβD i) σ]⟩
      map_add' := fun φ ψ => by
        funext i; apply Subtype.ext
        simp [LinearMap.liftBaseChange_add]
      map_smul' := fun c φ => by
        funext i; apply Subtype.ext
        simp [LinearMap.liftBaseChange_smul] }
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    have h0 : (φ : V →ₗ[ℚ_[p]] BdR p).liftBaseChange (BdR p) = 0 := by
      refine β.ext fun i => ?_
      have := congrArg (fun e => ((e i : bdrFix p F) : BdR p)) hφ
      simpa [Ψ] using this
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 ((1 : BdR p) ⊗ₜ[ℚ_[p]] v)
    rw [LinearMap.liftBaseChange_tmul, one_smul] at this
    simpa using this
  haveI : FiniteDimensional ℚ_[p] (ddrSpaceOver p ρ) := Module.Finite.of_injective Ψ hΨ
  have hle : finrank ℚ_[p] (ddrSpaceOver p ρ) ≤ Fintype.card b * d := by
    have := LinearMap.finrank_le_finrank_of_injective hΨ
    rwa [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, hB] at this
  -- `Θ : (B_dR^{G_F})^b → Hom_{G_F}(V, B_dR)`
  have hΘmem : ∀ e : b → bdrFix p F, ((β.constr (BdR p) (fun i => (e i : BdR p))).restrictScalars ℚ_[p] ∘ₗ
      TensorProduct.mk ℚ_[p] (BdR p) V 1) ∈ ddrSpaceOver p ρ := by
    intro e σ v
    set f := β.constr (BdR p) (fun i => (e i : BdR p))
    have key : ∀ m, f (Phi p ρ σ m) = bdrAct p (gfToGqp p F σ) (f m) := by
      intro m
      conv_lhs => rw [← β.sum_repr m]
      conv_rhs => rw [← β.sum_repr m]
      rw [Phi_sum p ρ β hβD, map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, Basis.constr_basis, Basis.constr_basis, smul_eq_mul, smul_eq_mul, map_mul,
        (e i).2 σ]
    have h1 : (1 : BdR p) ⊗ₜ[ℚ_[p]] (ρ σ v) = Phi p ρ σ ((1 : BdR p) ⊗ₜ[ℚ_[p]] v) := by
      rw [TensorProduct.map_tmul, drAct_apply, map_one]
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, TensorProduct.mk_apply]
    rw [h1, key]
  let Θ : (b → bdrFix p F) →ₗ[ℚ_[p]] ddrSpaceOver p ρ :=
    { toFun := fun e => ⟨_, hΘmem e⟩
      map_add' := fun e e' => by
        apply Subtype.ext
        refine LinearMap.ext fun v => ?_
        simp only [Pi.add_apply, Submodule.coe_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
          Function.comp_apply, TensorProduct.mk_apply, LinearMap.add_apply]
        rw [show (fun i => ((e i : BdR p) + (e' i : BdR p))) = (fun i => (e i : BdR p)) + (fun i => (e' i : BdR p))
          from rfl, map_add, LinearMap.add_apply]
      map_smul' := fun c e => by
        apply Subtype.ext
        refine LinearMap.ext fun v => ?_
        simp only [Pi.smul_apply, Submodule.coe_smul, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
          Function.comp_apply, TensorProduct.mk_apply, RingHom.id_apply, LinearMap.smul_apply]
        rw [show (fun i => c • (e i : BdR p)) = c • (fun i => (e i : BdR p)) from rfl, map_smul,
          LinearMap.smul_apply] }
  have hΘ : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    set f := β.constr (BdR p) (fun i => (e i : BdR p))
    have h1 : ∀ v, f ((1 : BdR p) ⊗ₜ[ℚ_[p]] v) = 0 := fun v => by
      have := LinearMap.congr_fun (congrArg Subtype.val he) v
      simpa [Θ, f] using this
    have h2 : f = 0 := by
      refine LinearMap.ext fun m => ?_
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul c v =>
        have : c ⊗ₜ[ℚ_[p]] v = c • ((1 : BdR p) ⊗ₜ[ℚ_[p]] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, h1, smul_zero, LinearMap.zero_apply]
      | add x y hx hy => rw [map_add, hx, hy, LinearMap.zero_apply, add_zero]
    funext i
    apply Subtype.ext
    have := LinearMap.congr_fun h2 (β i)
    rw [Basis.constr_basis] at this
    simpa using this
  have hge : Fintype.card b * d ≤ finrank ℚ_[p] (ddrSpaceOver p ρ) := by
    have := LinearMap.finrank_le_finrank_of_injective hΘ
    rwa [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, hB] at this
  change finrank ℚ_[p] (ddrSpaceOver p ρ) = d * n
  rw [le_antisymm hle hge, hcard, mul_comm]

/-- **The dual of a de Rham representation is de Rham, tensor form.** -/
theorem isDeRhamTensorOver_dual [FiniteDimensional ℚ_[p] V]
    (hB : finrank ℚ_[p] (bdrFix p F) = finrank ℚ_[p] F)
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (h : IsDeRhamTensorOver p ρ) :
    IsDeRhamTensorOver p ρ.dual :=
  (isDeRhamOver_iff_tensor_dual p ρ).mpr (isDeRhamOver_of_tensor p hB ρ h)

/-- **The chain's field from the two new leaves**, given that `V_p(A)` is finite-dimensional. -/
theorem deRhamH1AbVarT_of_printed (hdR : DeRhamVpAbVarT) (hB : BdRInvariantsOver)
    (hfd : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
      (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), FiniteDimensional ℚ_[p] (A.V p)) :
    DeRhamH1AbVarT := by
  intro p _ F _ _ _ A
  haveI := hfd p F A
  exact isDeRhamTensorOver_dual p (hB p F) (A.galRep p) (hdR p F A)

end

end DeRhamDict
