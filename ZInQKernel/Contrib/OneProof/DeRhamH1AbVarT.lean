import ZInQKernel.OneProof.H.TailS
import ZInQKernel.Contrib.G9.KerTheta
import ZInQKernel.Contrib.OneProof.HodgeTateDecompAbVar

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

/-! ## The algebra, for any field `B` with a semilinear group action

`K` a field, `B` a field and `K`-algebra, `G` a group acting on `B` by ring automorphisms (`aR`) that are
`K`-linear (`aL`), `ρ` an action of `G` on a finite-dimensional `K`-space `V`. If `dim_K B^G = d > 0` and
`dim_K (B ⊗ V)^G = d · dim V`, then `dim_K Hom_G(V, B) = d · dim V`. -/

namespace Gen

variable {K B G V : Type*} [Field K] [Field B] [Algebra K B] [Group G] [AddCommGroup V] [Module K V]
variable (aL : G → B →ₗ[K] B) (aR : G → B →+* B) (haR : ∀ g x, aL g x = aR g x) (ρ : G → V →ₗ[K] V)

/-- `g ⊗ ρ(g)` on `B ⊗ V`. -/
abbrev Phi (g : G) : B ⊗[K] V →ₗ[K] B ⊗[K] V := TensorProduct.map (aL g) (ρ g)

/-- `(B ⊗ V)^G`. -/
def Dsp : Submodule K (B ⊗[K] V) where
  carrier := {m | ∀ g, Phi aL ρ g m = m}
  zero_mem' g := map_zero _
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  smul_mem' c x hx g := by rw [map_smul, hx g]

/-- `B^G`. -/
def Esp : Submodule K B where
  carrier := {x | ∀ g, aR g x = x}
  zero_mem' g := map_zero _
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  smul_mem' c x hx g := by rw [← haR, map_smul, haR, hx g]

/-- `Hom_G(V, B)`. -/
def Hsp : Submodule K (V →ₗ[K] B) where
  carrier := {φ | ∀ g v, φ (ρ g v) = aR g (φ v)}
  zero_mem' g v := by simp
  add_mem' ha hb g v := by simp only [LinearMap.add_apply, ha g v, hb g v, map_add]
  smul_mem' c φ hφ g v := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hφ g v, ← haR g (c • φ v), (aL g).map_smul, haR]

variable {aL aR ρ}

include haR in
theorem Phi_smul (g : G) (b : B) (m : B ⊗[K] V) : Phi aL ρ g (b • m) = aR g b • Phi aL ρ g m := by
  induction m using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul',
      haR, haR, smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

include haR in
theorem Phi_sum {ι : Type*} [Fintype ι] (x : ι → B ⊗[K] V) (hx : ∀ i, x i ∈ Dsp aL ρ) (c : ι → B) (g : G) :
    Phi aL ρ g (∑ i, c i • x i) = ∑ i, aR g (c i) • x i := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Phi_smul haR, hx i g]

include haR in
theorem coeff_mem_Esp {ι : Type*} [Fintype ι] (x : ι → B ⊗[K] V) (hx : ∀ i, x i ∈ Dsp aL ρ)
    (hli : LinearIndependent B x) (c : ι → B) (hc : ∑ i, c i • x i ∈ Dsp aL ρ) (i : ι) :
    c i ∈ Esp aL aR haR := by
  intro g
  have h := hc g
  rw [Phi_sum haR x hx c g] at h
  have h2 : ∑ j, (aR g (c j) - c j) • x j = 0 := by
    rw [← sub_self (∑ j, c j • x j)]
    nth_rewrite 1 [← h]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => eq_sub_of_add_eq (by rw [← add_smul, sub_add_cancel])
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h2 i)

variable (aL aR) in
/-- `e ↦ Σ eᵢ xᵢ`, from `(B^G)^ι` to `B ⊗ V`. -/
def combo {ι : Type*} [Fintype ι] (x : ι → B ⊗[K] V) : (ι → Esp aL aR haR) →ₗ[K] B ⊗[K] V where
  toFun e := ∑ i, ((e i : B)) • x i
  map_add' e e' := by
    show ∑ i, (((e + e') i : Esp aL aR haR) : B) • x i = ∑ i, ((e i : Esp aL aR haR) : B) • x i +
      ∑ i, ((e' i : Esp aL aR haR) : B) • x i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, Submodule.coe_add, add_smul]
  map_smul' c e := by
    show ∑ i, (((c • e) i : Esp aL aR haR) : B) • x i = c • ∑ i, ((e i : Esp aL aR haR) : B) • x i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Submodule.coe_smul, smul_assoc]

theorem combo_injective {ι : Type*} [Fintype ι] (x : ι → B ⊗[K] V) (hli : LinearIndependent B x) :
    Function.Injective (combo aL aR haR x) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro e he
  funext i
  exact Subtype.ext (Fintype.linearIndependent_iff.mp hli (fun j => (e j : B)) he i)

theorem range_combo {ι : Type*} [Fintype ι] (x : ι → B ⊗[K] V) (hx : ∀ i, x i ∈ Dsp aL ρ)
    (hli : LinearIndependent B x) (hspan : ∀ y ∈ Dsp aL ρ, y ∈ Submodule.span B (Set.range x)) :
    LinearMap.range (combo aL aR haR x) = Dsp aL ρ := by
  ext y
  constructor
  · rintro ⟨e, rfl⟩ g
    change Phi aL ρ g (∑ i, ((e i : B)) • x i) = ∑ i, ((e i : B)) • x i
    rw [Phi_sum haR x hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(e i).2 g]
  · intro hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp (hspan y hy)
    refine ⟨fun i => ⟨c i, coeff_mem_Esp haR x hx hli c (hc ▸ hy) i⟩, ?_⟩
    exact hc

include haR in
theorem lift_Phi (φ : Hsp aL aR haR ρ) (g : G) (m : B ⊗[K] V) :
    (φ : V →ₗ[K] B).liftBaseChange B (Phi aL ρ g m) = aR g ((φ : V →ₗ[K] B).liftBaseChange B m) := by
  induction m using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.map_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, haR,
      φ.2 g v, smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem lbc_add (φ ψ : V →ₗ[K] B) (m : B ⊗[K] V) :
    (φ + ψ).liftBaseChange B m = φ.liftBaseChange B m + ψ.liftBaseChange B m := by
  rw [LinearMap.liftBaseChange, map_add]
  rfl

theorem lbc_smul (c : K) (φ : V →ₗ[K] B) (m : B ⊗[K] V) :
    (c • φ).liftBaseChange B m = c • φ.liftBaseChange B m := by
  induction m using TensorProduct.inductionOn with
  | tmul b v =>
    rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply, smul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

/-- **The equivariant maps `V → B`**: `dim_K Hom_G(V, B) = d · dim V` when `dim_K B^G = d > 0` and
`dim_K (B ⊗ V)^G = d · dim V`. -/
theorem finrank_Hsp [FiniteDimensional K V] {d : ℕ} (hB : finrank K (Esp aL aR haR) = d) (hd : 0 < d)
    (h : finrank K (Dsp aL ρ) = d * finrank K V) : finrank K (Hsp aL aR haR ρ) = d * finrank K V := by
  classical
  set D := Dsp aL ρ
  set n := finrank K V
  haveI hEfin : FiniteDimensional K (Esp aL aR haR) :=
    Module.finite_of_finrank_pos (by rw [hB]; exact hd)
  obtain ⟨b, hbD, hspan, hli⟩ := exists_linearIndependent B (D : Set (B ⊗[K] V))
  haveI : Finite b := hli.finite
  letI : Fintype b := Fintype.ofFinite b
  have hx : ∀ i : b, (i : B ⊗[K] V) ∈ D := fun i => hbD i.2
  have hsp : ∀ y ∈ D, y ∈ Submodule.span B (Set.range ((↑) : b → B ⊗[K] V)) := by
    intro y hy
    rw [Subtype.range_coe, hspan]
    exact Submodule.subset_span hy
  have hrange : LinearMap.range (combo aL aR haR ((↑) : b → B ⊗[K] V)) = D := range_combo haR _ hx hli hsp
  have hfD : finrank K D = Fintype.card b * d := by
    rw [← hrange, LinearMap.finrank_range_of_inj (combo_injective haR _ hli), Module.finrank_pi_fintype,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, hB]
  have hcard : Fintype.card b = n := by
    have h1 : finrank K D = d * n := h
    rw [hfD] at h1
    have : Fintype.card b * d = n * d := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hd this
  have hcardM : Fintype.card b = finrank B (B ⊗[K] V) := by
    rw [Module.finrank_baseChange, hcard]
  let β : Basis b B (B ⊗[K] V) := basisOfLinearIndependentOfCardEqFinrank' _ hli hcardM
  have hβ : ∀ i, β i = (i : B ⊗[K] V) := fun i => by
    simp [β, basisOfLinearIndependentOfCardEqFinrank']
  have hβD : ∀ i, β i ∈ D := fun i => by rw [hβ]; exact hx i
  -- `Ψ : Hom_G(V, B) → (B^G)^b`
  let Ψ : Hsp aL aR haR ρ →ₗ[K] (b → Esp aL aR haR) :=
    { toFun := fun φ i => ⟨(φ : V →ₗ[K] B).liftBaseChange B (β i), fun g => by
        rw [← lift_Phi haR, hβD i g]⟩
      map_add' := fun φ ψ => by
        funext i; apply Subtype.ext
        change ((φ + ψ : Hsp aL aR haR ρ) : V →ₗ[K] B).liftBaseChange B (β i) =
          (φ : V →ₗ[K] B).liftBaseChange B (β i) + (ψ : V →ₗ[K] B).liftBaseChange B (β i)
        rw [Submodule.coe_add, lbc_add]
      map_smul' := fun c φ => by
        funext i; apply Subtype.ext
        change ((c • φ : Hsp aL aR haR ρ) : V →ₗ[K] B).liftBaseChange B (β i) =
          c • (φ : V →ₗ[K] B).liftBaseChange B (β i)
        rw [Submodule.coe_smul, lbc_smul] }
  have hΨ : Function.Injective Ψ := by
    intro φ ψ hφψ
    have h0 : (φ : V →ₗ[K] B).liftBaseChange B = (ψ : V →ₗ[K] B).liftBaseChange B := by
      refine β.ext fun i => ?_
      have := congrArg (fun e => ((e i : Esp aL aR haR) : B)) hφψ
      simpa [Ψ] using this
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 ((1 : B) ⊗ₜ[K] v)
    rwa [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, one_smul, one_smul] at this
  have hmem : ∀ e : b → Esp aL aR haR, ((β.constr B (fun i => (e i : B))).restrictScalars K ∘ₗ
      TensorProduct.mk K B V 1) ∈ Hsp aL aR haR ρ := by
    intro e g v
    have key : ∀ m, β.constr B (fun i => (e i : B)) (Phi aL ρ g m) =
        aR g (β.constr B (fun i => (e i : B)) m) := by
      intro m
      conv_lhs => rw [← β.sum_repr m]
      conv_rhs => rw [← β.sum_repr m]
      rw [Phi_sum haR β hβD, map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, Basis.constr_basis, smul_eq_mul, smul_eq_mul, map_mul, (e i).2 g]
    have h1 : (1 : B) ⊗ₜ[K] (ρ g v) = Phi aL ρ g ((1 : B) ⊗ₜ[K] v) := by
      rw [TensorProduct.map_tmul, haR, map_one]
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, TensorProduct.mk_apply]
    rw [h1, key]
  have hΨs : Function.Surjective Ψ := by
    intro e
    refine ⟨⟨_, hmem e⟩, ?_⟩
    funext i
    apply Subtype.ext
    have hext : ∀ m, ((β.constr B (fun i => (e i : B))).restrictScalars K ∘ₗ
        TensorProduct.mk K B V 1).liftBaseChange B m = β.constr B (fun i => (e i : B)) m := by
      intro m
      induction m using TensorProduct.inductionOn with
      | tmul c v =>
        have hc : c ⊗ₜ[K] v = c • ((1 : B) ⊗ₜ[K] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [LinearMap.liftBaseChange_tmul, hc, map_smul]
        rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    change ((β.constr B (fun i => (e i : B))).restrictScalars K ∘ₗ
      TensorProduct.mk K B V 1).liftBaseChange B (β i) = (e i : B)
    rw [hext, Basis.constr_basis]
  rw [(LinearEquiv.ofBijective Ψ ⟨hΨ, hΨs⟩).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, hB, hcard, mul_comm]

end Gen

/-! ## Instantiation at `B_dR` -/

theorem isField_BdR : IsField (BdR p) := ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p

/-- `B_dR` as a field (the ring structure is Mathlib's). -/
def bdrField : Field (BdR p) := (isField_BdR p).toField

variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- **The dual of a de Rham representation is de Rham** (Fontaine; proved from `B_dR` a field and
`B_dR^{G_F} = F`). In pkg-I4's Hom form: `dim_{ℚ_p} Hom_{G_F}(V, B_dR) = [F:ℚ_p] dim V`. -/
theorem isDeRhamOver_of_tensor [FiniteDimensional ℚ_[p] V]
    (hB : finrank ℚ_[p] (bdrFix p F) = finrank ℚ_[p] F)
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (h : IsDeRhamTensorOver p ρ) :
    IsDeRhamOver p ρ := by
  exact @Gen.finrank_Hsp ℚ_[p] (BdR p) (Field.absoluteGaloisGroup F) V _ (bdrField p)
    (inferInstance : Algebra ℚ_[p] (BdR p)) _ _ _ (fun σ => drAct p (gfToGqp p F σ))
    (fun σ => bdrAct p (gfToGqp p F σ)) (fun _ _ => rfl) (fun σ => ρ σ) _ _ hB Module.finrank_pos h

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

/-- **The chain's field `deRhamH1AbVarT` from the two new leaves and the textbook field
`mumfordTorsionAlgClosed`** (which gives `dim V_p(A) = 2 dim A < ∞` through T26). -/
theorem deRhamH1AbVarT_of_leaves (hdR : DeRhamVpAbVarT) (hB : BdRInvariantsOver)
    (hM : AvSplit.MumfordTorsionAlgClosed) : DeRhamH1AbVarT :=
  deRhamH1AbVarT_of_printed hdR hB fun p _ F _ _ _ A => by
    obtain ⟨g, hg⟩ := dim_finite_I4 A
    exact (HodgeTateDict.finrank_V_of_tateModuleFree p (HodgeTateDict.tateModuleFree_of_mumford hM)
      (HodgeTateDict.natCast_p_ne_zero p F) A g hg).1

end DeRhamDict
