import ZInQKernel.OneProof.H.TailS
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.OneProof.H.LF4T5
import ZInQKernel.Contrib.AbVarBC.G9Instance
import ZInQKernel.Contrib.OneProof.DeRhamPrintTDict

/-!
# derham-print: `deRhamH1AbVarT` from two printed leaves (Fontaine) and the textbook field `mumfordTorsionAlgClosed`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task derham-print, 2026-11-16).
Report: `docs/research/derham-print.md`.

The chain's field `deRhamH1AbVarT : ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (`ZInQKernel/OneProof/H/TailS.lean`)
states that `Hom_{ℚ_p}(V_p A, ℚ_p)` (contragredient action) is de Rham, `dim_{ℚ_p} (B_dR ⊗ V^∨)^{G_F} =
[F:ℚ_p] · dim V^∨`. It was rated GLUE: the printed theorems it cites (Faltings 1989, Tsuji 1999, Scholze 2013
Cor. 1.8) are about `H¹_ét(A_{F̄}, ℚ_p)`, which is `Hom(V_p A, ℚ_p)` only through Milne 1986 Thm 15.1(a), and
Scholze's corollary is about rigid-analytic varieties. None of étale cohomology, algebraic de Rham cohomology or
rigid spaces exists in Mathlib, so those prints cannot be stated over genuine definitions today.

Here the field is proved from:

* `DeRhamVpAbVarPrinted` (printed form): Fontaine's theorem that the Tate module `V_p(A)` of an abelian variety
  over a finite extension of `ℚ_p` is de Rham, with the printed `D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_F}`;
* `BdRInvariantsPrinted` (printed form, dimension): Fontaine's `B_dR^{G_K} = K`, read as `dim_{ℚ_p} B_dR^{G_F} =
  [F:ℚ_p]`;
* `AvSplit.MumfordTorsionAlgClosed` (an existing textbook field), only for `dim V_p(A) < ∞` (via T26).

The step from `V` to `V^∨` (Fontaine's formalism: the dual of an admissible representation is admissible) is a Lean
proof, `Gen.finrank_Hsp`, for any field `B` with a semilinear group action, instantiated at `B_dR` (a field by
bdr-kertheta). That section is copied from dict-galois (`origin/wip/dict-galois` 81d1f67f,
`ZInQKernel/Contrib/OneProof/DeRhamH1AbVarT.lean`, lines 57-275, unchanged), as are the finiteness lemmas from its
`HodgeTateDecompAbVar.lean` (lines 49-79); dict-galois's deRham part was not folded.

The period ring: both leaves are read on the kernel's `B_dR` (Mathlib's `BDeRham 𝓞_ℂ_p p`). For prints defining
`B_dR = Frac(B_dR^+)` or `B_dR^+[1/ξ]` this is definition-level (bdr-kertheta's `isFractionRing_BDeRham`,
`bdREquivAway`); for prints defining `B_dR = B_dR^+[1/t]`, `t = log[ε]` (Berger), the dictionary is
`DeRhamPrint.TDict.bdREquivAwayT` (`DeRhamPrintTDict.lean`), proved here.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace DeRhamPrint

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

/-- **LEAF (printed form, dimension; Fontaine: `B_dR^{G_K} = K`).** Fontaine, *Le corps des périodes p-adiques*,
Astérisque 223 (1994), Exp. II, §1.5 and §3 (locator UNVERIFIED); Brinon–Conrad, *CMI summer school notes on
p-adic Hodge theory* (2009), §4.3-4.4 (`(B_dR)^{G_K} = K`, locator UNVERIFIED). Specialization `K = F` finite over
`ℚ_p`. `G_F` acts on `B_dR(𝓞_ℂ_p)` through pkg-I4's `gfToGqp` (restriction along an embedding `ℚ̄_p ≅ F̄`, whose
image is `G_{F'}`, `F' ⊆ ℚ̄_p` the image of `F`: `HodgeSplit.range_gfToGqp_eq`; the print's `K` is `F'`). Lean
form: `dim_{ℚ_p} B_dR^{G_F} = [F : ℚ_p]`, a consequence of the printed equality of fields (no embedding
`F → B_dR` is needed to state it). Period ring: Fontaine defines `B_dR = Frac(B_dR^+)` (definition-level,
`isFractionRing_BDeRham`); Brinon–Conrad's `B_dR^+[1/t]` or `B_dR^+[1/ξ]` are matched by `TDict.bdREquivAwayT`
and `bdREquivAway`. -/
def BdRInvariantsPrinted : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F],
    finrank ℚ_[p] (bdrFix p F) = finrank ℚ_[p] F

/-- **LEAF (printed form; Fontaine: the Tate module of an abelian variety is de Rham).** For an abelian variety
`A` over a finite extension `K` of `ℚ_p`, `V_p(A)` is a de Rham representation of `G_K`, i.e. `D_dR(V) =
(B_dR ⊗_{ℚ_p} V)^{G_K}` has `K`-dimension `dim_{ℚ_p} V`. Printed: Berger, *An introduction to the theory of p-adic
representations*, in *Geometric aspects of Dwork theory* (de Gruyter, 2004), §I.3 ("the Tate modules … of all
abelian varieties `A` are de Rham", attributed to Fontaine; wording read by h-leaves §3.2, VERIFIED as recorded
there); primary: Fontaine, Ann. of Math. 115 (1982) and LNM 1016 (1983) (statement numbers UNVERIFIED); for
`H^i_ét` of any proper smooth variety, Faltings 1989 and Tsuji 1999, which give it through Milne's
`H¹_ét = V_p(A)^∨`. Lean form: `dim_{ℚ_p} (B_dR ⊗ V_p(A))^{G_F} = [F:ℚ_p] · dim V_p(A)` (`IsDeRhamTensorOver`;
the only translation is `dim_{ℚ_p} = [F:ℚ_p] · dim_F` on the `F`-space `D_dR`), with pkg-I4's `V_p(A) = ℚ_p ⊗ T_p A`
and `G_F` acting through `gfToGqp` as in `BdRInvariantsPrinted`. Period ring: Berger defines `B_dR = B_dR^+[1/t]`,
matched with the kernel's `B_dR` by `TDict.bdREquivAwayT` (with the Galois action, `TDict.ext_of_extends`). -/
def DeRhamVpAbVarPrinted : Prop :=
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

/-! ## Instantiation at `B_dR` (dict-galois, unchanged) -/

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

/-- **The chain's field from the two printed leaves**, given that `V_p(A)` is finite-dimensional. -/
theorem deRhamH1AbVarT_of_printed (hdR : DeRhamVpAbVarPrinted) (hB : BdRInvariantsPrinted)
    (hfd : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
      (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), FiniteDimensional ℚ_[p] (A.V p)) :
    DeRhamH1AbVarT := by
  intro p _ F _ _ _ A
  haveI := hfd p F A
  exact isDeRhamTensorOver_dual p (hB p F) (A.galRep p) (hdR p F A)

/-! ## `dim V_p(A) < ∞` from `mumfordTorsionAlgClosed` (dict-galois's `HodgeTateDecompAbVar.lean`, unchanged) -/

omit [FiniteDimensional ℚ_[p] F] in
theorem natCast_p_ne_zero (F : Type) [Field F] [Algebra ℚ_[p] F] : (p : F) ≠ 0 := by
  have h : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [← map_natCast (algebraMap ℚ_[p] F)]
  exact (map_ne_zero_iff _ (algebraMap ℚ_[p] F).injective).mpr h

/-- The chain's `A` as a kernel `PkgI3.AbVar` (same fields). -/
def toKer {F : Type} [Field F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : _root_.PkgI3.AbVar F :=
  @_root_.PkgI3.AbVar.mk F _ A.X A.grp A.proper A.smooth A.geomInt

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj in
/-- **`V_p(A)` is finite-dimensional of dimension `2 dim A`** over a field `F` with `(p : F) ≠ 0`, from T26
(`PkgI3.TateModuleFree`). -/
theorem finrank_V_of_tateModuleFree (hT : _root_.PkgI3.TateModuleFree) {F : Type} [Field F] (hp : (p : F) ≠ 0)
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) :
    FiniteDimensional ℚ_[p] (A.V p) ∧ finrank ℚ_[p] (A.V p) = 2 * g := by
  obtain ⟨hfree, hfin, hrk⟩ := hT F (toKer A) p hp
  have e1 : finrank ℚ_[p] (A.V p) = finrank ℤ_[p] ((toKer A).T p) :=
    ((ZInQ.Contrib.AbVarBC.vToI4 p (toKer A)).finrank_eq).trans Module.finrank_baseChange
  have hdim : (toKer A).dim = (g : WithBot ℕ∞) := hg
  rw [hdim] at hrk
  have h2 : finrank ℤ_[p] ((toKer A).T p) = 2 * g := by
    have h' : (((finrank ℤ_[p] ((toKer A).T p) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((2 * g : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [hrk]; push_cast; rfl
    exact Nat.cast_injective (WithBot.coe_injective h')
  refine ⟨?_, e1.trans h2⟩
  change FiniteDimensional ℚ_[p] (TensorProduct ℤ_[p] ℚ_[p] ((toKer A).T p))
  infer_instance

/-- T26 from the chain's textbook field `mumfordTorsionAlgClosed`. -/
theorem tateModuleFree_of_mumford (hM : AvSplit.MumfordTorsionAlgClosed) : _root_.PkgI3.TateModuleFree :=
  T5Torsion.TateFree.tateModuleFree_of_torsionStructure (AvSplit.Final.h25 hM)

end

/-- **The chain's field `deRhamH1AbVarT` from the two printed leaves and the textbook field
`mumfordTorsionAlgClosed`** (which gives `dim V_p(A) = 2 dim A < ∞` through T26). -/
theorem deRhamH1AbVarT_of_leaves (hdR : DeRhamVpAbVarPrinted) (hB : BdRInvariantsPrinted)
    (hM : AvSplit.MumfordTorsionAlgClosed) : DeRhamH1AbVarT :=
  deRhamH1AbVarT_of_printed hdR hB fun p _ F _ _ _ A => by
    obtain ⟨g, hg⟩ := dim_finite_I4 A
    exact (finrank_V_of_tateModuleFree p (tateModuleFree_of_mumford hM) (natCast_p_ne_zero p F) A g hg).1

/-- **The consumer's form.** The only reader of the field (`TailX.lean`, through
`deRhamComparisonHT_of_leavesT`) converts it to pkg-I4's `IsDeRhamOver p (A.galRep p)` (dimension of
`Hom_{G_F}(V_p A, B_dR)`); the same from the leaves directly. -/
theorem isDeRhamOver_of_leaves (hdR : DeRhamVpAbVarPrinted) (hB : BdRInvariantsPrinted)
    (hM : AvSplit.MumfordTorsionAlgClosed) (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : IsDeRhamOver p (A.galRep p) := by
  obtain ⟨g, hg⟩ := dim_finite_I4 A
  haveI := (finrank_V_of_tateModuleFree p (tateModuleFree_of_mumford hM) (natCast_p_ne_zero p F) A g hg).1
  exact isDeRhamOver_of_tensor p (hB p F) (A.galRep p) (hdR p F A)

end DeRhamPrint
