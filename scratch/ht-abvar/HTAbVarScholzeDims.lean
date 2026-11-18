import ZInQKernel.Contrib.OneProof.DeRhamScholzeHT

/-!
# ht-abvar: the field `hodgeTateDecompAbVar` from the manuscript's route (`lem:de-rham-descent`, L10996-10997)

Task ht-abvar (2026-11-17; report `docs/research/ht-abvar.md`).

The H-bundle field `hodgeTateDecompAbVar` (`ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar`, `TailS.lean`) asks for the
Hodge–Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g` of an abelian variety of dimension `g` over a finite
`F/ℚ_p`. On the current route the multiplicities `(g, g)` come from the Weil pairing of a symmetric isogeny
`A → A^∨`, i.e. from the Picard rows (`hodgeTateDecompAbVar_of_open_k954`, TailZ69).

The manuscript reads the multiplicities off the Hodge numbers instead (diophantine_zq.tex L10996-10997: the two
Hodge numbers of `H¹_dR(A/F)` are `2, 2`, "consequently" the weights are `0,0,−1,−1`), through Scholze's filtered
comparison `D_dR(H¹_ét) ≅ H¹_dR(A/F)` (Cor. 1.8, cited at L736-737 and used in the lemma's first paragraph).
derham-scholze's leaves give de Rham with Hodge jumps in `[0, 1]` but no dimension of a graded piece, so one leaf
is added:

* `HodgeNumberH1AbVar` (LEAF, consequence): `dim_{ℚ_p} Fil¹ D_dR(H¹_ét(A_{F̄}, ℚ_p)) = [F:ℚ_p] · g`.

The rest is proved here: Fontaine's `gr D_dR ≅ D_HT` with dimensions (`hodgeTate01_dims`: `gr¹ D_dR ↪
Hom_{G_F}(V, ℂ_p(1))`, `gr⁰ D_dR ↪ Hom_{G_F}(V, ℂ_p)`, and Tate–Sen, derham-scholze's maps), Milne's
identification to move `Fil¹` from `H¹_ét` to `V_p(A)^∨`, `dim V_p(A) = 2g`, and the `ℂ_p`-dualization from the Hom
form to the tensor form (htdecomp-or's `dualEquiv`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
set_option synthInstance.maxHeartbeats 400000

namespace DeRhamScholze.HTAbVar

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open DeRhamScholze.HT
open scoped TensorProduct

noncomputable section

/-! ## §1. The leaf -/

/-- **LEAF (consequence; the manuscript's Hodge numbers through Scholze's filtered comparison).**
diophantine_zq.tex `lem:de-rham-descent`, L10996: "The two Hodge numbers of `H¹_dR(A/F)` are `2,2`" (abelian surface;
no citation, ELLIOT), carried to `D_dR(H¹_ét)` by the filtered isomorphism `D_dR(H¹_ét(A_{F̄}, ℚ_p)) ≅ H¹_dR(A/F)` of
Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 with Thms 9.1, 9.3 (cited at L736-737; applied in the lemma's first
paragraph, L10953-10965). For an abelian variety of dimension `g` the Hodge filtration of `H¹_dR(A/F)` has
`Fil¹ = H⁰(A, Ω¹)` of dimension `g` (Hodge–de Rham degeneration; `Ω¹_A` free of rank `g`; standard, e.g. Mumford,
*Abelian varieties*, §4; locator UNVERIFIED), so `dim_F Fil¹ D_dR(H¹_ét) = g`.

Lean form, over the objects of `DeRhamScholze.ScholzeDeRhamAlg`: `H¹_ét(A_{F̄}, ℚ_p) = ℚ_p ⊗ H¹(A_{F̄}, ℤ_p)` with
Mathlib's pro-étale `ℓ`-adic cohomology (`HQ`, `rhoH`), `Fil^j D_dR = D_dR ∩ (t^j B_dR^+ ⊗ W)` (`filD`), dimension
over `ℚ_p` (`= [F:ℚ_p] · dim_F`). Not printed form: `H_dR` is not in Mathlib, so the Hodge number is stated on the
étale side of the comparison. -/
def HodgeNumberH1AbVar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * g

/-! ## §2. Fontaine's `gr D_dR ≅ D_HT` with dimensions (jumps in `[0, 1]`) -/

section Dims

variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)

section Fil1

variable {t : BDeRhamPlus 𝓞_ℂ_[p] p} (ht : IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = Ideal.span {t})

include ht in
/-- **`gr¹ : D_dR ∩ Fil¹ ↪ Hom_{G_F}(V, ℂ_p(1))` and `ker gr⁰ ⊆ Fil¹`** (Hodge jumps in `[0, 1]`): the two bounds
`dim (D_dR ∩ Fil¹) ≤ dim Hom_{G_F}(V, ℂ_p(1))` and `dim D_dR ≤ dim Hom_{G_F}(V, ℂ_p) + dim (D_dR ∩ Fil¹)`
(the dimension form of derham-scholze's `finrank_ddr_le`). -/
theorem finrank_fil1_bounds (hσ : ∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (cycPow p σ 1) * t)
    (h0 : ddrSpaceOver p ρ ≤ filH p 0) (h2 : ddrSpaceOver p ρ ⊓ filH p 2 = ⊥)
    [FiniteDimensional ℚ_[p] (htSpaceOver p ρ 0)] [FiniteDimensional ℚ_[p] (htSpaceOver p ρ 1)] :
    finrank ℚ_[p] (ddrSpaceOver p ρ ⊓ filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) ≤
        finrank ℚ_[p] (htSpaceOver p ρ 1) ∧
      finrank ℚ_[p] (ddrSpaceOver p ρ) ≤ finrank ℚ_[p] (htSpaceOver p ρ 0) +
        finrank ℚ_[p] (ddrSpaceOver p ρ ⊓ filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) := by
  letI : AddCommGroup (ddrSpaceOver p ρ) := Module.addCommMonoidToAddCommGroup ℚ_[p]
  let S1 : Submodule ℚ_[p] (ddrSpaceOver p ρ) :=
    Submodule.comap (ddrSpaceOver p ρ).subtype (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p))
  let eS : S1 ≃ₗ[ℚ_[p]] (ddrSpaceOver p ρ ⊓ filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) :=
    { toFun := fun φ => ⟨φ.1.1, Submodule.mem_inf.mpr ⟨φ.1.2, φ.2⟩⟩
      invFun := fun ψ => ⟨⟨ψ.1, (Submodule.mem_inf.mp ψ.2).1⟩, (Submodule.mem_inf.mp ψ.2).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let incl1 : S1 →ₗ[ℚ_[p]] (filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) :=
    { toFun := fun φ => ⟨φ.1.1, φ.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let G1 : S1 →ₗ[ℚ_[p]] htSpaceOver p ρ 1 :=
    LinearMap.codRestrict _ (gr1 ht ∘ₗ incl1) (fun φ => gr1_mem ρ ht hσ _ φ.1.2)
  have hG1 : Function.Injective G1 := by
    refine (injective_iff_map_eq_zero G1).mpr fun φ hφ => ?_
    have h3 : gr1 ht (incl1 φ) = 0 := congrArg Subtype.val hφ
    have h4 : φ.1.1 ∈ ddrSpaceOver p ρ ⊓ filH p 2 :=
      Submodule.mem_inf.mpr ⟨φ.1.2, mem_filH2_of_gr1 ht (incl1 φ) h3⟩
    rw [h2, Submodule.mem_bot] at h4
    exact Subtype.ext (Subtype.ext h4)
  have hrk1 : Module.rank ℚ_[p] S1 ≤ finrank ℚ_[p] (htSpaceOver p ρ 1) := by
    rw [Module.finrank_eq_rank]; exact LinearMap.rank_le_of_injective G1 hG1
  have hS1 : finrank ℚ_[p] S1 ≤ finrank ℚ_[p] (htSpaceOver p ρ 1) := Module.finrank_le_of_rank_le hrk1
  let G0 : ddrSpaceOver p ρ →ₗ[ℚ_[p]] htSpaceOver p ρ 0 :=
    LinearMap.codRestrict _ (gr0 ∘ₗ Submodule.inclusion h0) (fun φ => gr0_mem ρ _ φ.2)
  have hker : LinearMap.ker G0 ≤ S1 := fun φ hφ =>
    mem_filH1_of_gr0 ht ⟨φ.1, h0 φ.2⟩ (congrArg Subtype.val (LinearMap.mem_ker.mp hφ))
  haveI : FiniteDimensional ℚ_[p] S1 :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrk1 (Cardinal.natCast_lt_aleph0))
  have hrk : Module.rank ℚ_[p] (ddrSpaceOver p ρ) ≤
      ((finrank ℚ_[p] (htSpaceOver p ρ 0) + finrank ℚ_[p] S1 : ℕ) : Cardinal) := by
    rw [← LinearMap.rank_range_add_rank_ker G0, Nat.cast_add]
    refine add_le_add ?_ ?_
    · rw [Module.finrank_eq_rank]; exact Submodule.rank_le _
    · rw [Module.finrank_eq_rank]; exact Submodule.rank_mono hker
  rw [← eS.finrank_eq]
  exact ⟨hS1, Module.finrank_le_of_rank_le hrk⟩

end Fil1

/-- The coordinate isomorphism of a `ℂ_p`-basis made of `F'`-bases of `Hom_{G_F}(V, ℂ_p)` and `Hom_{G_F}(V, ℂ_p(1))`
is `G_F`-equivariant (the last step of derham-scholze's `deRhamHodgeTate01_of_fontaineT`, for given bases). -/
theorem hom_decomp_of_basis {a b : ℕ} (bx : Basis (Fin a) (fieldF p F) (htF ρ 0))
    (by' : Basis (Fin b) (fieldF p F) (htF ρ 1))
    (hz : LinearIndependent ℂ_[p] (Sum.elim (fun i => ((bx i : htF ρ 0) : V →ₗ[ℚ_[p]] ℂ_[p]))
      (fun i => ((by' i : htF ρ 1) : V →ₗ[ℚ_[p]] ℂ_[p]))))
    (hcard : Fintype.card (Fin a ⊕ Fin b) = finrank ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p])) :
    ∃ (e : (V →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (f : V →ₗ[ℚ_[p]] ℂ_[p]),
        e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ ρ σ⁻¹) =
          ((fun k => cpAct p (gfToGqp p F σ) ((e f).1 k)),
            (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e f).2 k))) := by
  haveI := fd_hom (p := p) (V := V)
  let B := basisOfLinearIndependentOfCardEqFinrank' _ hz hcard
  refine ⟨B.equivFun.trans (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℂ_[p] ℂ_[p]), ?_⟩
  intro σ f
  have hB : ∀ k, (B k) ∈ htSpaceOver p ρ (wt k) := by
    rintro (i | i)
    · simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inl]; exact (bx i).2
    · simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank', Sum.elim_inr]; exact (by' i).2
  have hexp : tAct ρ σ f = ∑ k, (cpAct p (gfToGqp p F σ) (B.repr f k) *
      algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-wt k))) • B k := by
    conv_lhs => rw [← B.sum_repr f]
    rw [tAct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tAct_of_mem ρ (hB k), smul_smul, mul_comm]
  have hrep : B.repr (tAct ρ σ f) = fun k => cpAct p (gfToGqp p F σ) (B.repr f k) *
      algebraMap ℚ_[p] ℂ_[p] (cycPow p (gfToGqp p F σ) (-wt k)) := by
    rw [hexp]
    ext k
    rw [B.repr_sum_self]
  change (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℂ_[p] ℂ_[p]) (B.equivFun (tAct ρ σ f)) = _
  rw [Basis.equivFun_apply, hrep]
  ext k
  · simp only [LinearEquiv.sumArrowLequivProdArrow_apply_fst, Function.comp_apply, wt, Sum.elim_inl, neg_zero,
      cycPow_zero, map_one, mul_one, LinearEquiv.trans_apply, Basis.equivFun_apply]
  · simp only [LinearEquiv.sumArrowLequivProdArrow_apply_snd, Function.comp_apply, wt, Sum.elim_inr,
      LinearEquiv.trans_apply, Basis.equivFun_apply, Algebra.smul_def]
    ring


/-- **De Rham with Hodge jumps in `[0, 1]` and `dim Fil¹ D_dR = [F:ℚ_p] h` gives the Hom-form Hodge–Tate
decomposition with multiplicities `(dim V − h, h)`.** derham-scholze's `deRhamHodgeTate01_of_fontaineT` with the
dimension count: `Fil¹ D_dR(V^∨) ↪ Hom_{G_F}(V, ℂ_p(1))` by `gr¹` (`Fil² = 0`), so `h ≤ b`; `gr⁰` has kernel in
`Fil¹`, so `dim V ≤ a + h`; Tate–Sen gives `a + b ≤ dim V`. -/
theorem hodgeTate01_dims (hF : FontaineTwistT) (h1 : IsDeRhamFam p (fun σ => ρ.dual σ))
    (h2 : HodgeRange p (fun σ => ρ.dual σ) 1) (h : ℕ)
    (hfil1 : finrank ℚ_[p] (filD p (fun σ => ρ.dual σ) 1) = finrank ℚ_[p] F * h) :
    ∃ (a b : ℕ) (e : (V →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      (∀ (σ : Field.absoluteGaloisGroup F) (f : V →ₗ[ℚ_[p]] ℂ_[p]),
        e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ ρ σ⁻¹) =
          ((fun k => cpAct p (gfToGqp p F σ) ((e f).1 k)),
            (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e f).2 k)))) ∧
      a + h = finrank ℚ_[p] V ∧ b = h := by
  obtain ⟨t, ht, hσ⟩ := hF p
  obtain ⟨-, hrank⟩ := h1
  have hT := ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
  have hA := ZInQ.Contrib.CloudB3W11.axSenTate_proof
  have hD : finrank ℚ_[p] (ddrSpaceOver p ρ) = finrank ℚ_[p] F * finrank ℚ_[p] V := by
    rw [← map_ddrFam_dual ρ, LinearEquiv.finrank_map_eq, hrank, Subspace.dual_finrank_eq]
  have hfil : ∀ j, Submodule.map (tensorDualEquiv p).toLinearMap (filD p (fun σ => ρ.dual σ) j) =
      ddrSpaceOver p ρ ⊓ filH p j := by
    intro j
    rw [filD, Submodule.map_inf _ (tensorDualEquiv p).injective, map_ddrFam_dual, map_filRange_dual]
  obtain ⟨hf0, hf2⟩ := h2
  have h0 : ddrSpaceOver p ρ ≤ filH p 0 := by
    have := hfil 0
    rw [hf0, map_ddrFam_dual] at this
    exact inf_eq_left.mp this.symm
  have h2' : ddrSpaceOver p ρ ⊓ filH p 2 = ⊥ := by
    rw [← hfil 2]
    exact (congrArg _ hf2).trans (Submodule.map_bot _)
  have hF1 : finrank ℚ_[p] (ddrSpaceOver p ρ ⊓ filH p 1 : Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p)) =
      finrank ℚ_[p] F * h := by
    rw [← hfil 1, LinearEquiv.finrank_map_eq, hfil1]
  -- the `F'`-dimensions `a`, `b`
  obtain ⟨hfa, -⟩ := fd_htF0 ρ hT hA
  obtain ⟨hfb, -⟩ := fd_htF1 ρ hT hA
  have := hfa
  have := hfb
  haveI := fd_htSpaceOver ρ (0 : ℤ)
  haveI := fd_htSpaceOver ρ (1 : ℤ)
  haveI := fd_hom (p := p) (V := V)
  set a := finrank (fieldF p F) (htF ρ 0)
  set b := finrank (fieldF p F) (htF ρ 1)
  let bx := Module.finBasis (fieldF p F) (htF ρ 0)
  let by' := Module.finBasis (fieldF p F) (htF ρ 1)
  have hz := linIndep_two ρ hT hA (fun i => bx i) (fun i => by' i) bx.linearIndependent by'.linearIndependent
  -- Tate–Sen: `a + b ≤ dim V`
  have hab : a + b ≤ finrank ℚ_[p] V := by
    have := hz.fintype_card_le_finrank
    rwa [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_hom] at this
  obtain ⟨hl1, hl2⟩ := finrank_fil1_bounds ρ ht hσ h0 h2'
  have hhb : h ≤ b := by
    rw [hF1, finrank_htSpaceOver_eq] at hl1
    exact Nat.le_of_mul_le_mul_left hl1 Module.finrank_pos
  have hle := hl2
  rw [hD, finrank_htSpaceOver_eq, hF1, ← mul_add] at hle
  have hna : finrank ℚ_[p] V ≤ a + h := Nat.le_of_mul_le_mul_left hle Module.finrank_pos
  have hbh : b = h := by omega
  -- the `ℂ_p`-basis (as in `deRhamHodgeTate01_of_fontaineT`)
  have hcard : Fintype.card (Fin a ⊕ Fin b) = finrank ℂ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_hom]
    omega
  obtain ⟨e, he⟩ := hom_decomp_of_basis ρ bx by' hz hcard
  exact ⟨a, b, e, he, by omega, hbh⟩

end Dims

end

end DeRhamScholze.HTAbVar
