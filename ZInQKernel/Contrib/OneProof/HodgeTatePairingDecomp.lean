import ZInQKernel.OneProof.H.TailS
import ZInQKernel.Contrib.AbVarBC.G9Instance

/-!
# The Hodge–Tate decomposition of `V_p(A)`, part 1: linear algebra and the printed leaf

Task hodgetate-from-dr (2026-11-16; report `docs/research/hodgetate-from-dr.md`).

* §0 `HodgeTateDecompExists`: the new published-form leaf, Fontaine's Hodge–Tate decomposition
  `ℂ_p ⊗ V_p(A) ≅ (ℂ_p(1) ⊗_F t_A) ⊕ (ℂ_p ⊗_F t_{A'}^*)` with bases of the two finite-dimensional
  `F`-spaces chosen and their dimensions `a`, `b` left unspecified.
* §1 hodge-split's count (`ZInQKernel/OneProof/H/TailS.lean` §6) for a decomposition `ℂ_p(1)^a ⊕ ℂ_p^b`.
* §2 `eq_of_pairing`: a `G_F`-equivariant nondegenerate pairing on `V` with multiplier the cyclotomic
  character forces `a = b` (with Tate's two theorems); `add_eq_finrank`: `a + b = dim V`.

This module imports only `TailS` (in a later environment the same proofs time out in typeclass search).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option synthInstance.maxHeartbeats 400000

namespace ZInQ.Contrib.HodgeTateFromPairing

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

noncomputable section

/-! ## §0. The leaf -/

/-- **LEAF (Hodge–Tate decomposition of the Tate module of an abelian variety, bases chosen,
dimensions not specified).** Fontaine, *Formes différentielles et modules de Tate des variétés
abéliennes sur les corps locaux*, Invent. Math. 65 (1982), 379-409, Théorème principal (Tate 1967
§4, Cor. 2 of Thm 3 for good reduction; Faltings, JAMS 1 (1988) for `H¹_ét`; all locators
UNVERIFIED): for an abelian variety `A` over a finite extension `F` of `ℚ_p` there is a
`G_F`-equivariant `ℂ_p`-linear isomorphism `ℂ_p ⊗_{ℚ_p} V_p(A) ≅ (ℂ_p(1) ⊗_F t_A) ⊕
(ℂ_p ⊗_F t_{A'}^*)` (`t` = tangent space at the origin, `A'` the dual abelian variety). Lean form: after
choosing `F`-bases of the two finite-dimensional `F`-spaces (of dimensions `a`, `b`), `ℂ_p(1)^a ⊕ ℂ_p^b`;
`G_F` acts on `ℂ_p ⊗ V` by `σ ⊗ ρ(σ)` and on `ℂ_p(1)` by `c ↦ χ(σ) σ(c)`, through pkg-I4's `gfToGqp`.
This is `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` without the dimensions: nothing about
`dim t_A` or `dim t_{A'}^*` is used, so it is a specialization of the printed statement with no
further input. -/
def HodgeTateDecompExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (a b : ℕ) (e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))

/-- The field implies the leaf (so the leaf is not stronger than the field it replaces). -/
theorem hodgeTateDecompExists_of_field (h : HodgeTateDecompAbVar) : HodgeTateDecompExists := by
  intro p _ F _ _ _ A
  obtain ⟨g, hg⟩ := dim_finite_I4 A
  obtain ⟨e, he⟩ := h p F A g hg
  exact ⟨g, g, e, he⟩

variable (p : ℕ) [Fact p.Prime]
variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-! ## §1. The Hodge–Tate spaces from a decomposition `ℂ_p(1)^a ⊕ ℂ_p^b` (TailS §6 with `(g, g)` replaced by `(a, b)`) -/

section Decomp

variable {a b : ℕ}

/-- `w ↦ Σ w₁ₖ c₁ₖ + Σ w₂ₖ c₂ₖ`. -/
def psiC2 (c : (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) :
    ((Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) →ₗ[ℂ_[p]] ℂ_[p] where
  toFun w := ∑ k, w.1 k * c.1 k + ∑ k, w.2 k * c.2 k
  map_add' w w' := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r w := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_add, mul_assoc]

theorem psiC_apply2 (c w : (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) :
    psiC2 p c w = ∑ k, w.1 k * c.1 k + ∑ k, w.2 k * c.2 k := rfl

/-- The coordinates of a linear form on `W`. -/
def coordsW2 (ℓ : ((Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) →ₗ[ℂ_[p]] ℂ_[p]) :
    (Fin a → ℂ_[p]) × (Fin b → ℂ_[p]) :=
  (fun k => ℓ (Pi.single k 1, 0), fun k => ℓ (0, Pi.single k 1))

theorem psiC_single_fst2 (c : (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) (k : Fin a) :
    psiC2 p c (Pi.single k 1, 0) = c.1 k := by
  simp [psiC_apply2, Pi.single_apply]

theorem psiC_single_snd2 (c : (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) (k : Fin b) :
    psiC2 p c (0, Pi.single k 1) = c.2 k := by
  simp [psiC_apply2, Pi.single_apply]

theorem psiC_coordsW2 (ℓ : ((Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) →ₗ[ℂ_[p]] ℂ_[p]) :
    psiC2 p (coordsW2 p ℓ) = ℓ := by
  apply LinearMap.prod_ext
  · apply LinearMap.pi_ext'
    intro k
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.coe_single]
    rw [psiC_single_fst2]
    rfl
  · apply LinearMap.pi_ext'
    intro k
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.coe_single]
    rw [psiC_single_snd2]
    rfl

theorem psiC_add2 (c c' : (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) :
    psiC2 p (c + c') = psiC2 p c + psiC2 p c' := by
  refine LinearMap.ext fun w => ?_
  simp only [psiC_apply2, LinearMap.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  ring

theorem psiC_smul2 (r : ℚ_[p]) (c : (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) :
    psiC2 p (r • c) = r • psiC2 p c := by
  refine LinearMap.ext fun w => ?_
  simp only [psiC_apply2, LinearMap.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
    Finset.smul_sum, mul_smul_comm, smul_add]

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
  (e : ℂ_[p] ⊗[ℚ_[p]] V ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p]))

/-- `c ↦ (v ↦ ψ_c(e(1 ⊗ v)))`. -/
def PsiE2 : ((Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) →ₗ[ℚ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun c := (psiC2 p c).restrictScalars ℚ_[p] ∘ₗ (e.toLinearMap.restrictScalars ℚ_[p]) ∘ₗ
    TensorProduct.mk ℚ_[p] ℂ_[p] V 1
  map_add' c c' := by ext v; simp [psiC_add2]
  map_smul' r c := by ext v; simp [psiC_smul2]

theorem PsiE_apply2 (c : (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) (v : V) :
    PsiE2 p e c v = psiC2 p c (e (1 ⊗ₜ v)) := rfl

theorem tmul_eq_smul_one_tmul2 (c : ℂ_[p]) (v : V) :
    (c ⊗ₜ[ℚ_[p]] v : ℂ_[p] ⊗[ℚ_[p]] V) = c • ((1 : ℂ_[p]) ⊗ₜ v) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- A `ℂ_p`-linear form on `ℂ_p ⊗ V` vanishing on `1 ⊗ V` vanishes. -/
theorem ext_one_tmul2 {ℓ ℓ' : ℂ_[p] ⊗[ℚ_[p]] V →ₗ[ℂ_[p]] ℂ_[p]}
    (h : ∀ v, ℓ (1 ⊗ₜ v) = ℓ' (1 ⊗ₜ v)) : ℓ = ℓ' := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rw [tmul_eq_smul_one_tmul2, map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem PsiE_injective2 : Function.Injective (PsiE2 p e) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro c hc
  rw [LinearMap.mem_ker] at hc
  rw [Submodule.mem_bot]
  have h1 : (psiC2 p c) ∘ₗ e.toLinearMap = 0 := by
    apply ext_one_tmul2 p
    intro v
    have := LinearMap.congr_fun hc v
    rw [PsiE_apply2] at this
    simpa using this
  have h2 : psiC2 p c = 0 := by
    refine LinearMap.ext fun w => ?_
    have := LinearMap.congr_fun h1 (e.symm w)
    simpa using this
  ext k
  · rw [← psiC_single_fst2 p c k, h2]; rfl
  · rw [← psiC_single_snd2 p c k, h2]; rfl

theorem PsiE_surjective2 : Function.Surjective (PsiE2 p e) := by
  intro φ
  let ℓ := (LinearMap.liftBaseChange ℂ_[p] φ) ∘ₗ e.symm.toLinearMap
  refine ⟨coordsW2 p ℓ, ?_⟩
  ext v
  rw [PsiE_apply2, psiC_coordsW2]
  simp [ℓ]

/-! ### The Hodge–Tate spaces of `V` from the decomposition -/

variable (S : Set (GQp p))

/-- `{c ∈ W | c₁ₖ ∈ ℂ_p(i₁)^S, c₂ₖ ∈ ℂ_p(i₂)^S}`. -/
def PSub2 (i₁ i₂ : ℤ) : Submodule ℚ_[p] ((Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) where
  carrier := {c | (∀ k, c.1 k ∈ fixSp p i₁ S) ∧ ∀ k, c.2 k ∈ fixSp p i₂ S}
  zero_mem' := ⟨fun _ => (fixSp p i₁ S).zero_mem, fun _ => (fixSp p i₂ S).zero_mem⟩
  add_mem' ha hb := ⟨fun k => (fixSp p i₁ S).add_mem (ha.1 k) (hb.1 k),
    fun k => (fixSp p i₂ S).add_mem (ha.2 k) (hb.2 k)⟩
  smul_mem' r c hc := ⟨fun k => (fixSp p i₁ S).smul_mem r (hc.1 k),
    fun k => (fixSp p i₂ S).smul_mem r (hc.2 k)⟩

theorem finrank_PSub2 (i₁ i₂ : ℤ) [FiniteDimensional ℚ_[p] (fixSp p i₁ S)]
    [FiniteDimensional ℚ_[p] (fixSp p i₂ S)] :
    finrank ℚ_[p] (PSub2 p S (a := a) (b := b) i₁ i₂) =
      a * finrank ℚ_[p] (fixSp p i₁ S) + b * finrank ℚ_[p] (fixSp p i₂ S) := by
  let ι : ((Fin a → fixSp p i₁ S) × (Fin b → fixSp p i₂ S)) →ₗ[ℚ_[p]]
      ((Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) :=
    ((fixSp p i₁ S).subtype.compLeft (Fin a)).prodMap ((fixSp p i₂ S).subtype.compLeft (Fin b))
  have hinj : Function.Injective ι := by
    intro u u' h
    simp only [ι, LinearMap.prodMap_apply, Prod.mk.injEq] at h
    ext k
    · exact congrFun h.1 k
    · exact congrFun h.2 k
  have hrange : LinearMap.range ι = PSub2 p S i₁ i₂ := by
    ext c
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨fun k => (u.1 k).2, fun k => (u.2 k).2⟩
    · intro hc
      exact ⟨(fun k => ⟨c.1 k, hc.1 k⟩, fun k => ⟨c.2 k, hc.2 k⟩), rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_prod,
    Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp

variable (he : ∀ σ x, e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) x) =
  ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
    (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k))))

include he in
theorem PsiE_mem_fwd2 (j : ℤ) (c : (Fin a → ℂ_[p]) × (Fin b → ℂ_[p]))
    (hc : PsiE2 p e c ∈ htSpaceOver p ρ j) :
    c ∈ PSub2 p (Set.range (gfToGqp p F)) (j - 1) j := by
  -- extend the equivariance to `ℂ_p ⊗ V`
  have hx : ∀ σ x, psiC2 p c (e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) x)) =
      cycPow p (gfToGqp p F σ) j • cpAct p (gfToGqp p F σ) (psiC2 p c (e x)) := by
    intro σ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      rw [TensorProduct.map_tmul, cpLin_apply, tmul_eq_smul_one_tmul2 p (cpAct p _ a),
        tmul_eq_smul_one_tmul2 p a, map_smul, map_smul, map_smul, map_smul, smul_eq_mul,
        smul_eq_mul, map_mul]
      have := hc σ v
      rw [PsiE_apply2, PsiE_apply2] at this
      rw [this, mul_smul_comm]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rintro _ ⟨σ, rfl⟩
    have h1 := hx σ (e.symm (Pi.single k 1, 0))
    rw [he, LinearEquiv.apply_symm_apply, psiC_single_fst2] at h1
    have h2 : ((fun m => cycPow p (gfToGqp p F σ) 1 •
        cpAct p (gfToGqp p F σ) (((Pi.single k 1 : Fin a → ℂ_[p]), (0 : Fin b → ℂ_[p])).1 m)),
        (fun m => cpAct p (gfToGqp p F σ) (((Pi.single k 1 : Fin a → ℂ_[p]), (0 : Fin b → ℂ_[p])).2 m))) =
        cycPow p (gfToGqp p F σ) 1 • (((Pi.single k 1 : Fin a → ℂ_[p]), (0 : Fin b → ℂ_[p])) :
          (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) := by
      ext m
      · by_cases hm : m = k
        · subst hm; simp
        · simp [Pi.single_apply, hm]
      · simp
    rw [h2, LinearMap.map_smul_of_tower, psiC_single_fst2] at h1
    rw [htAct_apply]
    have hj : j = (j - 1) + 1 := by ring
    rw [hj, cycPow_add_one, mul_smul] at h1
    exact (smul_right_injective _ (cycPow_one_ne_zero p _) h1).symm
  · rintro _ ⟨σ, rfl⟩
    have h1 := hx σ (e.symm (0, Pi.single k 1))
    rw [he, LinearEquiv.apply_symm_apply, psiC_single_snd2] at h1
    have h2 : ((fun m => cycPow p (gfToGqp p F σ) 1 •
        cpAct p (gfToGqp p F σ) (((0 : Fin a → ℂ_[p]), (Pi.single k 1 : Fin b → ℂ_[p])).1 m)),
        (fun m => cpAct p (gfToGqp p F σ) (((0 : Fin a → ℂ_[p]), (Pi.single k 1 : Fin b → ℂ_[p])).2 m))) =
        (((0 : Fin a → ℂ_[p]), (Pi.single k 1 : Fin b → ℂ_[p])) :
          (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])) := by
      ext m
      · simp
      · by_cases hm : m = k
        · subst hm; simp
        · simp [Pi.single_apply, hm]
    rw [h2, psiC_single_snd2] at h1
    rw [htAct_apply]
    exact h1.symm

include he in
theorem PsiE_mem_bwd2 (j : ℤ) (c : (Fin a → ℂ_[p]) × (Fin b → ℂ_[p]))
    (hc : c ∈ PSub2 p (Set.range (gfToGqp p F)) (j - 1) j) :
    PsiE2 p e c ∈ htSpaceOver p ρ j := by
  intro σ v
  have h1 : ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ρ σ v) =
      TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) (1 ⊗ₜ v) := by
    rw [TensorProduct.map_tmul, cpLin_apply, map_one]
  rw [PsiE_apply2, PsiE_apply2, h1, he]
  obtain ⟨τ, hτ⟩ : ∃ τ, gfToGqp p F σ = τ := ⟨_, rfl⟩
  rw [hτ]
  obtain ⟨w, hw⟩ : ∃ w, e (1 ⊗ₜ v) = w := ⟨_, rfl⟩
  rw [hw]
  have hcj : algebraMap ℚ_[p] ℂ_[p] (cycPow p τ j) =
      algebraMap ℚ_[p] ℂ_[p] (cycPow p τ 1) * algebraMap ℚ_[p] ℂ_[p] (cycPow p τ (j - 1)) := by
    rw [← map_mul, ← cycPow_add_one]
    congr 2
    ring
  have t1 : ∀ m, (cycPow p τ 1 • cpAct p τ (w.1 m)) * c.1 m =
      cycPow p τ j • cpAct p τ (w.1 m * c.1 m) := by
    intro m
    have h := hc.1 m τ ⟨σ, hτ⟩
    rw [htAct_apply] at h
    conv_lhs => rw [← h]
    rw [map_mul, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, hcj]
    ring
  have t2 : ∀ m, cpAct p τ (w.2 m) * c.2 m = cycPow p τ j • cpAct p τ (w.2 m * c.2 m) := by
    intro m
    have h := hc.2 m τ ⟨σ, hτ⟩
    rw [htAct_apply] at h
    conv_lhs => rw [← h]
    rw [map_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  rw [psiC_apply2, psiC_apply2]
  rw [Finset.sum_congr rfl (fun m _ => t1 m), Finset.sum_congr rfl (fun m _ => t2 m)]
  rw [← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, map_add, map_sum, map_sum]

include he in
/-- **The count.** `htSpaceOver j ≅ (ℂ_p(j−1)^{G_F})ᵍ × (ℂ_p(j)^{G_F})ᵍ`. -/
theorem htSpaceOver_eq_map2 (j : ℤ) :
    htSpaceOver p ρ j = Submodule.map (PsiE2 p e) (PSub2 p (Set.range (gfToGqp p F)) (j - 1) j) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨c, rfl⟩ := PsiE_surjective2 p e φ
    exact ⟨c, PsiE_mem_fwd2 p ρ e he j c hφ, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact PsiE_mem_bwd2 p ρ e he j c hc

include he in
theorem finrank_htSpaceOver_of_decomp2 (j : ℤ) :
    finrank ℚ_[p] (htSpaceOver p ρ j) =
      finrank ℚ_[p] (PSub2 p (Set.range (gfToGqp p F)) (a := a) (b := b) (j - 1) j) := by
  rw [htSpaceOver_eq_map2 p ρ e he j]
  exact (Submodule.equivMapOfInjective _ (PsiE_injective2 p e) _).finrank_eq.symm


end Decomp

/-! ## §2. A Galois-equivariant nondegenerate pairing with multiplier `χ` forces `a = b` -/

section Pairing

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
  (B : LinearMap.BilinForm ℚ_[p] V) (hB : B.Nondegenerate)

/-- `Ψ_B : ℂ_p ⊗ V ≅ Hom_{ℚ_p}(V, ℂ_p)`, `c ⊗ x ↦ (v ↦ B(x, v) c)`. -/
def PsiB : (ℂ_[p] ⊗[ℚ_[p]] V) ≃ₗ[ℚ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) :=
  ((TensorProduct.congr (LinearEquiv.refl ℚ_[p] ℂ_[p]) (B.toDual hB)).trans
    (TensorProduct.comm ℚ_[p] ℂ_[p] (Module.Dual ℚ_[p] V))).trans
    (dualTensorHomEquiv ℚ_[p] V ℂ_[p])

theorem PsiB_tmul (c : ℂ_[p]) (x v : V) : PsiB p B hB (c ⊗ₜ x) v = B x v • c := by
  simp [PsiB, LinearMap.BilinForm.toDual_def]

/-- `(ℂ_p ⊗ V)^{G_F}`, for `G_F` acting by `σ ⊗ ρ(σ)`. -/
def WG : Submodule ℚ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) where
  carrier := {w | ∀ σ, TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) w = w}
  zero_mem' σ := map_zero _
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  smul_mem' c w hw σ := by rw [map_smul, hw σ]

variable (hmult : ∀ σ x y, B (ρ σ x) (ρ σ y) = cycPow p (gfToGqp p F σ) 1 * B x y)

include hmult in
theorem PsiB_map (σ : Field.absoluteGaloisGroup F) (w : ℂ_[p] ⊗[ℚ_[p]] V) (v : V) :
    PsiB p B hB (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) w) (ρ σ v) =
      cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) (PsiB p B hB w v) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    rw [TensorProduct.map_tmul, PsiB_tmul, PsiB_tmul, cpLin_apply, hmult, cpAct_smul, smul_smul]
  | add w w' hw hw' =>
    simp only [map_add, LinearMap.add_apply, hw, hw', smul_add]

include hmult in
/-- `Hom_{G_F}(V, ℂ_p(1)) = Ψ_B((ℂ_p ⊗ V)^{G_F})`. -/
theorem htSpaceOver_one_eq :
    htSpaceOver p ρ 1 = (WG p ρ).map (PsiB p B hB).toLinearMap := by
  ext φ
  obtain ⟨w, rfl⟩ := (PsiB p B hB).surjective φ
  constructor
  · intro hφ
    refine ⟨w, fun σ => ?_, rfl⟩
    apply (PsiB p B hB).injective
    refine LinearMap.ext fun u => ?_
    have hu : ρ σ (ρ σ⁻¹ u) = u := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← hu, PsiB_map p ρ B hB hmult]
    exact (hφ σ (ρ σ⁻¹ u)).symm
  · rintro ⟨w', hw', hww'⟩ σ v
    have hw : w ∈ WG p ρ := by
      have : w' = w := (PsiB p B hB).injective hww'
      exact this ▸ hw'
    calc PsiB p B hB w (ρ σ v)
        = PsiB p B hB (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) w) (ρ σ v) := by
          rw [hw σ]
      _ = _ := PsiB_map p ρ B hB hmult σ w v

include hB hmult in
theorem finrank_htSpaceOver_one_eq_WG :
    finrank ℚ_[p] (htSpaceOver p ρ 1) = finrank ℚ_[p] (WG p ρ) := by
  rw [htSpaceOver_one_eq p ρ B hB hmult]
  exact LinearEquiv.finrank_map_eq _ _

variable {a b : ℕ} (e : ℂ_[p] ⊗[ℚ_[p]] V ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p]))
  (he : ∀ σ x, e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) x) =
    ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
      (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k))))

include he in
/-- `e((ℂ_p ⊗ V)^{G_F}) = (ℂ_p(1)^{G_F})^a × (ℂ_p^{G_F})^b`. -/
theorem WG_map_eq :
    (WG p ρ).map ((e.restrictScalars ℚ_[p] : _ ≃ₗ[ℚ_[p]] _) : _ →ₗ[ℚ_[p]] _) =
      PSub2 p (Set.range (gfToGqp p F)) (a := a) (b := b) 1 0 := by
  ext u
  obtain ⟨w, rfl⟩ := e.surjective u
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w', hw', h⟩
    have h' : w' = w := e.injective h
    subst h'
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rintro _ ⟨σ, rfl⟩
      have h1 := congrArg (fun z => z.1 k) (he σ w')
      simp only at h1
      rw [hw' σ] at h1
      rw [htAct_apply]
      exact h1.symm
    · rintro _ ⟨σ, rfl⟩
      have h1 := congrArg (fun z => z.2 k) (he σ w')
      simp only at h1
      rw [hw' σ] at h1
      rw [htAct_apply, cycPow_zero, one_smul]
      exact h1.symm
  · intro hu
    refine ⟨w, fun σ => ?_, rfl⟩
    apply e.injective
    rw [he σ w]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · have := hu.1 k _ ⟨σ, rfl⟩
      rw [htAct_apply] at this
      exact this
    · have := hu.2 k _ ⟨σ, rfl⟩
      rw [htAct_apply, cycPow_zero, one_smul] at this
      exact this

include e in
/-- `a + b = dim V`. -/
theorem add_eq_finrank : a + b = finrank ℚ_[p] V := by
  have := e.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at this
  exact this.symm

include he hB hmult in
/-- **The two Hodge–Tate pieces have the same dimension.** -/
theorem eq_of_pairing (hT : TateTwistInvariants) (hA : AxSenTate) : a = b := by
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have := fd_fixSp_range p (F := F) hT hA 0
  have := fd_fixSp_range p (F := F) hT hA 1
  have h1 : finrank ℚ_[p] (htSpaceOver p ρ 1) = a * finrank ℚ_[p] F := by
    rw [finrank_htSpaceOver_of_decomp2 p ρ e he 1, show (1 : ℤ) - 1 = 0 by norm_num, finrank_PSub2,
      finrank_fixSp_range p hT hA, finrank_fixSp_range p hT hA]
    simp
  have h2 : finrank ℚ_[p] (WG p ρ) = b * finrank ℚ_[p] F := by
    rw [← LinearEquiv.finrank_map_eq (e.restrictScalars ℚ_[p]) (WG p ρ), WG_map_eq p ρ e he,
      finrank_PSub2, finrank_fixSp_range p hT hA, finrank_fixSp_range p hT hA]
    simp
  have h3 := finrank_htSpaceOver_one_eq_WG p ρ B hB hmult
  rw [h1, h2] at h3
  exact Nat.eq_of_mul_eq_mul_right hF h3

end Pairing

/-! ## §3. The cyclotomic character is natural -/

/-- **Naturality of Mathlib's cyclotomic character.** If `ι : L → M` is a ring map of fields with
all `p`-power roots of unity, and `ι ∘ g = h ∘ ι`, then `χ_L(g) = χ_M(h)`. -/
theorem cyclotomicCharacter_eq_of_comm (p : ℕ) [Fact p.Prime] {L M : Type*} [Field L] [Field M]
    [∀ i, HasEnoughRootsOfUnity L (p ^ i)] [∀ i, HasEnoughRootsOfUnity M (p ^ i)]
    (ι : L →+* M) (g : L ≃+* L) (h : M ≃+* M) (hι : ∀ x, ι (g x) = h (ι x)) :
    cyclotomicCharacter L p g = cyclotomicCharacter M p h := by
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L (p ^ n)
  have hζ' : IsPrimitiveRoot (ι ζ) (p ^ n) := hζ.map_of_injective ι.injective
  have h1 := cyclotomicCharacter.spec p (n := n) g ζ hζ.pow_eq_one
  have h2 := cyclotomicCharacter.spec p (n := n) h (ι ζ) hζ'.pow_eq_one
  have h3 : ι ζ ^ ((cyclotomicCharacter L p g).val.toZModPow n).val =
      ι ζ ^ ((cyclotomicCharacter M p h).val.toZModPow n).val := by
    rw [← map_pow, ← h1, hι, h2]
  exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

/-- pkg-I4's `χ(σ)` for `σ ∈ G_F` (through `gfToGqp`) is Mathlib's cyclotomic character of `F̄`. -/
theorem cyc_gfToGqp (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (σ : Field.absoluteGaloisGroup F) :
    cyc p (gfToGqp p F σ) = cyclotomicCharacter (AlgebraicClosure F) p σ.toRingEquiv := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  have : NeZero (p : F) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  have hc := ZInQ.Contrib.AbVarBC.map_comm (algebraMap ℚ_[p] F) σ
  letI : Algebra ℚ_[p] F := (algebraMap ℚ_[p] F).toAlgebra
  exact cyclotomicCharacter_eq_of_comm p
    ((IsAlgClosed.lift : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure F) : _ →+* _)
    (gfToGqp p F σ).toRingEquiv σ.toRingEquiv (fun x => hc x)

theorem cycPow_gfToGqp_one (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (σ : Field.absoluteGaloisGroup F) :
    cycPow p (gfToGqp p F σ) 1 =
      (((cyclotomicCharacter (AlgebraicClosure F) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := by
  rw [cycPow, zpow_one, cyc_gfToGqp]

end

end ZInQ.Contrib.HodgeTateFromPairing
