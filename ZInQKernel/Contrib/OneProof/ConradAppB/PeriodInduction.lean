import ZInQKernel.Contrib.OneProof.ConradAppB.Defs

/-!
# Inducing a one-dimensional period from `G_L` to `G_{ℚ_p}`

Let `L/ℚ_p` be finite Galois inside `ℚ_p^alg`, `η : G_{ℚ_p} → Lˣ` a homomorphism and
`c ∈ ℂ_p` nonzero with `σ c = η(σ) c` for `σ ∈ G_L`. Then `ℂ_p ⊗_{ℚ_p} L` contains a
nonzero `x` with `(σ ⊗ 1) x = (1 ⊗ η(σ)) x` for all `σ ∈ G_{ℚ_p}`.

Proof. Let `b` be a basis of `L` and `b*` its trace-dual basis; `e = ∑ᵢ bᵢ* ⊗ bᵢ`
satisfies `(1 ⊗ l) e = (l ⊗ 1) e`, and `∑ᵢ bᵢ* bᵢ` has trace `[L : ℚ_p] ≠ 0`. Put
`F(g) = (g ⊗ 1)((η(g)⁻¹ c ⊗ 1) e)`. Then `F(g h) = F(g)` for `h ∈ G_L` and
`(σ ⊗ 1) F(g) = (1 ⊗ η(σ)) F(σ g)`. Let `x = ∑_τ F(g_τ)` over lifts `g_τ` of
`τ ∈ Gal(L/ℚ_p)`. The multiplication map `a ⊗ l ↦ a l` sends `x` to `c ∑ᵢ bᵢ* bᵢ ≠ 0`,
since `∑ᵢ τ(bᵢ*) bᵢ = 0` for every embedding `τ ≠ id` of `L`.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ZInQ.Contrib.SenWeightZero

namespace PeriodInductionAux

section Casimir

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
  [Algebra.IsSeparable K E]

/-- `∑ᵢ bᵢ* ⊗ bᵢ` for a basis `b` and its trace-dual basis `b*`. -/
def casimir : E ⊗[K] E :=
  ∑ i, (Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) (Module.finBasis K E) i ⊗ₜ[K]
    Module.finBasis K E i

theorem one_tmul_mul_casimir (l : E) :
    ((1 : E) ⊗ₜ[K] l) * casimir K E = (l ⊗ₜ[K] (1 : E)) * casimir K E := by
  classical
  have hsymm : (Algebra.traceForm K E).IsSymm := Algebra.traceForm_isSymm K
  have hn := traceForm_nondegenerate K E
  let b := Module.finBasis K E
  let D := (Algebra.traceForm K E).dualBasis hn b
  have hbrepr : ∀ x j, b.repr x j = Algebra.trace K E (x * D j) := by
    intro x j
    have h := LinearMap.BilinForm.dualBasis_repr_apply hn D x j
    rw [show (Algebra.traceForm K E).dualBasis hn D = b from
      LinearMap.BilinForm.dualBasis_dualBasis hn hsymm b] at h
    rw [h, Algebra.traceForm_apply]
  have hDrepr : ∀ x j, D.repr x j = Algebra.trace K E (x * b j) := by
    intro x j
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  have hcas : casimir K E = ∑ i, D i ⊗ₜ[K] b i := rfl
  rw [hcas, Finset.mul_sum, Finset.mul_sum]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  calc ∑ i, D i ⊗ₜ[K] (l * b i)
      = ∑ i, D i ⊗ₜ[K] (∑ j, b.repr (l * b i) j • b j) := by
        simp only [b.sum_repr]
    _ = ∑ i, ∑ j, Algebra.trace K E (l * b i * D j) • (D i ⊗ₜ[K] b j) := by
        simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, hbrepr]
    _ = ∑ j, ∑ i, Algebra.trace K E (l * D j * b i) • (D i ⊗ₜ[K] b j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [mul_right_comm]
    _ = ∑ j, (∑ i, D.repr (l * D j) i • D i) ⊗ₜ[K] b j := by
        simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul', hDrepr]
    _ = ∑ j, (l * D j) ⊗ₜ[K] b j := by
        simp only [D.sum_repr]

theorem trace_lmul'_casimir :
    Algebra.trace K E (Algebra.TensorProduct.lmul' K (casimir K E)) = (Module.finrank K E : K) := by
  classical
  have h1 : ∀ i, Algebra.trace K E
      ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) (Module.finBasis K E) i *
        Module.finBasis K E i) = 1 := by
    intro i
    rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_dualBasis_left]
    simp
  simp only [casimir, map_sum, Algebra.TensorProduct.lmul'_apply_tmul, h1, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem lmul'_casimir_ne_zero [CharZero K] :
    Algebra.TensorProduct.lmul' K (casimir K E) ≠ 0 := by
  intro h
  have h2 := trace_lmul'_casimir K E
  rw [h, map_zero] at h2
  exact (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := K) (M := E)).ne') h2.symm

end Casimir

section Padic

variable (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The inclusion `L → ℂ_p`. -/
def incl : L →ₐ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp L.val

theorem incl_apply (y : L) : incl p L y = (((y : PadicAlgCl p)) : ℂ_[p]) := rfl

theorem cpVal_eq (z : Lˣ) : cpVal p z = incl p L (z : L) := rfl

theorem cpVal_mul (u v : Lˣ) : cpVal p (u * v) = cpVal p u * cpVal p v := by
  rw [cpVal_eq, cpVal_eq, cpVal_eq, Units.val_mul, map_mul]

theorem cpVal_one : cpVal p (1 : Lˣ) = 1 := by
  rw [cpVal_eq, Units.val_one, map_one]

theorem smul_incl_of_mem {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hh : h ∈ L.fixingSubgroup)
    (y : L) : h • incl p L y = incl p L y := by
  rw [incl_apply, PadicComplex.smul_coe,
    (IntermediateField.mem_fixingSubgroup_iff L h).mp hh _ y.2]

theorem smul_cpVal_of_mem {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hh : h ∈ L.fixingSubgroup)
    (z : Lˣ) : h • cpVal p z = cpVal p z :=
  smul_incl_of_mem p L hh (z : L)

/-- `σ ⊗ 1` on `ℂ_p ⊗_{ℚ_p} L`. -/
def galT (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    ℂ_[p] ⊗[ℚ_[p]] L →ₐ[ℚ_[p]] ℂ_[p] ⊗[ℚ_[p]] L :=
  Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ) (AlgHom.id ℚ_[p] L)

theorem galT_tmul (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (a : ℂ_[p]) (l : L) :
    galT p L σ (a ⊗ₜ[ℚ_[p]] l) = (σ • a) ⊗ₜ[ℚ_[p]] l := by
  rw [galT, Algebra.TensorProduct.map_tmul, PadicComplex.galAlgHom_apply, AlgHom.id_apply]

theorem galT_mul (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (z : ℂ_[p] ⊗[ℚ_[p]] L) :
    galT p L (σ * τ) z = galT p L σ (galT p L τ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a l => rw [galT_tmul, galT_tmul, galT_tmul, mul_smul]
  | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]

theorem galT_one_tmul (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (l : L) :
    galT p L σ ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] l) = (1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] l := by
  rw [galT, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem galT_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f : L →ₐ[ℚ_[p]] ℂ_[p])
    (z : L ⊗[ℚ_[p]] L) :
    galT p L σ (Algebra.TensorProduct.map f (AlgHom.id ℚ_[p] L) z) =
      Algebra.TensorProduct.map ((PadicComplex.galAlgHom p σ).comp f) (AlgHom.id ℚ_[p] L) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a l =>
    simp only [Algebra.TensorProduct.map_tmul, galT_tmul, AlgHom.comp_apply,
      PadicComplex.galAlgHom_apply]
  | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]

theorem galAlgHom_comp_incl_of_mem {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hh : h ∈ L.fixingSubgroup) : (PadicComplex.galAlgHom p h).comp (incl p L) = incl p L := by
  refine AlgHom.ext fun y => ?_
  rw [AlgHom.comp_apply, PadicComplex.galAlgHom_apply, smul_incl_of_mem p L hh]

theorem galAlgHom_comp_incl_ne {g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hg : g ∉ L.fixingSubgroup) : (PadicComplex.galAlgHom p g).comp (incl p L) ≠ incl p L := by
  intro h
  apply hg
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have h1 := congrArg (fun φ : L →ₐ[ℚ_[p]] ℂ_[p] => φ ⟨y, hy⟩) h
  simp only [AlgHom.comp_apply, PadicComplex.galAlgHom_apply, incl_apply,
    PadicComplex.smul_coe] at h1
  exact UniformSpace.Completion.coe_injective _ h1

/-- The multiplication map `ℂ_p ⊗_{ℚ_p} L → ℂ_p`. -/
def mulMap : ℂ_[p] ⊗[ℚ_[p]] L →ₐ[ℚ_[p]] ℂ_[p] :=
  Algebra.TensorProduct.productMap (AlgHom.id ℚ_[p] ℂ_[p]) (incl p L)

theorem mulMap_tmul (a : ℂ_[p]) (l : L) : mulMap p L (a ⊗ₜ[ℚ_[p]] l) = a * incl p L l := by
  rw [mulMap, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply]

theorem mulMap_map (f : L →ₐ[ℚ_[p]] ℂ_[p]) (z : L ⊗[ℚ_[p]] L) :
    mulMap p L (Algebra.TensorProduct.map f (AlgHom.id ℚ_[p] L) z) =
      Algebra.TensorProduct.productMap f (incl p L) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a l =>
    rw [Algebra.TensorProduct.map_tmul, mulMap_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.productMap_apply_tmul]
  | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]

variable [FiniteDimensional ℚ_[p] L]

theorem productMap_casimir_eq_zero (f : L →ₐ[ℚ_[p]] ℂ_[p]) (hf : f ≠ incl p L) :
    Algebra.TensorProduct.productMap f (incl p L) (casimir ℚ_[p] L) = 0 := by
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ incl p L l := by
    by_contra h
    push Not at h
    exact hf (AlgHom.ext h)
  have h := congrArg (Algebra.TensorProduct.productMap f (incl p L))
    (one_tmul_mul_casimir ℚ_[p] L l)
  simp only [map_mul, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul,
    mul_one] at h
  have h2 : (incl p L l - f l) *
      Algebra.TensorProduct.productMap f (incl p L) (casimir ℚ_[p] L) = 0 := by
    rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3).symm hl
  · exact h3

theorem productMap_incl_casimir_ne_zero :
    Algebra.TensorProduct.productMap (incl p L) (incl p L) (casimir ℚ_[p] L) ≠ 0 := by
  have h : Algebra.TensorProduct.productMap (incl p L) (incl p L) =
      (incl p L).comp (Algebra.TensorProduct.lmul' ℚ_[p]) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    rw [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
  rw [h, AlgHom.comp_apply]
  intro h0
  exact lmul'_casimir_ne_zero ℚ_[p] L ((map_eq_zero (incl p L)).mp h0)

/-- `e = ∑ᵢ bᵢ* ⊗ bᵢ` in `ℂ_p ⊗_{ℚ_p} L`. -/
def eC : ℂ_[p] ⊗[ℚ_[p]] L :=
  Algebra.TensorProduct.map (incl p L) (AlgHom.id ℚ_[p] L) (casimir ℚ_[p] L)

theorem one_tmul_mul_eC (l : L) :
    ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] l) * eC p L = (incl p L l ⊗ₜ[ℚ_[p]] (1 : L)) * eC p L := by
  have h := congrArg (Algebra.TensorProduct.map (incl p L) (AlgHom.id ℚ_[p] L))
    (one_tmul_mul_casimir ℚ_[p] L l)
  simp only [map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at h
  exact h

theorem galT_eC_of_mem {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hh : h ∈ L.fixingSubgroup) :
    galT p L h (eC p L) = eC p L := by
  rw [eC, galT_map, galAlgHom_comp_incl_of_mem p L hh]

theorem mulMap_galT_tmul_mul_eC (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (a : ℂ_[p]) :
    mulMap p L (galT p L g ((a ⊗ₜ[ℚ_[p]] (1 : L)) * eC p L)) =
      (g • a) * Algebra.TensorProduct.productMap ((PadicComplex.galAlgHom p g).comp (incl p L))
        (incl p L) (casimir ℚ_[p] L) := by
  rw [map_mul, map_mul, galT_tmul, mulMap_tmul, map_one, mul_one, eC, galT_map, mulMap_map]

variable (η : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ) (c : ℂ_[p])

/-- `F(g) = (g ⊗ 1)((η(g)⁻¹ c ⊗ 1) e)`. -/
def Fg (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : ℂ_[p] ⊗[ℚ_[p]] L :=
  galT p L g (((cpVal p (η g)⁻¹ * c) ⊗ₜ[ℚ_[p]] (1 : L)) * eC p L)

theorem Fg_mul_of_mem (hc : ∀ σ ∈ L.fixingSubgroup, σ • c = cpVal p (η σ) * c)
    (g h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hh : h ∈ L.fixingSubgroup) :
    Fg p L η c (g * h) = Fg p L η c g := by
  have key : h • (cpVal p (η (g * h))⁻¹ * c) = cpVal p (η g)⁻¹ * c := by
    have h1 : (η (g * h))⁻¹ * η h = (η g)⁻¹ := by
      rw [map_mul, mul_inv, inv_mul_cancel_right]
    rw [smul_mul', hc h hh, smul_cpVal_of_mem p L hh, ← mul_assoc, ← cpVal_mul, h1]
  unfold Fg
  rw [galT_mul, map_mul (galT p L h), galT_tmul, galT_eC_of_mem p L hh, key]

theorem galT_Fg (σ g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    galT p L σ (Fg p L η c g) =
      ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((η σ : Lˣ) : L)) * Fg p L η c (σ * g) := by
  have hs : cpVal p (η (σ * g))⁻¹ * c * incl p L ((η σ : Lˣ) : L) = cpVal p (η g)⁻¹ * c := by
    rw [mul_right_comm, ← cpVal_eq p L (η σ), ← cpVal_mul, map_mul, mul_inv_rev,
      inv_mul_cancel_right]
  unfold Fg
  rw [← galT_mul, ← galT_one_tmul p L (σ * g) ((η σ : Lˣ) : L), ← map_mul (galT p L (σ * g)),
    mul_left_comm ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((η σ : Lˣ) : L)), one_tmul_mul_eC,
    ← mul_assoc ((cpVal p (η (σ * g))⁻¹ * c) ⊗ₜ[ℚ_[p]] (1 : L)),
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, hs]

theorem mulMap_Fg_of_not_mem (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hg : g ∉ L.fixingSubgroup) : mulMap p L (Fg p L η c g) = 0 := by
  rw [Fg, mulMap_galT_tmul_mul_eC,
    productMap_casimir_eq_zero p L _ (galAlgHom_comp_incl_ne p L hg), mul_zero]

theorem mulMap_Fg_of_mem (hc : ∀ σ ∈ L.fixingSubgroup, σ • c = cpVal p (η σ) * c)
    (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hg : g ∈ L.fixingSubgroup) :
    mulMap p L (Fg p L η c g) =
      c * Algebra.TensorProduct.productMap (incl p L) (incl p L) (casimir ℚ_[p] L) := by
  rw [Fg, mulMap_galT_tmul_mul_eC, galAlgHom_comp_incl_of_mem p L hg, smul_mul', hc g hg,
    smul_cpVal_of_mem p L hg, ← mul_assoc, ← cpVal_mul, inv_mul_cancel, cpVal_one, one_mul]

end Padic

section Restriction

variable (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [IsGalois ℚ_[p] L]

/-- Restriction `G_{ℚ_p} → Gal(L/ℚ_p)`. -/
abbrev res : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* (L ≃ₐ[ℚ_[p]] L) :=
  AlgEquiv.restrictNormalHom L

theorem res_apply_coe (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : L) :
    ((res p L σ y : L) : PadicAlgCl p) = σ (y : PadicAlgCl p) :=
  AlgEquiv.restrictNormal_commutes σ L y

theorem mem_fixingSubgroup_iff_res (h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    h ∈ L.fixingSubgroup ↔ res p L h = 1 := by
  constructor
  · intro hh
    refine AlgEquiv.ext fun y => Subtype.ext ?_
    rw [res_apply_coe, AlgEquiv.one_apply]
    exact (IntermediateField.mem_fixingSubgroup_iff L h).mp hh _ y.2
  · intro hh
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have h1 := res_apply_coe p L h ⟨y, hy⟩
    rw [hh, AlgEquiv.one_apply] at h1
    exact h1.symm

theorem res_surjective : Function.Surjective (res p L) :=
  AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p)

/-- A lift of `τ ∈ Gal(L/ℚ_p)` to `G_{ℚ_p}`. -/
def lift (τ : L ≃ₐ[ℚ_[p]] L) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p :=
  Function.surjInv (res_surjective p L) τ

theorem res_lift (τ : L ≃ₐ[ℚ_[p]] L) : res p L (lift p L τ) = τ :=
  Function.surjInv_eq (res_surjective p L) τ

end Restriction

end PeriodInductionAux

open PeriodInductionAux in
theorem periodInduction_proof : PeriodInduction := by
  intro p _ L _ _ η c hc0 hc
  classical
  let x : ℂ_[p] ⊗[ℚ_[p]] L := ∑ τ : L ≃ₐ[ℚ_[p]] L, Fg p L η c (lift p L τ)
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hm : mulMap p L x =
        c * Algebra.TensorProduct.productMap (incl p L) (incl p L) (casimir ℚ_[p] L) := by
      simp only [x, map_sum]
      rw [Finset.sum_eq_single (1 : L ≃ₐ[ℚ_[p]] L)]
      · exact mulMap_Fg_of_mem p L η c hc _
          ((mem_fixingSubgroup_iff_res p L _).mpr (res_lift p L 1))
      · intro τ _ hτ
        apply mulMap_Fg_of_not_mem
        rw [mem_fixingSubgroup_iff_res, res_lift]
        exact hτ
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hx, map_zero] at hm
    exact mul_ne_zero hc0 (productMap_incl_casimir_ne_zero p L) hm.symm
  · intro σ
    change galT p L σ x = _
    have hstep : ∀ τ, Fg p L η c (σ * lift p L τ) = Fg p L η c (lift p L (res p L σ * τ)) := by
      intro τ
      have hmem : (lift p L (res p L σ * τ))⁻¹ * (σ * lift p L τ) ∈ L.fixingSubgroup := by
        rw [mem_fixingSubgroup_iff_res, map_mul, map_inv, res_lift, map_mul, res_lift,
          inv_mul_cancel]
      have h1 := Fg_mul_of_mem p L η c hc (lift p L (res p L σ * τ)) _ hmem
      rwa [mul_inv_cancel_left] at h1
    have hsum : ∀ (f : (L ≃ₐ[ℚ_[p]] L) → ℂ_[p] ⊗[ℚ_[p]] L) (a : ℂ_[p] ⊗[ℚ_[p]] L),
        ∑ τ, a * f τ = a * ∑ τ, f τ := fun f a => (Finset.mul_sum Finset.univ f a).symm
    simp only [x, map_sum, galT_Fg, hstep]
    rw [hsum]
    congr 1
    exact Equiv.sum_comp (Equiv.mulLeft (res p L σ)) (fun τ => Fg p L η c (lift p L τ))

end ZInQ.Contrib.SenWeightZero

end

