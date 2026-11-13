
/-! ### g0-mod-galois: the range G8-G12 from the leaf bundles -/

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

noncomputable section

/-- The pieces of the range G8-G12 that are not in the leaf bundles: Burnside (a textbook leaf;
`G8Matrix` is proved from it, `g8Matrix_of_burnside`), R14's determinant clause (a leaf, R14 as
published), and the named glue `G9Glue`, `G10Glue`, `G12Weight`, `DetTate`, `ResQFiniteIndex`
(`G12Det` is proved from the last two, R14Det and T18, `g12Det_of`). -/
structure GaloisPieces : Prop where
  burnside : BurnsideAbsIrred
  r14det : R14Det
  deRham : G9Glue
  odd : G10Glue
  weight : G12Weight
  detTate : DetTate
  finIndex : ResQFiniteIndex

/-- **G8-G12 from the leaf bundles** (`HSyn.ResearchLeaves`, `HSyn.TextbookLeaves`), glue-ssbc's
proved `SemisimpleBaseChange`, the outputs of G2, G3, G6, G7 and the five named pieces. -/
theorem g8_g12_of_leaves (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves) (m : GaloisPieces)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r₅ : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r₅ ∧ G9Out r₅ ∧ G10Out r₅ ∧
      G11Out T r₅ ∧ G12Out r₅ :=
  g8_g12 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t23 t.t11 t.t12
    r.r11r12 r.r14 r.r13 r.r15 t.t18 t.t19 t.t9 (g8Matrix_of_burnside m.burnside) m.deRham m.odd m.weight
    (g12Det_of m.r14det m.detTate m.finIndex (frobeniusDenseQ_of t.t18))
    A T h2 h6 h3 Tm c ε a β u h7

/-! ### How the conclusion feeds G13-G16 and `ModularConstituent` -/

/-- **What G13-G16 must deliver on the `J₁(N)` side** (input of the link lemma below): an
injective `G_K`-equivariant map from `r|G_K` (the matrices `r(σ)`, `σ ∈ G_K`, on `ℚ̄₅²`) into
`ℚ̄₅ ⊗ V₅(J)`, for `J = J₁(N)_{L'}` (G13: `r₅ ≅ ρ_{f,5}` and `ρ_{f,5} ⊂ V₅(J₁(N))`, R16). -/
def JSide {K : Type} [Field K] [NumberField K] (J : PkgI3.AbVar K) (r : GaloisRep 5 2) : Prop :=
  ∃ ιJ : (Fin 2 → PadicAlgCl 5) →ₗ[PadicAlgCl 5] Vb J 5, Function.Injective ιJ ∧
    ∀ σ w, tate J 5 σ (ιJ w) = ιJ ((r.mat (resQ K σ)).mulVec w)

/-- **Link lemma (proved).** G8's output (`ℚ̄₅ ⊗ V₅(A) ≅ r|G_K ⊕ r|G_K`) and the `J`-side of
G13-G16 (`JSide`) give `CommonConstituent A J`, the field of `ModularConstituent` that E1
(`PkgI3.E1_exists_hom_ne_zero`) consumes, with `ℓ = 5` and `E = ℚ̄₅`. -/
theorem commonConstituent_of_sides {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K)
    (r : GaloisRep 5 2)
    (e : Vb A 5 ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5) × (Fin 2 → PadicAlgCl 5))
    (hint : Intertwines (tate A 5) (fun σ => r.mat (resQ K σ)) e) (hJ : JSide J r) :
    HSyn.G0Split.CommonConstituent A J := by
  obtain ⟨ιJ, hιJ, hJeq⟩ := hJ
  let ιA : (Fin 2 → PadicAlgCl 5) →ₗ[PadicAlgCl 5] Vb A 5 :=
    e.symm.toLinearMap ∘ₗ LinearMap.inl (PadicAlgCl 5) _ _
  have hιA : Function.Injective ιA := e.symm.injective.comp LinearMap.inl_injective
  have hAeq : ∀ σ w, tate A 5 σ (ιA w) = ιA ((r.mat (resQ K σ)).mulVec w) := by
    intro σ w
    apply e.injective
    have h := hint σ (ιA w)
    simp only [ιA, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.inl_apply, LinearEquiv.apply_symm_apply] at h ⊢
    rw [h, Matrix.mulVec_zero]
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl 5) (A.galRep 5)) :=
    ⟨LinearMap.range ιA, by rintro σ _ ⟨w, rfl⟩; exact ⟨_, (hAeq σ w).symm⟩⟩
  let U' : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl 5) (J.galRep 5)) :=
    ⟨LinearMap.range ιJ, by rintro σ _ ⟨w, rfl⟩; exact ⟨_, (hJeq σ w).symm⟩⟩
  have keyA : ∀ w (h : ιA w ∈ U.toSubmodule),
      (LinearEquiv.ofInjective ιA hιA).symm ⟨ιA w, h⟩ = w := by
    intro w h
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    first
      | rfl
      | exact (LinearEquiv.ofInjective_apply (h := hιA) w).symm
  refine ⟨5, inferInstance, PadicAlgCl 5, inferInstance, inferInstance, U, U',
    (LinearEquiv.ofInjective ιA hιA).symm.trans (LinearEquiv.ofInjective ιJ hιJ), ?_, ?_⟩
  · intro h
    have h' : ιA (Pi.single 0 1) ∈ U.toSubmodule := ⟨_, rfl⟩
    rw [h] at h'
    have h0 : ιA (Pi.single 0 1) = 0 := h'
    have := hιA (h0.trans (map_zero ιA).symm)
    have := congrFun this 0
    simp at this
  · rintro σ ⟨_, w, rfl⟩
    have hmem : ιA ((r.mat (resQ K σ)).mulVec w) ∈ U.toSubmodule := ⟨_, rfl⟩
    have hx : (⟨GlueI3.repBaseChange (PadicAlgCl 5) (A.galRep 5) σ (ιA w),
        U.apply_mem_toSubmodule σ ⟨w, rfl⟩⟩ : U.toSubmodule) = ⟨_, hmem⟩ :=
      Subtype.ext (hAeq σ w)
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hx, keyA]
    first
      | (erw [keyA]; exact (hJeq σ w).symm)
      | (simp only [keyA]; exact (hJeq σ w).symm)

/-! ### Feeding g0-mod-newform's `G12Out` (G13-G16's input)

The next four definitions are copied verbatim from `scratch/g0-mod-newform/part_new.lean`
(commit 217e17f0), where they are G13's input interface. -/

namespace NF

/-- (copied from g0-mod-newform) `ρ` as a `Representation` on `ℚ̄_ℓⁿ`. -/
def toRep {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ : GaloisRep ℓ n) :
    Representation (PadicAlgCl ℓ) PkgI4.GQ (Fin n → PadicAlgCl ℓ) where
  toFun σ := Matrix.toLin' (ρ.mat σ)
  map_one' := by
    simp only [PkgI4.GaloisRep.mat, map_one, Units.val_one, Matrix.toLin'_one]; rfl
  map_mul' σ τ := by
    simp only [PkgI4.GaloisRep.mat, map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl

/-- (copied from g0-mod-newform) Pan-Berger's output on `r`, with the twist a Dirichlet
character at arithmetic Frobenius outside `S`. -/
def PanOutput {ℓ : ℕ} [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (r : GaloisRep ℓ 2) : Prop :=
  ∃ (M : ℕ) (χg : DirichletCharacter ℂ M) (g : PkgI4.CF M 2) (m : ℕ)
    (ψD : DirichletCharacter ℂ m) (ψ : GaloisChar ℓ) (S : Finset ℕ),
    0 < M ∧ PkgI4.IsNormalizedEigenform g χg ∧ 0 < m ∧ r.AttachedUpToTwist ψ ιC ιL g S ∧
    ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : PkgI4.Qbar, ιC β = ψD (p : ZMod m) ∧
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ), PkgI4.LiesOver v p →
        PkgI4.IsArithFrob τ v p → (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-- (copied from g0-mod-newform) `r|_{G_L}` is a constituent of `V_ℓ(A) ⊗ ℚ̄_ℓ`. -/
def IsConstituentOf (ℓ : ℕ) [Fact ℓ.Prime] {L : Type} [Field L] [Algebra ℚ L]
    (A : PkgI3.AbVar L) (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L)
    (r : GaloisRep ℓ 2) : Prop :=
  ∃ (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ)), U ≠ ⊥ ∧
    ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : PkgI4.GQ), (∀ x, i (σ x) = τ (i x)) →
      ∀ u : U.toSubmodule,
        e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) τ u, U.apply_mem_toSubmodule τ u.2⟩ =
          toRep r σ (e u)

/-- (copied from g0-mod-newform) The data that G8-G12 produce for the model `A/L'`. -/
structure ModData (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L) where
  i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L
  ιC : PkgI4.Qbar →ₐ[ℚ] ℂ
  ι5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5
  ι3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3
  r5 : GaloisRep 5 2
  r3 : GaloisRep 3 2

instance fact_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- (copied from g0-mod-newform) G13's input on the data `D`. -/
def G12Spec {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) : Prop :=
  D.r5.IsIrreducible ∧ D.r3.IsIrreducible ∧ IsConstituentOf 5 A D.i D.r5 ∧
    IsConstituentOf 3 A D.i D.r3 ∧ PanOutput D.ιC D.ι5 D.r5

/-- (copied from g0-mod-newform, there `G12Out`) some data `D` for `A` satisfy `G12Spec`. -/
def NewformG12Out {L : Type} [Field L] [NumberField L] (A : PkgI3.AbVar L) : Prop :=
  ∃ D : ModData L A, G12Spec D

end NF

/-- **Finite characters are Dirichlet characters (GLUE, unproved; h-trust C8 item 4).** From T17
(Kronecker–Weber): a continuous `ψ : G_ℚ → ℚ̄_ℓ^×` of finite image is, at arithmetic Frobenius
elements above `p ∉ S` (`S` the primes dividing the conductor `m`), the image under `ιL` of an
algebraic number `β` (a root of unity) with `ιC(β) = ψD(p)` for a Dirichlet character `ψD`
mod `m`. True: the kernel field of `ψ` is finite abelian over `ℚ`, hence inside `ℚ(ζ_m)`; the
values are roots of unity, which lie in `ιL(ℚ̄)`. -/
def FiniteCharDirichlet : Prop :=
  HSyn.KroneckerWeber →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ψ : GaloisChar ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ), (Set.range ψ.toHom).Finite →
    ∃ (m : ℕ) (ψD : DirichletCharacter ℂ m) (S : Finset ℕ), 0 < m ∧
      ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : PkgI4.Qbar, ιC β = ψD (p : ZMod m) ∧
        ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ), PkgI4.LiesOver v p →
          PkgI4.IsArithFrob τ v p → (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-- **G8's output gives g0-mod-newform's constituent clause (proved).** With `i = qEmb K`, the
`σ` with `i ∘ σ = τ ∘ i` is `resQ K τ` (`eq_resQ`), so G8's intertwining is `IsConstituentOf`. -/
theorem isConstituentOf_of_intertwines {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hint : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) :
    NF.IsConstituentOf ℓ A (qEmb K) r := by
  let ιA : (Fin 2 → PadicAlgCl ℓ) →ₗ[PadicAlgCl ℓ] Vb A ℓ :=
    e.symm.toLinearMap ∘ₗ LinearMap.inl (PadicAlgCl ℓ) _ _
  have hιA : Function.Injective ιA := e.symm.injective.comp LinearMap.inl_injective
  have hAeq : ∀ σ w, tate A ℓ σ (ιA w) = ιA ((r.mat (resQ K σ)).mulVec w) := by
    intro σ w
    apply e.injective
    have h := hint σ (ιA w)
    simp only [ιA, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.inl_apply, LinearEquiv.apply_symm_apply] at h ⊢
    rw [h, Matrix.mulVec_zero]
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)) :=
    ⟨LinearMap.range ιA, by rintro σ _ ⟨w, rfl⟩; exact ⟨_, (hAeq σ w).symm⟩⟩
  have keyA : ∀ w (h : ιA w ∈ U.toSubmodule),
      (LinearEquiv.ofInjective ιA hιA).symm ⟨ιA w, h⟩ = w := by
    intro w h
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    first
      | rfl
      | exact (LinearEquiv.ofInjective_apply (h := hιA) w).symm
  refine ⟨U, (LinearEquiv.ofInjective ιA hιA).symm, ?_, ?_⟩
  · intro h
    have h' : ιA (Pi.single 0 1) ∈ U.toSubmodule := ⟨_, rfl⟩
    rw [h] at h'
    have h0 : ιA (Pi.single 0 1) = 0 := h'
    have := hιA (h0.trans (map_zero ιA).symm)
    have := congrFun this 0
    simp at this
  · rintro τ σ hσ ⟨_, w, rfl⟩
    have hστ := eq_resQ K τ σ hσ
    have hmem : ιA ((r.mat (resQ K τ)).mulVec w) ∈ U.toSubmodule := ⟨_, rfl⟩
    have hx : (⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) τ (ιA w),
        U.apply_mem_toSubmodule τ ⟨w, rfl⟩⟩ : U.toSubmodule) = ⟨_, hmem⟩ :=
      Subtype.ext (hAeq τ w)
    rw [hx, keyA]
    first
      | (erw [keyA]; subst hστ; rfl)
      | (simp only [keyA]; subst hστ; rfl)
      | (erw [keyA]; subst hστ; simp [NF.toRep, Matrix.toLin'_apply])
      | (simp only [keyA]; subst hστ; simp [NF.toRep, Matrix.toLin'_apply])

/-- **G12's output gives g0-mod-newform's `PanOutput` (proved from `FiniteCharDirichlet`).** -/
theorem panOutput_of_g12 (hKW : HSyn.KroneckerWeber) (hFD : FiniteCharDirichlet)
    (r : GaloisRep 5 2) (h : G12Out r) : ∃ ιC ιL, NF.PanOutput ιC ιL r := by
  obtain ⟨N, χ, g, ψ, ιC, ιL, S, hN, hg, hfin, hatt⟩ := h
  obtain ⟨m, ψD, S', hm, hD⟩ := hFD hKW 5 ψ ιC ιL hfin
  refine ⟨ιC, ιL, N, χ, g, m, ψD, ψ, S ∪ S', hN, hg, hm, ?_, ?_⟩
  · intro p hp hpS
    exact hatt p hp (fun h' => hpS (Finset.mem_union_left _ h'))
  · intro p hp hpS
    exact hD p hp (fun h' => hpS (Finset.mem_union_right _ h'))

/-- **The range G8-G12 delivers g0-mod-newform's input `G12Out` (there; here `NF.NewformG12Out`).**
Proved from the leaves, the outputs of G2, G3, G6, G7 at `ℓ = 3` and `ℓ = 5`, the five named
pieces of this range and `FiniteCharDirichlet`. -/
theorem newformG12Out_of_galois (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : GaloisPieces) (hFD : FiniteCharDirichlet)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3₅ : G3Out A 5 T) (h3₃ : G3Out A 3 T)
    (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a₅ β₅ : PkgI4.GQ → PadicAlgCl 5)
    (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7₅ : G7Out A 5 Tm₅ c₅ ε₅ a₅ β₅ u₅)
    (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3) (Vb A 3))
    (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3) (a₃ β₃ : PkgI4.GQ → PadicAlgCl 3)
    (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3) (Vb A 3))
    (h7₃ : G7Out A 3 Tm₃ c₃ ε₃ a₃ β₃ u₃) (ι3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3) :
    NF.NewformG12Out A := by
  obtain ⟨r₅, ⟨hres₅, e₅, hint₅, hadj₅⟩, -, -, -, h12⟩ :=
    g8_g12_of_leaves r t m A T h2 h6 h3₅ Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, ⟨hres₃, e₃, hint₃, hadj₃⟩, -, -, -⟩ :=
    g8_g11 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t23 t.t11 t.t12
      (g8Matrix_of_burnside m.burnside) m.deRham m.odd A T h2 h6 3 h3₃ Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨ιC, ι5, hpan⟩ := panOutput_of_g12 t.t17 hFD r₅ h12
  exact ⟨⟨qEmb K, ιC, ι5, ι3, r₅, r₃⟩, isIrreducible_of_g8 hadj₅, isIrreducible_of_g8 hadj₃,
    isConstituentOf_of_intertwines A 5 r₅ e₅ (intertwines_res hres₅ hint₅),
    isConstituentOf_of_intertwines A 3 r₃ e₃ (intertwines_res hres₃ hint₃), hpan⟩

end

end G0Galois

#print axioms G0Galois.g8
#print axioms G0Galois.g8Matrix_of_burnside
#print axioms G0Galois.g11
#print axioms G0Galois.g12
#print axioms G0Galois.g8_g12
#print axioms G0Galois.g8_g12_of_leaves
#print axioms G0Galois.commonConstituent_of_sides
#print axioms G0Galois.isConstituentOf_of_intertwines
#print axioms G0Galois.newformG12Out_of_galois
