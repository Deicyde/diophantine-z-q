
/-! ### g0-mod-galois: the range G8-G12 from the leaf bundles -/

namespace G0Galois

open PkgI4 (GaloisRep)

/-- The five named glue pieces of the range G8-G12. -/
structure GaloisPieces : Prop where
  matrix : G8Matrix
  deRham : G9Glue
  odd : G10Glue
  weight : G12Weight
  det : G12Det

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
    r.r11r12 r.r14 r.r13 r.r15 t.t18 t.t19 t.t9 m.matrix m.deRham m.odd m.weight m.det
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
  let U : Subrepresentation (tate A 5) :=
    ⟨LinearMap.range ιA, by rintro σ _ ⟨w, rfl⟩; exact ⟨_, (hAeq σ w).symm⟩⟩
  let U' : Subrepresentation (tate J 5) :=
    ⟨LinearMap.range ιJ, by rintro σ _ ⟨w, rfl⟩; exact ⟨_, (hJeq σ w).symm⟩⟩
  have keyA : ∀ w (h : ιA w ∈ U.toSubmodule),
      (LinearEquiv.ofInjective ιA hιA).symm ⟨ιA w, h⟩ = w := by
    intro w h
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (LinearEquiv.ofInjective_apply ιA hιA w).symm
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
    simp only [LinearEquiv.trans_apply]
    rw [hx, keyA, keyA, LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply]
    exact (hJeq σ w).symm

end G0Galois

#print axioms G0Galois.g8
#print axioms G0Galois.g11
#print axioms G0Galois.g12
#print axioms G0Galois.g8_g12
#print axioms G0Galois.g8_g12_of_leaves
#print axioms G0Galois.commonConstituent_of_sides
