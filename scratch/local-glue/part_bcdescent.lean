
/-! ## §7f (local-glue). `DescentPts` for a base change (proved)

For `L ≤ L'` finite inside `ℚ̄`, `L/ℚ` Galois, and `A₀ : AbVar L` of dimension `2`,
`DescentPts (A₀)_{L'} L` holds (`descentPts_baseChange`), with `(A₀)_{L'}` the base change along
g0-mod-field's `incAlg` (as in g0-assemble's `TateBridge`). The model is the conjugate
`A₁ = A₀ ×_{L,γ} L`, where `γ ∈ Aut(L)` corrects the difference between the embeddings `L ↪ ℚ̄`
that Mathlib chooses inside `resQ L` and inside `resQ L'` (`jL L`, `jL' hLL'`; both have image
`L` since `L/ℚ` is normal). Points: `A₁(L̄) ≅ A₀(L̄_tw) ≅ A₀(L̄') ≅ (A₀)_{L'}(L̄')` by `bcPt`,
`trPt` along `θ = qEmb_{L'} ∘ qEmb_L⁻¹` (`L`-linear for the twisted structure `tw`), and `bcPt`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQ)
open CategoryTheory AlgebraicGeometry Limits MonObj

section BCDescentSec

attribute [local instance] RQ.numberField_of_fd

/-- `qEmb K` as a ring isomorphism `ℚ̄ ≃ K̄`. -/
def qEquiv (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective (G0Galois.qEmbRing K)
    ⟨(G0Galois.qEmbRing K).injective, qEmbRing_surjective K⟩

theorem qEquiv_apply (K : Type) [Field K] [NumberField K] (x : AlgebraicClosure ℚ) :
    qEquiv K x = G0Galois.qEmbRing K x := rfl

/-- The embedding `K ↪ ℚ̄` inside `resQ K`. -/
def jK (K : Type) [Field K] [NumberField K] : K →ₐ[ℚ] AlgebraicClosure ℚ :=
  ((qEquiv K).symm.toRingHom.comp (algebraMap K (AlgebraicClosure K))).toRatAlgHom

theorem qEquiv_jK (K : Type) [Field K] [NumberField K] (x : K) :
    qEquiv K (jK K x) = algebraMap K (AlgebraicClosure K) x := by
  show qEquiv K ((qEquiv K).symm _) = _
  exact (qEquiv K).apply_symm_apply _

variable {L L' : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L]
  [FiniteDimensional ℚ L'] (hLL' : L ≤ L')

/-- The embedding `L ↪ L' ↪ ℚ̄` inside `resQ L'`. -/
def jL' : L →ₐ[ℚ] AlgebraicClosure ℚ := (jK L').comp (IntermediateField.inclusion hLL')

variable [IsGalois ℚ L]

theorem mem_range_jK (x : L) : jL' hLL' x ∈ (jK L).fieldRange := by
  have h1 := AlgHom.fieldRange_of_normal (jK L)
  have h2 := AlgHom.fieldRange_of_normal (jL' hLL')
  have hx : jL' hLL' x ∈ (jL' hLL').fieldRange := ⟨x, rfl⟩
  rw [h2] at hx
  rw [h1]
  exact hx

/-- `γ = jK_L⁻¹ ∘ jL'`, a ring endomorphism of `L`. -/
def γL : L →+* L :=
  (AlgEquiv.ofInjectiveField (jK L)).symm.toRingEquiv.toRingHom.comp
    ((jL' hLL').toRingHom.codRestrict (jK L).fieldRange (mem_range_jK hLL'))

theorem jK_γL (x : L) : jK L (γL hLL' x) = jL' hLL' x := by
  have h := congrArg Subtype.val
    ((AlgEquiv.ofInjectiveField (jK L)).apply_symm_apply ⟨jL' hLL' x, mem_range_jK hLL' x⟩)
  exact h

theorem γL_bijective : Function.Bijective (γL hLL') := by
  have hinj : Function.Injective (γL hLL') := (γL hLL').injective
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective
    (f := (γL hLL').toRatAlgHom.toLinearMap)).mp hinj

/-- g0-mod-field's `incAlg` (`L → L'`). -/
@[instance_reducible] def incAlgL : Algebra L L' := (IntermediateField.inclusion hLL').toRingHom.toAlgebra

/-- The `L`-algebra structure on `L` through `γ`. -/
@[instance_reducible] def γAlg : Algebra L L := (γL hLL').toAlgebra

/-- The twisted `L`-algebra structure on `L̄`: `x ↦ qEmb_L (jL' x)`. -/
@[instance_reducible] def twAlg : Algebra L (AlgebraicClosure L) :=
  ((qEquiv L).toRingHom.comp (jL' hLL').toRingHom).toAlgebra

/-- The `L`-algebra structure on `L̄'` through `L ⊆ L'`. -/
@[instance_reducible] def compAlg : Algebra L (AlgebraicClosure L') :=
  ((algebraMap L' (AlgebraicClosure L')).comp (IntermediateField.inclusion hLL').toRingHom).toAlgebra

theorem tower_tw : @IsScalarTower L L (AlgebraicClosure L) (γAlg hLL').toSMul
    Algebra.toSMul (twAlg hLL').toSMul :=
  @IsScalarTower.of_algebraMap_eq L L (AlgebraicClosure L) _ _ _ (γAlg hLL') _ (twAlg hLL')
    (fun x => by
      show qEquiv L (jL' hLL' x) = algebraMap L (AlgebraicClosure L) (γL hLL' x)
      rw [← qEquiv_jK, jK_γL])

theorem tower_comp : @IsScalarTower L L' (AlgebraicClosure L') (incAlgL hLL').toSMul
    Algebra.toSMul (compAlg hLL').toSMul :=
  @IsScalarTower.of_algebraMap_eq L L' (AlgebraicClosure L') _ _ _ (incAlgL hLL') _ (compAlg hLL')
    (fun x => rfl)

/-- `θ = qEmb_{L'} ∘ qEmb_L⁻¹ : L̄_tw ≃ L̄'`, `L`-linear. -/
def θL : @AlgEquiv L (AlgebraicClosure L) (AlgebraicClosure L') _ _ _ (twAlg hLL')
    (compAlg hLL') :=
  @AlgEquiv.ofRingEquiv L (AlgebraicClosure L) (AlgebraicClosure L') _ _ _ (twAlg hLL')
    (compAlg hLL') ((qEquiv L).symm.trans (qEquiv L')) (fun x => by
      show qEquiv L' ((qEquiv L).symm (qEquiv L (jL' hLL' x))) =
        algebraMap L' (AlgebraicClosure L') (IntermediateField.inclusion hLL' x)
      rw [RingEquiv.symm_apply_apply]
      exact qEquiv_jK L' _)

theorem θL_apply (x : AlgebraicClosure L) : θL hLL' x = qEquiv L' ((qEquiv L).symm x) := rfl

/-- `θ σ₀ = σ' θ` when `resQ_L σ₀ = resQ_{L'} σ'`. -/
theorem θL_galois (σ₀ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L')
    (h : G0Galois.resQ L σ₀ = G0Galois.resQ L' σ') (x : AlgebraicClosure L) :
    σ' (θL hLL' x) = θL hLL' (σ₀ x) := by
  obtain ⟨y, rfl⟩ := (qEquiv L).surjective x
  have hθ : ∀ z, θL hLL' (qEquiv L z) = qEquiv L' z := fun z => by
    rw [θL_apply, RingEquiv.symm_apply_apply]
  have h1 := G0Galois.resQ_spec L σ₀ y
  have h2 := G0Galois.resQ_spec L' σ' y
  calc σ' (θL hLL' (qEquiv L y)) = σ' (qEquiv L' y) := by rw [hθ]
    _ = qEquiv L' (G0Galois.resQ L' σ' y) := h2.symm
    _ = qEquiv L' (G0Galois.resQ L σ₀ y) :=
        congrArg (fun g : GQ => qEquiv L' (g y)) h.symm
    _ = θL hLL' (qEquiv L (G0Galois.resQ L σ₀ y)) := (hθ _).symm
    _ = θL hLL' (σ₀ (qEquiv L y)) := congrArg (θL hLL') h1

/-- The conjugate model `A₁ = A₀ ×_{L,γ} L`. -/
abbrev conjModel (A₀ : PkgI3.AbVar L) : PkgI3.AbVar L :=
  @PkgI3.AbVar.baseChange L _ A₀ L _ (γAlg hLL')

/-- The base change `(A₀)_{L'}` along `incAlg` (as in `TateBridge`). -/
abbrev bcL' (A₀ : PkgI3.AbVar L) : PkgI3.AbVar L' :=
  @PkgI3.AbVar.baseChange L _ A₀ L' _ (incAlgL hLL')

/-- `φ : A₁(L̄) ≅ A₀(L̄_tw) ≅ A₀(L̄') ≅ (A₀)_{L'}(L̄')`. -/
def φL (A₀ : PkgI3.AbVar L) :
    (conjModel hLL' A₀).Pt (AlgebraicClosure L) ≃* (bcL' hLL' A₀).Pt (AlgebraicClosure L') :=
  ((@UnramTate.bcPt L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _ (twAlg hLL')
      (tower_tw hLL')).trans
    (@UnramTate.trPt L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
      (compAlg hLL') (θL hLL'))).trans
    (@UnramTate.bcPt L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _ (compAlg hLL')
      (tower_comp hLL')).symm

/-- `φ` intertwines `σ₀ ∈ G_L` and `σ' ∈ G_{L'}` with the same image in `G_ℚ` (proved). -/
theorem φL_galAct (A₀ : PkgI3.AbVar L) (σ₀ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L')
    (h : G0Galois.resQ L σ₀ = G0Galois.resQ L' σ')
    (P : (conjModel hLL' A₀).Pt (AlgebraicClosure L)) :
    φL hLL' A₀ ((conjModel hLL' A₀).galAct σ₀ P) =
      (bcL' hLL' A₀).galAct σ' (φL hLL' A₀ P) := by
  set b₁ := @UnramTate.bcPt L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _ (twAlg hLL')
      (tower_tw hLL') with hb₁
  set t := @UnramTate.trPt L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
      (compAlg hLL') (θL hLL') with ht
  set b₂ := @UnramTate.bcPt L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _ (compAlg hLL')
      (tower_comp hLL') with hb₂
  have e1 := @UnramTate.bcPt_galAct L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _
    (twAlg hLL') (tower_tw hLL') σ₀ P
  have e3 := @UnramTate.bcPt_galAct L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _
    (compAlg hLL') (tower_comp hLL') σ' (b₂.symm (t (b₁ P)))
  show b₂.symm (t (b₁ ((conjModel hLL' A₀).galAct σ₀ P))) =
    (bcL' hLL' A₀).galAct σ' (b₂.symm (t (b₁ P)))
  apply b₂.injective
  rw [MulEquiv.apply_symm_apply, e3, MulEquiv.apply_symm_apply]
  erw [e1]
  exact @UnramTate.trPt_galAct L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
    (compAlg hLL') (θL hLL') _ _ (fun x => θL_galois hLL' σ₀ σ' h x) (b₁ P)

/-- The conjugate model has the dimension of `A₀` (proved): base change along the isomorphism
`Spec γ` is homeomorphic to `A₀`. -/
theorem dim_conjModel (A₀ : PkgI3.AbVar L) : (conjModel hLL' A₀).dim = A₀.dim := by
  let e : L ≃+* L := RingEquiv.ofBijective (γL hLL') (γL_bijective hLL')
  have hiso : IsIso (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))) :=
    e.toCommRingCatIso.isIso_hom
  have hiso2 : IsIso (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL')))) :=
    inferInstance
  have hiso3 : IsIso (pullback.fst (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))))) := inferInstance
  show topologicalKrullDim (pullback (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))))) =
    topologicalKrullDim A₀.X.left
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.Hom.homeomorph (pullback.fst (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL')))))).isHomeomorph

/-- **`DescentPts` for a base change (proved).** For `L ≤ L'` finite in `ℚ̄`, `L/ℚ` Galois, and
`A₀ : AbVar L` with `dim A₀ = 2`, `DescentPts ((A₀)_{L'}) L` holds for G7Out's model field
`K = L'`, with the conjugate model `A₀ ×_{L,γ} L`. -/
theorem descentPts_baseChange (A₀ : PkgI3.AbVar L) (hdim : A₀.dim = 2) :
    DescentPts (K := L') (bcL' hLL' A₀) L :=
  ⟨inferInstance, conjModel hLL' A₀, φL hLL' A₀, (dim_conjModel hLL' A₀).trans hdim,
    fun σ₀ σ' h P => φL_galAct hLL' A₀ σ₀ σ' h P⟩

/-- **`LocalGlue` on G7's construction (proved).** For g0-mod-field's data: `L ≤ L'` finite
Galois in `ℚ̄`, `A₀ : AbVar L` with `dim A₀ = 2`, G7Out for `(A₀)_{L'}` over `K = L'`, G7's clauses,
the kernel-field clause `G_{L'} = G_L ∩ ker β_ℂ`, and the transport `β = ι ∘ β_ℂ` with `ι`
injective, `LocalGlue p Tm a β L` holds at every `p ≠ ℓ`, from the leaves R6 and I2-Tors and the
textbook Prop `UnramRoots` (used at `p = 2`). -/
theorem localGlue_of_baseChange {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : UnramRoots p ℓ) (hpℓ : p ≠ ℓ) [IsGalois ℚ L'] (A₀ : PkgI3.AbVar L)
    (hdim₀ : A₀.dim = 2)
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb (bcL' hLL' A₀) ℓ)}
    {c ε : GQ → GQ → PadicAlgCl ℓ} {a β : GQ → PadicAlgCl ℓ}
    {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb (bcL' hLL' A₀) ℓ)}
    (h7 : G0Galois.G7Out (bcL' hLL' A₀) ℓ Tm c ε a β u) (hC : G7Clauses β ε L)
    (βC : GQ → ℂˣ) (hker : ∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ) (hι : Function.Injective ιC)
    (hβ : ∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ)) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hC (kerWild_of_g7Data βC hker ιC hι hβ)
    (fun _ => descentPts_baseChange hLL' A₀ hdim₀)

/-- **`LocalGlue` on G7's construction, with `dim A₀ = 2` derived (proved):** as
`localGlue_of_baseChange`, where `dim A₀ = dim (A₀)_{L'} = 2` by g0-dim's
`G0Dim.pkgI3_dim_baseChange` (field base change preserves dimension) and G7Out's `dim` clause. -/
theorem localGlue_of_baseChange' {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : UnramRoots p ℓ) (hpℓ : p ≠ ℓ) [IsGalois ℚ L'] (A₀ : PkgI3.AbVar L)
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb (bcL' hLL' A₀) ℓ)}
    {c ε : GQ → GQ → PadicAlgCl ℓ} {a β : GQ → PadicAlgCl ℓ}
    {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb (bcL' hLL' A₀) ℓ)}
    (h7 : G0Galois.G7Out (bcL' hLL' A₀) ℓ Tm c ε a β u) (hC : G7Clauses β ε L)
    (βC : GQ → ℂˣ) (hker : ∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ) (hι : Function.Injective ιC)
    (hβ : ∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ)) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_baseChange hLL' hR6 hTors hU hpℓ A₀
    ((@G0Dim.pkgI3_dim_baseChange L _ L' _ (incAlgL hLL') A₀).symm.trans h7.1) h7 hC βC hker ιC
    hι hβ

end BCDescentSec


end G15Ram

end

#print axioms G15Ram.descentPts_baseChange
#print axioms G15Ram.localGlue_of_baseChange
#print axioms G15Ram.localGlue_of_baseChange'
