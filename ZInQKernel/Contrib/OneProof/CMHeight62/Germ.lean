import ZInQKernel.Contrib.OneProof.CMHeight62.Periods
import ZInQKernel.Contrib.OneProof.CMHeight62.Eval
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.Linearity

/-! # cmheight62-p1, step 4 (evaluation bridge): the germ `t` of `−x/y` along a uniformization

`jacDet` differentiates the evaluation of a chosen representative (`exists_rep`) of the germ
`t = tG ∈ 𝒪_{𝒢,ξ}`. We show that near `0` this evaluation, times `y`, is `−x`, all evaluated at
the image point in `E(ℂ)_{σ|K}`:

1. in the generic fibre `𝒢_L`, the pull-back of the representative of `t` and the pull-back
   (through `gen : 𝒢_L ≅ E_L` and `E_L → E`) of a representative `r` of `t_E` have the same germ
   at the identity `ξ_L` (`originStalkEquiv_spec`), hence agree on an open `W ∋ ξ_L`;
2. a complex point `p` of `𝒢` factors as `gpt p : Spec ℂ → 𝒢_L` followed by the projection,
   and `χ p = gpt p ≫ gen`; so near `0` both values are values of the same section on `W`;
3. on `E`, `r · y = −x` on `V_E ∩ (E ∖ 0)` (injectivity into the function field). -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice IsLocalRing
open _root_.ZInQ.LeafPush2 (CPts cptObj cDom cEvalAt IsUniformization)
open HDec.CMBranch.CMjBridges
open ZInQ.Contrib.RC53Assist.HodgeLineBinding (originStalkEquiv originStalkEquiv_spec
  gen_genericFibreUnit_eq stalkMapAt)

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

/-- Identification of stalks at inseparable points sends germs to germs. -/
theorem stalkCongr_germ {X : Scheme.{0}} {x y : X} (h : Inseparable x y) (V : X.Opens)
    (hx : x ∈ V) (s : Γ(X, V)) :
    (X.presheaf.stalkCongr h).hom (X.presheaf.germ V x hx s) =
      X.presheaf.germ V y (h.mem_open_iff V.isOpen |>.mp hx) s := by
  have h1 := ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf
    (U := V) hx h.ge) s
  rw [ConcreteCategory.comp_apply] at h1
  exact h1

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

section GenericFibre

variable (𝒢 : GroupModel E L)

/-- The projection `𝒢_L → 𝒢`. -/
abbrev fstGF : (genericFibre L 𝒢.G).left ⟶ 𝒢.G.left := pullback.fst 𝒢.G.hom (toGeneric L)

/-- The composite `𝒢_L ≅ E_L → E`. -/
def genE : (genericFibre L 𝒢.G).left ⟶ E.X.left := 𝒢.gen.hom.left ≫ bcProj E L

theorem genE_unit : genE 𝒢 (genericFibreUnit 𝒢) = abVarIdentity E := by
  change bcProj E L (𝒢.gen.hom.left (genericFibreUnit 𝒢)) = _
  rw [gen_genericFibreUnit_eq]
  exact bcProj_identity E L

/-- **Germ comparison in the generic fibre.** If `s ∈ Γ(𝒢, U)` represents `t = tG` at `ξ` and
`r ∈ Γ(E, V)` represents `t_E` at the identity, their pull-backs to `𝒢_L` have the same germ at
`ξ_L`. -/
theorem germ_pullbacks_eq (D : ShortData E) {U : 𝒢.G.left.Opens} (hU : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U)) (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit hU s = (D.tG 𝒢 : _))
    {V : E.X.left.Opens} (hV : abVarIdentity E ∈ V) (r : Γ(E.X.left, V))
    (hr : E.X.left.presheaf.germ V (abVarIdentity E) hV r = D.tE) :
    (genericFibre L 𝒢.G).left.presheaf.germ (fstGF 𝒢 ⁻¹ᵁ U) (genericFibreUnit 𝒢)
        (by show pullback.fst 𝒢.G.hom (toGeneric L) (genericFibreUnit 𝒢) ∈ U
            rw [fst_genericFibreUnit]; exact hU)
        ((fstGF 𝒢).app U s) =
      (genericFibre L 𝒢.G).left.presheaf.germ (genE 𝒢 ⁻¹ᵁ V) (genericFibreUnit 𝒢)
        (by change genE 𝒢 (genericFibreUnit 𝒢) ∈ V; rw [genE_unit]; exact hV)
        ((genE 𝒢).app V r) := by
  have hspec := originStalkEquiv_spec 𝒢 (D.tG 𝒢 : 𝒢.genStalk)
  have htG : originStalkEquiv 𝒢 (D.tG 𝒢 : 𝒢.genStalk) = ShortData.tL D := by
    change originStalkEquiv 𝒢 ((originStalkEquiv 𝒢).symm (ShortData.tL D)) = _
    exact RingEquiv.apply_symm_apply _ _
  rw [htG, ← hs] at hspec
  -- right side of `hspec`
  have hfu : fstGF 𝒢 (genericFibreUnit 𝒢) ∈ U := by
    show pullback.fst 𝒢.G.hom (toGeneric L) (genericFibreUnit 𝒢) ∈ U
    rw [fst_genericFibreUnit]; exact hU
  erw [stalkCongr_germ _ U hU s] at hspec
  erw [Scheme.Hom.germ_stalkMap_apply (fstGF 𝒢) U (genericFibreUnit 𝒢) hfu s] at hspec
  rw [← hspec]
  -- left side: `tL` is the germ of the pull-back of `r`
  have hbo : bcProj E L (abVarIdentity (E.baseChange L)) ∈ V := by
    rw [bcProj_identity]; exact hV
  have htL : ShortData.tL D = (E.baseChange L).X.left.presheaf.germ (bcProj E L ⁻¹ᵁ V)
      (abVarIdentity (E.baseChange L)) hbo ((bcProj E L).app V r) := by
    change (stalkMapAt (bcProj E L) (bcProj_identity E L)).hom D.tE = _
    rw [← hr]
    unfold stalkMapAt
    rw [CommRingCat.comp_apply]
    erw [stalkCongr_germ _ V hV r]
    exact Scheme.Hom.germ_stalkMap_apply (bcProj E L) V _ hbo r
  rw [htL]
  erw [stalkCongr_germ]
  erw [Scheme.Hom.germ_stalkMap_apply 𝒢.gen.hom.left (bcProj E L ⁻¹ᵁ V) (genericFibreUnit 𝒢)]
  rfl

end GenericFibre

section Points

variable (𝒢 : GroupModel E L) {σ : L →+* ℂ}

/-- The point of `Spec ℂ`, typed in `cptObj σ`. -/
def ptc {F : Type} [Field F] (σ : F →+* ℂ) : (cptObj σ).left := IsLocalRing.closedPoint ℂ

theorem eq_ptc {F : Type} [Field F] (σ : F →+* ℂ) (x : (cptObj σ).left) : x = ptc σ :=
  Subsingleton.elim (α := PrimeSpectrum ℂ) _ _

theorem top_le_preimage_iff {F : Type} [Field F] {τ : F →+* ℂ} {X : Scheme.{0}}
    (q : (cptObj τ).left ⟶ X) (W : X.Opens) : ⊤ ≤ q ⁻¹ᵁ W ↔ q (ptc τ) ∈ W := by
  constructor
  · intro h; exact h (Set.mem_univ _)
  · intro h x _
    rw [eq_ptc τ x]; exact h

/-- The point `Spec ℂ → 𝒢_L` underlying a complex point of `𝒢`. -/
def gpt (p : 𝒢.Pts σ) : (cptObj σ).left ⟶ (genericFibre L 𝒢.G).left :=
  (ZInQ.Metrization2.secC σ).left ≫ (ZInQ.Metrization2.mapG 𝒢 p).left

theorem gpt_fst (p : 𝒢.Pts σ) : gpt 𝒢 p ≫ fstGF 𝒢 = p.left :=
  (Category.assoc _ _ _).trans ((congrArg ((ZInQ.Metrization2.secC σ).left ≫ ·)
    (ZInQ.Metrization2.mapG_fstG 𝒢 p)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ p.left) (ZInQ.Metrization2.secC_fstC (L := L) σ)).trans
        (Category.id_comp _))))

theorem chi_left (p : 𝒢.Pts σ) :
    (ZInQ.Metrization2.chi 𝒢 p).left = gpt 𝒢 p ≫ 𝒢.gen.hom.left := by
  unfold ZInQ.Metrization2.chi gpt
  simp only [Over.comp_left, Category.assoc]

theorem gpt_eq (p : 𝒢.Pts σ) :
    gpt 𝒢 p = (ZInQ.Metrization2.chi 𝒢 p).left ≫ 𝒢.gen.inv.left :=
  ((Category.comp_id _).symm.trans (congrArg (gpt 𝒢 p ≫ ·)
    (ZInQ.Metrization2.gen_hom_inv_left 𝒢).symm)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ 𝒢.gen.inv.left) (chi_left 𝒢 p).symm))

theorem evalAt_eq_ev (p : 𝒢.Pts σ) (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U s = ev (gpt 𝒢 p) (fstGF 𝒢 ⁻¹ᵁ U) ((fstGF 𝒢).app U s) :=
  (congrArg (fun q : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left => ev q U s) (gpt_fst 𝒢 p).symm).trans
    (ev_comp (gpt 𝒢 p) (fstGF 𝒢) U s)

theorem ptL_chi_left (p : 𝒢.Pts σ) :
    (ptL E σ (ZInQ.Metrization2.chi 𝒢 p)).left = gpt 𝒢 p ≫ genE 𝒢 :=
  (ptL_left E σ _).trans ((congrArg (· ≫ bcProj E L) (chi_left 𝒢 p)).trans
    (Category.assoc _ _ _))

theorem cEvalAt_ptL_chi_eq_ev (p : 𝒢.Pts σ) (V : E.X.left.Opens) (r : Γ(E.X.left, V)) :
    cEvalAt (ptL E σ (ZInQ.Metrization2.chi 𝒢 p)) V r =
      ev (gpt 𝒢 p) (genE 𝒢 ⁻¹ᵁ V) ((genE 𝒢).app V r) :=
  (congrArg (fun q : Spec (CommRingCat.of ℂ) ⟶ E.X.left => ev q V r)
    (ptL_chi_left 𝒢 p)).trans (ev_comp (gpt 𝒢 p) (genE 𝒢) V r)

theorem one_left_apply (A : PkgI3.AbVar L) :
    (1 : CPts A σ).left (ptc σ) = abVarIdentity A := by
  change (η[A.X]).left ((cptObj σ).hom (ptc σ)) = _
  congr 1
  exact Subsingleton.elim _ _

theorem chi_one : ZInQ.Metrization2.chi 𝒢 (1 : 𝒢.Pts σ) = 1 := by
  have h := ZInQ.Metrization2.chi_mul 𝒢 (τ := σ) 1 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem gen_inv_identity :
    𝒢.gen.inv.left (abVarIdentity (E.baseChange L)) = genericFibreUnit 𝒢 := by
  have h := congrArg (fun f => f (genericFibreUnit 𝒢)) (ZInQ.Metrization2.gen_hom_inv_left 𝒢)
  have h' : 𝒢.gen.inv.left (𝒢.gen.hom.left (genericFibreUnit 𝒢)) = genericFibreUnit 𝒢 := h
  rwa [gen_genericFibreUnit_eq] at h'

theorem gpt_one_apply : gpt 𝒢 (1 : 𝒢.Pts σ) (ptc σ) = genericFibreUnit 𝒢 := by
  have h := congrArg (fun f => f (ptc σ)) (gpt_eq 𝒢 (1 : 𝒢.Pts σ))
  have h' : gpt 𝒢 1 (ptc σ) =
      𝒢.gen.inv.left ((ZInQ.Metrization2.chi 𝒢 (1 : 𝒢.Pts σ)).left (ptc σ)) := h
  rw [h', chi_one, one_left_apply]
  exact gen_inv_identity 𝒢

end Points

section ESide

variable (D : ShortData E)

theorem genericPoint_mem {V : E.X.left.Opens} (hV : (V : Set E.X.left).Nonempty) :
    genericPoint E.X.left ∈ V :=
  ((genericPoint_spec E.X.left).mem_open_set_iff V.isOpen).mpr (by simpa using hV)

/-- **`r · y = −x` on `V ∩ (E ∖ 0)`** for a representative `r` of `t_E`. -/
theorem rep_mul_y {V : E.X.left.Opens} (hV : abVarIdentity E ∈ V) (r : Γ(E.X.left, V))
    (hr : E.X.left.presheaf.germ V (abVarIdentity E) hV r = D.tE) :
    E.X.left.presheaf.map (homOfLE (inf_le_left : V ⊓ abVarPunctured E ≤ V)).op r *
      E.X.left.presheaf.map (homOfLE (inf_le_right : V ⊓ abVarPunctured E ≤ _)).op D.y =
    -E.X.left.presheaf.map (homOfLE (inf_le_right : V ⊓ abVarPunctured E ≤ _)).op D.x := by
  have := D.nonempty_punctured
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  have : Nonempty (V ⊓ abVarPunctured E : E.X.left.Opens) := by
    obtain ⟨⟨w, hw⟩⟩ := D.nonempty_punctured
    exact ⟨⟨genericPoint E.X.left, genericPoint_mem ⟨_, hV⟩, genericPoint_mem ⟨w, hw⟩⟩⟩
  apply E.X.left.germToFunctionField_injective (V ⊓ abVarPunctured E)
  rw [map_mul, map_neg, germToFunctionField_restrict, germToFunctionField_restrict,
    germToFunctionField_restrict, ← E.X.left.algebraMap_germ_eq_germToFunctionField hV, hr]
  erw [D.algebraMap_tE]
  change D.fXY * D.Y = -D.X
  rw [ShortData.fXY, neg_div, neg_mul, div_mul_cancel₀ _ D.Y_ne_zero]

/-- The evaluated form of `rep_mul_y`. -/
theorem ev_rep_mul_y {V : E.X.left.Opens} (hV : abVarIdentity E ∈ V) (r : Γ(E.X.left, V))
    (hr : E.X.left.presheaf.germ V (abVarIdentity E) hV r = D.tE)
    (q : Spec (CommRingCat.of ℂ) ⟶ E.X.left) (hq : ⊤ ≤ q ⁻¹ᵁ (V ⊓ abVarPunctured E)) :
    ev q V r * ev q (abVarPunctured E) D.y = -ev q (abVarPunctured E) D.x := by
  rw [ev_res q (inf_le_left : V ⊓ abVarPunctured E ≤ V) hq,
    ev_res q (inf_le_right : V ⊓ abVarPunctured E ≤ _) hq D.y,
    ev_res q (inf_le_right : V ⊓ abVarPunctured E ≤ _) hq D.x, ← ev_mul q _ hq, ← ev_neg q _ hq,
    rep_mul_y D hV r hr]

end ESide

section Bridge

open Filter Topology

/-- **The evaluation bridge.** Along an analytic uniformization `Φ` of the model, for `z` near
`0`, the chosen representative of `t = tG` (the one `germAlong`, hence `jacDet`, uses) satisfies
`t(Φ z) · y(p z) = −x(p z)` at the image point `p z ∈ E(ℂ)_{σ|K}` whenever `p z ≠ 0`. -/
theorem germAlong_mul_y (D : ShortData E) (𝒢 : GroupModel E L) {σ : L →+* ℂ}
    {Λ : Submodule ℤ (Fin 1 → ℂ)} {Φ : (Fin 1 → ℂ) → 𝒢.Pts σ}
    (hΦ : 𝒢.IsAnalyticUniformization σ Λ Φ)
    (hopen : ∀ W : (genericFibre L 𝒢.G).left.Opens, IsOpen {z | ⊤ ≤ gpt 𝒢 (Φ z) ⁻¹ᵁ W}) :
    ∀ᶠ z in 𝓝 0, ⊤ ≤ (ptL E σ (ZInQ.Metrization2.chi 𝒢 (Φ z))).left ⁻¹ᵁ abVarPunctured E →
      𝒢.germAlong Φ (D.tG 𝒢 : 𝒢.genStalk) z *
          cEvalAt (ptL E σ (ZInQ.Metrization2.chi 𝒢 (Φ z))) (abVarPunctured E) D.y =
        -cEvalAt (ptL E σ (ZInQ.Metrization2.chi 𝒢 (Φ z))) (abVarPunctured E) D.x := by
  set t : 𝒢.genStalk := (D.tG 𝒢 : 𝒢.genStalk)
  set U := (𝒢.exists_rep t).choose
  set m := (𝒢.exists_rep t).choose_spec.choose
  set s := (𝒢.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  obtain ⟨V, hV, r, hr⟩ := TopCat.Presheaf.exists_germ_eq E.X.left.presheaf D.tE
  have hg := germ_pullbacks_eq 𝒢 D m s hs hV r hr
  obtain ⟨W, hW, iU, iV, hWeq⟩ := TopCat.Presheaf.germ_eq _ _ _ _ _ _ hg
  have h0 : (0 : Fin 1 → ℂ) ∈ {z | ⊤ ≤ gpt 𝒢 (Φ z) ⁻¹ᵁ W} := by
    have h1 : Φ 0 = 1 := (hΦ.2.1 0).mpr Λ.zero_mem
    change ⊤ ≤ gpt 𝒢 (Φ 0) ⁻¹ᵁ W
    rw [h1, top_le_preimage_iff, gpt_one_apply]
    exact hW
  filter_upwards [(hopen W).mem_nhds h0] with z hz hpunct
  have hz' : ⊤ ≤ gpt 𝒢 (Φ z) ⁻¹ᵁ W := hz
  -- the model side
  have e1 : 𝒢.germAlong Φ t z = 𝒢.evalAt (Φ z) U s := rfl
  have e2 : 𝒢.evalAt (Φ z) U s =
      cEvalAt (ptL E σ (ZInQ.Metrization2.chi 𝒢 (Φ z))) V r := by
    rw [evalAt_eq_ev, cEvalAt_ptL_chi_eq_ev, ev_res _ iU.le hz', ev_res _ iV.le hz']
    exact congrArg _ hWeq
  -- the point lies in `V`
  have hqV : ⊤ ≤ (ptL E σ (ZInQ.Metrization2.chi 𝒢 (Φ z))).left ⁻¹ᵁ (V ⊓ abVarPunctured E) := by
    rw [top_le_preimage_iff] at hz' hpunct ⊢
    refine ⟨?_, hpunct⟩
    have := iV.le hz'
    change (gpt 𝒢 (Φ z) ≫ genE 𝒢) (ptc σ) ∈ V at this
    rwa [← ptL_chi_left] at this
  rw [e1, e2]
  exact ev_rep_mul_y D hV r hr _ hqV

end Bridge

end ZInQ.Contrib.CMHeight62
