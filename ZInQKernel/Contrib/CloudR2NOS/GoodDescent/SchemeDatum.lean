/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New actual henselization-neighbourhood scheme descent datum. All overlap
morphisms, naturality, identity and cocycle are constructed from the given
ORIGINAL generic-fibre cartesian identification and the pointed-etale
special-fibre geometry. No hdesc, effective quotient, properness or Neron
model-existence theorem is an input to this datum construction.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.OverlapTransport

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.GenericModel

variable {X U S : Scheme.{u}} {f : X ⟶ U} {p : U ⟶ S} {V : S.Opens}
  (M : GenericModel f p V)

/-- The comparison's genericity is a consequence of the constructed base
    morphism, not an extra geometric assumption. -/
theorem transportMap_mem_generic_test [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) {T T' : Scheme.{u}}
    (x : T ⟶ X) (v : T ⟶ U) (h : (x ≫ f) ≫ p = v ≫ p)
    (t : T' ⟶ T) (hx : ∀ a : T', (t ≫ x) a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V)) :
    ∀ a : T', (t ≫ M.transportMap s hV x v h) a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V) := by
  have he : (M.transportMap s hV x v h ≫ f) ≫ p = (x ≫ f) ≫ p :=
    (congrArg (· ≫ p) (M.transportMap_base s hV x v h)).trans h.symm
  intro a
  have ha := congrArg (fun q : T ⟶ S => q (t a)) he
  simp only [Scheme.Hom.comp_apply] at ha
  change p (f ((M.transportMap s hV x v h) (t a))) ∈ V
  rw [ha]
  exact hx a

private theorem genericMap_congr {T : Scheme.{u}} {a b : T ⟶ X}
    (he : a = b) (v : T ⟶ U)
    (ha : (a ≫ f) ≫ p = v ≫ p) (hb : (b ≫ f) ≫ p = v ≫ p)
    (hga : ∀ t : T, a t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V))
    (hgb : ∀ t : T, b t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V)) :
    M.genericMap a v ha hga = M.genericMap b v hb hgb := by
  cases he
  rfl

/-- The global triple-overlap cocycle. The common generic coordinates are
    retained, and the triple diagonal is covered using the *whole* special
    fibre. This does not invoke an assumed effective descent datum. -/
theorem transportMap_cocycle [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) {T : Scheme.{u}}
    (x : T ⟶ X) (v₂ v₃ : T ⟶ U)
    (h₂ : (x ≫ f) ≫ p = v₂ ≫ p) (h₃ : (x ≫ f) ≫ p = v₃ ≫ p)
    (h₂₃ : (M.transportMap s hV x v₂ h₂ ≫ f) ≫ p = v₃ ≫ p) :
    M.transportMap s hV (M.transportMap s hV x v₂ h₂) v₃ h₂₃ =
      M.transportMap s hV x v₃ h₃ := by
  let y := M.transportMap s hV x v₂ h₂
  have hybase : y ≫ f = v₂ := M.transportMap_base s hV x v₂ h₂
  let D₁₂ := equalityOpen p (x ≫ f) v₂ h₂
  let D₂₃ := equalityOpen p v₂ v₃ (h₂.symm.trans h₃)
  let D := D₁₂ ⊓ D₂₃
  let G := ((x ≫ f) ≫ p) ⁻¹ᵁ V
  have c₁₂ : D₁₂ ⊔ G = ⊤ := equality_sup_generic_eq_top p s V hV (x ≫ f) v₂ h₂
  have c₂₃ : D₂₃ ⊔ G = ⊤ := by
    have he := equality_sup_generic_eq_top p s V hV v₂ v₃ (h₂.symm.trans h₃)
    have hG : (v₂ ≫ p) ⁻¹ᵁ V = G := congrArg (fun a : T ⟶ S => a ⁻¹ᵁ V) h₂.symm
    rwa [hG] at he
  have c : D ⊔ G = ⊤ := by
    dsimp only [D]
    rw [sup_inf_right, c₁₂, c₂₃]
    simp
  apply hom_ext_two c
  · let r₁₂ : D.toScheme ⟶ D₁₂.toScheme := T.homOfLE inf_le_left
    let r₂₃ : D.toScheme ⟶ D₂₃.toScheme := T.homOfLE inf_le_right
    have he₁₂ : (D.ι ≫ x) ≫ f = D.ι ≫ v₂ := by
      have hr : r₁₂ ≫ D₁₂.ι = D.ι := T.homOfLE_ι inf_le_left
      have he := congrArg (r₁₂ ≫ ·) (equalityOpen_eq p (x ≫ f) v₂ h₂)
      change r₁₂ ≫ D₁₂.ι ≫ (x ≫ f) = r₁₂ ≫ D₁₂.ι ≫ v₂ at he
      simpa only [Category.assoc, reassoc_of% hr] using he
    have he₂₃ : D.ι ≫ v₂ = D.ι ≫ v₃ := by
      have hr : r₂₃ ≫ D₂₃.ι = D.ι := T.homOfLE_ι inf_le_right
      have he := congrArg (r₂₃ ≫ ·) (equalityOpen_eq p v₂ v₃ (h₂.symm.trans h₃))
      change r₂₃ ≫ D₂₃.ι ≫ v₂ = r₂₃ ≫ D₂₃.ι ≫ v₃ at he
      simpa only [reassoc_of% hr] using he
    have hey : D.ι ≫ y = D.ι ≫ x := M.transportMap_on_equal s hV x v₂ h₂ D.ι he₁₂
    have he₁₃ : (D.ι ≫ x) ≫ f = D.ι ≫ v₃ := he₁₂.trans he₂₃
    have he' : (D.ι ≫ y) ≫ f = D.ι ≫ v₃ := by rw [hey]; exact he₁₃
    calc
      D.ι ≫ M.transportMap s hV y v₃ h₂₃ = D.ι ≫ y :=
        M.transportMap_on_equal s hV y v₃ h₂₃ D.ι he'
      _ = D.ι ≫ x := hey
      _ = D.ι ≫ M.transportMap s hV x v₃ h₃ :=
        (M.transportMap_on_equal s hV x v₃ h₃ D.ι he₁₃).symm
  · let x₀ := G.ι ≫ x
    let u₂ := G.ι ≫ v₂
    let u₃ := G.ι ≫ v₃
    have hx : ∀ a, x₀ a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V) := by
      intro a
      change p (f (x a.1)) ∈ V
      exact a.2
    have h₂g : (x₀ ≫ f) ≫ p = u₂ ≫ p := by
      simpa only [x₀, u₂, Category.assoc] using congrArg (G.ι ≫ ·) h₂
    have h₃g : (x₀ ≫ f) ≫ p = u₃ ≫ p := by
      simpa only [x₀, u₃, Category.assoc] using congrArg (G.ι ≫ ·) h₃
    have hy : ∀ a, (G.ι ≫ y) a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V) :=
      M.transportMap_mem_generic_test s hV x v₂ h₂ G.ι hx
    have h₂₃g : ((G.ι ≫ y) ≫ f) ≫ p = u₃ ≫ p := by
      simpa only [u₃, Category.assoc] using congrArg (G.ι ≫ ·) h₂₃
    have hey : G.ι ≫ y = M.genericMap x₀ u₂ h₂g hx :=
      M.transportMap_on_generic s hV x v₂ h₂ G.ι hx h₂g
    have hg₂ := M.genericMap_mem x₀ u₂ h₂g hx
    have hg₂₃ : (M.genericMap x₀ u₂ h₂g hx ≫ f) ≫ p = u₃ ≫ p := by
      rw [← hey]
      exact h₂₃g
    have hec := M.genericMap_cocycle x₀ u₂ u₃ h₂g h₃g hx hg₂ hg₂₃
      (M.genericMap_mem _ _ hg₂₃ hg₂) (M.genericMap_mem x₀ u₃ h₃g hx)
    calc
      G.ι ≫ M.transportMap s hV y v₃ h₂₃ = M.genericMap (G.ι ≫ y) u₃ h₂₃g hy :=
        M.transportMap_on_generic s hV y v₃ h₂₃ G.ι hy h₂₃g
      _ = M.genericMap (M.genericMap x₀ u₂ h₂g hx) u₃ hg₂₃ hg₂ :=
        M.genericMap_congr hey u₃ h₂₃g hg₂₃ hy hg₂
      _ = M.genericMap x₀ u₃ h₃g hx := hec
      _ = G.ι ≫ M.transportMap s hV x v₃ h₃ :=
        (M.transportMap_on_generic s hV x v₃ h₃ G.ι hx h₃g).symm

/-- An actual datum of the already published, universe-polymorphic
    `CategoryTheory.Over.DescentDatum` type. It is CONSTRUCTED from the
    original generic model and special-fibre geometry; it is not an input. -/
def schemeDatum [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) : Over.DescentDatum p (Over.mk f) where
  transport u₁ u₂ h x := by
    have hx : x.left ≫ f = u₁ := by simpa only [Over.mk_hom] using Over.w x
    exact Over.homMk (M.transportMap s hV x.left u₂ ((congrArg (· ≫ p) hx).trans h))
      (M.transportMap_base s hV x.left u₂ _)
  transport_homMk_comp t u₁ u₂ h x := by
    apply Over.OverMorphism.ext
    change M.transportMap s hV (t ≫ x.left) (t ≫ u₂) _ =
      t ≫ M.transportMap s hV x.left u₂ _
    exact M.transportMap_natural s hV x.left u₂ _ t _
  transport_self v x := by
    apply Over.OverMorphism.ext
    exact M.transportMap_identity s hV x.left v _ (by simpa only [Over.mk_hom] using Over.w x)
  transport_transport u₁ u₂ u₃ h₁₂ h₂₃ x := by
    apply Over.OverMorphism.ext
    change M.transportMap s hV (M.transportMap s hV x.left u₂ _) u₃ _ =
      M.transportMap s hV x.left u₃ _
    exact M.transportMap_cocycle s hV x.left u₂ u₃ _ _ _

#print axioms transportMap_cocycle
#print axioms schemeDatum

end ZInQ.Contrib.CloudR2NOS.GoodDescent.GenericModel
