import ZInQKernel.Contrib.OneProof.QuotientP1.TameInvariants
import ZInQKernel.Contrib.OneProof.QuotientP1.QuotProper

/-!
# p1-quot3, part B: `TameQuotientSmoothRelDim` from the algebra (scratch)

The action of `G` on `Γ(X, q⁻¹ V)`, the algebra structures over `Γ(S, U)`, and the proof of
`HDec.MCRGlue.TameQuotientSmoothRelDim` from the chain's field `RegularSmoothPerfect`.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace HDec.MCRGlue.TameQuotScheme

open QuotientP1Proof.TameQuot

theorem appLE_comp_eq {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (U V W e₁ e₂ e₃) : g.appLE U V e₁ ≫ f.appLE V W e₂ = h.appLE U W e₃ := by
  subst hfg; rw [Scheme.Hom.appLE_comp_appLE]

theorem appLE_comp_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (U V W e₁ e₂ e₃) (x) : (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (h.appLE U W e₃).hom x := by
  rw [← appLE_comp_eq f g h hfg U V W e₁ e₂ e₃]; rfl

section Action

variable {X Z : Scheme.{0}} (q : X ⟶ Z) (W : Z.Opens)

/-- The action of an automorphism `g` with `g ≫ q = q` on `Γ(X, q⁻¹W)`. -/
def sect (g : Aut X) (h : g.asIso.hom ≫ q = q) : Γ(X, q ⁻¹ᵁ W) →+* Γ(X, q ⁻¹ᵁ W) :=
  (g.asIso.hom.appLE (q ⁻¹ᵁ W) (q ⁻¹ᵁ W) (preimage_le_of_comp_eq h W)).hom

theorem sect_congr (g g' : Aut X) (hgg : g = g') (h h') (b) : sect q W g h b = sect q W g' h' b := by
  subst hgg; rfl

theorem sect_one (g : Aut X) (h) (hg : g = 1) (b) : sect q W g h b = b := by
  subst hg
  change ((𝟙 X : X ⟶ X).appLE (q ⁻¹ᵁ W) ((𝟙 X : X ⟶ X) ⁻¹ᵁ (q ⁻¹ᵁ W)) le_rfl).hom b = b
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]
  rfl

theorem sect_mul (x y z : Aut X) (hx hy hz) (hxyz : z = x * y) (b) :
    sect q W z hz b = sect q W y hy (sect q W x hx b) := by
  subst hxyz
  exact (appLE_comp_apply y.asIso.hom x.asIso.hom (x * y).asIso.hom rfl _ _ _ _ _ _ b).symm

/-- The action of `G` on `Γ(X, q⁻¹W)` (`g` acts by `g⁻¹` pulled back, so that it is a left action). -/
def action (G : Subgroup (Aut X)) (hG : ∀ g ∈ G, g.asIso.hom ≫ q = q) :
    MulSemiringAction G Γ(X, q ⁻¹ᵁ W) where
  smul g b := sect q W ((g⁻¹ : G) : Aut X) (hG _ (g⁻¹ : G).2) b
  one_smul b := sect_one q W _ _ (by simp) b
  mul_smul g h b := sect_mul q W _ _ _ _ _ _ (by simp) b
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

theorem action_smul (G : Subgroup (Aut X)) (hG : ∀ g ∈ G, g.asIso.hom ≫ q = q) (g : G) (b) :
    (action q W G hG).smul g b = sect q W ((g⁻¹ : G) : Aut X) (hG _ (g⁻¹ : G).2) b := rfl

end Action

section Setup

variable {X Z S : Scheme.{0}} (q : X ⟶ Z) (fX : X ⟶ S) (fZ : Z ⟶ S) (hw : q ≫ fZ = fX)
  (G : Subgroup (Aut X)) (hGq : ∀ g ∈ G, g.asIso.hom ≫ q = q) (hGX : ∀ g ∈ G, g.asIso.hom ≫ fX = fX)

include hw in
theorem preimage_le (U : S.Opens) (V : Z.Opens) (e : V ≤ fZ ⁻¹ᵁ U) : q ⁻¹ᵁ V ≤ fX ⁻¹ᵁ U := by
  subst hw
  intro x hx
  exact e hx

include hw hGX in
/-- **The algebra at an affine open `V ⊆ Z` over `U ⊆ S`** (continuation-passing form): `Γ(Z, V) → Γ(X, q⁻¹V)`
over `Γ(S, U)` is injective, `G`-equivariant for the action of `G` (by `Γ(S, U)`-algebra maps), with image the
invariants. -/
theorem invariant_setup (hq : IsGQuotient G q) (U : S.Opens) (V : Z.Opens) (hV : IsAffineOpen V)
    (e : V ≤ fZ ⁻¹ᵁ U) (P : Prop)
    (H : letI : Algebra Γ(S, U) Γ(Z, V) := (fZ.appLE U V e).hom.toAlgebra
      letI : Algebra Γ(S, U) Γ(X, q ⁻¹ᵁ V) := (fX.appLE U (q ⁻¹ᵁ V) (preimage_le q fX fZ hw U V e)).hom.toAlgebra
      ∀ (ι : Γ(Z, V) →ₐ[Γ(S, U)] Γ(X, q ⁻¹ᵁ V)) [MulSemiringAction G Γ(X, q ⁻¹ᵁ V)]
        [SMulCommClass G Γ(S, U) Γ(X, q ⁻¹ᵁ V)], Function.Injective ι →
        (∀ (g : G) (a : Γ(Z, V)), g • ι a = ι a) →
        (∀ b : Γ(X, q ⁻¹ᵁ V), (∀ g : G, g • b = b) → ∃ a, ι a = b) → P) : P := by
  obtain ⟨hGq', -, hW⟩ := hq
  letI : Algebra Γ(S, U) Γ(Z, V) := (fZ.appLE U V e).hom.toAlgebra
  letI : Algebra Γ(S, U) Γ(X, q ⁻¹ᵁ V) :=
    (fX.appLE U (q ⁻¹ᵁ V) (preimage_le q fX fZ hw U V e)).hom.toAlgebra
  letI act : MulSemiringAction G Γ(X, q ⁻¹ᵁ V) := action q V G hGq'
  let ι : Γ(Z, V) →ₐ[Γ(S, U)] Γ(X, q ⁻¹ᵁ V) :=
    { (q.app V).hom with
      commutes' := fun r => by
        change (q.app V).hom ((fZ.appLE U V e).hom r) = (fX.appLE U (q ⁻¹ᵁ V) _).hom r
        rw [Scheme.Hom.app_eq_appLE]
        exact appLE_comp_apply q fZ fX hw _ _ _ _ _ _ r }
  have hsmul : ∀ (g : G) (b : Γ(X, q ⁻¹ᵁ V)),
      g • b = sect q V ((g⁻¹ : G) : Aut X) (hGq' _ (g⁻¹ : G).2) b := fun _ _ => rfl
  have hcomm : SMulCommClass G Γ(S, U) Γ(X, q ⁻¹ᵁ V) := ⟨fun g r b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hsmul g (algebraMap _ _ r)]
    congr 1
    exact appLE_comp_apply _ fX fX (hGX _ (g⁻¹ : G).2) _ _ _ _ _ _ r⟩
  refine H ι (by exact (hW V hV).1) (fun g a => ?_) (fun b hb => ?_)
  · rw [hsmul]
    change (sect q V _ _) ((q.app V).hom a) = (q.app V).hom a
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_comp_apply _ q q (hGq' _ (g⁻¹ : G).2) _ _ _ _ _ _ a
  · have hmem : b ∈ Set.range (q.app V) := by
      rw [(hW V hV).2]
      intro g hg
      have := hb (⟨g, hg⟩ : G)⁻¹
      rw [hsmul] at this
      have h2 : sect q V g (hGq' g hg) b = b := by
        rw [sect_congr q V g (((⟨g, hg⟩ : G)⁻¹⁻¹ : G) : Aut X) (by rw [inv_inv]) _ (hGq' _ (((⟨g, hg⟩ : G)⁻¹⁻¹ : G)).2)]
        exact this
      exact h2
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha⟩

end Setup

end HDec.MCRGlue.TameQuotScheme
