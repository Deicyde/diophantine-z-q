import Mathlib

namespace ZInQ.GRIsogDeg

open AlgebraicGeometry CategoryTheory Limits

universe u

/-- Points of `X` over a point `Spec L → Spec R → Y` factoring through `u : Spec R ⟶ Y`, for `f` finite,
are the ring maps `Γ(f⁻¹ u) → L` over `Γ(Spec R) → L`. -/
theorem points_equiv_ringHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {R : CommRingCat.{u}}
    (u : Spec R ⟶ Y) {L : Type u} [Field L] (φ : R ⟶ CommRingCat.of L) :
    Nonempty ({x : Spec (.of L) ⟶ X // x ≫ f = Spec.map φ ≫ u} ≃
      {ψ : Γ(pullback f u, ⊤) →+* L //
        ψ.comp (pullback.snd f u).appTop.hom = ((Scheme.ΓSpecIso R).hom ≫ φ).hom}) := by
  let f' := pullback.snd f u
  haveI : IsAffine (pullback f u) := isAffine_of_isAffineHom f'
  let toP : {x : Spec (.of L) ⟶ X // x ≫ f = Spec.map φ ≫ u} →
      {x' : Spec (.of L) ⟶ pullback f u // x' ≫ f' = Spec.map φ} := fun x =>
    ⟨pullback.lift x.1 (Spec.map φ) x.2, pullback.lift_snd _ _ _⟩
  have htoP : Function.Bijective toP := by
    refine ⟨fun a b h => Subtype.ext ?_, fun x' => ⟨⟨x'.1 ≫ pullback.fst f u, ?_⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun x' => x'.1 ≫ pullback.fst f u) h
      simpa [toP] using this
    · rw [Category.assoc, pullback.condition, ← Category.assoc, x'.2]
    · apply pullback.hom_ext
      · simp [toP]
      · simpa [toP] using x'.2.symm
  let toR : {x' : Spec (.of L) ⟶ pullback f u // x' ≫ f' = Spec.map φ} →
      {ψ : Γ(pullback f u, ⊤) →+* L //
        ψ.comp f'.appTop.hom = ((Scheme.ΓSpecIso R).hom ≫ φ).hom} := fun x' =>
    ⟨(x'.1.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom, by
      have h2 : f'.appTop ≫ x'.1.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom =
          (Scheme.ΓSpecIso R).hom ≫ φ := by
        rw [← Category.assoc, ← Scheme.Hom.comp_appTop, x'.2, Scheme.ΓSpecIso_naturality]
      exact congrArg CommRingCat.Hom.hom h2⟩
  have htoR : Function.Bijective toR := by
    refine ⟨fun a b h => Subtype.ext ?_, fun ψ => ?_⟩
    · have h' : a.1.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom =
          b.1.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom :=
        CommRingCat.hom_ext (congrArg Subtype.val h)
      exact ext_of_isAffine ((cancel_mono _).mp h')
    · let x' : Spec (.of L) ⟶ pullback f u :=
        Spec.map (CommRingCat.ofHom ψ.1) ≫ (pullback f u).isoSpec.inv
      have hx' : x'.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom = CommRingCat.ofHom ψ.1 := by
        have e1 : (pullback f u).isoSpec.hom.appTop ≫ x'.appTop =
            (Spec.map (CommRingCat.ofHom ψ.1)).appTop := by
          rw [← Scheme.Hom.comp_appTop]; simp [x']
        have e2 : (pullback f u).isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(pullback f u, ⊤)).hom :=
          Scheme.toSpecΓ_appTop _
        rw [e2] at e1
        rw [← cancel_epi (Scheme.ΓSpecIso Γ(pullback f u, ⊤)).hom, ← Category.assoc, e1,
          Scheme.ΓSpecIso_naturality]
        rfl
      have hcomp : x' ≫ f' = Spec.map φ := by
        apply ext_of_isAffine
        rw [← cancel_mono (Scheme.ΓSpecIso (.of L)).hom, Scheme.Hom.comp_appTop, Category.assoc, hx',
          Scheme.ΓSpecIso_naturality]
        ext r
        exact congrArg (fun g => g r) ψ.2
      exact ⟨⟨x', hcomp⟩, Subtype.ext (congrArg CommRingCat.Hom.hom hx')⟩
  exact ⟨(Equiv.ofBijective _ htoP).trans (Equiv.ofBijective _ htoR)⟩

end ZInQ.GRIsogDeg
