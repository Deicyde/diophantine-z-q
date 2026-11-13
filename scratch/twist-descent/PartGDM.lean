/-! # twist-descent, part GDM: kf-glue's `GaloisDescentMor` proved

kf-glue stated (unused) the standard Galois descent of morphisms along `ℚ̄/L` as
`GaloisDescentMor`. It follows from `TwistDescentHFD.hfd` with `K = L`, `e₁L = e₂L = id`, and
`X ×_{L,id} L ≅ X`; uniqueness because `X_{ℚ̄} → X` is an epimorphism. -/

section TwistDescentGDM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open TwistDescentXC TwistDescentHFD

namespace G0ModField.KernelField

open G0ModField

/-- **`GaloisDescentMor` holds** (kf-glue's statement, verbatim; no hypotheses). -/
theorem galoisDescentMor : GaloisDescentMor := by
  intro L _ X Y _ _ _ φ hφ
  have h₀ : sp (algebraMap L Qbar) = sp (algebraMap L Qbar) ≫ sp (RingHom.id L) :=
    sp_eq _ _ _ fun _ => rfl
  have hφs : φ.left ≫ pullback.snd Y.hom (sp (algebraMap L Qbar)) =
      pullback.snd X.hom (sp (algebraMap L Qbar)) := Over.w φ
  have hinv : ∀ k : Qbar ≃ₐ[ℚ] Qbar, k ∈ L.fixingSubgroup →
      ∀ (k₁ : sp (algebraMap L Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (algebraMap L Qbar))
        (k₂ : sp (algebraMap L Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (algebraMap L Qbar)),
        xc X (sp (k : Qbar →+* Qbar)) k₁ ≫ φ.left = φ.left ≫ xc Y (sp (k : Qbar →+* Qbar)) k₂ := by
    intro k hk k₁ k₂
    have := G4Conj.conj_cmp X Y (G4WeilRes.specGal k) k₁ k₁ φ
    rw [hφ k hk k₁] at this
    exact this.symm
  obtain ⟨φL, hφL⟩ := hfd X Y (RingHom.id L) (RingHom.id L) (algebraMap L Qbar)
    (algebraMap L Qbar) h₀ h₀ (fun _ => rfl) (fun _ => rfl) φ.left hφs hinv
  have hepi : Epi (xc X (sp (algebraMap L Qbar)) h₀) := xc_epi X (RingHom.id L) _ h₀
  have hφLs : φL ≫ pullback.snd Y.hom (sp (RingHom.id L)) =
      pullback.snd X.hom (sp (RingHom.id L)) := by
    rw [← cancel_epi (xc X (sp (algebraMap L Qbar)) h₀), ← Category.assoc, hφL,
      Category.assoc, xc_snd, ← Category.assoc, hφs, xc_snd]
  have hid : sp (RingHom.id L) = 𝟙 _ := sp_id_eq _ fun _ => rfl
  let j : X.left ⟶ pullback X.hom (sp (RingHom.id L)) :=
    pullback.lift (𝟙 _) X.hom (by rw [Category.id_comp, hid, Category.comp_id])
  let ψ0 : X.left ⟶ Y.left := j ≫ φL ≫ pullback.fst _ _
  have hψw : ψ0 ≫ Y.hom = X.hom := by
    simp only [ψ0, Category.assoc]
    rw [pullback.condition, reassoc_of% hφLs]
    simp only [j, pullback.lift_snd_assoc]
    rw [hid, Category.comp_id]
  have hj : pullback.fst X.hom (sp (algebraMap L Qbar)) ≫ j = xc X (sp (algebraMap L Qbar)) h₀ := by
    apply pullback.hom_ext
    · simp [j]
    · simp only [j, Category.assoc, pullback.lift_snd, xc_snd]
      rw [pullback.condition]
  have hex : (Over.pullback (G4WeilRes.specIncl L)).map (Over.homMk ψ0 hψw) = φ := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst, Over.homMk_left]
      show pullback.fst _ _ ≫ j ≫ φL ≫ pullback.fst _ _ = φ.left ≫ pullback.fst _ _
      rw [← Category.assoc, hj, ← Category.assoc, hφL, Category.assoc, xc_fst]
    · simp only [Over.pullback_map_left, pullback.lift_snd]
      exact hφs.symm
  refine ⟨Over.homMk ψ0 hψw, hex, fun ψ' hψ' => ?_⟩
  have hfe : Epi (pullback.fst X.hom (sp (algebraMap L Qbar))) :=
    TwistDescentGD.epi_of_isPullback_field (IsPullback.of_hasPullback X.hom _)
  apply Over.OverMorphism.ext
  apply (cancel_epi (pullback.fst X.hom (sp (algebraMap L Qbar)))).mp
  have e1 := congrArg (fun f => f.left ≫ pullback.fst Y.hom (sp (algebraMap L Qbar)))
    (hψ'.trans hex.symm)
  simp only [Over.pullback_map_left, pullback.lift_fst] at e1
  exact e1

end G0ModField.KernelField

end TwistDescentGDM

#print axioms G0ModField.KernelField.galoisDescentMor
