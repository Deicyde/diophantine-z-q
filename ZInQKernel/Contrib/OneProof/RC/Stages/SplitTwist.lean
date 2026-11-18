import ZInQKernel.Contrib.OneProof.RC.Stages.Kummer
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Defs

/-! The standard twist identification on geometric points, tex 8340–8343. -/

noncomputable section

open scoped WeierstrassCurve
open TauCeti WeierstrassCurve ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Stages

/-- Over the algebraic closure the coordinate change identifies the twist with the curve. -/
def geomTwist (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    (D : ℚ) (s : Qbar) (hs : s ≠ 0) (hsD : s ^ 2 = algebraMap ℚ Qbar D) :
    GeomPoint (qtwist E D) ≃+ GeomPoint E :=
  (AddEquiv.cast (M := fun W : WeierstrassCurve Qbar => W.toAffine.Point)
    (twistVC_smul E h₁ h₃ hs hsD).symm).trans
    (Affine.Point.addEquivVariableChange (E⁄Qbar) (twistVC s))

/-- Coordinates of the geometric twist identification. -/
private theorem geomTwist_some (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    (D : ℚ) (s : Qbar) (hs : s ≠ 0) (hsD : s ^ 2 = algebraMap ℚ Qbar D)
    {x y : Qbar} (hxy : ((qtwist E D)⁄Qbar).toAffine.Nonsingular x y) :
    ∃ h : (E⁄Qbar).toAffine.Nonsingular (s⁻¹ ^ 2 * x) (s⁻¹ ^ 3 * y),
      geomTwist E h₁ h₃ D s hs hsD (.some x y hxy) = .some _ _ h := by
  refine ⟨?_, ?_⟩
  · have hp := (Affine.variableChange_nonsingular (E⁄Qbar) (twistVC s) x y).mpr
      ((twistVC_smul E h₁ h₃ hs hsD).symm ▸ hxy)
    simpa [twistVC, hs] using hp
  · unfold geomTwist
    rw [AddEquiv.trans_apply, AddEquiv.cast_apply, Affine.Point.cast_some,
      Affine.Point.coe_addEquivVariableChange, Affine.Point.equivVariableChange_some]
    · simp [twistVC, hs]
    · exact (twistVC_smul E h₁ h₃ hs hsD).symm

/-- If the automorphism fixes the square root, it commutes with the identification
on every geometric point: the two affine coordinates are rescaled by fixed factors. -/
theorem geomTwist_equivariant (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    (D : ℚ) (s : Qbar) (hs : s ≠ 0) (hsD : s ^ 2 = algebraMap ℚ Qbar D)
    (g : GalQ) (hg : g s = s) (P : GeomPoint (qtwist E D)) :
    geomTwist E h₁ h₃ D s hs hsD (Affine.Point.map g.toAlgHom P) =
      Affine.Point.map (W' := E) g.toAlgHom (geomTwist E h₁ h₃ D s hs hsD P) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · simp only [← Affine.Point.zero_def, map_zero]
  · rw [Affine.Point.map_some]
    have hmap := ((qtwist E D).toAffine.baseChange_nonsingular
      (f := g.toAlgHom) g.injective x y).mpr hxy
    obtain ⟨hgxy, hleft⟩ := geomTwist_some E h₁ h₃ D s hs hsD hmap
    obtain ⟨hxy', hright⟩ := geomTwist_some E h₁ h₃ D s hs hsD hxy
    rw [hleft, hright, Affine.Point.map_some]
    simp only [map_mul, map_pow, map_inv₀, AlgEquiv.coe_toAlgHom, hg]

/-- The same intertwining relation at the Tate module. It transports the row by
the split-twist identification and compares the matrices in transported bases. -/
theorem geomTwist_tate_equivariant (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    (D : ℚ) (s : Qbar) (hs : s ≠ 0) (hsD : s ^ 2 = algebraMap ℚ Qbar D)
    (g : GalQ) (hg : g s = s) (t : TateMod (qtwist E D) 2) :
    TateModule.mapLinearMap (geomTwist E h₁ h₃ D s hs hsD).toAddMonoidHom
        (tateRep (qtwist E D) 2 g t) =
      tateRep E 2 g (TateModule.mapLinearMap (geomTwist E h₁ h₃ D s hs hsD).toAddMonoidHom t) := by
  apply TateModule.ext
  intro n
  apply Subtype.ext
  simp only [TateModule.mapLinearMap_apply, TateModule.proj_map, TateModule.levelMap_apply, coe_proj_tateRep,
    AddEquiv.coe_toAddMonoidHom]
  exact geomTwist_equivariant E h₁ h₃ D s hs hsD g hg _

/-- Two Galois elements which fix the square root and agree on the twist's
Tate module also agree on the untwisted Tate module. -/
theorem geomTwist_tate_action_eq (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    (D : ℚ) (s : Qbar) (hs : s ≠ 0) (hsD : s ^ 2 = algebraMap ℚ Qbar D)
    (g f : GalQ) (hg : g s = s) (hf : f s = s)
    (h : tateRep (qtwist E D) 2 g = tateRep (qtwist E D) 2 f) :
    tateRep E 2 g = tateRep E 2 f := by
  let e := geomTwist E h₁ h₃ D s hs hsD
  have he : e.toAddMonoidHom.comp e.symm.toAddMonoidHom = AddMonoidHom.id _ :=
    AddMonoidHom.ext fun t => e.apply_symm_apply t
  apply LinearMap.ext
  intro t
  let t' := TateModule.map (p := 2) e.symm.toAddMonoidHom t
  have ht : TateModule.mapLinearMap e.toAddMonoidHom t' = t := by
    rw [TateModule.mapLinearMap_apply]
    change ((TateModule.map e.toAddMonoidHom).comp (TateModule.map e.symm.toAddMonoidHom)) t = t
    rw [← TateModule.map_comp, he, TateModule.map_id]
    rfl
  rw [← ht, ← geomTwist_tate_equivariant E h₁ h₃ D s hs hsD g hg,
    ← geomTwist_tate_equivariant E h₁ h₃ D s hs hsD f hf, h]

#print axioms geomTwist_some
#print axioms geomTwist
#print axioms geomTwist_equivariant
#print axioms geomTwist_tate_equivariant
#print axioms geomTwist_tate_action_eq

end ZInQ.Manuscript.RC.Stages
