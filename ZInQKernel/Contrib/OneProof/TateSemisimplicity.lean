import ZInQKernel.Contrib.OneProof.TateRangeComplement
import ZInQKernel.Contrib.OneProof.R16Split

/-! # Faltings semisimplicity from the isogeny bound and the endomorphism algebra -/

noncomputable section
open PkgI3.AbVar
open scoped CategoryTheory.MonObj TensorProduct

namespace ZInQ.Contrib.TateFiniteApproximation

variable {K : Type} [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (A : PkgI3.AbVar K)

private def integralEndAction : End A →+* Module.End ℤ_[ℓ] (A.T ℓ) where
  __ := tateHom ℓ A A
  map_one' := R16Split.homT_one ℓ A
  map_mul' := R16Split.homT_mul ℓ A

/-- The scalar extension of the geometric endomorphism ring acting on the
rational Tate module over any ground field. -/
def rationalEndAction : (ℚ_[ℓ] ⊗[ℤ] End A) →ₐ[ℚ_[ℓ]] Module.End ℚ_[ℓ] (A.V ℓ) :=
  let f := (Module.End.baseChangeHom ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)).toRingHom.comp (integralEndAction ℓ A)
  Algebra.TensorProduct.lift (Algebra.ofId _ _) f.toIntAlgHom (fun r y => Algebra.commutes r (f y))

theorem rationalEndAction_tmul (a : ℚ_[ℓ]) (e : End A) :
    rationalEndAction ℓ A (a ⊗ₜ[ℤ] e) = a • (homT (ℓ := ℓ) e).baseChange ℚ_[ℓ] := by
  change algebraMap _ _ a * (homT (ℓ := ℓ) e).baseChange ℚ_[ℓ] = _
  rw [← Algebra.smul_def]

theorem rationalEndAction_commutes (x : ℚ_[ℓ] ⊗[ℤ] End A) (σ : Field.absoluteGaloisGroup K) :
    Commute (rationalEndAction ℓ A x) (A.galRep ℓ σ) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact hx.add_left hy
  | tmul a f =>
    have he : homT (ℓ := ℓ) f ∘ₗ A.galT σ = A.galT σ ∘ₗ homT f :=
      LinearMap.ext fun t => PkgI3.homT_galT f σ t
    rw [rationalEndAction_tmul]
    change (a • (homT f).baseChange ℚ_[ℓ]) ∘ₗ (A.galT σ).baseChange ℚ_[ℓ] =
      (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ (a • (homT f).baseChange ℚ_[ℓ])
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, he]

/-- Every integral combination of endomorphisms acts on rational Tate space
through the endomorphism algebra over ℚℓ. -/
theorem exists_rationalEndAction (ξ : ℤ_[ℓ] ⊗[ℤ] End A) :
    ∃ r : ℚ_[ℓ] ⊗[ℤ] End A, rationalEndAction ℓ A r = (tateHomZl ℓ A A ξ).baseChange ℚ_[ℓ] := by
  induction ξ using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a+b, by rw [map_add, map_add, LinearMap.baseChange_add, ha, hb]⟩
  | tmul a e =>
    refine ⟨(algebraMap ℤ_[ℓ] ℚ_[ℓ] a) ⊗ₜ[ℤ] e, ?_⟩
    rw [rationalEndAction_tmul, IsScalarTower.algebraMap_smul]
    exact (LinearMap.baseChange_smul _ _).symm

/-- The geometric part of Faltings semisimplicity uses the isogeny bound;
the remaining algebraic requirement is semisimplicity of the scalar extension
of the geometric endomorphism ring. -/
theorem faltingsSemisimple_at_of_endomorphism_algebra [NumberField K]
    [IsSemisimpleRing (ℚ_[ℓ] ⊗[ℤ] End A)]
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (g : ℕ) (height : ℝ) (hdim : A.dim = (g : WithBot ℕ∞))
    (hheight : ZInQ.SemistabAssembly.IsAnStableHeightSS A height) :
    (A.galRep ℓ).IsSemisimpleRepresentation := by
  apply semisimpleRepresentation_of_endomorphism_ranges _ (rationalEndAction ℓ A).toRingHom
    (rationalEndAction_commutes ℓ A)
  intro W
  obtain ⟨ξ, hξ⟩ := exists_endomorphism_with_rational_range A hGR g height hdim hheight W.toSubmodule
    (fun σ _ hw => W.apply_mem_toSubmodule σ hw)
  obtain ⟨r, hr⟩ := exists_rationalEndAction ℓ A ξ
  exact ⟨r, hr ▸ hξ⟩

end ZInQ.Contrib.TateFiniteApproximation
