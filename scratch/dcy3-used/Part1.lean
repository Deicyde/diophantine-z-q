import ZInQKernel.Contrib.OneProof.RayClassShimura

set_option linter.all false

noncomputable section

namespace DCY3Used

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

open scoped IsMulCommutative in
/-- **Every idele `s` of `K` is `[s, K]` for some `σ ∈ Aut(ℂ)`** (any `κ`): represent the absolute Artin
symbol of `s` by `g ∈ Gal(Kˢ/K)` and extend `g` to `ℂ` (Steinitz, `T5Glue.exists_ringEquiv_extend`). -/
theorem exists_sigma_artinCondC (κ : K →+* ℂ) (s : IdeleGroup (𝓞 K) K) :
    ∃ σ : ℂ ≃+* ℂ, ArtinCondC κ σ s := by
  letI : Algebra K ℂ := κ.toAlgebra
  let e : SeparableClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  have he : (e : SeparableClosure K →+* ℂ).comp (algebraMap K (SeparableClosure K)) = κ := by
    ext k; exact e.commutes k
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((globalClassFormation K).absoluteArtinMap
      (globalGroundEquiv K (Additive.ofMul (QuotientGroup.mk s : IdeleClassGroup (𝓞 K) K)))).toMul
  have hg' := congrArg Additive.ofMul hg
  rw [ofMul_toMul] at hg'
  obtain ⟨σ, hσ⟩ := T5Glue.exists_ringEquiv_extend (e : SeparableClosure K →+* ℂ) g.toRingEquiv
  refine ⟨σ, ?_⟩
  intro L _ _ _ _ j hj x
  obtain ⟨ι, hι⟩ := exists_iota κ (e : SeparableClosure K →+* ℂ) he L j hj
  have h1 := of_ideleClassArtinMap K L ι (QuotientGroup.mk s)
  have h0 := globalArtinMap_eq_of_mk_eq_absoluteArtinMap K L ι g hg'
  have h3 : Abelianization.of (ideleClassArtinMap K L (QuotientGroup.mk s)) =
      Abelianization.of (ι.restrictNormalHom g) := by
    rw [h1, h0, toMul_ofMul]
  have h2 : ideleClassArtinMap K L (QuotientGroup.mk s) = ι.restrictNormalHom g :=
    (Abelianization.equivOfComm (H := Gal(L/K))).injective h3
  rw [h2, ← hι, ← hι, AlgHom.restrictNormalHom_commutes]
  exact hσ (ι x)

/-- `σ` does not move the underlying point of a `ℂ`-point. -/
theorem ptC_galPt {Y : Over (Spec (CommRingCat.of ℚ))} (σ : ℂ ≃+* ℂ) (y : fieldPt ℂ ⟶ Y) :
    ShimuraSplit.ptC (galPt σ y).left = ShimuraSplit.ptC y.left := by
  unfold galPt ShimuraSplit.ptC
  rw [Over.comp_left, fieldMap_left, specToEquivOfField_comp]

/-- The upper half plane is connected. -/
example : ConnectedSpace UpperHalfPlane := inferInstance

end DCY3Used
