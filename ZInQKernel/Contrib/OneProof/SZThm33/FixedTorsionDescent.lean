import ZInQKernel.Contrib.OneProof.SZThm33.InertiaFieldFixed
import ZInQKernel.Contrib.OneProof.UnipotentForward
import ZInQKernel.Contrib.OneProof.MulEtale

/-!
# Inertia-fixed torsion descends to the strict henselization field
-/

noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.AbVarBC

namespace SZRaynaud

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (w : ValuationSubring Ω) (A : PkgI3.AbVar K)

/-- Prime-to-characteristic torsion fixed by the original inertia
group is rational over the fraction field of the strict henselization. -/
theorem exists_torsion_point_over_inertiaField (m : ℕ) (hm : (m : K) ≠ 0)
    (x : A.Pt Ω) (hx : x ^ m = 1)
    (hfix : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → A.galAct σ x = x) :
    ∃ y : A.Pt (GapSHPair.inertiaField (K := K) w),
      y ^ m = 1 ∧ extPt A (GapSHPair.inertiaField (K := K) w).val y = x := by
  let S := separableClosure K Ω
  let E := GapSHPair.inertiaField (K := K) w
  obtain ⟨u, hu⟩ := UnipotentForward.torsion_from_sepClosure
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof Ω A m hm x hx
  let jS := Spec.map (CommRingCat.ofHom (algebraMap S Ω))
  let u' : Spec (.of S) ⟶ A.X.left := u.left
  let x' : Spec (.of Ω) ⟶ A.X.left := x.left
  have hu' : jS ≫ u' = x' := congrArg Over.Hom.left hu
  let z := u' (IsLocalRing.closedPoint S)
  let i := A.X.left.affineCover.idx z
  let Y := A.X.left.affineCover.X i
  let f : Y ⟶ A.X.left := A.X.left.affineCover.f i
  let v : Spec (.of S) ⟶ Y := IsOpenImmersion.lift f u' (by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a (IsLocalRing.closedPoint S)]
    exact A.X.left.affineCover.covers z)
  have hv : v ≫ f = u' := IsOpenImmersion.lift_fac _ _ _
  let e := Y.isoSpec
  let a := Spec.preimage (v ≫ e.hom)
  have ha : Spec.map a ≫ e.inv ≫ f = u' := by
    rw [show Spec.map a = v ≫ e.hom from Spec.map_preimage _, Category.assoc,
      Iso.hom_inv_id_assoc, hv]
  let b := CommRingCat.ofHom ((algebraMap S Ω).comp a.hom)
  have hb : Spec.map b ≫ e.inv ≫ f = x' := by
    change Spec.map (a ≫ CommRingCat.ofHom (algebraMap S Ω)) ≫ e.inv ≫ f = x'
    rw [Spec.map_comp, Category.assoc, ha, hu']
  have hbfix (c : Γ(Y, ⊤)) (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
      σ (b.hom c) = b.hom c := by
    let g := CommRingCat.ofHom (σ : Ω →+* Ω)
    have hxg : Spec.map g ≫ x' = x' := congrArg Over.Hom.left (hfix σ hσ)
    have hbg : b ≫ g = b := by
      apply Spec.map_injective
      apply (cancel_mono (e.inv ≫ f)).mp
      rw [Spec.map_comp, Category.assoc, hb, hxg]
    exact congrArg (fun d : Γ(Y, ⊤) ⟶ CommRingCat.of Ω => d.hom c) hbg
  have hbmem (c : Γ(Y, ⊤)) : b.hom c ∈ E := by
    apply mem_inertiaField_of_fixed_of_isSeparable w
    · exact (mem_separableClosure_iff.mp (a.hom c).2)
    · exact hbfix c
  let bE : Γ(Y, ⊤) →+* E := b.hom.codRestrict E.toSubring hbmem
  let jE := Spec.map (CommRingCat.ofHom (algebraMap E Ω))
  let y : Spec (.of E) ⟶ A.X.left :=
    Spec.map (CommRingCat.ofHom bE) ≫ e.inv ≫ f
  have hy : jE ≫ y = x' := by
    dsimp [y]
    rw [← Category.assoc jE, ← Spec.map_comp]
    exact hb
  have hyK : y ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
    have : Epi jE := epi_spec_map_field _
    apply (cancel_epi jE).mp
    have hxw : x' ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := x.w
    rw [← Category.assoc, hy, hxw, ← Spec.map_comp]
    rfl
  let yE : A.Pt E := Over.homMk y hyK
  have hyE : extPt A E.val yE = x := by
    apply Over.OverMorphism.ext
    exact hy
  refine ⟨yE, ?_, hyE⟩
  apply extPt_injective A E.val
  rw [map_pow, hyE, hx, map_one]

#print axioms exists_torsion_point_over_inertiaField

end SZRaynaud
