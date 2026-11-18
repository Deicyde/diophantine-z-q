import ToricBaseChange.G3AssemblyV001

/-!
# From torsion-kernel triviality of the comparison to the torus kernel condition

Abstract setting of `toricRank_le_of_comparison`: `h : S' → S`, a group model `N/S`, `G = N ×_S S'`,
a homomorphism `u : G → N'` over `S'`, the special-fibre data `s : Spec k → S`, `σ' : Spec Ω → S'`,
`jb : k̄ → Ω`, `hsq`, an open subgroup `inc : U → N ×_S k` with a torus `e` over `k̄` (injective).
If every `m`-torsion `T`-point of `G` killed by `u` is trivial (`htors`, for all `T` over `S'`), then
the special-fibre comparison kills no nontrivial `m`-torsion point of the transported torus
(`torus_kernel_of_torsion_kernel`). The torus point is transposed along `Over.map σ' ⊣ Over.pullback σ'`
(a group isomorphism on points, `adjMulEquiv`) to a `Spec Ω`-point of `G` over `S'`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ToricBaseChange.ActualKernel

section Adjunction

variable {S1 S2 : Scheme.{0}} (g : S1 ⟶ S2)

theorem adj_homEquiv_mul (X : Over S1) (Y : Over S2) [GrpObj Y] (p q : (Over.map g).obj X ⟶ Y) :
    (Over.mapPullbackAdj g).homEquiv X Y (p * q) =
      (Over.mapPullbackAdj g).homEquiv X Y p * (Over.mapPullbackAdj g).homEquiv X Y q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- The adjunction `Over.map g ⊣ Over.pullback g` on points, as a group isomorphism. -/
def adjMulEquiv (X : Over S1) (Y : Over S2) [GrpObj Y] :
    ((Over.map g).obj X ⟶ Y) ≃* (X ⟶ (Over.pullback g).obj Y) :=
  { (Over.mapPullbackAdj g).homEquiv X Y with map_mul' := adj_homEquiv_mul g X Y }

theorem adjMulEquiv_symm_comp (X : Over S1) (Y Y' : Over S2) [GrpObj Y] [GrpObj Y']
    (w : X ⟶ (Over.pullback g).obj Y) (u : Y ⟶ Y') :
    (adjMulEquiv g X Y').symm (w ≫ (Over.pullback g).map u) = (adjMulEquiv g X Y).symm w ≫ u :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

end Adjunction

theorem torus_kernel_of_torsion_kernel {S S' : Scheme.{0}} (h : S' ⟶ S)
    (N : Over S) [GrpObj N] (N' : Over S') [GrpObj N'] (u : Comparison.bc h N ⟶ N') [IsMonHom u]
    (m : ℕ)
    (htors : ∀ (T : Over S') (w : T ⟶ Comparison.bc h N), w ^ m = 1 → w ≫ u = 1 → w = 1)
    {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ S)
    {Ω : Type} [Field Ω] (jb : AlgebraicClosure k →+* Ω)
    (σ' : Spec (CommRingCat.of Ω) ⟶ S') (hsq : σ' ≫ h = sφ (φι jb) ≫ s)
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (inc : U ⟶ (Over.pullback s).obj N)
    [IsOpenImmersion inc.left] [IsMonHom inc] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      letI := algK (algebraMap k (AlgebraicClosure k)) R
      (Fin r → Rˣ) →* (SpecPt k R ⟶ U))
    (he_inj : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R))
    (t : Fin r → Ωˣ) (ht : t ^ m = 1)
    (hψ : torusΩ jb U r e Ω t ≫
      Comparison.specialComparison h s σ' (sφ (φι jb)) hsq N N' u U inc = 1) :
    t = 1 := by
  haveI hiso : IsMonHom (Comparison.specialIso h s σ' (sφ (φι jb)) hsq N).hom :=
    Comparison.isMonHom_specialIso _ _ _ _ hsq N
  have hx : torusΩ jb U r e Ω t ^ m = 1 := by
    rw [← map_pow, ht, map_one]
  have hwu : (torusΩ jb U r e Ω t ≫ (Over.pullback (sφ (φι jb))).map inc ≫
      (Comparison.specialIso h s σ' (sφ (φι jb)) hsq N).hom) ≫ (Over.pullback σ').map u = 1 := by
    simp only [Category.assoc]
    exact hψ
  have hwm : (torusΩ jb U r e Ω t ≫ (Over.pullback (sφ (φι jb))).map inc ≫
      (Comparison.specialIso h s σ' (sφ (φι jb)) hsq N).hom) ^ m = 1 := by
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hwb1 : (adjMulEquiv σ' (SpecPt Ω Ω) (Comparison.bc h N)).symm
      (torusΩ jb U r e Ω t ≫ (Over.pullback (sφ (φι jb))).map inc ≫
        (Comparison.specialIso h s σ' (sφ (φι jb)) hsq N).hom) = 1 := by
    apply htors
    · rw [← map_pow, hwm, map_one]
    · rw [← adjMulEquiv_symm_comp, hwu, map_one]
  have hw1 : torusΩ jb U r e Ω t ≫ (Over.pullback (sφ (φι jb))).map inc ≫
      (Comparison.specialIso h s σ' (sφ (φι jb)) hsq N).hom = 1 := by
    have := congrArg (adjMulEquiv σ' (SpecPt Ω Ω) (Comparison.bc h N)) hwb1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have hx1 : torusΩ jb U r e Ω t ≫ (Over.pullback (sφ (φι jb))).map inc = 1 := by
    have h2 := congrArg (· ≫ (Comparison.specialIso h s σ' (sφ (φι jb)) hsq N).inv) hw1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, MonObj.one_comp] at h2
    exact h2
  haveI : Mono inc := Over.mono_of_mono_left inc
  have hx2 : torusΩ jb U r e Ω t = 1 := by
    apply (cancel_mono ((Over.pullback (sφ (φι jb))).map inc)).mp
    rw [hx1, MonObj.one_comp]
  apply @he_inj Ω _ (algBar jb Ω)
  rw [map_one]
  have h3 := congrArg (Φ (φι jb) U Ω) hx2
  simp only [torusΩ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply, map_one] at h3
  exact h3

end ToricBaseChange.ActualKernel
