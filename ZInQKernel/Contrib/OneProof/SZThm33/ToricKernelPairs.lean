import ZInQKernel.Contrib.OneProof.SZThm33.ToricKernelRigidity

/-! Kernel-pair transport for general finite extensions of fields, including
inseparable ones. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.ChevFree DictModels.RaynaudOr SmoothGroup

set_option linter.style.haveILetI false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SZRaynaud

section GeneralAlgebra

variable {k : Type} [Field k] {U : Over (Spec (CommRingCat.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}

theorem kbar_KI_ring (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (L : Type) [CommRing L] (ra rb : AlgebraicClosure k →+* L) (hab : ra.comp (φbar k) = rb.comp (φbar k))
    (u v : Spec (CommRingCat.of L) ⟶ U.left)
    (hu : u ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k))
    (hv : v ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k))
    (hb : Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) = Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k))
    (h : pullback.lift u _ hu ≫ π'.left = pullback.lift v _ hv ≫ π'.left) :
    pullback.lift u _ (hu.trans hb) ≫ π'.left = pullback.lift v _ (hv.trans hb) ≫ π'.left := by
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
  letI := B'.grp
  haveI := hπ
  let Φa := (Over.mapPullbackAdj (sφ (φbar k))).homEquiv (Over.mk (Spec.map (CommRingCat.ofHom ra))) U
  let Φb := (Over.mapPullbackAdj (sφ (φbar k))).homEquiv (Over.mk (Spec.map (CommRingCat.ofHom rb))) U
  let ua : Over.mk (Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k)) ⟶ U := Over.homMk u hu
  let va : Over.mk (Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k)) ⟶ U := Over.homMk v hv
  let ub : Over.mk (Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)) ⟶ U := Over.homMk u (hu.trans hb)
  let vb : Over.mk (Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k)) ⟶ U := Over.homMk v (hv.trans hb)
  -- a-side
  have ha1 : Φa ua ≫ π' = Φa va ≫ π' := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, homEquiv_left, Φa]
    exact h
  have ha2 : Φa (ua⁻¹ * va) ≫ π' = 1 := by
    rw [homEquiv_mul', homEquiv_inv, MonObj.mul_comp, GrpObj.inv_comp, ha1, _root_.inv_mul_cancel]
  letI Ia := ra.toAlgebra
  obtain ⟨t, ht⟩ := (he_ker L (Φa (ua⁻¹ * va))).mp ha2
  have hraw : (e L t).left ≫ pullback.fst U.hom (sφ (φbar k)) = (ua⁻¹ * va).left := by
    rw [ht]
    change (Φa (ua⁻¹ * va)).left ≫ _ = _
    rw [homEquiv_left, pullback.lift_fst]
  -- transfer
  have htr := congrArg Over.Hom.left
    (torusTransport_one_of_commRing π' r e he_nat L ra rb hab t)
  rw [torusTransport_left] at htr
  -- b-side
  have hrawb : (ua⁻¹ * va).left = (ub⁻¹ * vb).left := overMk_inv_mul_left hb u v hu hv
  have hb2 : Φb (ub⁻¹ * vb) ≫ π' = 1 := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, homEquiv_left]
    show pullback.lift (ub⁻¹ * vb).left (Spec.map (CommRingCat.ofHom rb)) (Over.w (ub⁻¹ * vb)) ≫ π'.left = _
    have e1 : pullback.lift (ub⁻¹ * vb).left (Spec.map (CommRingCat.ofHom rb)) (Over.w (ub⁻¹ * vb)) =
        pullback.lift ((e L t).left ≫ pullback.fst U.hom (sφ (φbar k))) (Spec.map (CommRingCat.ofHom rb))
          (by rw [hraw, Over.w (ua⁻¹ * va)]; exact hb) := by
      congr 1; rw [hraw, hrawb]
    rw [e1]
    exact htr
  have hb3 : Φb ub ≫ π' = Φb vb ≫ π' := by
    rw [homEquiv_mul', homEquiv_inv, MonObj.mul_comp, GrpObj.inv_comp] at hb2
    exact (inv_mul_eq_one.mp hb2)
  have := congrArg (fun z => Over.Hom.left z) hb3
  simp only [Φb, Over.comp_left, homEquiv_left] at this
  exact this

end GeneralAlgebra

section FiniteStage

variable {k : Type} [Field k] {U : Over (Spec (CommRingCat.of k))} [GrpObj U]
  {B' : PkgI3.AbVar (AlgebraicClosure k)}
  {k₁ : Type} [Field k₁] [Algebra k k₁] [Algebra k₁ (AlgebraicClosure k)]
  [IsScalarTower k k₁ (AlgebraicClosure k)]

theorem algebra_KI_of_ext_structure
    (π' : (Over.pullback (sφ (φbar k))).obj U ⟶ B'.X)
    (hπ : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      IsMonHom π') (r : ℕ)
    (e : letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U))
    (he_ker : letI := B'.grp; letI : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj
      ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ (Over.pullback (sφ (φbar k))).obj U),
      u ≫ π' = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    (X₁ : Over (Spec (CommRingCat.of k₁))) (π₁ : (Over.pullback (qq k k₁)).obj U ⟶ X₁)
    (c : B'.X.left ⟶ X₁.left) (hc : IsPullback c B'.X.hom X₁.hom (q₂ k k₁))
    (hcompat : π'.left ≫ c = rr U k₁ ≫ π₁.left)
    (L : Type) [CommRing L] (u v : Spec (CommRingCat.of L) ⟶ U.left)
    (a b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k₁))
    (ra rb : AlgebraicClosure k →+* L)
    (hra : Spec.map (CommRingCat.ofHom ra) ≫ q₂ k k₁ = a)
    (hrb : Spec.map (CommRingCat.ofHom rb) ≫ q₂ k k₁ = b)
    (hu : u ≫ U.hom = a ≫ qq k k₁) (hv : v ≫ U.hom = a ≫ qq k k₁) (hb : a ≫ qq k k₁ = b ≫ qq k k₁)
    (h : pullback.lift u a hu ≫ π₁.left = pullback.lift v a hv ≫ π₁.left) :
    pullback.lift u b (hu.trans hb) ≫ π₁.left = pullback.lift v b (hv.trans hb) ≫ π₁.left := by
  have hua : u ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) := by
    rw [hu, ← hra, Category.assoc, q₂_qq]
  have hva : v ≫ U.hom = Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) := by
    rw [hv, ← hra, Category.assoc, q₂_qq]
  have hbb : Spec.map (CommRingCat.ofHom ra) ≫ sφ (φbar k) = Spec.map (CommRingCat.ofHom rb) ≫ sφ (φbar k) := by
    rw [← q₂_qq (k₁ := k₁), ← Category.assoc, hra, hb, ← hrb, Category.assoc]
  have hab : ra.comp (φbar k) = rb.comp (φbar k) := by
    have := hbb
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp] at this
    have := Spec.map_injective this
    exact congrArg CommRingCat.Hom.hom this
  have hlift : ∀ (w : Spec (CommRingCat.of L) ⟶ U.left) (ρ : AlgebraicClosure k →+* L)
      (x : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k₁)) (hρ : Spec.map (CommRingCat.ofHom ρ) ≫ q₂ k k₁ = x)
      (hw : w ≫ U.hom = x ≫ qq k k₁) (hw' : w ≫ U.hom = Spec.map (CommRingCat.ofHom ρ) ≫ sφ (φbar k)),
      pullback.lift w x hw ≫ π₁.left = (pullback.lift w _ hw' ≫ π'.left) ≫ c := by
    intro w ρ x hρ hw hw'
    rw [Category.assoc, hcompat, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp
    · simp [hρ]
  have hst : ∀ (w : Spec (CommRingCat.of L) ⟶ U.left) (ρ : AlgebraicClosure k →+* L)
      (hw' : w ≫ U.hom = Spec.map (CommRingCat.ofHom ρ) ≫ sφ (φbar k)),
      (pullback.lift w _ hw' ≫ π'.left) ≫ B'.X.hom = Spec.map (CommRingCat.ofHom ρ) := by
    intro w ρ hw'
    rw [Category.assoc, Over.w π']
    exact pullback.lift_snd _ _ _
  have hk : pullback.lift u _ hua ≫ π'.left = pullback.lift v _ hva ≫ π'.left := by
    apply hc.hom_ext
    · rw [← hlift u ra a hra hu hua, ← hlift v ra a hra hv hva, h]
    · rw [hst, hst]
  have hk2 := kbar_KI_ring π' hπ r e he_ker he_nat L ra rb hab u v hua hva hbb hk
  rw [hlift u rb b hrb (hu.trans hb) (hua.trans hbb), hlift v rb b hrb (hv.trans hb) (hva.trans hbb), hk2]

end FiniteStage

#print axioms kbar_KI_ring
#print axioms algebra_KI_of_ext_structure

end SZRaynaud
