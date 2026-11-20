import ZInQKernel.Contrib.OneProof.SZThm33.ToricKernelTransport

/-! Prime-to-characteristic torsion extends the torus-kernel transport
criterion from fields to arbitrary commutative rings. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.ChevFree DictModels.RaynaudOr SmoothGroup

set_option linter.style.haveILetI false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 180000
set_option backward.isDefEq.respectTransparency false

namespace SZRaynaud

variable {k : Type} [Field k] {U : Over (Spec (.of k))} [GrpObj U]
  {B : PkgI3.AbVar (AlgebraicClosure k)}

local instance : GrpObj ((Over.pullback (sφ (φbar k))).obj U) := Functor.grpObjObj

variable (π : ((Over.pullback (sφ (φbar k))).obj U) ⟶ B.X) [IsMonHom π] (r : ℕ)
  (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ ((Over.pullback (sφ (φbar k))).obj U)))
  (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S] [Algebra (AlgebraicClosure k) S]
    (f : R →ₐ[(AlgebraicClosure k)] S) (t : Fin r → Rˣ),
    e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)

private abbrev specRingMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom f)

include he_nat in
private theorem torusTransport_field_one (R : Type) [Field R] (ra rb : (AlgebraicClosure k) →+* R)
    (hab : ra.comp (φbar k) = rb.comp (φbar k)) (t : Fin r → Rˣ) :
    torusTransport π r e R ra rb hab t = 1 := by
  apply Over.OverMorphism.ext
  rw [torusTransport_left, ZInQ.ChevFree.torus_kernel_transfer π inferInstance r e he_nat R ra rb hab t]
  rfl

private theorem torusTransport_congr {R : Type} [CommRing R]
    {a b a' b' : AlgebraicClosure k →+* R} (ha : a = a') (hb : b = b')
    (hab : a.comp (φbar k) = b.comp (φbar k)) (hab' : a'.comp (φbar k) = b'.comp (φbar k))
    (t : Fin r → Rˣ)
    (h : (torusTransport π r e R a b hab t).left = (1 : Over.mk (specRingMap b) ⟶ B.X).left) :
    torusTransport π r e R a' b' hab' t = 1 := by
  subst a' b'
  exact Over.OverMorphism.ext h

private theorem exists_invertible_large_integer (K : Type) [Field K] :
    ∃ ℓ : ℕ, 1 < ℓ ∧ IsUnit (ℓ : K) := by
  by_cases h : (2 : K) = 0
  · refine ⟨3, by decide, ?_⟩
    have h' : (3 : K) = 1 := by linear_combination h
    simpa only [Nat.cast_ofNat, h'] using (isUnit_one : IsUnit (1 : K))
  · exact ⟨2, by decide, isUnit_iff_ne_zero.mpr h⟩

include he_nat in
/-- A split torus kernel for the first structure map is a split torus kernel
for the second structure map, including when the test ring has nilpotents. -/
theorem torusTransport_one_of_commRing (R : Type) [CommRing R] (ra rb : (AlgebraicClosure k) →+* R)
    (hab : ra.comp (φbar k) = rb.comp (φbar k)) (t : Fin r → Rˣ) :
    torusTransport π r e R ra rb hab t = 1 := by
  let A := ToricRing R r
  let ra₀ : (AlgebraicClosure k) →+* A := (algebraMap R A).comp ra
  let rb₀ : (AlgebraicClosure k) →+* A := (algebraMap R A).comp rb
  have hab₀ : ra₀.comp (φbar k) = rb₀.comp (φbar k) := by
    simp only [ra₀, rb₀, RingHom.comp_assoc, hab]
  let u : Fin r → Aˣ := toricUniversal r
  let p : Over.mk (specRingMap rb₀) ⟶ B.X := torusTransport π r e A ra₀ rb₀ hab₀ u
  let f := p.left
  let g := (1 : Over.mk (specRingMap rb₀) ⟶ B.X).left
  have he : f ≫ B.X.hom = g ≫ B.X.hom :=
    (Over.w p).trans (Over.w (1 : Over.mk (specRingMap rb₀) ⟶ B.X)).symm
  have hre (D : Type) [CommRing D] (c : A →+* D) :
      (c.comp ra₀).comp (φbar k) = (c.comp rb₀).comp (φbar k) := by
    exact RingHom.ext fun x => congrArg c (DFunLike.congr_fun hab₀ x)
  have hn (D : Type) [CommRing D] (c : A →+* D) :
      specRingMap c ≫ f = (torusTransport π r e D (c.comp ra₀) (c.comp rb₀) (hre D c)
        (fun j => Units.map c (u j))).left :=
    torusTransport_natural_left π r e he_nat c ra₀ rb₀ hab₀ u (hre D c)
  have hg (D : Type) [CommRing D] (c : A →+* D) :
      specRingMap c ≫ g = (1 : Over.mk (specRingMap (c.comp rb₀)) ⟶ B.X).left := by
    change specRingMap c ≫ specRingMap rb₀ ≫ (η[B.X]).left =
      specRingMap (c.comp rb₀) ≫ (η[B.X]).left
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨ℓ, hℓ, hunit⟩ := exists_invertible_large_integer (AlgebraicClosure k)
  let power (n : ℕ) : B.X ⟶ B.X := 𝟙 B.X ^ (ℓ ^ n)
  have hEt (n : ℕ) : Etale (power n).left := by
    apply etale_pow B.X
    simpa only [Nat.cast_pow] using hunit.pow n
  have hfg : f = g := by
    apply affineToric_hom_ext_of_fieldTests_and_unramified hℓ B.X.hom f g he (fun n => (power n).left)
    · intro n
      haveI := hEt n
      infer_instance
    · intro n
      haveI := hEt n
      infer_instance
    · intro n
      let m := ℓ ^ n
      let D := AddMonoidAlgebra R (Fin r → ZMod m)
      let c : A →+* D := AddMonoidAlgebra.mapDomainRingHom R (modToricExponent r m)
      let x : Over.mk (specRingMap (c.comp rb₀)) ⟶ B.X :=
        torusTransport π r e D (c.comp ra₀) (c.comp rb₀) (hre D c)
          (fun j => Units.map c (u j))
      let y : Fin r → Dˣ := fun j => Units.map c (u j)
      have hy : y ^ m = 1 := funext fun j => toricUniversal_torsion (R := R) r m j
      have hpow : x ^ m = 1 := by
        change (torusTransport π r e D (c.comp ra₀) (c.comp rb₀) (hre D c) y) ^ m = 1
        rw [← map_pow, hy, map_one]
      change specRingMap c ≫ f ≫ (power n).left = specRingMap c ≫ g ≫ (power n).left
      rw [← Category.assoc, ← Category.assoc, hn D c, hg D c]
      change (x ≫ power n).left = ((1 : Over.mk (specRingMap (c.comp rb₀)) ⟶ B.X) ≫ power n).left
      rw [show x ≫ power n = 1 from by
          change x ≫ (𝟙 B.X ^ m) = 1
          rw [MonObj.comp_pow, Category.comp_id, hpow],
        show (1 : Over.mk (specRingMap (c.comp rb₀)) ⟶ B.X) ≫ power n = 1 from by
          change (1 : Over.mk (specRingMap (c.comp rb₀)) ⟶ B.X) ≫ (𝟙 B.X ^ m) = 1
          rw [MonObj.comp_pow, Category.comp_id, one_pow]]
    · intro n L _ a
      let d := affineToricTorsionι R r (ℓ ^ n)
      let c : A →+* L := (Spec.preimage (a ≫ d)).hom
      have hc : specRingMap c = a ≫ d := Spec.map_preimage _
      rw [← Category.assoc, ← Category.assoc, ← hc, hn L c, hg L c]
      rw [torusTransport_field_one π r e he_nat]
  let c := (toricEvaluate t).toRingHom
  have hr₁ : c.comp ra₀ = ra := RingHom.ext fun x => (toricEvaluate t).commutes (ra x)
  have hr₂ : c.comp rb₀ = rb := RingHom.ext fun x => (toricEvaluate t).commutes (rb x)
  have eq := (hn R c).symm.trans ((congrArg (specRingMap c ≫ ·) hfg).trans (hg R c))
  have hu : (fun j => Units.map c (u j)) = t := funext (toricEvaluate_universal t)
  rw [hu] at eq
  exact torusTransport_congr π r e hr₁ hr₂ (hre R c) hab t eq

#print axioms torusTransport_one_of_commRing

end SZRaynaud
