import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsTorusKernel
import ZInQKernel.Contrib.OneProof.FaltingsDict

/-! The torus in a semiabelian group contributes no rational kernel points
when prime-to-characteristic torsion has trivial kernel. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit ZInQ.SemiAbDescend ZInQ.Contrib.MilneQuasiInverse.Kernel

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace ZInQ.FaltingsRestate

/-- Finiteness of a prime-to-characteristic torsion-free algebraic subgroup of
an abelian variety, in the form of the rational image of a group homomorphism. -/
def FiniteAbelianImageOfNoInvertibleTorsion : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k)
    (X : Over (Spec (CommRingCat.of k))) [GrpObj X] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (g : X ⟶ B.X) [IsMonHom g],
    (∀ m : ℕ, (m : k) ≠ 0 → ∀ x : algPt k k ⟶ X, (x ≫ g) ^ m = 1 → x ≫ g = 1) →
    Finite (pointsMap g (algPt k k)).range

section Split

variable {k : Type} [Field k] [IsAlgClosed k]
local notation "Sch" => Over (Spec (CommRingCat.of k))
local notation "Pt" => algPt k k

set_option backward.isDefEq.respectTransparency false in
/-- A comparison on a split semiabelian group has finite rational kernel
when the corresponding abelian image satisfies the finiteness criterion. -/
theorem finite_rational_kernel_of_split_presentation
    (hA : FiniteAbelianImageOfNoInvertibleTorsion)
    {G H : Sch} [GrpObj G] [GrpObj H] [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom]
    (f : G ⟶ H) [IsMonHom f]
    (B : PkgI3.AbVar k) (π : G ⟶ B.X) [IsMonHom π]
    (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra k R],
      (Fin r → Rˣ) →* (algPt k R ⟶ G))
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hk : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ G),
      u ≫ π = 1 ↔ u ∈ (e R).range)
    (hn : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
      (φ : R →ₐ[k] S) (t : Fin r → Rˣ),
      e S (fun i => Units.map (φ : R →* S) (t i)) = algPtMap φ ≫ e R t)
    (hf : ∀ m : ℕ, (m : k) ≠ 0 → ∀ x : Pt ⟶ G, x ≫ f = 1 → x ^ m = 1 → x = 1) :
    Finite (Pt ⟶ kernelObject f) := by
  let Q := kernelObject f
  let ιQ := kernelInclusion f
  letI : GrpObj Q := kernelGroup f
  haveI : IsMonHom ιQ := kernelInclusion_isMonHom f
  haveI : Subsingleton (𝟙_ Sch).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : IsClosedImmersion (η[H]).left :=
    isClosedImmersion_of_comp_eq_id H.hom (η[H]).left (Over.w (η[H]))
  haveI : IsClosedImmersion ιQ.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (kernel_isPullback f).flip inferInstance
  haveI : LocallyOfFiniteType Q.hom := by
    rw [← Over.w ιQ]
    infer_instance
  haveI : QuasiCompact Q.hom := by
    rw [← Over.w ιQ]
    infer_instance
  have hkTriv (z : Pt ⟶ G) (hzf : z ≫ f = 1) (hzπ : z ≫ π = 1) : z = 1 := by
    obtain ⟨t, ht⟩ := (hk k z).mp hzπ
    let R := TorusRing k r
    let E := (pointsMap f Pt).comp (e k)
    let u : algPt k R ⟶ H := e R (tUniv r) ≫ f
    have hu (a : Fin r → kˣ) : algPtMap (torusLift a) ≫ u = E a := by
      have ha : (fun i => Units.map (torusLift (K := k) a).toMonoidHom (tUniv r i)) = a := by
        funext i
        apply Units.ext
        exact torusLift_tUniv a i
      have hn' : e k a = algPtMap (torusLift a) ≫ e R (tUniv r) :=
        (congrArg (e k) ha).symm.trans (hn R k (torusLift a) (tUniv r))
      change algPtMap (torusLift a) ≫ e R (tUniv r) ≫ f = e k a ≫ f
      rw [← Category.assoc, ← hn']
    have hEt : E t = 1 := by
      change e k t ≫ f = 1
      rwa [ht]
    have hE (m : ℕ) (hm : (m : k) ≠ 0) (a : Fin r → kˣ)
        (ha : E a = 1) (hp : a ^ m = 1) : a = 1 := by
      apply he k
      rw [map_one]
      apply hf m hm (e k a) ha
      rw [← map_pow, hp, map_one]
    have ht' := torus_parameter_kernel_rational_trivial E u hu hE t hEt
    rw [← ht, ht', map_one]
  let q := ιQ ≫ π
  have hK (x : Pt ⟶ Q) : x ≫ ιQ ≫ f = 1 := by
    rw [show ιQ ≫ f = 1 from kernelInclusion_comp f, MonObj.comp_one]
  have hq (x : Pt ⟶ Q) (hx : x ≫ q = 1) : x = 1 := by
    apply (cancel_mono ιQ).mp
    rw [MonObj.one_comp]
    exact hkTriv _ (by rw [Category.assoc, hK]) (by rwa [Category.assoc])
  have hq_inj : Function.Injective (pointsMap q Pt) := by
    intro x y hxy
    apply (div_eq_one.mp : x / y = 1 → x = y)
    apply hq
    change pointsMap q Pt (x / y) = 1
    rw [map_div, hxy, div_self']
  have hqT (m : ℕ) (hm : (m : k) ≠ 0) (x : Pt ⟶ Q) (hx : (x ≫ q) ^ m = 1) :
      x ≫ q = 1 := by
    have hxm : x ^ m = 1 := hq _ (by
      change pointsMap q Pt (x ^ m) = 1
      rw [map_pow]
      exact hx)
    have hxG : x ≫ ιQ = 1 := hf m hm _ (by rw [Category.assoc, hK]) (by
      change (pointsMap ιQ Pt x) ^ m = 1
      rw [← map_pow, hxm, map_one])
    change (x ≫ ιQ) ≫ π = 1
    rw [hxG, MonObj.one_comp]
  haveI : Finite (pointsMap q Pt).range := hA k B Q q hqT
  exact Finite.of_injective
    (fun x : Pt ⟶ Q => (⟨pointsMap q Pt x, x, rfl⟩ : (pointsMap q Pt).range))
    (fun _ _ h => hq_inj (congrArg Subtype.val h))

end Split

end ZInQ.FaltingsRestate
