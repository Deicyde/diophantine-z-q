import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.Contrib.HDecomp.I3Linalg.RhoCont
import ZInQKernel.Contrib.OneProof.H.TailQ

/-! Geometric torsion points are the finite levels of the integral Tate module. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open PkgI3.AbVar

namespace ZInQ.Contrib.TateLatticeTorsion

set_option linter.style.haveILetI false

/-- A finite surjective morphism over a field is surjective on geometric points. -/
theorem surjective_geometricPoints_of_finite {K : Type} [Field K]
    {X Y : Over (Spec (.of K))} (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left] :
    Function.Surjective (fun p : ptObj (K := K) (AlgebraicClosure K) ⟶ X => p ≫ f) := by
  intro p
  let p' : Spec (.of (AlgebraicClosure K)) ⟶ Y.left := p.left
  let S := pullback f.left p'
  let t : S ⟶ Spec (.of (AlgebraicClosure K)) := pullback.snd f.left p'
  have hpb := IsPullback.of_hasPullback f.left p'
  haveI : IsFinite t := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  haveI : Surjective t := MorphismProperty.of_isPullback (P := @Surjective) hpb inferInstance
  haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace t
  haveI : Nonempty S :=
    ⟨Classical.choose (t.surjective (IsLocalRing.closedPoint (AlgebraicClosure K)))⟩
  have hd : Dense (closedPoints S) := by
    rw [dense_iff_closure_eq, ← Set.univ_inter (closedPoints S),
      JacobsonSpace.closure_inter_closedPoints_eq_closure isOpen_univ.isLocallyClosed, closure_univ]
  obtain ⟨z, hz⟩ := hd.nonempty
  let Z := pointOfClosedPoint t z hz
  have hZ : Z ≫ t = 𝟙 _ := pointOfClosedPoint_comp t z hz
  have hc : pullback.fst f.left p' ≫ f.left = t ≫ p' := pullback.condition
  have hcomp : (Z ≫ pullback.fst f.left p') ≫ f.left = p' := by
    rw [Category.assoc, hc, ← Category.assoc, hZ, Category.id_comp]
  have hw : (Z ≫ pullback.fst f.left p') ≫ X.hom =
      (ptObj (K := K) (AlgebraicClosure K)).hom := by
    rw [← Over.w f, ← Category.assoc, hcomp]
    exact Over.w p
  exact ⟨Over.homMk (Z ≫ pullback.fst f.left p') hw, Over.OverMorphism.ext hcomp⟩

/-- Multiplication by a positive integer on geometric points of an abelian
variety in characteristic zero is surjective. -/
theorem surjective_nsmul_geometricPoints {K : Type} [Field K] [CharZero K]
    (A : PkgI3.AbVar K) {n : ℕ} (hn : 0 < n) :
    Function.Surjective (fun x : Additive (A.Pt (AlgebraicClosure K)) => n • x) := by
  let f := ((n : ℤ) : End A).hom
  have hf : IsIsogenyMor f :=
    ZInQ.Contrib.AbVarBC.mulIsogeny K A (n : ℤ) (Nat.cast_ne_zero.mpr hn.ne')
  haveI : IsFinite f.left := hf.1
  haveI : Surjective f.left := hf.2
  intro x
  obtain ⟨p, hp⟩ := surjective_geometricPoints_of_finite f (Additive.toMul x)
  refine ⟨Additive.ofMul p, ?_⟩
  change Additive.ofMul (p ^ n) = x
  rw [← AvSplit.comp_natCast_hom' A p n]
  exact congrArg Additive.ofMul hp

/-- Finite torsion levels lift to the Tate module when multiplication
by the prime is surjective on the ambient group. -/
theorem exists_tateCoord_of_torsion {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*} [AddCommGroup M]
    (h : Function.Surjective (fun x : M => ℓ • x)) {n : ℕ} {a : M} (ha : ℓ ^ n • a = 0) :
    ∃ x : PkgI3.Tate.T ℓ M, x.1 n = a := by
  classical
  choose pre hpre using h
  let y : ℕ → M := Nat.rec a (fun _ c => pre c)
  have hy : ∀ j : ℕ, ℓ • y (j + 1) = y j := fun j => hpre (y j)
  let x (j : ℕ) := ℓ ^ (n - j) • y (j - n)
  have h0 : x 0 = 0 := by simpa [x, y] using ha
  have hstep (j : ℕ) : ℓ • x (j + 1) = x j := by
    by_cases hj : j < n
    · have hj0 : j - n = 0 := Nat.sub_eq_zero_of_le hj.le
      have hj1 : j + 1 - n = 0 := Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt hj)
      have he : n - j = n - (j + 1) + 1 := by omega
      simp only [x, hj1, hj0, smul_smul, he, pow_succ, mul_comm ℓ]
    · have hj' := le_of_not_gt hj
      have h0' : n - j = 0 := Nat.sub_eq_zero_of_le hj'
      have h1' : n - (j + 1) = 0 := Nat.sub_eq_zero_of_le (hj'.trans (Nat.le_succ j))
      have he : j + 1 - n = (j - n) + 1 := by omega
      simpa only [x, h0', h1', he, pow_zero, one_nsmul] using hy (j - n)
  exact ⟨⟨x, h0, hstep⟩, by simp [x, y]⟩

/-- Every geometric `ℓ^n`-torsion point is the `n`-th coordinate
of an element of the integral Tate module. -/
theorem exists_tateCoord_of_geometric_torsion {K : Type} [Field K] [CharZero K]
    (A : PkgI3.AbVar K) {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {n : ℕ}
    {a : Additive (A.Pt (AlgebraicClosure K))} (ha : ℓ ^ n • a = 0) :
    ∃ x : A.T ℓ, x.1 n = a :=
  exists_tateCoord_of_torsion (surjective_nsmul_geometricPoints A hℓ.out.pos) ha

end ZInQ.Contrib.TateLatticeTorsion

#print axioms ZInQ.Contrib.TateLatticeTorsion.surjective_geometricPoints_of_finite
#print axioms ZInQ.Contrib.TateLatticeTorsion.exists_tateCoord_of_geometric_torsion
