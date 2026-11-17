import ZInQKernel.OneProof.H.TailZ24

/-! # pic-dict §0: verbatim copies of the three rows (TailZ24.lean l.302, l.366, l.708), checked by `rfl` -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace PicDictCopy

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

def PicZeroAbVar : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P),
    ∃ (B : AbVar K) (j : B.X ⟶ P), IsPicZero rep B j

def PhiAmpleIsogeny : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∀ L : A.X.left.Pic, IsAmple A.X.left L →
      ∀ lam : A.X ⟶ B.X, lam ≫ j = phiL rep L → IsIsogenyMor lam

def WeilPairingMumford : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j →
    ∃ e : ∀ n : ℕ, Pairing A B n,
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
        ∀ (x : tors A (m * n)) (y : tors B n),
          (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val) ∧
      (∀ (f : End A) (fv : End B), fv.hom ≫ j = j ≫ dualP rep f.hom → ∀ n : ℕ, 0 < n →
        (n : K) ≠ 0 → ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y) ∧
      (∀ L : A.X.left.Pic, IsAmple A.X.left L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
        ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ (x : tors A n) (y : tors B n),
        constK A ((e n x y).val : AlgebraicClosure K) =
          weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
            (Additive.toMul (y : HDec.WeilPairing.P B)))

example : PicZeroAbVar = T09Pic.PicZeroAbVar := rfl
example : PhiAmpleIsogeny = T09Pic.PhiAmpleIsogeny := rfl
example : WeilPairingMumford = T09Pic.WeilPairingMumford := rfl

end PicDictCopy
