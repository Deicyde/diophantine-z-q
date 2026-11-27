import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameRep3Card
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameAction

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Milne's count of torsion points, for every order prime to the characteristic

`MilneRem84` states J. S. Milne's Remark 8.4 for the geometric fibres of a false elliptic curve
over a `Z[1/30]`-scheme, for every `n` not divisible by the characteristic. Its instances at
`n = 3` and `n = 5` are the counts `GeomCard3` and `GeomCard5`. `GeomFreeM M` says that the
`M`-torsion of every geometric fibre has a generator.
-/

attribute [local instance] FEC.grp

/-- Leaf (Milne, Remark 8.4, at `g = 2`). At a geometric point whose characteristic does not
divide `n`, the `n`-torsion of a false elliptic curve over a `Z[1/30]`-scheme has `n ^ 4` points.

Source: J. S. Milne, *Abelian Varieties*, in G. Cornell and J. H. Silverman (eds.), *Arithmetic
Geometry*, Springer (1986), Remark 8.4, p. 14 of the author's retyped edition, with subscripts
and exponents transcribed: "If k is separably algebraically closed and n is not divisible by its
characteristic, then the theorem says that the kernel A_n(k) of n : A(k) → A(k) has n^{2g}
elements. As this is also true for all n′ dividing n, it follows that A_n(k) is a free
Z/nZ-module of rank 2g." The theorem it refers to is Thm 8.2, p. 13 of the same edition: "Let A
be an abelian variety of dimension g, and let n > 0 be an integer. Then n_A: A → A is an isogeny
of degree n^{2g}; it is étale if and only if the characteristic of k does not divide n." The same
statement is Remark 7.3, p. 34, of Milne's course notes v2.0 (2008). Section 20, p. 42 (ibid.,
1986) defines an abelian scheme as a proper smooth group scheme with connected geometric fibres,
so a geometric fibre of a false elliptic curve is an abelian variety; its dimension `g = 2` comes
from the field `smooth : SmoothOfRelativeDimension 2 F.hom` of `FEC`, so the count is `n ^ 4`. -/
def MilneRem84 : Prop :=
  ∀ (S : Over Z30Base) (A : FEC S.left) (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ S.left) (n : ℕ), (n : k) ≠ 0 →
    letI := A.grp
    Nat.card {x : Over.mk s ⟶ A.F // x ^ n = 1} = n ^ 4

/-- At every geometric point, the 5-torsion of a false elliptic curve has exactly 625 points. -/
def GeomCard5 : Prop :=
  ∀ (S : Over Z30Base) (A : FEC S.left) (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ S.left),
    letI := A.grp
    Nat.card {x : Over.mk s ⟶ A.F // x ^ 5 = 1} = 625

/-- At every geometric point, the `M`-torsion of a false elliptic curve over a `Z[1/30]`-scheme has a generator. -/
def GeomFreeM (M : ℕ) : Prop :=
  ∀ (S : Over Z30Base) (A : FEC S.left) (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ S.left), ∃ P : Over.mk s ⟶ A.F, IsGenAt M A s P

/-- A prime dividing `30` is nonzero in a field that receives a map from `Z[1/30]`. -/
theorem natCast_ne_zero_of_Z30 {k : Type} [Field k] (φ : Y3RouteA.Z30 →+* k) {p : ℕ}
    (hp : p.Prime) (h30 : p ∣ 30) : (p : k) ≠ 0 := by
  intro h0
  have hdvd : ringChar k ∣ p := (ringChar.spec k p).1 h0
  have hne : ringChar k ≠ p := ringChar_ne_of_Z30 φ h30
  have h1 : ringChar k ≠ 1 := by
    intro h
    have : ((1 : ℕ) : k) = 0 := (ringChar.spec k 1).2 (by rw [h])
    simp at this
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact h1 h
  · exact hne h

/-- The field of a geometric point of a `Z[1/30]`-scheme receives a map from `Z[1/30]`. -/
def ringHomOfPoint (S : Over Z30Base) {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ S.left) :
    Y3RouteA.Z30 →+* k :=
  (ringHomOfSpec (s ≫ S.hom)).hom

theorem geomCard3_of_rem84 (h : MilneRem84) : GeomCard3 := by
  intro S A k _ _ s
  have h3 : ((3 : ℕ) : k) ≠ 0 :=
    natCast_ne_zero_of_Z30 (ringHomOfPoint S s) Nat.prime_three (by norm_num)
  have := h S A k s 3 h3
  simpa using this

theorem geomCard5_of_rem84 (h : MilneRem84) : GeomCard5 := by
  intro S A k _ _ s
  have h5 : ((5 : ℕ) : k) ≠ 0 :=
    natCast_ne_zero_of_Z30 (ringHomOfPoint S s) Nat.prime_five (by norm_num)
  have := h S A k s 5 h5
  simpa using this

end Y3Buzzard
