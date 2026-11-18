import WeilTateDivisiblePointsV003
import WeilTateLeftCountV001
import WeilTateRootsInstanceV002

/-!
# Left nondegeneracy at level `n` on the actual `Ω`-points, divisibility discharged

For `A : PkgI3.AbVar K` with `K` of characteristic `0`, `Ω` algebraically closed over `K` and `n ≥ 1`
(so `(n : K) ≠ 0`): the divisibility input of `WeilTate.left_nondeg_of_hom_finite_ker` is the proved
`WeilTate.Divisible.pt_pow_surjective` (multiplication by `n` étale, finite, hence surjective; rational point
lifts), and the roots-of-unity input is `WeilTate.hasEnoughRootsOfUnity_exponent`.  The remaining inputs are
exactly: finiteness of `A(Ω)[n]`, a homomorphism `φ : A(Ω) →* D` with finite kernel, and a pairing
`e : D[n] →* Hom(A(Ω)[n], Ωˣ)` with trivial kernel.
-/

noncomputable section

open CategoryTheory MonObj
open scoped CategoryTheory.MonObj

namespace WeilTate.Divisible

theorem point_left_nondeg {K : Type} [Field K] [CharZero K] (A : PkgI3.AbVar K) {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (n : ℕ) (hn : 0 < n)
    [Finite (powMonoidHom n : A.Pt Ω →* A.Pt Ω).ker] {D : Type*} [CommGroup D]
    (φ : A.Pt Ω →* D) [Finite φ.ker]
    (e : (powMonoidHom n : D →* D).ker →* ((powMonoidHom n : A.Pt Ω →* A.Pt Ω).ker →* Ωˣ))
    (hR : ∀ d, e d = 1 → d = 1) (x : (powMonoidHom n : A.Pt Ω →* A.Pt Ω).ker)
    (hx : ∀ d, e d x = 1) : x = 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI := hasEnoughRootsOfUnity_exponent Ω (powMonoidHom n : A.Pt Ω →* A.Pt Ω).ker
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  exact left_nondeg_of_hom_finite_ker n (pt_pow_surjective A n hnK) φ e hR x hx

end WeilTate.Divisible

#check @WeilTate.Divisible.point_left_nondeg
#print axioms WeilTate.Divisible.point_left_nondeg
