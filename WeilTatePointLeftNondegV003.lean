import WeilTatePointLeftNondegV001
import ActualTorsionFinitenessV003

/-!
# Left nondegeneracy at level `n` on the actual `Ω`-points: torsion finiteness discharged

Successor of `WeilTatePointLeftNondegV001` (that edition is kept unchanged).  Finiteness of
`A(Ω)[n] = (powMonoidHom n).ker` is the accepted `ActualTorsionFiniteness.finite_original_torsion`
(stated for the predicate-identical `ActualFiniteLevel.torsionSubgroup A Ω n = {x | x ^ n = 1}`; the two
subgroups have the same carrier, so the transfer is an equivalence of subtypes through `Iff.rfl`).  The
remaining inputs are a homomorphism `φ : A(Ω) →* D` with finite kernel and a pairing
`e : D[n] →* Hom(A(Ω)[n], Ωˣ)` with trivial kernel.
-/

noncomputable section

open CategoryTheory MonObj
open scoped CategoryTheory.MonObj

namespace WeilTate.Divisible

theorem finite_powKer {K : Type} [Field K] [CharZero K] (A : PkgI3.AbVar K) {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (n : ℕ) (hn : 0 < n) :
    Finite (powMonoidHom n : A.Pt Ω →* A.Pt Ω).ker := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hnΩ : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  haveI := ActualTorsionFiniteness.finite_original_torsion A n hnΩ
  let f : (powMonoidHom n : A.Pt Ω →* A.Pt Ω).ker → ActualFiniteLevel.torsionSubgroup A Ω n :=
    fun x => ⟨x.1, x.2⟩
  exact Finite.of_injective f (fun x y h => Subtype.ext (congrArg Subtype.val h))

/-- **Left nondegeneracy of a right-perfect pairing on the actual `A(Ω)[n]`**, with divisibility, torsion
finiteness and roots of unity discharged; inputs: `φ` with finite kernel, `e` with trivial kernel. -/
theorem point_left_nondeg' {K : Type} [Field K] [CharZero K] (A : PkgI3.AbVar K) {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (n : ℕ) (hn : 0 < n) {D : Type*} [CommGroup D]
    (φ : A.Pt Ω →* D) [Finite φ.ker]
    (e : (powMonoidHom n : D →* D).ker →* ((powMonoidHom n : A.Pt Ω →* A.Pt Ω).ker →* Ωˣ))
    (hR : ∀ d, e d = 1 → d = 1) (x : (powMonoidHom n : A.Pt Ω →* A.Pt Ω).ker)
    (hx : ∀ d, e d x = 1) : x = 1 := by
  haveI := finite_powKer (Ω := Ω) A n hn
  exact point_left_nondeg (Ω := Ω) A n hn φ e hR x hx

end WeilTate.Divisible

#check @WeilTate.Divisible.finite_powKer
#check @WeilTate.Divisible.point_left_nondeg'
#print axioms WeilTate.Divisible.finite_powKer
#print axioms WeilTate.Divisible.point_left_nondeg'
